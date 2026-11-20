// SPDX-License-Identifier: Apache-2.0

//! READ replies that `splice(2)` their data from a file into `/dev/fuse`.
//!
//! `fuse_dev_splice_write()` takes a reply from a pipe as one message, header
//! first. The data of a READ reply goes into the pipe while the file system
//! handles the request, before the server knows the header, so a reply takes
//! two pipes. The data waits in one, and the header and then the data go into
//! the other, which the channel splices into the device. Each channel owns its
//! pipes and reuses them for every request.

use std::convert::TryFrom;
use std::fmt::Display;
use std::fs::File;
use std::io::{self, IoSlice, Read};
use std::os::fd::{AsRawFd, BorrowedFd, RawFd};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

use nix::errno::Errno;
use nix::fcntl::{fcntl, splice, FcntlArg, OFlag, SpliceFFlags};
use nix::sys::uio::writev;
use nix::unistd::pipe2;

use crate::pagesize;

#[derive(Debug)]
struct Pipe {
    r: File,
    w: File,
    /// The size of the pipe in bytes.
    size: AtomicUsize,
}

impl Pipe {
    fn new() -> io::Result<Self> {
        // Non-blocking, so that reading a pipe stops when it is empty.
        let (r, w) = pipe2(OFlag::O_CLOEXEC | OFlag::O_NONBLOCK)?;
        let size = fcntl(&w, FcntlArg::F_GETPIPE_SZ)? as usize;
        Ok(Pipe {
            r: r.into(),
            w: w.into(),
            size: AtomicUsize::new(size),
        })
    }

    fn size(&self) -> usize {
        self.size.load(Ordering::Relaxed)
    }

    fn set_size(&self, size: usize) -> bool {
        let Ok(size) = i32::try_from(size) else {
            return false;
        };
        match fcntl(&self.w, FcntlArg::F_SETPIPE_SZ(size)) {
            Ok(n) => {
                self.size.store(n as usize, Ordering::Relaxed);
                true
            }
            Err(_) => false,
        }
    }

    /// Grow the pipe to `need` bytes. If it can't, grow it as far as it can
    /// below that and return false.
    fn grow(&self, need: usize) -> bool {
        if need <= self.size() || self.set_size(need) {
            return true;
        }
        let mut size = need.next_power_of_two() / 2;
        while size > self.size() && !self.set_size(size) {
            size /= 2;
        }
        false
    }

    /// The number of bytes in the pipe.
    fn len(&self) -> io::Result<usize> {
        nix::ioctl_read_bad!(fionread, libc::FIONREAD, libc::c_int);
        let mut n = 0;
        // SAFETY: FIONREAD writes one int to `n`.
        unsafe { fionread(self.r.as_raw_fd(), &mut n) }?;
        Ok(n as usize)
    }

    /// Read everything in the pipe and append it to `buf`.
    fn drain(&self, buf: &mut Vec<u8>) -> io::Result<()> {
        match (&self.r).read_to_end(buf) {
            Err(e) if e.kind() != io::ErrorKind::WouldBlock => Err(e),
            _ => Ok(()),
        }
    }
}

/// Errors that mean splicing won't work for this channel, so it stops trying.
/// `EINVAL` comes from a file or device without splice support, `ENOSYS` and
/// `EPERM` from a kernel or seccomp filter that doesn't allow the syscall.
fn cant_splice(e: Errno) -> bool {
    matches!(e, Errno::EINVAL | Errno::ENOSYS | Errno::EPERM)
}

/// The pipes that one channel splices its READ replies through.
#[derive(Debug)]
pub(crate) struct SplicePipes {
    /// Holds the data while the file system handles the request.
    data: Pipe,
    /// Puts the header in front of the data.
    msg: Pipe,
    /// Whether `F_SETPIPE_SZ` may still grow the pipes.
    can_grow: AtomicBool,
    /// Whether the pipes may hold bytes of a reply that wasn't sent.
    dirty: AtomicBool,
    /// Set after an error that would happen again.
    disabled: AtomicBool,
}

impl SplicePipes {
    pub(crate) fn new() -> io::Result<Self> {
        Ok(SplicePipes {
            data: Pipe::new()?,
            msg: Pipe::new()?,
            can_grow: AtomicBool::new(true),
            dirty: AtomicBool::new(false),
            disabled: AtomicBool::new(false),
        })
    }

    /// Whether splicing still works for this channel.
    pub(crate) fn enabled(&self) -> bool {
        !self.disabled.load(Ordering::Relaxed)
    }

    fn disable(&self, what: &str, e: impl Display) {
        if !self.disabled.swap(true, Ordering::Relaxed) {
            warn!("fuse: {what} failed ({e}), sending READ replies without splice");
        }
    }

    /// Grow the pipes to hold a reply with `count` bytes of data from file
    /// offset `off`. Returns false if they can't grow that large.
    fn reserve(&self, off: u64, count: usize) -> bool {
        let page = pagesize();
        // The data takes a pipe slot per page it touches, and the header one more.
        let data = ((off % page as u64) as usize + count).div_ceil(page) * page;
        let msg = data + page;
        if data <= self.data.size() && msg <= self.msg.size() {
            return true;
        }
        if !self.can_grow.load(Ordering::Relaxed) {
            return false;
        }
        let data_grew = self.data.grow(data);
        let msg_grew = self.msg.grow(msg);
        if data_grew && msg_grew {
            return true;
        }
        // Without CAP_SYS_RESOURCE a pipe can't grow past pipe-max-size, 1 MiB
        // by default. Keep the largest sizes allowed, and copy the replies that
        // don't fit.
        self.can_grow.store(false, Ordering::Relaxed);
        false
    }

    /// Splice up to `count` bytes of the file `fd`, from offset `off`, into the
    /// data pipe. Returns `None` if the reply has to be copied instead.
    pub(crate) fn splice_in(&self, fd: RawFd, off: u64, count: usize) -> Option<usize> {
        if !self.reserve(off, count) {
            return None;
        }
        if self.dirty.load(Ordering::Relaxed) {
            // A reply that failed before it was sent left its data behind.
            let mut stale = Vec::new();
            if let Err(e) = self.data.drain(&mut stale).and(self.msg.drain(&mut stale)) {
                self.disable("emptying the splice pipes", e);
                return None;
            }
            self.dirty.store(false, Ordering::Relaxed);
        }
        let mut off = libc::loff_t::try_from(off).ok()?;
        // SAFETY: the caller's file owns `fd` for the duration of the call.
        let fd = unsafe { BorrowedFd::borrow_raw(fd) };
        let flags = SpliceFFlags::empty();
        match splice(fd, Some(&mut off), &self.data.w, None, count, flags) {
            Ok(n) => {
                self.dirty.store(n > 0, Ordering::Relaxed);
                Some(n)
            }
            Err(e) => {
                if cant_splice(e) {
                    self.disable("splice from a file", e);
                }
                None
            }
        }
    }

    /// Move the `buf.len()` bytes that `splice_in()` put in the data pipe to
    /// `buf`.
    pub(crate) fn take_data(&self, buf: &mut [u8]) -> io::Result<()> {
        (&self.data.r)
            .read_exact(buf)
            .inspect_err(|e| self.disable("reading back spliced data", e))?;
        self.dirty.store(false, Ordering::Relaxed);
        Ok(())
    }

    /// Send the reply made of `head` and the `len` bytes in the data pipe to
    /// the FUSE device `fuse`.
    pub(crate) fn send(&self, fuse: BorrowedFd, head: &[IoSlice], len: usize) -> io::Result<usize> {
        let head_len: usize = head.iter().map(|b| b.len()).sum();
        let total = head_len + len;
        let flags = SpliceFFlags::empty();
        // The bytes of `head` in the message pipe.
        let queued = writev(&self.msg.w, head).unwrap_or(0);
        if queued == head_len
            && splice(&self.data.r, None, &self.msg.w, None, len, flags) == Ok(len)
        {
            match splice(&self.msg.r, None, fuse, None, total, flags) {
                // fuse_dev_splice_write() empties the pipe before it parses the
                // message, so after an error with the pipe empty the kernel got
                // the reply and rejected it, as it would reject the same write().
                r if r.is_ok() || self.msg.len().ok() == Some(0) => {
                    self.dirty.store(false, Ordering::Relaxed);
                    return Ok(r?);
                }
                Err(e) if cant_splice(e) => self.disable("splice to the fuse device", e),
                _ => {}
            }
        }

        // The reply is still in the pipes. Copy it out and write it.
        let mut buf = Vec::with_capacity(total);
        self.msg.drain(&mut buf)?;
        self.data.drain(&mut buf)?;
        self.dirty.store(false, Ordering::Relaxed);
        if buf.len() != queued + len {
            self.disable("reading back a spliced reply", Errno::EIO);
            return Err(Errno::EIO.into());
        }
        let mut iov = head.to_vec();
        iov.push(IoSlice::new(&buf[queued..]));
        Ok(writev(fuse, &iov)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pipes_grow() {
        let pipes = SplicePipes::new().unwrap();
        let page = pagesize();
        assert!(pipes.reserve(0, pipes.data.size() / 2));
        // With pages over 8 KiB, 128 pages exceed pipe-max-size, 1 MiB by default.
        if !Pipe::new().unwrap().set_size(128 * page) {
            return;
        }
        // 64 pages of data from a page boundary fill a pipe of 64 slots, and
        // the header takes a 65th, so the message pipe grows to 128.
        assert!(pipes.reserve(0, 64 * page));
        assert_eq!(pipes.data.size(), 64 * page);
        assert_eq!(pipes.msg.size(), 128 * page);
        // From the middle of a page the data touches 65 pages.
        assert!(pipes.reserve(1, 64 * page));
        assert_eq!(pipes.data.size(), 128 * page);
    }

    #[test]
    fn test_pipes_stop_growing() {
        let pipes = SplicePipes::new().unwrap();
        // Only CAP_SYS_RESOURCE lets a pipe grow past pipe-max-size, 1 MiB by default.
        if pipes.reserve(0, 4 << 20) {
            assert!(pipes.msg.size() > 4 << 20);
            return;
        }
        assert!(!pipes.can_grow.load(Ordering::Relaxed));
        // The pipes took the largest size allowed, and replies that fit still splice.
        let size = pipes.msg.size();
        assert!((0x10000..4 << 20).contains(&size));
        assert_eq!(pipes.data.size(), size);
        assert!(pipes.reserve(0, size - pagesize()));
        assert!(!pipes.reserve(0, size));
    }
}
