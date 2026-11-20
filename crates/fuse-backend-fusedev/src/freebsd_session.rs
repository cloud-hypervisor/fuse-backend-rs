// SPDX-License-Identifier: Apache-2.0

//! FUSE session management for FreeBSD's fusefs(5).
//!
//! The kernel speaks the Linux wire protocol over `/dev/fuse`, so requests and replies use the
//! same reader and writer as on Linux. [`FuseSession::mount()`] calls nmount(2) with the device
//! fd in the `fd` option, the way mount_fusefs(8) does. There is no fusermount, so mounting needs
//! root, or `vfs.usermount=1`, a mountpoint the caller owns and
//! [`FuseSession::set_allow_other(false)`](FuseSession::set_allow_other).

use std::fs::{File, OpenOptions};
use std::os::unix::fs::OpenOptionsExt;
use std::os::unix::io::{AsFd, AsRawFd};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use nix::errno::Errno;
use nix::mount::{unmount, MntFlags, Nmount};
use nix::poll::{poll, PollFd, PollFlags, PollTimeout};
use nix::sys::eventfd::{EfdFlags, EventFd};
use nix::unistd::read;

use super::{
    pagesize, Error::SessionFailure, FuseBuf, FuseDevWriter, Reader, Result, FUSE_HEADER_SIZE,
    FUSE_KERN_BUF_PAGES,
};
use crate::{FuseChannelExt, FuseDevReaderExt, FuseSessionExt};

const FUSE_DEVICE: &str = "/dev/fuse";

/// A fuse session manager to manage the connection with the in kernel fuse driver.
pub struct FuseSession {
    mountpoint: PathBuf,
    fsname: String,
    subtype: String,
    file: Option<File>,
    // umount() unmounts by this id, so it can't hit a file system that replaced ours.
    fsid: Option<[i32; 2]>,
    bufsize: usize,
    readonly: bool,
    allow_other: bool,
    // Shared with every channel. Nothing reads it, so once written, it wakes every channel.
    waker: Arc<EventFd>,
}

impl FuseSession {
    /// Create a new fuse session, without mounting/connecting to the in kernel fuse driver.
    pub fn new(
        mountpoint: &Path,
        fsname: &str,
        subtype: &str,
        readonly: bool,
    ) -> Result<FuseSession> {
        let dest = mountpoint
            .canonicalize()
            .map_err(|_| SessionFailure(format!("invalid mountpoint {mountpoint:?}")))?;
        if !dest.is_dir() {
            return Err(SessionFailure(format!("{dest:?} is not a directory")));
        }
        let waker = EventFd::from_flags(EfdFlags::EFD_CLOEXEC)
            .map_err(|e| SessionFailure(format!("create eventfd: {e}")))?;

        Ok(FuseSession {
            mountpoint: dest,
            fsname: fsname.to_owned(),
            subtype: subtype.to_owned(),
            file: None,
            fsid: None,
            bufsize: FUSE_KERN_BUF_PAGES * pagesize() + FUSE_HEADER_SIZE,
            readonly,
            allow_other: true,
            waker: Arc::new(waker),
        })
    }

    /// Set the allow_other mount option. This allows other users than the one mounting the
    /// filesystem to access the filesystem. Only root may mount with it.
    pub fn set_allow_other(&mut self, allow_other: bool) {
        self.allow_other = allow_other;
    }

    /// Expose the associated FUSE session file.
    pub fn get_fuse_file(&self) -> Option<&File> {
        self.file.as_ref()
    }

    /// Force setting the associated FUSE session file.
    pub fn set_fuse_file(&mut self, file: File) {
        self.file = Some(file);
    }

    /// Get the mountpoint of the session.
    pub fn mountpoint(&self) -> &Path {
        &self.mountpoint
    }

    /// Get the file system name of the session.
    pub fn fsname(&self) -> &str {
        &self.fsname
    }

    /// Get the subtype of the session.
    pub fn subtype(&self) -> &str {
        &self.subtype
    }

    /// Get the default buffer size of the session.
    pub fn bufsize(&self) -> usize {
        self.bufsize
    }

    /// Mount the fuse mountpoint, building connection with the in kernel fuse driver.
    ///
    /// The kernel queues FUSE_INIT without waiting for it, so this returns before any channel
    /// serves the session.
    pub fn mount(&mut self) -> Result<()> {
        let (file, fsid) = fuse_kern_mount(
            &self.mountpoint,
            &self.fsname,
            &self.subtype,
            self.readonly,
            self.allow_other,
            self.bufsize,
        )?;
        self.file = Some(file);
        self.fsid = Some(fsid);
        Ok(())
    }

    /// Destroy a fuse session.
    ///
    /// Unmounts with `MNT_FORCE`, like libfuse. FreeBSD has no lazy unmount, and a plain one
    /// fails while anything in the mount is open.
    pub fn umount(&mut self) -> Result<()> {
        match self.file.take() {
            Some(file) => fuse_kern_umount(&self.mountpoint, self.fsid.take(), file),
            None => Ok(()),
        }
    }

    /// Create a new fuse message channel.
    pub fn new_channel(&self) -> Result<FuseChannel> {
        let file = self
            .file
            .as_ref()
            .ok_or_else(|| SessionFailure("invalid fuse session".to_string()))?
            .try_clone()
            .map_err(|e| SessionFailure(format!("dup fd: {e}")))?;
        Ok(FuseChannel {
            file,
            waker: self.waker.clone(),
            buf: vec![0x0u8; self.bufsize],
        })
    }

    /// Wake channel loop and exit
    ///
    /// This is final: channels created afterwards exit at once, too.
    pub fn wake(&self) -> Result<()> {
        self.waker
            .write(1)
            .map(drop)
            .map_err(|e| SessionFailure(format!("wake channel: {e}")))
    }
}

impl Drop for FuseSession {
    fn drop(&mut self) {
        let _ = self.umount();
    }
}

impl FuseSessionExt for FuseSession {
    fn file(&self) -> Option<&File> {
        self.file.as_ref()
    }

    fn bufsize(&self) -> usize {
        self.bufsize
    }
}

/// A fuse channel abstraction.
///
/// Each session can hold multiple channels. The channels share the session's fd and wait for
/// requests in poll(2). A blocking read would hang after an unmount, because the kernel then
/// wakes only one blocked reader, and a kqueue wait would hang too, because the kernel posts no
/// kqueue event when the session dies. Every poll(2) waiter wakes.
pub struct FuseChannel {
    file: File,
    waker: Arc<EventFd>,
    buf: Vec<u8>,
}

impl FuseChannel {
    /// Get next available FUSE request from the underlying fuse device file.
    ///
    /// Returns:
    /// - Ok(None): the session was woken, or the file system was unmounted
    /// - Ok(Some((reader, writer))): reader to receive request and writer to send reply
    /// - Err(e): error message
    pub fn get_request(&mut self) -> Result<Option<(Reader<'_>, FuseDevWriter<'_>)>> {
        let fd = self.file.as_raw_fd();
        loop {
            let mut fds = [
                PollFd::new(self.file.as_fd(), PollFlags::POLLIN),
                PollFd::new(self.waker.as_fd(), PollFlags::POLLIN),
            ];
            match poll(&mut fds, PollTimeout::NONE) {
                Ok(_) => {}
                Err(Errno::EINTR) => continue,
                Err(e) => return Err(SessionFailure(format!("poll: {e}"))),
            }
            if fds[1].any() == Some(true) {
                debug!("Will exit from fuse service");
                return Ok(None);
            }
            // The fd polls readable when a request is queued or when the session is gone, and
            // the read tells the two apart.
            match read(&self.file, &mut self.buf) {
                Ok(len) => {
                    // Reuse the buffer for both the Reader and the Writer, like the other
                    // channels: the Reader isn't used anymore once the Writer starts writing.
                    let buf = unsafe {
                        std::slice::from_raw_parts_mut(self.buf.as_mut_ptr(), self.buf.len())
                    };
                    // Reader::new() and Writer::new() should always return success.
                    let reader =
                        Reader::from_fuse_buffer(FuseBuf::new(&mut self.buf[..len])).unwrap();
                    let writer = FuseDevWriter::new(fd, buf).unwrap();
                    return Ok(Some((reader, writer)));
                }
                // Another channel took the request.
                Err(Errno::EAGAIN | Errno::EINTR) => continue,
                Err(Errno::ENODEV) => {
                    debug!(
                        "got ENODEV when reading fuse fd, assuming fuse filesystem was umounted."
                    );
                    return Ok(None);
                }
                Err(e) => {
                    warn!("read fuse dev failed on fd {fd}: {e}");
                    return Err(SessionFailure(format!("read new request: {e:?}")));
                }
            }
        }
    }
}

impl FuseChannelExt for FuseChannel {
    fn next_request(&mut self) -> Result<Option<(Reader<'_>, FuseDevWriter<'_>)>> {
        FuseChannel::get_request(self)
    }
}

/// Mount a fuse file system with nmount(2), using the options mount_fusefs(8) passes.
fn fuse_kern_mount(
    mountpoint: &Path,
    fsname: &str,
    subtype: &str,
    readonly: bool,
    allow_other: bool,
    bufsize: usize,
) -> Result<(File, [i32; 2])> {
    // The channels need a nonblocking fd. fcntl(F_SETFL) sets O_NONBLOCK through an ioctl that
    // the fuse device doesn't implement and fails with ENODEV, so set it at open.
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .custom_flags(libc::O_NONBLOCK)
        .open(FUSE_DEVICE)
        .map_err(|e| SessionFailure(format!("open {FUSE_DEVICE}: {e}")))?;
    // READ replies go through the channel buffer, so cap READ sizes at its size, as on Linux.
    // Core's INIT reply keeps max_write within it too. The kernel kills the session when a
    // request doesn't fit the buffer.
    let max_read = bufsize.to_string();
    let fd = file.as_raw_fd().to_string();

    let mut flags = MntFlags::MNT_NOSUID | MntFlags::MNT_NOATIME;
    if readonly {
        flags |= MntFlags::MNT_RDONLY;
    }
    // fusefs spells the names of its valued options with a trailing '='.
    let mut nmount = Nmount::new();
    nmount
        .str_opt_owned("fstype", "fusefs")
        .str_opt_owned("fspath", mountpoint)
        .str_opt_owned("from", FUSE_DEVICE)
        .str_opt_owned("fd", fd.as_str())
        .str_opt_owned("max_read=", max_read.as_str())
        .null_opt_owned("default_permissions");
    if !fsname.is_empty() {
        nmount.str_opt_owned("fsname=", fsname);
    }
    if !subtype.is_empty() {
        nmount.str_opt_owned("subtype=", subtype);
    }
    if allow_other {
        nmount.null_opt_owned("allow_other");
    }
    debug!("mount {fsname} on {mountpoint:?} with fusefs, fd {fd}, flags {flags:?}");
    nmount
        .nmount(flags)
        .map_err(|e| SessionFailure(format!("failed to mount {mountpoint:?}: {e}")))?;
    match fsid_of(mountpoint) {
        Ok(fsid) => Ok((file, fsid)),
        Err(e) => {
            // Nothing can have replaced the mount this soon, so unmount it by path.
            drop(file);
            let _ = unmount(mountpoint, MntFlags::MNT_FORCE);
            Err(SessionFailure(format!("statfs {mountpoint:?}: {e}")))
        }
    }
}

/// The id of the file system mounted at `path`, as umount(8) passes it to unmount(2).
fn fsid_of(path: &Path) -> nix::Result<[i32; 2]> {
    let fsid = nix::sys::statfs::statfs(path)?.filesystem_id();
    // SAFETY: libc's fsid_t is a repr(C) struct of two i32s, with the field private.
    Ok(unsafe { std::mem::transmute::<libc::fsid_t, [i32; 2]>(fsid) })
}

/// Unmount a fuse file system, by its id when [`FuseSession::mount()`] mounted it.
///
/// unmount(2) follows symlinks and unmounts whatever is mounted at a path. After an unmount from
/// outside, that can be another file system, so a path is only used for a session file set with
/// [`FuseSession::set_fuse_file()`].
fn fuse_kern_umount(mountpoint: &Path, fsid: Option<[i32; 2]>, file: File) -> Result<()> {
    // Close the session fd first, like libfuse. A channel that still serves answers the
    // unmount's FUSE_DESTROY, and once the channels have closed their fds, the kernel fails it.
    drop(file);
    let res = match fsid {
        Some([a, b]) => unmount(
            format!("FSID:{a}:{b}").as_str(),
            MntFlags::MNT_FORCE | MntFlags::MNT_BYFSID,
        ),
        None => unmount(mountpoint, MntFlags::MNT_FORCE),
    };
    match res {
        // Someone else unmounted it already: ENOENT for an id that's gone, EINVAL for a path
        // that isn't a mountpoint anymore.
        Ok(()) | Err(Errno::ENOENT | Errno::EINVAL) => Ok(()),
        Err(e) => Err(SessionFailure(format!(
            "failed to umount {mountpoint:?}: {e}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vmm_sys_util::tempdir::TempDir;

    #[test]
    fn test_new_session() {
        let se = FuseSession::new(Path::new("haha"), "foo", "bar", true);
        assert!(se.is_err());

        let dir = TempDir::new().unwrap();
        let se = FuseSession::new(dir.as_path(), "foo", "bar", false);
        assert!(se.is_ok());
    }

    #[test]
    fn test_new_channel_unmounted() {
        let dir = TempDir::new().unwrap();
        let se = FuseSession::new(dir.as_path(), "foo", "bar", false).unwrap();
        assert!(se.new_channel().is_err());
    }
}
