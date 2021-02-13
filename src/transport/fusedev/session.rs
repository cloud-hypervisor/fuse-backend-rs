// Copyright 2020-2021 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! FUSE session management.
//!
//! A FUSE channel is a FUSE request handling context that takes care of handling FUSE requests
//! sequentially. A FUSE session is a connection from a FUSE mountpoint to a FUSE server daemon.
//! A FUSE session can have multiple FUSE channels so that FUSE requests are handled in parallel.

use std::cell::RefCell;
use std::fs::{File, OpenOptions};
use std::ops::Deref;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::path::{Path, PathBuf};

use libc::{c_int, sysconf, _SC_PAGESIZE};
use nix::errno::Errno;
use nix::mount::{mount, umount2, MntFlags, MsFlags};
use nix::poll::{poll, PollFd, PollFlags};
use nix::unistd::{close, dup, getgid, getuid, read};
use nix::Error as nixError;

use epoll::{ControlOptions, Event, Events};
use nix::fcntl::{fcntl, FcntlArg, OFlag};

use super::{Error::SessionFailure, FuseBuf, Reader, Result, Writer};
use vmm_sys_util::eventfd::EventFd;

// These follows definition from libfuse.
const FUSE_KERN_BUF_SIZE: usize = 256;
const FUSE_HEADER_SIZE: usize = 0x1000;

const FUSE_DEVICE: &str = "/dev/fuse";
const FUSE_FSTYPE: &str = "fuse";

const FUSE_DEV_EVENT: u64 = 0;
const EXIT_FUSE_EVENT: u64 = 1;

/// A fuse session manager to manage the connection with the in kernel fuse driver.
pub struct FuseSession {
    mountpoint: PathBuf,
    fsname: String,
    subtype: String,
    file: Option<File>,
    bufsize: usize,
}

impl FuseSession {
    /// Create a new fuse session, without mounting/connecting to the in kernel fuse driver.
    pub fn new(mountpoint: &Path, fsname: &str, subtype: &str) -> Result<FuseSession> {
        let dest = mountpoint
            .canonicalize()
            .map_err(|_| SessionFailure(format!("invalid mountpoint {:?}", mountpoint)))?;
        if !dest.is_dir() {
            return Err(SessionFailure(format!("{:?} is not a directory", dest)));
        }

        Ok(FuseSession {
            mountpoint: dest,
            fsname: fsname.to_owned(),
            subtype: subtype.to_owned(),
            file: None,
            bufsize: FUSE_KERN_BUF_SIZE * pagesize() + FUSE_HEADER_SIZE,
        })
    }

    /// Mount the fuse mountpoint, building connection with the in kernel fuse driver.
    pub fn mount(&mut self) -> Result<()> {
        let flags =
            MsFlags::MS_NOSUID | MsFlags::MS_NODEV | MsFlags::MS_NOATIME | MsFlags::MS_RDONLY;

        let file = fuse_kern_mount(&self.mountpoint, &self.fsname, &self.subtype, flags)?;
        fcntl(file.as_raw_fd(), FcntlArg::F_SETFL(OFlag::O_NONBLOCK))
            .map_err(|e| SessionFailure(format!("set fd nonblocking: {}", e)))?;
        self.file = Some(file);

        Ok(())
    }

    /// Expose the associated fuse session file descriptor.
    ///
    /// Does not transfer FUSE session fd. Caller MUST NOT close the fd after getting it.
    pub fn get_fuse_fd(&mut self) -> Option<RawFd> {
        self.file.as_ref().map(|file| file.as_raw_fd())
    }

    /// Force setting the associated FUSE session file descriptor.
    ///
    /// Takes ownership of the fd. Caller MUST NOT close the fd after setting it.
    pub fn set_fuse_fd(&mut self, fd: RawFd) {
        self.file = Some(unsafe { File::from_raw_fd(fd) });
    }

    /// Destroy a fuse session.
    pub fn umount(&mut self) -> Result<()> {
        if let Some(file) = self.file.take() {
            // safe to unwrap as mountpoint was valid string otherwise mount fails
            fuse_kern_umount(self.mountpoint.to_str().unwrap(), file)
        } else {
            Ok(())
        }
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

    /// Create a new fuse message channel.
    pub fn new_channel(&self, evtfd: EventFd) -> Result<FuseChannel> {
        if let Some(file) = &self.file {
            FuseChannel::new(file.as_raw_fd(), evtfd, self.bufsize)
        } else {
            Err(SessionFailure("invalid fuse session".to_string()))
        }
    }
}

impl Drop for FuseSession {
    fn drop(&mut self) {
        let _ = self.umount();
    }
}

/// A fuse channel abstruction. Each session can hold multiple channels.
pub struct FuseChannel {
    fd: RawFd,
    epoll_fd: RawFd,
    buf: Vec<u8>,
    bufsize: usize,
    events: RefCell<Vec<Event>>,
}

fn register_event(epoll_fd: c_int, fd: RawFd, evt: Events, data: u64) -> Result<()> {
    let event = Event::new(evt, data);
    epoll::ctl(epoll_fd, ControlOptions::EPOLL_CTL_ADD, fd, event)
        .map_err(|e| SessionFailure(format!("epoll add error: {}", e)))
}

impl FuseChannel {
    fn new(fd: RawFd, evtfd: EventFd, bufsize: usize) -> Result<Self> {
        const EPOLL_EVENTS_LEN: usize = 100;
        let epoll_fd =
            epoll::create(true).map_err(|e| SessionFailure(format!("epoll create: {}", e)))?;

        register_event(epoll_fd, fd, Events::EPOLLIN, FUSE_DEV_EVENT)
            .map_err(|e| SessionFailure(format!("epoll register session fd: {}", e)))?;
        register_event(
            epoll_fd,
            evtfd.as_raw_fd(),
            Events::EPOLLIN,
            EXIT_FUSE_EVENT,
        )
        .map_err(|e| SessionFailure(format!("epoll register exit fd: {}", e)))?;

        Ok(FuseChannel {
            fd: dup(fd).map_err(|e| SessionFailure(format!("dup fd: {}", e)))?,
            epoll_fd,
            buf: vec![0x0u8; bufsize],
            bufsize,
            events: RefCell::new(vec![Event::new(Events::empty(), 0); EPOLL_EVENTS_LEN]),
        })
    }

    /// Get next available FUSE request from the underlying fuse device file.
    ///
    /// Returns:
    /// - Ok(None): signal has pending on the exiting event channel
    /// - Ok(Some((reader, writer))): reader to receive request and writer to send reply
    /// - Err(e): error message
    pub fn get_request(&mut self) -> Result<Option<(Reader, Writer)>> {
        loop {
            let num_events = epoll::wait(self.epoll_fd, -1, &mut self.events.borrow_mut())
                .map_err(|e| SessionFailure(format!("epoll wait: {}", e)))?;

            for event in self.events.borrow().iter().take(num_events) {
                let evset = match epoll::Events::from_bits(event.events) {
                    Some(evset) => evset,
                    None => {
                        let evbits = event.events;
                        warn!("epoll: ignoring unknown event set: 0x{:x}", evbits);
                        continue;
                    }
                };

                match evset {
                    Events::EPOLLIN => {
                        match event.data {
                            EXIT_FUSE_EVENT => {
                                // Directly returning from here is reliable as we handle only one
                                // epoll event which is `Read` or `Exit`.
                                // One more trick, we don't read the event fd so as to make all
                                // fuse threads exit. It relies on a LEVEL triggered event fd.
                                info!("Will exit from fuse service");
                                return Ok(None);
                            }
                            FUSE_DEV_EVENT => {
                                match read(self.fd, &mut self.buf) {
                                    Ok(len) => {
                                        let reader =
                                            Reader::new(FuseBuf::new(&mut self.buf[..len]))
                                                .map_err(|e| {
                                                    SessionFailure(format!(
                                                        "new read buffer: {}",
                                                        e
                                                    ))
                                                })?;
                                        let writer = Writer::new(self.fd, self.bufsize).unwrap();
                                        return Ok(Some((reader, writer)));
                                    }
                                    Err(nixError::Sys(e)) => match e {
                                        Errno::ENOENT => {
                                            // ENOENT means the operation was interrupted, it's safe
                                            // to restart
                                            trace!("restart reading");
                                            continue;
                                        }
                                        Errno::EAGAIN | Errno::EINTR => {
                                            continue;
                                        }
                                        Errno::ENODEV => {
                                            info!("fuse filesystem umounted");
                                            return Ok(None);
                                        }
                                        e => {
                                            warn! {"read fuse dev failed on fd {}: {}", self.fd, e};
                                            return Err(SessionFailure(format!(
                                                "read new request: {:?}",
                                                e
                                            )));
                                        }
                                    },
                                    Err(e) => {
                                        return Err(SessionFailure(format!("epoll error: {}", e)));
                                    }
                                }
                            }
                            x => {
                                error!("unexpected epoll event");
                                return Err(SessionFailure(format!(
                                    "unexpected epoll event: {}",
                                    x,
                                )));
                            }
                        }
                    }
                    x if (Events::EPOLLERR | Events::EPOLLHUP).contains(x) => {
                        info!("FUSE channel already closed!");
                        return Err(SessionFailure("epoll error".to_string()));
                    }
                    _ => {
                        // We should not step into this branch as other event is not registered.
                        continue;
                    }
                }
            }
        }
    }
}

impl Drop for FuseChannel {
    fn drop(&mut self) {
        let _ = close(self.fd);
    }
}

/// Safe wrapper for `sysconf(_SC_PAGESIZE)`.
#[inline(always)]
fn pagesize() -> usize {
    // Trivially safe
    unsafe { sysconf(_SC_PAGESIZE) as usize }
}

/// Mount a fuse file system
fn fuse_kern_mount(mountpoint: &Path, fsname: &str, subtype: &str, flags: MsFlags) -> Result<File> {
    let file = OpenOptions::new()
        .create(false)
        .read(true)
        .write(true)
        .open(FUSE_DEVICE)
        .map_err(|e| SessionFailure(format!("open {}: {}", FUSE_DEVICE, e)))?;
    let meta = mountpoint
        .metadata()
        .map_err(|e| SessionFailure(format!("stat {:?}: {}", mountpoint, e)))?;
    let opts = format!(
        "default_permissions,allow_other,fd={},rootmode={:o},user_id={},group_id={}",
        file.as_raw_fd(),
        meta.permissions().mode() & libc::S_IFMT,
        getuid(),
        getgid(),
    );
    let mut fstype = String::from(FUSE_FSTYPE);
    if !subtype.is_empty() {
        fstype.push('.');
        fstype.push_str(subtype);
    }

    info!(
        "mount source {} dest {} with fstype {} opts {} fd {}",
        fsname,
        mountpoint.to_str().unwrap(),
        fstype,
        opts,
        file.as_raw_fd(),
    );
    mount(
        Some(fsname),
        mountpoint,
        Some(fstype.deref()),
        flags,
        Some(opts.deref()),
    )
    .map_err(|e| SessionFailure(format!("failed to mount {:?}: {}", mountpoint, e)))?;

    Ok(file)
}

/// Umount a fuse file system
fn fuse_kern_umount(mountpoint: &str, file: File) -> Result<()> {
    let mut fds = [PollFd::new(file.as_raw_fd(), PollFlags::empty())];

    if poll(&mut fds, 0).is_ok() {
        // POLLERR means the file system is already umounted,
        // or the connection has been aborted via /sys/fs/fuse/connections/NNN/abort
        if let Some(event) = fds[0].revents() {
            if event == PollFlags::POLLERR {
                return Ok(());
            }
        }
    }

    // Drop to close fuse session fd, otherwise synchronous umount can recurse into filesystem and
    // cause deadlock.
    drop(file);
    umount2(mountpoint, MntFlags::MNT_DETACH)
        .map_err(|e| SessionFailure(format!("failed to umount {}: {}", mountpoint, e)))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::Path;
    use vmm_sys_util::tempdir::TempDir;

    #[test]
    fn test_new_session() {
        let se = FuseSession::new(Path::new("haha"), "foo", "bar");
        assert!(se.is_err());

        let dir = TempDir::new().unwrap();
        let se = FuseSession::new(dir.as_path(), "foo", "bar");
        assert!(se.is_ok());
    }

    #[test]
    fn test_new_channel() {
        // invalid session fd
        let ch = FuseChannel::new(30294, EventFd::new(0).unwrap(), 3);
        assert!(ch.is_err());

        let ch = FuseChannel::new(
            EventFd::new(0).unwrap().as_raw_fd(),
            EventFd::new(0).unwrap(),
            3,
        );
        assert!(ch.is_ok());
    }
}
