// Copyright 2020-2021 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! FUSE session management.
//!
//! A FUSE channel is a FUSE request handling context that takes care of handling FUSE requests
//! sequentially. A FUSE session is a connection from a FUSE mountpoint to a FUSE server daemon.
//! A FUSE session can have multiple FUSE channels so that FUSE requests are handled in parallel.

use std::fs::{File, OpenOptions};
use std::ops::Deref;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::io::AsRawFd;
use std::path::{Path, PathBuf};

use libc::{sysconf, _SC_PAGESIZE};
use nix::errno::Errno;
use nix::fcntl::{fcntl, FcntlArg, OFlag};
use nix::mount::{mount, umount2, MntFlags, MsFlags};
use nix::poll::{poll, PollFd, PollFlags};
use nix::unistd::{getgid, getuid, read};
use nix::Error as nixError;
use vmm_sys_util::eventfd::EventFd;
use vmm_sys_util::poll::{PollContext, WatchingEvents};

use super::{Error::SessionFailure, FuseBuf, Reader, Result, Writer};

// These follows definition from libfuse.
const FUSE_KERN_BUF_SIZE: usize = 256;
const FUSE_HEADER_SIZE: usize = 0x1000;

const FUSE_DEVICE: &str = "/dev/fuse";
const FUSE_FSTYPE: &str = "fuse";

const FUSE_DEV_EVENT: u32 = 0;
const EXIT_FUSE_EVENT: u32 = 1;

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

    /// Expose the associated FUSE session file.
    pub fn get_fuse_file(&mut self) -> Option<&File> {
        self.file.as_ref()
    }

    /// Force setting the associated FUSE session file.
    pub fn set_fuse_file(&mut self, file: File) {
        self.file = Some(file);
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
            let file = file
                .try_clone()
                .map_err(|e| SessionFailure(format!("dup fd: {}", e)))?;
            FuseChannel::new(file, evtfd, self.bufsize)
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
    file: File,
    poll_ctx: PollContext<u32>,
    bufsize: usize,
    buf: Vec<u8>,
}

impl FuseChannel {
    fn new(file: File, evtfd: EventFd, bufsize: usize) -> Result<Self> {
        let poll_ctx =
            PollContext::new().map_err(|e| SessionFailure(format!("epoll create: {}", e)))?;

        poll_ctx
            .add_fd_with_events(&file, WatchingEvents::empty().set_read(), FUSE_DEV_EVENT)
            .map_err(|e| SessionFailure(format!("epoll register session fd: {}", e)))?;
        poll_ctx
            .add_fd_with_events(&evtfd, WatchingEvents::empty().set_read(), EXIT_FUSE_EVENT)
            .map_err(|e| SessionFailure(format!("epoll register exit fd: {}", e)))?;

        Ok(FuseChannel {
            file,
            poll_ctx,
            bufsize,
            buf: vec![0x0u8; bufsize],
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
            let events = self
                .poll_ctx
                .wait()
                .map_err(|e| SessionFailure(format!("epoll wait: {}", e)))?;

            for event in events.iter() {
                if event.readable() {
                    let fd = self.file.as_raw_fd();
                    match event.token() {
                        EXIT_FUSE_EVENT => {
                            // Directly returning from here is reliable as we handle only one
                            // epoll event which is `Read` or `Exit`.
                            // One more trick, we don't read the event fd so as to make all
                            // fuse threads exit. It relies on a LEVEL triggered event fd.
                            info!("Will exit from fuse service");
                            return Ok(None);
                        }
                        FUSE_DEV_EVENT => {
                            match read(fd, &mut self.buf) {
                                Ok(len) => {
                                    let reader = Reader::new(FuseBuf::new(&mut self.buf[..len])).unwrap();
                                    let writer = Writer::new(fd, self.bufsize).unwrap();
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
                                        warn! {"read fuse dev failed on fd {}: {}", fd, e};
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
                            return Err(SessionFailure(format!("unexpected epoll event: {}", x,)));
                        }
                    }
                } else if event.hungup()
                /*|| event.has_error()*/ // TODO: upgrade to vmm-sys-util v0.8.0
                {
                    info!("FUSE channel already closed!");
                    return Err(SessionFailure("epoll error".to_string()));
                } else {
                    // We should not step into this branch as other event is not registered.
                    panic!("unknown epoll result events");
                }
            }
        }
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
    use vmm_sys_util::tempfile::TempFile;

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
        let ch = FuseChannel::new(
            TempFile::new().unwrap().into_file(),
            EventFd::new(0).unwrap(),
            3,
        );
        assert!(ch.is_ok());
    }
}
