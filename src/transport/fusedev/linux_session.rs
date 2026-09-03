// Copyright 2020-2022 Ant Group. All rights reserved.
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
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use crate::transport::fusedev::{FuseChannelExt, FuseSessionExt};
use mio::{Events, Poll, Token, Waker};
use nix::errno::Errno;
use nix::fcntl::{fcntl, FcntlArg, FdFlag, OFlag};
use nix::mount::{mount, umount2, MntFlags, MsFlags};
use nix::poll::{poll, PollFd, PollFlags};
use nix::sys::epoll::{epoll_ctl, EpollEvent, EpollFlags, EpollOp};
use nix::unistd::{getgid, getuid, read};

use super::{
    super::pagesize,
    Error::{IoError, SessionFailure},
    FuseBuf, FuseDevWriter, Reader, Result, FUSE_HEADER_SIZE, FUSE_KERN_BUF_PAGES,
};

// These follows definition from libfuse.
//
// Each channel registers exactly two tokens with its epoll instance (the exit
// waker and the fuse device fd), so a single `poll` can return at most two
// events. The event buffer is reused across requests (see `FuseChannel`), so a
// small fixed capacity is enough; 8 leaves ample headroom while keeping the
// buffer tiny instead of libfuse's 1024-entry (~12KB) allocation.
const POLL_EVENTS_CAPACITY: usize = 8;

const FUSE_DEVICE: &str = "/dev/fuse";
const FUSE_FSTYPE: &str = "fuse";
const FUSERMOUNT_BIN: &str = "fusermount3";

const EXIT_FUSE_EVENT: Token = Token(0);
const FUSE_DEV_EVENT: Token = Token(1);

/// A fuse session manager to manage the connection with the in kernel fuse driver.
pub struct FuseSession {
    mountpoint: PathBuf,
    fsname: String,
    subtype: String,
    file: Option<File>,
    // Socket to keep alive / drop for fusermount's auto_unmount.
    keep_alive: Option<UnixStream>,
    bufsize: usize,
    readonly: bool,
    wakers: Mutex<Vec<Arc<Waker>>>,
    auto_unmount: bool,
    allow_other: bool,
    target_mntns: Option<libc::pid_t>,
    // fusermount binary, default to fusermount3
    fusermount: String,
    mount_flags: Option<MsFlags>,
}

impl FuseSession {
    /// Create a new fuse session, without mounting/connecting to the in kernel fuse driver.
    pub fn new(
        mountpoint: &Path,
        fsname: &str,
        subtype: &str,
        readonly: bool,
    ) -> Result<FuseSession> {
        FuseSession::new_with_autounmount(mountpoint, fsname, subtype, readonly, false)
    }

    /// Create a new fuse session, without mounting/connecting to the in kernel fuse driver.
    pub fn new_with_autounmount(
        mountpoint: &Path,
        fsname: &str,
        subtype: &str,
        readonly: bool,
        auto_unmount: bool,
    ) -> Result<FuseSession> {
        let dest = mountpoint
            .canonicalize()
            .map_err(|_| SessionFailure(format!("invalid mountpoint {mountpoint:?}")))?;
        if !dest.is_dir() {
            return Err(SessionFailure(format!("{dest:?} is not a directory")));
        }

        Ok(FuseSession {
            mountpoint: dest,
            fsname: fsname.to_owned(),
            subtype: subtype.to_owned(),
            file: None,
            keep_alive: None,
            bufsize: FUSE_KERN_BUF_PAGES * pagesize() + FUSE_HEADER_SIZE,
            readonly,
            wakers: Mutex::new(Vec::new()),
            auto_unmount,
            target_mntns: None,
            fusermount: FUSERMOUNT_BIN.to_string(),
            allow_other: true,
            mount_flags: None,
        })
    }

    /// Set the target pid of mount namespace of the fuse session mount, the fuse will be mounted
    /// under the given mnt ns.
    pub fn set_target_mntns(&mut self, pid: Option<libc::pid_t>) {
        self.target_mntns = pid;
    }

    /// Set fusermount binary, default to fusermount3.
    pub fn set_fusermount(&mut self, bin: &str) {
        self.fusermount = bin.to_string();
    }

    /// Set the allow_other mount option. This allows other users than the one mounting the
    /// filesystem to access the filesystem. However, this option is usually restricted to the root
    /// user unless configured otherwise.
    pub fn set_allow_other(&mut self, allow_other: bool) {
        self.allow_other = allow_other;
    }

    /// Get current fusermount binary.
    pub fn get_fusermount(&self) -> &str {
        self.fusermount.as_str()
    }

    /// Expose the associated FUSE session file.
    pub fn get_fuse_file(&self) -> Option<&File> {
        self.file.as_ref()
    }

    /// Force setting the associated FUSE session file.
    pub fn set_fuse_file(&mut self, file: File) {
        self.file = Some(file);
    }

    /// Set custom mount flags for the session.
    /// If not set, default flags (MS_NOSUID | MS_NODEV | MS_NOATIME) will be
    /// used. MS_RDONLY will be added automatically if the session is readonly.
    /// Not setting MS_NOSUID and MS_NODEV will probably get ignored by
    /// fusermount3 for security reasons, so it means you need to be root to
    /// mount the FS.
    pub fn set_mount_flags(&mut self, flags: MsFlags) {
        self.mount_flags = Some(flags);
    }

    /// Get the currently configured mount flags, or None if using defaults.
    pub fn get_mount_flags(&self) -> Option<MsFlags> {
        self.mount_flags
    }

    /// Clone fuse file using ioctl FUSE_DEV_IOC_CLONE.
    pub fn clone_fuse_file(&self) -> Result<File> {
        let mut old_fd = self
            .file
            .as_ref()
            .ok_or(SessionFailure(
                "fuse session file doesn't exist".to_string(),
            ))?
            .as_raw_fd();

        let cloned_file = OpenOptions::new()
            .create(false)
            .read(true)
            .write(true)
            .open(FUSE_DEVICE)
            .map_err(|e| SessionFailure(format!("open {FUSE_DEVICE}: {e}")))?;

        // define the function which invokes "ioctl FUSE_DEV_IOC_CLONE"
        // refer: https://github.com/torvalds/linux/blob/c42d9eeef8e5ba9292eda36fd8e3c11f35ee065c/include/uapi/linux/fuse.h#L1051-L1052
        // #define FUSE_DEV_IOC_MAGIC   229
        // #define FUSE_DEV_IOC_CLONE   _IOR(FUSE_DEV_IOC_MAGIC, 0, uint32_t)
        nix::ioctl_read!(clone_fuse_fd, 229, 0, i32);

        unsafe { clone_fuse_fd(cloned_file.as_raw_fd(), (&mut old_fd) as *mut i32) }
            .map_err(|e| SessionFailure(format!("failed to clone fuse file: {:?}", e)))?;

        Ok(cloned_file)
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
    pub fn mount(&mut self) -> Result<()> {
        let mut flags = self
            .mount_flags
            .unwrap_or(MsFlags::MS_NOSUID | MsFlags::MS_NODEV | MsFlags::MS_NOATIME);
        if self.readonly {
            flags |= MsFlags::MS_RDONLY;
        }
        let (file, socket) = fuse_kern_mount(
            &self.mountpoint,
            &self.fsname,
            &self.subtype,
            flags,
            self.auto_unmount,
            self.allow_other,
            self.target_mntns,
            &self.fusermount,
        )?;

        fcntl(file.as_raw_fd(), FcntlArg::F_SETFL(OFlag::O_NONBLOCK))
            .map_err(|e| SessionFailure(format!("set fd nonblocking: {e}")))?;
        self.file = Some(file);
        self.keep_alive = socket;

        Ok(())
    }

    /// Destroy a fuse session.
    pub fn umount(&mut self) -> Result<()> {
        // If we have a keep_alive socket, just drop it,
        // and let fusermount do the unmount.
        if let (None, Some(file)) = (self.keep_alive.take(), self.file.take()) {
            if let Some(mountpoint) = self.mountpoint.to_str() {
                fuse_kern_umount(mountpoint, file, self.fusermount.as_str())
            } else {
                Err(SessionFailure("invalid mountpoint".to_string()))
            }
        } else {
            Ok(())
        }
    }

    /// Create a new fuse message channel.
    pub fn new_channel(&self) -> Result<FuseChannel> {
        if let Some(file) = &self.file {
            let file = file
                .try_clone()
                .map_err(|e| SessionFailure(format!("dup fd: {e}")))?;
            let channel = FuseChannel::new(file, self.bufsize)?;
            let waker = channel.get_waker();
            self.add_waker(waker)?;

            Ok(channel)
        } else {
            Err(SessionFailure("invalid fuse session".to_string()))
        }
    }

    /// Create a new blocking fuse message channel.
    ///
    /// The channel receives requests with plain blocking reads on a fuse
    /// device fd cloned with `FUSE_DEV_IOC_CLONE`, saving the `epoll_wait`
    /// syscall per request that [`Self::new_channel()`] pays.
    ///
    /// Note: blocking channels are not woken by [`Self::wake()`]; they exit
    /// when the fuse session is umounted (the pending read returns `ENODEV`).
    /// Requires kernel support for `FUSE_DEV_IOC_CLONE` (kernel >= 4.2).
    pub fn new_blocking_channel(&self) -> Result<BlockingFuseChannel> {
        let file = self.clone_fuse_file()?;
        Ok(BlockingFuseChannel::new(file, self.bufsize))
    }

    /// Wake channel loop and exit
    pub fn wake(&self) -> Result<()> {
        let wakers = self
            .wakers
            .lock()
            .map_err(|e| SessionFailure(format!("lock wakers: {e}")))?;
        for waker in wakers.iter() {
            waker
                .wake()
                .map_err(|e| SessionFailure(format!("wake channel: {e}")))?;
        }
        Ok(())
    }

    fn add_waker(&self, waker: Arc<Waker>) -> Result<()> {
        let mut wakers = self
            .wakers
            .lock()
            .map_err(|e| SessionFailure(format!("lock wakers: {e}")))?;
        wakers.push(waker);
        Ok(())
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
/// Each session can hold multiple channels.
pub struct FuseChannel {
    file: File,
    poll: Poll,
    waker: Arc<Waker>,
    buf: Vec<u8>,
    events: Events,
}

impl FuseChannel {
    fn new(file: File, bufsize: usize) -> Result<Self> {
        let poll = Poll::new().map_err(|e| SessionFailure(format!("epoll create: {e}")))?;
        let waker = Waker::new(poll.registry(), EXIT_FUSE_EVENT)
            .map_err(|e| SessionFailure(format!("epoll register session fd: {e}")))?;
        let waker = Arc::new(waker);

        // mio default add EPOLLET to event flags, so epoll will use edge-triggered mode.
        // It may let poll miss some event, so manually register the fd with only EPOLLIN flag
        // to use level-triggered mode.
        //
        // Also request EPOLLEXCLUSIVE: a session hands out channels over the
        // *same* fuse device fd (via `try_clone`), so without it one arriving
        // request makes every channel's `epoll_wait` report readable and they
        // all race into `read()`, where all but one get `EAGAIN` and re-poll
        // (thundering herd). EPOLLEXCLUSIVE makes the kernel wake a single
        // waiting channel per event instead. It requires level-triggered mode
        // (which we use) and kernel >= 4.5; older kernels reject the flag with
        // EINVAL, so fall back to a plain EPOLLIN registration there.
        let epoll = poll.as_raw_fd();
        let fd = file.as_raw_fd();
        let mut event = EpollEvent::new(
            EpollFlags::EPOLLIN | EpollFlags::EPOLLEXCLUSIVE,
            usize::from(FUSE_DEV_EVENT) as u64,
        );
        match epoll_ctl(epoll, EpollOp::EpollCtlAdd, fd, Some(&mut event)) {
            Ok(_) => {}
            Err(Errno::EINVAL) => {
                // Kernel < 4.5: EPOLLEXCLUSIVE is unsupported, retry without it.
                event = EpollEvent::new(EpollFlags::EPOLLIN, usize::from(FUSE_DEV_EVENT) as u64);
                epoll_ctl(epoll, EpollOp::EpollCtlAdd, fd, Some(&mut event))
                    .map_err(|e| SessionFailure(format!("epoll register channel fd: {e}")))?;
            }
            Err(e) => return Err(SessionFailure(format!("epoll register channel fd: {e}"))),
        }

        Ok(FuseChannel {
            file,
            poll,
            waker,
            buf: vec![0x0u8; bufsize],
            events: Events::with_capacity(POLL_EVENTS_CAPACITY),
        })
    }

    fn get_waker(&self) -> Arc<Waker> {
        self.waker.clone()
    }

    /// Get next available FUSE request from the underlying fuse device file.
    ///
    /// Returns:
    /// - Ok(None): signal has pending on the exiting event channel
    /// - Ok(Some((reader, writer))): reader to receive request and writer to send reply
    /// - Err(e): error message
    pub fn get_request(&mut self) -> Result<Option<(Reader<'_>, FuseDevWriter<'_>)>> {
        let mut need_exit = false;
        loop {
            let mut fusereq_available = false;
            match self.poll.poll(&mut self.events, None) {
                Ok(_) => {}
                Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(SessionFailure(format!("epoll wait: {e}"))),
            }

            for event in self.events.iter() {
                // We will handle errors when reading from the fuse device
                if event.is_readable() || event.is_error() {
                    match event.token() {
                        EXIT_FUSE_EVENT => need_exit = true,
                        FUSE_DEV_EVENT => fusereq_available = true,
                        x => {
                            error!("unexpected epoll event");
                            return Err(SessionFailure(format!("unexpected epoll event: {}", x.0)));
                        }
                    }
                } else {
                    // We should not step into this branch as other event is not registered.
                    panic!("unknown epoll result events");
                }
            }

            // Handle wake up event first. We don't read the event fd so that a LEVEL triggered
            // event can still be delivered to other threads/daemons.
            if need_exit {
                debug!("Will exit from fuse service");
                return Ok(None);
            }
            if fusereq_available {
                let fd = self.file.as_raw_fd();
                match read(fd, &mut self.buf) {
                    Ok(len) => {
                        // ###############################################
                        // Note: it's a heavy hack to reuse the same underlying data
                        // buffer for both Reader and Writer, in order to reduce memory
                        // consumption. Here we assume Reader won't be used anymore once
                        // we start to write to the Writer. To get rid of this hack,
                        // just allocate a dedicated data buffer for Writer.
                        let buf = unsafe {
                            std::slice::from_raw_parts_mut(self.buf.as_mut_ptr(), self.buf.len())
                        };
                        // Reader::new() and Writer::new() should always return success.
                        let reader =
                            Reader::from_fuse_buffer(FuseBuf::new(&mut self.buf[..len])).unwrap();
                        let writer = FuseDevWriter::new(fd, buf).unwrap();
                        return Ok(Some((reader, writer)));
                    }
                    Err(e) => match e {
                        Errno::ENOENT => {
                            // ENOENT means the operation was interrupted, it's safe to restart
                            trace!("restart reading due to ENOENT");
                            continue;
                        }
                        Errno::EAGAIN => {
                            trace!("restart reading due to EAGAIN");
                            continue;
                        }
                        Errno::EINTR => {
                            trace!("syscall interrupted");
                            continue;
                        }
                        Errno::ENODEV => {
                            debug!("got ENODEV when reading fuse fd, assuming fuse filesystem was umounted.");
                            return Ok(None);
                        }
                        e => {
                            warn! {"read fuse dev failed on fd {}: {}", fd, e};
                            return Err(SessionFailure(format!("read new request: {e:?}")));
                        }
                    },
                }
            }
        }
    }
}

/// A fuse channel that receives requests with plain blocking reads.
///
/// Compared to [`FuseChannel`], this channel saves the `epoll_wait` syscall
/// per request by reading the fuse device fd directly, at the cost of losing
/// wakeup-based shutdown: [`FuseSession::wake()`] has no effect on blocking
/// channels. A blocking channel exits instead when the fuse connection is
/// torn down (unmount or abort), which makes the pending read fail with
/// `ENODEV` and [`Self::get_request()`] return `Ok(None)`.
///
/// Blocking channels are created from a fuse device fd cloned with
/// `FUSE_DEV_IOC_CLONE`, which has its own file description and is thus
/// unaffected by the `O_NONBLOCK` flag set on the session fd.
pub struct BlockingFuseChannel {
    file: File,
    buf: Vec<u8>,
}

impl BlockingFuseChannel {
    fn new(file: File, bufsize: usize) -> Self {
        BlockingFuseChannel {
            file,
            buf: vec![0x0u8; bufsize],
        }
    }

    /// Get next available FUSE request from the underlying fuse device file.
    ///
    /// Blocks until a request arrives or the fuse connection is torn down.
    ///
    /// Returns:
    /// - Ok(None): the fuse session has been umounted or aborted
    /// - Ok(Some((reader, writer))): reader to receive request and writer to send reply
    /// - Err(e): error message
    pub fn get_request(&mut self) -> Result<Option<(Reader<'_>, FuseDevWriter<'_>)>> {
        loop {
            let fd = self.file.as_raw_fd();
            match read(fd, &mut self.buf) {
                Ok(len) => {
                    // ###############################################
                    // Note: it's a heavy hack to reuse the same underlying data
                    // buffer for both Reader and Writer, in order to reduce memory
                    // consumption. Here we assume Reader won't be used anymore once
                    // we start to write to the Writer. To get rid of this hack,
                    // just allocate a dedicated data buffer for Writer.
                    let buf = unsafe {
                        std::slice::from_raw_parts_mut(self.buf.as_mut_ptr(), self.buf.len())
                    };
                    // Reader::new() and Writer::new() should always return success.
                    let reader =
                        Reader::from_fuse_buffer(FuseBuf::new(&mut self.buf[..len])).unwrap();
                    let writer = FuseDevWriter::new(fd, buf).unwrap();
                    return Ok(Some((reader, writer)));
                }
                Err(e) => match e {
                    Errno::ENOENT => {
                        // ENOENT means the operation was interrupted, it's safe to restart
                        trace!("restart reading due to ENOENT");
                        continue;
                    }
                    Errno::EINTR => {
                        trace!("syscall interrupted");
                        continue;
                    }
                    Errno::ENODEV => {
                        debug!("got ENODEV when reading fuse fd, assuming fuse filesystem was umounted.");
                        return Ok(None);
                    }
                    // No EAGAIN arm on purpose: unlike `FuseChannel`, this fd is
                    // blocking (cloned via FUSE_DEV_IOC_CLONE, see the type docs),
                    // and the kernel only returns EAGAIN from a fuse device read
                    // for O_NONBLOCK file descriptions, so it cannot happen here.
                    e => {
                        warn! {"read fuse dev failed on fd {}: {}", fd, e};
                        return Err(SessionFailure(format!("read new request: {e:?}")));
                    }
                },
            }
        }
    }
}

impl FuseChannelExt for FuseChannel {
    fn next_request(&mut self) -> Result<Option<(Reader<'_>, FuseDevWriter<'_>)>> {
        FuseChannel::get_request(self)
    }
}

impl FuseChannelExt for BlockingFuseChannel {
    fn next_request(&mut self) -> Result<Option<(Reader<'_>, FuseDevWriter<'_>)>> {
        BlockingFuseChannel::get_request(self)
    }
}

/// Mount a fuse file system
#[allow(clippy::too_many_arguments)]
fn fuse_kern_mount(
    mountpoint: &Path,
    fsname: &str,
    subtype: &str,
    flags: MsFlags,
    auto_unmount: bool,
    allow_other: bool,
    target_mntns: Option<libc::pid_t>,
    fusermount: &str,
) -> Result<(File, Option<UnixStream>)> {
    let file = OpenOptions::new()
        .create(false)
        .read(true)
        .write(true)
        .open(FUSE_DEVICE)
        .map_err(|e| SessionFailure(format!("open {FUSE_DEVICE}: {e}")))?;
    let meta = mountpoint
        .metadata()
        .map_err(|e| SessionFailure(format!("stat {mountpoint:?}: {e}")))?;
    // the current implementation of fuse-backend-rs uses a fixed buffer to store the fuse response,
    // the default value of this buffer is as follows, but in fact, the kernel in the direct io path,
    // the size of the request may be larger than the length of this buffer (this is determined by
    // the max_read option to determine the maximum size of kernel requests, the default value is
    // a very large number), which leads to the buffer is not enough to fill the read content,
    // resulting in read failure. so here we limit the size of max_read to the length of our buffer,
    // so that the fuse kernel will not send requests that exceed the length of the buffer.
    // in virtiofs scene max_read can't be adjusted, his default is UINT_MAX, but we don't have to
    // worry about it, because the buffer is allocated by the kernel driver, we just use this buffer
    // to fill the response, so we don't need to do any adjustment.
    let max_read = FUSE_KERN_BUF_PAGES * pagesize() + FUSE_HEADER_SIZE;

    let mut opts = format!(
        "default_permissions,fd={},rootmode={:o},user_id={},group_id={},max_read={}",
        file.as_raw_fd(),
        meta.permissions().mode() & libc::S_IFMT,
        getuid(),
        getgid(),
        max_read
    );
    if allow_other {
        opts.push_str(",allow_other");
    }
    let mut fstype = String::from(FUSE_FSTYPE);
    if !subtype.is_empty() {
        fstype.push('.');
        fstype.push_str(subtype);
    }

    if let Some(mountpoint) = mountpoint.to_str() {
        debug!(
            "mount source {} dest {} with fstype {} opts {} fd {}",
            fsname,
            mountpoint,
            fstype,
            opts,
            file.as_raw_fd(),
        );
    }

    // mount in another mntns requires mounting with fusermount, which is a new process, as
    // multithreaded program is not allowed to join to another mntns, and the process running fuse
    // session might be multithreaded.
    if auto_unmount || target_mntns.is_some() {
        fuse_fusermount_mount(
            mountpoint,
            fsname,
            subtype,
            opts,
            flags,
            auto_unmount,
            target_mntns,
            fusermount,
        )
    } else {
        match mount(
            Some(fsname),
            mountpoint,
            Some(fstype.deref()),
            flags,
            Some(opts.deref()),
        ) {
            Ok(()) => Ok((file, None)),
            Err(Errno::EPERM) => fuse_fusermount_mount(
                mountpoint,
                fsname,
                subtype,
                opts,
                flags,
                auto_unmount,
                target_mntns,
                fusermount,
            ),
            Err(e) => Err(SessionFailure(format!(
                "failed to mount {mountpoint:?}: {e}"
            ))),
        }
    }
}

fn msflags_to_string(flags: MsFlags) -> String {
    [
        (MsFlags::MS_RDONLY, ("rw", "ro")),
        (MsFlags::MS_NOSUID, ("suid", "nosuid")),
        (MsFlags::MS_NODEV, ("dev", "nodev")),
        (MsFlags::MS_NOEXEC, ("exec", "noexec")),
        (MsFlags::MS_SYNCHRONOUS, ("async", "sync")),
        (MsFlags::MS_NOATIME, ("atime", "noatime")),
    ]
    .map(
        |(flag, (neg, pos))| {
            if flags.contains(flag) {
                pos
            } else {
                neg
            }
        },
    )
    .join(",")
}

/// Mount a fuse file system with fusermount
#[allow(clippy::too_many_arguments)]
fn fuse_fusermount_mount(
    mountpoint: &Path,
    fsname: &str,
    subtype: &str,
    opts: String,
    flags: MsFlags,
    auto_unmount: bool,
    target_mntns: Option<libc::pid_t>,
    fusermount: &str,
) -> Result<(File, Option<UnixStream>)> {
    let mut opts = vec![format!("fsname={fsname}"), opts, msflags_to_string(flags)];
    if !subtype.is_empty() {
        opts.push(format!("subtype={subtype}"));
    }
    if auto_unmount {
        opts.push("auto_unmount".to_owned());
    }
    let opts = opts.join(",");

    let (send, recv) = UnixStream::pair().unwrap();

    // Keep the sending socket around after exec to pass to fusermount.
    // When its partner recv closes, fusermount will unmount.
    // Remove the close-on-exec flag from the socket, so we can pass it to
    // fusermount.
    fcntl(send.as_raw_fd(), FcntlArg::F_SETFD(FdFlag::empty()))
        .map_err(|e| SessionFailure(format!("Failed to remove close-on-exec flag: {e}")))?;

    let mut cmd = match target_mntns {
        Some(pid) => {
            let mut c = std::process::Command::new("nsenter");
            c.arg("-t")
                .arg(format!("{}", pid))
                .arg("-m")
                .arg(fusermount);
            c
        }
        None => std::process::Command::new(fusermount),
    };
    // Old version of fusermount doesn't support long --options, yet.
    let mut proc = cmd
        .env("_FUSE_COMMFD", format!("{}", send.as_raw_fd()))
        .arg("-o")
        .arg(opts)
        .arg("--")
        .arg(mountpoint)
        .spawn()
        .map_err(IoError)?;

    if auto_unmount {
        std::thread::spawn(move || {
            let _ = proc.wait();
        });
    } else {
        match proc.wait().map_err(IoError)?.code() {
            Some(0) => {}
            exit_code => {
                return Err(SessionFailure(format!(
                    "Unexpected exit code when running fusermount: {exit_code:?}"
                )))
            }
        }
    }
    drop(send);

    match vmm_sys_util::sock_ctrl_msg::ScmSocket::recv_with_fd(&recv, &mut [0u8; 8]).map_err(
        |e| {
            SessionFailure(format!(
                "Unexpected error when receiving fuse file descriptor from fusermount: {}",
                e
            ))
        },
    )? {
        (_recv_bytes, Some(file)) => Ok((file, if auto_unmount { Some(recv) } else { None })),
        (recv_bytes, None) => Err(SessionFailure(format!(
            "fusermount did not send a file descriptor.  We received {recv_bytes} bytes."
        ))),
    }
}

/// Umount a fuse file system
fn fuse_kern_umount(mountpoint: &str, file: File, fusermount: &str) -> Result<()> {
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
    match umount2(mountpoint, MntFlags::MNT_DETACH) {
        Ok(()) => Ok(()),
        Err(Errno::EPERM) => fuse_fusermount_umount(mountpoint, fusermount),
        Err(e) => Err(SessionFailure(format!(
            "failed to umount {mountpoint}: {e}"
        ))),
    }
}

/// Umount a fuse file system by fusermount helper
fn fuse_fusermount_umount(mountpoint: &str, fusermount: &str) -> Result<()> {
    match std::process::Command::new(fusermount)
        .arg("--unmount")
        .arg("--quiet")
        .arg("--lazy")
        .arg("--")
        .arg(mountpoint)
        .status()
        .map_err(IoError)?
        .code()
    {
        Some(0) => Ok(()),
        exit_code => Err(SessionFailure(format!(
            "Unexpected exit code when unmounting via running fusermount: {exit_code:?}"
        ))),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::os::unix::io::FromRawFd;
    use std::path::Path;
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
    fn test_new_channel() {
        let fd = nix::unistd::dup(std::io::stdout().as_raw_fd()).unwrap();
        let file = unsafe { File::from_raw_fd(fd) };
        let _ = FuseChannel::new(file, 3).unwrap();
    }

    #[test]
    fn test_fusermount() {
        let dir = TempDir::new().unwrap();
        let se = FuseSession::new(dir.as_path(), "foo", "bar", true);
        assert!(se.is_ok());
        let mut se = se.unwrap();
        assert_eq!(se.get_fusermount(), FUSERMOUNT_BIN);

        se.set_fusermount("fusermount");
        assert_eq!(se.get_fusermount(), "fusermount");
    }

    #[test]
    fn test_clone_fuse_file() {
        let dir = TempDir::new().unwrap();
        let mut se = FuseSession::new(dir.as_path(), "foo", "bar", true).unwrap();
        se.mount().unwrap();

        let cloned_file = se.clone_fuse_file().unwrap();
        assert!(cloned_file.as_raw_fd() > 0);

        se.umount().unwrap();
        se.set_fuse_file(cloned_file);
        se.mount().unwrap();
    }

    #[test]
    fn test_new_blocking_channel() {
        let dir = TempDir::new().unwrap();
        let mut se = FuseSession::new(dir.as_path(), "foo", "bar", true).unwrap();
        assert!(se.new_blocking_channel().is_err());

        se.mount().unwrap();
        let ch = se.new_blocking_channel().unwrap();
        // The cloned fd has its own file description, so it stays blocking
        // even though the session fd is O_NONBLOCK.
        let flags = fcntl(ch.file.as_raw_fd(), FcntlArg::F_GETFL).unwrap();
        assert_eq!(
            OFlag::from_bits_truncate(flags) & OFlag::O_NONBLOCK,
            OFlag::empty()
        );

        se.umount().unwrap();
    }

    #[test]
    fn test_blocking_channel_exit_on_umount() {
        let dir = TempDir::new().unwrap();
        let mut se = FuseSession::new(dir.as_path(), "foo", "bar", true).unwrap();
        se.mount().unwrap();

        let mut ch = se.new_blocking_channel().unwrap();
        let (tx, rx) = std::sync::mpsc::channel();
        let thread = std::thread::spawn(move || {
            // A freshly-mounted connection queues FUSE_INIT, so the first
            // get_request() returns that request instead of blocking. Drain
            // requests until the umount below tears the connection down and
            // get_request() finally returns Ok(None): that is the teardown
            // contract this test asserts, and the only way a blocking channel
            // exits (FuseSession::wake() has no effect on it).
            let torn_down = loop {
                match ch.get_request() {
                    Ok(None) => break true,
                    Ok(Some(_)) => continue,
                    Err(_) => break false,
                }
            };
            tx.send(torn_down).unwrap();
        });

        se.umount().unwrap();
        // The pending read must return (Ok(None)) once the connection is
        // torn down; the timeout guards against a hang.
        assert_eq!(rx.recv_timeout(std::time::Duration::from_secs(5)), Ok(true));
        thread.join().unwrap();
    }
}

#[cfg(feature = "async-io")]
pub use asyncio::FuseDevTask;

#[cfg(feature = "async-io")]
/// Task context to handle fuse request in asynchronous mode.
mod asyncio {
    use std::cell::{Cell, RefCell};
    use std::os::unix::io::{AsRawFd, RawFd};
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    use futures_util::stream::{FuturesUnordered, StreamExt};
    use nix::fcntl::{fcntl, FcntlArg, OFlag};

    use crate::api::filesystem::AsyncFileSystem;
    use crate::api::server::Server;
    use crate::async_file::File as AsyncFile;
    use crate::file_buf::FileVolatileBuf;
    use crate::transport::{FuseBuf, FuseDevWriter, Reader};

    /// Default limit on the number of concurrently processed requests.
    ///
    /// The limit bounds both the io_uring queue depth and the memory used by
    /// the per-request buffers (one request buffer per in-flight request).
    const DEFAULT_MAX_INFLIGHT: usize = 16;

    /// Pool of reusable request buffers for pipelined request processing.
    ///
    /// Every in-flight request owns one buffer for its request data and
    /// reply. Buffers are allocated lazily on first use and recycled through
    /// the free list afterwards; once `max_inflight` buffers exist, no more
    /// buffers are allocated, which also bounds the number of concurrently
    /// processed requests and the memory used by them. When the pool is
    /// exhausted, the caller serves in-flight requests first instead of
    /// reading new ones (back pressure), and unread requests queue up in
    /// the kernel, which throttles the clients on its own once its queues
    /// fill up.
    struct BufferPool {
        free: RefCell<Vec<Vec<u8>>>,
        created: Cell<usize>,
        buf_size: usize,
        max_inflight: usize,
    }

    impl BufferPool {
        fn new(buf_size: usize, max_inflight: usize) -> Self {
            BufferPool {
                free: RefCell::new(Vec::new()),
                created: Cell::new(0),
                buf_size,
                max_inflight: max_inflight.max(1),
            }
        }

        /// Get a buffer from the pool, allocating a new one lazily if the
        /// pool is empty but the limit hasn't been reached yet, or return
        /// `None` if all buffers are in use.
        fn try_acquire(&self) -> Option<Vec<u8>> {
            if let Some(buf) = self.free.borrow_mut().pop() {
                return Some(buf);
            }
            if self.created.get() < self.max_inflight {
                self.created.set(self.created.get() + 1);
                return Some(vec![0x0u8; self.buf_size]);
            }
            None
        }

        /// Return a buffer to the pool for reuse.
        fn release(&self, buf: Vec<u8>) {
            self.free.borrow_mut().push(buf);
        }
    }

    /// Task context to handle fuse request in asynchronous mode.
    ///
    /// This structure provides a context to handle fuse request in asynchronous mode, including
    /// the fuse device file and a `Server` instance to serve requests.
    ///
    /// ## Examples
    /// ```text
    /// let buf_size = (crate::api::server::MAX_BUFFER_SIZE + 0x1000) as usize;
    /// let file = session.clone_fuse_file().unwrap();
    /// let state = Arc::new(AtomicBool::new(false));
    /// let mut task = FuseDevTask::new(buf_size, file, fs_server, state.clone());
    ///
    /// // Run the task
    /// executor.spawn(async move { task.poll_handler().await });
    ///
    /// // Stop the task
    /// state.store(true, Ordering::Relaxed);
    /// ```
    pub struct FuseDevTask<F: AsyncFileSystem + Sync> {
        file: AsyncFile,
        state: Arc<AtomicBool>,
        server: Arc<Server<F>>,
        buf_size: usize,
        max_inflight: usize,
    }

    impl<F: AsyncFileSystem + Sync> FuseDevTask<F> {
        /// Create a new fuse task context for asynchronous IO.
        ///
        /// The number of concurrently processed requests is limited to
        /// `DEFAULT_MAX_INFLIGHT`, use `Self::new_with_max_inflight()` to
        /// customize the limit.
        ///
        /// # Parameters
        /// - buf_size: size of buffer to receive requests from/send reply to the fuse fd.
        ///   It must be big enough to hold any request, at least
        ///   `crate::api::server::MAX_BUFFER_SIZE + 0x1000`, otherwise the kernel rejects
        ///   reads from the fuse device with `EINVAL` once the INIT handshake is done.
        ///   Note that requests are processed concurrently, each with its own buffer of
        ///   this size.
        /// - file: file object for the fuse device, ownership is taken by the task object
        /// - server: `Server` instance to serve requests from the fuse fd
        /// - state: shared flag to control the task object. The task stops picking up
        ///   new requests once it's set to `true`; the requests being processed are
        ///   completed first.
        pub fn new(
            buf_size: usize,
            file: std::fs::File,
            server: Arc<Server<F>>,
            state: Arc<AtomicBool>,
        ) -> Self {
            Self::new_with_max_inflight(buf_size, file, server, state, DEFAULT_MAX_INFLIGHT)
        }

        /// Create a new fuse task context for asynchronous IO with a custom
        /// limit on the number of concurrently processed requests.
        ///
        /// # Parameters
        /// - buf_size, file, server, state: same as `Self::new()`.
        /// - max_inflight: maximum number of requests processed concurrently.
        ///   Each in-flight request owns one buffer of `buf_size` bytes, so
        ///   this limit also bounds the memory used by the task. Values
        ///   smaller than 1 are clamped to 1.
        pub fn new_with_max_inflight(
            buf_size: usize,
            file: std::fs::File,
            server: Arc<Server<F>>,
            state: Arc<AtomicBool>,
            max_inflight: usize,
        ) -> Self {
            // The fuse device fd is a file description without `O_NONBLOCK`
            // (both freshly opened fds and fds cloned with `FUSE_DEV_IOC_CLONE`).
            // Set it explicitly, because reads issued while no request is
            // pending must not block the runtime thread:
            // - with the io-uring runtime, io-uring submits reads inline on
            //   fds without `O_NONBLOCK`, and `fuse_dev_do_read()` only honors
            //   `O_NONBLOCK` (not `IOCB_NOWAIT`), so a blocking fd would stall
            //   the io-uring submission thread. With `O_NONBLOCK` the read
            //   fails with `EAGAIN` and io-uring waits for readiness via poll
            //   instead.
            // - with the tokio runtime, reads are issued with plain
            //   `preadv()`, which would block the whole single-threaded
            //   runtime (stalling in-flight request handling and teardown).
            //   With `O_NONBLOCK` the read fails with `EAGAIN` and
            //   `poll_handler()` yields and retries instead.
            //
            // Note: `O_NONBLOCK` is a property of the file description, so the
            // fd must not be shared with other consumers of the same file
            // description; the task takes ownership of `file` for this reason.
            fcntl(file.as_raw_fd(), FcntlArg::F_SETFL(OFlag::O_NONBLOCK))
                .expect("failed to set fuse device fd nonblocking");

            FuseDevTask {
                file: AsyncFile::from_std_file(file),
                server,
                state,
                buf_size,
                max_inflight: max_inflight.max(1),
            }
        }

        /// Handler to process fuse requests in asynchronous mode.
        ///
        /// An async fn to handle requests from the fuse fd. It works in asynchronous IO mode when:
        /// - receiving request from fuse fd
        /// - handling requests by calling Server::async_handle_message()
        /// - sending reply to fuse fd
        ///
        /// Requests are processed concurrently: each request read from the fuse device
        /// is turned into a request-handling future pushed into a `FuturesUnordered`
        /// set, which is driven in parallel with reading the next request, so multiple
        /// requests are in flight at the same time even though the runtime is
        /// single-threaded. This allows the asynchronous IO engine (io_uring) to queue
        /// and batch IO operations instead of serving them one by one. The number of
        /// in-flight requests is bounded by the request buffer pool, and replies may
        /// be sent out of order, which is fine because the kernel matches replies to
        /// requests by their unique ids.
        ///
        /// The select loop is biased to complete in-flight requests before reading new
        /// ones: unread requests just queue up in the kernel without consuming
        /// userspace resources, while completed-but-unreplied requests pin request
        /// buffers and keep clients waiting, so draining them first keeps the buffer
        /// pool circulating and tail latency low. Note that a read issued on the fuse
        /// device is never canceled once started: when the select loop turns to
        /// in-flight work while a read is pending, the read is driven to completion
        /// before the loop restarts, because the kernel may consume a request from
        /// its queue into the read buffer at any point, and canceling the read
        /// afterwards would silently lose that request.
        ///
        /// The async fn repeatedly return Poll::Pending when polled until the state has been set
        /// to quiesce mode, or the fuse session has been torn down (EOF/`ENODEV` from the
        /// fuse device).
        ///
        /// Note: when driven by the tokio-uring runtime, io_uring submission queue entries
        /// are submitted to the kernel whenever the runtime parks, so the driving future
        /// must not busy-loop and should let the runtime park regularly (e.g. by running
        /// `poll_handler()` as a separate task). Otherwise requests may pile up in the
        /// kernel without being served.
        pub async fn poll_handler(&mut self) {
            // TODO: register the request buffers as io uring buffers.
            let fd = self.file.as_raw_fd();
            let pool = BufferPool::new(self.buf_size, self.max_inflight);
            let mut inflight = FuturesUnordered::new();

            'serve: while !self.state.load(Ordering::Acquire) {
                // Get a buffer for the next request. If the pool is exhausted,
                // all buffers are held by in-flight requests, so make progress
                // on those first (back pressure).
                let mut buf = match pool.try_acquire() {
                    Some(buf) => buf,
                    None => {
                        if let Some(buf) = inflight.next().await {
                            pool.release(buf);
                            continue 'serve;
                        }
                        // Unreachable: the pool never hands out more buffers
                        // than it created, and every created buffer is either
                        // in the free list or held by an in-flight request.
                        error!("request buffer pool is empty without in-flight requests");
                        break;
                    }
                };

                // The outcome of the read once it completes. Limit the scope
                // of the read future, so that its borrow of `buf` ends before
                // the buffer is handed over to a request or the pool.
                let read_result = {
                    // Safe because `vbuf` doesn't out-live `buf`.
                    let vbuf = unsafe { FileVolatileBuf::new(&mut buf) };
                    let read = self.file.async_read_at(vbuf, 0);
                    tokio::pin!(read);

                    loop {
                        tokio::select! {
                            biased;
                            // Complete in-flight requests first, see the function doc.
                            res = inflight.next(), if !inflight.is_empty() => {
                                // Safe: the set is non-empty, so next() only returns
                                // once a request future has completed.
                                pool.release(res.unwrap());
                            }
                            (result, _vbuf) = &mut read => {
                                break result;
                            }
                        }
                    }
                    // The read future has completed, so dropping it can't cancel
                    // an in-flight read and lose a request anymore.
                };

                match read_result {
                    Ok(0) => {
                        // EOF, the fuse session has been torn down.
                        pool.release(buf);
                        break 'serve;
                    }
                    Ok(len) => {
                        let server = self.server.clone();
                        inflight.push(handle_request(server, fd, buf, len));
                    }
                    Err(e) => {
                        pool.release(buf);
                        match e.raw_os_error() {
                            Some(libc::ENODEV)
                            | Some(libc::ENOTCONN)
                            | Some(libc::ECONNABORTED) => {
                                // The fuse device was unmounted or the connection was aborted.
                                break 'serve;
                            }
                            Some(libc::EINTR) => {
                                // Interrupted by a signal, retry the read.
                                continue 'serve;
                            }
                            Some(libc::EAGAIN) => {
                                // No request is pending and the io_uring
                                // read was issued on the nonblocking fuse
                                // fd. Some kernels complete the read with
                                // `EAGAIN` instead of arming poll on the
                                // fuse device, so retrying immediately
                                // would busy-loop without ever letting the
                                // runtime park (which is when io_uring
                                // submissions and reactor events are
                                // processed). Yield to the runtime before
                                // retrying instead.
                                tokio::task::yield_now().await;
                                continue 'serve;
                            }
                            _ => {
                                // TODO: error handling
                                error!("failed to read request from fuse device fd, {}", e);
                            }
                        }
                    }
                }
            }

            // Drain all in-flight requests before returning, so quiescing the
            // task doesn't drop requests without a reply.
            while let Some(buf) = inflight.next().await {
                pool.release(buf);
            }

            // TODO: unregister the request buffers as io uring buffers.
        }
    }

    /// Serve one fuse request and send its reply, then hand the request buffer
    /// back for reuse.
    async fn handle_request<F: AsyncFileSystem + Sync>(
        server: Arc<Server<F>>,
        fd: RawFd,
        mut buf: Vec<u8>,
        len: usize,
    ) -> Vec<u8> {
        // ###############################################
        // Note: it's a heavy hack to reuse the same underlying data
        // buffer for both Reader and Writer, in order to reduce memory
        // consumption. Here we assume Reader won't be used anymore once
        // we start to write to the Writer. To get rid of this hack,
        // just allocate a dedicated data buffer for Writer.
        let buf_slice = unsafe { std::slice::from_raw_parts_mut(buf.as_mut_ptr(), buf.len()) };
        // Reader::from_fuse_buffer() and FuseDevWriter::new() should always
        // return success.
        let reader = Reader::<()>::from_fuse_buffer(FuseBuf::new(&mut buf[0..len])).unwrap();
        let writer = FuseDevWriter::<()>::new(fd, buf_slice).unwrap();
        let result = unsafe {
            server
                .async_handle_message(reader, writer.into(), None, None)
                .await
        };

        if let Err(e) = result {
            // TODO: error handling
            error!("failed to handle fuse request, {}", e);
        }

        buf
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::async_runtime;
        use crate::passthrough::{Config, PassthroughFs};
        use vmm_sys_util::tempfile::TempFile;

        #[test]
        fn test_fuse_dev_task_quiesce() {
            let fs = PassthroughFs::<()>::new(Config::default()).unwrap();
            let server = Arc::new(Server::new(fs));
            let file = TempFile::new().unwrap().into_file();
            // Quiesce the task before polling it, so poll_handler() returns
            // right away without touching the device.
            let state = Arc::new(AtomicBool::new(true));
            let mut task = FuseDevTask::new(0x1000, file, server, state);

            async_runtime::block_on(task.poll_handler());
        }

        #[test]
        fn test_buffer_pool_limit() {
            let pool = BufferPool::new(64, 2);

            // Buffers are allocated lazily up to the limit...
            let buf1 = pool.try_acquire().unwrap();
            let buf2 = pool.try_acquire().unwrap();
            assert_eq!(buf1.len(), 64);
            assert_eq!(buf2.len(), 64);
            // ...and no buffer is handed out once the limit is reached.
            assert!(pool.try_acquire().is_none());

            // Released buffers are recycled and handed out again.
            pool.release(buf1);
            let buf3 = pool.try_acquire().unwrap();
            assert!(pool.try_acquire().is_none());
            pool.release(buf2);
            pool.release(buf3);
        }

        #[test]
        fn test_buffer_pool_limit_clamped() {
            // A limit of 0 is clamped to 1, so the pool stays usable.
            let pool = BufferPool::new(64, 0);
            assert!(pool.try_acquire().is_some());
            assert!(pool.try_acquire().is_none());
        }
    }
}
