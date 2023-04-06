// Copyright 2020-2022 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! FUSE session management.
//!
//! A FUSE channel is a FUSE request handling context that takes care of handling FUSE requests
//! sequentially. A FUSE session is a connection from a FUSE mountpoint to a FUSE server daemon.
//! A FUSE session can have multiple FUSE channels so that FUSE requests are handled in parallel.

use std::fs::{File, OpenOptions};
use std::io;
use std::io::IoSlice;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::io::{AsRawFd, RawFd};
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use mio::{Events, Poll, Token, Waker};
use nix::errno::Errno;
use nix::fcntl::{fcntl, FcntlArg, FdFlag, OFlag, SpliceFFlags};
use nix::mount::{mount, umount2, MntFlags, MsFlags};
use nix::poll::{poll, PollFd, PollFlags};
use nix::sys::epoll::{epoll_ctl, EpollEvent, EpollFlags, EpollOp};
use nix::unistd::{getgid, getuid, read};
use vm_memory::bitmap::BitmapSlice;

use super::{
    super::pagesize,
    Error::{IoError, SessionFailure},
    FuseBuf, FuseDevWriter, Reader, Result, FUSE_HEADER_SIZE, FUSE_KERN_BUF_PAGES,
};

// These follows definition from libfuse.
const POLL_EVENTS_CAPACITY: usize = 1024;

// fuse header consumes 1 buf + data(1MB) consumes at least 256 bufs
const DEFAULT_SPLICE_PIPE_READ_BUF_SIZE: usize = 260;
// fuse header consumes 1 buf + data(128KB) consumes at least 32 bufs
const DEFAULT_SPLICE_PIPE_WRITE_BUF_SIZE: usize = 64;

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
        let mut flags = MsFlags::MS_NOSUID | MsFlags::MS_NODEV | MsFlags::MS_NOATIME;
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

/// A fuse channel abstraction.
///
/// Each session can hold multiple channels.
pub struct FuseChannel {
    file: File,
    poll: Poll,
    waker: Arc<Waker>,
    buf: Vec<u8>,
    /// pipe for splice read
    r_p: Option<Pipe>,
    /// pipe for splice write (memory data, fd data)
    w_ps: Option<(Pipe, Pipe)>,
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
        let epoll = poll.as_raw_fd();
        let mut event = EpollEvent::new(EpollFlags::EPOLLIN, usize::from(FUSE_DEV_EVENT) as u64);
        epoll_ctl(
            epoll,
            EpollOp::EpollCtlAdd,
            file.as_raw_fd(),
            Some(&mut event),
        )
        .map_err(|e| SessionFailure(format!("epoll register channel fd: {e}")))?;

        Ok(FuseChannel {
            file,
            poll,
            waker,
            buf: vec![0x0u8; bufsize],
            r_p: None,
            w_ps: None,
        })
    }

    fn get_waker(&self) -> Arc<Waker> {
        self.waker.clone()
    }

    /// Enable using splice syscall to read FUSE requests
    ///
    /// Improve performance of write request because of less data copy.
    /// It's better to check whether FUSE module supports SPLICE_READ before enable this.
    ///
    /// let mut session = FuseSession::new("./mnt", "fs", "fs", false)?;
    /// let mut ch = session.new_channel()?;
    /// let fs = Server::new(MyFs::new()); // MyFs impl FileSystem trait
    /// loop {
    ///     // after handle init request, we know whether kernel support splice read
    ///     if fs.is_support_splice_read() {
    ///         ch.enable_splice_read();
    ///     }
    ///     let (r, w) = ch.get_request()?.unwrap();
    ///     fs.handle_message(r, w, None, None)?;
    /// }
    ///
    pub fn enable_splice_read(&mut self) -> Result<()> {
        if self.r_p.is_some() {
            return Ok(());
        }
        self.r_p = Some(Pipe::new(DEFAULT_SPLICE_PIPE_READ_BUF_SIZE * pagesize())?);
        Ok(())
    }

    /// Enable using splice syscall to reply FUSE requests
    ///
    /// Improve performance of read request because of less data copy.
    /// It's better to check whether FUSE module supports SPLICE_WRITE&SPLICE_MOVE before enable this.
    ///
    /// let mut session = FuseSession::new("./mnt", "fs", "fs", false)?;
    /// let mut ch = session.new_channel()?;
    /// let fs = Server::new(MyFs::new()); // MyFs impl FileSystem trait
    /// loop {
    ///     // after handle init request, we know whether kernel support splice write
    ///     if fs.is_support_splice_write() {
    ///         ch.enable_splice_write();
    ///     }
    ///     let (r, w) = ch.get_request()?.unwrap();
    ///     fs.handle_message(r, w, None, None)?;
    /// }
    ///
    pub fn enable_splice_write(&mut self) -> Result<()> {
        if self.w_ps.is_some() {
            return Ok(());
        }
        if self.w_ps.is_none() {
            self.w_ps = Some((
                Pipe::new(DEFAULT_SPLICE_PIPE_WRITE_BUF_SIZE * pagesize())?,
                Pipe::new(DEFAULT_SPLICE_PIPE_WRITE_BUF_SIZE * pagesize())?,
            ));
        }
        Ok(())
    }

    /// Check whether next FUSE request is available
    ///
    /// Returns:
    /// - Ok((available, need_exit)) whether FUSE request is available and whether fuse server need exit
    /// - Err(e) error message
    fn is_readable(&mut self) -> Result<(bool, bool)> {
        let mut events = Events::with_capacity(POLL_EVENTS_CAPACITY);
        let mut need_exit = false;
        let mut fusereq_available = false;
        match self.poll.poll(&mut events, None) {
            Ok(_) => {}
            Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => return Ok((false, false)),
            Err(e) => return Err(SessionFailure(format!("epoll wait: {}", e))),
        }

        for event in events.iter() {
            if event.is_readable() {
                match event.token() {
                    EXIT_FUSE_EVENT => need_exit = true,
                    FUSE_DEV_EVENT => fusereq_available = true,
                    x => {
                        error!("unexpected epoll event");
                        return Err(SessionFailure(format!("unexpected epoll event: {}", x.0)));
                    }
                }
            } else if event.is_error() {
                info!("FUSE channel already closed!");
                return Err(SessionFailure("epoll error".to_string()));
            } else {
                // We should not step into this branch as other event is not registered.
                panic!("unknown epoll result events");
            }
        }
        Ok((fusereq_available, need_exit))
    }

    fn prepare(&mut self) -> Result<()> {
        if self.r_p.is_some() && self.r_p.as_ref().unwrap().is_invalid() {
            self.r_p = Some(Pipe::new(DEFAULT_SPLICE_PIPE_READ_BUF_SIZE * pagesize())?);
        }
        if let Some((vm_p, fd_p)) = self.w_ps.as_mut() {
            if vm_p.is_invalid() {
                *vm_p = Pipe::new(DEFAULT_SPLICE_PIPE_WRITE_BUF_SIZE * pagesize())?;
            }
            if fd_p.is_invalid() {
                *fd_p = Pipe::new(DEFAULT_SPLICE_PIPE_WRITE_BUF_SIZE * pagesize())?;
            }
        }
        Ok(())
    }

    fn do_splice(&mut self) -> io::Result<usize> {
        loop {
            match nix::fcntl::splice(
                self.file.as_raw_fd(),
                None,
                self.r_p.as_ref().unwrap().wfd(),
                None,
                self.buf.len(),
                SpliceFFlags::empty(),
            ) {
                Ok(n) => return Ok(n),
                Err(nix::Error::EIO) => {
                    // FUSE reply EIO if pipe's available buffers are not enough to fill fuse request
                    // So we need resize pipe buf size
                    let pipe = self.r_p.as_mut().unwrap();
                    pipe.set_size(pipe.size() * 2)?;
                }
                Err(e) => return Err(e.into()),
            }
        }
    }

    /// Get next available FUSE request from the underlying fuse device file.
    ///
    /// Returns:
    /// - Ok(None): signal has pending on the exiting event channel
    /// - Ok(Some((reader, writer))): reader to receive request and writer to send reply
    /// - Err(e): error message
    pub fn get_request(&mut self) -> Result<Option<(Reader, FuseDevWriter)>> {
        loop {
            let (fusereq_available, need_exit) = self.is_readable()?;

            // Handle wake up event first. We don't read the event fd so that a LEVEL triggered
            // event can still be delivered to other threads/daemons.
            if need_exit {
                info!("Will exit from fuse service");
                return Ok(None);
            }
            if fusereq_available {
                let fd = self.file.as_raw_fd();
                self.prepare().map_err(|e| {
                    error!("failed to prepare, err = {:?}", e);
                    e
                })?;
                let err = if self.r_p.is_some() {
                    let res = self.do_splice();
                    match res {
                        Ok(n) => {
                            let buf = unsafe {
                                std::slice::from_raw_parts_mut(
                                    self.buf.as_mut_ptr(),
                                    self.buf.len(),
                                )
                            };
                            return Ok(Some((
                                Reader::from_pipe_reader(splice::PipeReader::new(
                                    self.r_p.as_mut().unwrap(),
                                    n,
                                )),
                                FuseDevWriter::with_pipe(
                                    fd,
                                    buf,
                                    self.w_ps.as_mut().map(|(vm_p, fd_p)| {
                                        (PipeWriter::new(vm_p), PipeWriter::new(fd_p))
                                    }),
                                )
                                .unwrap(),
                            )));
                        }
                        Err(e) => e,
                    }
                } else {
                    match read(fd, &mut self.buf) {
                        Ok(len) => {
                            let buf = unsafe {
                                std::slice::from_raw_parts_mut(
                                    self.buf.as_mut_ptr(),
                                    self.buf.len(),
                                )
                            };
                            // Reader::new() and Writer::new() should always return success.
                            let reader =
                                Reader::from_fuse_buffer(FuseBuf::new(&mut self.buf[..len]))
                                    .unwrap();
                            return Ok(Some((
                                reader,
                                FuseDevWriter::with_pipe(
                                    fd,
                                    buf,
                                    self.w_ps.as_mut().map(|(vm_p, fd_p)| {
                                        (PipeWriter::new(vm_p), PipeWriter::new(fd_p))
                                    }),
                                )
                                .unwrap(),
                            )));
                        }
                        Err(e) => e.into(),
                    }
                };
                match err.raw_os_error().unwrap_or(libc::EIO) {
                    libc::ENOENT => {
                        // ENOENT means the operation was interrupted, it's safe to restart
                        trace!("restart reading due to ENOENT");
                        continue;
                    }
                    libc::EAGAIN => {
                        trace!("restart reading due to EAGAIN");
                        continue;
                    }
                    libc::EINTR => {
                        trace!("syscall interrupted");
                        continue;
                    }
                    libc::ENODEV => {
                        info!("fuse filesystem umounted");
                        return Ok(None);
                    }
                    code => {
                        let e = nix::Error::from_i32(code);
                        warn! {"read fuse dev failed on fd {}: {}", fd, e};
                        return Err(SessionFailure(format!("read new request: {e:?}")));
                    }
                }
            }
        }
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
    let mut opts = format!(
        "default_permissions,fd={},rootmode={:o},user_id={},group_id={}",
        file.as_raw_fd(),
        meta.permissions().mode() & libc::S_IFMT,
        getuid(),
        getgid(),
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
        info!(
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

impl<'a, 'b, S: BitmapSlice + Default> FuseDevWriter<'a, 'b, S> {
    /// Construct writer with pipe
    pub fn with_pipe(
        fd: RawFd,
        data_buf: &'a mut [u8],
        pw: Option<(PipeWriter<'b>, PipeWriter<'b>)>,
    ) -> Result<FuseDevWriter<'a, 'b, S>> {
        let buf = unsafe { Vec::from_raw_parts(data_buf.as_mut_ptr(), 0, data_buf.len()) };
        Ok(FuseDevWriter {
            fd,
            buffered: false,
            buf: ManuallyDrop::new(buf),
            pw,
            bitmapslice: S::default(),
            phantom: PhantomData,
        })
    }
}

impl<'a, 'b, S: BitmapSlice> FuseDevWriter<'a, 'b, S> {
    /// Append fd buffer for FUSE reply.
    /// Often for FUSE read requests:
    ///     fuse reply header in buf and data in fd buffer
    pub fn append_fd_buf(&mut self, fd: RawFd, size: u64, off: Option<i64>) -> io::Result<usize> {
        if self.pw.is_none() || !self.buffered {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }
        self.check_available_space(size as usize)?;
        let n = self
            .pw
            .as_mut()
            .unwrap()
            .1
            .splice_from(fd, size as usize, off)?;
        Ok(n)
    }

    pub(crate) fn commit_by_splice(
        &mut self,
        other: Option<&mut FuseDevWriter<'a, 'b, S>>,
    ) -> io::Result<usize> {
        let (other_bufs, (mut pw, fd_pw)) = match other {
            Some(w) => (w.buf.as_slice(), w.pw.take().unwrap()),
            _ => (&[] as &[u8], self.pw.take().unwrap()),
        };
        match (self.buf.len(), other_bufs.len()) {
            (0, 0) => return Ok(0),
            (0, _) => pw.splice_from_buf(other_bufs),
            (_, 0) => pw.splice_from_buf(&self.buf),
            (_, _) => {
                let bufs = [IoSlice::new(self.buf.as_slice()), IoSlice::new(other_bufs)];
                pw.splice_from_iovec(&bufs)
            }
        }
        .map_err(|e| {
            error! {"fail to vmsplice to pipe on commit: {}", e};
            e
        })?;
        pw.splice_from_pipe(fd_pw)?;
        // final commit to fuse fd
        pw.splice_to_all(self.fd).map_err(|e| {
            error! {"fail to splice pipe fd to fuse device on commit: {}", e};
            e
        })
    }
}

impl<'a, S: BitmapSlice + Default> Reader<'a, S> {
    /// Construct a new Reader wrapper over PipeReader
    pub fn from_pipe_reader(reader: splice::PipeReader<'a>) -> Reader<'a, S> {
        ReaderInner::Pipe(reader).into()
    }
}

pub(crate) mod splice {
    use crate::transport::pagesize;
    use nix::fcntl::{FcntlArg, OFlag, SpliceFFlags};
    use std::io::IoSlice;
    use std::os::unix::io::RawFd;

    fn nr_pages(start: usize, len: usize) -> usize {
        let start_vfn = start / pagesize();
        let end_vfn = (start + len - 1) / pagesize();
        end_vfn - start_vfn + 1
    }

    #[inline]
    fn buf_nr_pages(buf: &[u8]) -> usize {
        let start = (buf.as_ptr() as usize) / pagesize();
        let end = (unsafe { buf.as_ptr().add(buf.len() - 1) as usize }) / pagesize();
        end - start + 1
    }

    #[derive(Debug)]
    pub struct Pipe {
        r: RawFd,
        w: RawFd,
        size: usize,
    }

    impl Drop for Pipe {
        fn drop(&mut self) {
            if self.is_invalid() {
                return;
            }
            nix::unistd::close(self.r).expect("failed to close pipe");
            nix::unistd::close(self.w).expect("failed to close pipe");
        }
    }

    impl Pipe {
        pub fn new(buf_size: usize) -> std::io::Result<Self> {
            let (r, w) = nix::unistd::pipe2(OFlag::O_NONBLOCK | OFlag::O_CLOEXEC)?;
            nix::fcntl::fcntl(w, FcntlArg::F_SETPIPE_SZ(buf_size as nix::libc::c_int))?;
            Ok(Self {
                r,
                w,
                size: buf_size,
            })
        }

        pub fn rfd(&self) -> RawFd {
            self.r
        }

        pub fn wfd(&self) -> RawFd {
            self.w
        }

        pub fn clear(&mut self) {
            let _ = nix::unistd::close(self.r);
            let _ = nix::unistd::close(self.w);
            self.r = -1;
            self.w = -1;
        }

        pub fn is_invalid(&self) -> bool {
            self.r == -1
        }

        pub fn set_size(&mut self, new_size: usize) -> std::io::Result<()> {
            nix::fcntl::fcntl(self.w, FcntlArg::F_SETPIPE_SZ(new_size as nix::libc::c_int))?;
            self.size = new_size;
            Ok(())
        }

        pub fn size(&self) -> usize {
            self.size
        }
    }

    /// Reader for fuse requests using fuse splice
    #[derive(Debug)]
    pub struct PipeReader<'a> {
        p: &'a mut Pipe,
        n_bytes: usize,
        bytes_consumed: usize,
    }

    impl<'a> Drop for PipeReader<'a> {
        fn drop(&mut self) {
            if self.n_bytes != 0 {
                self.p.clear();
            }
        }
    }

    impl<'a> std::io::Read for PipeReader<'a> {
        fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize> {
            if self.n_bytes == 0 {
                return Ok(0);
            }
            let n = nix::unistd::read(self.p.r, buf)?;
            self.n_bytes -= n;
            self.bytes_consumed += n;
            Ok(n)
        }
    }

    impl<'a> PipeReader<'a> {
        pub fn new(p: &'a mut Pipe, n_bytes: usize) -> PipeReader<'a> {
            Self {
                p,
                n_bytes,
                bytes_consumed: 0,
            }
        }

        pub fn available_bytes(&self) -> usize {
            self.n_bytes
        }

        pub fn bytes_consumed(&self) -> usize {
            self.bytes_consumed
        }

        pub fn splice_to(&mut self, fd: RawFd, len: usize) -> std::io::Result<usize> {
            let n = nix::fcntl::splice(self.p.r, None, fd, None, len, SpliceFFlags::empty())?;
            self.n_bytes -= n;
            self.bytes_consumed += n;
            Ok(n)
        }

        pub fn splice_to_at(
            &mut self,
            fd: RawFd,
            len: usize,
            off: &mut i64,
        ) -> std::io::Result<usize> {
            let n = nix::fcntl::splice(self.p.r, None, fd, Some(off), len, SpliceFFlags::empty())?;
            self.n_bytes -= n;
            self.bytes_consumed += n;
            Ok(n)
        }
    }

    #[derive(Debug)]
    pub struct PipeWriter<'a> {
        p: &'a mut Pipe,
        n_bufs: usize,
        n_bytes: usize,
    }

    impl<'a> PipeWriter<'a> {
        pub fn new(p: &'a mut Pipe) -> Self {
            Self {
                p,
                n_bufs: 0,
                n_bytes: 0,
            }
        }

        pub fn len(&self) -> usize {
            self.n_bytes
        }

        pub fn is_empty(&self) -> bool {
            self.len() == 0
        }

        fn splice_to(&mut self, fd: RawFd, len: usize) -> std::io::Result<usize> {
            let len = nix::fcntl::splice(
                self.p.rfd(),
                None,
                fd,
                None,
                len,
                SpliceFFlags::SPLICE_F_MOVE,
            )?;
            self.n_bytes -= len;
            Ok(len)
        }

        pub fn splice_to_all(mut self, fd: RawFd) -> std::io::Result<usize> {
            self.splice_to(fd, self.n_bytes)
        }

        fn may_grow_pipe(&mut self, more_bufs: usize) -> std::io::Result<()> {
            let expect_size = (self.n_bufs + more_bufs) * pagesize();
            if expect_size > self.p.size() {
                self.p.set_size(expect_size + 2 * pagesize())
            } else {
                Ok(())
            }
        }

        pub fn splice_from(
            &mut self,
            fd: RawFd,
            len: usize,
            mut off: Option<i64>,
        ) -> std::io::Result<usize> {
            let expect_bufs = len / pagesize() + 1;
            self.may_grow_pipe(expect_bufs)?;
            let ori_off = off;
            let n = nix::fcntl::splice(
                fd,
                off.as_mut(),
                self.p.wfd(),
                None,
                len,
                SpliceFFlags::SPLICE_F_MOVE,
            )?;
            if let Some(off) = ori_off {
                self.n_bufs += nr_pages(off as usize, n);
            } else {
                self.n_bufs += n / pagesize() + 1;
            }
            self.n_bytes += n;
            Ok(n)
        }

        pub fn splice_from_pipe(&mut self, mut other: PipeWriter<'_>) -> std::io::Result<usize> {
            self.may_grow_pipe(other.n_bufs)?;
            let n = nix::fcntl::splice(
                other.p.rfd(),
                None,
                self.p.wfd(),
                None,
                other.len(),
                SpliceFFlags::SPLICE_F_MOVE,
            )?;
            self.n_bytes += n;
            other.n_bytes -= n;
            self.n_bufs += other.n_bufs;
            Ok(n)
        }

        pub fn splice_from_buf(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            let expect_bufs = buf_nr_pages(buf);
            self.may_grow_pipe(expect_bufs)?;
            let n =
                nix::fcntl::vmsplice(self.p.wfd(), &[IoSlice::new(buf)], SpliceFFlags::empty())?;
            self.n_bufs += buf_nr_pages(&buf[..n]);
            self.n_bytes += n;
            Ok(n)
        }

        pub fn splice_from_iovec(&mut self, iovec: &[IoSlice]) -> std::io::Result<usize> {
            let mut expect_bufs = 0;
            let mut expect_size = 0;
            for iv in iovec.iter() {
                expect_size += iv.len();
                expect_bufs += buf_nr_pages(iv.as_ref());
            }
            self.may_grow_pipe(expect_bufs)?;
            let n = nix::fcntl::vmsplice(self.p.wfd(), iovec, SpliceFFlags::empty())?;
            if n != expect_size {
                let mut scan_len = 0;
                let mut grow_bufs = 0;
                for iv in iovec.iter() {
                    if n - scan_len > iv.len() {
                        grow_bufs += buf_nr_pages(iv.as_ref());
                    } else {
                        grow_bufs += buf_nr_pages(&iv.as_ref()[..n - scan_len]);
                        break;
                    }
                    scan_len += iv.len();
                }
                self.n_bufs += grow_bufs;
            } else {
                self.n_bufs += expect_bufs;
            }
            self.n_bytes += n;
            Ok(n)
        }
    }

    impl<'a> Drop for PipeWriter<'a> {
        fn drop(&mut self) {
            if !self.p.is_invalid() && self.n_bytes != 0 {
                self.p.clear();
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use crate::transport::fusedev::splice::{Pipe, PipeReader, PipeWriter};
        use nix::fcntl::SpliceFFlags;
        use std::io::{IoSlice, Read, Write};
        use std::os::unix::io::AsRawFd;
        use std::path::Path;
        use vmm_sys_util::tempfile::TempFile;

        #[test]
        fn test_splice_reader() {
            let p_res = Pipe::new(4096);
            assert!(p_res.is_ok());
            let mut p = p_res.unwrap();
            let content = "hello world!";
            // prepare test file data
            std::fs::write(Path::new("splice_testdata"), content).unwrap();
            let file = std::fs::File::open("splice_testdata").unwrap();
            let res = nix::fcntl::splice(
                file.as_raw_fd(),
                None,
                p.wfd(),
                None,
                content.len(),
                SpliceFFlags::empty(),
            );
            assert!(res.is_ok());
            assert_eq!(content.len(), res.unwrap());
            let mut reader = PipeReader::new(&mut p, content.len());
            let mut buf = vec![0_u8; 1024];
            let res = reader.read(&mut buf);
            assert!(res.is_ok());
            assert_eq!(content.len(), res.unwrap());
            assert_eq!(content.as_bytes(), &buf[..content.len()]);
            assert_eq!(0, reader.available_bytes());
            assert_eq!(content.len(), reader.bytes_consumed());
            drop(reader);

            let mut new_file = std::fs::OpenOptions::new()
                .write(true)
                .truncate(true)
                .create(true)
                .open("splice_testdata_2")
                .unwrap();
            let mut off = 0;
            nix::fcntl::splice(
                file.as_raw_fd(),
                Some(&mut off),
                p.wfd(),
                None,
                content.len(),
                SpliceFFlags::empty(),
            )
            .unwrap();
            let mut reader = PipeReader::new(&mut p, content.len());
            let res = reader.splice_to(new_file.as_raw_fd(), content.len());
            assert!(res.is_ok());
            assert_eq!(content.len(), res.unwrap());
            new_file.flush().unwrap();
            let data = std::fs::read("splice_testdata_2").unwrap();
            assert_eq!(content.as_bytes(), &data);
            drop(reader);

            off = 0;
            nix::fcntl::splice(
                file.as_raw_fd(),
                Some(&mut off),
                p.wfd(),
                None,
                content.len(),
                SpliceFFlags::empty(),
            )
            .unwrap();
            let mut reader = PipeReader::new(&mut p, content.len());
            let mut off2 = 1;
            let res = reader.splice_to_at(new_file.as_raw_fd(), content.len(), &mut off2);
            assert!(res.is_ok());
            assert_eq!(content.len(), res.unwrap());
            new_file.flush().unwrap();
            let data = std::fs::read("splice_testdata_2").unwrap();
            assert_eq!("hhello world!".as_bytes(), &data);

            drop(file);
            drop(new_file);
            let _ = std::fs::remove_file("splice_testdata");
            let _ = std::fs::remove_file("splice_testdata_2");
        }

        #[test]
        fn test_splice_writer() {
            let mut from = TempFile::new().unwrap().into_file();
            let to = TempFile::new().unwrap().into_file();
            let buf = [0_u8; 64];
            from.write(&buf).unwrap();
            let mut pipe = Pipe::new(4096).unwrap();
            let mut pw = PipeWriter::new(&mut pipe);
            assert_eq!(64, pw.splice_from_buf(&buf).unwrap());
            let buf2 = [0_u8; 16];
            assert_eq!(
                80,
                pw.splice_from_iovec(&[IoSlice::new(&buf), IoSlice::new(&buf2)])
                    .unwrap()
            );
            assert_eq!(144, pw.n_bytes);
            assert_eq!(32, pw.splice_from(from.as_raw_fd(), 32, Some(0)).unwrap());
            assert_eq!(32, pw.splice_from(from.as_raw_fd(), 48, Some(32)).unwrap());
            assert_eq!(208, pw.splice_to_all(to.as_raw_fd()).unwrap());
            assert!(!pipe.is_invalid());
        }
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
}

use crate::transport::fusedev::splice::{Pipe, PipeWriter};
use crate::transport::ReaderInner;
#[cfg(feature = "async_io")]
pub use asyncio::FuseDevTask;

#[cfg(feature = "async_io")]
/// Task context to handle fuse request in asynchronous mode.
mod asyncio {
    use std::os::unix::io::RawFd;
    use std::sync::Arc;

    use crate::api::filesystem::AsyncFileSystem;
    use crate::api::server::Server;
    use crate::transport::{FuseBuf, Reader, Writer};

    /// Task context to handle fuse request in asynchronous mode.
    ///
    /// This structure provides a context to handle fuse request in asynchronous mode, including
    /// the fuse fd, a internal buffer and a `Server` instance to serve requests.
    ///
    /// ## Examples
    /// ```ignore
    /// let buf_size = 0x1_0000;
    /// let state = AsyncExecutorState::new();
    /// let mut task = FuseDevTask::new(buf_size, fuse_dev_fd, fs_server, state.clone());
    ///
    /// // Run the task
    /// executor.spawn(async move { task.poll_handler().await });
    ///
    /// // Stop the task
    /// state.quiesce();
    /// ```
    pub struct FuseDevTask<F: AsyncFileSystem + Sync> {
        fd: RawFd,
        buf: Vec<u8>,
        state: AsyncExecutorState,
        server: Arc<Server<F>>,
    }

    impl<F: AsyncFileSystem + Sync> FuseDevTask<F> {
        /// Create a new fuse task context for asynchronous IO.
        ///
        /// # Parameters
        /// - buf_size: size of buffer to receive requests from/send reply to the fuse fd
        /// - fd: fuse device file descriptor
        /// - server: `Server` instance to serve requests from the fuse fd
        /// - state: shared state object to control the task object
        ///
        /// # Safety
        /// The caller must ensure `fd` is valid during the lifetime of the returned task object.
        pub fn new(
            buf_size: usize,
            fd: RawFd,
            server: Arc<Server<F>>,
            state: AsyncExecutorState,
        ) -> Self {
            FuseDevTask {
                fd,
                server,
                state,
                buf: vec![0x0u8; buf_size],
            }
        }

        /// Handler to process fuse requests in asynchronous mode.
        ///
        /// An async fn to handle requests from the fuse fd. It works in asynchronous IO mode when:
        /// - receiving request from fuse fd
        /// - handling requests by calling Server::async_handle_requests()
        /// - sending reply to fuse fd
        ///
        /// The async fn repeatedly return Poll::Pending when polled until the state has been set
        /// to quiesce mode.
        pub async fn poll_handler(&mut self) {
            // TODO: register self.buf as io uring buffers.
            let drive = AsyncDriver::default();

            while !self.state.quiescing() {
                let result = AsyncUtil::read(drive.clone(), self.fd, &mut self.buf, 0).await;
                match result {
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
                            Reader::<()>::new(FuseBuf::new(&mut self.buf[0..len])).unwrap();
                        let writer = Writer::new(self.fd, buf).unwrap();
                        let result = unsafe {
                            self.server
                                .async_handle_message(drive.clone(), reader, writer, None, None)
                                .await
                        };

                        if let Err(e) = result {
                            // TODO: error handling
                            error!("failed to handle fuse request, {}", e);
                        }
                    }
                    Err(e) => {
                        // TODO: error handling
                        error!("failed to read request from fuse device fd, {}", e);
                    }
                }
            }

            // TODO: unregister self.buf as io uring buffers.

            // Report that the task has been quiesced.
            self.state.report();
        }
    }

    impl<F: AsyncFileSystem + Sync> Clone for FuseDevTask<F> {
        fn clone(&self) -> Self {
            FuseDevTask {
                fd: self.fd,
                server: self.server.clone(),
                state: self.state.clone(),
                buf: vec![0x0u8; self.buf.capacity()],
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use std::os::unix::io::AsRawFd;

        use super::*;
        use crate::api::{Vfs, VfsOptions};
        use crate::async_util::{AsyncDriver, AsyncExecutor};

        #[test]
        fn test_fuse_task() {
            let state = AsyncExecutorState::new();
            let fs = Vfs::<AsyncDriver, ()>::new(VfsOptions::default());
            let _server = Arc::new(Server::<Vfs<AsyncDriver, ()>, AsyncDriver, ()>::new(fs));
            let file = vmm_sys_util::tempfile::TempFile::new().unwrap();
            let _fd = file.as_file().as_raw_fd();

            let mut executor = AsyncExecutor::new(32);
            executor.setup().unwrap();

            /*
            // Create three tasks, which could handle three concurrent fuse requests.
            let mut task = FuseDevTask::new(0x1000, fd, server.clone(), state.clone());
            executor
                .spawn(async move { task.poll_handler().await })
                .unwrap();
            let mut task = FuseDevTask::new(0x1000, fd, server.clone(), state.clone());
            executor
                .spawn(async move { task.poll_handler().await })
                .unwrap();
            let mut task = FuseDevTask::new(0x1000, fd, server.clone(), state.clone());
            executor
                .spawn(async move { task.poll_handler().await })
                .unwrap();
             */

            for _i in 0..10 {
                executor.run_once(false).unwrap();
            }

            // Set existing flag
            state.quiesce();
            // Close the fusedev fd, so all pending async io requests will be aborted.
            drop(file);

            for _i in 0..10 {
                executor.run_once(false).unwrap();
            }
        }
    }
}
