// Copyright 2020-2022 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! FUSE session management.
//!
//! A FUSE channel is a FUSE request handling context that takes care of handling FUSE requests
//! sequentially. A FUSE session is a connection from a FUSE mountpoint to a FUSE server daemon.
//! A FUSE session can have multiple FUSE channels so that FUSE requests are handled in parallel.

use mio::{Events, Poll, Token, Waker};
use std::fs::{File, OpenOptions};
use std::ops::Deref;
use std::os::unix::fs::PermissionsExt;
use std::os::unix::io::AsRawFd;
use std::os::unix::net::UnixStream;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Mutex};

use nix::errno::Errno;
use nix::fcntl::{fcntl, FcntlArg, FdFlag, OFlag};
use nix::mount::{mount, umount2, MntFlags, MsFlags};
use nix::poll::{poll, PollFd, PollFlags};
use nix::sys::epoll::{epoll_ctl, EpollEvent, EpollFlags, EpollOp};
use nix::unistd::{getgid, getuid, read};

use super::{
    super::pagesize,
    Error::{IoError, SessionFailure},
    FuseBuf, FuseDevWriter, Reader, Result, FUSE_HEADER_SIZE, FUSE_KERN_BUF_SIZE,
};

// These follows definition from libfuse.
const POLL_EVENTS_CAPACITY: usize = 1024;

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
            bufsize: FUSE_KERN_BUF_SIZE * pagesize() + FUSE_HEADER_SIZE,
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

    /// Expose the associated FUSE session file.
    pub fn get_fuse_file(&self) -> Option<&File> {
        self.file.as_ref()
    }

    /// Force setting the associated FUSE session file.
    pub fn set_fuse_file(&mut self, file: File) {
        self.file = Some(file);
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

    fn add_waker(&self, waker: Arc<Waker>) -> Result<()> {
        let mut wakers = self
            .wakers
            .lock()
            .map_err(|e| SessionFailure(format!("lock wakers: {e}")))?;
        wakers.push(waker);
        Ok(())
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
    pub fn get_request(&mut self) -> Result<Option<(Reader, FuseDevWriter)>> {
        let mut events = Events::with_capacity(POLL_EVENTS_CAPACITY);
        let mut need_exit = false;
        loop {
            let mut fusereq_available = false;
            match self.poll.poll(&mut events, None) {
                Ok(_) => {}
                Err(ref e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(e) => return Err(SessionFailure(format!("epoll wait: {e}"))),
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

            // Handle wake up event first. We don't read the event fd so that a LEVEL triggered
            // event can still be delivered to other threads/daemons.
            if need_exit {
                info!("Will exit from fuse service");
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
                            info!("fuse filesystem umounted");
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
            Err(nix::errno::Errno::EPERM) => fuse_fusermount_mount(
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
    nix::fcntl::fcntl(send.as_raw_fd(), FcntlArg::F_SETFD(FdFlag::empty()))
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
        Err(nix::errno::Errno::EPERM) => fuse_fusermount_umount(mountpoint, fusermount),
        Err(e) => Err(SessionFailure(format!(
            "failed to umount {mountpoint}: {e}"
        ))),
    }
}

/// Umount a fuse file system
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
}

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
