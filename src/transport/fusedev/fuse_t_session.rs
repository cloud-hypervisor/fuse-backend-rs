// Copyright 2020-2022 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! FUSE session management.
//!
//! A FUSE channel is a FUSE request handling context that takes care of handling FUSE requests
//! sequentially. A FUSE session is a connection from a FUSE mountpoint to a FUSE server daemon.
//! A FUSE session can have multiple FUSE channels so that FUSE requests are handled in parallel.

use std::fs::File;
use std::mem::size_of;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::os::unix::prelude::CommandExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;

use libc::{proc_pidpath, PROC_PIDPATHINFO_MAXSIZE};
use nix::errno::Errno;
use nix::sys::signal::{signal, SigHandler, Signal};
use nix::sys::socket::{recv, send, setsockopt, SetSockOpt};
use nix::sys::socket::{socketpair, AddressFamily, MsgFlags, SockFlag, SockType};
use nix::unistd::{close, fork, getpid, read, ForkResult};
use vm_memory::ByteValued;

use super::{
    Error::IoError, Error::SessionFailure, FuseBuf, FuseDevWriter, Reader, Result,
    FUSE_HEADER_SIZE, FUSE_KERN_BUF_SIZE,
};
use crate::transport::pagesize;

// These follows definition from libfuse.
const FS_SND_SIZE: usize = 4 * 1024 * 1024;

const FUSE_NFSSRV_PATH: &str = "/usr/local/bin/go-nfsv4";

#[derive(Clone, Debug)]
pub struct RcvBuf;

impl SetSockOpt for RcvBuf {
    type Val = usize;

    fn set(&self, fd: RawFd, val: &Self::Val) -> nix::Result<()> {
        unsafe {
            let res = libc::setsockopt(
                fd,
                libc::SOL_SOCKET,
                libc::SO_RCVBUF,
                val.as_slice().as_ptr() as *const _,
                size_of::<usize>() as libc::socklen_t,
            );
            Errno::result(res).map(drop)
        }
    }
}

#[derive(Clone, Debug)]
pub struct SndBuf;

impl SetSockOpt for SndBuf {
    type Val = usize;

    fn set(&self, fd: RawFd, val: &Self::Val) -> nix::Result<()> {
        unsafe {
            let res = libc::setsockopt(
                fd,
                libc::SOL_SOCKET,
                libc::SO_SNDBUF,
                val.as_slice().as_ptr() as *const _,
                size_of::<usize>() as libc::socklen_t,
            );
            Errno::result(res).map(drop)
        }
    }
}

/// A fuse session manager to manage the connection with the in kernel fuse driver.
pub struct FuseSession {
    mountpoint: PathBuf,
    fsname: String,
    subtype: String,
    file: Option<File>,
    file_lock: Arc<Mutex<()>>,
    bufsize: usize,
    readonly: bool,
    monitor_file: Option<File>,
    wait_handle: Option<JoinHandle<Result<()>>>,
}

unsafe impl Send for FuseSession {}

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
            .map_err(|_| SessionFailure(format!("invalid mountpoint {:?}", mountpoint)))?;
        if !dest.is_dir() {
            return Err(SessionFailure(format!("{:?} is not a directory", dest)));
        }

        Ok(FuseSession {
            mountpoint: dest,
            fsname: fsname.to_owned(),
            subtype: subtype.to_owned(),
            file: None,
            file_lock: Arc::new(Mutex::new(())),
            bufsize: FUSE_KERN_BUF_SIZE * pagesize() + FUSE_HEADER_SIZE,
            monitor_file: None,
            wait_handle: None,
            readonly,
        })
    }

    /// Mount the fuse mountpoint, building connection with the in kernel fuse driver.
    pub fn mount(&mut self) -> Result<()> {
        let files = fuse_kern_mount(&self.mountpoint, &self.fsname, &self.subtype, self.readonly)?;
        self.file = Some(files.0);
        self.monitor_file = Some(files.1);
        self.wait_handle = Some(self.send_mount_command()?);

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
        if let Some(file) = self.monitor_file.take() {
            if self.mountpoint.to_str().is_some() {
                fuse_kern_umount(file)
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
                .map_err(|e| SessionFailure(format!("dup fd: {}", e)))?;
            let file_lock = self.file_lock.clone();
            FuseChannel::new(file, file_lock, self.bufsize)
        } else {
            Err(SessionFailure("invalid fuse session".to_string()))
        }
    }

    /// Wake channel loop
    /// After macfuse unmount, read will throw ENODEV
    /// So wakers is no need for macfuse to interrupt channel
    pub fn wake(&self) -> Result<()> {
        Ok(())
    }

    /// wait for fuse-t handle mount command
    pub fn wait_mount(&mut self) -> Result<()> {
        if let Some(wait_handle) = self.wait_handle.take() {
            let _ = wait_handle.join()?;
        }
        Ok(())
    }

    fn send_mount_command(&self) -> Result<JoinHandle<Result<()>>> {
        let mon_fd = self
            .monitor_file
            .as_ref()
            .ok_or(SessionFailure("monitor fd is not ready".to_string()))
            .map(|f| f.as_raw_fd())?;

        let handle = std::thread::spawn(move || {
            let msg = b"mount";
            if let Err(e) = send(mon_fd, msg, MsgFlags::empty()) {
                return Err(SessionFailure(format!("send mount failed {:?}", e)));
            };

            let mut status = -1;
            loop {
                match recv(mon_fd, status.as_mut_slice(), MsgFlags::empty()) {
                    Ok(_size) => {
                        return if status == 0 {
                            Ok(())
                        } else {
                            Err(SessionFailure(format!("mount failed status: {:?}", status)))
                        }
                    }
                    Err(Errno::EINTR) => {
                        trace!("read mount status get eintr");
                        continue;
                    }
                    Err(e) => {
                        return Err(SessionFailure(format!("get mount status failed {:?}", e)));
                    }
                }
            }
        });
        Ok(handle)
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
    file_lock: Arc<Mutex<()>>,
    buf: Vec<u8>,
}

impl FuseChannel {
    fn new(file: File, file_lock: Arc<Mutex<()>>, bufsize: usize) -> Result<Self> {
        Ok(FuseChannel {
            file,
            file_lock,
            buf: vec![0x0u8; bufsize],
        })
    }

    fn read(&mut self, len: usize, offset: usize) -> Result<()> {
        let read_buf = &mut self.buf[offset..offset + len];
        let mut total: usize = 0;
        let fd = self.file.as_raw_fd();
        while total < len {
            match read(fd, read_buf) {
                Ok(size) => {
                    total += size;
                }
                Err(e) => match e {
                    Errno::ENOENT => {
                        // ENOENT means the operation was interrupted, it's safe
                        // to restart
                        trace!("restart reading");
                        continue;
                    }
                    Errno::EINTR => {
                        trace!("failld read EINTR");
                        continue;
                    }
                    // EAGIN requires the caller to handle it, and the current implementation assumes that FD is blocking.
                    Errno::EAGAIN => {
                        trace!("failld read EAGAIN");
                        return Err(IoError(e.into()));
                    }
                    Errno::ENODEV => {
                        info!("fuse filesystem umounted");
                        return Ok(());
                    }
                    e => {
                        warn! {"read fuse dev failed on fd {}: {}", fd, e};
                        return Err(SessionFailure(format!("read new request: {:?}", e)));
                    }
                },
            }
        }
        Ok(())
    }

    /// Get next available FUSE request from the underlying fuse device file.
    ///
    /// use-t reuses the same fd for all channels, which means multiple requests
    /// will exist on this fd. We need to read the buffer corresponding to the
    /// header size first to obtain the size, and then read the remaining part.
    /// Due to the two-step reading process, we need to use a mutex lock to ensure
    /// the correctness of the reading.
    ///
    /// Returns:
    /// - Ok(None): signal has pending on the exiting event channel
    /// - Ok(Some((reader, writer))): reader to receive request and writer to send reply
    /// - Err(e): error message
    pub fn get_request(&mut self) -> Result<Option<(Reader, FuseDevWriter)>> {
        let file_lock = self.file_lock.clone();
        let result = file_lock.lock();
        let fd = self.file.as_raw_fd();
        let size = size_of::<InHeader>();
        // read header
        self.read(size, 0)?;
        let in_header = InHeader::from_slice(&self.buf[0..size]);
        let header_len = in_header.unwrap().len as usize;
        let should_read_size = header_len - size;
        if should_read_size > 0 {
            self.read(should_read_size, size)?;
        }
        drop(result);

        let buf = unsafe { std::slice::from_raw_parts_mut(self.buf.as_mut_ptr(), self.buf.len()) };
        // Reader::new() and Writer::new() should always return success.
        let reader = Reader::from_fuse_buffer(FuseBuf::new(&mut self.buf[..header_len])).unwrap();
        let writer = FuseDevWriter::new(fd, buf).unwrap();
        Ok(Some((reader, writer)))
    }
}

fn fuse_kern_mount(
    mountpoint: &Path,
    fsname: &str,
    subtype: &str,
    rd_only: bool,
) -> Result<(File, File)> {
    unsafe { signal(Signal::SIGCHLD, SigHandler::SigDfl) }
        .map_err(|e| SessionFailure(format!("fail to reset SIGCHLD handler{:?}", e)))?;

    let (fd0, fd1) = socketpair(
        AddressFamily::Unix,
        SockType::Stream,
        None,
        SockFlag::empty(),
    )
    .map_err(|e| SessionFailure(format!("create socket failed {:?}", e)))?;

    setsockopt(fd0, SndBuf, &FS_SND_SIZE)
        .map_err(|e| SessionFailure(format!("set fd0 socket snd size {:?}", e)))?;
    setsockopt(fd0, RcvBuf, &FS_SND_SIZE)
        .map_err(|e| SessionFailure(format!("set fd0 socket rcv size {:?}", e)))?;
    setsockopt(fd1, SndBuf, &FS_SND_SIZE)
        .map_err(|e| SessionFailure(format!("set fd1 socket snd size {:?}", e)))?;
    setsockopt(fd1, RcvBuf, &FS_SND_SIZE)
        .map_err(|e| SessionFailure(format!("set fd1 socket rcv size {:?}", e)))?;

    let (mon_fd0, mon_fd1) = socketpair(
        AddressFamily::Unix,
        SockType::Stream,
        None,
        SockFlag::empty(),
    )
    .map_err(|e| SessionFailure(format!("create mon socket failed {:?}", e)))?;

    let res;
    unsafe {
        res = fork().map_err(|e| SessionFailure(format!("fork mount_macfuse failed {:?}", e)))?;
    }

    match res {
        ForkResult::Parent { .. } => {
            close(fd0).map_err(|e| SessionFailure(format!("parent close fd0 failed {:?}", e)))?;
            close(mon_fd0)
                .map_err(|e| SessionFailure(format!("parent close mon fd0 failed {:?}", e)))?;
            unsafe { Ok((File::from_raw_fd(fd1), File::from_raw_fd(mon_fd1))) }
        }
        ForkResult::Child => {
            close(fd1).map_err(|e| SessionFailure(format!("child close fd1 failed {:?}", e)))?;
            close(mon_fd1)
                .map_err(|e| SessionFailure(format!("child close mon fd1 failed {:?}", e)))?;

            let mut daemon_path: Vec<u8> = Vec::with_capacity(PROC_PIDPATHINFO_MAXSIZE as usize);
            unsafe {
                let res = proc_pidpath(
                    getpid().as_raw(),
                    daemon_path.as_mut_ptr() as *mut libc::c_void,
                    PROC_PIDPATHINFO_MAXSIZE as u32,
                );
                if res > 0 {
                    daemon_path.set_len(res as usize);
                }
            };
            if !daemon_path.is_empty() {
                let daemon_path = String::from_utf8(daemon_path)
                    .map_err(|e| SessionFailure(format!("get pid path failed {:?}", e)))?;
                std::env::set_var("_FUSE_DAEMON_PATH", daemon_path);
            }

            std::env::set_var("_FUSE_CALL_BY_LIB", "1");
            std::env::set_var("_FUSE_COMMFD", format!("{}", fd0));
            std::env::set_var("_FUSE_MONFD", format!("{}", mon_fd0));
            std::env::set_var("_FUSE_COMMVERS", "2");

            let mut cmd = Command::new(FUSE_NFSSRV_PATH);
            cmd.arg("--noatime=true")
                .arg("--noatime=true")
                // .arg("-d")
                // .arg("-c")
                .args(["--volname", &format!("{}-{}", fsname, subtype)]);
            if rd_only {
                cmd.arg("-r");
            }
            cmd.arg(mountpoint);
            cmd.exec();
            panic!("never arrive here")
        }
    }
}
/// Umount a fuse file system
fn fuse_kern_umount(file: File) -> Result<()> {
    let msg = b"unmount";
    send(file.as_raw_fd(), msg, MsgFlags::empty())
        .map_err(|e| SessionFailure(format!("send unmount failed {:?}", e)))?;

    drop(file);

    Ok(())
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
        let ch = FuseChannel::new(unsafe { File::from_raw_fd(0) }, Arc::new(Mutex::new(())), 3);
        assert!(ch.is_ok());
    }
}

use crate::abi::fuse_abi::InHeader;
#[cfg(feature = "async-io")]
pub use asyncio::FuseDevTask;

#[cfg(feature = "async-io")]
/// Task context to handle fuse request in asynchronous mode.
mod asyncio {
    use std::os::unix::io::RawFd;
    use std::sync::Arc;

    use crate::api::filesystem::AsyncFileSystem;
    use crate::api::server::Server;
    use crate::async_util::{AsyncDriver, AsyncExecutorState, AsyncUtil};
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
                        let reader = Reader::new(FuseBuf::new(&mut self.buf[0..len])).unwrap();
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
        use std::sync::Arc;

        use super::*;
        use crate::api::server::Server;
        use crate::api::{Vfs, VfsOptions};
        use crate::async_util::{AsyncDriver, AsyncExecutor, AsyncExecutorState};

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
