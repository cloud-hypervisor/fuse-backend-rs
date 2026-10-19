// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Multi-worker serving for the asynchronous fusedev transport.
//!
//! A [`FuseDevTask`] serves all requests from a single async runtime, which
//! caps throughput at what one thread can drive. [`AsyncFuseServing`] scales
//! the classic `/dev/fuse` transport out to N worker threads, mirroring the
//! multi-channel design of the synchronous transport: every worker owns
//! - a `/dev/fuse` file description cloned with `FUSE_DEV_IOC_CLONE`,
//! - a single-threaded async [`Runtime`] (with its own io_uring ring when
//!   the tokio-uring runtime is selected),
//! - a [`FuseDevTask`] serving each request to completion on that thread.
//!
//! The kernel hands each request to whichever worker has a pending read,
//! and every request is served wholly by one worker, so `?Send` request
//! futures and the zero-copy buffer traits keep their single-thread
//! guarantees.

use std::sync::mpsc::{channel, Sender};
use std::sync::Arc;
use std::thread;

use fuse_backend_core::api::filesystem::AsyncFileSystem;
use fuse_backend_core::api::server::Server;
use fuse_backend_core::async_runtime::Runtime;

use crate::serving::{FuseServing, WorkerSet};
use crate::{Error, FuseDevTask, FuseSession, Result};

/// Configuration of the multi-worker asynchronous serving layer.
#[derive(Clone, Copy, Debug)]
pub struct AsyncServingConfig {
    /// Number of worker threads serving requests in parallel. Every worker
    /// owns a `/dev/fuse` file description and a single-threaded async
    /// runtime, so kernel memory locked by io_uring rings and the memory
    /// used by request buffers both scale with this number. Values smaller
    /// than 1 are clamped to 1.
    pub workers: usize,
    /// Maximum number of requests processed concurrently by each worker.
    /// Every in-flight request owns one buffer of the session buffer size,
    /// so the memory used by in-flight requests scales with
    /// `workers * max_inflight`. `0` selects the `FuseDevTask` default.
    pub max_inflight: usize,
}

impl Default for AsyncServingConfig {
    fn default() -> Self {
        AsyncServingConfig {
            workers: 1,
            max_inflight: 0,
        }
    }
}

/// Serve FUSE requests with multiple asynchronous workers.
///
/// The serving layer takes ownership of the mounted session: dropping it
/// unmounts the filesystem and joins all serving threads.
pub struct AsyncFuseServing<F: AsyncFileSystem + Send + Sync + 'static> {
    session: FuseSession,
    workers: WorkerSet,
    _fs: std::marker::PhantomData<F>,
}

impl<F: AsyncFileSystem + Send + Sync + 'static> AsyncFuseServing<F> {
    /// Create a new multi-worker asynchronous serving layer on an already
    /// mounted session.
    ///
    /// Every worker clones the session's `/dev/fuse` file description with
    /// `FUSE_DEV_IOC_CLONE` and serves requests from it on its own async
    /// runtime. Unlike the FUSE-over-io_uring transport, no request needs
    /// special handling: any worker may serve the `FUSE_INIT` handshake, so
    /// the constructor doesn't consume it beforehand.
    ///
    /// The constructor returns once all workers have confirmed they are
    /// serving. If one dies during startup, e.g. because io_uring ring
    /// allocation fails once the other workers' rings exhausted
    /// `RLIMIT_MEMLOCK`, the session is torn down and an error returned
    /// instead of a serving layer silently missing a worker.
    pub fn new(
        mut session: FuseSession,
        server: Arc<Server<F>>,
        cfg: AsyncServingConfig,
    ) -> Result<AsyncFuseServing<F>> {
        let workers = cfg.workers.max(1);
        let max_inflight = cfg.max_inflight;
        let buf_size = session.bufsize();

        // Clone one file description per worker up front, so cloning
        // failures are reported before any thread is spawned. Each worker
        // gets an independent file description, so the `O_NONBLOCK` flag
        // its `FuseDevTask` sets and the reads its runtime issues never
        // interfere with the other workers.
        let mut files = Vec::with_capacity(workers);
        for _ in 0..workers {
            files.push(session.clone_fuse_file()?);
        }

        let mut set = WorkerSet::new();
        let exit = set.exit_flag();
        let tracker = set.tracker();
        let (ready_tx, ready_rx) = channel::<bool>();
        for (id, file) in files.into_iter().enumerate() {
            let handle = thread::Builder::new()
                .name(format!("fuse-async-{id}"))
                .spawn({
                    let server = server.clone();
                    let exit = exit.clone();
                    let tracker = tracker.clone();
                    let ready_tx = ready_tx.clone();
                    move || {
                        // Report the thread exit to the serving layer's
                        // wait().
                        let _exited = tracker.exit_guard();
                        // Runtime and task creation may panic (io_uring
                        // ring allocation, fd setup); the guard turns that
                        // into a constructor error below.
                        let guard = StartupGuard {
                            tx: &ready_tx,
                            reported: false,
                        };
                        let runtime = Runtime::new();
                        let mut task = match max_inflight {
                            0 => FuseDevTask::new(buf_size, file, server, exit),
                            n => {
                                FuseDevTask::new_with_max_inflight(buf_size, file, server, exit, n)
                            }
                        };
                        guard.ready();
                        runtime.block_on(task.poll_handler());
                    }
                });
            match handle {
                Ok(handle) => set.push(handle),
                Err(e) => {
                    set.stop(&mut session, false);
                    return Err(Error::SessionFailure(format!(
                        "async: spawn worker {id}: {e}"
                    )));
                }
            }
        }
        drop(ready_tx);

        // Wait until all workers have confirmed they are serving, bailing
        // out on the first one that died during startup.
        for _ in 0..workers {
            if ready_rx.recv() != Ok(true) {
                set.stop(&mut session, false);
                return Err(Error::SessionFailure(
                    "async: worker exited during startup".to_string(),
                ));
            }
        }

        Ok(AsyncFuseServing {
            session,
            workers: set,
            _fs: std::marker::PhantomData,
        })
    }
}

impl<F: AsyncFileSystem + Send + Sync + 'static> Drop for AsyncFuseServing<F> {
    fn drop(&mut self) {
        // Pending reads on the workers' cloned file descriptions cannot be
        // woken with FuseSession::wake(), which only reaches epoll-based
        // channels: tearing the connection down completes them with ENODEV
        // instead, which ends poll_handler(). Requests already in flight
        // are still served and replied before a worker exits.
        self.workers.stop(&mut self.session, false);
    }
}

impl<F: AsyncFileSystem + Send + Sync + 'static> FuseServing for AsyncFuseServing<F> {
    fn session(&self) -> &FuseSession {
        &self.session
    }

    fn wait(&self) {
        self.workers.wait();
    }
}

/// Reports a worker that exits before signaling readiness, so a startup
/// panic becomes a constructor error instead of a serving layer silently
/// missing a worker.
struct StartupGuard<'a> {
    tx: &'a Sender<bool>,
    reported: bool,
}

impl StartupGuard<'_> {
    /// Signal that the worker is serving, and disarm the guard.
    fn ready(mut self) {
        let _ = self.tx.send(true);
        self.reported = true;
    }
}

impl Drop for StartupGuard<'_> {
    fn drop(&mut self) {
        if !self.reported {
            let _ = self.tx.send(false);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use vmm_sys_util::tempdir::TempDir;

    use fuse_backend_passthrough::{Config, PassthroughFs};

    #[test]
    fn test_async_serving_unmounted_session() {
        let dir = TempDir::new().unwrap();
        let fs = PassthroughFs::<()>::new(Config::default()).unwrap();
        let server = Arc::new(Server::new(fs));
        // A session that was never mounted has no fuse file to clone.
        let se = FuseSession::new(dir.as_path(), "test", "", false).unwrap();
        assert!(AsyncFuseServing::new(se, server, AsyncServingConfig::default()).is_err());
    }

    #[test]
    fn test_async_serving_multi_worker() {
        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"multi-worker").unwrap();
        let mnt = TempDir::new().unwrap();

        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        let server = Arc::new(Server::new(fs));

        let mut se = FuseSession::new(mnt.as_path(), "async_serving_test", "", false).unwrap();
        se.mount().unwrap();

        let serving = AsyncFuseServing::new(
            se,
            server,
            AsyncServingConfig {
                workers: 2,
                max_inflight: 0,
            },
        )
        .unwrap();

        // IO through the mountpoint: each request is picked up by whichever
        // of the two workers reads it first, covering the whole range from
        // the FUSE_INIT handshake to reads and writes.
        assert_eq!(
            std::fs::read(mnt.as_path().join("hello")).unwrap(),
            b"multi-worker"
        );
        let created = mnt.as_path().join("created");
        std::fs::write(&created, b"written through the async mount").unwrap();
        assert_eq!(
            std::fs::read(&created).unwrap(),
            b"written through the async mount"
        );

        // Dropping the serving layer unmounts the session and joins the
        // workers, so the mountpoint is an empty directory afterwards.
        drop(serving);
        assert!(std::fs::read(mnt.as_path().join("hello")).is_err());
    }

    #[test]
    fn test_async_serving_detach() {
        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"detach").unwrap();
        let mnt = TempDir::new().unwrap();

        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        let server = Arc::new(Server::new(fs));

        let mut se = FuseSession::new(mnt.as_path(), "async_serving_test", "", false).unwrap();
        se.mount().unwrap();
        let serving =
            Arc::new(AsyncFuseServing::new(se, server, AsyncServingConfig::default()).unwrap());
        assert_eq!(
            std::fs::read(mnt.as_path().join("hello")).unwrap(),
            b"detach"
        );

        // Detaching through the shared serving layer stops the workers, so
        // a thread waiting for them returns.
        let (tx, rx) = std::sync::mpsc::channel();
        let waiter = {
            let serving = serving.clone();
            std::thread::spawn(move || {
                serving.wait();
                tx.send(()).unwrap();
            })
        };
        serving.session().detach().unwrap();
        rx.recv_timeout(std::time::Duration::from_secs(5))
            .expect("the workers didn't stop after detach()");
        waiter.join().unwrap();
        assert!(std::fs::read(mnt.as_path().join("hello")).is_err());
    }

    mod gated_dir {
        use std::ffi::CStr;
        use std::io;
        use std::sync::mpsc::Sender;
        use std::sync::Arc;
        use std::time::Duration;

        use async_trait::async_trait;
        use fuse_backend_core::abi::fuse_abi::stat64;
        use fuse_backend_core::api::filesystem::{
            AsyncFileSystem, Context, DirEntry, Entry, FileSystem, FsOptions, OpenOptions,
        };
        use tokio::sync::Semaphore;

        const ROOT: u64 = 1;
        const DIR: u64 = 2;
        /// The files in `dir`, with inodes from 3 on.
        pub(super) const FILES: [&str; 3] = ["a", "b", "c"];
        const DIR_HANDLE: u64 = 7;

        fn entry(inode: u64) -> Entry {
            let mut attr: stat64 = unsafe { std::mem::zeroed() };
            attr.st_ino = inode;
            if inode <= DIR {
                attr.st_mode = libc::S_IFDIR | 0o755;
                attr.st_nlink = 2;
            } else {
                attr.st_mode = libc::S_IFREG | 0o644;
                attr.st_nlink = 1;
            }
            Entry {
                inode,
                attr,
                attr_timeout: Duration::from_secs(60),
                entry_timeout: Duration::from_secs(60),
                ..Default::default()
            }
        }

        fn error(errno: i32) -> io::Error {
            io::Error::from_raw_os_error(errno)
        }

        /// The root holds the directory `dir` with `FILES`. Listing `dir` waits until `gate`
        /// opens, which a lookup of `gate` in the root does. Only the async handlers serve
        /// directories, and the sync ones fail.
        pub(super) struct GatedDirFs {
            /// Whether to ask the kernel for READDIRPLUS instead of READDIR.
            pub(super) plus: bool,
            pub(super) gate: Arc<Semaphore>,
            /// Gets "listing" when a listing starts to wait, and "releasedir" on RELEASEDIR.
            pub(super) events: Sender<&'static str>,
        }

        impl GatedDirFs {
            fn event(&self, event: &'static str) {
                let _ = self.events.send(event);
            }

            async fn list(
                &self,
                inode: u64,
                handle: u64,
                offset: u64,
                mut add_entry: impl FnMut(DirEntry, Entry) -> io::Result<usize>,
            ) -> io::Result<()> {
                if inode != DIR || handle != DIR_HANDLE {
                    return Err(error(libc::EBADF));
                }
                if offset == 0 {
                    self.event("listing");
                    // The permit goes back when it's dropped, so the gate stays open.
                    drop(self.gate.acquire().await);
                }
                for (i, name) in FILES.iter().enumerate().skip(offset as usize) {
                    let inode = i as u64 + 3;
                    let dir_entry = DirEntry {
                        ino: inode,
                        offset: i as u64 + 1,
                        type_: libc::DT_REG as u32,
                        name: name.as_bytes(),
                    };
                    if add_entry(dir_entry, entry(inode))? == 0 {
                        break;
                    }
                }
                Ok(())
            }
        }

        impl FileSystem for GatedDirFs {
            type Inode = u64;
            type Handle = u64;

            fn init(&self, _capable: FsOptions) -> io::Result<FsOptions> {
                if self.plus {
                    Ok(FsOptions::DO_READDIRPLUS)
                } else {
                    Ok(FsOptions::empty())
                }
            }

            fn lookup(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
                match (parent, name.to_bytes()) {
                    (ROOT, b"dir") => Ok(entry(DIR)),
                    (ROOT, b"gate") => {
                        self.gate.add_permits(1);
                        Err(error(libc::ENOENT))
                    }
                    (DIR, name) => FILES
                        .iter()
                        .position(|file| file.as_bytes() == name)
                        .map(|i| entry(i as u64 + 3))
                        .ok_or_else(|| error(libc::ENOENT)),
                    _ => Err(error(libc::ENOENT)),
                }
            }

            fn getattr(
                &self,
                _ctx: &Context,
                inode: u64,
                _handle: Option<u64>,
            ) -> io::Result<(stat64, Duration)> {
                let entry = entry(inode);
                Ok((entry.attr, entry.attr_timeout))
            }

            fn opendir(
                &self,
                _ctx: &Context,
                _inode: u64,
                _flags: u32,
            ) -> io::Result<(Option<u64>, OpenOptions)> {
                Err(error(libc::EIO))
            }

            fn readdir(
                &self,
                _ctx: &Context,
                _inode: u64,
                _handle: u64,
                _size: u32,
                _offset: u64,
                _add_entry: &mut dyn FnMut(DirEntry) -> io::Result<usize>,
            ) -> io::Result<()> {
                Err(error(libc::EIO))
            }

            fn readdirplus(
                &self,
                _ctx: &Context,
                _inode: u64,
                _handle: u64,
                _size: u32,
                _offset: u64,
                _add_entry: &mut dyn FnMut(DirEntry, Entry) -> io::Result<usize>,
            ) -> io::Result<()> {
                Err(error(libc::EIO))
            }
        }

        #[async_trait]
        impl AsyncFileSystem for GatedDirFs {
            async fn async_opendir(
                &self,
                _ctx: &Context,
                inode: u64,
                _flags: u32,
            ) -> io::Result<(Option<u64>, OpenOptions)> {
                match inode {
                    DIR => Ok((Some(DIR_HANDLE), OpenOptions::empty())),
                    _ => Err(error(libc::EACCES)),
                }
            }

            async fn async_readdir(
                &self,
                _ctx: &Context,
                inode: u64,
                handle: u64,
                _size: u32,
                offset: u64,
                add_entry: &mut (dyn FnMut(DirEntry) -> io::Result<usize> + Send),
            ) -> io::Result<()> {
                self.list(inode, handle, offset, |dir_entry, _| add_entry(dir_entry))
                    .await
            }

            async fn async_readdirplus(
                &self,
                _ctx: &Context,
                inode: u64,
                handle: u64,
                _size: u32,
                offset: u64,
                add_entry: &mut (dyn FnMut(DirEntry, Entry) -> io::Result<usize> + Send),
            ) -> io::Result<()> {
                self.list(inode, handle, offset, add_entry).await
            }

            async fn async_releasedir(
                &self,
                _ctx: &Context,
                inode: u64,
                _flags: u32,
                handle: u64,
            ) -> io::Result<()> {
                if inode != DIR || handle != DIR_HANDLE {
                    return Err(error(libc::EBADF));
                }
                self.event("releasedir");
                Ok(())
            }
        }
    }

    #[test]
    fn test_async_serving_readdir() {
        run_gated_readdir(false);
    }

    #[test]
    fn test_async_serving_readdirplus() {
        run_gated_readdir(true);
    }

    /// Closes a semaphore when dropped, so that whatever waits to acquire it fails and goes on.
    struct CloseOnDrop(Arc<tokio::sync::Semaphore>);

    impl Drop for CloseOnDrop {
        fn drop(&mut self) {
            self.0.close();
        }
    }

    /// Lists a directory through a mount with a single worker, while the file system holds
    /// the listing until a lookup in the same mount opens a gate. The lookup only gets served
    /// if the pending listing leaves the worker free.
    fn run_gated_readdir(plus: bool) {
        let timeout = std::time::Duration::from_secs(10);
        let mnt = TempDir::new().unwrap();
        let gate = Arc::new(tokio::sync::Semaphore::new(0));
        let (events_tx, events) = channel();
        let fs = gated_dir::GatedDirFs {
            plus,
            gate: gate.clone(),
            events: events_tx,
        };
        let server = Arc::new(Server::new(fs));

        let mut se = FuseSession::new(mnt.as_path(), "async_serving_test", "", false).unwrap();
        se.mount().unwrap();
        let serving = AsyncFuseServing::new(
            se,
            server,
            AsyncServingConfig {
                workers: 1,
                max_inflight: 0,
            },
        )
        .unwrap();
        // Dropping `serving` waits for the worker, which can't finish a listing that waits at the
        // gate. So close the gate first when the test ends, also when an assert fails.
        let _close_gate = CloseOnDrop(gate.clone());

        let dir = mnt.as_path().join("dir");
        let lister = thread::spawn(move || {
            let mut names: Vec<String> = std::fs::read_dir(dir)
                .unwrap()
                .map(|entry| entry.unwrap().file_name().into_string().unwrap())
                .collect();
            names.sort();
            names
        });
        assert_eq!(events.recv_timeout(timeout), Ok("listing"));

        let gate_path = mnt.as_path().join("gate");
        let (looked_up_tx, looked_up) = channel();
        let opener = thread::spawn(move || {
            assert!(std::fs::metadata(gate_path).is_err());
            looked_up_tx.send(()).unwrap();
        });
        let served = looked_up.recv_timeout(timeout).is_ok();
        if !served {
            // Let the listing finish, so that the threads and the mount go away.
            gate.add_permits(1);
        }
        opener.join().unwrap();
        let names = lister.join().unwrap();
        assert!(served, "the pending listing blocked the worker");
        assert_eq!(names, gated_dir::FILES);
        // The kernel sends RELEASEDIR in the background once the directory is closed.
        assert_eq!(events.recv_timeout(timeout), Ok("releasedir"));

        drop(serving);
        assert!(std::fs::read_dir(mnt.as_path().join("dir")).is_err());
    }
}
