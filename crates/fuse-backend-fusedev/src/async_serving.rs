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

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Sender};
use std::sync::Arc;
use std::thread::{self, JoinHandle};

use fuse_backend_core::api::filesystem::AsyncFileSystem;
use fuse_backend_core::api::server::Server;
use fuse_backend_core::async_runtime::Runtime;

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
    exit: Arc<AtomicBool>,
    workers: Vec<JoinHandle<()>>,
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

        let exit = Arc::new(AtomicBool::new(false));
        let (ready_tx, ready_rx) = channel::<bool>();
        let mut handles = Vec::with_capacity(workers);
        for (id, file) in files.into_iter().enumerate() {
            let handle = thread::Builder::new()
                .name(format!("fuse-async-{id}"))
                .spawn({
                    let server = server.clone();
                    let exit = exit.clone();
                    let ready_tx = ready_tx.clone();
                    move || {
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
                Ok(handle) => handles.push(handle),
                Err(e) => {
                    stop_workers(&mut session, &exit, handles);
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
                stop_workers(&mut session, &exit, handles);
                return Err(Error::SessionFailure(
                    "async: worker exited during startup".to_string(),
                ));
            }
        }

        Ok(AsyncFuseServing {
            session,
            exit,
            workers: handles,
            _fs: std::marker::PhantomData,
        })
    }
}

/// Signal all workers to stop, tear the connection down and join them.
///
/// Pending reads on the cloned file descriptions cannot be woken with
/// [`FuseSession::wake()`], which only reaches the epoll-based channels:
/// tearing the connection down completes them with `ENODEV` instead, which
/// ends `poll_handler()`. Requests already in flight are still served and
/// replied before a worker exits.
fn stop_workers(session: &mut FuseSession, exit: &Arc<AtomicBool>, workers: Vec<JoinHandle<()>>) {
    exit.store(true, Ordering::Release);
    let _ = session.umount();
    for handle in workers {
        let _ = handle.join();
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

impl<F: AsyncFileSystem + Send + Sync + 'static> Drop for AsyncFuseServing<F> {
    fn drop(&mut self) {
        let workers = std::mem::take(&mut self.workers);
        stop_workers(&mut self.session, &self.exit, workers);
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
}
