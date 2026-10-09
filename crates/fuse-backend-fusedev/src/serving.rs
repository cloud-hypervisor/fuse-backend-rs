// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! The unified serving layer of the fusedev transport.
//!
//! A *serving layer* owns a mounted [`FuseSession`], drives it with worker
//! threads and turns [`Drop`] into teardown: stop accepting new requests,
//! let in-flight requests finish, unmount the session and join all
//! workers. Three implementations share that shape:
//!
//! | implementation       | handler model        | transport            |
//! |----------------------|----------------------|----------------------|
//! | [`SyncFuseServing`]  | `F: FileSystem`      | classic `/dev/fuse`  |
//! | `AsyncFuseServing`   | `F: AsyncFileSystem` | classic `/dev/fuse`  |
//! | `UringFuseServing`   | `F: FileSystem`      | FUSE-over-io_uring   |
//!
//! The axes a serving layer owns are the *transport* and the *handler
//! model* — both fixed at the type level — plus the *worker count*, a
//! field of every serving configuration. Two knobs that look like serving
//! concerns deliberately are not:
//!
//! - *blocking vs non-blocking reception* is a configuration of the
//!   classic transport ([`SyncServingConfig::blocking`]): both reception
//!   modes serve the same handlers with the same semantics, so it stays a
//!   channel-level knob instead of becoming a distinct serving type;
//! - *relaying an async request to synchronous handlers* is a file-system
//!   level policy — see the passthrough driver's async handlers — and is
//!   invisible to the serving layer.
//!
//! # Choosing a serving layer
//!
//! Three inputs drive the choice:
//!
//! - **Kernel**: `UringFuseServing` needs Linux 6.14+ *and* the runtime
//!   fuse module parameter `enable_uring` turned on — a version check
//!   alone proves neither, so probe by constructing and fall back on
//!   `Error::UringNotSupported`. Everywhere else, including macOS, the
//!   classic transport is the choice.
//! - **Workload**: on a uring-capable kernel, metadata-heavy workloads
//!   gain the most (3.7x file creation at 8 threads), while large
//!   sequential IO currently regresses on uring — a known upstream
//!   limitation analyzed in `docs/fuse-uring-performance.md` in the
//!   repository — so classic multi-worker serving stays the throughput
//!   choice there.
//! - **Backing storage**: with local storage, synchronous handlers
//!   (`FileSystem`) saturate with one worker per CPU. When every request
//!   hides a network round trip, asynchronous handlers
//!   (`AsyncFileSystem`) decouple the request concurrency from the
//!   worker count.
//!
//! `AsyncFuseServing` needs the `async-io` feature and `UringFuseServing`
//! the `uring` feature; [`SyncFuseServing`] is always available.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};
use std::thread::{self, JoinHandle};

use fuse_backend_core::api::filesystem::FileSystem;
use fuse_backend_core::api::server::Server;

use crate::{Error, FuseChannelExt, FuseSession, Result};

/// A running serving layer that owns a mounted [`FuseSession`].
///
/// Semantics, uniform across implementations:
///
/// - A serving layer is constructed on an already mounted session and
///   starts its worker threads; the constructor returns once the workers
///   have started — the asynchronous and io_uring implementations
///   additionally wait for the workers to report readiness — and on
///   failure tears the session down and returns an error instead of a
///   serving layer silently missing a worker.
/// - Dropping the serving layer stops accepting new requests, lets
///   in-flight requests finish, unmounts the session and joins all
///   workers.
/// - [`FuseServing::wait`] blocks until the workers have drained after
///   teardown driven from outside the process, without tearing anything
///   down itself.
///
/// # Selecting the transport at runtime
///
/// The handler model is a type-level axis, so a daemon that picks its
/// transport at runtime switches implementations behind
/// `Box<dyn FuseServing>`:
///
/// ```text
/// let serving: Box<dyn FuseServing> =
///     match UringFuseServing::new(session, server.clone(), uring_cfg) {
///         Ok(s) => Box::new(s),
///         Err(Error::UringNotSupported) => {
///             // The uring constructor tears the failed session down, so
///             // remount before falling back to the classic transport.
///             Box::new(SyncFuseServing::new(remount()?, server, sync_cfg)?)
///         }
///         Err(e) => return Err(e),
///     };
/// ```
pub trait FuseServing: Send {
    /// The mounted session this serving layer owns.
    fn session(&self) -> &FuseSession;

    /// Block until all worker threads have exited.
    ///
    /// This serves teardown driven from outside the process — e.g. an
    /// admin `umount(8)` of the mountpoint — which ends every worker's
    /// reception with `ENODEV`. Dropping the serving layer instead
    /// performs the teardown itself and joins the workers.
    fn wait(&self);
}

/// Configuration of the synchronous serving layer.
#[derive(Clone, Copy, Debug)]
pub struct SyncServingConfig {
    /// Number of worker threads serving requests in parallel. Every worker
    /// owns one channel of the session, so the memory used by request
    /// buffers scales with this number. Values smaller than 1 are clamped
    /// to 1.
    ///
    /// On macOS the session exposes a single channel, so values greater
    /// than 1 are rejected by [`SyncFuseServing::new`].
    pub workers: usize,
    /// Receive requests with plain blocking reads on channels cloned with
    /// `FUSE_DEV_IOC_CLONE` instead of epoll-based channels, saving the
    /// `epoll_wait` syscall per request (kernel >= 4.2).
    ///
    /// Blocking channels cannot be woken by [`FuseSession::wake()`]; they
    /// exit when the connection is torn down. On macOS, where reception is
    /// inherently blocking, the knob is ignored.
    pub blocking: bool,
}

impl Default for SyncServingConfig {
    fn default() -> Self {
        SyncServingConfig {
            workers: 1,
            blocking: false,
        }
    }
}

/// Serve FUSE requests with synchronous worker threads over the classic
/// `/dev/fuse` transport.
///
/// The serving layer takes ownership of the mounted session: dropping it
/// unmounts the filesystem and joins all serving threads. This is the
/// serving loop every hand-rolled fusedev daemon duplicates, kept as a
/// library type: each worker owns a channel, receives requests from it and
/// dispatches them to the [`Server`] until the session is torn down.
///
/// On Linux every worker owns a channel created by
/// [`FuseSession::new_channel()`] — or, with
/// [`SyncServingConfig::blocking`], a blocking channel from
/// `FuseSession::new_blocking_channel()`. On macOS the session exposes a
/// single channel whose reception is inherently blocking, so the
/// configuration is validated accordingly.
pub struct SyncFuseServing<F: FileSystem + Send + Sync + 'static> {
    session: FuseSession,
    workers: WorkerSet,
    _fs: std::marker::PhantomData<F>,
}

impl<F: FileSystem + Send + Sync + 'static> SyncFuseServing<F> {
    /// Create a new synchronous serving layer on an already mounted session.
    ///
    /// All channels are created up front and one worker thread is spawned
    /// per channel. If a channel cannot be created or a worker cannot be
    /// spawned, the session is torn down and the error returned instead of
    /// a serving layer silently missing a worker.
    pub fn new(
        session: FuseSession,
        server: Arc<Server<F>>,
        cfg: SyncServingConfig,
    ) -> Result<SyncFuseServing<F>> {
        let workers = cfg.workers.max(1);

        #[cfg(target_os = "macos")]
        {
            // macFUSE hands the session out through a single channel and
            // its reception is a plain blocking read, so neither more
            // workers nor the blocking knob apply: error loudly instead of
            // silently clamping.
            if workers > 1 {
                return Err(Error::SessionFailure(format!(
                    "sync serving: the macOS session exposes a single channel, \
                     {workers} workers requested"
                )));
            }
            if cfg.blocking {
                warn!(
                    "sync serving: macOS reception is inherently blocking, \
                     ignoring the `blocking` configuration"
                );
            }
        }

        #[cfg(target_os = "linux")]
        {
            if cfg.blocking {
                spawn_workers(session, server, workers, FuseSession::new_blocking_channel)
            } else {
                spawn_workers(session, server, workers, FuseSession::new_channel)
            }
        }
        #[cfg(target_os = "macos")]
        {
            // macFUSE reception is a plain blocking read on the single
            // session channel; the configuration was validated above.
            spawn_workers(session, server, workers, FuseSession::new_channel)
        }
    }
}

impl<F: FileSystem + Send + Sync + 'static> FuseServing for SyncFuseServing<F> {
    fn session(&self) -> &FuseSession {
        &self.session
    }

    fn wait(&self) {
        self.workers.wait();
    }
}

impl<F: FileSystem + Send + Sync + 'static> Drop for SyncFuseServing<F> {
    fn drop(&mut self) {
        // Waking the session is a no-op unless epoll-based channels are
        // registered with it, so it is unconditional: blocking channels
        // exit through the ENODEV that tearing the connection down
        // produces.
        self.workers.stop(&mut self.session, true);
    }
}

/// Create `workers` channels and spawn one serving thread per channel.
fn spawn_workers<F, C>(
    mut session: FuseSession,
    server: Arc<Server<F>>,
    workers: usize,
    new_channel: impl Fn(&FuseSession) -> Result<C>,
) -> Result<SyncFuseServing<F>>
where
    F: FileSystem + Send + Sync + 'static,
    C: FuseChannelExt + Send + 'static,
{
    // Create all channels up front so a failure surfaces before any thread
    // is spawned.
    let mut channels = Vec::with_capacity(workers);
    for _ in 0..workers {
        channels.push(new_channel(&session)?);
    }

    let mut set = WorkerSet::new();
    for (id, ch) in channels.into_iter().enumerate() {
        let server = server.clone();
        let tracker = set.tracker();
        match thread::Builder::new()
            .name(format!("fuse-sync-{id}"))
            .spawn(move || {
                let _exited = tracker.exit_guard();
                svc_loop(&server, ch);
            }) {
            Ok(handle) => set.push(handle),
            Err(e) => {
                set.stop(&mut session, true);
                return Err(Error::SessionFailure(format!(
                    "sync: spawn worker {id}: {e}"
                )));
            }
        }
    }

    Ok(SyncFuseServing {
        session,
        workers: set,
        _fs: std::marker::PhantomData,
    })
}

/// Serve requests from one channel until the session is torn down.
///
/// The loop every hand-rolled fusedev daemon duplicates: block for the
/// next request, dispatch it to the server, and stop when the session goes
/// away — `Ok(None)` after a wake or an unmount, `EBADF` when the kernel
/// has already shut the connection down.
fn svc_loop<F: FileSystem + Send + Sync + 'static, C: FuseChannelExt>(
    server: &Arc<Server<F>>,
    mut ch: C,
) {
    loop {
        match ch.next_request() {
            Ok(Some((reader, writer))) => {
                if let Err(e) = server.handle_message(reader, writer, None, None) {
                    match e {
                        // The kernel has shut down this session.
                        fuse_backend_core::Error::EncodeMessage(ref err)
                            if err.raw_os_error() == Some(libc::EBADF) =>
                        {
                            break;
                        }
                        _ => {
                            warn!("sync serving: failed to handle message: {e}");
                            continue;
                        }
                    }
                }
            }
            Ok(None) => {
                info!("sync worker exits");
                break;
            }
            Err(e) => {
                warn!("sync serving: failed to read a request: {e}");
                break;
            }
        }
    }
}

/// The shared lifecycle state of a serving layer's worker threads.
///
/// The `exit` flag lets cooperative workers stop early, the exit tracker
/// backs [`FuseServing::wait`], and the handles back the uniform teardown
/// of [`WorkerSet::stop`].
pub(crate) struct WorkerSet {
    exit: Arc<AtomicBool>,
    tracker: Arc<WorkerExitTracker>,
    handles: Vec<JoinHandle<()>>,
}

impl WorkerSet {
    pub(crate) fn new() -> Self {
        WorkerSet {
            exit: Arc::new(AtomicBool::new(false)),
            tracker: Arc::new(WorkerExitTracker::default()),
            handles: Vec::new(),
        }
    }

    /// The exit flag shared with every worker.
    // Only the async and uring serving layers hand the flag to their
    // workers, so the accessor only exists in configurations that compile
    // one of them.
    #[cfg(any(
        all(target_os = "linux", feature = "async-io"),
        all(target_os = "linux", feature = "uring")
    ))]
    pub(crate) fn exit_flag(&self) -> Arc<AtomicBool> {
        self.exit.clone()
    }

    /// The exit tracker, for arming a guard at the top of a worker thread.
    pub(crate) fn tracker(&self) -> Arc<WorkerExitTracker> {
        self.tracker.clone()
    }

    pub(crate) fn push(&mut self, handle: JoinHandle<()>) {
        self.handles.push(handle);
    }

    /// Signal all workers to stop, tear the session down and join them.
    ///
    /// `wake` wakes the epoll-based channels registered with the session,
    /// which snaps their `epoll_wait` out immediately; blocking channels
    /// and io_uring workers instead exit through the `ENODEV`/ring-error
    /// completion that tearing the connection down produces. In-flight
    /// requests are still served and replied before a worker exits.
    pub(crate) fn stop(&mut self, session: &mut FuseSession, wake: bool) {
        self.exit.store(true, Ordering::Release);
        if wake {
            let _ = session.wake();
        }
        let _ = session.umount();
        let handles = std::mem::take(&mut self.handles);
        for handle in handles {
            let _ = handle.join();
        }
    }

    /// Block until every worker thread has exited; see
    /// [`FuseServing::wait`].
    pub(crate) fn wait(&self) {
        let mut finished = self.tracker.finished.lock().unwrap();
        while *finished < self.handles.len() {
            finished = self.tracker.notified.wait(finished).unwrap();
        }
    }
}

/// Counts worker threads that have exited, so [`WorkerSet::wait`] can
/// block until all of them have drained without tearing the session down.
#[derive(Default)]
pub(crate) struct WorkerExitTracker {
    finished: Mutex<usize>,
    notified: Condvar,
}

impl WorkerExitTracker {
    /// Arm a guard that counts this worker when its thread exits.
    pub(crate) fn exit_guard(self: &Arc<Self>) -> WorkerExitGuard {
        WorkerExitGuard {
            tracker: self.clone(),
        }
    }
}

/// Reports one worker exit when dropped, i.e. when its thread finishes.
pub(crate) struct WorkerExitGuard {
    tracker: Arc<WorkerExitTracker>,
}

impl Drop for WorkerExitGuard {
    fn drop(&mut self) {
        let mut finished = self.tracker.finished.lock().unwrap();
        *finished += 1;
        self.tracker.notified.notify_all();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vmm_sys_util::tempdir::TempDir;

    /// A file system with every handler defaulted: enough to construct a
    /// server around it, which is all the error-path tests below need.
    struct StubFileSystem;

    impl FileSystem for StubFileSystem {
        type Inode = u64;
        type Handle = u64;
    }

    #[test]
    fn test_sync_serving_unmounted_session() {
        let dir = TempDir::new().unwrap();
        let server = Arc::new(Server::new(StubFileSystem));
        // A session that was never mounted has no channel to hand out.
        let se = FuseSession::new(dir.as_path(), "test", "", false).unwrap();
        assert!(SyncFuseServing::new(se, server, SyncServingConfig::default()).is_err());
    }

    #[cfg(target_os = "macos")]
    #[test]
    fn test_sync_serving_macos_rejects_multiple_workers() {
        let dir = TempDir::new().unwrap();
        let server = Arc::new(Server::new(StubFileSystem));
        // macFUSE exposes a single channel, so multi-worker serving is
        // rejected before any channel is created.
        let se = FuseSession::new(dir.as_path(), "test", "", false).unwrap();
        let cfg = SyncServingConfig {
            workers: 2,
            blocking: false,
        };
        assert!(SyncFuseServing::new(se, server, cfg).is_err());
    }

    #[test]
    fn test_worker_set_wait_counts_exits() {
        let dir = TempDir::new().unwrap();
        let mut set = WorkerSet::new();
        for _ in 0..2 {
            let tracker = set.tracker();
            let handle = thread::Builder::new()
                .spawn(move || {
                    let _exited = tracker.exit_guard();
                })
                .unwrap();
            set.push(handle);
        }

        // wait() returns once both threads have run to completion, and
        // stop() joins them and drains the set (umount on a session that
        // was never mounted is a no-op).
        let mut session = FuseSession::new(dir.as_path(), "test", "", false).unwrap();
        set.wait();
        set.stop(&mut session, true);
    }

    #[cfg(target_os = "linux")]
    mod linux {
        use super::*;

        use fuse_backend_passthrough::{Config, PassthroughFs};

        fn mount_passthrough(src: &TempDir, mnt: &TempDir, cfg: SyncServingConfig) {
            let fs = PassthroughFs::<()>::new(Config {
                root_dir: src.as_path().to_string_lossy().to_string(),
                do_import: false,
                ..Default::default()
            })
            .unwrap();
            fs.import().unwrap();
            let server = Arc::new(Server::new(fs));

            let mut se = FuseSession::new(mnt.as_path(), "sync_serving_test", "", false).unwrap();
            se.mount().unwrap();

            let serving = SyncFuseServing::new(se, server, cfg).unwrap();

            // IO through the mountpoint covers the whole range from the
            // FUSE_INIT handshake to reads and writes, whichever worker
            // picks each request up.
            assert_eq!(
                std::fs::read(mnt.as_path().join("hello")).unwrap(),
                b"multi-worker"
            );
            let created = mnt.as_path().join("created");
            std::fs::write(&created, b"written through the sync mount").unwrap();
            assert_eq!(
                std::fs::read(&created).unwrap(),
                b"written through the sync mount"
            );

            // Dropping the serving layer unmounts the session and joins
            // the workers, so the mountpoint is an empty directory
            // afterwards.
            drop(serving);
            assert!(std::fs::read(mnt.as_path().join("hello")).is_err());
        }

        #[test]
        fn test_sync_serving_multi_worker() {
            let src = TempDir::new().unwrap();
            std::fs::write(src.as_path().join("hello"), b"multi-worker").unwrap();
            let mnt = TempDir::new().unwrap();

            mount_passthrough(
                &src,
                &mnt,
                SyncServingConfig {
                    workers: 2,
                    blocking: false,
                },
            );
        }

        #[test]
        fn test_sync_serving_blocking_channels() {
            let src = TempDir::new().unwrap();
            std::fs::write(src.as_path().join("hello"), b"multi-worker").unwrap();
            let mnt = TempDir::new().unwrap();

            mount_passthrough(
                &src,
                &mnt,
                SyncServingConfig {
                    workers: 2,
                    blocking: true,
                },
            );
        }
    }
}
