// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! The unified serving layer of the fusedev transport.
//!
//! A *serving layer* owns a mounted [`FuseSession`], drives it with worker
//! threads and turns [`Drop`] into teardown: stop accepting new requests,
//! let in-flight requests finish, unmount the session, end a connection
//! that outlives the unmount and join all workers. Three implementations
//! share that shape:
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

use std::fs::File;
use std::io::Write;
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
/// - Files that are still open on the mount keep its connection up after
///   the unmount. On Linux, [`SyncFuseServing`] and `AsyncFuseServing` end
///   it through fusectl, like `umount -f`, once the workers have replied
///   to the requests they took. Later requests on those files then fail
///   with `ENOTCONN`. Otherwise a child process that inherited a `/dev/fuse` fd
///   would keep the connection up with nobody serving it, and an exec that
///   closes such a file would hang the child for good. This needs fusectl
///   mounted at `/sys/fs/fuse/connections`, where the user that mounted the
///   file system may end the connection. Without it, blocking channels and
///   the tokio-uring runtime serve until the files are closed, and the
///   other workers stop.
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
    /// reception with `ENODEV`. On Linux, another thread can start that
    /// teardown with `FuseSession::detach()` on [`FuseServing::session()`].
    /// The Linux serving layers are `Sync`, so share one as
    /// `dyn FuseServing + Sync` for this. Dropping the serving layer
    /// instead performs the teardown itself and joins the workers.
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
    /// exit when the connection is torn down, which dropping the serving
    /// layer does once they are idle (see [`FuseServing`]). On macOS, where
    /// reception is inherently blocking, the knob is ignored.
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
        // produces, by the unmount or by stop() through fusectl.
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
    #[cfg(target_os = "linux")]
    set.end_connection_on_stop(&session);
    for (id, ch) in channels.into_iter().enumerate() {
        let server = server.clone();
        let tracker = set.tracker();
        match thread::Builder::new()
            .name(format!("fuse-sync-{id}"))
            .spawn(move || {
                let exited = tracker.exit_guard();
                svc_loop(&server, ch, exited.activity());
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
/// has already shut the connection down. It also stops after a request
/// while a stop waits to end the connection.
fn svc_loop<F: FileSystem + Send + Sync + 'static, C: FuseChannelExt>(
    server: &Arc<Server<F>>,
    mut ch: C,
    activity: &WorkerActivity,
) {
    loop {
        match ch.next_request() {
            Ok(Some((reader, writer))) => {
                activity.busy();
                let res = server.handle_message(reader, writer, None, None);
                let stopping = activity.idle();
                if let Err(e) = res {
                    match e {
                        // The kernel has shut down this session.
                        fuse_backend_core::Error::EncodeMessage(ref err)
                            if err.raw_os_error() == Some(libc::EBADF) =>
                        {
                            break;
                        }
                        _ => warn!("sync serving: failed to handle message: {e}"),
                    }
                }
                if stopping {
                    break;
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
    /// The fusectl `abort` file of the connection, see
    /// [`WorkerSet::end_connection_on_stop`].
    abort: Option<File>,
}

impl WorkerSet {
    pub(crate) fn new() -> Self {
        WorkerSet {
            exit: Arc::new(AtomicBool::new(false)),
            tracker: Arc::new(WorkerExitTracker::default()),
            handles: Vec::new(),
            abort: None,
        }
    }

    /// Make [`WorkerSet::stop`] end the connection of `session` if it
    /// outlives the unmount, once every worker is idle. The workers must
    /// report the requests they serve through their [`WorkerActivity`].
    #[cfg(target_os = "linux")]
    pub(crate) fn end_connection_on_stop(&mut self, session: &FuseSession) {
        match crate::linux_session::open_abort_file(session) {
            Ok(abort) => self.abort = Some(abort),
            Err(e) => info!(
                "serving: can't open the fusectl abort file ({e}), so a stop leaves the \
                 connection of a busy mount up"
            ),
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
    ///
    /// Open files keep the connection of a lazily unmounted file system up.
    /// With [`WorkerSet::end_connection_on_stop`], the connection then ends
    /// once every worker is idle.
    pub(crate) fn stop(&mut self, session: &mut FuseSession, wake: bool) {
        self.exit.store(true, Ordering::Release);
        if wake {
            let _ = session.wake();
        }
        let _ = session.umount();
        // See FuseServing for why. If the unmount ended the connection, the
        // write does nothing.
        if let Some(mut abort) = self.abort.take() {
            self.tracker.wait_idle();
            if let Err(e) = abort.write_all(b"1") {
                warn!("serving: can't end the FUSE connection that outlived the unmount: {e}");
            }
        }
        let handles = std::mem::take(&mut self.handles);
        for handle in handles {
            let _ = handle.join();
        }
    }

    /// Block until every worker thread has exited; see
    /// [`FuseServing::wait`].
    pub(crate) fn wait(&self) {
        let mut workers = self.tracker.workers.lock().unwrap();
        while workers.finished < self.handles.len() {
            workers = self.tracker.notified.wait(workers).unwrap();
        }
    }
}

/// Counts worker threads that have exited, so [`WorkerSet::wait`] can
/// block until all of them have drained without tearing the session down,
/// and tracks which workers serve requests.
#[derive(Default)]
pub(crate) struct WorkerExitTracker {
    workers: Mutex<Workers>,
    notified: Condvar,
    /// Set once [`WorkerExitTracker::wait_idle`] waits for busy workers.
    draining: AtomicBool,
}

#[derive(Default)]
struct Workers {
    /// How many worker threads have exited.
    finished: usize,
    /// The busy flag of every worker.
    busy: Vec<Arc<BusyFlag>>,
}

impl WorkerExitTracker {
    /// Arm a guard that counts this worker when its thread exits.
    pub(crate) fn exit_guard(self: &Arc<Self>) -> WorkerExitGuard {
        let busy = Arc::new(BusyFlag::default());
        self.workers.lock().unwrap().busy.push(busy.clone());
        WorkerExitGuard {
            activity: WorkerActivity {
                tracker: self.clone(),
                busy,
            },
        }
    }

    /// Block until no worker serves a request. A worker that takes one
    /// while this returns isn't waited for.
    fn wait_idle(&self) {
        // Pairs with the SeqCst store and load in WorkerActivity::idle():
        // either the worker sees `draining` and notifies, or the check
        // below sees it idle.
        self.draining.store(true, Ordering::SeqCst);
        let mut workers = self.workers.lock().unwrap();
        while workers
            .busy
            .iter()
            .any(|busy| busy.0.load(Ordering::SeqCst))
        {
            workers = self.notified.wait(workers).unwrap();
        }
    }
}

/// Each worker writes its flag twice per request, so keep the flags on
/// separate cache lines.
#[derive(Default)]
#[repr(align(64))]
struct BusyFlag(AtomicBool);

/// Reports whether a worker serves requests, so that [`WorkerSet::stop`]
/// can wait until it has replied to the ones it took.
#[derive(Clone)]
pub(crate) struct WorkerActivity {
    tracker: Arc<WorkerExitTracker>,
    busy: Arc<BusyFlag>,
}

impl WorkerActivity {
    /// The worker took a request.
    pub(crate) fn busy(&self) {
        self.busy.0.store(true, Ordering::Relaxed);
    }

    /// The worker has replied to every request it took. Returns true while a
    /// stop waits to end the connection. The worker should then take no more
    /// requests, or new ones could keep the stop waiting.
    pub(crate) fn idle(&self) -> bool {
        self.busy.0.store(false, Ordering::SeqCst);
        let draining = self.tracker.draining.load(Ordering::SeqCst);
        if draining {
            let _workers = self.tracker.workers.lock().unwrap();
            self.tracker.notified.notify_all();
        }
        draining
    }
}

/// Reports one worker exit when dropped, i.e. when its thread finishes.
pub(crate) struct WorkerExitGuard {
    activity: WorkerActivity,
}

impl WorkerExitGuard {
    /// Where the worker reports the requests it serves.
    pub(crate) fn activity(&self) -> &WorkerActivity {
        &self.activity
    }
}

impl Drop for WorkerExitGuard {
    fn drop(&mut self) {
        let tracker = &self.activity.tracker;
        let mut workers = tracker.workers.lock().unwrap();
        self.activity.busy.0.store(false, Ordering::SeqCst);
        workers.finished += 1;
        tracker.notified.notify_all();
    }
}

#[cfg(test)]
pub(crate) mod tests {
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
    pub(crate) mod linux {
        use super::*;

        use std::io::Read;
        use std::os::fd::AsRawFd;
        use std::os::unix::process::CommandExt;
        use std::sync::mpsc;
        use std::time::Duration;

        use fuse_backend_passthrough::{Config, PassthroughFs};

        /// Serves PassthroughFs with `serve` and drops the serving layer while
        /// a child holds a file on the mount, as a command that a daemon spawns
        /// does until its exec. The child copies a /dev/fuse fd of the
        /// connection above the file, so the exec closes the file first, and
        /// the FLUSH of that close needs an answer. The child waits before its
        /// exec until the drop has returned. A drop or a child that hangs fails
        /// the test, once ending the connection through fusectl has freed it.
        pub(crate) fn stop_with_child_in_exec<S: FuseServing + 'static>(
            serve: impl FnOnce(FuseSession, Arc<Server<PassthroughFs>>) -> S,
        ) {
            let src = TempDir::new().unwrap();
            std::fs::write(src.as_path().join("hello"), b"held").unwrap();
            let mnt = TempDir::new().unwrap();
            let fs = PassthroughFs::<()>::new(Config {
                root_dir: src.as_path().to_string_lossy().to_string(),
                do_import: false,
                ..Default::default()
            })
            .unwrap();
            fs.import().unwrap();
            let mut se = FuseSession::new(mnt.as_path(), "serving_test", "", false).unwrap();
            se.mount().unwrap();
            let serving = serve(se, Arc::new(Server::new(fs)));
            let mountpoint = serving.session().mountpoint().to_owned();
            let fuse_fd = serving.session().get_fuse_file().unwrap().as_raw_fd();

            let mut abort = match crate::linux_session::open_abort_file(serving.session()) {
                Ok(abort) => abort,
                Err(e) => {
                    eprintln!("can't open the fusectl abort file ({e}), skipping");
                    return;
                }
            };
            let held = File::open(mountpoint.join("hello")).unwrap();
            let held_fd = held.as_raw_fd();
            let (forked, forked_w) = nix::unistd::pipe2(nix::fcntl::OFlag::O_CLOEXEC).unwrap();
            let (go_r, go) = nix::unistd::pipe2(nix::fcntl::OFlag::O_CLOEXEC).unwrap();

            let (done_tx, done) = mpsc::channel();
            let spawner = thread::spawn(move || {
                let (forked_w, go_r) = (forked_w.as_raw_fd(), go_r.as_raw_fd());
                let mut cmd = std::process::Command::new("true");
                // SAFETY: the closure only makes async-signal-safe syscalls on fds that the
                // child inherited.
                unsafe {
                    cmd.pre_exec(move || {
                        if libc::fcntl(fuse_fd, libc::F_DUPFD_CLOEXEC, held_fd + 1) < 0 {
                            return Err(std::io::Error::last_os_error());
                        }
                        let mut byte = 0u8;
                        libc::write(forked_w, (&raw const byte).cast(), 1);
                        libc::read(go_r, (&raw mut byte).cast(), 1);
                        Ok(())
                    });
                }
                let _ = done_tx.send(cmd.status());
            });
            File::from(forked)
                .read_exact(&mut [0u8])
                .expect("the child didn't fork");

            let (stopped_tx, stopped) = mpsc::channel();
            let stopper = thread::spawn(move || {
                drop(serving);
                let _ = stopped_tx.send(());
            });
            let ((), stop_hung) = recv_or_abort(&stopped, &mut abort);
            stopper.join().unwrap();

            File::from(go).write_all(b"g").unwrap();
            let (status, child_hung) = recv_or_abort(&done, &mut abort);
            spawner.join().unwrap();
            drop(held);

            assert!(
                !stop_hung,
                "the stop hung while a file on the mount was open"
            );
            assert!(!child_hung, "the child hung in its exec, flushing the file");
            assert!(status.unwrap().success());
        }

        /// Waits for `rx`. If that takes 5s, ends the connection through
        /// `abort` to free whatever hangs, and waits again. Returns the
        /// value and whether it had to end the connection.
        fn recv_or_abort<T>(rx: &mpsc::Receiver<T>, abort: &mut File) -> (T, bool) {
            match rx.recv_timeout(Duration::from_secs(5)) {
                Ok(value) => (value, false),
                Err(_) => {
                    abort.write_all(b"1").unwrap();
                    (rx.recv().unwrap(), true)
                }
            }
        }

        /// Answers a LOOKUP of "slow" in the root with ENOENT, but only 100ms
        /// after `mountpoint` is unmounted, and reports on `started` when it
        /// gets one.
        pub(crate) struct SlowLookupFs {
            mountpoint: std::path::PathBuf,
            started: mpsc::Sender<()>,
        }

        impl FileSystem for SlowLookupFs {
            type Inode = u64;
            type Handle = u64;

            fn lookup(
                &self,
                _ctx: &fuse_backend_core::api::filesystem::Context,
                parent: u64,
                name: &std::ffi::CStr,
            ) -> std::io::Result<fuse_backend_core::api::filesystem::Entry> {
                if parent == 1 && name.to_bytes() == b"slow" {
                    let _ = self.started.send(());
                    for _ in 0..1000 {
                        let mountinfo = std::fs::read_to_string("/proc/self/mountinfo")?;
                        if crate::linux_session::mount_minor(&mountinfo, &self.mountpoint).is_none()
                        {
                            // Give a stop that wouldn't wait for the reply
                            // the time to end the connection first.
                            thread::sleep(Duration::from_millis(100));
                            break;
                        }
                        thread::sleep(Duration::from_millis(10));
                    }
                }
                Err(std::io::Error::from_raw_os_error(libc::ENOENT))
            }

            fn getattr(
                &self,
                _ctx: &fuse_backend_core::api::filesystem::Context,
                _inode: u64,
                _handle: Option<u64>,
            ) -> std::io::Result<(fuse_backend_core::abi::fuse_abi::stat64, Duration)> {
                // SAFETY: stat64 is plain data, for which zeroes are valid.
                let mut attr: fuse_backend_core::abi::fuse_abi::stat64 =
                    unsafe { std::mem::zeroed() };
                attr.st_ino = 1;
                attr.st_mode = libc::S_IFDIR | 0o755;
                attr.st_nlink = 2;
                Ok((attr, Duration::from_secs(60)))
            }
        }

        #[cfg(feature = "async-io")]
        impl fuse_backend_core::api::filesystem::AsyncFileSystem for SlowLookupFs {}

        /// Serves `SlowLookupFs` with `serve`, looks up "slow" and drops the
        /// serving layer while the lookup waits. The unmount leaves the
        /// connection up, because the lookup uses the mount, and the reply
        /// must still get through.
        pub(crate) fn stop_with_request_in_flight<S: FuseServing>(
            serve: impl FnOnce(FuseSession, Arc<Server<SlowLookupFs>>) -> S,
        ) {
            let mnt = TempDir::new().unwrap();
            let (started_tx, started) = mpsc::channel();
            let fs = SlowLookupFs {
                mountpoint: mnt.as_path().canonicalize().unwrap(),
                started: started_tx,
            };
            let mut se = FuseSession::new(mnt.as_path(), "serving_test", "", false).unwrap();
            se.mount().unwrap();
            let serving = serve(se, Arc::new(Server::new(fs)));

            let slow = mnt.as_path().join("slow");
            let lookup = thread::spawn(move || std::fs::metadata(slow).unwrap_err());
            started
                .recv_timeout(Duration::from_secs(5))
                .expect("the lookup didn't start");
            drop(serving);
            let err = lookup.join().unwrap();
            assert_eq!(
                err.raw_os_error(),
                Some(libc::ENOENT),
                "the stop failed the request in flight: {err}"
            );
        }

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

        /// A detached mount that is still in use keeps its connection up.
        /// Neither a second detach() nor dropping the serving layer may
        /// unmount the mountpoint again, because another mount may be
        /// there by then. In this test, that is the tmpfs the file system
        /// was mounted over.
        #[test]
        fn test_sync_serving_detach_busy() {
            use nix::mount::{mount, umount2, MntFlags, MsFlags};

            let mnt = TempDir::new().unwrap();
            if let Err(e) = mount(
                Some("tmpfs"),
                mnt.as_path(),
                Some("tmpfs"),
                MsFlags::empty(),
                None::<&str>,
            ) {
                eprintln!("can't mount a tmpfs ({e}), skipping");
                return;
            }
            let below = mnt.as_path().join("below");
            std::fs::write(&below, b"tmpfs").unwrap();

            let src = TempDir::new().unwrap();
            std::fs::write(src.as_path().join("hello"), b"busy").unwrap();
            let fs = PassthroughFs::<()>::new(Config {
                root_dir: src.as_path().to_string_lossy().to_string(),
                do_import: false,
                ..Default::default()
            })
            .unwrap();
            fs.import().unwrap();
            let mut se = FuseSession::new(mnt.as_path(), "sync_serving_test", "", false).unwrap();
            se.mount().unwrap();
            let server = Arc::new(Server::new(fs));
            let serving = SyncFuseServing::new(se, server, SyncServingConfig::default()).unwrap();

            let busy = std::fs::File::open(mnt.as_path().join("hello")).unwrap();
            serving.session().detach().unwrap();
            assert_eq!(std::fs::read(&below).unwrap(), b"tmpfs");
            serving.session().detach().unwrap();
            assert_eq!(std::fs::read(&below).unwrap(), b"tmpfs");
            drop(serving);
            assert_eq!(std::fs::read(&below).unwrap(), b"tmpfs");

            drop(busy);
            umount2(mnt.as_path(), MntFlags::MNT_DETACH).unwrap();
        }

        fn sync_serving<F: FileSystem + Send + Sync + 'static>(
            blocking: bool,
        ) -> impl FnOnce(FuseSession, Arc<Server<F>>) -> SyncFuseServing<F> {
            move |se, server| {
                let cfg = SyncServingConfig {
                    workers: 2,
                    blocking,
                };
                SyncFuseServing::new(se, server, cfg).unwrap()
            }
        }

        #[test]
        fn test_sync_serving_stop_with_request_in_flight() {
            stop_with_request_in_flight(sync_serving(false));
        }

        #[test]
        fn test_sync_serving_blocking_stop_with_request_in_flight() {
            stop_with_request_in_flight(sync_serving(true));
        }

        #[test]
        fn test_sync_serving_stop_with_child_in_exec() {
            stop_with_child_in_exec(sync_serving(false));
        }

        #[test]
        fn test_sync_serving_blocking_stop_with_child_in_exec() {
            stop_with_child_in_exec(sync_serving(true));
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
