// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! `Runtime` to wrap over tokio current-thread `Runtime` and tokio-uring `Runtime`.
//!
//! By default the runtime type is auto-detected: `tokio-uring` is used if io-uring is
//! available, otherwise the tokio current-thread runtime is used. Other platforms always use
//! tokio. The `FUSE_BACKEND_RS_ASYNC_RUNTIME` environment variable overrides the
//! detection. It accepts `tokio`, and on Linux also `uring`. Calling [`set_runtime_type()`]
//! before any other function of this module or `async_file` overrides both. This is useful when
//! the application's own tokio runtime drives futures from this crate, such as
//! `FuseDevTask::poll_handler()`, because a plain tokio runtime can't poll `tokio-uring` objects.
//!
//! Code outside this module and `async_file` doesn't match on [`RuntimeType`]. It dispatches on
//! what the runtime means for the operation instead: [`RuntimeType::file_io_blocks()`] tells
//! whether file IO blocks the calling thread, and `async_file::File::uses_io_uring()` tells
//! whether file IO goes through io_uring. A new behavioral difference between the runtimes
//! should become such a capability query, not a new `match` site in a filesystem crate.
//!
//! Note: creating io-uring rings locks kernel memory accounted against `RLIMIT_MEMLOCK`
//! (see `account_memlock()` in the kernel). If the limit is too low (e.g. the default
//! 64KB), ring creation may fail with `ENOMEM`, in which case [`Runtime::new()`] panics
//! with a hint. Raise the limit with e.g. `ulimit -l unlimited` or force the tokio
//! runtime with `FUSE_BACKEND_RS_ASYNC_RUNTIME=tokio` instead.

use std::future::Future;
use std::io;
use std::sync::{LazyLock, OnceLock};

/// Environment variable that selects the runtime type, `tokio` or, on Linux, `uring`.
pub const RUNTIME_TYPE_ENV: &str = "FUSE_BACKEND_RS_ASYNC_RUNTIME";

/// Number of submission queue entries of the io-uring rings created by this crate.
///
/// Must match the value handed to `tokio_uring::builder()` in [`Runtime::new()`],
/// so that `RuntimeType::probe_io_uring()` faithfully reflects the memory required
/// to create a real runtime.
#[cfg(target_os = "linux")]
const RING_ENTRIES: u32 = 256;

pub(crate) static RUNTIME_TYPE: LazyLock<RuntimeType> = LazyLock::new(RuntimeType::new);

/// The runtime type requested with `set_runtime_type()`, which takes precedence over the
/// environment variable.
static REQUESTED_RUNTIME_TYPE: OnceLock<RuntimeType> = OnceLock::new();

/// The error of the failed io-uring probe, which `set_runtime_type()` reports.
#[cfg(target_os = "linux")]
static PROBE_ERROR: OnceLock<io::Error> = OnceLock::new();

/// Type of the asynchronous runtime used by this crate.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RuntimeType {
    /// The tokio current-thread runtime, with plain syscalls for file IO.
    Tokio,
    /// The tokio-uring runtime, with io-uring for file IO.
    #[cfg(target_os = "linux")]
    Uring,
}

/// Select the runtime type instead of detecting it.
///
/// The crate fixes the type on first use, so call this before creating a [`Runtime`], an
/// `async_file::File` or a `FuseDevTask`. It overrides `FUSE_BACKEND_RS_ASYNC_RUNTIME`. It
/// returns an error if the type in effect is a different one. If io-uring isn't available, the
/// error says why.
pub fn set_runtime_type(runtime_type: RuntimeType) -> io::Result<()> {
    let _ = REQUESTED_RUNTIME_TYPE.set(runtime_type);
    let current = *RUNTIME_TYPE;
    if current == runtime_type {
        return Ok(());
    }
    #[cfg(target_os = "linux")]
    if let (RuntimeType::Uring, Some(e)) = (runtime_type, PROBE_ERROR.get()) {
        return Err(io::Error::new(
            e.kind(),
            format!("io-uring isn't available: {e}"),
        ));
    }
    Err(io::Error::other(format!(
        "async runtime type is {current:?}, not {runtime_type:?}"
    )))
}

/// Get the runtime type used by this crate, detecting it if it isn't fixed yet.
pub fn runtime_type() -> RuntimeType {
    *RUNTIME_TYPE
}

impl RuntimeType {
    /// Whether async file IO on this runtime type blocks the calling thread. It does on tokio,
    /// which makes plain syscalls, and doesn't on io-uring.
    pub fn file_io_blocks(self) -> bool {
        matches!(self, RuntimeType::Tokio)
    }

    fn new() -> Self {
        let requested = REQUESTED_RUNTIME_TYPE
            .get()
            .copied()
            .or_else(Self::from_env);
        match requested {
            Some(RuntimeType::Tokio) => Self::Tokio,
            #[cfg(target_os = "linux")]
            _ => match Self::probe_io_uring() {
                Ok(()) => Self::Uring,
                Err(e) => {
                    warn!("io-uring isn't available, falling back to tokio: {}", e);
                    let _ = PROBE_ERROR.set(e);
                    Self::Tokio
                }
            },
            #[cfg(not(target_os = "linux"))]
            None => Self::Tokio,
        }
    }

    /// The runtime type requested with `FUSE_BACKEND_RS_ASYNC_RUNTIME`, if any.
    fn from_env() -> Option<Self> {
        let val = std::env::var(RUNTIME_TYPE_ENV).ok()?;
        let requested = Self::parse_env(&val);
        if requested.is_none() {
            warn!(
                "unknown value '{}' for environment variable {}, ignored",
                val, RUNTIME_TYPE_ENV
            );
        }
        requested
    }

    fn parse_env(val: &str) -> Option<Self> {
        match val.trim().to_ascii_lowercase().as_str() {
            "tokio" => Some(Self::Tokio),
            #[cfg(target_os = "linux")]
            "uring" | "io-uring" => Some(Self::Uring),
            _ => None,
        }
    }

    /// Check that io-uring works here and supports the operations this crate uses.
    #[cfg(target_os = "linux")]
    fn probe_io_uring() -> io::Result<()> {
        use io_uring::{opcode, IoUring, Probe};

        // Create the ring with the same number of entries as the real runtimes,
        // because ring memory is accounted against `RLIMIT_MEMLOCK` and probing
        // with a smaller ring may succeed where `Runtime::new()` would fail.
        let io_uring = IoUring::new(RING_ENTRIES).map_err(|e| {
            io::Error::new(
                e.kind(),
                format!(
                    "can't create a ring with {RING_ENTRIES} entries ({e}). \
                     Check RLIMIT_MEMLOCK if the error is ENOMEM"
                ),
            )
        })?;

        let mut probe = Probe::new();
        io_uring
            .submitter()
            .register_probe(&mut probe)
            .map_err(|e| io::Error::new(e.kind(), format!("can't register a probe ({e})")))?;

        for (code, name) in [
            (opcode::Fsync::CODE, "FSYNC"),
            (opcode::Read::CODE, "READ"),
            (opcode::Write::CODE, "WRITE"),
        ] {
            if !probe.is_supported(code) {
                return Err(io::Error::new(
                    io::ErrorKind::Unsupported,
                    format!("the {name} operation isn't supported"),
                ));
            }
        }
        Ok(())
    }
}

/// An adapter enum to support both tokio current-thread Runtime and tokio-uring Runtime.
pub enum Runtime {
    /// Tokio current thread Runtime, with a `LocalSet` to support spawning
    /// `!Send` tasks via `spawn_local()`.
    Tokio(tokio::task::LocalSet, tokio::runtime::Runtime),
    #[cfg(target_os = "linux")]
    /// Tokio-uring Runtime.
    Uring(std::sync::Mutex<tokio_uring::Runtime>),
}

impl Runtime {
    /// Create a new instance of async Runtime.
    ///
    /// A `tokio-uring::Runtime` is create if io-uring is available, otherwise a tokio current
    /// thread Runtime will be created. The runtime type may also be forced with the
    /// `FUSE_BACKEND_RS_ASYNC_RUNTIME` environment variable, see the module documentation.
    ///
    /// # Panic
    /// Panic if failed to create the Runtime object.
    pub fn new() -> Self {
        // Check whether io-uring is available.
        #[cfg(target_os = "linux")]
        if matches!(*RUNTIME_TYPE, RuntimeType::Uring) {
            // It's fine to use a ring with RING_ENTRIES entries here, because
            // `RUNTIME_TYPE` has been set to `Uring` only after a ring of the
            // same size was created successfully by `probe_io_uring()`.
            match tokio_uring::Runtime::new(tokio_uring::builder().entries(RING_ENTRIES)) {
                Ok(rt) => return Runtime::Uring(std::sync::Mutex::new(rt)),
                Err(e) => {
                    // Don't fall back to the tokio runtime here: `RUNTIME_TYPE` is
                    // already published as `Uring`, so files are opened as io-uring
                    // files and would panic or deadlock when polled by a plain tokio
                    // runtime. Fail loudly instead.
                    panic!(
                        "failed to create a tokio-uring runtime: {}. io-uring was detected \
                         at startup but ring creation failed now; check `RLIMIT_MEMLOCK` \
                         (e.g. `ulimit -l`) if the error is ENOMEM, or force the tokio \
                         runtime with {}=tokio",
                        e, RUNTIME_TYPE_ENV
                    );
                }
            }
        }

        // Create tokio runtime if io-uring is not supported.
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("utils: failed to create tokio runtime for current thread");
        Runtime::Tokio(tokio::task::LocalSet::new(), rt)
    }

    /// Run a future to completion.
    pub fn block_on<F: Future>(&self, f: F) -> F::Output {
        match self {
            Runtime::Tokio(local, rt) => rt.block_on(local.run_until(f)),
            #[cfg(target_os = "linux")]
            Runtime::Uring(rt) => rt.lock().unwrap().block_on(f),
        }
    }

    /// Spawns a new asynchronous task, returning a [`JoinHandle`] for it.
    ///
    /// Spawning a task enables the task to execute concurrently to other tasks.
    /// There is no guarantee that a spawned task will execute to completion. When a
    /// runtime is shutdown, all outstanding tasks are dropped, regardless of the
    /// lifecycle of that task.
    ///
    /// This function must be called from the context of a `Runtime` object,
    /// i.e. within the future passed to `Runtime::block_on()`.
    ///
    /// [`JoinHandle`]: tokio::task::JoinHandle
    pub fn spawn<T: std::future::Future + 'static>(task: T) -> tokio::task::JoinHandle<T::Output> {
        match *RUNTIME_TYPE {
            RuntimeType::Tokio => tokio::task::spawn_local(task),
            #[cfg(target_os = "linux")]
            RuntimeType::Uring => tokio_uring::spawn(task),
        }
    }

    /// Spawn a blocking task on the blocking thread pool, returning a [`JoinHandle`] for it.
    ///
    /// The async runtime used by this crate is single-threaded, so blocking operations
    /// executed inline stall the processing of all other requests. Offload such work to
    /// the tokio blocking thread pool with this method instead, so the async task can
    /// keep serving requests while the blocking work runs on pool threads.
    ///
    /// Both runtime variants are backed by tokio runtimes, so the blocking pool is
    /// available with both of them.
    ///
    /// This function must be called from the context of a `Runtime` object,
    /// i.e. within the future passed to `Runtime::block_on()`.
    ///
    /// [`JoinHandle`]: tokio::task::JoinHandle
    pub fn spawn_blocking<F, R>(f: F) -> tokio::task::JoinHandle<R>
    where
        F: FnOnce() -> R + Send + 'static,
        R: Send + 'static,
    {
        tokio::task::spawn_blocking(f)
    }
}

/// Start an async runtime.
pub fn start<F: Future>(future: F) -> F::Output {
    Runtime::new().block_on(future)
}

impl Default for Runtime {
    fn default() -> Self {
        Runtime::new()
    }
}

/// Run a callback with the default `Runtime` object.
pub fn with_runtime<F, R>(f: F) -> R
where
    F: FnOnce(&Runtime) -> R,
{
    let rt = Runtime::new();
    f(&rt)
}

/// Run a future to completion with the default `Runtime` object.
pub fn block_on<F: Future>(f: F) -> F::Output {
    Runtime::new().block_on(f)
}

/// Spawns a new asynchronous task with the defualt `Runtime`, returning a [`JoinHandle`] for it.
///
/// Spawning a task enables the task to execute concurrently to other tasks.
/// There is no guarantee that a spawned task will execute to completion. When a
/// runtime is shutdown, all outstanding tasks are dropped, regardless of the
/// lifecycle of that task.
///
/// This function must be called from the context of a `Runtime` object,
/// i.e. within the future passed to `Runtime::block_on()`.
///
/// [`JoinHandle`]: tokio::task::JoinHandle
pub fn spawn<T: std::future::Future + 'static>(task: T) -> tokio::task::JoinHandle<T::Output> {
    Runtime::spawn(task)
}

/// Spawn a blocking task on the blocking thread pool of the default `Runtime`,
/// returning a [`JoinHandle`] for it.
///
/// See `Runtime::spawn_blocking()` for details. This function must be called
/// from the context of a `Runtime` object, i.e. within the future passed to
/// `Runtime::block_on()`.
///
/// [`JoinHandle`]: tokio::task::JoinHandle
pub fn spawn_blocking<F, R>(f: F) -> tokio::task::JoinHandle<R>
where
    F: FnOnce() -> R + Send + 'static,
    R: Send + 'static,
{
    Runtime::spawn_blocking(f)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_env() {
        assert!(matches!(
            RuntimeType::parse_env("tokio"),
            Some(RuntimeType::Tokio)
        ));
        assert!(matches!(
            RuntimeType::parse_env(" Tokio "),
            Some(RuntimeType::Tokio)
        ));
        assert!(RuntimeType::parse_env("").is_none());
        assert!(RuntimeType::parse_env("foobar").is_none());

        #[cfg(target_os = "linux")]
        {
            assert!(matches!(
                RuntimeType::parse_env("uring"),
                Some(RuntimeType::Uring)
            ));
            assert!(matches!(
                RuntimeType::parse_env("IO-URING"),
                Some(RuntimeType::Uring)
            ));
        }
    }

    #[test]
    fn test_with_runtime() {
        let res = with_runtime(|rt| rt.block_on(async { 1 }));
        assert_eq!(res, 1);

        let res = with_runtime(|rt| rt.block_on(async { 3 }));
        assert_eq!(res, 3);
    }

    #[test]
    fn test_block_on() {
        let res = block_on(async { 1 });
        assert_eq!(res, 1);

        let res = block_on(async { 3 });
        assert_eq!(res, 3);
    }

    #[test]
    fn test_spawn_blocking() {
        let main_tid = std::thread::current().id();

        // The closure must run to completion on a thread of the blocking pool,
        // not on the thread driving the runtime.
        let (tid, res) = block_on(async {
            let handle = Runtime::spawn_blocking(|| {
                // Simulate a blocking syscall, which must not stall the
                // async runtime thread.
                std::thread::sleep(std::time::Duration::from_millis(10));
                (std::thread::current().id(), 42)
            });
            handle.await.unwrap()
        });
        assert_ne!(tid, main_tid);
        assert_eq!(res, 42);

        // Concurrent blocking tasks must run in parallel on pool threads.
        let tids = block_on(async {
            let mut handles = Vec::new();
            for _ in 0..8 {
                handles.push(spawn_blocking(|| {
                    std::thread::sleep(std::time::Duration::from_millis(50));
                    std::thread::current().id()
                }));
            }
            let mut tids = Vec::new();
            for h in handles {
                tids.push(h.await.unwrap());
            }
            tids
        });
        tids.iter().for_each(|t| assert_ne!(*t, main_tid));
        let distinct: std::collections::HashSet<std::thread::ThreadId> = tids.into_iter().collect();
        assert!(distinct.len() >= 2);
    }
}
