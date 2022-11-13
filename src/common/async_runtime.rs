// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! `Runtime` to wrap over tokio current-thread `Runtime` and tokio-uring `Runtime`.

use std::future::Future;

use lazy_static::lazy_static;

lazy_static! {
    pub(crate) static ref RUNTIME_TYPE: RuntimeType = RuntimeType::new();
}

pub(crate) enum RuntimeType {
    Tokio,
    #[cfg(target_os = "linux")]
    Uring,
}

impl RuntimeType {
    fn new() -> Self {
        #[cfg(target_os = "linux")]
        {
            if Self::probe_io_uring() {
                return Self::Uring;
            }
        }
        Self::Tokio
    }

    #[cfg(target_os = "linux")]
    fn probe_io_uring() -> bool {
        use io_uring::{opcode, IoUring, Probe};

        let io_uring = match IoUring::new(1) {
            Ok(io_uring) => io_uring,
            Err(_) => {
                return false;
            }
        };
        let submitter = io_uring.submitter();

        let mut probe = Probe::new();

        // Check we can register a probe to validate supported operations.
        if let Err(_) = submitter.register_probe(&mut probe) {
            return false;
        }

        // Check IORING_OP_FSYNC is supported
        if !probe.is_supported(opcode::Fsync::CODE) {
            return false;
        }

        // Check IORING_OP_READ is supported
        if !probe.is_supported(opcode::Read::CODE) {
            return false;
        }

        // Check IORING_OP_WRITE is supported
        if !probe.is_supported(opcode::Write::CODE) {
            return false;
        }
        return true;
    }
}

/// An adapter enum to support both tokio current-thread Runtime and tokio-uring Runtime.
pub enum Runtime {
    /// Tokio current thread Runtime.
    Tokio(tokio::runtime::Runtime),
    #[cfg(target_os = "linux")]
    /// Tokio-uring Runtime.
    Uring(std::sync::Mutex<tokio_uring::Runtime>),
}

impl Runtime {
    /// Create a new instance of async Runtime.
    ///
    /// A `tokio-uring::Runtime` is create if io-uring is available, otherwise a tokio current
    /// thread Runtime will be created.
    ///
    /// # Panic
    /// Panic if failed to create the Runtime object.
    pub fn new() -> Self {
        // Check whether io-uring is available.
        #[cfg(target_os = "linux")]
        if matches!(*RUNTIME_TYPE, RuntimeType::Uring) {
            if let Ok(rt) = tokio_uring::Runtime::new(&tokio_uring::builder()) {
                return Runtime::Uring(std::sync::Mutex::new(rt));
            }
        }

        // Create tokio runtime if io-uring is not supported.
        let rt = tokio::runtime::Builder::new_current_thread()
            .enable_all()
            .build()
            .expect("utils: failed to create tokio runtime for current thread");
        Runtime::Tokio(rt)
    }

    /// Run a future to completion.
    pub fn block_on<F: Future>(&self, f: F) -> F::Output {
        match self {
            Runtime::Tokio(rt) => rt.block_on(f),
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
    /// This function must be called from the context of a `tokio-uring` runtime.
    ///
    /// [`JoinHandle`]: tokio::task::JoinHandle
    pub fn spawn<T: std::future::Future + 'static>(
        &self,
        task: T,
    ) -> tokio::task::JoinHandle<T::Output> {
        match self {
            Runtime::Tokio(_) => tokio::task::spawn_local(task),
            #[cfg(target_os = "linux")]
            Runtime::Uring(_) => tokio_uring::spawn(task),
        }
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
/// This will create a new Runtime to run spawn.
///
/// [`JoinHandle`]: tokio::task::JoinHandle
pub fn spawn<T: std::future::Future + 'static>(task: T) -> tokio::task::JoinHandle<T::Output> {
    let rt = Runtime::new();
    rt.spawn(task)
}

#[cfg(test)]
mod tests {
    use super::*;

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
}
