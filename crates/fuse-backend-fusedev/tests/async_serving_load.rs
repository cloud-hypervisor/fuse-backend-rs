// SPDX-License-Identifier: Apache-2.0

//! A worker that keeps finding requests must still let its runtime run, or the handlers that
//! wait for a timer or, on tokio-uring, for io_uring IO never finish. The stall happens on tokio,
//! so the test runs there unless `FUSE_BACKEND_RS_ASYNC_RUNTIME` selects a runtime.
//! `tests/async_serving.rs` checks workers that block while idle. Mounting needs root or
//! fusermount3, and the test skips without either.

#![cfg(all(target_os = "linux", feature = "async-io"))]

mod common;

mod async_serving_load {
    use fuse_backend_core::async_runtime::{self, RuntimeType, RUNTIME_TYPE_ENV};
    use fuse_backend_fusedev::AsyncServingConfig;

    #[test]
    fn test_async_serving_busy_worker_lets_runtime_run() {
        // io_uring reads always wait for the runtime to park, so the default on a host with
        // io_uring wouldn't exercise the tokio path.
        if std::env::var_os(RUNTIME_TYPE_ENV).is_none() {
            async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();
        }
        super::common::check_busy_worker_lets_runtime_run(AsyncServingConfig {
            workers: 1,
            ..Default::default()
        });
    }
}
