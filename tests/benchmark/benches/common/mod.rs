// SPDX-License-Identifier: Apache-2.0

//! Helpers that the micro-benchmarks share.

use std::future::Future;
use std::io;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context as TaskContext, Poll};

use vmm_sys_util::tempdir::TempDir;

use fuse_backend_rs::api::filesystem::{Context, FileSystem, FsOptions};
use fuse_backend_rs::passthrough::{Config, PassthroughFs};

pub const TEST_FILE: &str = "benchfile";

/// Create a `PassthroughFs` backed by a fresh temporary directory holding
/// `TEST_FILE` with `size` bytes. It's shared between threads, so it can
/// offload to the blocking thread pool.
pub fn prepare_fs(size: usize) -> (Arc<PassthroughFs<()>>, TempDir) {
    let source = TempDir::new().unwrap();
    std::fs::write(source.as_path().join(TEST_FILE), vec![0xa5u8; size]).unwrap();

    let cfg = Config {
        root_dir: source.as_path().to_str().unwrap().to_string(),
        do_import: true,
        ..Default::default()
    };
    let fs = PassthroughFs::<()>::new_shared(cfg).unwrap();
    fs.import().unwrap();
    fs.init(FsOptions::all()).unwrap();
    (fs, source)
}

pub fn prepare_context() -> Context {
    Context {
        uid: unsafe { libc::getuid() },
        gid: unsafe { libc::getgid() },
        pid: unsafe { libc::getpid() },
        ..Default::default()
    }
}

/// Box `io`, a file's asynchronous IO, as the `Send` future of the
/// asynchronous zero-copy traits. The benchmarks poll everything on one
/// thread, like a transport keeps such IO on the serving thread.
pub fn on_this_thread<'a>(
    io: impl Future<Output = io::Result<usize>> + 'a,
) -> Pin<Box<dyn Future<Output = io::Result<usize>> + Send + 'a>> {
    struct OneThread<F>(F);
    // Safe because the benchmarks poll and drop it on the thread that made it.
    unsafe impl<F> Send for OneThread<F> {}
    impl<F: Future> Future for OneThread<F> {
        type Output = F::Output;
        fn poll(self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<F::Output> {
            // Safe because the future is never moved out of `self`.
            unsafe { self.map_unchecked_mut(|s| &mut s.0) }.poll(cx)
        }
    }
    Box::pin(OneThread(io))
}
