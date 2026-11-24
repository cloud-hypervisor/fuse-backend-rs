// SPDX-License-Identifier: Apache-2.0

//! A file system whose handler waits for the runtime, and a check that a busy worker still lets
//! it run, for the tests that serve with `AsyncFuseServing`.

use std::ffi::CStr;
use std::io;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::channel;
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use async_trait::async_trait;
use fuse_backend_core::abi::fuse_abi::stat64;
use fuse_backend_core::api::filesystem::{AsyncFileSystem, Context, Entry, FileSystem};
use fuse_backend_core::api::server::Server;
use fuse_backend_core::async_file::File as AsyncFile;
use fuse_backend_core::async_runtime;
use fuse_backend_fusedev::{AsyncFuseServing, AsyncServingConfig, FuseSession};
use vmm_sys_util::tempdir::TempDir;

/// The root's attributes don't stay cached, so each stat is a request. Every lookup fails.
/// A lookup of `slow` first waits for a 1 ms tokio timer and opens `/dev/null`, which
/// tokio-uring does with io_uring.
struct SlowLookupFs;

impl FileSystem for SlowLookupFs {
    type Inode = u64;
    type Handle = u64;

    fn getattr(
        &self,
        _ctx: &Context,
        inode: u64,
        _handle: Option<u64>,
    ) -> io::Result<(stat64, Duration)> {
        let mut attr: stat64 = unsafe { std::mem::zeroed() };
        attr.st_ino = inode;
        attr.st_mode = libc::S_IFDIR | 0o755;
        attr.st_nlink = 2;
        Ok((attr, Duration::ZERO))
    }
}

#[async_trait]
impl AsyncFileSystem for SlowLookupFs {
    async fn async_lookup(&self, _ctx: &Context, _parent: u64, name: &CStr) -> io::Result<Entry> {
        if name.to_bytes() == b"slow" {
            tokio::time::sleep(Duration::from_millis(1)).await;
            // A tokio-uring file isn't Send, and the future of a handler must be, so the
            // open runs in a task.
            async_runtime::spawn(async {
                AsyncFile::async_open("/dev/null", false, false)
                    .await
                    .map(drop)
            })
            .await
            .unwrap()?;
        }
        Err(io::Error::from_raw_os_error(libc::ENOENT))
    }
}

/// Keep one worker of `cfg` busy and check that 20 lookups whose handler waits for the runtime
/// still finish. Skips if the mount fails.
pub fn check_busy_worker_lets_runtime_run(cfg: AsyncServingConfig) {
    let mnt = TempDir::new().unwrap();
    let mut se = FuseSession::new(mnt.as_path(), "async_serving_load", "", false).unwrap();
    se.set_allow_other(false);
    if let Err(e) = se.mount() {
        eprintln!("can't mount ({}), skipping", e);
        return;
    }
    let serving = AsyncFuseServing::new(se, Arc::new(Server::new(SlowLookupFs)), cfg).unwrap();

    // Stats of the root keep the worker finding requests. The kernel runs lookups in one
    // directory one at a time, but not GETATTR.
    let stop = Arc::new(AtomicBool::new(false));
    let load: Vec<_> = (0..16)
        .map(|_| {
            let dir = mnt.as_path().to_path_buf();
            let stop = stop.clone();
            thread::spawn(move || {
                while !stop.load(Ordering::Relaxed) {
                    std::fs::metadata(&dir).unwrap();
                }
            })
        })
        .collect();
    thread::sleep(Duration::from_millis(100));

    let (tx, rx) = channel();
    let slow = mnt.as_path().join("slow");
    let probe = thread::spawn(move || {
        let start = Instant::now();
        for _ in 0..20 {
            assert!(std::fs::metadata(&slow).is_err());
        }
        let _ = tx.send(start.elapsed());
    });
    let took = rx.recv_timeout(Duration::from_secs(10));
    stop.store(true, Ordering::Relaxed);
    for t in load {
        t.join().unwrap();
    }
    probe.join().unwrap();
    drop(serving);

    let took = took.expect("20 lookups that wait for the runtime took over 10s under load");
    assert!(
        took < Duration::from_secs(2),
        "20 lookups that wait for the runtime took {:?} under load",
        took
    );
}
