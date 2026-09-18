// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

//! Micro-benchmarks comparing the synchronous `FileSystem` interface with
//! the delegated `AsyncFileSystem` interface of `PassthroughFs`.
//!
//! These numbers quantify the framework overhead of the async path
//! (runtime dispatch + delegation) on a per-operation basis, without the
//! kernel fuse transport in the loop. For end-to-end numbers including the
//! fuse transport, use the fio-based comparison in
//! `tests/scripts/bench_sync_async.sh`.
//!
//! Run with: `cargo bench` from this directory (Linux only).

use std::ffi::CString;
use std::io;
use std::sync::Arc;

use criterion::{criterion_group, criterion_main, BatchSize, Criterion};
use vmm_sys_util::tempdir::TempDir;

use fuse_backend_rs::abi::fuse_abi::{CreateIn, ROOT_ID};
use fuse_backend_rs::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, FileSystem, FsOptions,
    ZeroCopyReader, ZeroCopyWriter,
};
use fuse_backend_rs::async_runtime::Runtime;
use fuse_backend_rs::file_buf::FileVolatileSlice;
use fuse_backend_rs::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};
use fuse_backend_rs::passthrough::{Config, PassthroughFs};

const DATA_SIZE: u32 = 4096;
const TEST_FILE: &str = "benchfile";

/// An in-memory sink implementing `ZeroCopyWriter`/`AsyncZeroCopyWriter`,
/// to receive data from `read()`/`async_read()`.
struct MemWriter(Vec<u8>);

impl MemWriter {
    fn new() -> Self {
        MemWriter(Vec::new())
    }
}

impl io::Write for MemWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl ZeroCopyWriter for MemWriter {
    fn write_from(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        if self.0.len() < count {
            self.0.resize(count, 0);
        }
        // Safe because the slice points into `self.0` and doesn't out-live it.
        // The file offset only selects the read position within `f`; received
        // data is always placed at the start of the buffer.
        let slice = unsafe { FileVolatileSlice::from_raw_ptr(self.0.as_mut_ptr(), count) };
        f.read_at_volatile(slice, off)
    }

    fn available_bytes(&self) -> usize {
        usize::MAX
    }
}

#[async_trait::async_trait(?Send)]
impl AsyncZeroCopyWriter for MemWriter {
    async fn async_write_from(
        &mut self,
        _f: Arc<dyn AsyncFileReadWriteVolatile>,
        _count: usize,
        _off: u64,
    ) -> io::Result<usize> {
        unreachable!("the synchronous delegation never uses the async zero-copy path")
    }
}

/// An in-memory source implementing `ZeroCopyReader`/`AsyncZeroCopyReader`,
/// to provide data to `write()`/`async_write()`.
struct MemReader(Vec<u8>);

impl io::Read for MemReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = std::cmp::min(buf.len(), self.0.len());
        buf[..n].copy_from_slice(&self.0[..n]);
        self.0.drain(..n);
        Ok(n)
    }
}

impl ZeroCopyReader for MemReader {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let start = off as usize;
        if start >= self.0.len() {
            return Ok(0);
        }
        let n = std::cmp::min(count, self.0.len() - start);
        // Safe because the buffer is only read from and the slice doesn't
        // out-live `self.0`.
        let slice =
            unsafe { FileVolatileSlice::from_raw_ptr(self.0.as_ptr().add(start) as *mut u8, n) };
        f.write_at_volatile(slice, off)
    }
}

#[async_trait::async_trait(?Send)]
impl AsyncZeroCopyReader for MemReader {
    async fn async_read_to(
        &mut self,
        _f: Arc<dyn AsyncFileReadWriteVolatile>,
        _count: usize,
        _off: u64,
    ) -> io::Result<usize> {
        unreachable!("the synchronous delegation never uses the async zero-copy path")
    }
}

/// Create a `PassthroughFs` backed by a fresh temporary directory holding a
/// single `DATA_SIZE`-byte file.
fn prepare_fs() -> (PassthroughFs<()>, TempDir) {
    let source = TempDir::new().unwrap();
    std::fs::write(
        source.as_path().join(TEST_FILE),
        vec![0xa5u8; DATA_SIZE as usize],
    )
    .unwrap();

    let cfg = Config {
        root_dir: source.as_path().to_str().unwrap().to_string(),
        do_import: true,
        ..Default::default()
    };
    let fs = PassthroughFs::<()>::new(cfg).unwrap();
    fs.import().unwrap();
    fs.init(FsOptions::all()).unwrap();
    (fs, source)
}

fn prepare_context() -> Context {
    Context {
        uid: unsafe { libc::getuid() },
        gid: unsafe { libc::getgid() },
        pid: unsafe { libc::getpid() },
        ..Default::default()
    }
}

fn bench_lookup_getattr(c: &mut Criterion) {
    let (fs, _source) = prepare_fs();
    let ctx = prepare_context();
    let name = CString::new(TEST_FILE).unwrap();
    let rt = Runtime::new();

    c.bench_function("lookup+forget/sync", |b| {
        b.iter(|| {
            let entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
            fs.forget(&ctx, entry.inode, 1);
        })
    });
    c.bench_function("lookup+forget/async", |b| {
        b.iter(|| {
            rt.block_on(async {
                let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
                fs.forget(&ctx, entry.inode, 1);
            });
        })
    });

    // Lookup once and benchmark getattr on the resulting inode.
    let entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
    let inode = entry.inode;
    c.bench_function("getattr/sync", |b| {
        b.iter(|| fs.getattr(&ctx, inode, None).unwrap())
    });
    c.bench_function("getattr/async", |b| {
        b.iter(|| rt.block_on(fs.async_getattr(&ctx, inode, None)).unwrap())
    });
    fs.forget(&ctx, inode, 1);
}

fn bench_read(c: &mut Criterion) {
    let (fs, _source) = prepare_fs();
    let ctx = prepare_context();
    let name = CString::new(TEST_FILE).unwrap();
    let rt = Runtime::new();

    let entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
    let inode = entry.inode;
    let mut w = MemWriter::new();

    c.bench_function("open+read4k+release/sync", |b| {
        b.iter(|| {
            let (handle, _opts, _) = fs.open(&ctx, inode, libc::O_RDONLY as u32, 0).unwrap();
            let handle = handle.unwrap();
            fs.read(
                &ctx,
                inode,
                handle,
                &mut w,
                DATA_SIZE,
                0,
                None,
                libc::O_RDONLY as u32,
            )
            .unwrap();
            fs.release(
                &ctx,
                inode,
                libc::O_RDONLY as u32,
                handle,
                false,
                false,
                None,
            )
            .unwrap();
        })
    });
    c.bench_function("open+read4k+release/async", |b| {
        b.iter(|| {
            rt.block_on(async {
                let (handle, _opts) = fs
                    .async_open(&ctx, inode, libc::O_RDONLY as u32, 0)
                    .await
                    .unwrap();
                let handle = handle.unwrap();
                fs.async_read(
                    &ctx,
                    inode,
                    handle,
                    &mut w,
                    DATA_SIZE,
                    0,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
                fs.release(
                    &ctx,
                    inode,
                    libc::O_RDONLY as u32,
                    handle,
                    false,
                    false,
                    None,
                )
                .unwrap();
            });
        })
    });
    fs.forget(&ctx, inode, 1);
}

fn bench_write(c: &mut Criterion) {
    let (fs, _source) = prepare_fs();
    let ctx = prepare_context();
    let name = CString::new(TEST_FILE).unwrap();
    let rt = Runtime::new();

    let entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
    let inode = entry.inode;

    c.bench_function("open+write4k+release/sync", |b| {
        b.iter_batched(
            || MemReader(vec![0x5au8; DATA_SIZE as usize]),
            |mut r| {
                let (handle, _opts, _) = fs.open(&ctx, inode, libc::O_RDWR as u32, 0).unwrap();
                let handle = handle.unwrap();
                fs.write(
                    &ctx,
                    inode,
                    handle,
                    &mut r,
                    DATA_SIZE,
                    0,
                    None,
                    false,
                    libc::O_RDWR as u32,
                    0,
                )
                .unwrap();
                fs.release(&ctx, inode, libc::O_RDWR as u32, handle, false, false, None)
                    .unwrap();
            },
            BatchSize::SmallInput,
        )
    });
    c.bench_function("open+write4k+release/async", |b| {
        b.iter_batched(
            || MemReader(vec![0x5au8; DATA_SIZE as usize]),
            |mut r| {
                rt.block_on(async {
                    let (handle, _opts) = fs
                        .async_open(&ctx, inode, libc::O_RDWR as u32, 0)
                        .await
                        .unwrap();
                    let handle = handle.unwrap();
                    fs.async_write(
                        &ctx,
                        inode,
                        handle,
                        &mut r,
                        DATA_SIZE,
                        0,
                        None,
                        false,
                        libc::O_RDWR as u32,
                        0,
                    )
                    .await
                    .unwrap();
                    fs.release(&ctx, inode, libc::O_RDWR as u32, handle, false, false, None)
                        .unwrap();
                });
            },
            BatchSize::SmallInput,
        )
    });
    fs.forget(&ctx, inode, 1);
}

fn bench_create_unlink(c: &mut Criterion) {
    let (fs, _source) = prepare_fs();
    let ctx = prepare_context();
    let name = CString::new("benchtmp").unwrap();
    let args = CreateIn {
        flags: (libc::O_RDWR | libc::O_CREAT | libc::O_TRUNC) as u32,
        mode: 0o644,
        umask: 0,
        fuse_flags: 0,
    };
    let rt = Runtime::new();

    c.bench_function("create+release+unlink/sync", |b| {
        b.iter(|| {
            let (entry, handle, _opts, _) = fs.create(&ctx, ROOT_ID, &name, args).unwrap();
            if let Some(handle) = handle {
                fs.release(&ctx, entry.inode, args.flags, handle, false, false, None)
                    .unwrap();
            }
            fs.forget(&ctx, entry.inode, 1);
            fs.unlink(&ctx, ROOT_ID, &name).unwrap();
        })
    });
    c.bench_function("create+release+unlink/async", |b| {
        b.iter(|| {
            rt.block_on(async {
                let (entry, handle, _opts) =
                    fs.async_create(&ctx, ROOT_ID, &name, args).await.unwrap();
                if let Some(handle) = handle {
                    fs.release(&ctx, entry.inode, args.flags, handle, false, false, None)
                        .unwrap();
                }
                fs.forget(&ctx, entry.inode, 1);
                fs.unlink(&ctx, ROOT_ID, &name).unwrap();
            });
        })
    });
}

criterion_group!(
    benches,
    bench_lookup_getattr,
    bench_read,
    bench_write,
    bench_create_unlink,
);
criterion_main!(benches);
