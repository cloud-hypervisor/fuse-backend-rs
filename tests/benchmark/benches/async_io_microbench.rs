// SPDX-License-Identifier: Apache-2.0

//! Micro-benchmarks of the asynchronous data path, without the kernel fuse
//! transport in the loop.
//!
//! - `vectored/*` moves data between a file and N page-sized buffers, as a
//!   virtio-fs descriptor chain hands them over. `write` goes through
//!   `Reader::async_read_to_at()` and `read` through
//!   `AsyncFileReadWriteVolatile::async_read_vectored_at_volatile()`.
//! - `passthrough/*` serves READ and WRITE with `PassthroughFs`, with the
//!   blocking thread pool off (`inline`) and on (`pool`). The READ writer
//!   fails the inline page cache attempt, so READ measures the path that
//!   serves cache misses, here with the data in the page cache.
//!
//! The data lives in a temporary directory, so set `TMPDIR` to pick the file
//! system. The runtime type comes from `FUSE_BACKEND_RS_ASYNC_RUNTIME`:
//!
//! ```sh
//! FUSE_BACKEND_RS_ASYNC_RUNTIME=tokio cargo bench --bench async_io_microbench
//! ```

mod common;

use std::ffi::CString;
use std::io;
use std::sync::Arc;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use vm_memory::VolatileSlice;
use vmm_sys_util::tempdir::TempDir;

use fuse_backend_rs::abi::fuse_abi::ROOT_ID;
use fuse_backend_rs::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, FileSystem, ZeroCopyReader,
    ZeroCopyWriter,
};
use fuse_backend_rs::async_file::File;
use fuse_backend_rs::async_runtime::{self, Runtime};
use fuse_backend_rs::buffer::Reader;
use fuse_backend_rs::file_buf::{FileVolatileBuf, FileVolatileSlice};
use fuse_backend_rs::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};

use common::{prepare_context, prepare_fs, TEST_FILE};

/// Size of each buffer of a vectored operation, a page like virtio-fs uses.
const SEGMENT: usize = 4096;
/// Buffer counts of the vectored operations.
const SEGMENTS: [usize; 3] = [1, 16, 256];
/// Request sizes of the passthrough operations.
const REQUEST_SIZES: [usize; 3] = [4096, 128 << 10, 1 << 20];

fn bench_vectored(c: &mut Criterion) {
    let rt = Runtime::new();
    let dir = TempDir::new().unwrap();
    let path = dir.as_path().join(TEST_FILE);
    let max = SEGMENTS[SEGMENTS.len() - 1] * SEGMENT;
    std::fs::write(&path, vec![0xa5u8; max]).unwrap();
    let file = rt.block_on(File::async_open(&path, true, false)).unwrap();
    let mut mem = vec![0x5au8; max];

    let mut group = c.benchmark_group(format!("vectored/{:?}", async_runtime::runtime_type()));
    for &n in SEGMENTS.iter() {
        let len = n * SEGMENT;
        group.throughput(Throughput::Bytes(len as u64));
        group.bench_with_input(BenchmarkId::new("write", n), &n, |b, &n| {
            b.iter(|| {
                // Safe because the slices point into `mem`, which outlives the reader.
                let slices = mem
                    .chunks_mut(SEGMENT)
                    .take(n)
                    .map(|s| unsafe { VolatileSlice::new(s.as_mut_ptr(), s.len()) })
                    .collect();
                let mut r = Reader::<()>::from_volatile_slices(slices);
                let cnt = rt.block_on(r.async_read_to_at(&file, len, 0)).unwrap();
                assert_eq!(cnt, len);
            })
        });
        group.bench_with_input(BenchmarkId::new("read", n), &n, |b, &n| {
            b.iter(|| {
                // Safe because the buffers point into `mem`, which outlives them.
                let bufs = mem
                    .chunks_mut(SEGMENT)
                    .take(n)
                    .map(|s| unsafe { FileVolatileBuf::from_raw_ptr(s.as_mut_ptr(), 0, s.len()) })
                    .collect();
                let (res, _) = rt.block_on(file.async_read_vectored_at_volatile(bufs, 0));
                assert_eq!(res.unwrap(), len);
            })
        });
    }
    group.finish();
}

/// A reply buffer whose inline `write_from()` misses, like a READ whose
/// data isn't in the page cache, so the file system serves it another way.
struct MissWriter {
    buf: Vec<u8>,
    len: usize,
}

impl io::Write for MissWriter {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        let n = std::cmp::min(data.len(), self.buf.len() - self.len);
        self.buf[self.len..self.len + n].copy_from_slice(&data[..n]);
        self.len += n;
        Ok(n)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl ZeroCopyWriter for MissWriter {
    fn write_from(
        &mut self,
        _f: &mut dyn FileReadWriteVolatile,
        _count: usize,
        _off: u64,
    ) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EAGAIN))
    }

    fn available_bytes(&self) -> usize {
        self.buf.len() - self.len
    }
}

#[async_trait::async_trait(?Send)]
impl AsyncZeroCopyWriter for MissWriter {
    async fn async_write_from(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let count = std::cmp::min(count, self.buf.len() - self.len);
        // Safe because the buffer points into `self.buf`, which outlives it.
        let buf =
            unsafe { FileVolatileBuf::from_raw_ptr(self.buf.as_mut_ptr().add(self.len), 0, count) };
        let (res, _) = f.async_read_at_volatile(buf, off).await;
        let n = res?;
        self.len += n;
        Ok(n)
    }
}

/// A request buffer holding the payload of a WRITE.
struct PayloadReader {
    data: Vec<u8>,
    pos: usize,
}

impl io::Read for PayloadReader {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = std::cmp::min(buf.len(), self.data.len() - self.pos);
        buf[..n].copy_from_slice(&self.data[self.pos..self.pos + n]);
        self.pos += n;
        Ok(n)
    }
}

impl ZeroCopyReader for PayloadReader {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let n = std::cmp::min(count, self.data.len() - self.pos);
        // Safe because the slice points into `self.data`, which outlives it.
        let slice =
            unsafe { FileVolatileSlice::from_raw_ptr(self.data.as_mut_ptr().add(self.pos), n) };
        let n = f.write_at_volatile(slice, off)?;
        self.pos += n;
        Ok(n)
    }
}

#[async_trait::async_trait(?Send)]
impl AsyncZeroCopyReader for PayloadReader {
    async fn async_read_to(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let n = std::cmp::min(count, self.data.len() - self.pos);
        // Safe because the buffer points into `self.data`, which outlives it.
        let buf =
            unsafe { FileVolatileBuf::from_raw_ptr(self.data.as_mut_ptr().add(self.pos), n, n) };
        let (res, _) = f.async_write_at_volatile(buf, off).await;
        let n = res?;
        self.pos += n;
        Ok(n)
    }
}

fn bench_passthrough(c: &mut Criterion) {
    let max = REQUEST_SIZES[REQUEST_SIZES.len() - 1];
    let (fs, _source) = prepare_fs(max);
    let ctx = prepare_context();
    let name = CString::new(TEST_FILE).unwrap();
    let inode = fs.lookup(&ctx, ROOT_ID, &name).unwrap().inode;
    let flags = libc::O_RDWR as u32;
    let handle = fs.open(&ctx, inode, flags, 0).unwrap().0.unwrap();
    let rt = Runtime::new();
    let mut w = MissWriter {
        buf: vec![0u8; max],
        len: 0,
    };
    let mut r = PayloadReader {
        data: vec![0x5au8; max],
        pos: 0,
    };

    let mut group = c.benchmark_group(format!("passthrough/{:?}", async_runtime::runtime_type()));
    for pool in [false, true] {
        fs.enable_async_thread_pool(pool);
        let mode = if pool { "pool" } else { "inline" };
        for &size in REQUEST_SIZES.iter() {
            group.throughput(Throughput::Bytes(size as u64));
            group.bench_with_input(
                BenchmarkId::new(format!("read_miss/{mode}"), size),
                &size,
                |b, &size| {
                    b.iter(|| {
                        w.len = 0;
                        let n = rt
                            .block_on(fs.async_read(
                                &ctx,
                                inode,
                                handle,
                                &mut w,
                                size as u32,
                                0,
                                None,
                                flags,
                            ))
                            .unwrap();
                        assert_eq!(n, size);
                    })
                },
            );
            group.bench_with_input(
                BenchmarkId::new(format!("write/{mode}"), size),
                &size,
                |b, &size| {
                    b.iter(|| {
                        r.pos = 0;
                        let n = rt
                            .block_on(fs.async_write(
                                &ctx,
                                inode,
                                handle,
                                &mut r,
                                size as u32,
                                0,
                                None,
                                false,
                                flags,
                                0,
                            ))
                            .unwrap();
                        assert_eq!(n, size);
                    })
                },
            );
        }
    }
    group.finish();
    fs.release(&ctx, inode, flags, handle, false, false, None)
        .unwrap();
}

criterion_group!(benches, bench_vectored, bench_passthrough);
criterion_main!(benches);
