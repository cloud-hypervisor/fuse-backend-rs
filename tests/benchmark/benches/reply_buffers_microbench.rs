// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

//! Micro-benchmark of a READ handler that serves file data from memory, the
//! way a file system with a chunk cache does.
//!
//! Each iteration runs one READ through `Server::handle_message()` and a
//! `FuseDevWriter`, once with the handler copying its chunks into the reply
//! (`copy`) and once handing them over with `write_owned()` (`owned`). The
//! writer sends the reply to a file in `/dev/shm`, so the kernel still copies
//! the data as it would on `/dev/fuse` and only the userspace copy differs.
//! In the `cold` cases successive READs walk through a pool much larger than
//! the CPU caches, like reads from a large chunk cache. In the `hot` cases
//! every READ serves the same data, like chunks that were just decompressed.
//!
//! Run with: `cargo bench --bench reply_buffers_microbench` from this
//! directory (Linux only).

use std::ffi::CStr;
use std::io::{self, Seek, SeekFrom};
use std::mem::{offset_of, size_of};
use std::ops::Range;
use std::os::fd::AsRawFd;
use std::path::Path;
use std::sync::Arc;
use std::time::Duration;

use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};
use vm_memory::ByteValued;
use vmm_sys_util::tempfile::TempFile;

use fuse_backend_rs::abi::fuse_abi::{InHeader, Opcode, OutHeader, ReadIn};
use fuse_backend_rs::api::filesystem::{Context, Entry, FileSystem, ZeroCopyWriter};
use fuse_backend_rs::api::server::Server;
use fuse_backend_rs::transport::{FuseDevWriter, Reader};

/// The largest READ the benchmark issues.
const MAX_READ: usize = 1 << 20;

/// The size of the file data, well beyond the last-level cache.
const POOL_SIZE: usize = 256 << 20;

/// Where the READ offset sits in an encoded request.
const OFFSET_POS: usize = size_of::<InHeader>() + offset_of!(ReadIn, offset);

/// A range of the shared file data, handed to the transport by `write_owned()`.
struct ChunkSlice {
    data: Arc<[u8]>,
    range: Range<usize>,
}

impl AsRef<[u8]> for ChunkSlice {
    fn as_ref(&self) -> &[u8] {
        &self.data[self.range.clone()]
    }
}

/// A one-file file system whose data lives in memory, split into chunks of
/// `chunk_size` bytes.
struct ChunkFs {
    data: Arc<[u8]>,
    chunk_size: usize,
    owned: bool,
}

impl FileSystem for ChunkFs {
    type Inode = u64;
    type Handle = u64;

    fn lookup(&self, _ctx: &Context, _parent: u64, _name: &CStr) -> io::Result<Entry> {
        Err(io::Error::from_raw_os_error(libc::ENOENT))
    }

    fn read(
        &self,
        _ctx: &Context,
        _inode: u64,
        _handle: u64,
        w: &mut dyn ZeroCopyWriter,
        size: u32,
        offset: u64,
        _lock_owner: Option<u64>,
        _flags: u32,
    ) -> io::Result<usize> {
        let mut pos = offset as usize;
        let end = pos + size as usize;
        while pos < end {
            let chunk_end = (pos / self.chunk_size + 1) * self.chunk_size;
            let range = pos..chunk_end.min(end);
            pos = range.end;
            if self.owned {
                w.write_owned(Box::new(ChunkSlice {
                    data: self.data.clone(),
                    range,
                }))?;
            } else {
                w.write_all(&self.data[range])?;
            }
        }
        Ok(size as usize)
    }
}

/// Encode a READ request for `size` bytes. The benchmark sets the offset at
/// `OFFSET_POS` before each READ.
fn read_request(size: usize) -> Vec<u8> {
    let len = size_of::<InHeader>() + size_of::<ReadIn>();
    let header = InHeader {
        len: len as u32,
        opcode: Opcode::Read as u32,
        unique: 1,
        nodeid: 2,
        ..Default::default()
    };
    let read_in = ReadIn {
        size: size as u32,
        ..Default::default()
    };
    let mut req = header.as_slice().to_vec();
    req.extend_from_slice(read_in.as_slice());
    req
}

fn bench_read(c: &mut Criterion) {
    let data: Arc<[u8]> = (0..POOL_SIZE).map(|i| (i >> 12) as u8).collect();
    let mut out = TempFile::new_in(Path::new("/dev/shm")).unwrap().into_file();
    let fd = out.as_raw_fd();
    let mut reply = vec![0u8; MAX_READ + size_of::<OutHeader>()];

    let mut group = c.benchmark_group("read_from_memory");
    for (cache, stride) in [("hot", 0), ("cold", 1)] {
        for chunk_size in [64 << 10, 256 << 10] {
            for size in [4 << 10, 32 << 10, 128 << 10, MAX_READ] {
                group.throughput(Throughput::Bytes(size as u64));
                for owned in [false, true] {
                    let server = Server::new(ChunkFs {
                        data: data.clone(),
                        chunk_size,
                        owned,
                    });
                    let mut req = read_request(size);
                    let mut offset = 0;
                    let mode = if owned { "owned" } else { "copy" };
                    let id = BenchmarkId::new(
                        format!("{cache}/{mode}/chunk{}k", chunk_size >> 10),
                        format!("{}k", size >> 10),
                    );
                    group.bench_function(id, |b| {
                        b.iter(|| {
                            offset = (offset + stride * size) % (POOL_SIZE - size);
                            req[OFFSET_POS..][..8].copy_from_slice(&(offset as u64).to_ne_bytes());
                            // Rewrite the sink from the start, so it doesn't grow.
                            out.seek(SeekFrom::Start(0)).unwrap();
                            let r = Reader::<()>::from_slice(&mut req);
                            let w = FuseDevWriter::<()>::new(fd, &mut reply).unwrap();
                            let n = server.handle_message(r, w, None, None).unwrap();
                            assert_eq!(n, size_of::<OutHeader>() + size);
                        })
                    });
                }
            }
        }
    }
    group.finish();
}

criterion_group! {
    name = benches;
    config = Criterion::default().measurement_time(Duration::from_secs(3));
    targets = bench_read
}
criterion_main!(benches);
