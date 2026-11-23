// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! FUSE-over-io_uring serving transport (experimental, kernel 6.14+, protocol 7.42).
//!
//! Requests registered through `IORING_OP_URING_CMD` SQEs on the /dev/fuse file
//! are delivered as CQEs; replies are sent back together with a re-registration
//! through `FUSE_IO_URING_CMD_COMMIT_AND_FETCH`. One kernel queue exists per
//! possible CPU, and each entry is attached to an explicit queue id chosen by
//! the daemon in the SQE command payload.
//!
//! The kernel still uses the classic /dev/fuse path for requests it cannot
//! route through io_uring (FUSE_FORGET, FUSE_INTERRUPT and requests queued
//! before entries were registered), so a classic channel thread keeps serving
//! in parallel.
//!
//! `UringFuseServing::new()` serves the rings with the synchronous handlers,
//! one request at a time per worker. `UringFuseServing::new_async()` serves
//! them with the asynchronous handlers, up to one request per ring entry at
//! a time per worker.
//!
//! On Linux 7.3 and later, the kernel can take the payload buffers from one
//! buffer pool per queue instead of one buffer per entry. See
//! `UringConfig::bufs_per_queue`.
//!
//! Experimental: the kernel interface is still evolving.

use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, IoSlice, Write};
use std::mem::ManuallyDrop;
use std::os::unix::io::{AsRawFd, RawFd};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Sender};
use std::sync::{Arc, Condvar, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use io_uring::{cqueue, opcode, squeue, types, IoUring};
use vm_memory::ByteValued;

use fuse_backend_core::abi::fuse_abi::{InHeader, Opcode, OutHeader, ReadIn};
use fuse_backend_core::abi::fuse_uring::{
    FuseUringBufpool, FuseUringCmdReq, FuseUringReqHeader, FUSE_IO_URING_CMD_ADD_BUFPOOL,
    FUSE_IO_URING_CMD_ADD_QUEUE, FUSE_IO_URING_CMD_COMMIT_AND_FETCH, FUSE_IO_URING_CMD_REGISTER,
    FUSE_URING_ENT_ZERO_COPY, FUSE_URING_IOV_SEGS, FUSE_URING_OP_IN_OUT_SZ, FUSE_URING_ZERO_COPY,
};
use fuse_backend_core::api::filesystem::FileSystem;
use fuse_backend_core::api::server::Server;
use fuse_backend_core::buffer::{Error::*, Reader, Result, Writer, ZeroCopySource};
use fuse_backend_core::file_buf::FileVolatileSlice;
use fuse_backend_core::file_traits::FileReadWriteVolatile;
#[cfg(feature = "async-io")]
use fuse_backend_core::{
    api::filesystem::AsyncFileSystem,
    async_runtime::{self, Runtime},
    file_buf::FileVolatileBuf,
    file_traits::AsyncFileReadWriteVolatile,
};
#[cfg(feature = "async-io")]
use futures_util::{
    stream::{FuturesUnordered, StreamExt},
    FutureExt,
};
#[cfg(feature = "async-io")]
use tokio::io::{unix::AsyncFd, Interest};
use vm_memory::bitmap::BitmapSlice;
use vm_memory::mmap::MmapRegion;

use crate::serving::{FuseServing, WorkerSet};
#[cfg(feature = "async-io")]
use crate::FuseDevTask;
use crate::{FuseChannel, FuseDevReaderExt, FuseSession, FUSE_HEADER_SIZE};

/// Size of `fuse_in_header`/`fuse_out_header` on the wire.
const IN_HEADER_SIZE: usize = 40;
const OUT_HEADER_SIZE: usize = 16;

/// Configuration of the io_uring serving transport.
#[derive(Clone, Copy, Debug)]
pub struct UringConfig {
    /// Number of worker threads, each owning one io_uring instance. The
    /// workers share the entries of every kernel queue, so several of them
    /// serve a busy queue. `0` means one worker per online CPU. The worker
    /// count is capped at `entries_per_queue` times the number of queues,
    /// so that every worker holds at least one entry.
    pub workers: usize,
    /// Number of ring entries registered per kernel queue, i.e. the number
    /// of in-flight requests each queue may hold. `0` counts as 1.
    pub entries_per_queue: usize,
    /// Number of payload buffers in each queue's buffer pool, on kernels
    /// that support buffer pools (Linux 7.3). The kernel lends a buffer to
    /// an entry only while it serves a request that carries a payload or
    /// takes a reply body, and it lends the free buffer with the lowest
    /// address first. A request waits in the kernel while all buffers of its
    /// queue are busy. A pool holds at most `entries_per_queue` buffers,
    /// because each entry holds at most one. `0`, or a kernel without
    /// buffer pools, gives every entry a buffer of its own instead.
    /// `UringFuseServing::new_async()` makes any other value
    /// `entries_per_queue`.
    pub bufs_per_queue: usize,
    /// Serve the reads and writes of opens that ask for it with zero-copy
    /// (`OpenOptions::IO_URING_ZERO_COPY`, Linux 7.3). The kernel lends the
    /// client's pages to the request, and the transport moves the data
    /// between them and the file the file system names with io_uring
    /// fixed-buffer operations, without copying it through memory. It
    /// needs buffer pools and CAP_SYS_ADMIN, and the transport serves
    /// without it otherwise. File systems must pass reads and writes of
    /// such opens to `ZeroCopyWriter::write_from()` and
    /// `ZeroCopyReader::read_to()` with a file that has a descriptor.
    /// `UringFuseServing::new_async()` ignores it.
    pub zero_copy: bool,
}

impl Default for UringConfig {
    fn default() -> Self {
        UringConfig {
            workers: 0,
            entries_per_queue: 4,
            bufs_per_queue: 4,
            zero_copy: false,
        }
    }
}

/// Whether the kernel lets this process serve FUSE over io_uring: the fuse
/// module's `enable_uring` parameter is on, and the process may create an
/// io_uring, which the `kernel.io_uring_disabled` sysctl can forbid.
///
/// Returns `false` also when the kernel has no FUSE-over-io_uring support
/// (kernel < 6.14, so the `enable_uring` parameter does not exist) or the
/// fuse module cannot be loaded. If the fuse module is not loaded yet, the
/// check opens `/dev/fuse`, which loads it.
///
/// `UringFuseServing::new()` still fails with `Error::UringNotSupported` if
/// the kernel refuses the transport at INIT, but checking first saves a
/// mount that has to fall back to `/dev/fuse`.
pub fn uring_available() -> bool {
    const PARAM: &str = "/sys/module/fuse/parameters/enable_uring";
    let read = || std::fs::read_to_string(PARAM);
    let param = read().or_else(|e| {
        // A fuse module that isn't loaded yet loads when /dev/fuse opens.
        if e.kind() != io::ErrorKind::NotFound || File::open("/dev/fuse").is_err() {
            return Err(e);
        }
        read()
    });
    param.is_ok_and(|v| v.trim() == "Y") && IoUring::new(1).is_ok()
}

/// Parse a CPU mask like "0-3,5,8-11" into the number of possible CPUs,
/// which is the number of kernel fuse queues.
fn parse_cpu_mask(content: &str) -> Result<usize> {
    let mut count = 0usize;
    for part in content.trim().split(',') {
        let range: Vec<&str> = part.split('-').collect();
        let (start, end) = match range.as_slice() {
            [a] => (*a, *a),
            [a, b] => (*a, *b),
            _ => return Err(SessionFailure(format!("invalid cpu mask range: {part}"))),
        };
        let start: usize = start
            .trim()
            .parse()
            .map_err(|_| SessionFailure(format!("invalid cpu mask: {content}")))?;
        let end: usize = end
            .trim()
            .parse()
            .map_err(|_| SessionFailure(format!("invalid cpu mask: {content}")))?;
        if end < start {
            return Err(SessionFailure(format!("invalid cpu mask range: {part}")));
        }
        count += end - start + 1;
    }
    if count == 0 {
        return Err(SessionFailure("empty cpu mask".to_string()));
    }
    Ok(count)
}

/// Read `/sys/devices/system/cpu/possible` to get the number of possible
/// CPUs, which is the number of kernel fuse queues.
fn possible_cpu_count() -> Result<usize> {
    let content = std::fs::read_to_string("/sys/devices/system/cpu/possible")
        .map_err(|e| SessionFailure(format!("read possible cpu mask: {e}")))?;
    parse_cpu_mask(&content)
}

/// Assign the ring entries of all queues to `workers` workers, returning
/// the queue id and registration round of every entry each worker
/// registers. `entries_per_queue` must be at least 1, and `bufs` is the
/// number of buffers in each queue's pool.
///
/// The kernel puts a request on the queue of the CPU that sends it, and a
/// single flusher thread sends all writeback WRITEs. A worker that owned
/// whole queues would serve such a stream alone, so the entries of every
/// queue go to consecutive workers instead. The kernel hands a request to
/// any free entry of its queue, so a busy queue reaches the other workers
/// once one worker's entries are all in use.
///
/// The kernel also hands a request to the entry of its queue that became
/// free last, see `UringWorker::register()`. So each queue registers one
/// entry of each of its workers last, one per round. A queue with an entry
/// on every worker registers the one on worker `qid % workers`, which
/// would own it with whole queues, last, so its requests go there while it
/// has one at a time. Queues 0 to `workers - 1` end on different workers,
/// and so do the next `workers` queues and so on. The other entries
/// register before them, in round 0.
fn spread_entries(
    nr_queues: usize,
    entries_per_queue: usize,
    workers: usize,
    bufs: usize,
) -> Vec<Vec<(u16, usize)>> {
    let total = nr_queues * entries_per_queue;
    let workers = workers.clamp(1, total);
    // The last queue_workers entries of a queue belong to different
    // workers, and the rest register before them.
    let queue_workers = entries_per_queue.min(workers);
    let rest = entries_per_queue - queue_workers;
    // With buffer pools, the entries that register last keep the buffers.
    let holders = bufs.clamp(1, queue_workers);
    // Queue qid's workers start at qid * entries_per_queue % workers, which
    // repeats after this many queues.
    let (mut gcd, mut b) = (entries_per_queue, workers);
    while b != 0 {
        (gcd, b) = (b, gcd % b);
    }
    let period = workers / gcd;
    let mut entries = vec![Vec::new(); workers];
    for qid in 0..nr_queues {
        // Queues workers apart have the same workers, so each one turns
        // the entries before its last one on, and its other buffers go to
        // different workers than the previous one's.
        let turn = qid / workers * (holders - 1);
        for nth in 0..entries_per_queue {
            let w = (qid * entries_per_queue + nth) % workers;
            let round = if nth < rest {
                0
            } else {
                // The number of last entries that register after this one.
                // The last one is on worker qid % workers if the queue has
                // an entry on every worker, else it moves on by one after
                // each period.
                let after = if queue_workers == workers {
                    (qid + workers - w) % workers
                } else {
                    (qid / period + queue_workers - (nth - rest)) % queue_workers
                };
                let after = match after {
                    0 => 0,
                    a => (a - 1 + turn) % (queue_workers - 1) + 1,
                };
                usize::from(rest > 0) + queue_workers - 1 - after
            };
            entries[w].push((qid as u16, round));
        }
    }
    entries
}

/// What the transport needs to know about a request with this opcode: the
/// size of the per-opcode arguments carried in the entry `op_in` slot, for
/// reassembling the classic wire layout, and whether the request has out
/// arguments, i.e. takes a reply body. The kernel copies `in_args[0]` (the
/// per-op header) into `op_in` and the remaining arguments into the payload
/// area, so a size of 0 means a known opcode without a fixed header. Over a
/// buffer pool, the kernel lends no buffer to a request without a payload
/// and without out arguments. `None` marks opcodes this table doesn't know.
fn op_args(opcode: u32) -> Option<(usize, bool)> {
    // No wildcard arm, so that a new Opcode doesn't build without an entry.
    let args = match Opcode::from(opcode) {
        Opcode::Lookup => (0, true),                         // name only
        Opcode::Forget => (8, false),                        // ForgetIn
        Opcode::Getattr => (16, true),                       // GetattrIn
        Opcode::Setattr => (88, true),                       // SetattrIn
        Opcode::Readlink => (0, true),                       // no arguments
        Opcode::Symlink => (0, true),                        // name + linkname
        Opcode::Mknod => (16, true),                         // MknodIn
        Opcode::Mkdir => (8, true),                          // MkdirIn
        Opcode::Unlink | Opcode::Rmdir => (0, false),        // name only
        Opcode::Rename => (8, false),                        // RenameIn
        Opcode::Link => (8, true),                           // LinkIn
        Opcode::Open => (8, true),                           // OpenIn
        Opcode::Read => (40, true),                          // ReadIn
        Opcode::Write => (40, true),                         // WriteIn
        Opcode::Statfs => (0, true),                         // no arguments
        Opcode::Release => (24, false),                      // ReleaseIn
        Opcode::Fsync => (16, false),                        // FsyncIn
        Opcode::Setxattr => (8, false),                      // SetxattrIn
        Opcode::Getxattr => (8, true),                       // GetxattrIn
        Opcode::Listxattr => (8, true),                      // GetxattrIn
        Opcode::Removexattr => (0, false),                   // name only
        Opcode::Flush => (24, false),                        // FlushIn
        Opcode::Init => (16, true),                          // InitIn
        Opcode::Opendir => (8, true),                        // OpenIn
        Opcode::Readdir | Opcode::Readdirplus => (40, true), // ReadIn
        Opcode::Releasedir => (24, false),                   // ReleaseIn
        Opcode::Fsyncdir => (16, false),                     // FsyncIn
        Opcode::Getlk => (48, true),                         // LkIn
        Opcode::Setlk | Opcode::Setlkw => (48, false),       // LkIn
        Opcode::Access => (8, false),                        // AccessIn
        Opcode::Create => (16, true),                        // CreateIn
        Opcode::Interrupt => (8, false),                     // InterruptIn
        Opcode::Bmap => (16, true),                          // BmapIn
        Opcode::Destroy => (0, false),                       // no arguments
        Opcode::Ioctl => (32, true),                         // IoctlIn
        Opcode::Poll => (24, true),                          // PollIn
        Opcode::NotifyReply => (0, false),                   // payload only
        Opcode::BatchForget => (8, false),                   // BatchForgetIn
        Opcode::Fallocate => (32, false),                    // FallocateIn
        Opcode::Rename2 => (16, false),                      // Rename2In
        Opcode::Lseek => (24, true),                         // LseekIn
        Opcode::CopyFileRange => (56, true),                 // CopyFileRangeIn
        // SETUPMAPPING/REMOVEMAPPING only exist on the virtiofs DAX window
        // path, never on /dev/fuse. Opcode::from() maps the numbers without
        // a variant to MaxOpcode and never returns the byte-swapped INIT
        // opcodes.
        Opcode::SetupMapping
        | Opcode::RemoveMapping
        | Opcode::MaxOpcode
        | Opcode::CuseInitBswapReserved
        | Opcode::InitBswapReserved => return None,
    };
    Some(args)
}

/// A [Writer] for io_uring replies that routes the reply header and body
/// into separate ring entry areas, eliminating the reply-staging memcpy.
///
/// The first `OUT_HEADER_SIZE` (16) bytes written go to `header` (which
/// points at the entry's `in_out` slot — the `fuse_out_header` area). All
/// subsequent bytes go to `body` (which points at the entry's payload area).
///
/// After `handle_message` returns, both regions contain the final reply and
/// the entry is ready for `COMMIT_AND_FETCH` without any post-copy.
#[derive(Debug, PartialEq, Eq)]
pub struct UringWriter<'a, S: BitmapSlice = ()> {
    /// Backed by the entry's `in_out` area; receives `fuse_out_header` (16 bytes).
    header: ManuallyDrop<Vec<u8>>,
    /// Backed by the entry's payload area; receives the reply body.
    body: ManuallyDrop<Vec<u8>>,
    /// The reply data of a zero-copy READ, which only the transport can
    /// produce.
    zero_copy: Option<ZeroCopyBody<'a>>,
    phantom: std::marker::PhantomData<&'a mut [S]>,
}

/// Reads a file into the client pages of a zero-copy READ.
trait ZeroCopySink: Sync {
    /// Read `count` bytes from the file `fd` at offset `off` into the client
    /// pages, starting `pos` bytes into them. Returns how many it read.
    fn read_from_file(&self, pos: usize, fd: RawFd, count: usize, off: u64) -> io::Result<usize>;

    /// Copy `data` into the client pages, starting `pos` bytes into them.
    /// This is the slow way, for replies built in memory.
    fn write_from_memory(&self, pos: usize, data: &[u8]) -> io::Result<()>;

    /// Let `fill` put up to `count` bytes into memory, and copy what it
    /// returns into the client pages, starting `pos` bytes into them.
    /// Returns how many bytes it copied. This is the slow way, for files
    /// without a descriptor.
    fn fill_from(
        &self,
        pos: usize,
        count: usize,
        fill: &mut dyn FnMut(&mut [u8]) -> io::Result<usize>,
    ) -> io::Result<usize>;
}

/// The reply data of a zero-copy READ: up to `cap` bytes that `sink` reads
/// into the client pages, of which `len` are read.
#[derive(Clone, Copy)]
struct ZeroCopyBody<'a> {
    sink: &'a dyn ZeroCopySink,
    cap: usize,
    len: usize,
}

impl ZeroCopyBody<'_> {
    /// Copy `data` from memory into the client pages, after what is there.
    fn push_memory(&mut self, data: &[u8]) -> io::Result<()> {
        check_space(self.cap - self.len, data.len())?;
        self.sink.write_from_memory(self.len, data)?;
        self.len += data.len();
        Ok(())
    }
}

impl std::fmt::Debug for ZeroCopyBody<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ZeroCopyBody")
            .field("cap", &self.cap)
            .field("len", &self.len)
            .finish()
    }
}

impl PartialEq for ZeroCopyBody<'_> {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::addr_eq(self.sink, other.sink) && self.cap == other.cap && self.len == other.len
    }
}

impl Eq for ZeroCopyBody<'_> {}

impl<'a, S: BitmapSlice> UringWriter<'a, S> {
    /// Construct a writer that routes the first `OUT_HEADER_SIZE` bytes
    /// to `header_buf` and all subsequent bytes to `body_buf`.
    pub fn new(header_buf: &'a mut [u8], body_buf: &'a mut [u8]) -> Self {
        debug_assert!(
            header_buf.len() >= OUT_HEADER_SIZE,
            "header slot must hold at least fuse_out_header ({} bytes)",
            OUT_HEADER_SIZE,
        );
        // Safe because ManuallyDrop prevents Vec from freeing externally-owned memory.
        let header = unsafe {
            ManuallyDrop::new(Vec::from_raw_parts(
                header_buf.as_mut_ptr(),
                0,
                header_buf.len(),
            ))
        };
        let body = unsafe {
            ManuallyDrop::new(Vec::from_raw_parts(
                body_buf.as_mut_ptr(),
                0,
                body_buf.len(),
            ))
        };
        UringWriter {
            header,
            body,
            zero_copy: None,
            phantom: std::marker::PhantomData,
        }
    }

    /// Let `sink` produce up to `cap` bytes of reply data, for a zero-copy
    /// READ. `write_from_at()` then reads the file into the client pages
    /// instead of the body.
    fn with_zero_copy(mut self, sink: &'a dyn ZeroCopySink, cap: usize) -> Self {
        self.zero_copy = Some(ZeroCopyBody { sink, cap, len: 0 });
        self
    }

    /// Split the writer at `offset` bytes of the combined (header + body)
    /// capacity. The zero-copy reply data, which comes after the body, goes
    /// to the returned writer.
    ///
    /// The two regions are non-contiguous, so the split redistributes
    /// capacity between `self` (first `offset` bytes) and the returned
    /// writer (remainder). This supports the two patterns used by the
    /// server:
    ///
    /// - `split_at(0)`: `self` becomes empty, returned writer keeps
    ///   everything (used by notify helpers).
    /// - `split_at(size_of::<OutHeader>())`: `self` keeps the header slot,
    ///   returned writer gets the body slot (used by READ / READDIR).
    pub fn split_at(&mut self, offset: usize) -> Result<UringWriter<'a, S>> {
        let total_cap = self.header.capacity() + self.body.capacity();
        if offset > total_cap {
            return Err(SplitOutOfBounds(offset));
        }

        let hdr_cap = self.header.capacity();
        let body_cap = self.body.capacity();
        let hdr_ptr = self.header.as_mut_ptr();
        let body_ptr = self.body.as_mut_ptr();

        // Drain both Vecs (they must be empty for from_raw_parts reuse).
        // Safety: both Vecs are freshly constructed with len=0.
        unsafe {
            self.header.set_len(0);
            self.body.set_len(0);
        }

        if offset <= hdr_cap {
            // Split falls within (or at the end of) the header region.
            // self gets header[0..offset], returned gets header[offset..] + body.
            let self_hdr = unsafe { ManuallyDrop::new(Vec::from_raw_parts(hdr_ptr, 0, offset)) };
            let other_hdr = unsafe {
                ManuallyDrop::new(Vec::from_raw_parts(
                    hdr_ptr.add(offset),
                    0,
                    hdr_cap - offset,
                ))
            };
            let other_body =
                unsafe { ManuallyDrop::new(Vec::from_raw_parts(body_ptr, 0, body_cap)) };
            self.header = self_hdr;
            // self.body is already drained (len=0, cap=body_cap) — shrink it.
            self.body = unsafe { ManuallyDrop::new(Vec::from_raw_parts(body_ptr, 0, 0)) };
            Ok(UringWriter {
                header: other_hdr,
                body: other_body,
                zero_copy: self.zero_copy.take(),
                phantom: std::marker::PhantomData,
            })
        } else {
            // Split falls within the body region (offset > hdr_cap).
            // self gets header + body[0..offset-hdr_cap],
            // returned gets body[offset-hdr_cap..].
            let body_split = offset - hdr_cap;
            let other_body = unsafe {
                ManuallyDrop::new(Vec::from_raw_parts(
                    body_ptr.add(body_split),
                    0,
                    body_cap - body_split,
                ))
            };
            // self keeps full header (already drained) and body[0..body_split].
            self.body = unsafe { ManuallyDrop::new(Vec::from_raw_parts(body_ptr, 0, body_split)) };
            Ok(UringWriter {
                header: unsafe {
                    ManuallyDrop::new(Vec::from_raw_parts(
                        std::ptr::NonNull::dangling().as_ptr(),
                        0,
                        0,
                    ))
                },
                body: other_body,
                zero_copy: self.zero_copy.take(),
                phantom: std::marker::PhantomData,
            })
        }
    }

    /// Total bytes written across both regions and the zero-copy data.
    pub fn bytes_written(&self) -> usize {
        self.header.len() + self.body.len() + self.zero_copy.map_or(0, |zc| zc.len)
    }

    /// Total capacity available across both regions and the zero-copy data.
    pub fn available_bytes(&self) -> usize {
        (self.header.capacity() - self.header.len())
            + (self.body.capacity() - self.body.len())
            + self.zero_copy.map_or(0, |zc| zc.cap - zc.len)
    }

    /// Account the bytes written by self and an optional split-off partner.
    pub fn commit(&mut self, other: Option<&UringWriter<'a, S>>) -> io::Result<usize> {
        let o = other.map(|w| w.bytes_written()).unwrap_or(0);
        Ok(self.bytes_written() + o)
    }

    fn check_available_space(&self, sz: usize) -> io::Result<()> {
        check_space(self.available_bytes(), sz)
    }

    /// Write data, routing the first `OUT_HEADER_SIZE` bytes to the header
    /// region and the remainder to the body region.
    fn scatter_write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.check_available_space(data.len())?;
        let hdr_remaining = self.header.capacity() - self.header.len();
        let to_hdr = data.len().min(hdr_remaining);
        if to_hdr < data.len() {
            match self.zero_copy.as_mut() {
                // The reply data of a zero-copy READ goes into the client
                // pages, through memory. That can fail, so it goes first,
                // and a failed write leaves the header alone.
                Some(zc) => zc.push_memory(&data[to_hdr..])?,
                None => self.body.extend_from_slice(&data[to_hdr..]),
            }
        }
        if to_hdr > 0 {
            self.header.extend_from_slice(&data[..to_hdr]);
        }
        Ok(data.len())
    }

    /// The unwritten end of the body region, after checking that `count`
    /// more bytes fit into it. Free space in the header slot doesn't count,
    /// because file data only goes into the body.
    fn body_tail(&mut self, count: usize) -> io::Result<*mut u8> {
        let spare = self.body.spare_capacity_mut();
        check_space(spare.len(), count)?;
        Ok(spare.as_mut_ptr().cast())
    }

    /// Account `cnt` bytes that a file read placed at `body_tail()`.
    ///
    /// # Safety
    /// The bytes must have been written at the pointer `body_tail(count)`
    /// returned, with `cnt <= count`.
    unsafe fn advance_body(&mut self, cnt: usize) {
        let new_len = self.body.len() + cnt;
        self.body.set_len(new_len);
    }

    /// Stage data read from a file descriptor at offset `off` into the body
    /// region. Must be called after the header has been fully written.
    pub fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        if let Some(zc) = self.zero_copy.as_mut() {
            check_space(zc.cap - zc.len, count)?;
            let Some(fd) = src.raw_fd() else {
                // Without a file descriptor, read the file into memory and
                // copy that into the client pages.
                let cnt = zc.sink.fill_from(zc.len, count, &mut |buf| {
                    // Safe because the slice covers `buf`, which outlives it.
                    let slice = unsafe { FileVolatileSlice::from_mut_slice(buf) };
                    src.read_at_volatile(slice, off)
                })?;
                zc.len += cnt;
                return Ok(cnt);
            };
            let cnt = zc.sink.read_from_file(zc.len, fd, count, off)?.min(count);
            zc.len += cnt;
            return Ok(cnt);
        }
        let tail = self.body_tail(count)?;
        // Safe because body_tail() checked that count bytes fit.
        let cnt = src
            .read_vectored_at_volatile(
                unsafe { &[FileVolatileSlice::from_raw_ptr(tail, count)] },
                off,
            )?
            .min(count);
        // Safe because the read placed cnt <= count bytes at the tail.
        unsafe { self.advance_body(cnt) };
        Ok(cnt)
    }

    /// Stage data read asynchronously from a file at offset `off` into the
    /// body region, like `write_from_at()`.
    ///
    /// The read points into memory the writer borrows, so the caller must
    /// not drop the future before it completes.
    #[cfg(feature = "async-io")]
    pub async fn async_write_from_at<F: AsyncFileReadWriteVolatile + ?Sized>(
        &mut self,
        src: &F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        if self.zero_copy.is_some() {
            // Moving zero-copy data waits on the worker's ring, which only
            // the synchronous handlers may do.
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                "zero-copy data can't be written asynchronously",
            ));
        }
        let tail = self.body_tail(count)?;
        // Safe because body_tail() checked that count bytes fit, and the
        // writer borrows the body region for 'a, which outlives the read.
        let buf = unsafe { FileVolatileBuf::from_raw_ptr(tail, 0, count) };
        let (res, _) = src.async_read_at_volatile(buf, off).await;
        let cnt = res?.min(count);
        // Safe because the read placed cnt <= count bytes at the tail.
        unsafe { self.advance_body(cnt) };
        Ok(cnt)
    }
}

fn check_space(available: usize, requested: usize) -> io::Result<()> {
    if requested > available {
        Err(io::Error::new(
            io::ErrorKind::InvalidData,
            format!("data out of range, available {available} requested {requested}"),
        ))
    } else {
        Ok(())
    }
}

impl<S: BitmapSlice> Write for UringWriter<'_, S> {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.scatter_write(data)
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        let total = bufs.iter().fold(0, |acc, b| acc + b.len());
        self.check_available_space(total)?;
        let mut written = 0usize;
        for b in bufs {
            if b.is_empty() {
                continue;
            }
            written += self.scatter_write(b)?;
        }
        Ok(written)
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl<'a, S: BitmapSlice> Writer for UringWriter<'a, S> {
    // The synchronous methods and `async_write_from_at` forward to the
    // inherent methods of the same name. The writer only stages the reply in
    // memory, so the other `async_*` methods run the `io::Write` methods and
    // `commit()`.
    fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        UringWriter::write_from_at(self, src, count, off)
    }

    fn split_at(&mut self, offset: usize) -> Result<Self> {
        UringWriter::split_at(self, offset)
    }

    fn available_bytes(&self) -> usize {
        UringWriter::available_bytes(self)
    }

    fn bytes_written(&self) -> usize {
        UringWriter::bytes_written(self)
    }

    fn commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        UringWriter::commit(self, other)
    }

    #[cfg(feature = "async-io")]
    async fn async_write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.write(data)
    }

    #[cfg(feature = "async-io")]
    async fn async_write2(&mut self, data: &[u8], data2: &[u8]) -> io::Result<usize> {
        self.write_vectored(&[IoSlice::new(data), IoSlice::new(data2)])
    }

    #[cfg(feature = "async-io")]
    async fn async_write3(&mut self, data: &[u8], data2: &[u8], data3: &[u8]) -> io::Result<usize> {
        self.write_vectored(&[IoSlice::new(data), IoSlice::new(data2), IoSlice::new(data3)])
    }

    #[cfg(feature = "async-io")]
    async fn async_write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.write_all(buf)
    }

    #[cfg(feature = "async-io")]
    async fn async_write_from_at<F: AsyncFileReadWriteVolatile + ?Sized>(
        &mut self,
        src: &F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        UringWriter::async_write_from_at(self, src, count, off).await
    }

    #[cfg(feature = "async-io")]
    async fn async_commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        UringWriter::commit(self, other)
    }
}

// Both buffers are owned by the caller (ring entry areas);
// UringWriter holds ManuallyDrop Vec shells, so dropping
// the writer never frees the memory.

/// The buffer pools of the kernel queues, in one anonymous mapping of
/// `queue_len` bytes per queue. The kernel cuts each queue's pool into
/// buffers of `buf_size` bytes and lends them to the queue's entries, which
/// can sit on any worker. Only pages that a request touched take memory.
struct BufPools {
    region: MmapRegion<()>,
    queue_len: usize,
    buf_size: usize,
}

impl BufPools {
    fn new(nr_queues: usize, bufs_per_queue: usize, buf_size: usize) -> io::Result<BufPools> {
        let queue_len = bufs_per_queue
            .checked_mul(buf_size)
            .filter(|&n| n <= u32::MAX as usize)
            .ok_or_else(|| io::Error::other("uring: buffer pool exceeds 4 GiB per queue"))?;
        let region = MmapRegion::build(
            None,
            queue_len * nr_queues,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE,
        )
        .map_err(io::Error::other)?;
        Ok(BufPools {
            region,
            queue_len,
            buf_size,
        })
    }

    /// The pool of queue `qid`, as the ADD_BUFPOOL command takes it.
    fn queue_pool(&self, qid: usize) -> FuseUringBufpool {
        FuseUringBufpool {
            uaddr: self.region.as_ptr() as u64 + (qid * self.queue_len) as u64,
            len: self.queue_len as u32,
            reserved: 0,
        }
    }

    /// The buffer at `offset` in the pool of queue `qid`, checked against
    /// the pool's layout.
    fn buffer(&self, qid: u16, offset: usize) -> Result<(NonNull<u8>, usize)> {
        let start = qid as usize * self.queue_len + offset;
        if offset % self.buf_size != 0
            || offset + self.buf_size > self.queue_len
            || start + self.buf_size > self.region.size()
        {
            return Err(SessionFailure(format!(
                "uring: buffer offset {offset} outside the pool of queue {qid}"
            )));
        }
        // Safe because the buffer lies inside the mapping, which isn't null.
        let ptr = unsafe { NonNull::new_unchecked(self.region.as_ptr().add(start)) };
        Ok((ptr, self.buf_size))
    }
}

/// Create a buffer pool for each kernel queue and hand them to the kernel
/// with ADD_QUEUE and ADD_BUFPOOL, before any entry registers. The kernel
/// offered buffer pools at INIT, so a failing command is an error.
///
/// With `zero_copy`, the queues also serve reads and writes with zero-copy,
/// which needs CAP_SYS_ADMIN and a kernel with protocol 7.46. If the kernel
/// refuses it with EPERM, or with EINVAL because it predates zero-copy, the
/// queues are added without it. Returns the pools and whether the queues
/// have zero-copy.
fn add_bufpools(
    fd: RawFd,
    nr_queues: usize,
    bufs_per_queue: usize,
    buf_size: usize,
    mut zero_copy: bool,
) -> io::Result<(BufPools, bool)> {
    let pools = BufPools::new(nr_queues, bufs_per_queue, buf_size)?;
    let mut ring = FuseRing::builder().build((nr_queues * 2).max(2) as u32)?;
    let mut first = 0;
    if zero_copy {
        // Try the first queue alone, so a refusal leaves no queue with
        // zero-copy. A kernel without zero-copy rejects the flag with
        // EINVAL. ADD_QUEUE also answers EINVAL for a missing ring or a bad
        // queue id, but INIT created the ring and queue 0 always exists.
        match add_queues(&mut ring, fd, &pools, 0..1, FUSE_URING_ZERO_COPY) {
            Err(e) if matches!(e.raw_os_error(), Some(libc::EPERM | libc::EINVAL)) => {
                warn!("uring: the kernel refused zero-copy ({e}), serving without it");
                zero_copy = false;
            }
            res => {
                res?;
                first = 1;
            }
        }
    }
    let flags = if zero_copy { FUSE_URING_ZERO_COPY } else { 0 };
    add_queues(&mut ring, fd, &pools, first..nr_queues, flags)?;
    Ok((pools, zero_copy))
}

/// Send ADD_QUEUE with `flags` and ADD_BUFPOOL for each queue in `qids`, and
/// return the first error the kernel reports.
fn add_queues(
    ring: &mut FuseRing,
    fd: RawFd,
    pools: &BufPools,
    qids: std::ops::Range<usize>,
    flags: u64,
) -> io::Result<()> {
    let mut pending = 0;
    {
        let mut sq = ring.submission();
        for qid in qids {
            let add_queue = FuseUringCmdReq {
                qid: qid as u16,
                flags,
                ..Default::default()
            };
            let add_bufpool = FuseUringCmdReq {
                flags: 0,
                bufpool: pools.queue_pool(qid),
                ..add_queue
            };
            // ADD_BUFPOOL needs the queue, so it runs after the ADD_QUEUE it
            // is linked to, and the kernel cancels it if that fails.
            let sqes = [
                cmd_sqe(fd, FUSE_IO_URING_CMD_ADD_QUEUE, &add_queue, None)
                    .flags(squeue::Flags::IO_LINK)
                    .user_data(qid as u64),
                cmd_sqe(fd, FUSE_IO_URING_CMD_ADD_BUFPOOL, &add_bufpool, None)
                    .user_data(qid as u64),
            ];
            // Safe because the commands point at nothing but the pool, which
            // lives as long as the entries the kernel lends its buffers to.
            unsafe { sq.push_multiple(&sqes) }
                .map_err(|_| io::Error::other("uring: setup ring full"))?;
            pending += 2;
        }
    }
    // The ADD_BUFPOOL of a failed ADD_QUEUE fails with ECANCELED, so report
    // another error if there is one.
    let mut error = None;
    while pending > 0 {
        submit_and_wait(ring, pending)?;
        for cqe in ring.completion() {
            pending -= 1;
            let res = cqe.result();
            if res < 0 && (error.is_none() || error == Some(libc::ECANCELED)) {
                error = Some(-res);
            }
        }
    }
    match error {
        Some(errno) => Err(io::Error::from_raw_os_error(errno)),
        None => Ok(()),
    }
}

/// Build a uring command SQE for `cmd_op` with `req` as its command payload.
/// `iovecs` is the iovec array of the entry the command registers or
/// commits.
fn cmd_sqe(
    fd: RawFd,
    cmd_op: u32,
    req: &FuseUringCmdReq,
    iovecs: Option<&[libc::iovec; FUSE_URING_IOV_SEGS]>,
) -> squeue::Entry128 {
    let mut bytes = [0u8; 80];
    bytes[..std::mem::size_of::<FuseUringCmdReq>()].copy_from_slice(req.as_slice());

    let mut sqe = opcode::UringCmd80::new(types::Fd(fd), cmd_op)
        .cmd(bytes)
        .build();
    let Some(iovecs) = iovecs else {
        return sqe;
    };
    // fuse_uring_get_iovec_from_sqe() wants the iovec array in sqe->addr
    // and the segment count in sqe->len. The crate has no setter for them
    // on URING_CMD entries, so write them at their offsets in struct
    // io_uring_sqe (include/uapi/linux/io_uring.h).
    const SQE_ADDR: usize = 16;
    const SQE_LEN: usize = 24;
    // Safe because Entry128 is a repr(C) SQE128 that starts with struct
    // io_uring_sqe, so both writes stay inside it.
    unsafe {
        let raw = (&raw mut sqe).cast::<u8>();
        raw.add(SQE_ADDR)
            .cast::<u64>()
            .write_unaligned(iovecs.as_ptr() as u64);
        raw.add(SQE_LEN)
            .cast::<u32>()
            .write_unaligned(FUSE_URING_IOV_SEGS as u32);
    }
    sqe
}

/// A FUSE ring. `IORING_OP_URING_CMD` with the FUSE command payload needs
/// 128-byte SQEs.
type FuseRing = IoUring<squeue::Entry128, cqueue::Entry>;

/// The number of zero-copy requests served, for the tests.
#[cfg(test)]
static ZERO_COPY_REQUESTS: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// The number of copies of zero-copy data through memory, for the tests.
#[cfg(test)]
static ZERO_COPY_BOUNCES: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

/// `user_data` of a zero-copy fixed-buffer operation. Entry indexes never
/// reach it.
const ZERO_COPY_USER_DATA: u64 = u64::MAX;

/// The completions of ring entries that a worker took off its ring and
/// hasn't handled yet, and how many entries the kernel still holds.
struct Completions {
    queue: VecDeque<(usize, i32)>,
    nr_entries: usize,
    /// The number of entries whose command the kernel hasn't completed.
    armed: usize,
}

impl Completions {
    /// Completions for `nr_entries` entries, all of them armed.
    fn new(nr_entries: usize) -> Self {
        Completions {
            queue: VecDeque::new(),
            nr_entries,
            armed: nr_entries,
        }
    }

    /// Take all completions off `ring`. The entries' completions join the
    /// queue, and the result of a zero-copy operation is returned.
    fn receive(&mut self, ring: &mut FuseRing) -> Option<i32> {
        let mut zero_copy = None;
        for cqe in ring.completion() {
            let idx = cqe.user_data() as usize;
            if cqe.user_data() == ZERO_COPY_USER_DATA {
                zero_copy = Some(cqe.result());
            } else if idx < self.nr_entries {
                self.armed = self.armed.saturating_sub(1);
                self.queue.push_back((idx, cqe.result()));
            } else {
                warn!("uring worker: CQE with unexpected user_data {}", idx);
            }
        }
        zero_copy
    }
}

/// How a zero-copy request moves its data.
#[derive(Clone, Copy)]
enum ZeroCopyKind {
    /// A WRITE whose data, `len` bytes, is in the client pages.
    Write { len: usize },
    /// A READ that may put up to `cap` bytes into the client pages.
    Read { cap: usize },
}

/// A worker's ring as a zero-copy request uses it: fixed-buffer reads and
/// writes on the buffer table slot where the kernel registered the client's
/// pages. Completions of ring entries that arrive meanwhile join the
/// worker's queue.
struct ZeroCopyIo<'r> {
    ring: Mutex<(&'r mut FuseRing, &'r mut Completions)>,
    slot: u16,
    /// The worker's memory file, which the copies through memory go
    /// through. The lock keeps two copies from using it at once.
    bounce: Mutex<&'r BounceBuf>,
}

/// The memory file that a worker's copies of zero-copy data through memory
/// go through, and a mapping of it. Fixed-buffer operations move data
/// between the file and the client pages, and the worker reaches the same
/// pages through the mapping.
struct BounceBuf {
    map: MmapRegion<()>,
}

impl BounceBuf {
    /// A memory file of `len` bytes, the most one copy moves.
    fn new(len: usize) -> io::Result<BounceBuf> {
        use nix::sys::memfd::{memfd_create, MFdFlags};
        let name = std::ffi::CStr::from_bytes_with_nul(b"fuse-uring-zero-copy\0").unwrap();
        let fd = memfd_create(name, MFdFlags::MFD_CLOEXEC).map_err(io::Error::from)?;
        let file = File::from(fd);
        file.set_len(len as u64)?;
        let map = MmapRegion::from_file(vm_memory::FileOffset::new(file, 0), len)
            .map_err(io::Error::other)?;
        Ok(BounceBuf { map })
    }

    /// The descriptor of the file.
    fn fd(&self) -> RawFd {
        // The mapping was built from the file, so it has one.
        self.map.file_offset().unwrap().file().as_raw_fd()
    }

    /// The mapped pages of the file.
    ///
    /// # Safety
    /// The caller must hold the lock around the `BounceBuf`, so that nothing
    /// else uses the pages.
    #[allow(clippy::mut_from_ref)]
    unsafe fn pages(&self) -> &mut [u8] {
        std::slice::from_raw_parts_mut(self.map.as_ptr(), self.map.size())
    }
}

impl ZeroCopyIo<'_> {
    /// Run `sqe` on the ring and wait for its result.
    fn run(&self, sqe: squeue::Entry) -> io::Result<usize> {
        let sqe = squeue::Entry128::from(sqe.user_data(ZERO_COPY_USER_DATA));
        let mut guard = self
            .ring
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let (ring, completions) = &mut *guard;
        // Safe because the operation points at the registered buffer, which
        // the kernel keeps until the entry commits, and the worker commits
        // only after this returns.
        while unsafe { ring.submission().push(&sqe) }.is_err() {
            submit(ring)?;
        }
        loop {
            submit_and_wait(ring, 1)?;
            match completions.receive(ring) {
                Some(res) if res < 0 => return Err(io::Error::from_raw_os_error(-res)),
                Some(res) => return Ok(res as usize),
                None => {}
            }
        }
    }
}

/// The length of a fixed-buffer operation for `count` bytes.
fn fixed_len(count: usize) -> u32 {
    count.min(u32::MAX as usize) as u32
}

// The kernel registers the client pages from address 0 of the slot, so
// `pos` is the address of the first byte to move.
impl ZeroCopyIo<'_> {
    /// Read `len` bytes of the memory file into the client pages, starting
    /// `pos` bytes into them.
    fn read_bounce(&self, bounce: &BounceBuf, pos: usize, len: usize) -> io::Result<()> {
        let fd = bounce.fd();
        let mut done = 0;
        while done < len {
            let n = self.read_from_file(pos + done, fd, len - done, done as u64)?;
            if n == 0 {
                return Err(io::Error::from(io::ErrorKind::UnexpectedEof));
            }
            done += n;
        }
        Ok(())
    }
}

impl ZeroCopySink for ZeroCopyIo<'_> {
    fn read_from_file(&self, pos: usize, fd: RawFd, count: usize, off: u64) -> io::Result<usize> {
        let buf = pos as *mut u8;
        self.run(
            opcode::ReadFixed::new(types::Fd(fd), buf, fixed_len(count), self.slot)
                .offset(off)
                .build(),
        )
    }

    fn write_from_memory(&self, pos: usize, data: &[u8]) -> io::Result<()> {
        let mut done = 0;
        while done < data.len() {
            done += self.fill_from(pos + done, data.len() - done, &mut |buf| {
                let n = buf.len().min(data.len() - done);
                buf[..n].copy_from_slice(&data[done..done + n]);
                Ok(n)
            })?;
        }
        Ok(())
    }

    fn fill_from(
        &self,
        pos: usize,
        count: usize,
        fill: &mut dyn FnMut(&mut [u8]) -> io::Result<usize>,
    ) -> io::Result<usize> {
        #[cfg(test)]
        ZERO_COPY_BOUNCES.fetch_add(1, Ordering::Relaxed);
        // Through the memory file into the client pages, which only
        // fixed-buffer operations reach.
        let bounce = self
            .bounce
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        // Safe because this holds the lock.
        let pages = unsafe { bounce.pages() };
        let len = count.min(pages.len());
        let n = fill(&mut pages[..len])?.min(len);
        self.read_bounce(&bounce, pos, n)?;
        Ok(n)
    }
}

impl ZeroCopySource for ZeroCopyIo<'_> {
    fn write_to_file(
        &self,
        pos: usize,
        fd: RawFd,
        count: usize,
        off: Option<u64>,
    ) -> io::Result<usize> {
        let buf = pos as *const u8;
        // Offset u64::MAX, the kernel's -1, writes at the file's position.
        let off = off.unwrap_or(u64::MAX);
        self.run(
            opcode::WriteFixed::new(types::Fd(fd), buf, fixed_len(count), self.slot)
                .offset(off)
                .build(),
        )
    }

    fn read_to_memory(
        &self,
        pos: usize,
        count: usize,
        take: &mut dyn FnMut(&[u8]) -> io::Result<usize>,
    ) -> io::Result<usize> {
        #[cfg(test)]
        ZERO_COPY_BOUNCES.fetch_add(1, Ordering::Relaxed);
        // From the client pages into the memory file, then to `take`
        // through the mapping.
        let bounce = self
            .bounce
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        let len = count.min(bounce.map.size());
        let n = self.write_to_file(pos, bounce.fd(), len, Some(0))?.min(len);
        // Safe because this holds the lock, and the kernel is done writing
        // the pages.
        let pages = unsafe { bounce.pages() };
        take(&pages[..n])
    }
}

/// Give `ring` an empty table of `nr` fixed buffers, where the kernel
/// registers the client pages of zero-copy requests. io-uring 0.6 has no
/// `register_buffers_sparse()`, so this makes the `IORING_REGISTER_BUFFERS2`
/// call itself, the way its `register_files_sparse()` does for files.
fn register_sparse_buffers(ring: &FuseRing, nr: usize) -> io::Result<()> {
    /// `struct io_uring_rsrc_register`.
    #[repr(C)]
    struct RsrcRegister {
        nr: u32,
        flags: u32,
        resv2: u64,
        data: u64,
        tags: u64,
    }
    const IORING_REGISTER_BUFFERS2: libc::c_long = 15;
    const IORING_RSRC_REGISTER_SPARSE: u32 = 1;
    let reg = RsrcRegister {
        nr: nr as u32,
        flags: IORING_RSRC_REGISTER_SPARSE,
        resv2: 0,
        data: 0,
        tags: 0,
    };
    // Safe because the kernel only reads `reg`, which outlives the call.
    let ret = unsafe {
        libc::syscall(
            libc::SYS_io_uring_register,
            ring.as_raw_fd(),
            IORING_REGISTER_BUFFERS2,
            &reg as *const RsrcRegister,
            std::mem::size_of::<RsrcRegister>(),
        )
    };
    if ret < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

/// Where the payload buffers of an entry come from.
enum Payload {
    /// The entry has a payload area of its own, of this many bytes.
    Own(usize),
    /// The entry's queue has a buffer pool in these pools, and the kernel
    /// lends the entry a buffer per request.
    Pool(Arc<BufPools>),
}

/// Size of an entry's request scratch: the in header plus the largest fixed
/// arguments a request can carry in `op_in`.
const REQ_SCRATCH_SIZE: usize = IN_HEADER_SIZE + FUSE_URING_OP_IN_OUT_SZ;

/// A request the kernel delivered into a ring entry, with the Reader over it
/// and the UringWriter for its reply. Both borrow the entry.
struct Request<'a> {
    unique: u64,
    /// The largest reply body the request may stage.
    reply_cap: usize,
    reader: Reader<'a, ()>,
    writer: UringWriter<'a, ()>,
    /// How the client pages of a zero-copy request move its data. The
    /// caller attaches them to the reader or the writer.
    zero_copy: Option<ZeroCopyKind>,
}

/// One ring entry: the memory areas the kernel reads and writes, plus a scratch
/// region used to reassemble the request header and fixed arguments.
struct UringEntry {
    qid: u16,
    /// Single allocation, laid out as
    /// [FuseUringReqHeader][own payload area][request scratch of REQ_SCRATCH_SIZE].
    mem: Box<[u8]>,
    payload: Payload,
    /// The slot of the worker's buffer table where the kernel registers the
    /// client pages of the entry's zero-copy requests, if its queue has
    /// zero-copy.
    zero_copy_slot: Option<u16>,
    /// iovec array referenced by the SQEs, must stay at a stable address.
    iovecs: Box<[libc::iovec; FUSE_URING_IOV_SEGS]>,
}

impl UringEntry {
    fn new(qid: u16, payload: Payload) -> UringEntry {
        let own_cap = match payload {
            Payload::Own(cap) => cap,
            Payload::Pool(_) => 0,
        };
        let header_len = std::mem::size_of::<FuseUringReqHeader>();
        let mem = vec![0u8; header_len + own_cap + REQ_SCRATCH_SIZE].into_boxed_slice();
        let base = mem.as_ptr();
        // A queue with a buffer pool takes no payload buffer at REGISTER.
        let own_payload = if own_cap == 0 {
            std::ptr::null_mut()
        } else {
            // Safe because the payload area follows the header in `mem`.
            unsafe { base.add(header_len) as *mut libc::c_void }
        };
        let iovecs = Box::new([
            libc::iovec {
                iov_base: base as *mut libc::c_void,
                iov_len: header_len,
            },
            libc::iovec {
                iov_base: own_payload,
                iov_len: own_cap,
            },
        ]);
        UringEntry {
            qid,
            mem,
            payload,
            zero_copy_slot: None,
            iovecs,
        }
    }

    /// Size of the entry's own payload area.
    fn own_cap(&self) -> usize {
        self.iovecs[1].iov_len
    }

    /// The payload buffer of the delivered request and its size. Over a
    /// buffer pool, the kernel reports the offset of the buffer it lent, but
    /// a request without a payload and without out arguments gets no buffer
    /// and offset 0, the same as the first buffer. Such a request gets an
    /// empty buffer, so its handler can't write into another entry's.
    fn payload_buffer(
        &mut self,
        has_out_args: bool,
        payload_sz: usize,
    ) -> Result<(NonNull<u8>, usize)> {
        match &self.payload {
            Payload::Own(cap) => {
                let header_len = std::mem::size_of::<FuseUringReqHeader>();
                // Safe because the own payload area follows the header in `mem`.
                let ptr = unsafe { NonNull::new_unchecked(self.mem.as_mut_ptr().add(header_len)) };
                Ok((ptr, *cap))
            }
            Payload::Pool(_) if payload_sz == 0 && !has_out_args => Ok((NonNull::dangling(), 0)),
            Payload::Pool(pools) => {
                pools.buffer(self.qid, self.header().ring_ent_in_out.offset as usize)
            }
        }
    }

    fn header(&self) -> &FuseUringReqHeader {
        let ptr = self.mem.as_ptr() as *const FuseUringReqHeader;
        // Safe because the allocation starts with an aligned FuseUringReqHeader.
        unsafe { &*ptr }
    }

    fn header_mut(&mut self) -> &mut FuseUringReqHeader {
        let ptr = self.mem.as_mut_ptr() as *mut FuseUringReqHeader;
        // Safe because the allocation starts with an aligned FuseUringReqHeader.
        unsafe { &mut *ptr }
    }

    /// Build the `FUSE_IO_URING_CMD_REGISTER`/`COMMIT_AND_FETCH` SQE for this
    /// entry, with `commit_id` set in the command payload.
    fn cmd_sqe(&self, fd: i32, cmd_op: u32, commit_id: u64, user_data: u64) -> squeue::Entry128 {
        let mut req = FuseUringCmdReq {
            qid: self.qid,
            commit_id,
            ..Default::default()
        };
        if let Some(slot) = self.zero_copy_slot {
            req.set_ent_zero_copy_buf_index(slot);
        }
        cmd_sqe(fd, cmd_op, &req, Some(&self.iovecs)).user_data(user_data)
    }

    /// Stage a `-errno` error reply, so that the subsequent
    /// `COMMIT_AND_FETCH` hands the client a proper error instead of the
    /// request data still sitting in the entry areas.
    fn stage_error_reply(&mut self, errno: i32) {
        // A partial reply may have overwritten the in header by now, but the
        // out header keeps `unique` at the same offset.
        let out = OutHeader {
            len: OUT_HEADER_SIZE as u32,
            error: -errno,
            unique: self.in_header().unique,
        };
        let header = self.header_mut();
        header.in_out[..OUT_HEADER_SIZE].copy_from_slice(out.as_slice());
        header.ring_ent_in_out.payload_sz = 0;
    }

    /// The header of the request the kernel delivered into this entry.
    fn in_header(&self) -> InHeader {
        let mut hdr = InHeader::default();
        hdr.as_mut_slice()
            .copy_from_slice(&self.header().in_out[..IN_HEADER_SIZE]);
        hdr
    }

    /// How the client pages of the delivered zero-copy request with
    /// `opcode` and `payload_sz` move its data.
    fn zero_copy_kind(&self, opcode: u32, payload_sz: usize) -> Result<ZeroCopyKind> {
        if opcode == Opcode::Read as u32 {
            // The kernel lends no payload buffer, and the reply data is
            // ReadIn.size bytes at most.
            let read_in = ReadIn::from_slice(&self.header().op_in[..size_of::<ReadIn>()])
                .ok_or_else(|| SessionFailure("uring: malformed zero-copy READ".into()))?;
            Ok(ZeroCopyKind::Read {
                cap: read_in.size as usize,
            })
        } else if opcode == Opcode::Write as u32 {
            // The kernel lends a payload buffer for WriteOut, and payload_sz
            // counts the data in the client pages.
            Ok(ZeroCopyKind::Write { len: payload_sz })
        } else {
            Err(SessionFailure(format!(
                "uring: zero-copy request with opcode {opcode}"
            )))
        }
    }

    /// Check the request the kernel delivered into this entry, and build
    /// the Reader over it and the UringWriter for its reply.
    ///
    /// This copies the in header and the fixed arguments behind it into the
    /// request scratch. The payload stays in the payload buffer, the
    /// entry's own or the one the kernel lent it, and the Reader reads it
    /// there. The writer puts the reply header into the `in_out` slot and
    /// the reply body into the payload buffer, so nothing is copied
    /// afterwards. Returns `None` if the entry already holds the reply.
    fn request(&mut self) -> Result<Option<Request<'_>>> {
        let in_header = self.in_header();
        // Answer an opcode the table doesn't know with ENOSYS here, rather
        // than dispatch it without its arguments. The kernel then stops
        // sending it, as it does with FUSE_STATX.
        let Some((args_len, has_out_args)) = op_args(in_header.opcode) else {
            self.stage_error_reply(libc::ENOSYS);
            return Ok(None);
        };
        let ent_in_out = self.header().ring_ent_in_out;
        let zero_copy = if ent_in_out.flags & FUSE_URING_ENT_ZERO_COPY == 0 {
            None
        } else {
            Some(self.zero_copy_kind(in_header.opcode, ent_in_out.payload_sz as usize)?)
        };
        let payload_sz = match zero_copy {
            // The payload buffer holds no data of a zero-copy WRITE.
            Some(ZeroCopyKind::Write { .. }) => 0,
            _ => ent_in_out.payload_sz as usize,
        };
        let (payload_buf, payload_cap, zc_cap) = match zero_copy {
            // A zero-copy READ has no payload buffer, even when it asks for
            // 0 bytes.
            Some(ZeroCopyKind::Read { cap }) => (NonNull::dangling(), 0, cap),
            _ => {
                let (buf, cap) = self.payload_buffer(has_out_args, payload_sz)?;
                (buf, cap, 0)
            }
        };
        if args_len > FUSE_URING_OP_IN_OUT_SZ || payload_sz > payload_cap {
            return Err(SessionFailure(format!(
                "uring: malformed request, opcode {} args {} payload {}",
                in_header.opcode, args_len, payload_sz
            )));
        }
        let header_len = std::mem::size_of::<FuseUringReqHeader>();
        let own_cap = self.own_cap();
        let base = self.mem.as_mut_ptr();
        // Safe because the entry allocation holds the request header, then
        // the own payload area, then the request scratch, which fits the in
        // header plus the largest fixed arguments checked above. The payload
        // buffer is the own area or a pool buffer the kernel lent the entry,
        // which the kernel doesn't touch until the entry commits.
        //
        // The Reader's payload and the Writer's body are mutable slices over
        // the same payload buffer, which Rust's aliasing rules don't allow.
        // This relies on the server parsing the whole request before it
        // writes the reply. Removing the overlap needs Reader and Writer
        // APIs over raw pointers.
        let (scratch, payload, out_header, body) = unsafe {
            let header = &*(base as *const FuseUringReqHeader);
            let scratch = std::slice::from_raw_parts_mut(
                base.add(header_len + own_cap),
                IN_HEADER_SIZE + args_len,
            );
            scratch[..IN_HEADER_SIZE].copy_from_slice(in_header.as_slice());
            scratch[IN_HEADER_SIZE..].copy_from_slice(&header.op_in[..args_len]);
            (
                scratch,
                std::slice::from_raw_parts_mut(payload_buf.as_ptr(), payload_sz),
                std::slice::from_raw_parts_mut(base, OUT_HEADER_SIZE),
                std::slice::from_raw_parts_mut(payload_buf.as_ptr(), payload_cap),
            )
        };

        let reader = Reader::from_uring_buffers(scratch, payload)?;
        Ok(Some(Request {
            unique: in_header.unique,
            reply_cap: payload_cap + zc_cap,
            reader,
            writer: UringWriter::new(out_header, body),
            zero_copy,
        }))
    }

    /// Record the size of the staged reply, `total` bytes including the
    /// reply header, whose body may take `reply_cap` bytes. `unique` names
    /// the request in errors.
    fn finish(&mut self, unique: u64, reply_cap: usize, total: usize) -> Result<()> {
        // Forget-like requests have no reply.
        let payload_len = match total {
            0 => 0,
            n if (OUT_HEADER_SIZE..=OUT_HEADER_SIZE + reply_cap).contains(&n) => {
                n - OUT_HEADER_SIZE
            }
            n => {
                return Err(SessionFailure(format!(
                    "uring: malformed reply of {n} bytes for unique 0x{unique:x}"
                )))
            }
        };
        self.header_mut().ring_ent_in_out.payload_sz = payload_len as u32;
        Ok(())
    }
}

/// The function a worker thread runs: `UringWorker::run()`, or
/// `UringWorker::run_async()` for asynchronous handlers.
type RunFn<F> = fn(UringWorker<F>, Arc<AtomicBool>, Sender<io::Result<()>>) -> io::Result<()>;

/// Prepare the body of the thread that serves the requests the kernel sends
/// through `/dev/fuse`: `UringFuseServing::fallback_sync()`, or
/// `UringFuseServing::fallback_async()` for asynchronous handlers. The body
/// sends on the `Sender` once it serves, and exits without sending if it
/// can't.
type FallbackFn<F> = fn(
    &mut FuseSession,
    Arc<Server<F>>,
    Arc<AtomicBool>,
) -> Result<Box<dyn FnOnce(Sender<()>) + Send>>;

/// One io_uring based serving thread, holding ring entries of several
/// kernel queues.
struct UringWorker<F: FileSystem + Send + Sync + 'static> {
    fd: File,
    /// Queue id and registration round of every ring entry this worker
    /// registers.
    entries: Vec<(u16, usize)>,
    /// Size of the payload area of an entry whose queue has no buffer pool.
    payload_cap: usize,
    /// The queues' buffer pools, if the kernel took them.
    pools: Option<Arc<BufPools>>,
    /// The memory file that copies of zero-copy data through memory go
    /// through, if the queues have zero-copy.
    bounce: Option<BounceBuf>,
    /// The registration rounds that all workers take part in.
    rounds: Arc<RegisterRounds>,
    server: Arc<Server<F>>,
    /// Ends the connection when the worker fails.
    abort: Arc<ConnectionAbort>,
}

/// Lets the workers register their entries in rounds, see
/// `UringWorker::register()`. Every worker waits at the end of each of the
/// `rounds` rounds until all workers have registered that round's entries.
struct RegisterRounds {
    rounds: usize,
    workers: usize,
    state: Mutex<RoundsState>,
    cv: Condvar,
}

#[derive(Default)]
struct RoundsState {
    round: usize,
    /// The number of workers done with the current round.
    done: usize,
    failed: bool,
}

impl RegisterRounds {
    fn new(workers: usize, rounds: usize) -> RegisterRounds {
        RegisterRounds {
            rounds,
            workers,
            state: Mutex::new(RoundsState::default()),
            cv: Condvar::new(),
        }
    }

    /// Wait until all workers are done with the current round. Returns
    /// false if a worker failed.
    fn wait(&self) -> bool {
        let mut state = self.state.lock().unwrap();
        let round = state.round;
        state.done += 1;
        if state.done == self.workers {
            state.round += 1;
            state.done = 0;
            self.cv.notify_all();
        }
        let state = self
            .cv
            .wait_while(state, |s| s.round == round && !s.failed)
            .unwrap();
        !state.failed
    }

    /// Fail the rounds, which releases the workers waiting for a round, and
    /// they fail too. A worker that won't take part in all rounds must call
    /// it, or the others wait forever.
    fn fail(&self) {
        // This runs while a panic unwinds, so it must not panic on a
        // poisoned lock.
        self.state
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner)
            .failed = true;
        self.cv.notify_all();
    }
}

/// Fails the rounds when dropped. Forget it once the worker is done.
struct RoundsGuard<'a>(&'a RegisterRounds);

impl Drop for RoundsGuard<'_> {
    fn drop(&mut self) {
        self.0.fail();
    }
}

/// Ends a FUSE connection, like `umount -f`, through its `abort` file in
/// the fusectl file system. A worker that fails leaves its queues without
/// entries, so requests that the kernel puts on them would wait forever.
/// Ending the connection fails those requests and the other workers'
/// commands instead, so every worker stops and `wait()` returns.
struct ConnectionAbort {
    /// `/sys/fs/fuse/connections/<minor>/abort`, if fusectl is mounted.
    path: Option<std::path::PathBuf>,
    /// Whether a worker ended the connection already.
    done: AtomicBool,
}

/// The minor device number of the last mount at `mountpoint`, an
/// absolute path, in `mountinfo`, the format of /proc/self/mountinfo.
fn mount_minor(mountinfo: &str, mountpoint: &std::path::Path) -> Option<u32> {
    // mountinfo writes space, tab, newline and backslash as octal escapes.
    let mountpoint: String = mountpoint
        .to_str()?
        .chars()
        .map(|c| match c {
            ' ' | '\t' | '\n' | '\\' => format!("\\{:03o}", c as u32),
            c => c.to_string(),
        })
        .collect();
    mountinfo.lines().rev().find_map(|line| {
        // ID, parent ID, major:minor, root, mount point, ...
        let mut fields = line.split(' ');
        let dev = fields.nth(2)?;
        let point = fields.nth(1)?;
        if point != mountpoint {
            return None;
        }
        dev.split_once(':')?.1.parse().ok()
    })
}

impl ConnectionAbort {
    /// The abort file of the connection mounted at `mountpoint`. fusectl
    /// names connections after the minor number of the mount's device,
    /// which comes from /proc/self/mountinfo, because a stat() of the
    /// mountpoint would wait for a FUSE request that nobody serves yet.
    /// `FuseSession` keeps the mountpoint canonical, as mountinfo has it.
    fn new(mountpoint: &std::path::Path) -> ConnectionAbort {
        let path = std::fs::read_to_string("/proc/self/mountinfo")
            .ok()
            .and_then(|info| mount_minor(&info, mountpoint))
            .map(|minor| {
                std::path::PathBuf::from(format!("/sys/fs/fuse/connections/{minor}/abort"))
            })
            .filter(|path| path.exists());
        ConnectionAbort {
            path,
            done: AtomicBool::new(false),
        }
    }

    /// End the connection, unless another worker did.
    fn abort(&self) {
        if self.done.swap(true, Ordering::AcqRel) {
            return;
        }
        let Some(path) = &self.path else {
            error!("uring: can't end the FUSE connection without fusectl, unmount it by hand");
            return;
        };
        if let Err(e) = std::fs::write(path, b"1") {
            error!("uring: can't end the FUSE connection, unmount it by hand: {e}");
        }
    }
}

/// Whether a worker that stopped with `result` failed while the connection
/// was up. Commands fail with ENOTCONN, ENODEV or ECANCELED once it ended,
/// also through an unmount from outside, and its minor number may then
/// belong to a new connection already.
fn failed_while_connected(result: &io::Result<()>, exit: &AtomicBool) -> bool {
    match result {
        Ok(()) => false,
        Err(e)
            if matches!(
                e.raw_os_error(),
                Some(libc::ENOTCONN | libc::ENODEV | libc::ECANCELED)
            ) =>
        {
            false
        }
        Err(_) => !exit.load(Ordering::Relaxed),
    }
}

impl<F: FileSystem + Send + Sync + 'static> UringWorker<F> {
    /// Create the worker's ring and entries and register the entries,
    /// reporting the outcome through `ready_tx`. The kernel holds all
    /// entries afterwards. `prepare` runs on the new ring before the
    /// registration, and its failure fails the setup.
    fn setup<T>(
        &self,
        ready_tx: &Sender<io::Result<()>>,
        prepare: impl FnOnce(&FuseRing) -> io::Result<T>,
    ) -> io::Result<(FuseRing, Vec<UringEntry>, T)> {
        // Release the other workers from the rounds if this one fails or
        // panics before it has taken part in all of them.
        let rounds = RoundsGuard(&self.rounds);
        let fail = |e: &io::Error| {
            let _ = ready_tx.send(Err(io::Error::other(e.to_string())));
        };
        let created = self.create_ring().and_then(|ring| {
            let prepared = prepare(&ring)?;
            Ok((ring, prepared))
        });
        let (mut ring, prepared) = match created {
            Ok(created) => created,
            Err(e) => {
                fail(&e);
                return Err(e);
            }
        };
        let mut entries: Vec<UringEntry> = Vec::with_capacity(self.entries.len());
        for &(qid, _) in &self.entries {
            let payload = match &self.pools {
                Some(pools) => Payload::Pool(pools.clone()),
                None => Payload::Own(self.payload_cap),
            };
            let mut entry = UringEntry::new(qid, payload);
            if self.bounce.is_some() {
                entry.zero_copy_slot = Some(entries.len() as u16);
            }
            entries.push(entry);
        }
        match self.register(&mut ring, &entries) {
            Ok(()) => {
                std::mem::forget(rounds);
                let _ = ready_tx.send(Ok(()));
                Ok((ring, entries, prepared))
            }
            Err((e, armed)) => {
                // Report the error before the others fail the rounds and
                // report theirs.
                fail(&e);
                drop(rounds);
                // The serving layer tears the connection down when it gets
                // the error, which gives the registered entries back.
                drop(prepared);
                let mut completions = Completions::new(entries.len());
                completions.armed = armed;
                release_entries(ring, entries, completions);
                Err(e)
            }
        }
    }

    /// The worker's ring, with a sparse buffer table of a slot per entry if
    /// the queues have zero-copy.
    fn create_ring(&self) -> io::Result<FuseRing> {
        let ring = FuseRing::builder().build((self.entries.len() * 2) as u32)?;
        if self.bounce.is_some() {
            register_sparse_buffers(&ring, self.entries.len()).map_err(|e| {
                io::Error::other(format!(
                    "registering the zero-copy buffer table failed: {e}"
                ))
            })?;
        }
        Ok(ring)
    }

    /// Register `entries` in `self.rounds`, each in the round
    /// `spread_entries()` gave it. Returns the error and the number of
    /// entries the kernel holds on failure. That counts every queued
    /// REGISTER, since `release_entries()` submits what a failed submit
    /// left queued.
    ///
    /// The kernel gives a request to the entry of its queue that became free
    /// last, so with rounds the entries a queue frees last at startup belong
    /// to different workers, and the first of them, the last to register, is
    /// on different workers for different queues.
    /// `docs/fuse-uring-performance.md` explains why that matters.
    /// The rounds only set that order at startup. Later it is the order of
    /// the last commits.
    fn register(
        &self,
        ring: &mut FuseRing,
        entries: &[UringEntry],
    ) -> std::result::Result<(), (io::Error, usize)> {
        let fd = self.fd.as_raw_fd();
        let mut armed = 0;
        for round in 0..self.rounds.rounds {
            {
                let mut sq = ring.submission();
                for (idx, (entry, &(_, r))) in entries.iter().zip(&self.entries).enumerate() {
                    if r != round {
                        continue;
                    }
                    // The CQE of each REGISTER SQE returns once a request
                    // has been assigned to the entry.
                    let sqe = entry.cmd_sqe(fd, FUSE_IO_URING_CMD_REGISTER, 0, idx as u64);
                    // Safe because release_entries() keeps the entries
                    // alive while the kernel holds them.
                    if unsafe { sq.push(&sqe) }.is_err() {
                        return Err((io::Error::other("submission queue full"), armed));
                    }
                    armed += 1;
                }
            }
            // The kernel registers the entries while it submits them.
            if let Err(e) = submit(ring) {
                return Err((e, armed));
            }
            if !self.rounds.wait() {
                return Err((io::Error::other("another worker failed to register"), armed));
            }
        }
        Ok(())
    }

    fn run(self, exit: Arc<AtomicBool>, ready_tx: Sender<io::Result<()>>) -> io::Result<()> {
        let (mut ring, mut entries, ()) = self.setup(&ready_tx, |_| Ok(()))?;
        let fd = self.fd.as_raw_fd();
        // A handler that panics stops the worker like an error, and the
        // panic goes on once the kernel has given the entries back.
        let mut panic = None;

        let mut completions = Completions::new(entries.len());
        let result = 'serve: loop {
            if let Err(e) = submit_and_wait(&mut ring, 1) {
                break 'serve Err(e);
            }
            // A zero-copy operation whose wait failed in ZeroCopyIo::run()
            // completes late, with nothing left to do.
            completions.receive(&mut ring);

            while let Some((idx, res)) = completions.queue.pop_front() {
                let entry = &mut entries[idx];
                if res < 0 {
                    break 'serve stop_result(&exit, res);
                }

                let served = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                    self.process(entry, &mut ring, &mut completions)
                }));
                if let Some(payload) = settle(entry, served) {
                    panic = Some(payload);
                    break 'serve Err(io::Error::other("a request handler panicked"));
                }
                if let Err(e) = push_commit(&mut ring, fd, entry, idx) {
                    break 'serve Err(e);
                }
                // Count the commit once it is queued, because
                // release_entries() submits anything still queued.
                completions.armed += 1;
            }
            // The wait at the top of the loop submits the queued commits.
        };
        // The kernel gives the entries back once the connection ends.
        if failed_while_connected(&result, &exit) {
            self.abort.abort();
        }
        release_entries(ring, entries, completions);
        if let Some(payload) = panic {
            error!("uring worker: a request handler panicked");
            std::panic::resume_unwind(payload);
        }
        result
    }

    /// Serve the request delivered into `entry` and stage its reply there.
    ///
    /// The client pages of a zero-copy request stay with the kernel, and
    /// fixed-buffer operations on `ring` move the data between them and the
    /// file. Ring completions that arrive meanwhile go to `completions`.
    fn process(
        &self,
        entry: &mut UringEntry,
        ring: &mut FuseRing,
        completions: &mut Completions,
    ) -> Result<()> {
        let slot = entry.zero_copy_slot;
        let Some(Request {
            unique,
            reply_cap,
            reader,
            writer,
            zero_copy,
        }) = entry.request()?
        else {
            return Ok(());
        };
        let zc_io;
        let (reader, writer) = match zero_copy {
            None => (reader, writer),
            Some(kind) => {
                let (Some(slot), Some(bounce)) = (slot, self.bounce.as_ref()) else {
                    return Err(SessionFailure(
                        "uring: zero-copy request on a worker without zero-copy".into(),
                    ));
                };
                #[cfg(test)]
                ZERO_COPY_REQUESTS.fetch_add(1, Ordering::Relaxed);
                zc_io = ZeroCopyIo {
                    ring: Mutex::new((ring, completions)),
                    slot,
                    bounce: Mutex::new(bounce),
                };
                match kind {
                    ZeroCopyKind::Write { len } => (reader.with_zero_copy(&zc_io, len), writer),
                    ZeroCopyKind::Read { cap } => (reader, writer.with_zero_copy(&zc_io, cap)),
                }
            }
        };
        let total = self
            .server
            .handle_message(reader, writer, None, None)
            .map_err(|e| {
                SessionFailure(format!("uring: handle message unique 0x{unique:x}: {e}"))
            })?;
        entry.finish(unique, reply_cap, total)
    }
}

/// Submit what is queued on `ring`. A signal that interrupts the submit is
/// no error, because whatever it left queued goes with the next submit.
fn submit(ring: &mut FuseRing) -> io::Result<()> {
    match ring.submit() {
        Ok(_) => Ok(()),
        Err(e) if e.raw_os_error() == Some(libc::EINTR) => Ok(()),
        Err(e) => Err(e),
    }
}

/// Submit what is queued on `ring` and wait for `want` completions, retrying
/// when a signal interrupts the wait.
fn submit_and_wait(ring: &mut FuseRing, want: usize) -> io::Result<()> {
    loop {
        match ring.submit_and_wait(want) {
            Ok(_) => return Ok(()),
            Err(e) if e.raw_os_error() == Some(libc::EINTR) => {}
            Err(e) => return Err(e),
        }
    }
}

#[cfg(feature = "async-io")]
impl<F: AsyncFileSystem + Send + Sync + 'static> UringWorker<F> {
    /// Serve requests with the asynchronous handlers, each in its own
    /// future, on an async runtime of this thread.
    fn run_async(self, exit: Arc<AtomicBool>, ready_tx: Sender<io::Result<()>>) -> io::Result<()> {
        // Create the runtime and register the ring fd with it before the
        // registration, so a failure fails the constructor and can't free
        // entries the kernel holds. Runtime::new() panics on failure. That
        // has to become an error here, because the other workers keep the
        // ready channel open and the constructor would never see this
        // thread exit.
        let (mut ring, entries, (runtime, ring_ready)) = self.setup(&ready_tx, |ring| {
            let runtime = std::panic::catch_unwind(Runtime::new)
                .map_err(|_| io::Error::other("failed to create the async runtime"))?;
            // Safe because the AsyncFd is dropped in serve_async(), before
            // release_entries() closes the ring.
            let ring_ready = runtime
                .block_on(async {
                    unsafe { AsyncFd::register_with_interest(ring.as_raw_fd(), Interest::READABLE) }
                })
                .map_err(io::Error::from)?;
            Ok((runtime, ring_ready))
        })?;
        let mut completions = Completions::new(entries.len());
        let mut entries: Vec<Option<UringEntry>> = entries.into_iter().map(Some).collect();
        // Like run(), the worker goes on with a handler's panic once the
        // kernel has given the entries back.
        let mut panic = None;
        let result = runtime.block_on(self.serve_async(
            &mut ring,
            ring_ready,
            &mut entries,
            &mut completions,
            &exit,
            &mut panic,
        ));
        release_entries(ring, entries.into_iter().flatten().collect(), completions);
        if let Some(payload) = panic {
            error!("uring worker: a request handler panicked");
            std::panic::resume_unwind(payload);
        }
        result
    }

    /// The loop of `run_async()`. A delivered request moves its entry into
    /// a request future, which hands it back with the reply staged. So the
    /// kernel and a handler never use an entry at the same time, and a
    /// waiting handler doesn't hold up the requests in other entries.
    ///
    /// The ring fd is readable while completions are queued, so the loop
    /// sleeps in the runtime until a completion or a request future is
    /// ready. It commits all requests that are done by then and submits
    /// the commits in one `io_uring_enter()`. It lets the runtime park every
    /// `PARK_AFTER_REQUESTS` requests.
    ///
    /// Tearing the connection down fails the commands of the armed entries,
    /// which stops the loop. While no entry is armed, no command can fail,
    /// so the loop checks `exit` every `EXIT_POLL` instead.
    async fn serve_async(
        &self,
        ring: &mut FuseRing,
        ring_ready: AsyncFd<RawFd>,
        entries: &mut [Option<UringEntry>],
        completions: &mut Completions,
        exit: &AtomicBool,
        panic: &mut Option<Box<dyn std::any::Any + Send>>,
    ) -> io::Result<()> {
        let fd = self.fd.as_raw_fd();
        let server = &*self.server;
        let mut inflight = FuturesUnordered::new();
        // The requests taken since the last park().
        let mut taken = 0;

        let result = 'serve: loop {
            completions.receive(ring);
            while let Some((idx, res)) = completions.queue.pop_front() {
                let Some(mut entry) = entries[idx].take() else {
                    break 'serve Err(io::Error::other(format!(
                        "completion for entry {idx}, which a handler holds"
                    )));
                };
                if res < 0 {
                    entries[idx] = Some(entry);
                    break 'serve stop_result(exit, res);
                }
                inflight.push(async move {
                    let served = std::panic::AssertUnwindSafe(process_async(server, &mut entry))
                        .catch_unwind()
                        .await;
                    let caught = settle(&mut entry, served);
                    (idx, entry, caught)
                });
                taken += 1;
            }
            if !ring.submission().is_empty() {
                if let Err(e) = submit(ring) {
                    break 'serve Err(e);
                }
            }
            if taken >= PARK_AFTER_REQUESTS {
                taken = 0;
                async_runtime::park().await;
            }

            tokio::select! {
                biased;
                Some(done) = inflight.next(), if !inflight.is_empty() => {
                    let mut done = Some(done);
                    while let Some((idx, entry, caught)) = done {
                        if let Some(payload) = caught {
                            // The handler may have left a read into the
                            // entry running, so leak the entry. The kernel
                            // doesn't hold it.
                            std::mem::forget(entry);
                            *panic = Some(payload);
                            break 'serve Err(io::Error::other("a request handler panicked"));
                        }
                        let pushed = push_commit(ring, fd, &entry, idx);
                        entries[idx] = Some(entry);
                        if let Err(e) = pushed {
                            break 'serve Err(e);
                        }
                        completions.armed += 1;
                        done = inflight.next().now_or_never().flatten();
                    }
                }
                ready = ring_ready.readable() => match ready {
                    // Clear the readiness before draining the completion
                    // queue at the top of the loop, so a completion that
                    // arrives in between makes the fd readable again.
                    Ok(mut guard) => guard.clear_ready(),
                    Err(e) => break 'serve Err(e),
                },
                // Lazy, because select! builds the futures of disabled
                // branches too.
                _ = async { tokio::time::sleep(EXIT_POLL).await }, if completions.armed == 0 => {
                    if exit.load(Ordering::Relaxed) {
                        break 'serve Ok(());
                    }
                }
            }
        };

        // A failed worker ends the connection now, so the requests on its
        // queues don't wait for it, and the kernel gives its entries back.
        if failed_while_connected(&result, exit) {
            self.abort.abort();
        }

        // Let the requests in flight finish before release_entries() can
        // free their entries, because a handler may have a read into its
        // entry pending in the kernel. Their replies still go out if the
        // connection is up. Handlers that don't finish in time are leaked
        // with their entries, so a stuck one can't hang the shutdown.
        let drain = async {
            while let Some((idx, entry, caught)) = inflight.next().await {
                if let Some(payload) = caught {
                    std::mem::forget(entry);
                    panic.get_or_insert(payload);
                    continue;
                }
                if push_commit(ring, fd, &entry, idx).is_ok() {
                    completions.armed += 1;
                    let _ = submit(ring);
                }
                entries[idx] = Some(entry);
            }
        };
        if tokio::time::timeout(DRAIN_TIMEOUT, drain).await.is_err() {
            warn!(
                "uring worker: leaking {} requests whose handlers didn't finish",
                inflight.len()
            );
            std::mem::forget(inflight);
        }
        result
    }
}

/// How many requests an async worker takes before it lets its runtime park
/// with `async_runtime::park()`, whose doc says why that matters.
///
/// While requests keep coming, the worker finds them on its ring without
/// waiting, and its runtime never parks. A return to the runtime isn't
/// enough, because a runtime with a task to run or a woken `block_on()`
/// future polls its driver without parking. So unlike `PARK_AFTER_READS` of
/// `FuseDevTask`, the count doesn't restart when the worker waited.
#[cfg(feature = "async-io")]
const PARK_AFTER_REQUESTS: usize = 64;

/// How long a stopping async worker waits for its handlers to finish.
#[cfg(feature = "async-io")]
const DRAIN_TIMEOUT: Duration = Duration::from_secs(10);

/// How often an async worker without armed entries checks whether the
/// serving layer is stopping.
#[cfg(feature = "async-io")]
const EXIT_POLL: Duration = Duration::from_millis(100);

#[cfg(feature = "async-io")]
async fn process_async<F: AsyncFileSystem + Sync>(
    server: &Server<F>,
    entry: &mut UringEntry,
) -> Result<()> {
    let Some(Request {
        unique,
        reader,
        writer,
        zero_copy,
        reply_cap,
    }) = entry.request()?
    else {
        return Ok(());
    };
    if zero_copy.is_some() {
        return Err(SessionFailure(
            "uring: zero-copy request on an async worker".into(),
        ));
    }
    // Safe because the reader and writer borrow `entry`, which the request
    // future owns, and the worker never drops a request future before it
    // completes.
    let total = unsafe { server.async_handle_message(reader, writer, None, None) }
        .await
        .map_err(|e| SessionFailure(format!("uring: handle message unique 0x{unique:x}: {e}")))?;
    entry.finish(unique, reply_cap, total)
}

/// Stage an EIO reply in `entry` if its handler failed, and return the
/// panic payload if it panicked.
fn settle(
    entry: &mut UringEntry,
    served: std::thread::Result<Result<()>>,
) -> Option<Box<dyn std::any::Any + Send>> {
    match served {
        Ok(Ok(())) => None,
        Ok(Err(e)) => {
            warn!("uring worker: failed to handle request: {e}");
            entry.stage_error_reply(libc::EIO);
            None
        }
        Err(payload) => Some(payload),
    }
}

/// What a worker returns after a command failed with `res`. It is `Ok` if
/// the serving layer is stopping, which fails the commands as it tears the
/// connection down, and the error otherwise. A failed command leaves the
/// entry in an undefined state, so the worker stops instead of guessing.
fn stop_result(exit: &AtomicBool, res: i32) -> io::Result<()> {
    if exit.load(Ordering::Relaxed) {
        Ok(())
    } else {
        Err(io::Error::from_raw_os_error(-res))
    }
}

/// Queue the `COMMIT_AND_FETCH` for the entry at `idx`, which hands its
/// staged reply to the kernel and registers it for the next request.
fn push_commit(ring: &mut FuseRing, fd: RawFd, entry: &UringEntry, idx: usize) -> io::Result<()> {
    let commit_id = entry.header().ring_ent_in_out.commit_id;
    let sqe = entry.cmd_sqe(
        fd,
        FUSE_IO_URING_CMD_COMMIT_AND_FETCH,
        commit_id,
        idx as u64,
    );
    loop {
        // Safe because release_entries() keeps the entries alive while the
        // kernel holds them.
        if unsafe { ring.submission().push(&sqe) }.is_ok() {
            return Ok(());
        }
        // The submission queue can never hold more outstanding commits than
        // completed entries, so submitting must eventually make room.
        submit(ring)?;
    }
}

/// How long a stopping worker waits for the kernel to give back the ring
/// entries it still holds.
const RELEASE_TIMEOUT: Duration = Duration::from_secs(1);

/// Drop `ring` and `entries` once the kernel holds none of the entries.
///
/// The kernel may copy a request into an entry until it completes the
/// entry's command, and closing the ring only cancels the commands later,
/// from a workqueue. So wait for the `armed` outstanding completions first,
/// which arrive quickly once the connection is torn down. If they don't
/// arrive within `RELEASE_TIMEOUT`, leak the entries instead of freeing
/// memory the kernel may still write to.
fn release_entries(mut ring: FuseRing, entries: Vec<UringEntry>, completions: Completions) {
    let Completions {
        nr_entries,
        mut armed,
        ..
    } = completions;
    let deadline = Instant::now() + RELEASE_TIMEOUT;
    while armed > 0 {
        let left = deadline.saturating_duration_since(Instant::now());
        if left.is_zero() {
            break;
        }
        let ts = types::Timespec::new()
            .sec(left.as_secs())
            .nsec(left.subsec_nanos());
        let args = types::SubmitArgs::new().timespec(&ts);
        // Not submit_and_wait(): a timeout or a full completion queue is no
        // reason to stop waiting either.
        match ring.submitter().submit_with_args(1, &args) {
            Ok(_) => {}
            Err(e)
                if matches!(
                    e.raw_os_error(),
                    Some(libc::ETIME | libc::EINTR | libc::EBUSY | libc::EAGAIN)
                ) => {}
            Err(e) => {
                warn!("uring worker: waiting for entries failed: {e}");
                break;
            }
        }
        // Count the completions tagged with an entry index. An async worker
        // passes only the entries it holds again, so `entries` may be
        // shorter than the worker's entry count.
        armed = armed.saturating_sub(
            ring.completion()
                .filter(|cqe| cqe.user_data() < nr_entries as u64)
                .count(),
        );
    }
    if armed > 0 {
        warn!("uring worker: leaking {armed} ring entries that the kernel still holds");
        std::mem::forget(entries);
    }
    drop(ring);
}

/// Serve FUSE requests over io_uring (experimental).
///
/// The serving layer takes ownership of the mounted session: dropping it
/// unmounts the filesystem and joins all serving threads.
pub struct UringFuseServing<F: FileSystem + Send + Sync + 'static> {
    session: FuseSession,
    workers: WorkerSet,
    /// The number of buffers in each queue's pool, or 0 without pools.
    #[cfg(test)]
    pool_bufs: usize,
    /// Whether the queues have zero-copy.
    #[cfg(test)]
    zero_copy: bool,
    _fs: std::marker::PhantomData<F>,
}

impl<F: FileSystem + Send + Sync + 'static> UringFuseServing<F> {
    /// Create a new io_uring serving transport on an already mounted session.
    ///
    /// The `FUSE_OVER_IO_URING` capability must have been requested through
    /// `Server::set_uring()` before mounting. This constructor consumes the
    /// INIT request on a classic channel and verifies that the kernel
    /// accepted the capability, returning `Error::UringNotSupported`
    /// otherwise so that the caller can fall back to the classic transport.
    pub fn new(
        session: FuseSession,
        server: Arc<Server<F>>,
        cfg: UringConfig,
    ) -> Result<UringFuseServing<F>> {
        Self::start(session, server, cfg, UringWorker::run, Self::fallback_sync)
    }

    /// Handle INIT, then start the workers, each running `run`, and the
    /// fallback thread that `fallback` prepares.
    fn start(
        mut session: FuseSession,
        server: Arc<Server<F>>,
        cfg: UringConfig,
        run: RunFn<F>,
        fallback: FallbackFn<F>,
    ) -> Result<UringFuseServing<F>> {
        warn!("FUSE-over-io_uring transport is experimental, the kernel interface may change");

        let payload_cap = session.bufsize().saturating_sub(FUSE_HEADER_SIZE);
        let nr_queues = possible_cpu_count()?;

        // The first message on a new connection is always FUSE_INIT; handle
        // it on a classic channel and verify the negotiation outcome.
        let mut init_ch = session.new_channel()?;
        match init_ch.get_request() {
            Ok(Some((reader, writer))) => {
                server
                    .handle_message(reader, writer, None, None)
                    .map_err(|e| SessionFailure(format!("uring: INIT failed: {e}")))?;
            }
            Ok(None) => {
                return Err(SessionFailure(
                    "uring: session interrupted during INIT".into(),
                ))
            }
            Err(e) => return Err(SessionFailure(format!("uring: INIT read failed: {e}"))),
        }
        if !server.uring_enabled() {
            return Err(UringNotSupported);
        }

        let workers = if cfg.workers == 0 {
            std::thread::available_parallelism()
                .map(|n| n.get())
                .unwrap_or(1)
        } else {
            cfg.workers
        };
        let entries_per_queue = cfg.entries_per_queue.max(1);

        let file = session
            .get_fuse_file()
            .ok_or_else(|| SessionFailure("uring: session not mounted".into()))?
            .try_clone()
            .map_err(|e| SessionFailure(format!("uring: dup fuse fd: {e}")))?;

        // A queue's entries hold at most one buffer each, so more buffers
        // than entries would never be lent.
        let bufs_per_queue = cfg.bufs_per_queue.min(entries_per_queue);
        let spread = spread_entries(nr_queues, entries_per_queue, workers, bufs_per_queue);
        let workers = spread.len();
        // The kernel takes a 16-bit buffer table slot per entry, and each
        // entry of a worker gets its own slot.
        let worker_entries = spread.iter().map(Vec::len).max().unwrap_or(0);
        let want_zero_copy = cfg.zero_copy && worker_entries <= u16::MAX as usize + 1;
        if cfg.zero_copy && !want_zero_copy {
            warn!("uring: zero-copy needs at most 65536 entries per worker, serving without it");
        }
        let mut zero_copy = false;
        let pools = if bufs_per_queue > 0 && server.uring_bufpool_supported() {
            let buf_size = server.uring_payload_size();
            let pools;
            (pools, zero_copy) = add_bufpools(
                file.as_raw_fd(),
                nr_queues,
                bufs_per_queue,
                buf_size,
                want_zero_copy,
            )
            .map_err(|e| SessionFailure(format!("uring: adding the buffer pools failed: {e}")))?;
            info!(
                "uring: each queue has a pool of {bufs_per_queue} buffers of {buf_size} bytes{}",
                if zero_copy { ", and zero-copy" } else { "" }
            );
            Some(Arc::new(pools))
        } else {
            if cfg.zero_copy {
                warn!("uring: zero-copy needs buffer pools, serving without it");
            }
            None
        };

        // Build one worker per entry set, cloning the fuse fd up front so
        // cloning failures are reported before any thread is spawned.
        let abort = Arc::new(ConnectionAbort::new(session.mountpoint()));
        let nr_rounds = spread.iter().flatten().map(|&(_, round)| round + 1).max();
        let rounds = Arc::new(RegisterRounds::new(workers, nr_rounds.unwrap_or(1)));
        let mut worker_list = Vec::with_capacity(workers);
        for entries in spread {
            worker_list.push(UringWorker {
                fd: file
                    .try_clone()
                    .map_err(|e| SessionFailure(format!("uring: dup fuse fd: {e}")))?,
                entries,
                payload_cap,
                pools: pools.clone(),
                // Zero-copy comes only with buffer pools.
                bounce: match pools.as_ref().filter(|_| zero_copy) {
                    Some(pools) => Some(BounceBuf::new(pools.buf_size).map_err(|e| {
                        SessionFailure(format!("uring: creating the zero-copy memory file: {e}"))
                    })?),
                    None => None,
                },
                rounds: rounds.clone(),
                server: server.clone(),
                abort: abort.clone(),
            });
        }

        let mut set = WorkerSet::new();
        let exit = set.exit_flag();
        let tracker = set.tracker();
        let (ready_tx, ready_rx) = channel();
        for (id, worker) in worker_list.into_iter().enumerate() {
            let handle = thread::Builder::new().name(format!("uring-{id}")).spawn({
                let exit = exit.clone();
                let tracker = tracker.clone();
                let ready_tx = ready_tx.clone();
                move || {
                    // Report the thread exit to the serving layer's wait().
                    let _exited = tracker.exit_guard();
                    // Registration failures are reported through
                    // ready_tx; the return value only carries the error
                    // out of the thread, which nobody reads.
                    let _ = run(worker, exit, ready_tx);
                }
            });
            match handle {
                Ok(handle) => set.push(handle),
                Err(e) => {
                    // Release the workers already waiting for this one in
                    // the registration rounds, or stop() can't join them.
                    rounds.fail();
                    set.stop(&mut session, true);
                    return Err(SessionFailure(format!("uring: spawn worker {id}: {e}")));
                }
            }
        }
        drop(ready_tx);

        // Wait until all entries are registered, bailing out on the first
        // worker failure (e.g. the fuse module parameter disabled uring).
        for _ in 0..workers {
            match ready_rx.recv() {
                Ok(Ok(())) => {}
                Ok(Err(e)) => {
                    set.stop(&mut session, true);
                    return Err(SessionFailure(format!(
                        "uring: entry registration failed: {e}"
                    )));
                }
                Err(_) => {
                    set.stop(&mut session, true);
                    return Err(SessionFailure(
                        "uring: worker exited during registration".to_string(),
                    ));
                }
            }
        }

        let fallback = match fallback(&mut session, server, exit.clone()) {
            Ok(body) => body,
            Err(e) => {
                set.stop(&mut session, true);
                return Err(e);
            }
        };
        let (fallback_tx, fallback_rx) = channel();
        let fallback = match thread::Builder::new()
            .name("uring-fallback".to_string())
            .spawn({
                let tracker = tracker.clone();
                move || {
                    let _exited = tracker.exit_guard();
                    fallback(fallback_tx)
                }
            }) {
            Ok(handle) => handle,
            Err(e) => {
                set.stop(&mut session, true);
                return Err(SessionFailure(format!("uring: spawn fallback thread: {e}")));
            }
        };
        set.push(fallback);
        // A fallback thread that panicked while starting, for example while
        // creating its async runtime, dropped the sender without sending.
        if fallback_rx.recv().is_err() {
            set.stop(&mut session, true);
            return Err(SessionFailure(
                "uring: fallback thread exited during startup".to_string(),
            ));
        }

        Ok(UringFuseServing {
            session,
            workers: set,
            #[cfg(test)]
            pool_bufs: if pools.is_some() { bufs_per_queue } else { 0 },
            #[cfg(test)]
            zero_copy,
            _fs: std::marker::PhantomData,
        })
    }

    /// Serve the requests that come through `/dev/fuse` with the synchronous
    /// handlers.
    fn fallback_sync(
        session: &mut FuseSession,
        server: Arc<Server<F>>,
        exit: Arc<AtomicBool>,
    ) -> Result<Box<dyn FnOnce(Sender<()>) + Send>> {
        let ch = session.new_channel()?;
        Ok(Box::new(move |ready| {
            let _ = ready.send(());
            Self::fallback_loop(ch, server, exit)
        }))
    }

    fn fallback_loop(mut ch: FuseChannel, server: Arc<Server<F>>, exit: Arc<AtomicBool>) {
        loop {
            match ch.get_request() {
                Ok(Some((reader, writer))) => {
                    if let Err(e) = server.handle_message(reader, writer, None, None) {
                        match e {
                            // The kernel has shut down this session.
                            fuse_backend_core::Error::EncodeMessage(ref err)
                                if err.raw_os_error() == Some(libc::EBADF) =>
                            {
                                break
                            }
                            _ => {
                                warn!("uring fallback: failed to handle message: {e}");
                                continue;
                            }
                        }
                    }
                }
                Ok(None) => break,
                Err(_) => break,
            }
            if exit.load(Ordering::Relaxed) {
                break;
            }
        }
    }
}

#[cfg(feature = "async-io")]
impl<F: AsyncFileSystem + Send + Sync + 'static> UringFuseServing<F> {
    /// Create an io_uring serving transport that serves requests with the
    /// asynchronous handlers of `F`.
    ///
    /// This works like [`Self::new()`], but every worker runs an async
    /// runtime from `async_runtime::Runtime::new()` and serves each request
    /// in its own future, up to one per ring entry it registered. So a
    /// handler that waits, for example on a remote store, doesn't hold up
    /// the worker's other requests. `UringConfig::entries_per_queue` bounds
    /// how many requests sent from one CPU can wait at the same time, so
    /// set it higher than for synchronous handlers.
    ///
    /// The requests that the kernel sends through `/dev/fuse`, such as
    /// INTERRUPT and the ones it queued before the workers registered their
    /// entries, go to a `FuseDevTask`, which also uses the asynchronous
    /// handlers. A stopping worker waits up to 10 seconds for its handlers
    /// to finish, and leaks the requests of the ones that don't. A leaked
    /// request keeps the buffer pools mapped, and so does a request whose
    /// handler panics.
    ///
    /// A request keeps its payload buffer while its handler waits, so a
    /// queue's buffer pool gets `entries_per_queue` buffers, whatever
    /// non-zero `bufs_per_queue` says. `docs/fuse-uring-performance.md` has
    /// the numbers. A `bufs_per_queue` of 0 still gives every entry a buffer
    /// of its own. The workers serve without zero-copy.
    pub fn new_async(
        session: FuseSession,
        server: Arc<Server<F>>,
        mut cfg: UringConfig,
    ) -> Result<UringFuseServing<F>> {
        // The async workers can't move zero-copy data yet.
        if cfg.zero_copy {
            warn!("uring: the async workers can't serve zero-copy, serving without it");
            cfg.zero_copy = false;
        }
        if cfg.bufs_per_queue > 0 {
            // start() counts 0 entries as 1.
            cfg.bufs_per_queue = cfg.entries_per_queue.max(1);
        }
        Self::start(
            session,
            server,
            cfg,
            UringWorker::run_async,
            Self::fallback_async,
        )
    }

    /// Serve the requests that come through `/dev/fuse` with the asynchronous
    /// handlers, on a `FuseDevTask` with a file description of its own.
    fn fallback_async(
        session: &mut FuseSession,
        server: Arc<Server<F>>,
        exit: Arc<AtomicBool>,
    ) -> Result<Box<dyn FnOnce(Sender<()>) + Send>> {
        let file = session.clone_fuse_file()?;
        let buf_size = session.bufsize();
        Ok(Box::new(move |ready| {
            let runtime = Runtime::new();
            let mut task = FuseDevTask::new(buf_size, file, server, exit);
            let _ = ready.send(());
            runtime.block_on(task.poll_handler());
        }))
    }
}

impl<F: FileSystem + Send + Sync + 'static> Drop for UringFuseServing<F> {
    fn drop(&mut self) {
        // Tearing down the connection completes all outstanding ring entries
        // with an error, which unblocks the worker threads; the fallback
        // thread is woken through its epoll channel.
        self.workers.stop(&mut self.session, true);
    }
}

impl<F: FileSystem + Send + Sync + 'static> FuseServing for UringFuseServing<F> {
    fn session(&self) -> &FuseSession {
        &self.session
    }

    fn wait(&self) {
        self.workers.wait();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use vmm_sys_util::tempdir::TempDir;

    use fuse_backend_core::abi::fuse_abi::{
        AccessIn, AttrOut, BatchForgetIn, BmapIn, CopyFileRangeIn, CreateIn, EntryOut, FallocateIn,
        FlushIn, ForgetIn, FsyncIn, GetattrIn, GetxattrIn, InHeader, InitIn, InterruptIn, IoctlIn,
        LinkIn, LkIn, LseekIn, MkdirIn, MknodIn, Opcode, OpenIn, OutHeader, PollIn, ReadIn,
        ReleaseIn, Rename2In, RenameIn, SetattrIn, SetxattrIn, WriteIn, ROOT_ID,
    };
    use fuse_backend_core::api::filesystem::FsOptions;
    use fuse_backend_passthrough::{Config, PassthroughFs};

    #[test]
    fn test_uring_available() {
        // The answer must match the transport the mount actually gets.
        let src = TempDir::new().unwrap();
        let mnt = TempDir::new().unwrap();
        let server = passthrough_server(src.as_path(), false);
        server.set_uring(true);
        let mut se = FuseSession::new(mnt.as_path(), "uring_available_test", "", false).unwrap();
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({e}), skipping");
            return;
        }
        let cfg = UringConfig {
            workers: 1,
            entries_per_queue: 1,
            bufs_per_queue: 0,
            zero_copy: false,
        };
        let r = UringFuseServing::new(se, server, cfg);
        if uring_available() {
            if let Err(e) = r {
                panic!("uring_available() said yes, but the mount got {}", e);
            }
        } else {
            assert!(
                r.is_err(),
                "uring_available() said no, but the mount got the transport"
            );
        }
    }

    #[test]
    fn test_parse_cpu_mask() {
        assert_eq!(parse_cpu_mask("0").unwrap(), 1);
        assert_eq!(parse_cpu_mask("0-3\n").unwrap(), 4);
        assert_eq!(parse_cpu_mask("0-3,5,8-11").unwrap(), 9);
        assert!(parse_cpu_mask("").is_err());
        assert!(parse_cpu_mask("3-1").is_err());
        assert!(parse_cpu_mask("a-b").is_err());
        assert!(parse_cpu_mask("1-2-3").is_err());
        assert!(possible_cpu_count().unwrap() >= 1);
    }

    #[test]
    fn test_spread_entries() {
        use std::collections::HashSet;

        let cases = [
            (24, 16, 4, 4),
            (24, 4, 24, 4),
            (4, 2, 3, 1),
            (1, 1, 8, 0),
            (24, 5, 4, 2),
            (96, 4, 8, 4),
            (96, 16, 8, 4),
            (96, 16, 12, 4),
            (96, 4, 96, 4),
            (4, 3, 1, 3),
        ];
        for (queues, per_queue, workers, bufs) in cases {
            let spread = spread_entries(queues, per_queue, workers, bufs);
            assert_eq!(spread.len(), workers.min(queues * per_queue));
            let workers = spread.len();
            let k = per_queue.min(workers);
            let holders = bufs.clamp(1, k);
            let mut by_queue = vec![Vec::new(); queues];
            for (w, q) in spread.iter().enumerate() {
                for &(qid, round) in q {
                    by_queue[qid as usize].push((round, w));
                }
            }
            for (qid, by_round) in by_queue.iter_mut().enumerate() {
                by_round.sort();
                assert_eq!(by_round.len(), per_queue, "queue {qid}");
                // The last k entries of a queue take a round each, after the
                // others, on k different workers, which are all the
                // queue's workers.
                let (rest, last) = by_round.split_at(per_queue - k);
                assert!(last.windows(2).all(|w| w[0].0 < w[1].0), "queue {}", qid);
                assert!(rest.iter().all(|&(r, _)| r == 0 && r < last[0].0));
                let owners: HashSet<usize> = last.iter().map(|&(_, w)| w).collect();
                assert_eq!(owners.len(), k, "queue {qid}");
                // A queue with an entry on every worker ends on the one that
                // would own it with whole queues.
                if k == workers {
                    assert_eq!(last[k - 1].1, qid % workers, "queue {qid}");
                }
            }
            // Queues 0 to workers - 1 end their registration on different
            // workers, and so do the next workers queues and so on.
            let tops: Vec<usize> = by_queue.iter().map(|q| q.last().unwrap().1).collect();
            for chunk in tops.chunks(workers) {
                assert_eq!(chunk.iter().collect::<HashSet<_>>().len(), chunk.len());
            }
            // Queues workers apart give their other buffers to different
            // workers, so enough of them hold buffers on all k workers.
            if k == workers && holders > 1 {
                let span = (k - 1).div_ceil(holders - 1).saturating_sub(1) * workers;
                for qid in 0..queues.saturating_sub(span) {
                    let held: HashSet<usize> = (qid..=qid + span)
                        .step_by(workers)
                        .flat_map(|q| by_queue[q][per_queue - holders..].iter().map(|&(_, w)| w))
                        .collect();
                    assert_eq!(held.len(), k, "queue {qid}");
                }
            }
            // The workers get the same number of entries, give or take one.
            let sizes: Vec<usize> = spread.iter().map(Vec::len).collect();
            assert!(sizes.iter().max().unwrap() - sizes.iter().min().unwrap() <= 1);
        }
        // Zero workers count as 1.
        assert_eq!(spread_entries(2, 1, 0, 0), vec![vec![(0, 0), (1, 0)]]);
    }

    #[test]
    fn test_register_rounds() {
        let rounds = Arc::new(RegisterRounds::new(3, 2));
        let done: Vec<_> = (0..3)
            .map(|_| {
                let rounds = rounds.clone();
                std::thread::spawn(move || (0..2).all(|_| rounds.wait()))
            })
            .collect();
        assert!(done.into_iter().all(|t| t.join().unwrap()));

        // A failed worker releases the others from their round.
        let rounds = Arc::new(RegisterRounds::new(2, 1));
        let waiter = std::thread::spawn({
            let rounds = rounds.clone();
            move || rounds.wait()
        });
        drop(RoundsGuard(&rounds));
        assert!(!waiter.join().unwrap());
    }

    #[test]
    fn test_op_args() {
        // Per-opcode argument sizes, derived from the *In structures of the
        // fuse ABI (which mirror the kernel's first in_arg per opcode) and
        // from the server-side request decoders.
        let expected: &[(u32, usize)] = &[
            (Opcode::Lookup as u32, 0),
            (Opcode::Forget as u32, std::mem::size_of::<ForgetIn>()),
            (Opcode::Getattr as u32, std::mem::size_of::<GetattrIn>()),
            (Opcode::Setattr as u32, std::mem::size_of::<SetattrIn>()),
            (Opcode::Readlink as u32, 0),
            (Opcode::Symlink as u32, 0),
            (Opcode::Mknod as u32, std::mem::size_of::<MknodIn>()),
            (Opcode::Mkdir as u32, std::mem::size_of::<MkdirIn>()),
            (Opcode::Unlink as u32, 0),
            (Opcode::Rmdir as u32, 0),
            (Opcode::Rename as u32, std::mem::size_of::<RenameIn>()),
            (Opcode::Link as u32, std::mem::size_of::<LinkIn>()),
            (Opcode::Open as u32, std::mem::size_of::<OpenIn>()),
            (Opcode::Read as u32, std::mem::size_of::<ReadIn>()),
            (Opcode::Write as u32, std::mem::size_of::<WriteIn>()),
            (Opcode::Statfs as u32, 0),
            (Opcode::Release as u32, std::mem::size_of::<ReleaseIn>()),
            (Opcode::Fsync as u32, std::mem::size_of::<FsyncIn>()),
            (Opcode::Setxattr as u32, std::mem::size_of::<SetxattrIn>()),
            (Opcode::Getxattr as u32, std::mem::size_of::<GetxattrIn>()),
            (Opcode::Listxattr as u32, std::mem::size_of::<GetxattrIn>()),
            (Opcode::Removexattr as u32, 0),
            (Opcode::Flush as u32, std::mem::size_of::<FlushIn>()),
            (Opcode::Init as u32, std::mem::size_of::<InitIn>()),
            (Opcode::Opendir as u32, std::mem::size_of::<OpenIn>()),
            (Opcode::Readdir as u32, std::mem::size_of::<ReadIn>()),
            (Opcode::Releasedir as u32, std::mem::size_of::<ReleaseIn>()),
            (Opcode::Fsyncdir as u32, std::mem::size_of::<FsyncIn>()),
            (Opcode::Getlk as u32, std::mem::size_of::<LkIn>()),
            (Opcode::Setlk as u32, std::mem::size_of::<LkIn>()),
            (Opcode::Setlkw as u32, std::mem::size_of::<LkIn>()),
            (Opcode::Access as u32, std::mem::size_of::<AccessIn>()),
            (Opcode::Create as u32, std::mem::size_of::<CreateIn>()),
            (Opcode::Interrupt as u32, std::mem::size_of::<InterruptIn>()),
            (Opcode::Bmap as u32, std::mem::size_of::<BmapIn>()),
            (Opcode::Destroy as u32, 0),
            (Opcode::Ioctl as u32, std::mem::size_of::<IoctlIn>()),
            (Opcode::Poll as u32, std::mem::size_of::<PollIn>()),
            (Opcode::NotifyReply as u32, 0),
            (
                Opcode::BatchForget as u32,
                std::mem::size_of::<BatchForgetIn>(),
            ),
            (Opcode::Fallocate as u32, std::mem::size_of::<FallocateIn>()),
            (Opcode::Readdirplus as u32, std::mem::size_of::<ReadIn>()),
            (Opcode::Rename2 as u32, std::mem::size_of::<Rename2In>()),
            (Opcode::Lseek as u32, std::mem::size_of::<LseekIn>()),
            (
                Opcode::CopyFileRange as u32,
                std::mem::size_of::<CopyFileRangeIn>(),
            ),
        ];
        for &(op, len) in expected {
            assert_eq!(op_args(op).map(|a| a.0), Some(len), "opcode {}", op);
        }
        // Everything else (holes, virtiofs-only and newer opcodes) isn't in
        // the table.
        for op in 0..=64u32 {
            if !expected.iter().any(|&(e, _)| e == op) {
                assert_eq!(op_args(op), None, "opcode {}", op);
            }
        }
        assert_eq!(op_args(u32::MAX), None);
        // The requests without out arguments, which take no reply body.
        let no_out_args = [
            Opcode::Forget,
            Opcode::Unlink,
            Opcode::Rmdir,
            Opcode::Rename,
            Opcode::Release,
            Opcode::Fsync,
            Opcode::Setxattr,
            Opcode::Removexattr,
            Opcode::Flush,
            Opcode::Releasedir,
            Opcode::Fsyncdir,
            Opcode::Setlk,
            Opcode::Setlkw,
            Opcode::Access,
            Opcode::Interrupt,
            Opcode::Destroy,
            Opcode::NotifyReply,
            Opcode::BatchForget,
            Opcode::Fallocate,
            Opcode::Rename2,
        ];
        for &(op, _) in expected {
            let has_out_args = !no_out_args.iter().any(|&o| o as u32 == op);
            assert_eq!(op_args(op).unwrap().1, has_out_args, "opcode {}", op);
        }
    }

    #[test]
    fn test_uring_entry_layout() {
        let payload_cap = 4096;
        let entry = UringEntry::new(3, Payload::Own(payload_cap));
        assert_eq!(entry.qid, 3);

        let header_len = std::mem::size_of::<FuseUringReqHeader>();
        let total = header_len + payload_cap + REQ_SCRATCH_SIZE;
        assert_eq!(entry.mem.len(), total);

        // The iovec array must describe the header and payload areas of the
        // same allocation, at stable addresses.
        let base = entry.mem.as_ptr() as usize;
        assert_eq!(entry.iovecs[0].iov_base as usize, base);
        assert_eq!(entry.iovecs[0].iov_len, header_len);
        assert_eq!(entry.iovecs[1].iov_base as usize, base + header_len);
        assert_eq!(entry.iovecs[1].iov_len, payload_cap);

        // All slots of the header must be reachable through the pointers.
        assert_eq!(entry.header().ring_ent_in_out.payload_sz, 0);
    }

    /// The SQE128 of a uring command, built field by field at the offsets of
    /// `struct io_uring_sqe` in include/uapi/linux/io_uring.h, with the
    /// 80-byte command area at offset 48.
    fn uapi_cmd_sqe(
        fd: i32,
        cmd_op: u32,
        flags: u8,
        addr: u64,
        len: u32,
        user_data: u64,
        req: &FuseUringCmdReq,
    ) -> [u8; 128] {
        let mut sqe = [0u8; 128];
        sqe[0] = 46; // IORING_OP_URING_CMD
        sqe[1] = flags;
        sqe[4..8].copy_from_slice(&fd.to_ne_bytes());
        sqe[8..12].copy_from_slice(&cmd_op.to_ne_bytes());
        sqe[16..24].copy_from_slice(&addr.to_ne_bytes());
        sqe[24..28].copy_from_slice(&len.to_ne_bytes());
        sqe[32..40].copy_from_slice(&user_data.to_ne_bytes());
        sqe[48..48 + std::mem::size_of::<FuseUringCmdReq>()].copy_from_slice(req.as_slice());
        sqe
    }

    #[test]
    fn test_cmd_sqe() {
        // Safe because Entry128 is a repr(C) SQE128 of integers, without
        // padding, and io-uring builds it zeroed, so all 128 bytes are
        // initialized.
        let bytes = |sqe: squeue::Entry128| unsafe {
            std::mem::transmute::<squeue::Entry128, [u8; 128]>(sqe)
        };
        let fd = 42;

        // A setup command, as add_bufpools() builds it.
        let add_queue = FuseUringCmdReq {
            qid: 3,
            ..Default::default()
        };
        let sqe = cmd_sqe(fd, FUSE_IO_URING_CMD_ADD_QUEUE, &add_queue, None)
            .flags(squeue::Flags::IO_LINK)
            .user_data(3);
        let link = squeue::Flags::IO_LINK.bits();
        let expected = uapi_cmd_sqe(fd, FUSE_IO_URING_CMD_ADD_QUEUE, link, 0, 0, 3, &add_queue);
        assert_eq!(bytes(sqe), expected);

        // The entry commands, which also carry the entry's iovec array.
        let entry = UringEntry::new(7, Payload::Own(64));
        let iovecs = entry.iovecs.as_ptr() as u64;
        let segs = FUSE_URING_IOV_SEGS as u32;
        for (cmd_op, commit_id, user_data) in [
            (FUSE_IO_URING_CMD_REGISTER, 0, 5),
            (FUSE_IO_URING_CMD_COMMIT_AND_FETCH, 0xdead_beef, 6),
        ] {
            let sqe = entry.cmd_sqe(fd, cmd_op, commit_id, user_data);
            let req = FuseUringCmdReq {
                qid: 7,
                commit_id,
                ..Default::default()
            };
            let expected = uapi_cmd_sqe(fd, cmd_op, 0, iovecs, segs, user_data, &req);
            assert_eq!(bytes(sqe), expected, "cmd_op {cmd_op}");
        }
    }

    #[test]
    fn test_uring_writer_scatter_basic() {
        // Header slot: 16 bytes (OUT_HEADER_SIZE); body slot: 128 bytes.
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 128];

        {
            let mut w = UringWriter::<'_, ()>::new(&mut hdr, &mut body);
            assert_eq!(w.bytes_written(), 0);
            assert_eq!(w.available_bytes(), OUT_HEADER_SIZE + 128);

            // First 16 bytes must land in the header slot.
            w.write_all(&[0xAA; OUT_HEADER_SIZE]).unwrap();
            assert_eq!(w.bytes_written(), OUT_HEADER_SIZE);

            // Next bytes must spill into the body slot.
            w.write_all(&[1u8, 2, 3]).unwrap();
            assert_eq!(w.bytes_written(), OUT_HEADER_SIZE + 3);

            // Writes beyond the available capacity must fail.
            let big = vec![0u8; 200];
            assert!(w.write(&big).is_err());
            assert_eq!(w.bytes_written(), OUT_HEADER_SIZE + 3);
        }

        assert_eq!(&hdr[..], &[0xAA; OUT_HEADER_SIZE]);
        assert_eq!(&body[..3], &[1, 2, 3]);
    }

    #[test]
    fn test_uring_writer_scatter_single_write() {
        // A single write() that straddles the header/body boundary.
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 64];

        {
            let mut w = UringWriter::<'_, ()>::new(&mut hdr, &mut body);
            let data: Vec<u8> = (0..48).collect();
            w.write_all(&data).unwrap();
            assert_eq!(w.bytes_written(), 48);
        }

        // First 16 bytes → header
        assert_eq!(&hdr[..], &(0..16).collect::<Vec<u8>>()[..]);
        // Remaining 32 bytes → body
        assert_eq!(&body[..32], &(16..48).collect::<Vec<u8>>()[..]);
    }

    #[test]
    fn test_uring_writer_scatter_commit() {
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 64];
        let mut w = UringWriter::<'_, ()>::new(&mut hdr, &mut body);
        w.write_all(&[1u8; OUT_HEADER_SIZE]).unwrap();
        w.write_all(&[2u8; 32]).unwrap();
        assert_eq!(w.bytes_written(), OUT_HEADER_SIZE + 32);

        // commit() accounts the staged bytes without touching a device.
        assert_eq!(w.commit(None).unwrap(), OUT_HEADER_SIZE + 32);
    }

    #[test]
    fn test_uring_writer_scatter_write_from_at() {
        let dir = TempDir::new().unwrap();
        let path = dir.as_path().join("data");
        std::fs::write(&path, (0..64).collect::<Vec<u8>>()).unwrap();

        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 32];

        {
            let mut w = UringWriter::<'_, ()>::new(&mut hdr, &mut body);

            // Write the header first so write_from_at lands in the body region.
            w.write_all(&[0xFF; OUT_HEADER_SIZE]).unwrap();

            let file = File::open(&path).unwrap();
            assert_eq!(
                w.write_from_at(file.try_clone().unwrap(), 16, 8).unwrap(),
                16
            );
            assert_eq!(w.bytes_written(), OUT_HEADER_SIZE + 16);

            // More data than available body space must be rejected.
            assert!(w.write_from_at(file, 32, 0).is_err());
        }

        // Body should contain file data starting at offset 8.
        assert_eq!(&body[..16], &(8..24).collect::<Vec<u8>>()[..]);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn test_uring_writer_async() {
        use fuse_backend_core::async_file::File as AsyncFile;
        use fuse_backend_core::async_runtime;

        let dir = TempDir::new().unwrap();
        let path = dir.as_path().join("data");
        std::fs::write(&path, (0..64).collect::<Vec<u8>>()).unwrap();

        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 32];
        {
            let mut w = UringWriter::<'_, ()>::new(&mut hdr, &mut body);
            async_runtime::block_on(async {
                // Writes fill the header slot first and spill into the body,
                // like the synchronous writes do.
                w.async_write_all(&[0xFF; OUT_HEADER_SIZE + 1])
                    .await
                    .unwrap();
                assert_eq!(w.async_write2(&[1], &[2]).await.unwrap(), 2);

                let file = AsyncFile::async_open(&path, false, false).await.unwrap();
                // Read through the trait with an unsized file, as the async
                // server does.
                let src: &dyn AsyncFileReadWriteVolatile = &file;
                assert_eq!(
                    Writer::async_write_from_at(&mut w, src, 16, 8)
                        .await
                        .unwrap(),
                    16
                );
                assert_eq!(w.async_commit(None).await.unwrap(), OUT_HEADER_SIZE + 19);
                // The writer rejects more data than the body has left.
                assert!(w.async_write_from_at(&file, 16, 0).await.is_err());
            });
        }

        assert_eq!(&hdr[..], &[0xFF; OUT_HEADER_SIZE]);
        assert_eq!(&body[..3], &[0xFF, 1, 2]);
        assert_eq!(&body[3..19], &(8..24).collect::<Vec<u8>>()[..]);
    }

    /// The constructor a mount test serves with, `UringFuseServing::new()`
    /// or `UringFuseServing::new_async()`.
    type StartFn<F> = fn(FuseSession, Arc<Server<F>>, UringConfig) -> Result<UringFuseServing<F>>;

    /// Mount at `mnt` and serve `server` over io_uring, or return None if
    /// the kernel rejects FUSE-over-io_uring.
    fn mount_uring<F: FileSystem + Send + Sync + 'static>(
        server: Arc<Server<F>>,
        mnt: &std::path::Path,
        cfg: UringConfig,
        start: StartFn<F>,
    ) -> Option<UringFuseServing<F>> {
        server.set_uring(true);
        let mut se = FuseSession::new(mnt, "uring_serving_test", "", false).unwrap();
        se.mount().unwrap();
        match start(se, server, cfg) {
            Ok(serving) => Some(serving),
            Err(UringNotSupported) => {
                eprintln!("FUSE-over-io_uring is not available, skipping");
                None
            }
            Err(e) => panic!("uring serving failed: {}", e),
        }
    }

    fn passthrough_server(
        src: &std::path::Path,
        zero_copy: bool,
    ) -> Arc<Server<PassthroughFs<()>>> {
        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.to_string_lossy().to_string(),
            do_import: false,
            uring_zero_copy: zero_copy,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        Arc::new(Server::new(fs))
    }

    #[cfg(feature = "async-io")]
    mod barrier_fs {
        /// A root directory in which looking up `wait-<n>` succeeds once
        /// `barrier` has as many lookups waiting as it was created for.
        pub(super) struct BarrierFs {
            pub(super) barrier: tokio::sync::Barrier,
        }

        use std::ffi::CStr;
        use std::io;
        use std::time::Duration;

        use async_trait::async_trait;
        use fuse_backend_core::abi::fuse_abi::{stat64, FsOptions, ROOT_ID};
        use fuse_backend_core::api::filesystem::{AsyncFileSystem, Context, Entry, FileSystem};

        pub(super) fn stat(inode: u64) -> stat64 {
            // Safe because stat64 is plain data.
            let mut st: stat64 = unsafe { std::mem::zeroed() };
            st.st_ino = inode;
            st.st_nlink = 1;
            st.st_mode = if inode == ROOT_ID {
                libc::S_IFDIR | 0o755
            } else {
                libc::S_IFREG | 0o444
            };
            st
        }

        impl FileSystem for BarrierFs {
            type Inode = u64;
            type Handle = u64;

            fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
                // Without PARALLEL_DIROPS, the kernel serializes lookups in a
                // directory.
                Ok(capable & FsOptions::PARALLEL_DIROPS)
            }
        }

        #[allow(unused_variables)]
        #[async_trait]
        impl AsyncFileSystem for BarrierFs {
            async fn async_lookup(
                &self,
                ctx: &Context,
                parent: u64,
                name: &CStr,
            ) -> io::Result<Entry> {
                let name = name.to_str().unwrap_or_default();
                let Some(n) = name
                    .strip_prefix("wait-")
                    .and_then(|n| n.parse::<u64>().ok())
                else {
                    return Err(io::Error::from_raw_os_error(libc::ENOENT));
                };
                self.barrier.wait().await;
                Ok(Entry {
                    inode: ROOT_ID + 1 + n,
                    generation: 0,
                    attr: stat(ROOT_ID + 1 + n),
                    attr_flags: 0,
                    attr_timeout: Duration::ZERO,
                    entry_timeout: Duration::ZERO,
                })
            }

            async fn async_getattr(
                &self,
                ctx: &Context,
                inode: u64,
                handle: Option<u64>,
            ) -> io::Result<(stat64, Duration)> {
                Ok((stat(inode), Duration::ZERO))
            }
        }
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn test_uring_async_serving_overlaps_requests() {
        use barrier_fs::BarrierFs;

        const LOOKUPS: usize = 4;
        let mnt = TempDir::new().unwrap();
        let server = Arc::new(Server::new(BarrierFs {
            barrier: tokio::sync::Barrier::new(LOOKUPS),
        }));
        // One worker, with room for all lookups even if they come from the
        // same CPU. Serving them one at a time would never pass the barrier.
        let cfg = UringConfig {
            workers: 1,
            entries_per_queue: LOOKUPS,
            ..Default::default()
        };
        let Some(serving) = mount_uring(server, mnt.as_path(), cfg, UringFuseServing::new_async)
        else {
            return;
        };

        let (tx, rx) = channel();
        for n in 0..LOOKUPS {
            let path = mnt.as_path().join(format!("wait-{n}"));
            let tx = tx.clone();
            thread::spawn(move || {
                tx.send(
                    std::fs::metadata(path)
                        .map(|_| ())
                        .map_err(|e| e.to_string()),
                )
                .unwrap()
            });
        }
        for _ in 0..LOOKUPS {
            assert_eq!(rx.recv_timeout(Duration::from_secs(10)), Ok(Ok(())));
        }
        drop(serving);
    }

    #[cfg(feature = "async-io")]
    mod slow_lookup_fs {
        /// A root directory whose attributes don't stay cached, so each stat
        /// is a request. Every lookup fails. A lookup of `slow` first waits
        /// for a 1 ms tokio timer and opens `/dev/null`, which tokio-uring
        /// does with io_uring.
        pub(super) struct SlowLookupFs;

        use std::ffi::CStr;
        use std::io;
        use std::time::Duration;

        use async_trait::async_trait;
        use fuse_backend_core::abi::fuse_abi::stat64;
        use fuse_backend_core::api::filesystem::{AsyncFileSystem, Context, Entry, FileSystem};
        use fuse_backend_core::async_file::File as AsyncFile;
        use fuse_backend_core::async_runtime;

        impl FileSystem for SlowLookupFs {
            type Inode = u64;
            type Handle = u64;

            fn getattr(
                &self,
                _ctx: &Context,
                inode: u64,
                _handle: Option<u64>,
            ) -> io::Result<(stat64, Duration)> {
                Ok((super::barrier_fs::stat(inode), Duration::ZERO))
            }
        }

        #[async_trait]
        impl AsyncFileSystem for SlowLookupFs {
            async fn async_lookup(
                &self,
                _ctx: &Context,
                _parent: u64,
                name: &CStr,
            ) -> io::Result<Entry> {
                if name.to_bytes() == b"slow" {
                    tokio::time::sleep(Duration::from_millis(1)).await;
                    // A tokio-uring file isn't Send, and the future of a
                    // handler must be, so the open runs in a task.
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
    }

    /// A worker that keeps finding requests still lets its runtime park, so
    /// handlers that wait for a timer or for tokio-uring IO finish.
    #[cfg(feature = "async-io")]
    #[test]
    fn test_uring_async_serving_busy_worker_lets_runtime_park() {
        let mnt = TempDir::new().unwrap();
        let cfg = UringConfig {
            workers: 1,
            ..Default::default()
        };
        let Some(serving) = mount_uring(
            Arc::new(Server::new(slow_lookup_fs::SlowLookupFs)),
            mnt.as_path(),
            cfg,
            UringFuseServing::new_async,
        ) else {
            return;
        };

        // Stats of the root keep the worker finding requests. The kernel
        // runs lookups in one directory one at a time, but not GETATTR.
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
        // An idle worker parks, which lets a stalled probe finish.
        stop.store(true, Ordering::Relaxed);
        for t in load {
            t.join().unwrap();
        }
        probe.join().unwrap();
        drop(serving);

        let took = took.expect("20 lookups that wait for the runtime took over 10s under load");
        eprintln!("20 lookups took {:?} under load", took);
        assert!(
            took < Duration::from_secs(2),
            "20 lookups that wait for the runtime took {:?} under load",
            took
        );
    }

    /// A worker over PassthroughFs, for exercising process() without a
    /// kernel supporting FUSE_URING.
    fn make_worker() -> (UringWorker<Arc<PassthroughFs<()>>>, TempDir) {
        let source = TempDir::new().unwrap();
        let cfg = Config {
            root_dir: source.as_path().to_str().unwrap().to_string(),
            do_import: true,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();

        let worker = UringWorker {
            fd: File::open("/dev/null").unwrap(),
            entries: vec![(0, 0)],
            payload_cap: 4096,
            pools: None,
            bounce: None,
            rounds: Arc::new(RegisterRounds::new(1, 1)),
            server: Arc::new(Server::new(Arc::new(fs))),
            abort: Arc::new(ConnectionAbort {
                path: None,
                done: AtomicBool::new(false),
            }),
        };
        (worker, source)
    }

    /// Plant a request into the entry header/payload areas the way the
    /// kernel does.
    fn plant_request(entry: &mut UringEntry, opcode: u32, args: &[u8], payload: &[u8]) {
        // Safe because getuid/getgid/getpid are always valid.
        let (uid, gid, pid) = unsafe { (libc::getuid(), libc::getgid(), libc::getpid() as u32) };
        let hdr = InHeader {
            len: (IN_HEADER_SIZE + args.len() + payload.len()) as u32,
            opcode,
            unique: 2,
            nodeid: ROOT_ID,
            uid,
            gid,
            pid,
            ..Default::default()
        };

        let header = entry.header_mut();
        header.in_out[..IN_HEADER_SIZE].copy_from_slice(hdr.as_slice());
        header.op_in[..args.len()].copy_from_slice(args);
        let base = entry.mem.as_mut_ptr();
        // Safe because the payload area is a disjoint part of the entry
        // allocation and payload fits into payload_cap.
        unsafe {
            let header_len = std::mem::size_of::<FuseUringReqHeader>();
            std::ptr::copy_nonoverlapping(payload.as_ptr(), base.add(header_len), payload.len());
        }
        entry.header_mut().ring_ent_in_out.payload_sz = payload.len() as u32;
        entry.header_mut().ring_ent_in_out.commit_id = 2;
    }

    /// Serve the request planted in `entry` with `worker`, on a ring of its
    /// own.
    fn process_entry<F: FileSystem + Send + Sync + 'static>(
        worker: &UringWorker<F>,
        entry: &mut UringEntry,
    ) -> Result<()> {
        let mut ring = FuseRing::builder().build(8).unwrap();
        let mut completions = Completions::new(1);
        worker.process(entry, &mut ring, &mut completions)
    }

    fn parse_out_header(entry: &UringEntry) -> OutHeader {
        let mut out = OutHeader::default();
        out.as_mut_slice()
            .copy_from_slice(&entry.header().in_out[..OUT_HEADER_SIZE]);
        out
    }

    #[test]
    fn test_process_getattr() {
        let (worker, _source) = make_worker();
        let mut entry = UringEntry::new(0, Payload::Own(worker.payload_cap));

        let args = GetattrIn::default();
        plant_request(&mut entry, Opcode::Getattr as u32, args.as_slice(), &[]);
        process_entry(&worker, &mut entry).unwrap();

        let out = parse_out_header(&entry);
        assert_eq!(out.error, 0);
        assert_eq!(out.unique, 2);
        // The reply body is staged in the payload area behind the
        // fuse_out_header slot.
        assert_eq!(
            entry.header().ring_ent_in_out.payload_sz as usize,
            std::mem::size_of::<AttrOut>()
        );
        assert_eq!(entry.header().ring_ent_in_out.commit_id, 2);
    }

    #[test]
    fn test_process_lookup_payload_only() {
        let (worker, _source) = make_worker();
        let mut entry = UringEntry::new(0, Payload::Own(worker.payload_cap));

        // LOOKUP carries no fixed arguments, only the name in the payload.
        plant_request(&mut entry, Opcode::Lookup as u32, &[], b"fuse-file\0");
        // Lookup fails with ENOENT on the empty directory, which still
        // exercises the payload reassembly; the reply must be an error.
        process_entry(&worker, &mut entry).unwrap();
        let out = parse_out_header(&entry);
        assert_eq!(out.error, -libc::ENOENT);
        assert_eq!(entry.header().ring_ent_in_out.payload_sz, 0);

        // And succeeds once the file exists.
        std::fs::write(_source.as_path().join("fuse-file"), "x").unwrap();
        plant_request(&mut entry, Opcode::Lookup as u32, &[], b"fuse-file\0");
        process_entry(&worker, &mut entry).unwrap();
        let out = parse_out_header(&entry);
        assert_eq!(out.error, 0);
        assert_eq!(
            entry.header().ring_ent_in_out.payload_sz as usize,
            std::mem::size_of::<EntryOut>()
        );
    }

    #[test]
    fn test_process_malformed_request_gets_einval() {
        let (worker, _source) = make_worker();
        let mut entry = UringEntry::new(0, Payload::Own(worker.payload_cap));

        // A name without its NUL: the server answers EINVAL, and the
        // worker commits that reply instead of its EIO.
        plant_request(&mut entry, Opcode::Lookup as u32, &[], b"fuse-file");
        process_entry(&worker, &mut entry).unwrap();
        let out = parse_out_header(&entry);
        assert_eq!(
            (out.len as usize, out.error),
            (OUT_HEADER_SIZE, -libc::EINVAL)
        );
        assert_eq!(entry.header().ring_ent_in_out.payload_sz, 0);
    }

    #[test]
    fn test_process_unknown_opcode_gets_enosys() {
        /// The STATX opcode, which the transport's table doesn't know.
        const FUSE_STATX: u32 = 52;
        let (worker, _source) = make_worker();
        let mut entry = UringEntry::new(0, Payload::Own(worker.payload_cap));

        // The kernel only falls back to GETATTR after ENOSYS.
        plant_request(&mut entry, FUSE_STATX, &[0u8; 24], &[]);
        process_entry(&worker, &mut entry).unwrap();
        assert_eq!(parse_out_header(&entry).error, -libc::ENOSYS);
        assert_eq!(entry.header().ring_ent_in_out.payload_sz, 0);
    }

    #[test]
    fn test_stage_error_reply_after_rejected_request() {
        let (worker, _source) = make_worker();
        let mut entry = UringEntry::new(0, Payload::Own(worker.payload_cap));

        // Simulate the kernel delivering a request with a payload larger
        // than the entry: process() fails, and the worker must commit a
        // proper error reply rather than echoing the request data back.
        plant_request(
            &mut entry,
            Opcode::Getattr as u32,
            GetattrIn::default().as_slice(),
            &[],
        );
        entry.header_mut().ring_ent_in_out.payload_sz = (worker.payload_cap + 1) as u32;
        assert!(process_entry(&worker, &mut entry).is_err());
        entry.stage_error_reply(libc::EIO);

        let out = parse_out_header(&entry);
        assert_eq!(out.len, OUT_HEADER_SIZE as u32);
        assert_eq!(out.error, -libc::EIO);
        assert_eq!(out.unique, 2);
        assert_eq!(entry.header().ring_ent_in_out.payload_sz, 0);
        // The commit_id delivered by the kernel must be preserved so that
        // COMMIT_AND_FETCH matches the request.
        assert_eq!(entry.header().ring_ent_in_out.commit_id, 2);
    }

    #[test]
    fn test_bufpools_buffer() {
        let pools = BufPools::new(2, 3, 4096).unwrap();
        let base = pools.region.as_ptr();
        // The second buffer of queue 1 sits behind queue 0's three.
        let (ptr, len) = pools.buffer(1, 4096).unwrap();
        assert_eq!(ptr.as_ptr(), base.wrapping_add(4 * 4096));
        assert_eq!(len, 4096);
        assert_eq!(pools.queue_pool(1).uaddr, base as u64 + 3 * 4096);
        assert_eq!(pools.queue_pool(1).len, 3 * 4096);
        // Offsets between buffers or past the pool, and unknown queues.
        assert!(pools.buffer(1, 100).is_err());
        assert!(pools.buffer(1, 3 * 4096).is_err());
        assert!(pools.buffer(2, 0).is_err());
        // A pool must fit the 32-bit length of ADD_BUFPOOL.
        assert!(BufPools::new(1, 4097, 1 << 20).is_err());
    }

    #[test]
    fn test_process_pooled() {
        let (worker, _source) = make_worker();
        let pools = Arc::new(BufPools::new(1, 2, 4096).unwrap());
        let mut entry = UringEntry::new(0, Payload::Pool(pools.clone()));
        // REGISTER must not carry a payload buffer.
        assert!(entry.iovecs[1].iov_base.is_null());
        assert_eq!(entry.iovecs[1].iov_len, 0);

        // The reply body goes into the buffer the kernel lent.
        plant_request(
            &mut entry,
            Opcode::Getattr as u32,
            GetattrIn::default().as_slice(),
            &[],
        );
        entry.header_mut().ring_ent_in_out.offset = 4096;
        process_entry(&worker, &mut entry).unwrap();
        assert_eq!(parse_out_header(&entry).error, 0);
        let body = pools.buffer(0, 4096).unwrap().0.as_ptr();
        let mut attr = AttrOut::default();
        // Safe because the pool's second buffer holds the reply body.
        unsafe {
            std::ptr::copy_nonoverlapping(
                body,
                attr.as_mut_slice().as_mut_ptr(),
                std::mem::size_of::<AttrOut>(),
            )
        };
        assert_eq!(attr.attr.mode & libc::S_IFMT, libc::S_IFDIR);

        // A request without a payload and without a reply body gets no
        // buffer, even though offset 0 names the first one.
        plant_request(&mut entry, Opcode::Fsync as u32, &[0u8; 16], &[]);
        entry.header_mut().ring_ent_in_out.offset = 0;
        assert_eq!(entry.payload_buffer(false, 0).unwrap().1, 0);
        // Offset 0 with a reply body is the first buffer.
        let (ptr, len) = entry.payload_buffer(true, 0).unwrap();
        assert_eq!((ptr, len), pools.buffer(0, 0).unwrap());
    }

    #[test]
    fn test_process_rejects_oversized_reply() {
        let (worker, _source) = make_worker();
        // A payload area too small to hold the GETATTR reply body must be
        // rejected instead of panicking in the staging copy.
        let mut entry = UringEntry::new(0, Payload::Own(8));
        plant_request(
            &mut entry,
            Opcode::Getattr as u32,
            GetattrIn::default().as_slice(),
            &[],
        );
        assert!(process_entry(&worker, &mut entry).is_err());
    }

    /// A zero-copy sink that records what it was asked to read.
    #[derive(Default)]
    struct RecordingSink {
        /// The file reads: position, fd, count and offset.
        reads: std::sync::Mutex<Vec<(usize, RawFd, usize, u64)>>,
        /// The copies from memory: position and data.
        writes: std::sync::Mutex<Vec<(usize, Vec<u8>)>>,
    }

    impl ZeroCopySink for RecordingSink {
        fn read_from_file(
            &self,
            pos: usize,
            fd: RawFd,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            self.reads.lock().unwrap().push((pos, fd, count, off));
            Ok(count)
        }

        fn write_from_memory(&self, pos: usize, data: &[u8]) -> io::Result<()> {
            self.writes.lock().unwrap().push((pos, data.to_vec()));
            Ok(())
        }

        fn fill_from(
            &self,
            pos: usize,
            count: usize,
            fill: &mut dyn FnMut(&mut [u8]) -> io::Result<usize>,
        ) -> io::Result<usize> {
            let mut buf = vec![0u8; count];
            let n = fill(&mut buf)?;
            self.write_from_memory(pos, &buf[..n])?;
            Ok(n)
        }
    }

    #[test]
    fn test_uring_writer_zero_copy() {
        let sink = RecordingSink::default();
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut w = UringWriter::<()>::new(&mut hdr, &mut []).with_zero_copy(&sink, 4096);
        assert_eq!(w.available_bytes(), OUT_HEADER_SIZE + 4096);

        // The server splits off the header first, and the data part keeps
        // the zero-copy reply.
        let mut data = w.split_at(OUT_HEADER_SIZE).unwrap();
        assert_eq!(w.available_bytes(), OUT_HEADER_SIZE);
        assert_eq!(data.available_bytes(), 4096);

        let mut file = File::open("/dev/null").unwrap();
        let fd = file.as_raw_fd();
        assert_eq!(data.write_from_at(&mut file, 1000, 7).unwrap(), 1000);
        assert_eq!(data.write_from_at(&mut file, 96, 1007).unwrap(), 96);
        assert_eq!(
            *sink.reads.lock().unwrap(),
            vec![(0, fd, 1000, 7), (1000, fd, 96, 1007)]
        );
        assert!(data.write_from_at(&mut file, 4000, 0).is_err());
        // Reply data built in memory reaches the client pages through the
        // sink too.
        data.write_all(&[1, 2, 3]).unwrap();
        assert_eq!(*sink.writes.lock().unwrap(), vec![(1096, vec![1, 2, 3])]);

        w.write_all(&[0u8; OUT_HEADER_SIZE]).unwrap();
        assert_eq!(w.commit(Some(&data)).unwrap(), OUT_HEADER_SIZE + 1099);
    }

    #[test]
    fn test_uring_writer_split_at_zero() {
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 256];
        let mut w = UringWriter::<()>::new(&mut hdr, &mut body);

        // split_at(0): self becomes empty, other gets everything.
        let other = w.split_at(0).unwrap();
        assert_eq!(w.available_bytes(), 0);
        assert_eq!(other.available_bytes(), OUT_HEADER_SIZE + 256);
    }

    #[test]
    fn test_uring_writer_split_at_header_size() {
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 256];
        let mut w = UringWriter::<()>::new(&mut hdr, &mut body);

        // split_at(OUT_HEADER_SIZE): self keeps header, other gets body.
        let mut other = w.split_at(OUT_HEADER_SIZE).unwrap();
        assert_eq!(w.available_bytes(), OUT_HEADER_SIZE);
        assert_eq!(other.available_bytes(), 256);

        // Write OutHeader to self (header region).
        let out = OutHeader {
            len: (OUT_HEADER_SIZE + 10) as u32,
            error: 0,
            unique: 42,
        };
        w.write_all(out.as_slice()).unwrap();
        assert_eq!(w.bytes_written(), OUT_HEADER_SIZE);

        // Write data to other (body region).
        other.write_all(&[0xABu8; 10]).unwrap();
        assert_eq!(other.bytes_written(), 10);

        // Commit combines both.
        let total = w.commit(Some(&other)).unwrap();
        assert_eq!(total, OUT_HEADER_SIZE + 10);
    }

    #[test]
    fn test_uring_writer_split_at_beyond_capacity() {
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 64];
        let mut w = UringWriter::<()>::new(&mut hdr, &mut body);

        // split_at beyond total capacity must fail.
        assert!(w.split_at(OUT_HEADER_SIZE + 65).is_err());
    }

    #[test]
    fn test_uring_writer_split_at_body_offset() {
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 256];
        let mut w = UringWriter::<()>::new(&mut hdr, &mut body);

        // split_at beyond header into body region.
        let offset = OUT_HEADER_SIZE + 100;
        let other = w.split_at(offset).unwrap();
        assert_eq!(w.available_bytes(), offset);
        assert_eq!(other.available_bytes(), 256 - 100);
    }

    /// Turn O_DIRECT on for a file the mount opened without it, then write
    /// and read it. With zero-copy, PassthroughFs then reads and writes the
    /// data through its aligned bounce buffer, which zero-copy data reaches
    /// only through a copy in memory. Skipped where the backing file system
    /// lacks O_DIRECT. Returns whether it ran.
    fn check_late_direct_io(src: &std::path::Path, mnt: &std::path::Path) -> bool {
        use std::os::unix::fs::{FileExt, OpenOptionsExt};
        let probe = src.join("direct-probe");
        std::fs::write(&probe, b"").unwrap();
        if std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECT)
            .open(&probe)
            .is_err()
        {
            eprintln!("the backing file system lacks O_DIRECT, skipping");
            return false;
        }

        let f = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .open(mnt.join("late-direct"))
            .unwrap();
        // Safe because fcntl() only reads and sets the flags of the fd.
        let flags = unsafe { libc::fcntl(f.as_raw_fd(), libc::F_GETFL) };
        assert_eq!(
            unsafe { libc::fcntl(f.as_raw_fd(), libc::F_SETFL, flags | libc::O_DIRECT) },
            0
        );
        // O_DIRECT wants aligned memory.
        #[repr(align(4096))]
        struct Aligned([u8; 8192]);
        let mut buf = Box::new(Aligned([0; 8192]));
        let mut back = Box::new(Aligned([0; 8192]));
        let (buf, back) = (&mut buf.0, &mut back.0);
        for (i, b) in buf.iter_mut().enumerate() {
            *b = (i % 251) as u8;
        }
        f.write_all_at(buf, 0).unwrap();
        f.read_exact_at(back, 0).unwrap();
        assert!(buf == back);
        true
    }

    /// Whether this process runs as root in the initial user namespace,
    /// which zero-copy needs.
    fn real_root() -> bool {
        // Safe because geteuid() is always valid.
        let euid = unsafe { libc::geteuid() };
        euid == 0
            && std::fs::read_to_string("/proc/self/uid_map").is_ok_and(|map| {
                map.split_whitespace().collect::<Vec<_>>() == ["0", "0", "4294967295"]
            })
    }

    /// Serve a PassthroughFs over io_uring with `start`, `workers` workers,
    /// 2 entries and `bufs_per_queue` buffers per queue, and zero-copy if
    /// `zero_copy`. Check that a kernel with buffer pools gives each queue
    /// `pool_bufs` buffers, read and write through the mount, then check
    /// that dropping the serving layer gets the ring entries back from the
    /// kernel and unmounts.
    fn check_passthrough_mount(
        start: StartFn<PassthroughFs<()>>,
        workers: usize,
        bufs_per_queue: usize,
        zero_copy: bool,
        pool_bufs: usize,
    ) {
        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"over io_uring").unwrap();
        let mnt = TempDir::new().unwrap();
        let server = passthrough_server(src.as_path(), zero_copy);
        let cfg = UringConfig {
            workers,
            entries_per_queue: 2,
            bufs_per_queue,
            zero_copy,
        };
        let Some(serving) = mount_uring(server.clone(), mnt.as_path(), cfg, start) else {
            return;
        };
        // Kernels with buffer pools must get them when the config asks, and
        // zero-copy too when the test runs as root.
        let pooled = server.uring_bufpool_supported();
        assert_eq!(serving.pool_bufs, if pooled { pool_bufs } else { 0 });
        if serving.pool_bufs > 0 && zero_copy && real_root() {
            assert!(serving.zero_copy);
        }
        eprintln!(
            "uring mount: {workers} workers, {bufs_per_queue} buffers per queue, zero-copy {}",
            serving.zero_copy
        );

        assert_eq!(
            std::fs::read(mnt.as_path().join("hello")).unwrap(),
            b"over io_uring"
        );
        let created = mnt.as_path().join("created");
        std::fs::write(&created, b"written over io_uring").unwrap();
        assert_eq!(std::fs::read(&created).unwrap(), b"written over io_uring");

        // Writes and reads of whole payload buffers, from several threads
        // so that requests wait for buffers when the pools are small.
        std::thread::scope(|scope| {
            for i in 0..4u8 {
                let path = mnt.as_path().join(format!("big-{i}"));
                scope.spawn(move || {
                    let data: Vec<u8> = (0..3 << 20).map(|n: u32| (n as u8) ^ i).collect();
                    let mut f = File::create(&path).unwrap();
                    f.write_all(&data).unwrap();
                    // FSYNC and RELEASE carry no payload and take no body.
                    f.sync_all().unwrap();
                    drop(f);
                    assert!(std::fs::read(&path).unwrap() == data);
                    std::fs::remove_file(&path).unwrap();
                });
            }
        });

        // With zero-copy, the reads and writes above went through it.
        if serving.zero_copy {
            assert!(ZERO_COPY_REQUESTS.load(Ordering::Relaxed) > 0);
        }
        // A late O_DIRECT sends the data of zero-copy requests through
        // memory.
        if check_late_direct_io(src.as_path(), mnt.as_path()) && serving.zero_copy {
            assert!(ZERO_COPY_BOUNCES.load(Ordering::Relaxed) > 0);
        }

        // Tearing the connection down completes the commands of all armed
        // entries, so the workers get their entries back well within
        // RELEASE_TIMEOUT instead of waiting it out and leaking them.
        let start = Instant::now();
        drop(serving);
        assert!(start.elapsed() < RELEASE_TIMEOUT);
        assert!(std::fs::read(mnt.as_path().join("hello")).is_err());
    }

    #[test]
    fn test_uring_serving_mount() {
        for (bufs_per_queue, zero_copy) in
            [(0, false), (1, false), (4, false), (1, true), (4, true)]
        {
            // A pool holds at most as many buffers as the queue has entries.
            let pool_bufs = bufs_per_queue.min(2);
            check_passthrough_mount(
                UringFuseServing::new,
                2,
                bufs_per_queue,
                zero_copy,
                pool_bufs,
            );
        }
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn test_uring_async_serving_mount() {
        // A pool gets a buffer per entry, even when the config asks for 1.
        check_passthrough_mount(UringFuseServing::new_async, 2, 0, false, 0);
        check_passthrough_mount(UringFuseServing::new_async, 2, 1, false, 2);
    }

    /// With more workers than queues, every queue's entries are spread over
    /// several workers.
    #[test]
    fn test_uring_serving_more_workers_than_queues() {
        check_passthrough_mount(
            UringFuseServing::new,
            possible_cpu_count().unwrap() + 1,
            0,
            false,
            0,
        );
    }

    #[test]
    fn test_uring_writer_write_from_at_ignores_header_space() {
        let dir = TempDir::new().unwrap();
        let path = dir.as_path().join("data");
        std::fs::write(&path, [0u8; 64]).unwrap();

        // The header slot is still empty, so the writer has room for 24
        // bytes, but only 8 of them are in the body, where file data goes.
        let mut hdr = vec![0u8; OUT_HEADER_SIZE];
        let mut body = vec![0u8; 8];
        let mut w = UringWriter::<'_, ()>::new(&mut hdr, &mut body);
        assert_eq!(w.available_bytes(), OUT_HEADER_SIZE + 8);
        assert!(w.write_from_at(File::open(&path).unwrap(), 16, 0).is_err());
        assert_eq!(
            w.write_from_at(File::open(&path).unwrap(), 8, 0).unwrap(),
            8
        );
    }

    #[test]
    fn test_mount_minor() {
        let info = "22 1 0:21 / /proc rw - proc proc rw\n\
                    95 30 0:84 / /tmp/a rw - fuse.x x rw\n\
                    96 30 0:86 / /tmp/a rw - fuse.x x rw\n";
        // The last mount at a path is the one in effect.
        assert_eq!(mount_minor(info, "/tmp/a".as_ref()), Some(86));
        assert_eq!(mount_minor(info, "/tmp/b".as_ref()), None);
        // Special characters are octal escapes.
        let info = "97 30 0:88 / /tmp/a\\040b rw - fuse.x x rw\n";
        assert_eq!(mount_minor(info, "/tmp/a b".as_ref()), Some(88));
    }

    /// A file system whose LOOKUP panics.
    struct PanicFs;

    impl FileSystem for PanicFs {
        type Inode = u64;
        type Handle = u64;

        fn lookup(
            &self,
            _ctx: &fuse_backend_core::api::filesystem::Context,
            _parent: u64,
            _name: &std::ffi::CStr,
        ) -> io::Result<fuse_backend_core::api::filesystem::Entry> {
            panic!("LOOKUP panics");
        }

        fn getattr(
            &self,
            _ctx: &fuse_backend_core::api::filesystem::Context,
            inode: u64,
            _handle: Option<u64>,
        ) -> io::Result<(fuse_backend_core::abi::fuse_abi::stat64, Duration)> {
            // Safe because stat64 is plain data.
            let mut st: fuse_backend_core::abi::fuse_abi::stat64 = unsafe { std::mem::zeroed() };
            st.st_ino = inode;
            st.st_nlink = 1;
            st.st_mode = libc::S_IFDIR | 0o755;
            Ok((st, Duration::ZERO))
        }
    }

    // The async defaults call the sync handlers, so LOOKUP panics too.
    #[cfg(feature = "async-io")]
    impl fuse_backend_core::api::filesystem::AsyncFileSystem for PanicFs {}

    /// A worker of `start` whose handler panics ends the connection, so the
    /// request fails instead of waiting forever, and `wait()` returns.
    fn check_handler_panic(start: StartFn<PanicFs>) {
        let mnt = TempDir::new().unwrap();
        let server = Arc::new(Server::new(PanicFs));
        server.set_uring(true);
        let mut se = FuseSession::new(mnt.as_path(), "uring_panic_test", "", false).unwrap();
        se.mount().unwrap();
        if ConnectionAbort::new(se.mountpoint()).path.is_none() {
            eprintln!("fusectl isn't mounted, skipping");
            return;
        }
        let cfg = UringConfig {
            workers: 1,
            entries_per_queue: 1,
            bufs_per_queue: 0,
            zero_copy: false,
        };
        let serving = match start(se, server, cfg) {
            Ok(serving) => Arc::new(serving),
            Err(UringNotSupported) => {
                eprintln!("FUSE-over-io_uring is not available, skipping");
                return;
            }
            Err(e) => panic!("uring serving failed: {}", e),
        };

        let (tx, rx) = channel();
        let path = mnt.as_path().join("panics");
        std::thread::spawn(move || {
            let _ = tx.send(std::fs::metadata(path).is_err());
        });
        assert_eq!(rx.recv_timeout(Duration::from_secs(5)), Ok(true));
        let (tx, rx) = channel();
        let waiting = serving.clone();
        std::thread::spawn(move || {
            waiting.wait();
            let _ = tx.send(());
        });
        rx.recv_timeout(Duration::from_secs(5))
            .expect("the worker didn't end the connection after the panic");
    }

    #[test]
    fn test_uring_serving_handler_panic() {
        check_handler_panic(UringFuseServing::new);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn test_uring_async_serving_handler_panic() {
        check_handler_panic(UringFuseServing::new_async);
    }

    /// Ending the connection, as a failed worker does, stops every worker,
    /// so `wait()` returns instead of serving on with a hanging queue.
    #[test]
    fn test_uring_serving_connection_abort() {
        let src = TempDir::new().unwrap();
        // A mountpoint with a space, which mountinfo escapes.
        let dir = TempDir::new().unwrap();
        let mnt = dir.as_path().join("mount point");
        std::fs::create_dir(&mnt).unwrap();
        let server = passthrough_server(src.as_path(), false);
        server.set_uring(true);
        let mut se = FuseSession::new(mnt.as_path(), "uring_serving_test", "", false).unwrap();
        se.mount().unwrap();
        let abort = ConnectionAbort::new(se.mountpoint());
        if abort.path.is_none() {
            eprintln!("fusectl isn't mounted, skipping");
            return;
        }
        let cfg = UringConfig {
            workers: 2,
            entries_per_queue: 2,
            bufs_per_queue: 0,
            zero_copy: false,
        };
        let serving = match UringFuseServing::new(se, server, cfg) {
            Ok(serving) => Arc::new(serving),
            Err(UringNotSupported) => {
                eprintln!("FUSE-over-io_uring is not available, skipping");
                return;
            }
            Err(e) => panic!("uring serving failed: {}", e),
        };
        std::fs::read_dir(mnt.as_path()).unwrap().for_each(drop);

        abort.abort();
        let (tx, rx) = channel();
        let waiting = serving.clone();
        std::thread::spawn(move || {
            waiting.wait();
            let _ = tx.send(());
        });
        rx.recv_timeout(Duration::from_secs(5))
            .expect("the workers didn't stop after the connection ended");
        assert!(std::fs::read_dir(mnt.as_path()).is_err());
    }
}
