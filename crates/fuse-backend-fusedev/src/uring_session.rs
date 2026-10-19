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
//! route through io_uring (FUSE_INTERRUPT and requests queued before entries
//! were registered), so a classic channel thread keeps serving in parallel.
//!
//! On Linux 7.3 and later, the kernel can take the payload buffers from one
//! buffer pool per queue instead of one buffer per entry. See
//! `UringConfig::bufs_per_queue`.
//!
//! Experimental: the kernel interface is still evolving.

use std::fs::File;
use std::io::{self, IoSlice, Write};
use std::mem::ManuallyDrop;
use std::os::unix::io::{AsRawFd, RawFd};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Sender};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use io_uring::{cqueue, opcode, squeue, types, IoUring};
use vm_memory::ByteValued;

use fuse_backend_core::abi::fuse_abi::{InHeader, OutHeader};
use fuse_backend_core::abi::fuse_uring::{
    FuseUringBufpool, FuseUringCmdReq, FuseUringEntInOut, FuseUringReqHeader,
    FUSE_IO_URING_CMD_ADD_BUFPOOL, FUSE_IO_URING_CMD_ADD_QUEUE, FUSE_IO_URING_CMD_COMMIT_AND_FETCH,
    FUSE_IO_URING_CMD_REGISTER, FUSE_URING_IN_OUT_HEADER_SZ, FUSE_URING_IOV_SEGS,
};
use fuse_backend_core::api::filesystem::FileSystem;
use fuse_backend_core::api::server::Server;
use fuse_backend_core::buffer::{Error::*, Reader, Result, Writer};
use fuse_backend_core::file_buf::FileVolatileSlice;
use fuse_backend_core::file_traits::FileReadWriteVolatile;
use vm_memory::bitmap::BitmapSlice;
use vm_memory::mmap::MmapRegion;

use crate::serving::{FuseServing, WorkerSet};
use crate::{FuseBuf, FuseChannel, FuseDevReaderExt, FuseSession, FUSE_HEADER_SIZE};

/// Size of `fuse_in_header`/`fuse_out_header` on the wire.
const IN_HEADER_SIZE: usize = 40;
const OUT_HEADER_SIZE: usize = 16;

/// Field-for-field mirror of `struct io_uring_sqe`, used to reach the
/// `addr`/`len` fields of an SQE128 which the io-uring crate does not
/// expose for `IORING_OP_URING_CMD` entries.
#[allow(dead_code)]
#[repr(C)]
struct SqeMirror {
    opcode: u8,
    flags: u8,
    ioprio: u16,
    fd: i32,
    off: u64,
    addr: u64,
    len: u32,
    op_flags: u32,
    user_data: u64,
    buf_index: u16,
    personality: u16,
    splice_fd_in: i32,
    addr3: u64,
    pad2: u64,
}

/// Configuration of the io_uring serving transport.
#[derive(Clone, Copy, Debug)]
pub struct UringConfig {
    /// Number of worker threads, each owning one io_uring instance. The
    /// kernel queues are distributed among the workers round-robin.
    /// `0` means one worker per online CPU.
    pub workers: usize,
    /// Number of ring entries registered per kernel queue, i.e. the number
    /// of in-flight requests each queue may hold.
    pub entries_per_queue: usize,
    /// Number of payload buffers in each queue's buffer pool, on kernels
    /// that support buffer pools (Linux 7.3). The kernel lends a buffer to
    /// an entry only while it serves a request that carries a payload or
    /// takes a reply body, and it lends the free buffer with the lowest
    /// address first. A request waits in the kernel while all buffers of its
    /// queue are busy. A pool holds at most `entries_per_queue` buffers,
    /// because each entry holds at most one. `0`, or a kernel without
    /// buffer pools, gives every entry a buffer of its own instead.
    pub bufs_per_queue: usize,
}

impl Default for UringConfig {
    fn default() -> Self {
        UringConfig {
            workers: 0,
            entries_per_queue: 4,
            bufs_per_queue: 4,
        }
    }
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

/// What the transport needs to know about a request with this opcode: the
/// size of the per-opcode arguments carried in the entry `op_in` slot, for
/// reassembling the classic wire layout, and whether the request has out
/// arguments, i.e. takes a reply body. The kernel copies `in_args[0]` (the
/// per-op header) into `op_in` and the remaining arguments into the payload
/// area, so a size of 0 means a known opcode without a fixed header. Over a
/// buffer pool, the kernel lends no buffer to a request without a payload
/// and without out arguments. `None` marks opcodes this table doesn't know.
fn op_args(opcode: u32) -> Option<(usize, bool)> {
    let args = match opcode {
        1 => (0, true),         // LOOKUP: name only
        2 => (8, false),        // FORGET: ForgetIn
        3 => (16, true),        // GETATTR: GetattrIn
        4 => (88, true),        // SETATTR: SetattrIn
        5 => (0, true),         // READLINK: no arguments
        6 => (0, true),         // SYMLINK: name + linkname
        8 => (16, true),        // MKNOD: MknodIn
        9 => (8, true),         // MKDIR: MkdirIn
        10 | 11 => (0, false),  // UNLINK/RMDIR: name only
        12 => (8, false),       // RENAME: RenameIn
        13 => (8, true),        // LINK: LinkIn
        14 => (8, true),        // OPEN: OpenIn
        15 => (40, true),       // READ: ReadIn
        16 => (40, true),       // WRITE: WriteIn
        17 => (0, true),        // STATFS: no arguments
        18 => (24, false),      // RELEASE: ReleaseIn
        20 => (16, false),      // FSYNC: FsyncIn
        21 => (8, false),       // SETXATTR: SetxattrIn
        22 => (8, true),        // GETXATTR: GetxattrIn
        23 => (8, true),        // LISTXATTR: GetxattrIn
        24 => (0, false),       // REMOVEXATTR: name only
        25 => (24, false),      // FLUSH: FlushIn
        26 => (16, true),       // INIT: InitIn
        27 => (8, true),        // OPENDIR: OpenIn
        28 | 44 => (40, true),  // READDIR/READDIRPLUS: ReadIn
        29 => (24, false),      // RELEASEDIR: ReleaseIn
        30 => (16, false),      // FSYNCDIR: FsyncIn
        31 => (48, true),       // GETLK: LkIn
        32 | 33 => (48, false), // SETLK/SETLKW: LkIn
        34 => (8, false),       // ACCESS: AccessIn
        35 => (16, true),       // CREATE: CreateIn
        36 => (8, false),       // INTERRUPT: InterruptIn
        37 => (16, true),       // BMAP: BmapIn
        38 => (0, false),       // DESTROY: no arguments
        39 => (32, true),       // IOCTL: IoctlIn
        40 => (24, true),       // POLL: PollIn
        41 => (0, false),       // NOTIFY_REPLY: payload only
        42 => (8, false),       // BATCH_FORGET: BatchForgetIn
        43 => (32, false),      // FALLOCATE: FallocateIn
        45 => (16, false),      // RENAME2: Rename2In
        46 => (24, true),       // LSEEK: LseekIn
        47 => (56, true),       // COPY_FILE_RANGE: CopyFileRangeIn
        // SETUPMAPPING/REMOVEMAPPING only exist on the virtiofs DAX window
        // path and are never delivered through /dev/fuse, opcodes 0, 7 and
        // 19 are undefined, and request() answers the rest, such as
        // SYNCFS, TMPFILE and STATX, with ENOSYS.
        _ => return None,
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
    phantom: std::marker::PhantomData<&'a mut [S]>,
}

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
            phantom: std::marker::PhantomData,
        }
    }

    /// Split the writer at `offset` bytes of the combined (header + body)
    /// capacity.
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
                phantom: std::marker::PhantomData,
            })
        }
    }

    /// Total bytes written across both regions.
    pub fn bytes_written(&self) -> usize {
        self.header.len() + self.body.len()
    }

    /// Total capacity available across both regions.
    pub fn available_bytes(&self) -> usize {
        (self.header.capacity() - self.header.len()) + (self.body.capacity() - self.body.len())
    }

    /// Account the bytes written by self and an optional split-off partner.
    pub fn commit(&mut self, other: Option<&UringWriter<'a, S>>) -> io::Result<usize> {
        let o = other.map(|w| w.bytes_written()).unwrap_or(0);
        Ok(self.bytes_written() + o)
    }

    fn check_available_space(&self, sz: usize) -> io::Result<()> {
        if sz > self.available_bytes() {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    self.available_bytes(),
                    sz,
                ),
            ))
        } else {
            Ok(())
        }
    }

    /// Write data, routing the first `OUT_HEADER_SIZE` bytes to the header
    /// region and the remainder to the body region.
    fn scatter_write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.check_available_space(data.len())?;
        let hdr_remaining = self.header.capacity() - self.header.len();
        let to_hdr = data.len().min(hdr_remaining);
        if to_hdr > 0 {
            self.header.extend_from_slice(&data[..to_hdr]);
        }
        if to_hdr < data.len() {
            self.body.extend_from_slice(&data[to_hdr..]);
        }
        Ok(data.len())
    }

    /// Stage data read from a file descriptor at offset `off` into the body
    /// region. Must be called after the header has been fully written.
    pub fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.check_available_space(count)?;
        let cnt = src.read_vectored_at_volatile(
            // Safe because check_available_space() ensures capacity.
            unsafe {
                &[FileVolatileSlice::from_raw_ptr(
                    self.body.as_mut_ptr().add(self.body.len()),
                    count,
                )]
            },
            off,
        )?;
        let new_len = self.body.len() + cnt;
        // Safe because cnt <= count was checked above.
        unsafe { self.body.set_len(new_len) };
        Ok(cnt)
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
    // All methods forward to the inherent methods of the same name; the
    // explicit `UringWriter::` prefix keeps the forwarding unambiguous and
    // makes removing an inherent method a compile error instead of silent
    // infinite recursion. The uring transport has no async-io support and
    // relies on the trait's default `EINVAL` implementations for the
    // `async_*` methods.
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
fn add_bufpools(
    fd: RawFd,
    nr_queues: usize,
    bufs_per_queue: usize,
    buf_size: usize,
) -> io::Result<BufPools> {
    let pools = BufPools::new(nr_queues, bufs_per_queue, buf_size)?;
    let mut ring = IoUring::<squeue::Entry128, cqueue::Entry>::generic_builder()
        .build((nr_queues * 2) as u32)?;
    {
        let mut sq = ring.submission();
        for qid in 0..nr_queues {
            let add_queue = FuseUringCmdReq {
                qid: qid as u16,
                ..Default::default()
            };
            let add_bufpool = FuseUringCmdReq {
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
        }
    }
    let mut pending = nr_queues * 2;
    while pending > 0 {
        match ring.submit_and_wait(pending) {
            Ok(_) => {}
            Err(e) if e.raw_os_error() == Some(libc::EINTR) => {}
            Err(e) => return Err(e),
        }
        for cqe in ring.completion() {
            pending -= 1;
            if cqe.result() < 0 {
                return Err(io::Error::other(format!(
                    "adding the buffer pool of queue {} failed: {}",
                    cqe.user_data(),
                    io::Error::from_raw_os_error(-cqe.result())
                )));
            }
        }
    }
    Ok(pools)
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

    let sqe = opcode::UringCmd80::new(types::Fd(fd), cmd_op)
        .cmd(bytes)
        .build();
    let Some(iovecs) = iovecs else {
        return sqe;
    };
    // sqe->addr points to the iovec array and sqe->len to the segment
    // count, as required by fuse_uring_get_iovec_from_sqe(). The crate
    // exposes no accessor for them on URING_CMD entries, so patch them
    // through a layout mirror of the SQE.
    //
    // Safe because SqeMirror mirrors the kernel ABI layout of
    // io_uring_sqe and Entry128 is an SQE plus a 64-byte command area;
    // the sizes are asserted below and only addr/len are overwritten.
    unsafe {
        assert_eq!(
            std::mem::size_of::<(SqeMirror, [u8; 64])>(),
            std::mem::size_of::<squeue::Entry128>()
        );
        let (mut inner, cmd_area) =
            std::mem::transmute::<squeue::Entry128, (SqeMirror, [u8; 64])>(sqe);
        inner.addr = iovecs.as_ptr() as u64;
        inner.len = FUSE_URING_IOV_SEGS as u32;
        std::mem::transmute::<(SqeMirror, [u8; 64]), squeue::Entry128>((inner, cmd_area))
    }
}

/// Where the payload buffers of an entry come from.
enum Payload {
    /// The entry has a payload area of its own, of this many bytes.
    Own(usize),
    /// The entry's queue has a buffer pool in these pools, and the kernel
    /// lends the entry a buffer per request.
    Pool(Arc<BufPools>),
}

/// One ring entry: the memory areas the kernel reads/writes plus scratch
/// regions used to reassemble requests and collect replies.
struct UringEntry {
    qid: u16,
    /// Single allocation, laid out as
    /// [FuseUringReqHeader][own payload area][request scratch][reply scratch].
    mem: Box<[u8]>,
    payload: Payload,
    /// iovec array referenced by the SQEs, must stay at a stable address.
    iovecs: Box<[libc::iovec; FUSE_URING_IOV_SEGS]>,
}

impl UringEntry {
    fn new(qid: u16, payload: Payload) -> UringEntry {
        let own_cap = match payload {
            Payload::Own(cap) => cap,
            Payload::Pool(_) => 0,
        };
        let scratch = FUSE_HEADER_SIZE + own_cap;
        let header_len = std::mem::size_of::<FuseUringReqHeader>();
        let mem = vec![0u8; header_len + own_cap + 2 * scratch].into_boxed_slice();
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
        let req = FuseUringCmdReq {
            qid: self.qid,
            commit_id,
            ..Default::default()
        };
        cmd_sqe(fd, cmd_op, &req, Some(&self.iovecs)).user_data(user_data)
    }

    /// Stage a `-errno` error reply, so that the subsequent
    /// `COMMIT_AND_FETCH` hands the client a proper error instead of the
    /// request data still sitting in the entry areas.
    fn stage_error_reply(&mut self, errno: i32) {
        let header = self.header_mut();
        let mut in_hdr = InHeader::default();
        in_hdr
            .as_mut_slice()
            .copy_from_slice(&header.in_out[..IN_HEADER_SIZE]);
        let out = OutHeader {
            len: OUT_HEADER_SIZE as u32,
            error: -errno,
            unique: in_hdr.unique,
        };
        header.in_out[..OUT_HEADER_SIZE].copy_from_slice(out.as_slice());
        header.ring_ent_in_out.payload_sz = 0;
    }
}

/// One io_uring based serving thread, responsible for a subset of the kernel
/// queues.
struct UringWorker<F: FileSystem + Send + Sync + 'static> {
    fd: File,
    qids: Vec<u16>,
    entries_per_queue: usize,
    /// Size of the payload area of an entry whose queue has no buffer pool.
    payload_cap: usize,
    /// The queues' buffer pools, if the kernel took them.
    pools: Option<Arc<BufPools>>,
    server: Arc<Server<F>>,
}

impl<F: FileSystem + Send + Sync + 'static> UringWorker<F> {
    fn run(self, exit: Arc<AtomicBool>, ready_tx: Sender<io::Result<()>>) -> io::Result<()> {
        let total_entries = self.qids.len() * self.entries_per_queue;
        let mut ring: IoUring<squeue::Entry128, cqueue::Entry> =
            IoUring::<squeue::Entry128, cqueue::Entry>::generic_builder()
                .build((total_entries * 2) as u32)?;
        let fd = self.fd.as_raw_fd();

        let mut entries: Vec<UringEntry> = Vec::with_capacity(total_entries);
        for qid in &self.qids {
            for _ in 0..self.entries_per_queue {
                let payload = match &self.pools {
                    Some(pools) => Payload::Pool(pools.clone()),
                    None => Payload::Own(self.payload_cap),
                };
                entries.push(UringEntry::new(*qid, payload));
            }
        }

        // Register all entries; the CQE of each REGISTER SQE returns once a
        // request has been assigned to the entry.
        let registered = (|| {
            let mut sq = ring.submission();
            for (idx, entry) in entries.iter().enumerate() {
                let sqe = entry.cmd_sqe(fd, FUSE_IO_URING_CMD_REGISTER, 0, idx as u64);
                // Safe because release_entries() keeps the entries alive
                // while the kernel holds them.
                unsafe { sq.push(&sqe) }
                    .map_err(|e| io::Error::other(format!("submission queue full: {e}")))?;
            }
            drop(sq);
            ring.submit()
        })()
        .map(|_| ());
        let _ = ready_tx.send(match &registered {
            Ok(()) => Ok(()),
            Err(e) => Err(io::Error::other(e.to_string())),
        });
        registered?;
        // The number of entries whose command the kernel hasn't completed.
        let mut armed = entries.len();

        let result = 'serve: loop {
            match ring.submit_and_wait(1) {
                Ok(_) => {}
                // A signal interrupted the wait, which is no reason to stop.
                Err(e) if e.raw_os_error() == Some(libc::EINTR) => continue,
                Err(e) => break 'serve Err(e),
            }

            // Drain the completion queue first so that its borrow is
            // released before entries are processed and commits submitted.
            let completed: Vec<(usize, i32)> = ring
                .completion()
                .map(|cqe| (cqe.user_data() as usize, cqe.result()))
                .collect();
            if completed.is_empty() {
                continue;
            }
            let returned = completed
                .iter()
                .filter(|(idx, _)| *idx < entries.len())
                .count();
            armed = armed.saturating_sub(returned);

            for (idx, res) in completed {
                if idx >= entries.len() {
                    warn!("uring worker: CQE with unexpected user_data {}", idx);
                    continue;
                }
                let entry = &mut entries[idx];
                if res < 0 {
                    if exit.load(Ordering::Relaxed) {
                        break 'serve Ok(());
                    }
                    // Registration/commit failures leave the entry in an
                    // undefined state; stop serving rather than guessing.
                    break 'serve Err(io::Error::from_raw_os_error(-res));
                }

                if let Err(e) = self.process(entry) {
                    warn!("uring worker: failed to handle request: {e}");
                    entry.stage_error_reply(libc::EIO);
                }

                let ent: FuseUringEntInOut = entry.header().ring_ent_in_out;
                let sqe = entry.cmd_sqe(
                    fd,
                    FUSE_IO_URING_CMD_COMMIT_AND_FETCH,
                    ent.commit_id,
                    idx as u64,
                );
                loop {
                    let pushed = {
                        let mut sq = ring.submission();
                        // Safe because release_entries() keeps the entries
                        // alive while the kernel holds them.
                        unsafe { sq.push(&sqe) }.is_ok()
                    };
                    if pushed {
                        break;
                    }
                    // The submission queue can never hold more outstanding
                    // commits than completed entries, so submitting must
                    // eventually make room.
                    if let Err(e) = ring.submit() {
                        break 'serve Err(e);
                    }
                }
                // Count the commit once it is queued, because
                // release_entries() submits anything still queued.
                armed += 1;
            }
            if let Err(e) = ring.submit() {
                break 'serve Err(e);
            }
        };
        release_entries(ring, entries, armed);
        result
    }

    /// Handle one delivered request: reassemble the header/args in the
    /// request scratch, dispatch to the server with scatter types that
    /// reference the entry's payload area directly (zero-copy on the data
    /// path), and stage the reply straight into the entry areas.
    fn process(&self, entry: &mut UringEntry) -> Result<()> {
        let in_header: InHeader = {
            let header = entry.header();
            let mut hdr = InHeader::default();
            hdr.as_mut_slice()
                .copy_from_slice(&header.in_out[..IN_HEADER_SIZE]);
            hdr
        };
        // Answer an opcode the table doesn't know with ENOSYS here, rather
        // than dispatch it without its arguments. The kernel then stops
        // sending it, as it does with FUSE_STATX.
        let Some((args_len, has_out_args)) = op_args(in_header.opcode) else {
            entry.stage_error_reply(libc::ENOSYS);
            return Ok(());
        };
        let payload_sz = entry.header().ring_ent_in_out.payload_sz as usize;
        let (payload_buf, payload_cap) = entry.payload_buffer(has_out_args, payload_sz)?;
        if args_len > FUSE_URING_IN_OUT_HEADER_SZ || payload_sz > payload_cap {
            return Err(SessionFailure(format!(
                "uring: malformed request, opcode {} args {} payload {}",
                in_header.opcode, args_len, payload_sz
            )));
        }

        let header_len = std::mem::size_of::<FuseUringReqHeader>();
        let own_cap = entry.own_cap();
        let scratch = FUSE_HEADER_SIZE + own_cap;
        let base = entry.mem.as_mut_ptr();

        // Assemble only the small header/args portion in the request scratch
        // region (40 + args_len bytes). The payload (up to ~128K for large
        // writes) stays in the entry's payload area and is read directly by
        // the scatter Reader, eliminating the per-request payload memcpy.
        //
        // Safe because the slices below address disjoint regions of the
        // entry allocation and live for the duration of this function only.
        unsafe {
            let header = &*(base as *const FuseUringReqHeader);
            let req_scratch =
                std::slice::from_raw_parts_mut(base.add(header_len + own_cap), scratch);
            let mut off = 0;
            req_scratch[off..off + IN_HEADER_SIZE]
                .copy_from_slice(&header.in_out[..IN_HEADER_SIZE]);
            off += IN_HEADER_SIZE;
            req_scratch[off..off + args_len].copy_from_slice(&header.op_in[..args_len]);
        }

        let total = {
            // Build a scatter Reader:
            //   Buffer 1 (header scratch): InHeader + opcode args
            //   Buffer 2 (payload buffer): request payload — only when
            //     payload_sz > 0, avoiding a copy of up to ~128K.
            //
            // Build a scatter Writer:
            //   Header slot (entry.in_out): fuse_out_header (16 bytes)
            //   Body slot (payload buffer): reply body
            // Both are written in place — no post-copy after handle_message.
            let header_args_len = IN_HEADER_SIZE + args_len;
            let header_scratch = unsafe {
                std::slice::from_raw_parts_mut(base.add(header_len + own_cap), header_args_len)
            };

            let reader = if payload_sz > 0 {
                // SAFETY: The Reader's buffer 2 and the Writer's body below
                // both cover the payload buffer, the entry's own or the one
                // the kernel lent it, which the kernel doesn't touch until
                // the entry commits.
                // This is technically overlapping mutable borrows, but is
                // sound because:
                //   (1) The Reader is fully consumed during argument parsing
                //       (before handle_message returns).
                //   (2) The Writer only writes to the payload area during
                //       reply construction (after the Reader is consumed).
                //   (3) Both slices are constructed via raw pointers inside
                //       unsafe blocks, so the borrow checker doesn't track
                //       them across the handle_message call.
                // A future refactor could eliminate this by using raw
                // pointers in both Reader and Writer APIs.
                let entry_payload =
                    unsafe { std::slice::from_raw_parts_mut(payload_buf.as_ptr(), payload_sz) };
                Reader::<()>::from_uring_buffers(header_scratch, entry_payload)?
            } else {
                Reader::<()>::from_fuse_buffer(FuseBuf::new(header_scratch))?
            };

            // The reply header goes into entry.in_out[0..OUT_HEADER_SIZE] and
            // the reply body goes directly into the payload buffer.
            // See SAFETY comment above regarding overlap with Reader's buffer 2.
            let in_out_header = unsafe { std::slice::from_raw_parts_mut(base, OUT_HEADER_SIZE) };
            let payload_area =
                unsafe { std::slice::from_raw_parts_mut(payload_buf.as_ptr(), payload_cap) };
            let writer = UringWriter::<()>::new(in_out_header, payload_area);

            self.server
                .handle_message(reader, writer, None, None)
                .map_err(|e| {
                    SessionFailure(format!(
                        "uring: handle message unique 0x{:x}: {}",
                        in_header.unique, e
                    ))
                })?
        };

        if total > 0 {
            // The scatter writer already placed the reply directly in the
            // entry areas; just record the payload size and validate.
            if total < OUT_HEADER_SIZE || total > OUT_HEADER_SIZE + payload_cap {
                return Err(SessionFailure(format!(
                    "uring: malformed reply of {} bytes for unique 0x{:x}",
                    total, in_header.unique
                )));
            }
            let payload_len = total - OUT_HEADER_SIZE;
            entry.header_mut().ring_ent_in_out.payload_sz = payload_len as u32;
        } else {
            // Forget-like requests carry no reply.
            entry.header_mut().ring_ent_in_out.payload_sz = 0;
        }

        Ok(())
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
fn release_entries(
    mut ring: IoUring<squeue::Entry128, cqueue::Entry>,
    entries: Vec<UringEntry>,
    mut armed: usize,
) {
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
        match ring.submitter().submit_with_args(1, &args) {
            Ok(_) => {}
            Err(e)
                if matches!(
                    e.raw_os_error(),
                    Some(libc::ETIME | libc::EINTR | libc::EBUSY | libc::EAGAIN)
                ) => {}
            Err(_) => break,
        }
        let len = entries.len();
        armed = armed.saturating_sub(
            ring.completion()
                .filter(|cqe| (cqe.user_data() as usize) < len)
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
    /// Whether the queues have buffer pools.
    #[cfg(test)]
    pooled: bool,
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
        mut session: FuseSession,
        server: Arc<Server<F>>,
        cfg: UringConfig,
    ) -> Result<UringFuseServing<F>> {
        warn!("FUSE-over-io_uring transport is experimental, the kernel interface may change");

        let payload_cap = session.bufsize().saturating_sub(FUSE_HEADER_SIZE);
        let nr_queues = possible_cpu_count()?;

        // The first message on a new connection is always FUSE_INIT; handle
        // it on a classic channel and verify the negotiation outcome.
        let mut init_ch = session.new_channel()?;
        let fallback_ch = session.new_channel()?;
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
        let workers = workers.min(nr_queues);

        let mut queue_ids: Vec<Vec<u16>> = vec![Vec::new(); workers];
        for qid in 0..nr_queues {
            queue_ids[qid % workers].push(qid as u16);
        }

        let file = session
            .get_fuse_file()
            .ok_or_else(|| SessionFailure("uring: session not mounted".into()))?
            .try_clone()
            .map_err(|e| SessionFailure(format!("uring: dup fuse fd: {e}")))?;

        // A queue's entries hold at most one buffer each, so more buffers
        // than entries would never be lent.
        let bufs_per_queue = cfg.bufs_per_queue.min(cfg.entries_per_queue.max(1));
        let pools = if bufs_per_queue > 0 && server.uring_bufpool_supported() {
            let buf_size = server.uring_payload_size();
            let pools = add_bufpools(file.as_raw_fd(), nr_queues, bufs_per_queue, buf_size)
                .map_err(|e| SessionFailure(format!("uring: {e}")))?;
            info!("uring: each queue has a pool of {bufs_per_queue} buffers of {buf_size} bytes");
            Some(Arc::new(pools))
        } else {
            None
        };

        // Build one worker per queue set, cloning the fuse fd up front so
        // cloning failures are reported before any thread is spawned.
        let mut worker_list = Vec::with_capacity(workers);
        for ids in queue_ids {
            worker_list.push(UringWorker {
                fd: file
                    .try_clone()
                    .map_err(|e| SessionFailure(format!("uring: dup fuse fd: {e}")))?,
                qids: ids,
                entries_per_queue: cfg.entries_per_queue,
                payload_cap,
                pools: pools.clone(),
                server: server.clone(),
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
                    let _ = worker.run(exit, ready_tx);
                }
            });
            match handle {
                Ok(handle) => set.push(handle),
                Err(e) => {
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

        let fallback = match thread::Builder::new()
            .name("uring-fallback".to_string())
            .spawn({
                let exit = exit.clone();
                let tracker = tracker.clone();
                move || {
                    let _exited = tracker.exit_guard();
                    Self::fallback_loop(fallback_ch, server, exit)
                }
            }) {
            Ok(handle) => handle,
            Err(e) => {
                set.stop(&mut session, true);
                return Err(SessionFailure(format!("uring: spawn fallback thread: {e}")));
            }
        };
        set.push(fallback);

        Ok(UringFuseServing {
            session,
            workers: set,
            #[cfg(test)]
            pooled: pools.is_some(),
            _fs: std::marker::PhantomData,
        })
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
        let total = header_len + payload_cap + 2 * (FUSE_HEADER_SIZE + payload_cap);
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

    #[test]
    fn test_cmd_sqe() {
        let entry = UringEntry::new(7, Payload::Own(64));
        let sqe = entry.cmd_sqe(42, FUSE_IO_URING_CMD_REGISTER, 0xdead_beef, 5);

        assert_eq!(
            std::mem::size_of::<(SqeMirror, [u8; 64])>(),
            std::mem::size_of::<squeue::Entry128>()
        );
        // Safe because of the size assertion above.
        let (inner, extra): (SqeMirror, [u8; 64]) = unsafe { std::mem::transmute(sqe) };

        // IORING_OP_URING_CMD as of kernel ABI 6.14.
        assert_eq!(inner.opcode, 46);
        assert_eq!(inner.fd, 42);
        assert_eq!(inner.addr, entry.iovecs.as_ptr() as u64);
        assert_eq!(inner.len, FUSE_URING_IOV_SEGS as u32);
        assert_eq!(inner.user_data, 5);

        // The io-uring crate splits the 80-byte command payload of an
        // SQE128: the first 16 bytes are placed in the sqe cmd union
        // (the addr3/__pad2 slots), the remaining 64 bytes in the extra
        // area, so the payload is contiguous at sqe offsets 48..128 and
        // io_uring_sqe128_cmd() reads it in one piece.
        let mut cmd_bytes = [0u8; 80];
        cmd_bytes[0..8].copy_from_slice(&inner.addr3.to_le_bytes());
        cmd_bytes[8..16].copy_from_slice(&inner.pad2.to_le_bytes());
        cmd_bytes[16..80].copy_from_slice(&extra);

        // The command payload must carry the queue id and commit id.
        let cmd = FuseUringCmdReq {
            qid: 7,
            commit_id: 0xdead_beef,
            ..Default::default()
        };
        assert_eq!(
            cmd_bytes[..std::mem::size_of::<FuseUringCmdReq>()],
            *cmd.as_slice()
        );
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
            qids: vec![0],
            entries_per_queue: 1,
            payload_cap: 4096,
            pools: None,
            server: Arc::new(Server::new(Arc::new(fs))),
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
        worker.process(&mut entry).unwrap();

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
        worker.process(&mut entry).unwrap();
        let out = parse_out_header(&entry);
        assert_eq!(out.error, -libc::ENOENT);
        assert_eq!(entry.header().ring_ent_in_out.payload_sz, 0);

        // And succeeds once the file exists.
        std::fs::write(_source.as_path().join("fuse-file"), "x").unwrap();
        plant_request(&mut entry, Opcode::Lookup as u32, &[], b"fuse-file\0");
        worker.process(&mut entry).unwrap();
        let out = parse_out_header(&entry);
        assert_eq!(out.error, 0);
        assert_eq!(
            entry.header().ring_ent_in_out.payload_sz as usize,
            std::mem::size_of::<EntryOut>()
        );
    }

    #[test]
    fn test_process_unknown_opcode_gets_enosys() {
        /// The STATX opcode, which the transport's table doesn't know.
        const FUSE_STATX: u32 = 52;
        let (worker, _source) = make_worker();
        let mut entry = UringEntry::new(0, Payload::Own(worker.payload_cap));

        // The kernel only falls back to GETATTR after ENOSYS.
        plant_request(&mut entry, FUSE_STATX, &[0u8; 24], &[]);
        worker.process(&mut entry).unwrap();
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
        assert!(worker.process(&mut entry).is_err());
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
        worker.process(&mut entry).unwrap();
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
        assert!(worker.process(&mut entry).is_err());
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

    /// Serve a PassthroughFs over io_uring with each queue's buffer pool
    /// holding `bufs_per_queue` buffers, read and write through the mount,
    /// then check that dropping the serving layer gets the ring entries
    /// back from the kernel and unmounts.
    fn check_passthrough_mount(bufs_per_queue: usize) {
        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"over io_uring").unwrap();
        let mnt = TempDir::new().unwrap();
        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        let server = Arc::new(Server::new(fs));
        server.set_uring(true);
        let mut se = FuseSession::new(mnt.as_path(), "uring_serving_test", "", false).unwrap();
        se.mount().unwrap();
        let cfg = UringConfig {
            workers: 2,
            entries_per_queue: 2,
            bufs_per_queue,
        };
        let serving = match UringFuseServing::new(se, server.clone(), cfg) {
            Ok(serving) => serving,
            Err(UringNotSupported) => {
                eprintln!("FUSE-over-io_uring is not available, skipping");
                return;
            }
            Err(e) => panic!("uring serving failed: {}", e),
        };
        // Kernels with buffer pools must get them when the config asks.
        assert_eq!(
            serving.pooled,
            bufs_per_queue > 0 && server.uring_bufpool_supported()
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
        for bufs_per_queue in [0, 1, 4] {
            check_passthrough_mount(bufs_per_queue);
        }
    }
}
