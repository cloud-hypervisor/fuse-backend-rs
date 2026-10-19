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

use std::collections::VecDeque;
use std::fs::File;
use std::io::{self, IoSlice, Write};
use std::mem::ManuallyDrop;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::mpsc::{channel, Sender};
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use io_uring::{cqueue, opcode, squeue, types, IoUring};
use vm_memory::ByteValued;

use fuse_backend_core::abi::fuse_abi::{InHeader, Opcode, OutHeader, ReadIn};
use fuse_backend_core::abi::fuse_uring::{
    FuseUringBufpool, FuseUringCmdReq, FuseUringEntInOut, FuseUringReqHeader,
    FUSE_IO_URING_CMD_ADD_BUFPOOL, FUSE_IO_URING_CMD_ADD_QUEUE, FUSE_IO_URING_CMD_COMMIT_AND_FETCH,
    FUSE_IO_URING_CMD_REGISTER, FUSE_URING_ENT_ZERO_COPY, FUSE_URING_IN_OUT_HEADER_SZ,
    FUSE_URING_IOV_SEGS, FUSE_URING_ZERO_COPY,
};
use fuse_backend_core::api::filesystem::FileSystem;
use fuse_backend_core::api::server::Server;
use fuse_backend_core::buffer::{Error::*, Reader, Result, Writer, ZeroCopySource};
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
    /// Serve the reads and writes of opens that ask for it with zero-copy
    /// (`OpenOptions::IO_URING_ZERO_COPY`, Linux 7.3). The kernel lends the
    /// client's pages to the request, and the transport moves the data
    /// between them and the file the file system names with io_uring
    /// fixed-buffer operations, without copying it through memory. It
    /// needs buffer pools and CAP_SYS_ADMIN, and the transport serves
    /// without it otherwise. File systems must pass reads and writes of
    /// such opens to `ZeroCopyWriter::write_from()` and
    /// `ZeroCopyReader::read_to()` with a file that has a descriptor.
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
        // File data only goes into the body, so free space in the header
        // slot doesn't count.
        check_space(self.body.capacity() - self.body.len(), count)?;
        let cnt = src
            .read_vectored_at_volatile(
                // Safe because the body has room for count more bytes.
                unsafe {
                    &[FileVolatileSlice::from_raw_ptr(
                        self.body.as_mut_ptr().add(self.body.len()),
                        count,
                    )]
                },
                off,
            )?
            .min(count);
        let new_len = self.body.len() + cnt;
        // Safe because the read placed cnt <= count bytes behind the body.
        unsafe { self.body.set_len(new_len) };
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
    let mut ring = FuseRing::generic_builder().build((nr_queues * 2).max(2) as u32)?;
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

/// The completions of ring entries that a worker took off its ring and
/// hasn't handled yet, and how many entries the kernel still holds.
struct Completions {
    queue: VecDeque<(usize, i32)>,
    nr_entries: usize,
    /// The number of entries whose command the kernel hasn't completed.
    armed: usize,
}

impl Completions {
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
        use nix::sys::memfd::{memfd_create, MemFdCreateFlag};
        let name = std::ffi::CStr::from_bytes_with_nul(b"fuse-uring-zero-copy\0").unwrap();
        let fd = memfd_create(name, MemFdCreateFlag::MFD_CLOEXEC).map_err(io::Error::from)?;
        // Safe because the fd is new and nothing else owns it.
        let file = unsafe { File::from_raw_fd(fd) };
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
            ring.submit()?;
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
                .offset(off as libc::off_t)
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
        // Offset -1 writes at the file's position.
        let off = off.map_or(-1, |off| off as libc::off_t);
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
/// registers the client pages of zero-copy requests. io-uring 0.5 has no
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

/// One ring entry: the memory areas the kernel reads/writes plus scratch
/// regions used to reassemble requests and collect replies.
struct UringEntry {
    qid: u16,
    /// Single allocation, laid out as
    /// [FuseUringReqHeader][own payload area][request scratch][reply scratch].
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
    /// The memory file that copies of zero-copy data through memory go
    /// through, if the queues have zero-copy.
    bounce: Option<BounceBuf>,
    server: Arc<Server<F>>,
}

impl<F: FileSystem + Send + Sync + 'static> UringWorker<F> {
    fn run(self, exit: Arc<AtomicBool>, ready_tx: Sender<io::Result<()>>) -> io::Result<()> {
        let total_entries = self.qids.len() * self.entries_per_queue;
        let mut ring = FuseRing::generic_builder().build((total_entries * 2) as u32)?;
        if self.bounce.is_some() {
            if let Err(e) = register_sparse_buffers(&ring, total_entries) {
                let _ = ready_tx.send(Err(io::Error::other(format!(
                    "registering the zero-copy buffer table failed: {e}"
                ))));
                return Err(e);
            }
        }
        let fd = self.fd.as_raw_fd();

        let mut entries: Vec<UringEntry> = Vec::with_capacity(total_entries);
        for qid in &self.qids {
            for _ in 0..self.entries_per_queue {
                let payload = match &self.pools {
                    Some(pools) => Payload::Pool(pools.clone()),
                    None => Payload::Own(self.payload_cap),
                };
                let mut entry = UringEntry::new(*qid, payload);
                if self.bounce.is_some() {
                    entry.zero_copy_slot = Some(entries.len() as u16);
                }
                entries.push(entry);
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

        let mut completions = Completions {
            queue: VecDeque::new(),
            nr_entries: entries.len(),
            armed: entries.len(),
        };
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
                    if exit.load(Ordering::Relaxed) {
                        break 'serve Ok(());
                    }
                    // Registration/commit failures leave the entry in an
                    // undefined state; stop serving rather than guessing.
                    break 'serve Err(io::Error::from_raw_os_error(-res));
                }

                if let Err(e) = self.process(entry, &mut ring, &mut completions) {
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
                completions.armed += 1;
            }
            if let Err(e) = ring.submit() {
                break 'serve Err(e);
            }
        };
        release_entries(ring, entries, completions.armed);
        result
    }

    /// Handle one delivered request: reassemble the header/args in the
    /// request scratch, dispatch to the server with scatter types that
    /// reference the entry's payload area directly (zero-copy on the data
    /// path), and stage the reply straight into the entry areas.
    ///
    /// The client pages of a zero-copy request stay with the kernel, and
    /// fixed-buffer operations on `ring` move the data between them and the
    /// file. Ring completions that arrive meanwhile go to `stash`.
    fn process(
        &self,
        entry: &mut UringEntry,
        ring: &mut FuseRing,
        completions: &mut Completions,
    ) -> Result<()> {
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
        let ent_in_out = entry.header().ring_ent_in_out;
        let payload_sz = ent_in_out.payload_sz as usize;
        if ent_in_out.flags & FUSE_URING_ENT_ZERO_COPY == 0 {
            return self.process_copied(entry, in_header, args_len, has_out_args, payload_sz, None);
        }

        let kind = if in_header.opcode == Opcode::Read as u32 {
            // The kernel lends no payload buffer, and the reply data is
            // ReadIn.size bytes at most.
            let read_in = ReadIn::from_slice(&entry.header().op_in[..size_of::<ReadIn>()])
                .ok_or_else(|| SessionFailure("uring: malformed zero-copy READ".into()))?;
            ZeroCopyKind::Read {
                cap: read_in.size as usize,
            }
        } else if in_header.opcode == Opcode::Write as u32 {
            // The kernel lends a payload buffer for WriteOut, and payload_sz
            // counts the data in the client pages.
            ZeroCopyKind::Write { len: payload_sz }
        } else {
            return Err(SessionFailure(format!(
                "uring: zero-copy request with opcode {}",
                in_header.opcode
            )));
        };
        let (Some(slot), Some(bounce)) = (entry.zero_copy_slot, self.bounce.as_ref()) else {
            return Err(SessionFailure(
                "uring: zero-copy request on a worker without zero-copy".into(),
            ));
        };
        #[cfg(test)]
        ZERO_COPY_REQUESTS.fetch_add(1, Ordering::Relaxed);
        let zc_io = ZeroCopyIo {
            ring: Mutex::new((ring, completions)),
            slot,
            bounce: Mutex::new(bounce),
        };
        // The payload buffer holds no data of a zero-copy WRITE.
        let payload_sz = match kind {
            ZeroCopyKind::Write { .. } => 0,
            ZeroCopyKind::Read { .. } => payload_sz,
        };
        self.process_copied(
            entry,
            in_header,
            args_len,
            has_out_args,
            payload_sz,
            Some((&zc_io, kind)),
        )
    }

    /// Serve the request in `entry` whose payload buffer holds `payload_sz`
    /// bytes, and move the data of a zero-copy request through `zero_copy`.
    fn process_copied(
        &self,
        entry: &mut UringEntry,
        in_header: InHeader,
        args_len: usize,
        has_out_args: bool,
        payload_sz: usize,
        zero_copy: Option<(&ZeroCopyIo<'_>, ZeroCopyKind)>,
    ) -> Result<()> {
        let zc_cap = match zero_copy {
            Some((_, ZeroCopyKind::Read { cap })) => cap,
            _ => 0,
        };
        let (payload_buf, payload_cap) = match zero_copy {
            // A zero-copy READ has no payload buffer, even when it asks for
            // 0 bytes.
            Some((_, ZeroCopyKind::Read { .. })) => (NonNull::dangling(), 0),
            _ => entry.payload_buffer(has_out_args, payload_sz)?,
        };
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
            let reader = match zero_copy {
                Some((zc_io, ZeroCopyKind::Write { len })) => reader.with_zero_copy(zc_io, len),
                _ => reader,
            };

            // The reply header goes into entry.in_out[0..OUT_HEADER_SIZE] and
            // the reply body goes directly into the payload buffer.
            // See SAFETY comment above regarding overlap with Reader's buffer 2.
            let in_out_header = unsafe { std::slice::from_raw_parts_mut(base, OUT_HEADER_SIZE) };
            let payload_area =
                unsafe { std::slice::from_raw_parts_mut(payload_buf.as_ptr(), payload_cap) };
            let writer = UringWriter::<()>::new(in_out_header, payload_area);
            let writer = match zero_copy {
                Some((zc_io, ZeroCopyKind::Read { cap })) => writer.with_zero_copy(zc_io, cap),
                _ => writer,
            };

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
            if total < OUT_HEADER_SIZE || total > OUT_HEADER_SIZE + payload_cap + zc_cap {
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
fn release_entries(mut ring: FuseRing, entries: Vec<UringEntry>, mut armed: usize) {
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
        // The kernel takes a 16-bit buffer table slot per entry, and each
        // entry of a worker gets its own slot.
        let worker_entries =
            queue_ids.iter().map(Vec::len).max().unwrap_or(0) * cfg.entries_per_queue;
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
                // Zero-copy comes only with buffer pools.
                bounce: match pools.as_ref().filter(|_| zero_copy) {
                    Some(pools) => Some(BounceBuf::new(pools.buf_size).map_err(|e| {
                        SessionFailure(format!("uring: creating the zero-copy memory file: {e}"))
                    })?),
                    None => None,
                },
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
            #[cfg(test)]
            zero_copy,
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
            bounce: None,
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

    /// Serve the request planted in `entry` with `worker`, on a ring of its
    /// own.
    fn process_entry<F: FileSystem + Send + Sync + 'static>(
        worker: &UringWorker<F>,
        entry: &mut UringEntry,
    ) -> Result<()> {
        let mut ring = FuseRing::generic_builder().build(8).unwrap();
        let mut completions = Completions {
            queue: VecDeque::new(),
            nr_entries: 1,
            armed: 1,
        };
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

    /// Serve a PassthroughFs over io_uring with each queue's buffer pool
    /// holding `bufs_per_queue` buffers, and zero-copy if `zero_copy`, read
    /// and write through the mount, then check that dropping the serving
    /// layer gets the ring entries back from the kernel and unmounts.
    fn check_passthrough_mount(bufs_per_queue: usize, zero_copy: bool) {
        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"over io_uring").unwrap();
        let mnt = TempDir::new().unwrap();
        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            uring_zero_copy: zero_copy,
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
            zero_copy,
        };
        let serving = match UringFuseServing::new(se, server.clone(), cfg) {
            Ok(serving) => serving,
            Err(UringNotSupported) => {
                eprintln!("FUSE-over-io_uring is not available, skipping");
                return;
            }
            Err(e) => panic!("uring serving failed: {}", e),
        };
        // Kernels with buffer pools must get them when the config asks, and
        // zero-copy too when the test runs as root.
        assert_eq!(
            serving.pooled,
            bufs_per_queue > 0 && server.uring_bufpool_supported()
        );
        if serving.pooled && zero_copy && real_root() {
            assert!(serving.zero_copy);
        }
        eprintln!(
            "uring mount: {bufs_per_queue} buffers per queue, zero-copy {}",
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
            check_passthrough_mount(bufs_per_queue, zero_copy);
        }
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
}
