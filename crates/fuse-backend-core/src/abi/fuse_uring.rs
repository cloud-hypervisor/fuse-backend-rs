// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Linux FUSE-over-io_uring ABI definitions, protocol version 7.42 (kernel 6.14+),
//! and the buffer pools of protocol 7.46 (kernel 7.3).
//!
//! Experimental: the kernel interface is still evolving.

#![allow(missing_docs)]

use vm_memory::ByteValued;

/// INIT flag: client supports serving FUSE requests over io_uring (protocol 7.42).
pub const FUSE_OVER_IO_URING: u64 = 1_u64 << 41;

/// INIT flag the kernel sets when it supports io_uring buffer pools (protocol 7.46).
pub const FUSE_HAS_IO_URING_BUFPOOL: u64 = 1_u64 << 43;

/// Size of the fuse_in_header/fuse_out_header slot inside `FuseUringReqHeader`.
pub const FUSE_URING_IN_OUT_HEADER_SZ: usize = 128;

/// Size of the per-opcode header slot inside `FuseUringReqHeader`.
pub const FUSE_URING_OP_IN_OUT_SZ: usize = 128;

/// Number of iovec segments a REGISTER SQE must describe (headers + payload).
pub const FUSE_URING_IOV_SEGS: usize = 2;

/// iovec segment index of the headers area (`FuseUringReqHeader`).
pub const FUSE_URING_IOV_HEADERS: usize = 0;

/// iovec segment index of the payload area.
pub const FUSE_URING_IOV_PAYLOAD: usize = 1;

/// SQE command opcodes, placed in `sqe->cmd_op` of an `IORING_OP_URING_CMD` SQE.
pub const FUSE_IO_URING_CMD_INVALID: u32 = 0;
pub const FUSE_IO_URING_CMD_REGISTER: u32 = 1;
pub const FUSE_IO_URING_CMD_COMMIT_AND_FETCH: u32 = 2;
/// Create a queue (protocol 7.46). Buffer pools need it.
pub const FUSE_IO_URING_CMD_ADD_QUEUE: u32 = 3;
/// Give a queue a buffer pool (protocol 7.46). The queue must exist and must
/// not have registered entries with their own payload buffers yet.
pub const FUSE_IO_URING_CMD_ADD_BUFPOOL: u32 = 4;

/// `FuseUringCmdReq::flags` of ADD_QUEUE: serve the queue's reads and writes
/// with zero-copy (protocol 7.46). The kernel then registers the client's
/// pages of such a request in the server's io_uring buffer table, at the
/// index the entry gave at REGISTER, and the server moves the data with
/// fixed-buffer operations. Needs a buffer pool and CAP_SYS_ADMIN.
pub const FUSE_URING_ZERO_COPY: u64 = 1;

/// `FuseUringEntInOut::flags` of a request whose pages the kernel
/// registered for zero-copy instead of copying them (protocol 7.46).
pub const FUSE_URING_ENT_ZERO_COPY: u64 = 1;

/// Shared in/out descriptor of one ring entry, embedded in `FuseUringReqHeader`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FuseUringEntInOut {
    pub flags: u64,
    /// Commit ID to echo back with `FUSE_IO_URING_CMD_COMMIT_AND_FETCH`.
    pub commit_id: u64,
    /// Size of the payload in bytes (request: set by kernel, reply: set by daemon).
    pub payload_sz: u32,
    /// Offset of the request's payload buffer in the queue's buffer pool, if
    /// the queue has one (protocol 7.46). Before that it was padding.
    pub offset: u32,
    pub reserved: u64,
}

/// Header area of one ring entry, registered through `FUSE_IO_URING_CMD_REGISTER`.
///
/// Layout mirrors `struct fuse_uring_req_header`: a 128-byte in/out header slot
/// holding `fuse_in_header` (request) or `fuse_out_header` (reply), a 128-byte
/// per-opcode header slot holding the request arguments, and the shared
/// entry descriptor.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct FuseUringReqHeader {
    pub in_out: [u8; FUSE_URING_IN_OUT_HEADER_SZ],
    pub op_in: [u8; FUSE_URING_OP_IN_OUT_SZ],
    pub ring_ent_in_out: FuseUringEntInOut,
}

impl Default for FuseUringReqHeader {
    fn default() -> Self {
        // All fields are plain bytes, a zeroed value is valid.
        unsafe { std::mem::zeroed() }
    }
}

/// Command payload of an uring command SQE, placed in the 80-byte command
/// area of an SQE128.
///
/// Layout mirrors `struct fuse_uring_cmd_req`. REGISTER and
/// COMMIT_AND_FETCH use `commit_id` and `qid`, ADD_QUEUE uses `qid`, and
/// ADD_BUFPOOL uses `qid` and `bufpool`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FuseUringCmdReq {
    pub flags: u64,
    /// Entry identifier, taken from `FuseUringEntInOut.commit_id`.
    pub commit_id: u64,
    /// Index of the per-CPU queue the command is for.
    pub qid: u16,
    pub padding: [u8; 6],
    /// The buffer pool of an ADD_BUFPOOL command (protocol 7.46).
    pub bufpool: FuseUringBufpool,
}

/// Buffer pool of a queue, `fuse_uring_cmd_req.bufpool`. The kernel cuts it
/// into buffers of the connection's maximum payload size.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FuseUringBufpool {
    /// Address of the pool in the daemon's memory.
    pub uaddr: u64,
    /// Length of the pool in bytes.
    pub len: u32,
    pub reserved: u32,
}

impl FuseUringCmdReq {
    /// Set `ent_zero_copy_buf_index` of a REGISTER command for a queue with
    /// zero-copy: the index in the server's io_uring buffer table where the
    /// kernel registers the client's pages of the entry's requests. The
    /// kernel puts it in a union with `bufpool`, at the same offset.
    pub fn set_ent_zero_copy_buf_index(&mut self, index: u16) {
        let mut uaddr = [0u8; 8];
        uaddr[..2].copy_from_slice(&index.to_ne_bytes());
        self.bufpool = FuseUringBufpool {
            uaddr: u64::from_ne_bytes(uaddr),
            ..Default::default()
        };
    }
}

// SAFETY: all four structs are `repr(C)` plain data types without padding
// holes or pointer members, matching their kernel counterparts.
unsafe impl ByteValued for FuseUringEntInOut {}
unsafe impl ByteValued for FuseUringReqHeader {}
unsafe impl ByteValued for FuseUringCmdReq {}
unsafe impl ByteValued for FuseUringBufpool {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layouts() {
        assert_eq!(std::mem::size_of::<FuseUringEntInOut>(), 32);
        assert_eq!(std::mem::size_of::<FuseUringReqHeader>(), 288);
        assert_eq!(std::mem::size_of::<FuseUringCmdReq>(), 40);
        assert_eq!(std::mem::offset_of!(FuseUringCmdReq, bufpool), 24);
        assert_eq!(std::mem::offset_of!(FuseUringEntInOut, offset), 20);
        assert_eq!(
            std::mem::offset_of!(FuseUringReqHeader, ring_ent_in_out),
            FUSE_URING_IN_OUT_HEADER_SZ + FUSE_URING_OP_IN_OUT_SZ
        );
        assert_eq!(std::mem::offset_of!(FuseUringCmdReq, qid), 16);
    }
}
