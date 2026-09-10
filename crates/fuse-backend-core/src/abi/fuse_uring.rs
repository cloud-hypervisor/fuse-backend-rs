// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Linux FUSE-over-io_uring ABI definitions, protocol version 7.42 (kernel 6.14+).
//!
//! Experimental: the kernel interface is still evolving (reduced queue counts,
//! bufpool/zero-copy extensions are being developed upstream). Only the minimal
//! 7.42 interface is defined here; in-flight extensions are intentionally left
//! out.

#![allow(missing_docs)]

use vm_memory::ByteValued;

/// INIT flag: client supports serving FUSE requests over io_uring (protocol 7.42).
pub const FUSE_OVER_IO_URING: u64 = 1_u64 << 41;

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

/// Shared in/out descriptor of one ring entry, embedded in `FuseUringReqHeader`.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FuseUringEntInOut {
    pub flags: u64,
    /// Commit ID to echo back with `FUSE_IO_URING_CMD_COMMIT_AND_FETCH`.
    pub commit_id: u64,
    /// Size of the payload in bytes (request: set by kernel, reply: set by daemon).
    pub payload_sz: u32,
    pub padding: u32,
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
/// Layout mirrors `struct fuse_uring_cmd_req`. For REGISTER and
/// COMMIT_AND_FETCH only `commit_id` and `qid` are used.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default)]
pub struct FuseUringCmdReq {
    pub flags: u64,
    /// Entry identifier, taken from `FuseUringEntInOut.commit_id`.
    pub commit_id: u64,
    /// Index of the per-CPU queue the command is for.
    pub qid: u16,
    pub padding: [u8; 6],
}

// SAFETY: all three structs are `repr(C)` plain data types without padding
// holes or pointer members, matching their kernel counterparts.
unsafe impl ByteValued for FuseUringEntInOut {}
unsafe impl ByteValued for FuseUringReqHeader {}
unsafe impl ByteValued for FuseUringCmdReq {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_layouts() {
        assert_eq!(std::mem::size_of::<FuseUringEntInOut>(), 32);
        assert_eq!(std::mem::size_of::<FuseUringReqHeader>(), 288);
        assert_eq!(std::mem::size_of::<FuseUringCmdReq>(), 24);
        assert_eq!(
            std::mem::offset_of!(FuseUringReqHeader, ring_ent_in_out),
            FUSE_URING_IN_OUT_HEADER_SZ + FUSE_URING_OP_IN_OUT_SZ
        );
        assert_eq!(std::mem::offset_of!(FuseUringCmdReq, qid), 16);
    }
}
