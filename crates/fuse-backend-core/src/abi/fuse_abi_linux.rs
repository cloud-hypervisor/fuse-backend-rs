// Copyright 2019 The Chromium OS Authors. All rights reserved.
//
// SPDX-License-Identifier: BSD-3-Clause

//! Linux Fuse Application Binary Interfaces.
//!
//! The wire-format structs live in `fuse_abi_wire.rs`; this prelude only
//! re-exports the glibc LFS-64 libc names the body uses.

#![allow(missing_docs)]

pub use libc::{
    blksize_t, dev_t, ino64_t, mode_t, nlink_t, off64_t, pread64, preadv64, pwrite64, pwritev64,
    stat64, statvfs64,
};

include!("fuse_abi_wire.rs");
