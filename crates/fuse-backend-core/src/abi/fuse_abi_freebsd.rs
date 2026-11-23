// Copyright 2026 The Chromium OS Authors. All rights reserved.
//
// SPDX-License-Identifier: BSD-3-Clause

//! FreeBSD Fuse Application Binary Interfaces.
//!
//! FreeBSD's in-kernel fusefs driver implements the Linux FUSE wire protocol,
//! so the wire-format structs are shared verbatim with the Linux ABI.  This
//! prelude bridges the glibc LFS-64 libc names the shared body uses to
//! FreeBSD's native libc spelling: FreeBSD's `ino_t`, `off_t`, `stat` and
//! `statvfs` are already 64-bit, and its `pread`/`preadv`/`pwrite`/`pwritev`
//! take full `off_t` offsets, so each `-64` name is a plain alias.  This
//! arm gives FreeBSD a type-checked ABI only: nothing here claims the
//! server's runtime behaviors (mount lifecycle, INIT handshake, flag
//! negotiation) have been verified against a FreeBSD kernel.

#![allow(missing_docs)]

pub use libc::{blksize_t, dev_t, mode_t, nlink_t};
pub use libc::{
    ino_t as ino64_t, off_t as off64_t, pread as pread64, preadv as preadv64, pwrite as pwrite64,
    pwritev as pwritev64, stat as stat64, statvfs as statvfs64,
};

include!("fuse_abi_wire.rs");
