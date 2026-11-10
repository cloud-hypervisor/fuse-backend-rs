// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS directory-walk seam.
//!
//! macOS has no `getdents64()`; directory enumeration there goes through
//! `fdopendir()`/`readdir()`, which the future port will wire up.  For the
//! framework, [`getdents64`] answers `ENOSYS` so a macOS mount fails cleanly
//! instead of enumerating wrongly.  [`skip_to_cookie`] keeps the real
//! implementation though: it is pure buffer logic over the `LinuxDirent64`
//! wire format that the (portable) cookie tests exercise.

// API-parity stub twin: `skip_to_cookie` is only reached through the portable
// tests until the port fills in real enumeration.
#![allow(dead_code)]

use std::io;
use std::mem::size_of;
use std::os::unix::io::RawFd;

use crate::os::LinuxDirent64;
use crate::util::enosys;
use vm_memory::ByteValued;

/// Skip entries in a getdents64 buffer up to and including the entry whose
/// `d_off` equals `offset`.  After this returns, `buf` starts with the entry
/// immediately after the matched one.  Returns `true` if the target cookie
/// was found, `false` otherwise.
pub(crate) fn skip_to_cookie(buf: &mut Vec<u8>, offset: u64) -> bool {
    let mut cur: usize = 0;
    let mut found = false;
    let mut target_reclen: usize = 0;
    while cur + size_of::<LinuxDirent64>() <= buf.len() {
        let front = &buf[cur..cur + size_of::<LinuxDirent64>()];
        let dirent64 = match LinuxDirent64::from_slice(front) {
            Some(d) => d,
            // Defend against a malformed getdents64 buffer.
            None => break,
        };
        let reclen = dirent64.d_reclen as usize;
        // Defend against a malformed getdents64 buffer: a record shorter
        // than the header would loop forever.
        if reclen < size_of::<LinuxDirent64>() {
            break;
        }
        if dirent64.d_off as u64 == offset {
            found = true;
            target_reclen = reclen;
            break;
        }
        cur += reclen;
    }

    if found {
        cur += target_reclen;
        buf.drain(..cur);
    }
    found
}

/// Read the next batch of directory entries from the directory descriptor
/// `dir_fd`, resuming at cookie `offset`.
///
/// `ENOSYS`: macOS has no `getdents64()`; the port will walk the directory
/// with `fdopendir()`/`readdir()` instead (see #182 for a reference
/// implementation).
pub(crate) fn getdents64(
    _dir_fd: RawFd,
    _cookie_hit: bool,
    _offset: u64,
    _size: u32,
) -> io::Result<Vec<u8>> {
    Err(enosys())
}
