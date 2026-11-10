// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Linux directory stream operations: the `getdents64` walk behind `readdir`.
//!
//! The rest of the crate only sees [`getdents64`], which returns the raw
//! dirent buffer; parsing it into reply entries stays with the protocol-level
//! caller.

use std::io;
use std::mem::size_of;
use std::os::unix::io::RawFd;

use crate::os::LinuxDirent64;
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
/// `dir_fd` into a freshly allocated buffer of capacity `size`, resuming at
/// cookie `offset`.
///
/// `cookie_hit` reports whether the caller's cookie cache already left the
/// descriptor positioned right after the entry whose `d_off == offset`, in
/// which case the `lseek64()` positioning is skipped entirely.
///
/// The caller must hold the file lock of the directory stream: this walk
/// works with the kernel offset, so no other thread may move it while we do.
/// Both the fast path and the fallback leave the descriptor positioned right
/// after the last entry in the returned buffer.
pub(crate) fn getdents64(
    dir_fd: RawFd,
    cookie_hit: bool,
    offset: u64,
    size: u32,
) -> io::Result<Vec<u8>> {
    let mut buf = Vec::<u8>::with_capacity(size as usize);

    // NFSv4 directory cookies (`nfs_cookie4`, RFC 7530) are unsigned 64-bit and roughly
    // half exceed `INT64_MAX`. When the guest resumes a readdir from such a cookie, the
    // `u64` -> `off64_t` cast produces a negative value and the host kernel's
    // `nfs_llseek_dir()` rejects it with `EINVAL`. In that case fall back to a linear scan
    // from the beginning, skipping past the target cookie so the caller receives exactly the
    // entries it has not seen yet.
    let seek_ok = if cookie_hit {
        true
    } else if offset > i64::MAX as u64 {
        false
    } else {
        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe { libc::lseek64(dir_fd, offset as libc::off64_t, libc::SEEK_SET) };
        if res >= 0 {
            true
        } else {
            let err = io::Error::last_os_error();
            // Only the "offset too large" case is recoverable here.
            if err.raw_os_error() != Some(libc::EINVAL) {
                return Err(err);
            }
            false
        }
    };

    if seek_ok {
        // Safe because the kernel guarantees that it will only write to `buf` and we check
        // the return value.
        let res = unsafe {
            libc::syscall(
                libc::SYS_getdents64,
                dir_fd,
                buf.as_mut_ptr() as *mut LinuxDirent64,
                size as libc::c_int,
            )
        };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }
        // Safe because we trust the value returned by kernel.
        unsafe { buf.set_len(res as usize) };
    } else {
        // Fallback for cookies the kernel cannot `lseek()` to: rewind and walk batches with
        // `getdents64` until the entry whose `d_off == offset` is consumed, then return the
        // entries after it. We never re-seek nor discard an already-read batch, so no
        // entries are lost.
        //
        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe { libc::lseek64(dir_fd, 0, libc::SEEK_SET) };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }

        let mut found = false;
        loop {
            // Safe because the kernel guarantees that it will only write to `buf` and we
            // check the return value.
            let res = unsafe {
                libc::syscall(
                    libc::SYS_getdents64,
                    dir_fd,
                    buf.as_mut_ptr() as *mut LinuxDirent64,
                    size as libc::c_int,
                )
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
            // Safe because we trust the value returned by kernel.
            unsafe { buf.set_len(res as usize) };

            if res == 0 {
                // EOF: either the target cookie was never found (the entry is gone or the
                // cookie was stale) or it was the very last entry of the directory. Return
                // an empty buffer so the guest stops iterating instead of looping forever.
                break;
            }

            if found {
                // Already past the target entry, this batch is the reply.
                break;
            }

            if skip_to_cookie(&mut buf, offset) {
                // Consumed everything up to and including the target entry. If it was the
                // last record of this batch, fetch the next one: returning an empty reply
                // here would falsely signal end-of-directory.
                found = true;
                if !buf.is_empty() {
                    break;
                }
            } else {
                buf.clear();
            }
        }
    }

    Ok(buf)
}
