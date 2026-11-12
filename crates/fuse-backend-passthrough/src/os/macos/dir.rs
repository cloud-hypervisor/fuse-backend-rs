// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS directory-walk seam.
//!
//! macOS has no `getdents64()`; directory enumeration goes through
//! `fdopendir()`/`readdir()`.  [`getdents64`] walks the directory that way
//! and synthesizes a `getdents64`-format buffer, so the shared `do_readdir`
//! consumes the same records as on Linux.  Darwin hands out no usable
//! directory cookies (see [`getdents64`] for the details), so the seam
//! issues its own entry-index cookies and resumes by rewinding and skipping.

// API-parity twin: `skip_to_cookie` is only reached through the portable
// tests; the macOS walk resumes by rewinding and counting entries, so it
// needs no cookie-scan fallback.
#![allow(dead_code)]

use std::ffi::CStr;
use std::io;
use std::mem::size_of;
use std::os::unix::io::RawFd;
use std::ptr;

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
/// `dir_fd`, resuming at cookie `offset`, as a `getdents64`-format buffer.
///
/// Darwin hands out no usable directory cookies: `readdir()`'s `d_seekoff`
/// reads zero on APFS, `telldir()` cookies index the current `DIR` stream's
/// private state (a fresh stream cannot seek to them), and
/// `getdirentries()`'s basep cookies are opaque batch positions.  So this
/// seam issues its own: every entry — including "." and ".." — is numbered
/// 1, 2, 3, ... in walk order, and an entry's `d_off` is its number.
/// Resuming at cookie `offset` means rewinding (`lseek(fd, 0, SEEK_SET)`
/// restarts a Darwin directory walk deterministically), skipping the first
/// `offset` entries, and returning the rest up to `size` bytes.  A resume
/// costs O(offset) — the price of correctness where the filesystem offers
/// no real cookies.
///
/// `cookie_hit` reports whether the caller's cookie cache already consumed
/// the batch ending at `offset`.  Positions are re-derived from index 0 on
/// every call here, so it changes nothing and is ignored.
///
/// The index cookies are only stable while the directory is unchanged: an
/// entry removed before the resume cookie shifts every later index down (a
/// later entry is silently skipped) and an insertion shifts them up (an
/// entry is repeated) across batches.  POSIX permits exactly this for
/// `readdir()` across `seekdir()`-style resumes, and Linux's hash-based
/// cookies mostly avoid it; the alternative — pinning entries — is not
/// available through the Darwin directory interface.
///
/// The caller must hold the file lock of the directory stream: the walk
/// below duplicates `dir_fd`, and the duplicate shares the caller's
/// open-file offset while it runs.
pub(crate) fn getdents64(
    dir_fd: RawFd,
    _cookie_hit: bool,
    offset: u64,
    size: u32,
) -> io::Result<Vec<u8>> {
    let mut buf = Vec::<u8>::with_capacity(size as usize);

    // fdopendir() takes ownership of the descriptor it is given (closedir()
    // closes it), while `dir_fd` stays owned by the caller; duplicate the
    // descriptor first.
    //
    // Safe because this doesn't modify any memory and we check the return
    // value.
    let dup_fd = unsafe { libc::dup(dir_fd) };
    if dup_fd < 0 {
        return Err(io::Error::last_os_error());
    }

    // Rewind to the start of the walk: on a Darwin directory descriptor
    // this restarts the enumeration deterministically, in the same order as
    // every previous walk.
    //
    // Safe because this doesn't modify any memory and we check the return
    // value.
    let res = unsafe { libc::lseek(dup_fd, 0, libc::SEEK_SET) };
    if res < 0 {
        let err = io::Error::last_os_error();
        // Safe because `dup_fd` is a valid descriptor just returned by
        // dup(), not yet handed to fdopendir().
        unsafe { libc::close(dup_fd) };
        return Err(err);
    }

    // Safe because `dup_fd` is a valid directory descriptor just rewound
    // by lseek().
    let dir = unsafe { libc::fdopendir(dup_fd) };
    if dir.is_null() {
        let err = io::Error::last_os_error();
        // Safe because fdopendir() failed, so `dup_fd` is still ours to
        // close.
        unsafe { libc::close(dup_fd) };
        return Err(err);
    }

    // The number of entries consumed so far, i.e. the cookie of the entry
    // readdir() just handed out.
    let mut index: u64 = 0;
    loop {
        // Safe because this doesn't modify any memory and readdir() returns
        // a pointer into the DIR stream's own buffer that stays valid until
        // the next call.
        unsafe { *libc::__error() = 0 };
        let entry_ptr = unsafe { libc::readdir(dir) };
        if entry_ptr.is_null() {
            // readdir() returns NULL both at end-of-directory and on error;
            // a set errno distinguishes them (EOF leaves the cleared errno
            // untouched).  Treating an error as EOF would hand the caller a
            // truncated listing as success, where Linux's getdents64()
            // fails the syscall instead.
            if unsafe { *libc::__error() } != 0 {
                let err = io::Error::last_os_error();
                // Safe because `dir` was created by fdopendir().
                unsafe { libc::closedir(dir) };
                return Err(err);
            }
            break;
        }
        index += 1;
        if index <= offset {
            // An entry at or before the resume cookie was consumed in an
            // earlier batch: skip it.
            continue;
        }
        // Copy only the fields actually used, field by field: readdir()
        // returns a variable-sized record (the real `d_reclen`), while
        // `libc::dirent` declares `d_name` as a full [1024] array, so a
        // whole-struct read would run past the end of the record.  The
        // pointer stays valid until the next readdir() call and each field
        // is read within the bounds readdir() guarantees.
        //
        // Safe because d_name is NUL-terminated.
        let (d_ino, d_type) = unsafe {
            (
                ptr::addr_of!((*entry_ptr).d_ino).read(),
                ptr::addr_of!((*entry_ptr).d_type).read(),
            )
        };
        let name =
            unsafe { CStr::from_ptr(ptr::addr_of!((*entry_ptr).d_name) as *const libc::c_char) }
                .to_bytes();

        let record_len = dirent64_reclen(name.len());
        if buf.len() + record_len > size as usize {
            if buf.is_empty() {
                // Mirrors the Linux getdents64(): a reply too small for even
                // one entry is EINVAL.  Not reachable through FUSE (reply
                // buffers are page-sized), just parity.
                //
                // Safe because `dir` was created by fdopendir().
                unsafe { libc::closedir(dir) };
                return Err(io::Error::from_raw_os_error(libc::EINVAL));
            }
            // The caller's buffer is full; the entry stays unread for the
            // resume, which skips exactly `index - 1` entries.
            break;
        }

        let start = buf.len();
        // Serialize the packed header field by field; `LinuxDirent64` is
        // `repr(packed)`, so a struct-to-slice copy would need to dance
        // around unaligned references anyway.
        let mut header = [0u8; size_of::<LinuxDirent64>()];
        header[0..8].copy_from_slice(&d_ino.to_le_bytes());
        header[8..16].copy_from_slice(&index.to_le_bytes());
        header[16..18].copy_from_slice(&(record_len as u16).to_le_bytes());
        header[18] = d_type;
        buf.extend_from_slice(&header);
        buf.extend_from_slice(name);
        // NUL-terminate the name and pad the record to `record_len`, the
        // way the Linux getdents64() does.
        buf.resize(start + record_len, 0);
    }

    // Safe because `dir` was created by fdopendir(); this closes the
    // duplicated descriptor only, `dir_fd` stays valid.
    unsafe { libc::closedir(dir) };

    Ok(buf)
}

/// Record length of a `getdents64` entry for a name of `namelen` bytes: the
/// 19-byte header, the name, its NUL terminator, all padded to 8-byte
/// alignment — the layout the shared `do_readdir()` parser (and the Linux
/// kernel's `filldir64()`) expects.
fn dirent64_reclen(namelen: usize) -> usize {
    (size_of::<LinuxDirent64>() + namelen + 1 + 7) & !7
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::os::fd::AsRawFd;

    /// Decode a getdents64 buffer into (ino, cookie, type, name) tuples.
    fn decode(buf: &[u8]) -> Vec<(u64, u64, u8, String)> {
        let mut out = Vec::new();
        let mut cur = 0;
        while cur + size_of::<LinuxDirent64>() <= buf.len() {
            let dirent64 =
                LinuxDirent64::from_slice(&buf[cur..cur + size_of::<LinuxDirent64>()]).unwrap();
            let reclen = dirent64.d_reclen as usize;
            assert!(reclen >= size_of::<LinuxDirent64>() && cur + reclen <= buf.len());
            // Records are padded to 8-byte alignment.
            assert_eq!(reclen & 7, 0);
            let namelen = reclen - size_of::<LinuxDirent64>();
            let name = &buf[cur + size_of::<LinuxDirent64>()..cur + reclen];
            // The name is NUL-terminated inside the padded area.
            assert_eq!(name[namelen - 1], 0);
            let name = name[..name.iter().position(|&b| b == 0).unwrap()].to_vec();
            out.push((
                dirent64.d_ino,
                dirent64.d_off as u64,
                dirent64.d_ty,
                String::from_utf8(name).unwrap(),
            ));
            cur += reclen;
        }
        assert_eq!(cur, buf.len());
        out
    }

    #[test]
    fn test_getdents64_walk_and_resume() {
        let dir = vmm_sys_util::tempdir::TempDir::new().unwrap();
        std::fs::write(dir.as_path().join("a.txt"), "a").unwrap();
        std::fs::write(dir.as_path().join("b.txt"), "b").unwrap();
        std::fs::create_dir(dir.as_path().join("subdir")).unwrap();

        let fd = File::open(dir.as_path()).unwrap();

        // Full walk from the start.
        let entries = decode(&getdents64(fd.as_raw_fd(), false, 0, 4096).unwrap());
        assert!(entries.len() >= 5); // ".", ".." and the three entries
        let names: Vec<&str> = entries.iter().map(|(_, _, _, n)| n.as_str()).collect();
        assert!(names.contains(&"a.txt"));
        assert!(names.contains(&"b.txt"));
        assert!(names.contains(&"subdir"));
        // Cookies strictly increase, and the entry types are the BSD/Linux
        // DT_* values.
        assert!(entries.windows(2).all(|w| w[0].1 < w[1].1));
        // Cookies are self-issued entry indexes: 1, 2, 3, ... in walk
        // order, counting "." and ".." like every other entry.
        for (i, e) in entries.iter().enumerate() {
            assert_eq!(e.1, (i + 1) as u64);
        }
        let subdir = entries.iter().find(|(_, _, _, n)| n == "subdir").unwrap();
        assert_eq!(subdir.2, libc::DT_DIR);
        let a = entries.iter().find(|(_, _, _, n)| n == "a.txt").unwrap();
        assert_eq!(a.2, libc::DT_REG);

        // Resume from the first entry's cookie: exactly the entries after
        // it.  (Readdir order on APFS is hash order, so no entry but the
        // first is guaranteed not to be last.)
        let mut rest = decode(&getdents64(fd.as_raw_fd(), false, entries[0].1, 4096).unwrap());
        assert_eq!(rest.len(), entries.len() - 1);
        let after_first: Vec<&str> = entries[1..].iter().map(|(_, _, _, n)| n.as_str()).collect();
        let got: Vec<&str> = rest.iter().map(|(_, _, _, n)| n.as_str()).collect();
        assert_eq!(got, after_first);

        // Resume from the last cookie of that batch: end of directory.
        let last = rest.pop().unwrap();
        assert!(getdents64(fd.as_raw_fd(), false, last.1, 4096)
            .unwrap()
            .is_empty());

        // The cookie_hit fast path is advisory and ignored here: the result
        // is derived from the rewind-and-skip, not the descriptor position.
        let batch = getdents64(fd.as_raw_fd(), false, 0, 4096).unwrap();
        let entries = decode(&batch);
        let last = entries.last().unwrap().1;
        assert!(getdents64(fd.as_raw_fd(), true, last, 4096)
            .unwrap()
            .is_empty());
    }

    #[test]
    fn test_getdents64_pagination() {
        let dir = vmm_sys_util::tempdir::TempDir::new().unwrap();
        std::fs::write(dir.as_path().join("a.txt"), "a").unwrap();
        std::fs::write(dir.as_path().join("b.txt"), "b").unwrap();
        std::fs::create_dir(dir.as_path().join("subdir")).unwrap();

        let fd = File::open(dir.as_path()).unwrap();

        // Walk with a reply that holds only one record, resuming each batch
        // at the previous batch's last cookie.
        let mut seen = Vec::new();
        let mut cookie = 0u64;
        loop {
            let buf = getdents64(fd.as_raw_fd(), false, cookie, 48).unwrap();
            if buf.is_empty() {
                break;
            }
            let entries = decode(&buf);
            // Every batch holds at least one entry and the walk continues
            // exactly where the previous one stopped.
            assert_eq!(entries[0].1, cookie + 1);
            cookie = entries.last().unwrap().1;
            seen.extend(entries);
        }

        // The paginated walk sees exactly the single-shot walk, in order:
        // the rewind-and-skip resume is position-independent.
        let full = decode(&getdents64(fd.as_raw_fd(), false, 0, 4096).unwrap());
        assert_eq!(seen, full);
    }

    #[test]
    fn test_getdents64_small_reply() {
        let dir = vmm_sys_util::tempdir::TempDir::new().unwrap();
        std::fs::write(dir.as_path().join("a.txt"), "a").unwrap();

        let fd = File::open(dir.as_path()).unwrap();

        // A reply too small for even one record is EINVAL, like the Linux
        // getdents64().
        let err = getdents64(fd.as_raw_fd(), false, 0, 8).unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::EINVAL));
    }
}
