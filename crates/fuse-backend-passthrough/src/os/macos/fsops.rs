// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS file-operation syscall shims.
//!
//! Implements the shims that have a portable macOS equivalent — `stat_fd`,
//! `sync_fd`, `fstatvfs`, `fchown`, `lseek` and plain `renameat` — and answers
//! `ENOSYS` for the Linux-only ones: `fallocate` (macOS has no
//! `fallocate(2)`), the raw `copy_file_range` syscall, `AT_EMPTY_PATH`-based
//! hard links and the `/proc/self/fd` path behind the xattr shims.  A macOS
//! mount thus fails cleanly on those operations instead of half-working; the
//! future port can fill them with real macOS equivalents (e.g. the
//! `f{set,get,remove,list}xattr` family and `F_PREALLOCATE`).

use std::ffi::CStr;
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::{AsRawFd, RawFd};

use fuse_backend_core::abi::fuse_abi as fuse;
use fuse_backend_core::api::filesystem::{GetxattrReply, ListxattrReply};

use crate::util::enosys;

/// Query filesystem statistics for the filesystem backing `fd`.
pub(crate) fn fstatvfs(fd: RawFd) -> io::Result<fuse::statvfs64> {
    let mut out = MaybeUninit::<fuse::statvfs64>::zeroed();

    // Safe because the kernel will only write data in `out` and we check the
    // return value.
    let res = unsafe { libc::fstatvfs(fd, out.as_mut_ptr()) };
    if res == 0 {
        // Safe because the kernel guarantees that the struct is now fully initialized.
        Ok(unsafe { out.assume_init() })
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Stat `path` (or `dir` itself when `path` is `None`) relative to `dir`.
///
/// macOS has no `AT_EMPTY_PATH`, so the fd case uses `fstat()` and the path
/// case `fstatat()`.
pub(crate) fn stat_fd(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<fuse::stat64> {
    let mut st = MaybeUninit::<fuse::stat64>::zeroed();

    // Safe because the kernel will only write data in `st` and we check the
    // return value.
    let res = match path {
        None => unsafe { libc::fstat(dir.as_raw_fd(), st.as_mut_ptr()) },
        Some(path) => unsafe {
            libc::fstatat(
                dir.as_raw_fd(),
                path.as_ptr(),
                st.as_mut_ptr(),
                libc::AT_SYMLINK_NOFOLLOW,
            )
        },
    };
    if res >= 0 {
        // Safe because the kernel guarantees that the struct is now fully initialized.
        Ok(unsafe { st.assume_init() })
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Flush the file data (and metadata, unless `datasync` is set) of `fd`.
///
/// macOS has no `fdatasync()`, so both flavors degenerate to `fsync()`.
pub(crate) fn sync_fd(fd: &impl AsRawFd, _datasync: bool) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::fsync(fd.as_raw_fd()) };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Change the owner of the file referenced by `fd` to `(uid, gid)`.
///
/// `uid` or `gid` equal to `u32::MAX` (i.e. `(uid_t)-1`) leaves the respective
/// id unchanged.
pub(crate) fn fchown_by_fd(fd: RawFd, uid: u32, gid: u32) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::fchown(fd, uid, gid) };
    if res < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// Create a hard link named `newname` in directory `newdir_fd` to the file
/// referenced by `fd`.
///
/// `ENOSYS`: macOS has no `AT_EMPTY_PATH` for `linkat()` and no
/// `/proc/self/fd` magic symlinks to fall back on, so a file cannot be
/// linked by descriptor.
pub(crate) fn linkat_by_fd(
    _fd: RawFd,
    _proc_self_fd: RawFd,
    _mode: u32,
    _newdir_fd: RawFd,
    _newname: &CStr,
) -> io::Result<()> {
    Err(enosys())
}

/// Rename `oldpath` under `olddir_fd` to `newpath` under `newdir_fd`,
/// honoring the `RENAME_*` flags carried by the FUSE protocol.
///
/// Plain renames map to `renameat()`; the flag-carrying variants
/// (`RENAME_NOREPLACE`, `RENAME_EXCHANGE`, `RENAME_WHITEOUT`) need Linux's
/// `renameat2()`, which macOS lacks.
pub(crate) fn renameat2(
    olddir_fd: RawFd,
    oldpath: &CStr,
    newdir_fd: RawFd,
    newpath: &CStr,
    flags: u32,
) -> io::Result<()> {
    if flags != 0 {
        return Err(enosys());
    }

    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::renameat(olddir_fd, oldpath.as_ptr(), newdir_fd, newpath.as_ptr()) };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Position the descriptor `fd` at `offset`, interpreting `whence` as the raw
/// `SEEK_*` value carried by the FUSE protocol.
pub(crate) fn lseek(fd: RawFd, offset: u64, whence: u32) -> io::Result<u64> {
    // The FUSE protocol carries Linux's SEEK_* values, where 3 is SEEK_DATA
    // and 4 is SEEK_HOLE. Darwin defines the two the other way around
    // (SEEK_HOLE is 3, SEEK_DATA is 4), so translate them instead of passing
    // the wire value through; 0/1/2 coincide on both systems.
    let whence = match whence {
        3 => libc::SEEK_DATA,
        4 => libc::SEEK_HOLE,
        w => w as libc::c_int,
    };
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::lseek(fd, offset as libc::off_t, whence) };
    if res < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(res as u64)
    }
}

/// Preallocate or deallocate disk space for the file referenced by `fd`.
///
/// `ENOSYS`: macOS has no `fallocate()`; the closest analog is the
/// `F_PREALLOCATE` `fcntl`, which the port will wire up.
pub(crate) fn fallocate64(_fd: RawFd, _mode: u32, _offset: u64, _length: u64) -> io::Result<()> {
    Err(enosys())
}

/// Copy `len` bytes between the two descriptors at the given offsets through
/// the raw `copy_file_range` syscall, returning the number of bytes copied.
///
/// The two offset locals are owned by this function, so the backing files'
/// own positions are neither read nor advanced.
///
/// `ENOSYS`: macOS has no `copy_file_range()`; `fcopyfile()` is the analog
/// for the port to wire up.
pub(crate) fn copy_file_range(
    _fd_in: RawFd,
    _offset_in: u64,
    _fd_out: RawFd,
    _offset_out: u64,
    _len: usize,
    _flags: u64,
) -> io::Result<usize> {
    Err(enosys())
}

/// Set the extended attribute `name` of the file referenced by `fd`.
///
/// `ENOSYS`: the Linux shim reaches the file through `/proc/self/fd`, which
/// macOS lacks; the port will use the `fsetxattr()` family instead.
pub(crate) fn setxattr(_fd: RawFd, _name: &CStr, _value: &[u8], _flags: u32) -> io::Result<()> {
    Err(enosys())
}

/// Get the extended attribute `name` of the file referenced by `fd`.
///
/// `ENOSYS`; see [`setxattr`].
pub(crate) fn getxattr(_fd: RawFd, _name: &CStr, _size: u32) -> io::Result<GetxattrReply> {
    Err(enosys())
}

/// List the extended attribute names of the file referenced by `fd`.
///
/// `ENOSYS`; see [`setxattr`].
pub(crate) fn listxattr(_fd: RawFd, _size: u32) -> io::Result<ListxattrReply> {
    Err(enosys())
}

/// Remove the extended attribute `name` from the file referenced by `fd`.
///
/// `ENOSYS`; see [`setxattr`].
pub(crate) fn removexattr(_fd: RawFd, _name: &CStr) -> io::Result<()> {
    Err(enosys())
}
