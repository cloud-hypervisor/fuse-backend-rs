// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Thin Linux syscall shims backing the passthrough file operations:
//! `fallocate64`, the raw `copy_file_range` syscall and the xattr operations.
//!
//! The xattr operations work through a `/proc/self/fd/<fd>` path because the
//! `f{set,get,remove,list}xattr` functions reject descriptors opened with
//! `O_PATH`.

use std::ffi::{CStr, CString};
use std::io;
use std::os::unix::io::RawFd;

use fuse_backend_core::api::filesystem::{GetxattrReply, ListxattrReply};

/// Position the descriptor `fd` at `offset`, interpreting `whence` as the raw
/// `SEEK_*` value carried by the FUSE protocol.
pub(crate) fn lseek(fd: RawFd, offset: u64, whence: u32) -> io::Result<u64> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::lseek(fd, offset as libc::off64_t, whence as libc::c_int) };
    if res < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(res as u64)
    }
}

/// Preallocate or deallocate disk space for the file referenced by `fd`.
pub(crate) fn fallocate64(fd: RawFd, mode: u32, offset: u64, length: u64) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        libc::fallocate64(
            fd,
            mode as libc::c_int,
            offset as libc::off64_t,
            length as libc::off64_t,
        )
    };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Copy `len` bytes between the two descriptors at the given offsets through
/// the raw `copy_file_range` syscall, returning the number of bytes copied.
///
/// The two offset locals are owned by this function, so the backing files'
/// own positions are neither read nor advanced.
pub(crate) fn copy_file_range(
    fd_in: RawFd,
    offset_in: u64,
    fd_out: RawFd,
    offset_out: u64,
    len: usize,
    flags: u64,
) -> io::Result<usize> {
    let mut off_in: libc::loff_t = offset_in as libc::loff_t;
    let mut off_out: libc::loff_t = offset_out as libc::loff_t;

    // Safe because the only memory this modifies is the two offset locals
    // which we own, and we check the return value.
    let res = unsafe {
        libc::syscall(
            libc::SYS_copy_file_range,
            fd_in,
            &mut off_in as *mut libc::loff_t,
            fd_out,
            &mut off_out as *mut libc::loff_t,
            len,
            flags as libc::c_uint,
        )
    };
    if res < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(res as usize)
    }
}

/// Build the `/proc/self/fd/<fd>` path through which the xattr operations
/// below reach files opened with `O_PATH`.
fn xattr_pathname(fd: RawFd) -> io::Result<CString> {
    CString::new(format!("/proc/self/fd/{}", fd))
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
}

/// Set the extended attribute `name` of the file referenced by `fd`.
pub(crate) fn setxattr(fd: RawFd, name: &CStr, value: &[u8], flags: u32) -> io::Result<()> {
    let pathname = xattr_pathname(fd)?;

    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        libc::setxattr(
            pathname.as_ptr(),
            name.as_ptr(),
            value.as_ptr() as *const libc::c_void,
            value.len(),
            flags as libc::c_int,
        )
    };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Get the extended attribute `name` of the file referenced by `fd`.
pub(crate) fn getxattr(fd: RawFd, name: &CStr, size: u32) -> io::Result<GetxattrReply> {
    let pathname = xattr_pathname(fd)?;
    let mut buf = Vec::<u8>::with_capacity(size as usize);

    // Safe because this will only modify the contents of `buf`.
    let res = unsafe {
        libc::getxattr(
            pathname.as_ptr(),
            name.as_ptr(),
            buf.as_mut_ptr() as *mut libc::c_void,
            size as libc::size_t,
        )
    };
    if res < 0 {
        return Err(io::Error::last_os_error());
    }

    if size == 0 {
        Ok(GetxattrReply::Count(res as u32))
    } else {
        // Safe because we trust the value returned by kernel.
        unsafe { buf.set_len(res as usize) };
        Ok(GetxattrReply::Value(buf))
    }
}

/// List the extended attribute names of the file referenced by `fd`.
pub(crate) fn listxattr(fd: RawFd, size: u32) -> io::Result<ListxattrReply> {
    let pathname = xattr_pathname(fd)?;
    let mut buf = Vec::<u8>::with_capacity(size as usize);

    // Safe because this will only modify the contents of `buf`.
    let res = unsafe {
        libc::listxattr(
            pathname.as_ptr(),
            buf.as_mut_ptr() as *mut libc::c_char,
            size as libc::size_t,
        )
    };
    if res < 0 {
        return Err(io::Error::last_os_error());
    }

    if size == 0 {
        Ok(ListxattrReply::Count(res as u32))
    } else {
        // Safe because we trust the value returned by kernel.
        unsafe { buf.set_len(res as usize) };
        Ok(ListxattrReply::Names(buf))
    }
}

/// Remove the extended attribute `name` from the file referenced by `fd`.
pub(crate) fn removexattr(fd: RawFd, name: &CStr) -> io::Result<()> {
    let pathname = xattr_pathname(fd)?;

    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::removexattr(pathname.as_ptr(), name.as_ptr()) };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}
