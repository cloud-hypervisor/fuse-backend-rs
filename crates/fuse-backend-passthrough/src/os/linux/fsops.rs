// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Thin Linux syscall shims backing the passthrough file operations:
//! `stat_fd`, `sync_fd`, `fstatvfs`, `fchown`, `lseek`, `renameat2`,
//! `linkat_by_fd`, `fallocate64`, the raw `copy_file_range` syscall and the
//! xattr operations.
//!
//! The xattr operations work through a `/proc/self/fd/<fd>` path because the
//! `f{set,get,remove,list}xattr` functions reject descriptors opened with
//! `O_PATH`.

use std::ffi::{CStr, CString};
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::{AsRawFd, RawFd};

use fuse_backend_core::abi::fuse_abi as fuse;
use fuse_backend_core::api::filesystem::{GetxattrReply, ListxattrReply};
use fuse_backend_core::api::EMPTY_CSTR;

/// Query filesystem statistics for the filesystem backing `fd`.
pub(crate) fn fstatvfs(fd: RawFd) -> io::Result<fuse::statvfs64> {
    let mut out = MaybeUninit::<fuse::statvfs64>::zeroed();

    // Safe because the kernel will only write data in `out` and we check the
    // return value.
    let res = unsafe { libc::fstatvfs64(fd, out.as_mut_ptr()) };
    if res == 0 {
        // Safe because the kernel guarantees that the struct is now fully initialized.
        Ok(unsafe { out.assume_init() })
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Change the owner of the file referenced by `fd` to `(uid, gid)`.
///
/// `uid` or `gid` equal to `u32::MAX` (i.e. `(uid_t)-1`) leaves the respective
/// id unchanged.
pub(crate) fn fchown_by_fd(fd: RawFd, uid: u32, gid: u32) -> io::Result<()> {
    // Safe because this is a constant value and a valid C string.
    let empty = unsafe { CStr::from_bytes_with_nul_unchecked(b"\0") };

    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        libc::fchownat(
            fd,
            empty.as_ptr(),
            uid,
            gid,
            libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
        )
    };
    if res < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(())
    }
}

/// Create a hard link named `newname` in directory `newdir_fd` to the file
/// referenced by `fd`.
///
/// `mode` is the cached file type of the linked inode (used to reject
/// linking a symlink through the `/proc/self/fd` fallback, which would link
/// the symlink's target instead); `proc_self_fd` is the daemon's fd for
/// `/proc/self/fd`.
pub(crate) fn linkat_by_fd(
    fd: RawFd,
    proc_self_fd: RawFd,
    mode: u32,
    newdir_fd: RawFd,
    newname: &CStr,
) -> io::Result<()> {
    // Safe because this is a constant value and a valid C string.
    let empty = unsafe { CStr::from_bytes_with_nul_unchecked(b"\0") };

    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        libc::linkat(
            fd,
            empty.as_ptr(),
            newdir_fd,
            newname.as_ptr(),
            libc::AT_EMPTY_PATH,
        )
    };
    if res == 0 {
        return Ok(());
    }

    let err = io::Error::last_os_error();
    // linkat() with AT_EMPTY_PATH requires CAP_DAC_READ_SEARCH,
    // which unprivileged daemons don't have, and the kernel reports
    // the missing capability as ENOENT. Retry through /proc/self/fd,
    // following the magic symlink to the file the fd refers to.
    if err.raw_os_error() != Some(libc::ENOENT) {
        return Err(err);
    }

    // The retry cannot link a symlink itself: following the
    // magic symlink resolves to the link target, so the new
    // name would point at the target instead of the symlink.
    // Report the missing capability instead of linking the
    // wrong file. The file type cannot change for a live
    // inode, so the cached mode is reliable here.
    if (mode & libc::S_IFMT) == libc::S_IFLNK {
        return Err(io::Error::from_raw_os_error(libc::EPERM));
    }
    let oldpath = CString::new(format!("{}", fd))
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        libc::linkat(
            proc_self_fd,
            oldpath.as_ptr(),
            newdir_fd,
            newname.as_ptr(),
            libc::AT_SYMLINK_FOLLOW,
        )
    };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Rename `oldpath` under `olddir_fd` to `newpath` under `newdir_fd`,
/// honoring the `RENAME_*` flags carried by the FUSE protocol.
pub(crate) fn renameat2(
    olddir_fd: RawFd,
    oldpath: &CStr,
    newdir_fd: RawFd,
    newpath: &CStr,
    flags: u32,
) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    // TODO: Switch to libc::renameat2 once https://github.com/rust-lang/libc/pull/1508 lands
    // and we have glibc 2.28.
    let res = unsafe {
        libc::syscall(
            libc::SYS_renameat2,
            olddir_fd,
            oldpath.as_ptr(),
            newdir_fd,
            newpath.as_ptr(),
            flags,
        )
    };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

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

/// Stat `path` (or `dir` itself when `path` is `None`) relative to `dir`.
///
/// Both cases go through `fstatat64()` with `AT_EMPTY_PATH`.
pub(crate) fn stat_fd(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<fuse::stat64> {
    // Safe because this is a constant value and a valid C string.
    let pathname =
        path.unwrap_or_else(|| unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) });
    let mut st = MaybeUninit::<fuse::stat64>::zeroed();

    // Safe because the kernel will only write data in `st` and we check the return value.
    let res = unsafe {
        libc::fstatat64(
            dir.as_raw_fd(),
            pathname.as_ptr(),
            st.as_mut_ptr(),
            libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
        )
    };
    if res >= 0 {
        // Safe because the kernel guarantees that the struct is now fully initialized.
        Ok(unsafe { st.assume_init() })
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Flush the file data (and metadata, unless `datasync` is set) of `fd`.
pub(crate) fn sync_fd(fd: &impl AsRawFd, datasync: bool) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        if datasync {
            libc::fdatasync(fd.as_raw_fd())
        } else {
            libc::fsync(fd.as_raw_fd())
        }
    };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}
