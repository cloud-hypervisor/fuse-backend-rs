// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS file-operation syscall shims.
//!
//! Implements the shims that have a portable macOS equivalent — `stat_fd`,
//! `sync_fd`, `fstatvfs`, `fchown`, `lseek`, `getpath_by_fd`, plain
//! `renameat` and the xattr family — and answers
//! `ENOSYS` for the Linux-only ones: `fallocate` (macOS has no
//! `fallocate(2)`), the raw `copy_file_range` syscall and
//! `AT_EMPTY_PATH`-based hard links.  A macOS
//! mount thus fails cleanly on those operations instead of half-working.

use std::ffi::{CStr, CString};
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

/// Get the absolute pathname of the file referenced by `fd` via
/// `fcntl(F_GETPATH)`.
///
/// The descriptor pins the file's vnode, and the kernel keeps the vnode's
/// name chain up to date, so the returned path is the file's *current* path:
/// renames of the file, or of any directory above it, are reflected.  For a
/// file with no remaining path (i.e. unlinked), the last known path is
/// returned; opening it fails with `ENOENT`.  This is macOS's only way back
/// from a descriptor to a path — there is no `/proc/self/fd`.
pub(crate) fn getpath_by_fd(fd: &impl AsRawFd) -> io::Result<CString> {
    // F_GETPATH requires a buffer of at least MAXPATHLEN bytes and
    // NUL-terminates the path inside it.
    let mut buf = vec![0u8; libc::PATH_MAX as usize];

    // Safe because the kernel will only write up to PATH_MAX bytes into `buf`
    // and we check the return value.
    let res = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_GETPATH, buf.as_mut_ptr()) };
    if res < 0 {
        return Err(io::Error::last_os_error());
    }

    let len = buf.iter().position(|&b| b == 0).unwrap_or(buf.len());
    buf.truncate(len);
    CString::new(buf).map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))
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
/// Darwin's `fsetxattr()` accepts the `O_EVTONLY` descriptors the handle map
/// hands out (unlike Linux, where the `O_PATH` handles force the xattr
/// operations through `/proc/self/fd`), so the fd-based call needs no path
/// dance.  `flags` is passed through verbatim: macFUSE's kernel forwards the
/// macOS caller's `XATTR_*` options (Darwin values, e.g. `XATTR_CREATE` and
/// `XATTR_REPLACE`, which differ from Linux's) to `FUSE_SETXATTR` unchanged,
/// so translating them here would corrupt them.  The same symmetry holds for
/// errnos: Darwin reports a missing attribute as `ENOATTR`, and the kernel
/// passes it back to the macOS caller unchanged.
pub(crate) fn setxattr(fd: RawFd, name: &CStr, value: &[u8], flags: u32) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe {
        libc::fsetxattr(
            fd,
            name.as_ptr(),
            value.as_ptr() as *const libc::c_void,
            value.len(),
            0,
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
///
/// Like the Linux twin, a `size` of 0 turns the call into a size query; see
/// [`setxattr`] for the fd and errno conventions.
pub(crate) fn getxattr(fd: RawFd, name: &CStr, size: u32) -> io::Result<GetxattrReply> {
    let mut buf = Vec::<u8>::with_capacity(size as usize);

    // Safe because this will only modify the contents of `buf`.
    let res = unsafe {
        libc::fgetxattr(
            fd,
            name.as_ptr(),
            buf.as_mut_ptr() as *mut libc::c_void,
            size as libc::size_t,
            0,
            0,
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
///
/// Like the Linux twin, a `size` of 0 turns the call into a size query; see
/// [`setxattr`] for the fd and errno conventions.
pub(crate) fn listxattr(fd: RawFd, size: u32) -> io::Result<ListxattrReply> {
    let mut buf = Vec::<u8>::with_capacity(size as usize);

    // Safe because this will only modify the contents of `buf`.
    let res = unsafe {
        libc::flistxattr(
            fd,
            buf.as_mut_ptr() as *mut libc::c_char,
            size as libc::size_t,
            0,
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
///
/// See [`setxattr`] for the fd and errno conventions.
pub(crate) fn removexattr(fd: RawFd, name: &CStr) -> io::Result<()> {
    // Safe because this doesn't modify any memory and we check the return value.
    let res = unsafe { libc::fremovexattr(fd, name.as_ptr(), 0) };
    if res == 0 {
        Ok(())
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::fd::FromRawFd;
    use vmm_sys_util::tempdir::TempDir;

    /// Open `path` with `flags` and hand back an owned descriptor, so the
    /// tests close what they open.
    fn open_owned(path: &CStr, flags: libc::c_int) -> fs::File {
        // Safe because `path` is a valid NUL-terminated string, this does
        // not modify any memory, and we check the return value.
        let fd = unsafe { libc::open(path.as_ptr(), flags) };
        assert!(fd >= 0);
        // Safe because we just opened this fd.
        unsafe { fs::File::from_raw_fd(fd) }
    }

    #[test]
    fn test_getpath_by_fd() {
        let dir = TempDir::new().unwrap();
        let path = dir.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        let file = fs::File::open(&path).unwrap();
        let path = getpath_by_fd(&file).unwrap();
        assert!(path.to_string_lossy().ends_with("file.txt"));

        // The derived path must name the same file as the descriptor.
        let st1 = stat_fd(&file, None).unwrap();
        let reopened = fs::File::open(path.to_string_lossy().as_ref()).unwrap();
        let st2 = stat_fd(&reopened, None).unwrap();
        assert_eq!(st1.st_dev, st2.st_dev);
        assert_eq!(st1.st_ino, st2.st_ino);
    }

    #[test]
    fn test_xattr_roundtrip_on_evtonly_fd() {
        let dir = TempDir::new().unwrap();
        let path = dir.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        // The handle map hands out O_EVTONLY descriptors; the fd-based xattr
        // calls must work on them.
        let cpath = path
            .to_str()
            .and_then(|p| CString::new(p).ok())
            .expect("valid path");
        let file = open_owned(&cpath, libc::O_EVTONLY);
        let fd = file.as_raw_fd();
        let name = CStr::from_bytes_with_nul(b"user.probe\0").unwrap();

        setxattr(fd, name, b"value", 0).unwrap();
        match getxattr(fd, name, 16).unwrap() {
            GetxattrReply::Value(v) => assert_eq!(v, b"value"),
            GetxattrReply::Count(_) => panic!("expected a value"),
        }
        // size == 0 is the size-query form.
        match getxattr(fd, name, 0).unwrap() {
            GetxattrReply::Count(n) => assert_eq!(n, 5),
            GetxattrReply::Value(_) => panic!("expected a count"),
        }
        match listxattr(fd, 256).unwrap() {
            ListxattrReply::Names(names) => {
                assert!(names.split(|&b| b == 0).any(|n| n == b"user.probe"))
            }
            ListxattrReply::Count(_) => panic!("expected names"),
        }
        removexattr(fd, name).unwrap();
        // A missing attribute is ENOATTR, the errno the macFUSE kernel
        // passes back to the (macOS) caller verbatim.
        let err = match getxattr(fd, name, 16) {
            Err(e) => e,
            Ok(_) => panic!("expected an error for a missing attribute"),
        };
        assert_eq!(err.raw_os_error(), Some(libc::ENOATTR));
        let err = removexattr(fd, name).unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ENOATTR));

        // Darwin's XATTR_* option values (what macFUSE puts on the wire)
        // pass through verbatim: CREATE on an existing attribute is EEXIST,
        // REPLACE on a missing one is ENOATTR.
        setxattr(fd, name, b"value", 0).unwrap();
        let err = setxattr(fd, name, b"other", libc::XATTR_CREATE as u32).unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::EEXIST));
        removexattr(fd, name).unwrap();
        let err = setxattr(fd, name, b"other", libc::XATTR_REPLACE as u32).unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ENOATTR));
    }
}
