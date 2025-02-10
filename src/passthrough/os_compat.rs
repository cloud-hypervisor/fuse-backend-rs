// Copyright (C) 2020-2022 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
// SPDX-License-Identifier: Apache-2.0

use std::ffi::{CStr, CString};
use std::fs::File;
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, RawFd};

use vm_memory::ByteValued;

use super::util::openat;

#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Default)]
pub struct LinuxDirent64 {
    pub d_ino: libc::ino64_t,
    pub d_off: libc::off64_t,
    pub d_reclen: libc::c_ushort,
    pub d_ty: libc::c_uchar,
}
unsafe impl ByteValued for LinuxDirent64 {}

#[cfg(target_env = "gnu")]
pub use libc::statx as statx_st;

#[cfg(target_env = "gnu")]
pub use libc::{STATX_BASIC_STATS, STATX_MNT_ID};

// musl provides the 'struct statx', but without stx_mnt_id.
// However, the libc crate does not provide libc::statx
// if musl is used. So we add just the required struct and
// constants to make it works.
#[cfg(not(target_env = "gnu"))]
#[repr(C)]
pub struct statx_st_timestamp {
    pub tv_sec: i64,
    pub tv_nsec: u32,
    pub __statx_timestamp_pad1: [i32; 1],
}

#[cfg(not(target_env = "gnu"))]
#[repr(C)]
pub struct statx_st {
    pub stx_mask: u32,
    pub stx_blksize: u32,
    pub stx_attributes: u64,
    pub stx_nlink: u32,
    pub stx_uid: u32,
    pub stx_gid: u32,
    pub stx_mode: u16,
    __statx_pad1: [u16; 1],
    pub stx_ino: u64,
    pub stx_size: u64,
    pub stx_blocks: u64,
    pub stx_attributes_mask: u64,
    pub stx_atime: statx_st_timestamp,
    pub stx_btime: statx_st_timestamp,
    pub stx_ctime: statx_st_timestamp,
    pub stx_mtime: statx_st_timestamp,
    pub stx_rdev_major: u32,
    pub stx_rdev_minor: u32,
    pub stx_dev_major: u32,
    pub stx_dev_minor: u32,
    pub stx_mnt_id: u64,
    __statx_pad2: u64,
    __statx_pad3: [u64; 12],
}

#[cfg(not(target_env = "gnu"))]
pub const STATX_BASIC_STATS: libc::c_uint = 0x07ff;

#[cfg(not(target_env = "gnu"))]
pub const STATX_MNT_ID: libc::c_uint = 0x1000;

pub struct SafeOpenAt {
    has_openat2: bool,
}

impl SafeOpenAt {
    pub fn new() -> Self {
        // Checking for `openat2()` since it first appeared in Linux 5.6.
        // SAFETY: all-zero byte-pattern is a valid `libc::open_how`
        let how: libc::open_how = unsafe { std::mem::zeroed() };
        let cwd = CString::new(".").unwrap();
        // SAFETY: `cwd.as_ptr()` points to a valid NUL-terminated string,
        // and the `how` pointer is a valid pointer to an `open_how` struct.
        let fd = unsafe {
            libc::syscall(
                libc::SYS_openat2,
                libc::AT_FDCWD,
                cwd.as_ptr(),
                std::ptr::addr_of!(how),
                std::mem::size_of::<libc::open_how>(),
            )
        };

        let has_openat2 = fd >= 0;
        if has_openat2 {
            // SAFETY: `fd` is an open file descriptor
            unsafe {
                libc::close(fd as libc::c_int);
            }
        }

        Self { has_openat2 }
    }

    /// An utility function that uses `openat2(2)` to restrict the how the provided pathname
    /// is resolved. It uses the following flags:
    /// - `RESOLVE_IN_ROOT`: Treat the directory referred to by dirfd as the root directory while
    /// resolving pathname. This has the effect as though virtiofsd had used chroot(2) to modify its
    /// root directory to dirfd.
    /// - `RESOLVE_NO_MAGICLINKS`: Disallow all magic-link (i.e., proc(2) link-like files) resolution
    /// during path resolution.
    ///
    /// Additionally, the flags `O_NOFOLLOW` and `O_CLOEXEC` are added.
    ///
    /// # Error
    ///
    /// Will return `Err(errno)` if `openat2(2)` fails, see the man page for details.
    ///
    /// # Safety
    ///
    /// The caller must ensure that dirfd is a valid file descriptor.
    pub fn openat(
        &self,
        dir: &impl AsRawFd,
        path: &CStr,
        flags: libc::c_int,
        mode: u32,
    ) -> io::Result<File> {
        // Fallback to openat
        if !self.has_openat2 {
            return openat(dir, path, flags, mode);
        }

        // `openat2(2)` returns an error if `how.mode` contains bits other than those in range 07777,
        // let's ignore the extra bits to be compatible with `openat(2)`.
        let mode = mode as u64 & 0o7777;

        // SAFETY: all-zero byte-pattern represents a valid `libc::open_how`
        let mut how: libc::open_how = unsafe { std::mem::zeroed() };
        // - RESOLVE_IN_ROOT
        // Treat the directory referred to by dirfd as the root directory while resolving pathname.
        // Absolute symbolic links are interpreted relative to dirfd. If a prefix component of
        // pathname equates to dirfd, then an immediately following .. component likewise equates
        // to dirfd (just as /.. is traditionally equivalent to /).  If pathname is an absolute
        // path, it is also interpreted relative to dirfd.
        //
        // The effect of this flag is as though the calling process had used chroot(2) to
        // (temporarily) modify its root directory (to the directory referred to by dirfd).
        // However, unlike chroot(2) (which changes the filesystem root permanently for a process),
        // RESOLVE_IN_ROOT allows a program to efficiently restrict path resolution on a per-open
        // basis.
        //
        // Currently, this flag also disables magic-link resolution.  However, this may change
        // in the future. Therefore, to ensure that magic links are not resolved, the caller should
        // explicitly specify RESOLVE_NO_MAGICLINKS.
        //
        // - RESOLVE_NO_MAGICLINKS
        // Disallow all magic-link resolution during path resolution.
        //
        // Magic links are symbolic link-like objects that are most notably found in proc(5);
        // examples include /proc/pid/exe and /proc/pid/fd/*.  (See symlink(7) for more details.)
        //
        // Unknowingly opening magic links can be risky for some applications.  Examples of such
        // risks include the following:
        // •  If the process opening a pathname is a controlling process that currently has no
        //    controlling terminal (see credentials(7)), then opening a magic link inside
        //    /proc/pid/fd that happens to refer to a terminal would cause the process to acquire
        //    a controlling terminal.
        //
        // •  In a containerized environment, a magic link inside /proc may refer to an object
        //    outside the container, and thus may provide a means to escape from the container.
        //
        // Because of such risks, an application may prefer to disable magic link resolution using
        // the RESOLVE_NO_MAGICLINKS flag.
        //
        // If the trailing component (i.e., basename) of pathname is a magic link, how.resolve
        // contains RESOLVE_NO_MAGICLINKS, and how.flags contains both O_PATH and O_NOFOLLOW,
        // then an O_PATH file descriptor referencing the magic link will be returned.
        how.resolve = libc::RESOLVE_IN_ROOT | libc::RESOLVE_NO_MAGICLINKS;
        how.flags = flags as u64;
        how.mode = mode;

        // SAFETY: `pathname` points to a valid NUL-terminated string, and the `how` pointer is a valid
        // pointer to an `open_how` struct. However, the caller must ensure that `dir` can provide a
        // valid file descriptor (this can be changed to BorrowedFd).
        let ret = unsafe {
            libc::syscall(
                libc::SYS_openat2,
                dir.as_raw_fd(),
                path.as_ptr(),
                std::ptr::addr_of!(how),
                std::mem::size_of::<libc::open_how>(),
            )
        };
        if ret == -1 {
            Err(io::Error::last_os_error())
        } else {
            // Safe because we have just open the RawFd.
            let file = unsafe { File::from_raw_fd(ret as RawFd) };
            Ok(file)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::File;
    use std::os::unix::fs;
    use vmm_sys_util::tempdir::TempDir;

    #[test]
    fn test_openat2() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("build.rs").unwrap();

        let opener = SafeOpenAt::new();
        assert!(opener.has_openat2);
        opener.openat(&dir, &filename, libc::O_RDONLY, 0).unwrap();
    }

    #[test]
    // If pathname is an absolute path, it is also interpreted relative to dirfd.
    fn test_openat2_absolute() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("/build.rs").unwrap();

        let opener = SafeOpenAt::new();
        assert!(opener.has_openat2);
        opener.openat(&dir, &filename, libc::O_RDONLY, 0).unwrap();
    }

    #[test]
    // If a prefix component of pathname equates to dirfd, then an immediately following ..
    // component likewise equates to dirfd
    fn test_openat2_parent() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("/../../build.rs").unwrap();

        let opener = SafeOpenAt::new();
        assert!(opener.has_openat2);
        opener.openat(&dir, &filename, libc::O_RDONLY, 0).unwrap();
    }

    #[test]
    // Absolute symbolic links are interpreted relative to dirfd.
    fn test_openat2_symlink() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let tmpdir = TempDir::new().unwrap();
        let dest = tmpdir.as_path().join("build.rs");
        fs::symlink("/build.rs", dest).unwrap();
        let filename = CString::new("build.rs").unwrap();

        let opener = SafeOpenAt::new();
        assert!(opener.has_openat2);
        opener.openat(&dir, &filename, libc::O_RDONLY, 0).unwrap();
    }
}
