// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS stat seam.
//!
//! macOS has no `statx()`; the closest equivalent is `fstat()`/`fstatat()`,
//! which also lack the mount-id concept (`statx`'s `STATX_MNT_ID`).  The
//! `StatExt` twin keeps the `mnt_id` field so `InodeId` and the inode store
//! stay shared, always filled with 0: on macOS the `(st_dev, st_ino)` pair
//! is unique system-wide, so the mount id carries no extra information.

use std::ffi::CStr;
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::AsRawFd;

use fuse_backend_core::abi::fuse_abi as fuse;

pub type MountId = u64;

pub struct StatExt {
    pub st: fuse::stat64,
    pub mnt_id: MountId,
}

/// Execute a stat on `dir` (or on `path` relative to `dir` when given) to
/// get the extended status.
///
/// This mirrors the Linux `statx()` seam: `path == None` stats the
/// descriptor itself, `Some(path)` stats `path` relative to `dir` without
/// following a final symlink.
pub fn statx(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<StatExt> {
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
        // Safe because the kernel guarantees that the struct is now fully
        // initialized.
        Ok(StatExt {
            st: unsafe { st.assume_init() },
            mnt_id: 0,
        })
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::os_compat;
    use std::ffi::CString;
    use std::fs::File;

    #[test]
    fn test_statx() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("Cargo.toml").unwrap();

        let st1 = statx(&dir, None).unwrap();
        let st2 = statx(&dir, Some(&filename)).unwrap();

        assert_eq!(st1.mnt_id, st2.mnt_id);
        assert_eq!(st1.st.st_dev, st2.st.st_dev);
        assert_ne!(st1.st.st_ino, st2.st.st_ino);
        // `O_PATH` is `O_EVTONLY` on macOS, which can open regular files and
        // directories for stat purposes.
        assert_ne!(os_compat::O_PATH, 0);
    }
}
