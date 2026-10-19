// Copyright (C) 2023 Ant Group. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

#![allow(missing_docs)]

use std::ffi::{CStr, CString};
use std::io::{Error, ErrorKind, Result};

use super::{Context, Entry, FileSystem, GetxattrReply};
use crate::abi::fuse_abi::stat64;

pub const OPAQUE_XATTR_LEN: u32 = 16;
pub const OPAQUE_XATTR: &str = "user.fuseoverlayfs.opaque";
pub const UNPRIVILEGED_OPAQUE_XATTR: &str = "user.overlay.opaque";
pub const PRIVILEGED_OPAQUE_XATTR: &str = "trusted.overlay.opaque";

/// A filesystem must implement Layer trait, or it cannot be used as an OverlayFS layer.
pub trait Layer: FileSystem {
    /// Return the root inode number
    fn root_inode(&self) -> Self::Inode;

    /// Create whiteout file with name <name>.
    ///
    /// If this call is successful then the lookup count of the `Inode` associated with the returned
    /// `Entry` must be increased by 1.
    fn create_whiteout(&self, ctx: &Context, parent: Self::Inode, name: &CStr) -> Result<Entry> {
        // Use temp value to avoid moved 'parent'.
        let ino: u64 = parent.into();
        match self.lookup(ctx, ino.into(), name) {
            Ok(v) => {
                // Find whiteout char dev.
                if is_whiteout(v.attr) {
                    return Ok(v);
                }
                // Non-negative entry with inode larger than 0 indicates file exists.
                if v.inode != 0 {
                    // Decrease the refcount.
                    self.forget(ctx, v.inode.into(), 1);
                    // File exists with same name, create whiteout file is not allowed.
                    return Err(Error::from_raw_os_error(libc::EEXIST));
                }
            }
            Err(e) => match e.raw_os_error() {
                Some(raw_error) => {
                    // We expect ENOENT error.
                    if raw_error != libc::ENOENT {
                        return Err(e);
                    }
                }
                None => return Err(e),
            },
        }

        // Try to create whiteout char device with 0/0 device number.
        let dev = libc::makedev(0, 0);
        let mode = libc::S_IFCHR | 0o777;
        self.mknod(ctx, ino.into(), name, mode, dev as u32, 0)
    }

    /// Delete whiteout file with name <name>.
    fn delete_whiteout(&self, ctx: &Context, parent: Self::Inode, name: &CStr) -> Result<()> {
        // Use temp value to avoid moved 'parent'.
        let ino: u64 = parent.into();
        match self.lookup(ctx, ino.into(), name) {
            Ok(v) => {
                if v.inode != 0 {
                    // Decrease the refcount since we make a lookup call.
                    self.forget(ctx, v.inode.into(), 1);
                }

                // Find whiteout so we can safely delete it.
                if is_whiteout(v.attr) {
                    return self.unlink(ctx, ino.into(), name);
                }
                //  Non-negative entry with inode larger than 0 indicates file exists.
                if v.inode != 0 {
                    // File exists but not whiteout file.
                    return Err(Error::from_raw_os_error(libc::EINVAL));
                }
            }
            Err(e) => match e.raw_os_error() {
                Some(raw_error) => {
                    // ENOENT is acceptable.
                    if raw_error != libc::ENOENT {
                        return Err(e);
                    }
                }
                None => return Err(e),
            },
        }
        Ok(())
    }

    /// Check if the Inode is a whiteout file
    fn is_whiteout(&self, ctx: &Context, inode: Self::Inode) -> Result<bool> {
        let (st, _) = self.getattr(ctx, inode, None)?;

        // Check attributes of the inode to see if it's a whiteout char device.
        Ok(is_whiteout(st))
    }

    /// Set the directory to opaque.
    fn set_opaque(&self, ctx: &Context, inode: Self::Inode) -> Result<()> {
        // Use temp value to avoid moved 'parent'.
        let ino: u64 = inode.into();

        // Get attributes and check if it's directory.
        let (st, _d) = self.getattr(ctx, ino.into(), None)?;
        if !is_dir(st) {
            // Only directory can be set to opaque.
            return Err(Error::from_raw_os_error(libc::ENOTDIR));
        }
        // A directory is made opaque by setting the xattr "trusted.overlay.opaque" to "y".
        // See ref: https://docs.kernel.org/filesystems/overlayfs.html#whiteouts-and-opaque-directories
        self.setxattr(
            ctx,
            ino.into(),
            to_cstring(OPAQUE_XATTR)?.as_c_str(),
            b"y",
            0,
        )
    }

    /// Check if the directory is opaque.
    fn is_opaque(&self, ctx: &Context, inode: Self::Inode) -> Result<bool> {
        // Use temp value to avoid moved 'parent'.
        let ino: u64 = inode.into();

        // Get attributes of the directory.
        let (st, _d) = self.getattr(ctx, ino.into(), None)?;
        if !is_dir(st) {
            return Err(Error::from_raw_os_error(libc::ENOTDIR));
        }

        // Return Result<is_opaque>.
        let check_attr = |inode: Self::Inode, attr_name: &str, attr_size: u32| -> Result<bool> {
            let cname = CString::new(attr_name)?;
            match self.getxattr(ctx, inode, cname.as_c_str(), attr_size) {
                Ok(v) => {
                    // xattr name exists and we get value.
                    if let GetxattrReply::Value(buf) = v {
                        if buf.len() == 1 && buf[0].eq_ignore_ascii_case(&b'y') {
                            return Ok(true);
                        }
                    }
                    // No value found, go on to next check.
                    Ok(false)
                }
                Err(e) => {
                    if let Some(raw_error) = e.raw_os_error() {
                        // ENODATA means the xattr is absent. EOPNOTSUPP and
                        // ENOSYS mean the filesystem has no xattr support at
                        // all: tmpfs answers EOPNOTSUPP to user.* xattrs
                        // before Linux 6.12 and a layer with xattr support
                        // disabled answers ENOSYS. Such a filesystem can
                        // never hold an opaque xattr, so treat all of them
                        // as not opaque instead of failing. (ENOTSUP is not
                        // listed: it is the same errno as EOPNOTSUPP on
                        // Linux.)
                        if matches!(raw_error, libc::ENODATA | libc::EOPNOTSUPP | libc::ENOSYS) {
                            return Ok(false);
                        }
                    }

                    Err(e)
                }
            }
        };

        // A directory is made opaque by setting some specific xattr to "y".
        // See ref: https://docs.kernel.org/filesystems/overlayfs.html#whiteouts-and-opaque-directories

        // Check our customized version of the xattr "user.fuseoverlayfs.opaque".
        let is_opaque = check_attr(ino.into(), OPAQUE_XATTR, OPAQUE_XATTR_LEN)?;
        if is_opaque {
            return Ok(true);
        }

        // Also check for the unprivileged version of the xattr "trusted.overlay.opaque".
        let is_opaque = check_attr(ino.into(), PRIVILEGED_OPAQUE_XATTR, OPAQUE_XATTR_LEN)?;
        if is_opaque {
            return Ok(true);
        }

        // Also check for the unprivileged version of the xattr "user.overlay.opaque".
        let is_opaque = check_attr(ino.into(), UNPRIVILEGED_OPAQUE_XATTR, OPAQUE_XATTR_LEN)?;
        if is_opaque {
            return Ok(true);
        }

        Ok(false)
    }
}

pub(crate) fn is_dir(st: stat64) -> bool {
    st.st_mode & libc::S_IFMT == libc::S_IFDIR
}

pub(crate) fn is_chardev(st: stat64) -> bool {
    st.st_mode & libc::S_IFMT == libc::S_IFCHR
}

pub(crate) fn is_whiteout(st: stat64) -> bool {
    // A whiteout is created as a character device with 0/0 device number.
    // See ref: https://docs.kernel.org/filesystems/overlayfs.html#whiteouts-and-opaque-directories
    let major = libc::major(st.st_rdev);
    let minor = libc::minor(st.st_rdev);
    is_chardev(st) && major == 0 && minor == 0
}

pub(crate) fn to_cstring(name: &str) -> Result<CString> {
    CString::new(name).map_err(|e| Error::new(ErrorKind::InvalidData, e))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Duration;

    // Test double for a Layer: getattr reports a file of <mode> and getxattr
    // answers from a closure, so is_opaque()'s handling of the getxattr
    // errnos can be checked without any backing filesystem.
    struct MockLayer<F: Fn(&CStr) -> Result<GetxattrReply>> {
        mode: u32,
        getxattr: F,
    }

    impl<F: Fn(&CStr) -> Result<GetxattrReply>> FileSystem for MockLayer<F> {
        type Inode = u64;
        type Handle = u64;

        fn getattr(
            &self,
            _ctx: &Context,
            _inode: Self::Inode,
            _handle: Option<Self::Handle>,
        ) -> Result<(stat64, Duration)> {
            // Safe: an all-zero stat64 is a valid stat of a hidden file.
            let mut st: stat64 = unsafe { std::mem::zeroed() };
            st.st_mode = self.mode;
            Ok((st, Duration::ZERO))
        }

        fn getxattr(
            &self,
            _ctx: &Context,
            _inode: Self::Inode,
            name: &CStr,
            _size: u32,
        ) -> Result<GetxattrReply> {
            (self.getxattr)(name)
        }
    }

    impl<F: Fn(&CStr) -> Result<GetxattrReply>> Layer for MockLayer<F> {
        fn root_inode(&self) -> Self::Inode {
            1
        }
    }

    fn is_opaque_with(
        mode: u32,
        getxattr: impl Fn(&CStr) -> Result<GetxattrReply>,
    ) -> Result<bool> {
        MockLayer { mode, getxattr }.is_opaque(&Context::default(), 1)
    }

    // ENODATA means the xattr is absent. EOPNOTSUPP/ENOTSUP and ENOSYS mean
    // the filesystem has no xattr support at all: tmpfs answers EOPNOTSUPP
    // to user.* xattrs before Linux 6.12, and a layer with xattr support
    // disabled answers ENOSYS. Such a filesystem can never be opaque.
    #[test]
    fn test_is_opaque_xattr_unsupported() {
        for errno in [libc::ENODATA, libc::EOPNOTSUPP, libc::ENOTSUP, libc::ENOSYS] {
            let opaque =
                is_opaque_with(libc::S_IFDIR, |_| Err(Error::from_raw_os_error(errno))).unwrap();
            assert!(!opaque, "errno {} must mean not opaque", errno);
        }
    }

    // Any of the three opaque xattrs set to "y" marks the directory opaque.
    #[test]
    fn test_is_opaque_with_xattr_set() {
        for name in [
            OPAQUE_XATTR,
            PRIVILEGED_OPAQUE_XATTR,
            UNPRIVILEGED_OPAQUE_XATTR,
        ] {
            let cname = CString::new(name).unwrap();
            let opaque = is_opaque_with(libc::S_IFDIR, move |probe| {
                if probe == cname.as_c_str() {
                    Ok(GetxattrReply::Value(b"y".to_vec()))
                } else {
                    Err(Error::from_raw_os_error(libc::ENODATA))
                }
            })
            .unwrap();
            assert!(opaque, "{} must mean opaque", name);
        }
    }

    // An xattr holding anything other than "y" does not make it opaque.
    #[test]
    fn test_is_opaque_with_other_value() {
        let opaque =
            is_opaque_with(libc::S_IFDIR, |_| Ok(GetxattrReply::Value(b"n".to_vec()))).unwrap();
        assert!(!opaque);
    }

    // Errors other than the absent/unsupported ones still fail the check.
    #[test]
    fn test_is_opaque_propagates_other_errors() {
        let e = is_opaque_with(libc::S_IFDIR, |_| {
            Err(Error::from_raw_os_error(libc::EPERM))
        })
        .unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::EPERM));
    }

    // Only a directory can be checked for opacity.
    #[test]
    fn test_is_opaque_rejects_non_directory() {
        let e = is_opaque_with(libc::S_IFREG, |_| {
            Err(Error::from_raw_os_error(libc::ENODATA))
        })
        .unwrap_err();
        assert_eq!(e.raw_os_error(), Some(libc::ENOTDIR));
    }
}
