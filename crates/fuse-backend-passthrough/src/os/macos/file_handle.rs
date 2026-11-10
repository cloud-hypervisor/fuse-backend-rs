// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS file-handle seam: a degenerate twin of the Linux `file_handle`.
//!
//! macOS has neither `name_to_handle_at()` nor `open_by_handle_at()`, so
//! [`FileHandle::from_name_at()`] always reports "no handle available" and
//! every inode is tracked by its open descriptor ([`InodeHandle::File`])
//! instead.  The handle-shaped types ([`FileHandle`],
//! [`OpenableFileHandle`] and the [`InodeHandle::Handle`] variant) exist so
//! the shared `lib.rs`/`inode_store.rs` code compiles unchanged; they are
//! never constructed on macOS.

// API-parity stub twin: the handle types above exist only so shared code
// compiles and are never constructed on macOS, which dead-code analysis
// would flag.
#![allow(dead_code)]

use std::ffi::CStr;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::ops::Deref;
use std::os::fd::{AsFd, BorrowedFd};
use std::os::unix::io::{AsRawFd, RawFd};
use std::sync::Arc;

use super::mount_fd::{MPRError, MPRResult, MountFd, MountFds, MountId};
use super::os_compat;
use crate::fsops::stat_fd;
use crate::util::{enosys, openat};
use fuse_backend_core::abi::fuse_abi as fuse;

/// Struct to maintain information for a file handle.
///
/// The Linux twin carries the opaque handle from `name_to_handle_at()`;
/// macOS has no equivalent, so this degenerate form only keeps the mount id
/// that the inode store's handle-key machinery expects.  It is never
/// constructed outside tests.
#[derive(Clone, Default, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct FileHandle {
    pub(crate) mnt_id: MountId,
}

impl FileHandle {
    /// Create a file handle for the given file.
    ///
    /// Always `Ok(None)`: macOS has no `name_to_handle_at()`, so files are
    /// tracked by descriptor instead.  This mirrors the Linux twin's
    /// permanent "no handle" answer for filesystems that do not support
    /// handles.
    pub fn from_name_at(_dir_fd: &impl AsRawFd, _path: &CStr) -> io::Result<Option<Self>> {
        Ok(None)
    }

    /// Create a file handle from a `fd`.
    /// This is a wrapper around `from_name_at()` and so has the same interface.
    pub fn from_fd(_fd: &impl AsRawFd) -> io::Result<Option<Self>> {
        Ok(None)
    }

    /// Return an openable copy of the file handle by ensuring that `mount_fd` contains a valid fd
    /// for the mount the file handle is for.
    ///
    /// Unreachable on macOS because `from_name_at()` never returns a handle;
    /// answers `ENOSYS` if it is ever called.
    pub fn into_openable<F>(
        self,
        _mount_fds: &MountFds,
        _reopen_fd: F,
    ) -> MPRResult<OpenableFileHandle>
    where
        F: FnOnce(RawFd, libc::c_int, u32) -> io::Result<File>,
    {
        Err(MPRError::from(enosys()))
    }
}

/// An openable file handle, mirroring the Linux twin's shape.
///
/// Never constructed on macOS: `FileHandle::from_name_at()` always returns
/// `None`, so there is nothing to open by handle.
pub struct OpenableFileHandle {
    handle: Arc<FileHandle>,
    mount_fd: Arc<MountFd>,
}

impl Debug for OpenableFileHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Openable file handle: mountfd {}, mnt id {}",
            self.mount_fd.as_fd().as_raw_fd(),
            self.handle.mnt_id,
        )
    }
}

impl OpenableFileHandle {
    /// Open a file from an openable file handle.
    ///
    /// macOS has no `open_by_handle_at()`; answers `ENOSYS` if it is ever
    /// called.
    pub fn open(&self, _flags: libc::c_int) -> io::Result<File> {
        Err(enosys())
    }

    pub fn file_handle(&self) -> &Arc<FileHandle> {
        &self.handle
    }
}

/**
 * Represents the file associated with an inode (`InodeData`).
 *
 * When obtaining such a file, it may either be a new file (the `Owned` variant), in which case the
 * object's lifetime is static, or it may reference `InodeData.file` (the `Ref` variant), in which
 * case the object's lifetime is that of the respective `InodeData` object.
 */
#[derive(Debug)]
pub(crate) enum InodeFile<'a> {
    Owned(File),
    Ref(&'a File),
}

impl AsRawFd for InodeFile<'_> {
    /// Return a file descriptor for this file
    /// Note: This fd is only valid as long as the `InodeFile` exists.
    fn as_raw_fd(&self) -> RawFd {
        match self {
            Self::Owned(file) => file.as_raw_fd(),
            Self::Ref(file_ref) => file_ref.as_raw_fd(),
        }
    }
}

impl AsFd for InodeFile<'_> {
    fn as_fd(&self) -> BorrowedFd<'_> {
        match self {
            Self::Owned(file) => file.as_fd(),
            Self::Ref(file_ref) => file_ref.as_fd(),
        }
    }
}

#[derive(Debug)]
pub(crate) enum InodeHandle {
    File(File),
    Handle(Arc<OpenableFileHandle>),
}

impl InodeHandle {
    pub(crate) fn file_handle(&self) -> Option<&FileHandle> {
        match self {
            InodeHandle::File(_) => None,
            InodeHandle::Handle(h) => Some(h.file_handle().deref()),
        }
    }

    pub(crate) fn get_file(&self) -> io::Result<InodeFile<'_>> {
        match self {
            InodeHandle::File(f) => Ok(InodeFile::Ref(f)),
            InodeHandle::Handle(h) => {
                let f = h.open(os_compat::O_PATH)?;
                Ok(InodeFile::Owned(f))
            }
        }
    }

    pub(crate) fn open_file(&self, _flags: libc::c_int, _proc_self_fd: &File) -> io::Result<File> {
        // The `File` variant holds an `O_EVTONLY` descriptor (macOS's
        // `O_PATH` analog), and there is no way to derive an I/O-capable
        // descriptor from it: no `/proc/self/fd` to reopen through, and
        // `dup()` shares the original's access mode so `fcntl(F_SETFL)`
        // cannot widen it.  The `Handle` variant would need
        // `open_by_handle_at()`, which macOS lacks.  How to reopen for I/O
        // (e.g. #182's fd+path handle model) is a decision for the port.
        Err(enosys())
    }

    pub(crate) fn stat(&self) -> io::Result<fuse::stat64> {
        match self {
            InodeHandle::File(f) => stat_fd(f, None),
            InodeHandle::Handle(_h) => {
                let file = self.get_file()?;
                stat_fd(&file, None)
            }
        }
    }
}

/// Open `pathname` relative to `dir`, hardened for path traversal: the
/// `O_NOFOLLOW` and `O_CLOEXEC` flags are forced on top of the caller's
/// `flags`.
pub(crate) fn open_file_restricted(
    dir: &impl AsRawFd,
    pathname: &CStr,
    flags: libc::c_int,
    mode: u32,
) -> io::Result<File> {
    let flags = libc::O_NOFOLLOW | libc::O_CLOEXEC | flags;

    openat(dir, pathname, flags, mode)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    #[test]
    fn test_file_handle_stubs() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("Cargo.toml").unwrap();

        // No handle can ever be created on macOS.
        assert!(FileHandle::from_fd(&dir).unwrap().is_none());
        assert!(FileHandle::from_name_at(&dir, &filename).unwrap().is_none());

        // The degenerate handle still orders and compares by mount id.
        let h1 = FileHandle { mnt_id: 0 };
        let h2 = FileHandle { mnt_id: 1 };
        assert!(h1 < h2);
        assert_ne!(h1, h2);
        assert_eq!(h1, FileHandle::default());
    }

    #[test]
    fn test_inode_handle_file() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let handle = InodeHandle::File(dir);

        assert!(handle.file_handle().is_none());

        let st = handle.stat().unwrap();
        assert_ne!(st.st_ino, 0);

        let file = handle.get_file().unwrap();
        assert!(file.as_raw_fd() >= 0);

        // Reopening for I/O needs a `/proc/self/fd` equivalent, which macOS
        // lacks, so the descriptor-based handle reports ENOSYS.
        let null = File::open("/dev/null").unwrap();
        let err = handle.open_file(libc::O_RDONLY, &null).unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ENOSYS));
    }
}
