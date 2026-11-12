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
//!
//! The descriptor alone cannot serve I/O: it is opened with `O_EVTONLY`
//! (macOS's `O_PATH` analog), macOS has no `/proc/self/fd` to reopen it
//! through, and `dup()` would only share the `O_EVTONLY` access mode.  So
//! [`InodeHandle::open_file()`] reopens the file by path instead: it derives
//! the descriptor's *current* path with `fcntl(F_GETPATH)` (the kernel keeps
//! the pinned vnode's name chain up to date, so renames are tracked), opens
//! that path, and verifies the reopened file's `(st_dev, st_ino)` against the
//! inode's identity to catch the open-by-path races.

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
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::sync::Arc;

use super::mount_fd::{MPRError, MPRResult, MountFd, MountFds, MountId};
use super::os_compat;
use crate::fsops::{getpath_by_fd, stat_fd};
use crate::inode_store::InodeId;
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

    /// Open the tracked file again for I/O, with `flags`.
    ///
    /// The handle's `O_EVTONLY` descriptor cannot be turned into an
    /// I/O-capable one directly (no `/proc/self/fd` to reopen through, and
    /// `dup()` shares the access mode), so the file is opened again by path:
    /// `fcntl(F_GETPATH)` on the handle's descriptor yields the file's
    /// *current* path (renames of the file or of its parents are tracked),
    /// which is then opened with the caller's flags.  The reopened file's
    /// `(st_dev, st_ino)` is verified against `id` to catch the
    /// open-by-path race with unlink + recreate under the same name.
    ///
    /// `O_TRUNC` is applied by `ftruncate()` only after that check: an
    /// `open()` with `O_TRUNC` would zero whatever file the path names at
    /// open time, and in the unlink-plus-recreate race that is an innocent
    /// new file, not the tracked inode.
    ///
    /// `proc_self_fd` is the Linux twin's reopen vehicle and is unused.
    pub(crate) fn open_file(
        &self,
        flags: libc::c_int,
        _proc_self_fd: &File,
        id: &InodeId,
    ) -> io::Result<File> {
        match self {
            InodeHandle::File(f) => {
                let path = getpath_by_fd(f)?;
                let wants_trunc = flags & libc::O_TRUNC != 0;
                let flags = flags & !libc::O_TRUNC;
                let file = match open_path(&path, flags) {
                    Ok(file) => file,
                    // The file may have been renamed between the F_GETPATH
                    // and the open; re-derive the path once before giving up.
                    Err(e) if e.kind() == io::ErrorKind::NotFound => {
                        let path = getpath_by_fd(f)?;
                        open_path(&path, flags)?
                    }
                    Err(e) => return Err(e),
                };

                let st = stat_fd(&file, None)?;
                if st.st_dev != id.dev || st.st_ino != id.ino {
                    // The path now names a different file: this inode's
                    // entry is stale.  ESTALE is the conventional
                    // stale-file-handle errno: the Linux FUSE kernel drops
                    // its entry cache and re-issues the lookup on seeing
                    // it; macFUSE at minimum surfaces it to the caller.
                    return Err(io::Error::from_raw_os_error(libc::ESTALE));
                }
                if wants_trunc {
                    // Safe: `file` is an owned descriptor that just passed
                    // the identity check.
                    if unsafe { libc::ftruncate(file.as_raw_fd(), 0) } < 0 {
                        return Err(io::Error::last_os_error());
                    }
                }
                Ok(file)
            }
            // Unreachable: `FileHandle::from_name_at()` never yields a
            // handle on macOS, so inodes are always tracked by descriptor.
            InodeHandle::Handle(_) => Err(enosys()),
        }
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
/// `O_CLOEXEC` flag is forced on top of the caller's `flags`, and the final
/// path component is never followed through a symlink.
///
/// The no-follow hardening uses Darwin's `O_SYMLINK` instead of Linux's
/// `O_NOFOLLOW`: Darwin's `open()` fails `ELOOP` on a final symlink even
/// for descriptor-only opens, while `O_SYMLINK` opens the symlink itself —
/// which is exactly the `O_PATH | O_NOFOLLOW` behavior the shared lookup
/// code relies on to track symlink inodes.
pub(crate) fn open_file_restricted(
    dir: &impl AsRawFd,
    pathname: &CStr,
    flags: libc::c_int,
    mode: u32,
) -> io::Result<File> {
    let flags = libc::O_SYMLINK | libc::O_CLOEXEC | flags;

    openat(dir, pathname, flags, mode)
}

/// Open the absolute `path`, hardened for path traversal like
/// [`open_file_restricted`]: `O_NOFOLLOW` and `O_CLOEXEC` are forced on top
/// of the caller's `flags`.
///
/// Unlike the lookup path, a final symlink is an error here (`ELOOP`): the
/// caller asked to reopen a tracked inode for I/O, and a symlink inode is
/// never that file.
fn open_path(path: &CStr, flags: libc::c_int) -> io::Result<File> {
    let flags = libc::O_NOFOLLOW | libc::O_CLOEXEC | flags;

    // Safe because `path` is a valid NUL-terminated string, this does not
    // modify any memory, and we check the return value.  The `mode` argument
    // is ignored without `O_CREAT`, which callers never pass.
    let fd = unsafe { libc::open(path.as_ptr(), flags) };
    if fd >= 0 {
        // Safe because we just opened this fd.
        Ok(unsafe { File::from_raw_fd(fd) })
    } else {
        Err(io::Error::last_os_error())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::os_compat::S_IFLNK;
    use crate::os_compat::S_IFMT;
    use crate::os_compat::S_IFREG;
    use std::ffi::CString;
    use std::fs;
    use std::io::Read;
    use std::os::unix::fs::OpenOptionsExt;
    use vmm_sys_util::tempdir::TempDir;

    fn open_evtonly(path: &std::path::Path) -> File {
        fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_EVTONLY)
            .open(path)
            .unwrap()
    }

    fn inode_id_of(file: &File) -> InodeId {
        let st = stat_fd(file, None).unwrap();
        InodeId {
            ino: st.st_ino,
            dev: st.st_dev,
            mnt: 0,
        }
    }

    fn null_fd() -> File {
        File::open("/dev/null").unwrap()
    }

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
    }

    #[test]
    fn test_inode_handle_open_file() {
        let tmp = TempDir::new().unwrap();
        let path = tmp.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        let fd = open_evtonly(&path);
        let id = inode_id_of(&fd);
        let handle = InodeHandle::File(fd);

        let mut file = handle.open_file(libc::O_RDONLY, &null_fd(), &id).unwrap();
        let mut buf = String::new();
        file.read_to_string(&mut buf).unwrap();
        assert_eq!(buf, "hello");
    }

    #[test]
    fn test_inode_handle_open_file_tracks_rename() {
        let tmp = TempDir::new().unwrap();
        let old = tmp.as_path().join("old.txt");
        let new = tmp.as_path().join("new.txt");
        fs::write(&old, "hello").unwrap();

        let fd = open_evtonly(&old);
        let id = inode_id_of(&fd);
        let handle = InodeHandle::File(fd);

        // The handle's descriptor keeps the file's identity, and F_GETPATH
        // reports its current path, so the reopen must survive the rename
        // and still pass the dev/ino validation.
        fs::rename(&old, &new).unwrap();

        let mut file = handle.open_file(libc::O_RDONLY, &null_fd(), &id).unwrap();
        let mut buf = String::new();
        file.read_to_string(&mut buf).unwrap();
        assert_eq!(buf, "hello");
    }

    #[test]
    fn test_inode_handle_open_file_stale_id() {
        let tmp = TempDir::new().unwrap();
        let path = tmp.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        let fd = open_evtonly(&path);
        let mut id = inode_id_of(&fd);
        let handle = InodeHandle::File(fd);

        // A different file's identity: the reopen succeeds but the dev/ino
        // validation must reject it as stale.
        id.ino = id.ino.wrapping_add(1);
        let err = handle
            .open_file(libc::O_RDONLY, &null_fd(), &id)
            .unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ESTALE));
    }

    #[test]
    fn test_inode_handle_open_file_deleted() {
        let tmp = TempDir::new().unwrap();
        let path = tmp.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        let fd = open_evtonly(&path);
        let id = inode_id_of(&fd);
        let handle = InodeHandle::File(fd);

        // An unlinked file has no path left to reopen through, unlike on
        // Linux where the /proc/self/fd reopen keeps serving it.
        fs::remove_file(&path).unwrap();
        assert!(handle.open_file(libc::O_RDONLY, &null_fd(), &id).is_err());
    }

    #[test]
    fn test_inode_handle_open_file_truncates() {
        let tmp = TempDir::new().unwrap();
        let path = tmp.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        let fd = open_evtonly(&path);
        let id = inode_id_of(&fd);
        let handle = InodeHandle::File(fd);

        handle
            .open_file(libc::O_WRONLY | libc::O_TRUNC, &null_fd(), &id)
            .unwrap();
        assert_eq!(fs::read(&path).unwrap(), b"");
    }

    #[test]
    fn test_inode_handle_open_file_truncates_nothing_when_stale() {
        let tmp = TempDir::new().unwrap();
        let path = tmp.as_path().join("file.txt");
        fs::write(&path, "hello").unwrap();

        let fd = open_evtonly(&path);
        let id = inode_id_of(&fd);
        let handle = InodeHandle::File(fd);

        // Unlinked files keep their last known path in F_GETPATH, and a
        // re-created file at that path is a different inode.  O_TRUNC must
        // not be applied at open() time: it would zero the innocent new
        // file before the dev/ino check rejects the reopen as stale.
        fs::remove_file(&path).unwrap();
        fs::write(&path, "replaced").unwrap();

        let err = handle
            .open_file(libc::O_WRONLY | libc::O_TRUNC, &null_fd(), &id)
            .unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ESTALE));
        assert_eq!(fs::read(&path).unwrap(), b"replaced");
    }

    #[test]
    fn test_open_file_restricted_symlink() {
        let tmp = TempDir::new().unwrap();
        let target = tmp.as_path().join("target.txt");
        fs::write(&target, "hello").unwrap();
        let link = tmp.as_path().join("link.lnk");
        std::os::unix::fs::symlink(&target, &link).unwrap();

        let dirfd = open_evtonly(tmp.as_path());

        // A symlink is opened as itself (Linux O_PATH | O_NOFOLLOW
        // semantics), not followed and not ELOOP.
        let name = CString::new("link.lnk").unwrap();
        let file = open_file_restricted(&dirfd, &name, os_compat::O_PATH, 0).unwrap();
        let st = stat_fd(&file, None).unwrap();
        assert_eq!(u32::from(st.st_mode) & S_IFMT, S_IFLNK);

        // Regular files and directories keep opening normally.
        let name = CString::new("target.txt").unwrap();
        let file = open_file_restricted(&dirfd, &name, os_compat::O_PATH, 0).unwrap();
        let st = stat_fd(&file, None).unwrap();
        assert_eq!(u32::from(st.st_mode) & S_IFMT, S_IFREG);
    }
}
