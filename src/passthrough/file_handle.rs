// Copyright 2021 Red Hat, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::cmp::Ordering;
use std::ffi::CStr;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::sync::Arc;

use vmm_sys_util::fam::{FamStruct, FamStructWrapper};

use super::mount_fd::{MountFd, MountFds, MountId};

/// An arbitrary maximum size for CFileHandle::f_handle.
///
/// According to Linux ABI, struct file_handle has a flexible array member 'f_handle', with
/// maximum value of 128 bytes defined in file include/linux/exportfs.h
pub const MAX_HANDLE_SIZE: usize = 128;

/// Dynamically allocated array.
#[derive(Default)]
#[repr(C)]
pub struct __IncompleteArrayField<T>(::std::marker::PhantomData<T>, [T; 0]);
impl<T> __IncompleteArrayField<T> {
    #[inline]
    pub unsafe fn as_ptr(&self) -> *const T {
        self as *const __IncompleteArrayField<T> as *const T
    }
    #[inline]
    pub unsafe fn as_mut_ptr(&mut self) -> *mut T {
        self as *mut __IncompleteArrayField<T> as *mut T
    }
    #[inline]
    pub unsafe fn as_slice(&self, len: usize) -> &[T] {
        ::std::slice::from_raw_parts(self.as_ptr(), len)
    }
    #[inline]
    pub unsafe fn as_mut_slice(&mut self, len: usize) -> &mut [T] {
        ::std::slice::from_raw_parts_mut(self.as_mut_ptr(), len)
    }
}

/// The structure to transfer file_handle struct between user space and kernel space.
/// ```c
/// struct file_handle {
///     __u32 handle_bytes;
///     int handle_type;
///     /* file identifier */
///     unsigned char f_handle[];
/// }
/// ```
#[derive(Default)]
#[repr(C)]
pub struct CFileHandleInner {
    pub handle_bytes: libc::c_uint,
    pub handle_type: libc::c_int,
    pub f_handle: __IncompleteArrayField<libc::c_char>,
}

vmm_sys_util::generate_fam_struct_impl!(
    CFileHandleInner,
    libc::c_char,
    f_handle,
    libc::c_uint,
    handle_bytes,
    MAX_HANDLE_SIZE
);

type CFileHandleWrapper = FamStructWrapper<CFileHandleInner>;

#[derive(Clone)]
struct CFileHandle {
    pub wrapper: CFileHandleWrapper,
}

impl CFileHandle {
    fn new(size: usize) -> Self {
        CFileHandle {
            wrapper: CFileHandleWrapper::new(size).unwrap(),
        }
    }
}

// Safe because f_handle is readonly once FileHandle is initialized.
unsafe impl Send for CFileHandle {}
unsafe impl Sync for CFileHandle {}

impl Ord for CFileHandle {
    fn cmp(&self, other: &Self) -> Ordering {
        let s_fh = self.wrapper.as_fam_struct_ref();
        let o_fh = other.wrapper.as_fam_struct_ref();
        if s_fh.handle_bytes != o_fh.handle_bytes {
            return s_fh.handle_bytes.cmp(&o_fh.handle_bytes);
        }
        let length = s_fh.handle_bytes as usize;
        if s_fh.handle_type != o_fh.handle_type {
            return s_fh.handle_type.cmp(&o_fh.handle_type);
        }
        unsafe {
            if s_fh.f_handle.as_ptr() != o_fh.f_handle.as_ptr() {
                return s_fh
                    .f_handle
                    .as_slice(length)
                    .cmp(o_fh.f_handle.as_slice(length));
            }
        }

        Ordering::Equal
    }
}

impl PartialOrd for CFileHandle {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for CFileHandle {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for CFileHandle {}

impl Debug for CFileHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let fh = self.wrapper.as_fam_struct_ref();
        write!(
            f,
            "File handle: type {}, len {}",
            fh.handle_type, fh.handle_bytes
        )
    }
}

/// Struct to maintain information for a file handle.
#[derive(Clone, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct FileHandle {
    pub(crate) mnt_id: u64,
    handle: CFileHandle,
}

impl Default for FileHandle {
    fn default() -> Self {
        Self {
            mnt_id: 0,
            handle: CFileHandle::new(0),
        }
    }
}

extern "C" {
    fn name_to_handle_at(
        dirfd: libc::c_int,
        pathname: *const libc::c_char,
        file_handle: *mut CFileHandleInner,
        mount_id: *mut libc::c_int,
        flags: libc::c_int,
    ) -> libc::c_int;

    // Technically `file_handle` should be a `mut` pointer, but `open_by_handle_at()` is specified
    // not to change it, so we can declare it `const`.
    fn open_by_handle_at(
        mount_fd: libc::c_int,
        file_handle: *const CFileHandleInner,
        flags: libc::c_int,
    ) -> libc::c_int;
}

impl FileHandle {
    /// Create a file handle for the given file.
    pub fn from_name_at(dir_fd: RawFd, path: &CStr) -> io::Result<Self> {
        let mut mount_id: libc::c_int = 0;
        let mut c_fh = CFileHandle::new(0);

        // Per name_to_handle_at(2), the caller can discover the required size
        // for the file_handle structure by making a call in which
        // handle->handle_bytes is zero.  In this case, the call fails with the
        // error EOVERFLOW and handle->handle_bytes is set to indicate the
        // required size; the caller can then use this information to allocate a
        // structure of the correct size.
        let ret = unsafe {
            name_to_handle_at(
                dir_fd,
                path.as_ptr(),
                c_fh.wrapper.as_mut_fam_struct_ptr(),
                &mut mount_id,
                libc::AT_EMPTY_PATH,
            )
        };
        if ret == -1 {
            let e = io::Error::last_os_error();
            // unwrap is safe as e is obtained from last_os_error().
            if e.raw_os_error().unwrap() != libc::EOVERFLOW {
                return Err(e);
            }
        } else {
            return Err(io::Error::from(io::ErrorKind::InvalidData));
        }

        let needed = c_fh.wrapper.as_fam_struct_ref().handle_bytes as usize;
        let mut c_fh = CFileHandle::new(needed);

        // name_to_handle_at() does not trigger a mount when the final component of the pathname is
        // an automount point. When a filesystem supports both file handles and automount points,
        // a name_to_handle_at() call on an automount point will return with error EOVERFLOW
        // without having increased handle_bytes.  This can happen since Linux 4.13 with NFS
        // when accessing a directory which is on a separate filesystem on the server. In this case,
        // the automount can be triggered by adding a "/" to the end of the pathname.
        let ret = unsafe {
            name_to_handle_at(
                dir_fd,
                path.as_ptr(),
                c_fh.wrapper.as_mut_fam_struct_ptr(),
                &mut mount_id,
                libc::AT_EMPTY_PATH,
            )
        };
        if ret == 0 {
            Ok(FileHandle {
                mnt_id: mount_id as u64,
                handle: c_fh,
            })
        } else {
            Err(io::Error::last_os_error())
        }
    }
}

pub struct OpenableFileHandle {
    handle: Arc<FileHandle>,
    mount_fd: Arc<MountFd>,
}

impl Debug for OpenableFileHandle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let fh = self.handle.handle.wrapper.as_fam_struct_ref();
        write!(
            f,
            "Openable file handle: mountfd {}, type {}, len {}",
            self.mount_fd.file().as_raw_fd(),
            fh.handle_type,
            fh.handle_bytes
        )
    }
}

impl OpenableFileHandle {
    /// Create a file handle for the given file.
    ///
    /// Also ensure that `mount_fds` contains a valid fd for the mount the file is on (so that
    /// `handle.open_with_mount_fds()` will work).
    ///
    /// If `path` is empty, `reopen_dir` may be invoked to duplicate `dir` with custom
    /// `libc::open()` flags.
    pub fn from_name_at<F>(
        dir_fd: RawFd,
        path: &CStr,
        mount_fds: &MountFds,
        reopen_dir: F,
    ) -> io::Result<OpenableFileHandle>
    where
        F: FnOnce(RawFd, libc::c_int, u32) -> io::Result<File>,
    {
        let handle = FileHandle::from_name_at(dir_fd, path).map_err(|e| {
            error!("from_name_at failed error {:?}", e);
            e
        })?;

        let mount_fd = mount_fds
            .get(handle.mnt_id, reopen_dir)
            .map_err(|e| e.into_inner())?;

        Ok(OpenableFileHandle {
            handle: Arc::new(handle),
            mount_fd,
        })
    }

    /// Open a file handle (low-level wrapper).
    ///
    /// `mount_fd` must be an open non-`O_PATH` file descriptor for an inode on the same mount as
    /// the file to be opened, i.e. the mount given by `self.mnt_id`.
    pub fn open(&self, flags: libc::c_int) -> io::Result<File> {
        let ret = unsafe {
            open_by_handle_at(
                self.mount_fd.file().as_raw_fd(),
                self.handle.handle.wrapper.as_fam_struct_ptr(),
                flags,
            )
        };
        if ret >= 0 {
            // Safe because `open_by_handle_at()` guarantees this is a valid fd
            let file = unsafe { File::from_raw_fd(ret) };
            Ok(file)
        } else {
            let e = io::Error::last_os_error();
            error!("open_by_handle_at failed error {:?}", e);
            Err(e)
        }
    }

    pub fn mount_id(&self) -> MountId {
        self.handle.mnt_id
    }

    pub fn file_handle(&self) -> &Arc<FileHandle> {
        &self.handle
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn generate_c_file_handle(
        handle_bytes: usize,
        handle_type: libc::c_int,
        buf: Vec<libc::c_char>,
    ) -> CFileHandle {
        let mut wrapper = CFileHandle::new(handle_bytes);
        let fh = wrapper.wrapper.as_mut_fam_struct();
        fh.handle_type = handle_type;
        unsafe {
            fh.f_handle
                .as_mut_slice(handle_bytes)
                .copy_from_slice(buf.as_slice());
        }

        wrapper
    }

    #[test]
    fn test_file_handle_derives() {
        let h1 = generate_c_file_handle(128, 3, vec![0; 128]);
        let mut fh1 = FileHandle {
            mnt_id: 0,
            handle: h1,
        };

        let h2 = generate_c_file_handle(127, 3, vec![0; 127]);
        let fh2 = FileHandle {
            mnt_id: 0,
            handle: h2,
        };

        let h3 = generate_c_file_handle(128, 4, vec![0; 128]);
        let fh3 = FileHandle {
            mnt_id: 0,
            handle: h3,
        };

        let h4 = generate_c_file_handle(128, 3, vec![1; 128]);
        let fh4 = FileHandle {
            mnt_id: 0,
            handle: h4,
        };

        let h5 = generate_c_file_handle(128, 3, vec![0; 128]);
        let mut fh5 = FileHandle {
            mnt_id: 0,
            handle: h5,
        };

        assert!(fh1 > fh2);
        assert!(fh1 != fh2);
        assert!(fh1 < fh3);
        assert!(fh1 != fh3);
        assert!(fh1 < fh4);
        assert!(fh1 != fh4);
        assert!(fh1 == fh5);

        unsafe {
            fh1.handle
                .wrapper
                .as_mut_fam_struct()
                .f_handle
                .as_mut_slice(128)[0] = 1;
        }
        assert!(fh1 > fh5);
        unsafe {
            fh5.handle
                .wrapper
                .as_mut_fam_struct()
                .f_handle
                .as_mut_slice(128)[0] = 1;
        }
        assert!(fh1 == fh5);
    }

    #[test]
    fn test_c_file_handle_wrapper() {
        let buf = (0..=127).collect::<Vec<libc::c_char>>();
        let mut wrapper = generate_c_file_handle(MAX_HANDLE_SIZE, 3, buf.clone());
        let fh = wrapper.wrapper.as_mut_fam_struct();

        assert_eq!(fh.handle_bytes as usize, MAX_HANDLE_SIZE);
        assert_eq!(fh.handle_type, 3);
        assert_eq!(
            unsafe { fh.f_handle.as_slice(MAX_HANDLE_SIZE) },
            buf.as_slice(),
        );
    }
}
