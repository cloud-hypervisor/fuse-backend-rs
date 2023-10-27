// Copyright 2021 Red Hat, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::cmp::Ordering;
use std::collections::HashMap;
use std::ffi::CStr;
use std::fmt::{Debug, Formatter};
use std::fs::File;
use std::io;
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::sync::{RwLock, RwLockReadGuard, RwLockWriteGuard};

use vmm_sys_util::{
    fam::{FamStruct, FamStructWrapper},
    generate_fam_struct_impl,
};

use crate::passthrough::PassthroughFs;

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

generate_fam_struct_impl!(
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
            let e = io::Error::last_os_error();
            Err(e)
        }
    }

    /// Create a file handle for the given file.
    ///
    /// Also ensure that `mount_fds` contains a valid fd for the mount the file is on (so that
    /// `handle.open_with_mount_fds()` will work).
    ///
    /// If `path` is empty, `reopen_dir` may be invoked to duplicate `dir` with custom
    /// `libc::open()` flags.
    pub fn from_name_at_with_mount_fds<F>(
        dir_fd: RawFd,
        path: &CStr,
        mount_fds: &MountFds,
        reopen_dir: F,
    ) -> io::Result<Self>
    where
        F: FnOnce(RawFd, libc::c_int, u32) -> io::Result<File>,
    {
        let handle = Self::from_name_at(dir_fd, path).map_err(|e| {
            error!("from_name_at failed error {:?}", e);
            e
        })?;

        mount_fds.ensure_mount_point(handle.mnt_id, dir_fd, path, reopen_dir)?;

        Ok(handle)
    }

    /// Open a file handle (low-level wrapper).
    ///
    /// `mount_fd` must be an open non-`O_PATH` file descriptor for an inode on the same mount as
    /// the file to be opened, i.e. the mount given by `self.mnt_id`.
    fn open(&self, mount_fd: &impl AsRawFd, flags: libc::c_int) -> io::Result<File> {
        let ret = unsafe {
            open_by_handle_at(
                mount_fd.as_raw_fd(),
                self.handle.wrapper.as_fam_struct_ptr(),
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

    /// Open a file handle, using the given `mount_fds` hash map.
    ///
    /// Look up `self.mnt_id` in `mount_fds`, and pass the result to `self.open()`.
    pub fn open_with_mount_fds(
        &self,
        mount_fds: &MountFds,
        flags: libc::c_int,
    ) -> io::Result<File> {
        let mount_fds_locked = mount_fds.get_map();
        let mount_file = mount_fds_locked.get(&self.mnt_id).ok_or_else(|| {
            error!(
                "open_with_mount_fds: mnt_id {:?} is not found.",
                &self.mnt_id
            );
            io::Error::from_raw_os_error(libc::ENODEV)
        })?;

        self.open(mount_file, flags)
    }
}

/// Struct to maintain <mount ID, mountpoint file> mapping for open_by_handle_at().
///
/// Creating a file handle only returns a mount ID; opening a file handle requires an open fd on the
/// respective mount.  This is a type in which we can store fds that we know are associated with a
/// given mount ID, so that when opening a handle we can look it up.
#[derive(Default)]
pub struct MountFds {
    pub(crate) map: RwLock<HashMap<u64, File>>,
}

impl MountFds {
    pub fn new() -> Self {
        MountFds::default()
    }

    pub fn get_map(&self) -> RwLockReadGuard<'_, HashMap<u64, std::fs::File>> {
        self.map.read().unwrap()
    }

    pub fn get_map_mut(&self) -> RwLockWriteGuard<'_, HashMap<u64, std::fs::File>> {
        self.map.write().unwrap()
    }

    fn ensure_mount_point<F>(
        &self,
        mnt_id: u64,
        dir_fd: RawFd,
        path: &CStr,
        reopen_dir: F,
    ) -> io::Result<()>
    where
        F: FnOnce(RawFd, libc::c_int, u32) -> io::Result<File>,
    {
        if self.get_map().contains_key(&mnt_id) {
            return Ok(());
        }

        let (path_fd, _path_file) = if path.to_bytes().is_empty() {
            // `open_by_handle_at()` needs a non-`O_PATH` fd, and `dir` may be `O_PATH`, so we
            // have to open a new fd here
            // We do not know whether `dir`/`path` is a special file, though, and we must not open
            // special files with anything but `O_PATH`, so we have to get some `O_PATH` fd first
            // that we can stat to find out whether it is safe to open.
            // (When opening a new fd here, keep a `File` object around so the fd is closed when it
            // goes out of scope.)
            (dir_fd, None)
        } else {
            let f = PassthroughFs::<()>::open_file(
                dir_fd,
                path,
                libc::O_PATH | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0,
            )
            .map_err(|e| {
                error!(
                    "from_name_at_with_mount_fds: open_file on {:?} failed error {:?}",
                    path, e
                );
                e
            })?;
            (f.as_raw_fd(), Some(f))
        };

        // liubo: TODO find mnt id
        // Ensure that `file` refers to an inode with the mount ID we need
        // if statx(&file, None)?.mnt_id != handle.mnt_id {
        //     return Err(io::Error::from_raw_os_error(libc::EIO));
        // }

        let st = PassthroughFs::<()>::stat_fd(path_fd, None)?;
        // Ensure that we can safely reopen `path_fd` with `O_RDONLY`
        let file_type = st.st_mode & libc::S_IFMT;
        if file_type != libc::S_IFREG && file_type != libc::S_IFDIR {
            error!(
                "from_name_at_with_mount_fds: file {:?} is special file",
                path
            );
            return Err(io::Error::from_raw_os_error(libc::EIO));
        }

        let file = reopen_dir(
            path_fd,
            libc::O_RDONLY | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            st.st_mode,
        )?;
        self.get_map_mut().insert(mnt_id, file);

        Ok(())
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
