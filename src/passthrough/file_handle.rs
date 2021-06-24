// Copyright 2021 Red Hat, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::ffi::CStr;
use std::fs::File;
use std::io;
use std::os::unix::io::{AsRawFd, FromRawFd};

/// An arbitrary maximum size for CFileHandle::f_handle.
///
/// According to Linux ABI, struct file_handle has a flexible array member 'f_handle', but it's
/// hard-coded here for simplicity.
const MAX_HANDLE_SZ: usize = 128;

#[repr(C)]
struct CFileHandle {
    // Size of f_handle [in, out]
    handle_bytes: libc::c_uint,
    // Handle type [out]
    handle_type: libc::c_int,
    // File identifier (sized by caller) [out]
    f_handle: [libc::c_char; MAX_HANDLE_SZ],
}

impl CFileHandle {
    fn new() -> Self {
        CFileHandle {
            handle_bytes: MAX_HANDLE_SZ as libc::c_uint,
            handle_type: 0,
            f_handle: [0; MAX_HANDLE_SZ],
        }
    }
}

pub struct FileHandle {
    #[allow(dead_code)]
    mnt_id: u64,
    handle: CFileHandle,
}

extern "C" {
    fn name_to_handle_at(
        dirfd: libc::c_int,
        pathname: *const libc::c_char,
        file_handle: *mut CFileHandle,
        mount_id: *mut libc::c_int,
        flags: libc::c_int,
    ) -> libc::c_int;

    // Technically `file_handle` should be a `mut` pointer, but `open_by_handle_at()` is specified
    // not to change it, so we can declare it `const`.
    fn open_by_handle_at(
        mount_fd: libc::c_int,
        file_handle: *const CFileHandle,
        flags: libc::c_int,
    ) -> libc::c_int;
}

impl FileHandle {
    /// Create a file handle for the given file.
    #[allow(dead_code)]
    fn from_name_at(dir: &impl AsRawFd, path: &CStr) -> io::Result<Self> {
        let mut mount_id: libc::c_int = 0;
        let mut c_fh = CFileHandle::new();

        let ret = unsafe {
            name_to_handle_at(
                dir.as_raw_fd(),
                path.as_ptr(),
                &mut c_fh,
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

    /**
     * Open a file handle (low-level wrapper).
     *
     * `mount_fd` must be an open non-`O_PATH` file descriptor for an inode on the same mount as
     * the file to be opened, i.e. the mount given by `self.mnt_id`.
     */
    #[allow(dead_code)]
    fn open(&self, mount_fd: &impl AsRawFd, flags: libc::c_int) -> io::Result<File> {
        let ret = unsafe { open_by_handle_at(mount_fd.as_raw_fd(), &self.handle, flags) };
        if ret >= 0 {
            // Safe because `open_by_handle_at()` guarantees this is a valid fd
            let file = unsafe { File::from_raw_fd(ret) };
            Ok(file)
        } else {
            Err(io::Error::last_os_error())
        }
    }
}
