// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS mount-fd seam: a degenerate twin of the Linux `MountFds`.
//!
//! The Linux version maps mount IDs (from `name_to_handle_at()`) to open fds
//! on the respective mounts, so `open_by_handle_at()` can reopen files by
//! handle.  macOS has neither `name_to_handle_at()` nor `open_by_handle_at()`
//! — `FileHandle::from_name_at()` on macOS always reports "no handle
//! available" — so no mount fd is ever actually needed.  The types exist so
//! the shared `lib.rs`/`file_handle` code compiles unchanged; `MountFds::get()`
//! is never called in practice and answers `ENOSYS` if it ever is.

// API-parity stub twin: several items below exist only so shared code
// compiles and are never constructed or called on macOS, which dead-code
// analysis would flag.
#![allow(dead_code)]

use std::fs::File;
use std::io;
use std::os::fd::{AsFd, BorrowedFd};
use std::sync::Arc;

/// Type alias for mount id.
pub type MountId = u64;

/// An open descriptor on a mount, as required by `open_by_handle_at()`.
///
/// Never constructed on macOS; it only exists so `OpenableFileHandle` has the
/// same shape as on Linux.
pub struct MountFd {
    _file: File,
}

impl AsFd for MountFd {
    fn as_fd(&self) -> BorrowedFd<'_> {
        self._file.as_fd()
    }
}

/// Map from mount IDs to open fds on the respective mounts.
///
/// Degenerate on macOS: `get()` is unreachable because no `FileHandle` is
/// ever created, and answers `ENOSYS` regardless of the requested mount ID.
pub struct MountFds;

impl MountFds {
    pub fn new(_mount_prefix: Option<String>) -> io::Result<Self> {
        Ok(Self)
    }

    /// Signature-compatible with the Linux twin; there is no
    /// `/proc/self/mountinfo` to read on macOS, so the file is unused.
    pub fn with_mount_info_file(_mount_info: File, _mount_prefix: Option<String>) -> Self {
        Self
    }

    pub fn get<F>(&self, _mount_id: MountId, _reopen_fd: F) -> MPRResult<Arc<MountFd>>
    where
        F: FnOnce(std::os::unix::io::RawFd, libc::c_int, u32) -> io::Result<File>,
    {
        Err(MPRError::from(enosys_mount_fds()))
    }

    pub fn error_for<E: ToString + Into<io::Error>>(&self, _mount_id: MountId, err: E) -> MPRError {
        MPRError::from(err)
    }
}

fn enosys_mount_fds() -> io::Error {
    io::Error::from_raw_os_error(libc::ENOSYS)
}

/// Error object for mount-point-related errors (hence MPR), mirroring the
/// Linux twin's surface.  Only `From`, `Display`, `silent()` and
/// `into_inner()` are consumed by shared code.
#[derive(Debug)]
pub struct MPRError {
    io: io::Error,
    description: String,
    silent: bool,
}

/// Type alias for convenience
pub type MPRResult<T> = Result<T, MPRError>;

impl<E: ToString + Into<io::Error>> From<E> for MPRError {
    /// Convert any stringifyable error object that can be converted to an
    /// `io::Error` to an `MPRError`.  The initial description is taken from
    /// the original error object.
    fn from(err: E) -> Self {
        let description = err.to_string();
        MPRError {
            io: err.into(),
            description,
            silent: false,
        }
    }
}

impl MPRError {
    /// Override the current description
    #[must_use]
    pub fn set_desc(mut self, s: String) -> Self {
        self.description = s;
        self
    }

    /// Add a prefix to the description
    #[must_use]
    pub fn prefix(self, s: String) -> Self {
        let new_desc = format!("{}: {}", s, self.description);
        self.set_desc(new_desc)
    }

    /// Mark this error as silent (i.e. not to be logged)
    #[must_use]
    pub fn silence(mut self) -> Self {
        self.silent = true;
        self
    }

    /// Return whether this error is silent (i.e. should not be logged)
    pub fn silent(&self) -> bool {
        self.silent
    }

    /// Return the `io::Error` from an `MPRError` and drop the rest
    pub fn into_inner(self) -> io::Error {
        self.io
    }
}

impl std::fmt::Display for MPRError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.description)
    }
}

impl std::error::Error for MPRError {}
