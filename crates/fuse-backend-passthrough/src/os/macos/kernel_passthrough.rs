// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

//! The macOS twin of the Linux kernel-passthrough surface. The macFUSE
//! kernel has no passthrough mode, so the type surface exists for the shared
//! code and the public API to compile, but every operation is inert:
//! `set_backing_files()` accepts the files and drops them, and handles
//! never get a backing id.

use std::fs::File;
use std::io;
use std::os::fd::BorrowedFd;
use std::sync::Arc;

use crate::util::enosys;
use crate::Inode;

/// Registers the backing files of Linux kernel FUSE passthrough. macOS has
/// no FUSE passthrough, so implementations of this trait are never driven
/// there; the trait keeps the crate's public API identical across
/// platforms.
pub trait BackingFiles: Send + Sync {
    /// Register `fd` as a backing file and return its backing id, such as with
    /// `fuse_backing_open()` of the fusedev transport.
    fn open(&self, fd: BorrowedFd<'_>) -> io::Result<u32>;

    /// Release a backing id returned by `open()`, such as with `fuse_backing_close()`.
    fn close(&self, backing_id: u32) -> io::Result<()>;
}

/// The macOS twin of the Linux backing-id bookkeeping. macOS has no FUSE
/// passthrough, so it keeps no state: handles never get a backing id.
pub(crate) struct KernelPassthrough;

impl KernelPassthrough {
    pub(crate) fn new(_files: Arc<dyn BackingFiles>) -> Self {
        KernelPassthrough
    }

    /// macOS has no backing ids, so no handle shares one.
    pub(crate) fn share(&self, _inode: Inode) -> Option<u32> {
        None
    }

    pub(crate) fn acquire(&self, _inode: Inode, _file: &File) -> io::Result<u32> {
        Err(enosys())
    }

    pub(crate) fn release(&self, _inode: Inode) {}

    pub(crate) fn close_all(&self) {}
}
