// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

//! The Linux kernel FUSE passthrough: reads, writes and mmap of open files
//! are served by the host files without involving the daemon. The kernel
//! refers to a registered backing file by a backing id, which
//! `PassthroughFs::set_backing_files()` hands to the transport.

use std::collections::HashMap;
use std::fs::File;
use std::io;
use std::os::fd::{AsFd, BorrowedFd};
use std::sync::{Arc, Mutex};

use log::{debug, warn};

use crate::Inode;

/// Registers the backing files of Linux kernel FUSE passthrough, which passes reads, writes and
/// mmap of open files to the host files without involving the server. See
/// `PassthroughFs::set_backing_files()`.
pub trait BackingFiles: Send + Sync {
    /// Register `fd` as a backing file and return its backing id, such as with
    /// `fuse_backing_open()` of the fusedev transport.
    fn open(&self, fd: BorrowedFd<'_>) -> io::Result<u32>;

    /// Release a backing id returned by `open()`, such as with `fuse_backing_close()`.
    fn close(&self, backing_id: u32) -> io::Result<()>;
}

/// The backing ids of the inodes open in kernel passthrough mode.
pub(crate) struct KernelPassthrough {
    pub(crate) files: Arc<dyn BackingFiles>,
    /// The backing id and the number of open handles of each inode. The kernel fails an open of
    /// an inode that is already open in passthrough mode unless it passes through to the same
    /// backing file, so all the handles of an inode share one id.
    pub(crate) ids: Mutex<HashMap<Inode, (u32, usize)>>,
}

impl KernelPassthrough {
    pub(crate) fn new(files: Arc<dyn BackingFiles>) -> Self {
        Self {
            files,
            ids: Mutex::new(HashMap::new()),
        }
    }

    /// Get the backing id of `inode` for a new handle if the inode has one.
    pub(crate) fn share(&self, inode: Inode) -> Option<u32> {
        // Do not expect poisoned lock here, so safe to unwrap().
        let mut ids = self.ids.lock().unwrap();
        let (id, handles) = ids.get_mut(&inode)?;
        *handles += 1;
        Some(*id)
    }

    /// Get the backing id of `inode` for a new handle, registering `file` if the inode has none.
    pub(crate) fn acquire(&self, inode: Inode, file: &File) -> io::Result<u32> {
        if let Some(id) = self.share(inode) {
            return Ok(id);
        }
        // Register the file without the lock, so that a slow ioctl doesn't hold up the opens and
        // releases of other inodes.
        let new_id = self.files.open(file.as_fd());
        let mut ids = self.ids.lock().unwrap();
        if let Some((id, handles)) = ids.get_mut(&inode) {
            // Another open of the inode registered it meanwhile, and the kernel needs all the
            // opens of an inode to use the same id. Use that id, even if registering this file
            // failed.
            *handles += 1;
            let id = *id;
            drop(ids);
            if let Ok(new_id) = new_id {
                self.close(inode, new_id);
            }
            return Ok(id);
        }
        let new_id = new_id?;
        ids.insert(inode, (new_id, 1));
        Ok(new_id)
    }

    fn close(&self, inode: Inode, id: u32) {
        if let Err(e) = self.files.close(id) {
            warn!(
                "fuse: failed to close backing id {} of inode {}: {}",
                id, inode, e
            );
        }
    }

    /// Drop the reference of a released handle, and close the backing id of `inode` with the last
    /// one. Files that the kernel opened with the id keep using the backing file.
    pub(crate) fn release(&self, inode: Inode) {
        let mut ids = self.ids.lock().unwrap();
        if let std::collections::hash_map::Entry::Occupied(mut e) = ids.entry(inode) {
            e.get_mut().1 -= 1;
            if e.get().1 == 0 {
                let (id, _) = e.remove();
                // Nothing needs the map during the ioctl.
                drop(ids);
                self.close(inode, id);
            }
        }
    }

    /// Close the backing ids of all inodes. Otherwise the kernel keeps them until the connection
    /// ends.
    pub(crate) fn close_all(&self) {
        let ids: Vec<u32> = self
            .ids
            .lock()
            .unwrap()
            .drain()
            .map(|(_, (id, _))| id)
            .collect();
        for id in ids {
            // This fails once the connection has ended, and then there is nothing to close.
            if let Err(e) = self.files.close(id) {
                debug!("fuse: failed to close backing id {}: {}", id, e);
            }
        }
    }
}
