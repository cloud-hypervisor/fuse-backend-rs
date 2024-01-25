// Copyright (C) 2023 Alibaba Cloud. All rights reserved.
// Copyright 2021 Red Hat, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::{
    ffi::{CStr, CString},
    fs::File,
    io,
    ops::Deref,
    sync::{atomic::Ordering, Arc},
};

use vm_memory::bitmap::BitmapSlice;

use crate::{abi::fuse_abi::Opcode, passthrough::util::einval};

use super::{
    inode_store::{InodeId, InodeStore},
    stat::{open, stat, Stat},
    util::{enosys, eperm},
    Inode, InodeData, InodeFile, InodeMap, PassthroughFs, MAX_HOST_INO,
};

pub type InoT = libc::ino_t;
pub type InodeMode = u16;
pub type LibcStat = libc::stat;
pub type OffT = libc::off_t;
pub type StatVfs = libc::statvfs;

#[derive(Debug)]
pub enum InodeHandle {
    File(File, CString),
}

impl InodeHandle {
    pub fn get_file(&self) -> io::Result<InodeFile<'_>> {
        match self {
            InodeHandle::File(f, _) => Ok(InodeFile::Ref(f)),
        }
    }

    fn open_file(&self, flags: libc::c_int) -> io::Result<File> {
        match self {
            InodeHandle::File(_, pathname) => open(pathname, flags, 0),
        }
    }

    pub fn stat(&self) -> io::Result<Stat> {
        match self {
            InodeHandle::File(f, _) => stat(f),
        }
    }

    fn get_path(&self) -> io::Result<CString> {
        match self {
            InodeHandle::File(_, pathname) => Ok(pathname.clone()),
        }
    }
}

impl InodeData {
    pub fn open_file(&self, flags: libc::c_int) -> io::Result<File> {
        self.handle.open_file(flags)
    }

    pub fn get_path(&self) -> io::Result<CString> {
        self.handle.get_path()
    }
}

impl InodeMap {
    pub fn get_inode_locked(inodes: &InodeStore, id: &InodeId) -> Option<Inode> {
        inodes.inode_by_id(id).copied()
    }

    pub fn get_alt(&self, id: &InodeId) -> Option<Arc<InodeData>> {
        let inodes = self.inodes.read().unwrap();

        Self::get_alt_locked(inodes.deref(), id)
    }

    pub fn get_alt_locked(inodes: &InodeStore, id: &InodeId) -> Option<Arc<InodeData>> {
        inodes.get_by_id(id).map(Arc::clone)
    }
}

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    pub fn open_file(&self, pathname: &CStr) -> io::Result<(File, Stat)> {
        let path_file = self.open_file_restricted(pathname, libc::O_NOFOLLOW, 0o40777)?;
        let st = stat(&path_file)?;

        Ok((path_file, st))
    }

    fn open_file_restricted(&self, pathname: &CStr, flags: i32, mode: u32) -> io::Result<File> {
        let flags = libc::O_NOFOLLOW | libc::O_CLOEXEC | flags;
        open(pathname, flags, mode)
    }

    pub fn allocate_inode(&self, inodes: &InodeStore, id: &InodeId) -> io::Result<Inode> {
        if !self.cfg.use_host_ino {
            // If the inode has already been assigned before, the new inode is not reassigned,
            // ensuring that the same file is always the same inode
            Ok(InodeMap::get_inode_locked(inodes, id)
                .unwrap_or_else(|| self.next_inode.fetch_add(1, Ordering::Relaxed)))
        } else {
            let inode = if id.ino > MAX_HOST_INO {
                // Prefer looking for previous mappings from memory
                match InodeMap::get_inode_locked(inodes, id) {
                    Some(ino) => ino,
                    None => self.ino_allocator.get_unique_inode(id)?,
                }
            } else {
                self.ino_allocator.get_unique_inode(id)?
            };

            Ok(inode)
        }
    }

    pub fn seal_size_check(
        &self,
        opcode: Opcode,
        file_size: u64,
        offset: u64,
        size: u64,
        _mode: i32,
    ) -> io::Result<()> {
        if offset.checked_add(size).is_none() {
            error!(
                "fuse: {:?}: invalid `offset` + `size` ({}+{}) overflows u64::MAX",
                opcode, offset, size
            );
            return Err(einval());
        }

        match opcode {
            // write should not exceed the file size.
            Opcode::Write => {
                if size + offset > file_size {
                    return Err(eperm());
                }
            }

            // setattr operation should be handled in setattr handler.
            _ => return Err(enosys()),
        }

        Ok(())
    }
}
