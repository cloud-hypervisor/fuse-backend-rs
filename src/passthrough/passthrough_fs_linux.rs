// Copyright (C) 2023 Alibaba Cloud. All rights reserved.
// Copyright 2021 Red Hat, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::{
    ffi::{CStr, OsString},
    fs::File,
    io,
    ops::Deref,
    os::{
        fd::{AsRawFd, RawFd},
        unix::ffi::OsStringExt,
    },
    path::PathBuf,
    sync::{atomic::Ordering, Arc},
};

use vm_memory::bitmap::BitmapSlice;

use crate::{abi::fuse_abi::Opcode, passthrough::util::einval};

use super::{
    file_handle::{FileHandle, OpenableFileHandle},
    inode_store::{InodeId, InodeStore},
    statx::{statx, StatExt},
    util::{enosys, eperm, openat, reopen_fd_through_proc, stat_fd},
    Inode, InodeData, InodeFile, InodeMap, PassthroughFs, MAX_HOST_INO,
};

pub type InoT = libc::ino64_t;
pub type InodeMode = u32;
pub type LibcStat = libc::stat64;
pub type OffT = libc::off64_t;
pub type StatVfs = libc::statvfs64;

#[derive(Debug)]
pub enum InodeHandle {
    File(File),
    Handle(Arc<OpenableFileHandle>),
}

impl InodeHandle {
    pub fn file_handle(&self) -> Option<&FileHandle> {
        match self {
            InodeHandle::File(_) => None,
            InodeHandle::Handle(h) => Some(h.file_handle().deref()),
        }
    }

    pub fn get_file(&self) -> io::Result<InodeFile<'_>> {
        match self {
            InodeHandle::File(f) => Ok(InodeFile::Ref(f)),
            InodeHandle::Handle(h) => {
                let f = h.open(libc::O_PATH)?;
                Ok(InodeFile::Owned(f))
            }
        }
    }

    pub fn open_file(&self, flags: libc::c_int, proc_self_fd: &File) -> io::Result<File> {
        match self {
            InodeHandle::File(f) => reopen_fd_through_proc(f, flags, proc_self_fd),
            InodeHandle::Handle(h) => h.open(flags),
        }
    }

    pub fn stat(&self) -> io::Result<LibcStat> {
        match self {
            InodeHandle::File(f) => stat_fd(f, None),
            InodeHandle::Handle(_h) => {
                let file = self.get_file()?;
                stat_fd(&file, None)
            }
        }
    }
}

impl InodeData {
    pub fn open_file(&self, flags: libc::c_int, proc_self_fd: &File) -> io::Result<File> {
        self.handle.open_file(flags, proc_self_fd)
    }
}

impl InodeMap {
    fn get_inode_locked(
        inodes: &InodeStore,
        id: &InodeId,
        handle: Option<&FileHandle>,
    ) -> Option<Inode> {
        match handle {
            Some(h) => inodes.inode_by_handle(h).copied(),
            None => inodes.inode_by_id(id).copied(),
        }
    }

    pub fn get_alt(&self, id: &InodeId, handle: Option<&FileHandle>) -> Option<Arc<InodeData>> {
        // Do not expect poisoned lock here, so safe to unwrap().
        let inodes = self.inodes.read().unwrap();

        Self::get_alt_locked(inodes.deref(), id, handle)
    }

    pub fn get_alt_locked(
        inodes: &InodeStore,
        id: &InodeId,
        handle: Option<&FileHandle>,
    ) -> Option<Arc<InodeData>> {
        handle
            .and_then(|h| inodes.get_by_handle(h))
            .or_else(|| {
                inodes.get_by_id(id).filter(|data| {
                    // When we have to fall back to looking up an inode by its IDs, ensure that
                    // we hit an entry that does not have a file handle.  Entries with file
                    // handles must also have a handle alt key, so if we have not found it by
                    // that handle alt key, we must have found an entry with a mismatching
                    // handle; i.e. an entry for a different file, even though it has the same
                    // inode ID.
                    // (This can happen when we look up a new file that has reused the inode ID
                    // of some previously unlinked inode we still have in `.inodes`.)
                    handle.is_none() || data.handle.file_handle().is_none()
                })
            })
            .map(Arc::clone)
    }
}

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    pub fn keep_fds(&self) -> Vec<RawFd> {
        vec![self.proc_self_fd.as_raw_fd()]
    }

    fn readlinkat(dfd: i32, pathname: &CStr) -> io::Result<PathBuf> {
        let mut buf = Vec::with_capacity(libc::PATH_MAX as usize);

        // Safe because the kernel will only write data to buf and we check the return value
        let buf_read = unsafe {
            libc::readlinkat(
                dfd,
                pathname.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_char,
                buf.capacity(),
            )
        };
        if buf_read < 0 {
            error!("fuse: readlinkat error");
            return Err(io::Error::last_os_error());
        }

        // Safe because we trust the value returned by kernel.
        unsafe { buf.set_len(buf_read as usize) };
        buf.shrink_to_fit();

        // Be careful:
        // - readlink() does not append a terminating null byte to buf
        // - OsString instances are not NUL terminated
        Ok(PathBuf::from(OsString::from_vec(buf)))
    }

    /// Get the file pathname corresponding to the Inode
    /// This function is used by Nydus blobfs
    pub fn readlinkat_proc_file(&self, inode: Inode) -> io::Result<PathBuf> {
        use std::ffi::CString;

        let data = self.inode_map.get(inode)?;
        let file = data.get_file()?;
        let pathname = CString::new(format!("{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        Self::readlinkat(self.proc_self_fd.as_raw_fd(), &pathname)
    }

    pub fn open_file(
        dfd: &impl AsRawFd,
        pathname: &CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<File> {
        openat(dfd, pathname, flags, mode)
    }

    fn open_file_restricted(
        &self,
        dir: &impl AsRawFd,
        pathname: &CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<File> {
        let flags = libc::O_NOFOLLOW | libc::O_CLOEXEC | flags;

        // TODO
        //if self.os_facts.has_openat2 {
        //    oslib::do_open_relative_to(dir, pathname, flags, mode)
        //} else {
        openat(dir, pathname, flags, mode)
        //}
    }

    /// Create a File or File Handle for `name` under directory `dir_fd` to support `lookup()`.
    pub fn open_file_and_handle(
        &self,
        dir: &impl AsRawFd,
        name: &CStr,
    ) -> io::Result<(File, Option<FileHandle>, StatExt)> {
        let path_file = self.open_file_restricted(dir, name, libc::O_PATH, 0)?;
        let st = statx(&path_file, None)?;
        let handle = if self.cfg.inode_file_handles {
            FileHandle::from_fd(&path_file)?
        } else {
            None
        };

        Ok((path_file, handle, st))
    }

    pub fn to_openable_handle(&self, fh: FileHandle) -> io::Result<Arc<OpenableFileHandle>> {
        fh.into_openable(&self.mount_fds, |fd, flags, _mode| {
            reopen_fd_through_proc(&fd, flags, &self.proc_self_fd)
        })
        .map(Arc::new)
        .map_err(|e| {
            if !e.silent() {
                error!("{}", e);
            }
            e.into_inner()
        })
    }

    pub fn allocate_inode(
        &self,
        inodes: &InodeStore,
        id: &InodeId,
        handle_opt: Option<&FileHandle>,
    ) -> io::Result<Inode> {
        if !self.cfg.use_host_ino {
            // If the inode has already been assigned before, the new inode is not reassigned,
            // ensuring that the same file is always the same inode
            Ok(InodeMap::get_inode_locked(inodes, id, handle_opt)
                .unwrap_or_else(|| self.next_inode.fetch_add(1, Ordering::Relaxed)))
        } else {
            let inode = if id.ino > MAX_HOST_INO {
                // Prefer looking for previous mappings from memory
                match InodeMap::get_inode_locked(inodes, id, handle_opt) {
                    Some(ino) => ino,
                    None => self.ino_allocator.get_unique_inode(id)?,
                }
            } else {
                self.ino_allocator.get_unique_inode(id)?
            };

            Ok(inode)
        }
    }

    // When seal_size is set, we don't allow operations that could change file size nor allocate
    // space beyond EOF
    pub fn seal_size_check(
        &self,
        opcode: Opcode,
        file_size: u64,
        offset: u64,
        size: u64,
        mode: i32,
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

            Opcode::Fallocate => {
                let op = mode & !(libc::FALLOC_FL_KEEP_SIZE | libc::FALLOC_FL_UNSHARE_RANGE);
                match op {
                    // Allocate, punch and zero, must not change file size.
                    0 | libc::FALLOC_FL_PUNCH_HOLE | libc::FALLOC_FL_ZERO_RANGE => {
                        if size + offset > file_size {
                            return Err(eperm());
                        }
                    }
                    // collapse and insert will change file size, forbid.
                    libc::FALLOC_FL_COLLAPSE_RANGE | libc::FALLOC_FL_INSERT_RANGE => {
                        return Err(eperm());
                    }
                    // Invalid operation
                    _ => return Err(einval()),
                }
            }

            // setattr operation should be handled in setattr handler.
            _ => return Err(enosys()),
        }

        Ok(())
    }
}

pub struct CapFsetid {}

impl Drop for CapFsetid {
    fn drop(&mut self) {
        if let Err(e) = caps::raise(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID) {
            error!("fail to restore thread cap_fsetid: {}", e);
        };
    }
}

pub fn drop_cap_fsetid() -> io::Result<Option<CapFsetid>> {
    if !caps::has_cap(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID)
        .map_err(|_e| io::Error::new(io::ErrorKind::PermissionDenied, "no CAP_FSETID capability"))?
    {
        return Ok(None);
    }
    caps::drop(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID).map_err(|_e| {
        io::Error::new(
            io::ErrorKind::PermissionDenied,
            "failed to drop CAP_FSETID capability",
        )
    })?;
    Ok(Some(CapFsetid {}))
}
