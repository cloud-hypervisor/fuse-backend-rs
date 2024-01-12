// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Fuse passthrough file system, mirroring an existing FS hierarchy.

use std::ffi::{CStr, CString};
use std::fs::File;
use std::io;
use std::mem::{self, size_of, ManuallyDrop, MaybeUninit};
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

use super::*;
use crate::abi::fuse_abi::{CreateIn, Opcode, FOPEN_IN_KILL_SUIDGID};
#[cfg(any(feature = "vhost-user-fs", feature = "virtiofs"))]
use crate::abi::virtio_fs;
use crate::api::filesystem::{
    Context, DirEntry, Entry, FileSystem, FsOptions, GetxattrReply, ListxattrReply, OpenOptions,
    SetattrValid, ZeroCopyReader, ZeroCopyWriter,
};
use crate::bytes_to_cstr;
#[cfg(any(feature = "vhost-user-fs", feature = "virtiofs"))]
use crate::transport::FsCacheReqHandler;

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    fn open_inode(&self, inode: Inode, flags: i32) -> io::Result<File> {
        let data = self.inode_map.get(inode)?;
        if !is_safe_inode(data.mode) {
            Err(ebadf())
        } else {
            let new_flags = self.get_writeback_open_flags(flags);
            data.open_file(new_flags | libc::O_CLOEXEC)
        }
    }

    fn do_open(
        &self,
        inode: Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions, Option<u32>)> {
        let file = self.open_inode(inode, flags as i32)?;

        let data = HandleData::new(inode, file, flags);
        let handle = self.next_handle.fetch_add(1, Ordering::Relaxed);
        self.handle_map.insert(handle, data);

        let mut opts = OpenOptions::empty();
        match self.cfg.cache_policy {
            // We only set the direct I/O option on files.
            CachePolicy::Never => opts.set(
                OpenOptions::DIRECT_IO,
                flags & (libc::O_DIRECTORY as u32) == 0,
            ),
            CachePolicy::Metadata => {
                if flags & (libc::O_DIRECTORY as u32) == 0 {
                    opts |= OpenOptions::DIRECT_IO;
                } else {
                    opts |= OpenOptions::KEEP_CACHE;
                }
            }
            CachePolicy::Always => {
                opts |= OpenOptions::KEEP_CACHE;
            }
            _ => {}
        };

        Ok((Some(handle), opts, None))
    }

    fn do_getattr(&self, inode: Inode, handle: Option<Handle>) -> io::Result<(LibCStat, Duration)> {
        let st;
        let data = self.inode_map.get(inode).map_err(|e| {
            error!("fuse: do_getattr ino {} Not find err {:?}", inode, e);
            e
        })?;

        // kernel sends 0 as handle in case of no_open, and it depends on fuse server to handle
        // this case correctly.
        if !self.no_open.load(Ordering::Relaxed) && handle.is_some() {
            // Safe as we just checked handle
            let hd = self.handle_map.get(handle.unwrap(), inode)?;
            st = stat(hd.get_file());
        } else {
            st = data.handle.stat();
        }

        let st = st.map_err(|e| {
            error!("fuse: do_getattr stat failed ino {} err {:?}", inode, e);
            e
        })?;

        Ok((st.st, self.cfg.attr_timeout))
    }
}

impl<S: BitmapSlice + Send + Sync> FileSystem for PassthroughFs<S> {
    type Inode = Inode;
    type Handle = Handle;

    fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
        if self.cfg.do_import {
            self.import()?;
        }

        let mut opts = FsOptions::FILE_OPS;

        Ok(opts)
    }

    fn lookup(&self, _ctx: &Context, parent: Self::Inode, name: &CStr) -> io::Result<Entry> {
        if name.to_bytes_with_nul().contains(&SLASH_ASCII) {
            return Err(einval());
        }
        self.do_lookup(parent, name)
    }

    fn open(
        &self,
        _ctx: &Context,
        inode: Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions, Option<u32>)> {
        if self.no_open.load(Ordering::Relaxed) {
            info!("fuse: open is not supported.");
            Err(enosys())
        } else {
            self.do_open(inode, flags, fuse_flags)
        }
    }

    fn create(
        &self,
        ctx: &Context,
        parent: Inode,
        name: &CStr,
        args: CreateIn,
    ) -> io::Result<(Entry, Option<Handle>, OpenOptions, Option<u32>)> {
        self.validate_path_component(name)?;

        let dir = self.inode_map.get(parent)?;
        let dir_file = dir.get_file()?;

        let new_file = {
            let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;

            let flags = self.get_writeback_open_flags(args.flags as i32);
            Self::create_file_excl(&dir_file, name, flags, args.mode & !(args.umask & 0o777))?
        };

        let entry = self.do_lookup(parent, name)?;
        let file = match new_file {
            // File didn't exist, now created by create_file_excl()
            Some(f) => f,
            // File exists, and args.flags doesn't contain O_EXCL. Now let's open it with
            // open_inode().
            None => {
                let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;
                self.open_inode(entry.inode, args.flags as i32)?
            }
        };

        let ret_handle = if !self.no_open.load(Ordering::Relaxed) {
            let handle = self.next_handle.fetch_add(1, Ordering::Relaxed);
            let data = HandleData::new(entry.inode, file, args.flags);

            self.handle_map.insert(handle, data);
            Some(handle)
        } else {
            None
        };

        let mut opts = OpenOptions::empty();
        match self.cfg.cache_policy {
            CachePolicy::Never => opts |= OpenOptions::DIRECT_IO,
            CachePolicy::Metadata => opts |= OpenOptions::DIRECT_IO,
            CachePolicy::Always => opts |= OpenOptions::KEEP_CACHE,
            _ => {}
        };

        Ok((entry, ret_handle, opts, None))
    }

    fn getattr(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Option<Handle>,
    ) -> io::Result<(LibCStat, Duration)> {
        self.do_getattr(inode, handle)
    }
}
