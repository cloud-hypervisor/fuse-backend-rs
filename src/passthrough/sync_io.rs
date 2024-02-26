// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Fuse passthrough file system, mirroring an existing FS hierarchy.

use std::ffi::{CStr, CString};
use std::fs::File;
use std::io;
use std::mem::{ManuallyDrop, MaybeUninit};
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

#[cfg(target_os = "macos")]
use super::stat::stat as stat_fd;
#[cfg(target_os = "linux")]
use super::util::stat_fd;
use super::*;
use crate::abi::fuse_abi::{CreateIn, Opcode};
#[cfg(target_os = "linux")]
use crate::abi::fuse_abi::{FOPEN_IN_KILL_SUIDGID, WRITE_KILL_PRIV};
#[cfg(any(feature = "vhost-user-fs", feature = "virtiofs"))]
use crate::abi::virtio_fs;
use crate::api::filesystem::{
    Context, DirEntry, Entry, FileSystem, FsOptions, GetxattrReply, ListxattrReply, OpenOptions,
    SetattrValid, ZeroCopyReader, ZeroCopyWriter,
};
#[cfg(any(feature = "vhost-user-fs", feature = "virtiofs"))]
use crate::transport::FsCacheReqHandler;

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    fn open_inode(&self, inode: Inode, flags: i32) -> io::Result<File> {
        let data = self.inode_map.get(inode)?;
        if !is_safe_inode(data.mode) {
            Err(ebadf())
        } else {
            let new_flags = self.get_writeback_open_flags(flags);
            #[cfg(target_os = "linux")]
            return data.open_file(new_flags | libc::O_CLOEXEC, &self.proc_self_fd);
            #[cfg(target_os = "macos")]
            return data.open_file(new_flags | libc::O_CLOEXEC);
        }
    }

    /// Check the HandleData flags against the flags from the current request
    /// if these do not match update the file descriptor flags and store the new
    /// result in the HandleData entry
    #[inline(always)]
    fn check_fd_flags(&self, data: Arc<HandleData>, fd: RawFd, flags: u32) -> io::Result<()> {
        let open_flags = data.get_flags();
        if open_flags != flags {
            let ret = unsafe { libc::fcntl(fd, libc::F_SETFL, flags) };
            if ret != 0 {
                return Err(io::Error::last_os_error());
            }
            data.set_flags(flags);
        }
        Ok(())
    }

    pub fn do_getattr(
        &self,
        inode: Inode,
        handle: Option<Handle>,
    ) -> io::Result<(LibcStat, Duration)> {
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
            st = stat_fd(
                hd.get_file(),
                #[cfg(target_os = "linux")]
                None,
            )
        } else {
            st = data.handle.stat();
        }

        let st = st.map_err(|e| {
            error!("fuse: do_getattr stat failed ino {} err {:?}", inode, e);
            e
        })?;
        Ok((
            #[cfg(target_os = "linux")]
            st,
            #[cfg(target_os = "macos")]
            st.st,
            self.cfg.attr_timeout,
        ))
    }

    fn do_open(
        &self,
        inode: Inode,
        flags: u32,
        #[cfg(target_os = "linux")] fuse_flags: u32,
        #[cfg(target_os = "macos")] _fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions, Option<u32>)> {
        #[cfg(target_os = "linux")]
        let killpriv = if self.killpriv_v2.load(Ordering::Relaxed)
            && (fuse_flags & FOPEN_IN_KILL_SUIDGID != 0)
        {
            self::drop_cap_fsetid()?
        } else {
            None
        };
        let file = self.open_inode(inode, flags as i32)?;
        #[cfg(target_os = "linux")]
        drop(killpriv);

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
                #[cfg(target_os = "linux")]
                if flags & (libc::O_DIRECTORY as u32) == 0 {
                    opts |= OpenOptions::DIRECT_IO;
                } else {
                    opts |= OpenOptions::CACHE_DIR | OpenOptions::KEEP_CACHE;
                }

                #[cfg(target_os = "macos")]
                if flags & (libc::O_DIRECTORY as u32) == 0 {
                    opts |= OpenOptions::DIRECT_IO;
                } else {
                    opts |= OpenOptions::KEEP_CACHE;
                }
            }
            CachePolicy::Always => {
                opts |= OpenOptions::KEEP_CACHE;
                #[cfg(target_os = "linux")]
                if flags & (libc::O_DIRECTORY as u32) != 0 {
                    opts |= OpenOptions::CACHE_DIR;
                }
            }
            _ => {}
        };

        Ok((Some(handle), opts, None))
    }

    fn do_unlink(&self, parent: Inode, name: &CStr, flags: libc::c_int) -> io::Result<()> {
        let data = self.inode_map.get(parent)?;
        let file = data.get_file()?;
        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe { libc::unlinkat(file.as_raw_fd(), name.as_ptr(), flags) };

        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    pub fn get_dirdata(
        &self,
        handle: Handle,
        inode: Inode,
        flags: libc::c_int,
    ) -> io::Result<Arc<HandleData>> {
        let no_open = self.no_opendir.load(Ordering::Relaxed);
        if !no_open {
            self.handle_map.get(handle, inode)
        } else {
            let file = self.open_inode(inode, flags | libc::O_DIRECTORY)?;
            Ok(Arc::new(HandleData::new(inode, file, flags as u32)))
        }
    }

    fn get_data(
        &self,
        handle: Handle,
        inode: Inode,
        flags: libc::c_int,
    ) -> io::Result<Arc<HandleData>> {
        let no_open = self.no_open.load(Ordering::Relaxed);
        if !no_open {
            self.handle_map.get(handle, inode)
        } else {
            let file = self.open_inode(inode, flags)?;
            Ok(Arc::new(HandleData::new(inode, file, flags as u32)))
        }
    }
}

impl<S: BitmapSlice + Send + Sync> FileSystem for PassthroughFs<S> {
    type Inode = Inode;
    type Handle = Handle;

    #[cfg(target_os = "linux")]
    fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
        if self.cfg.do_import {
            self.import()?;
        }

        let mut opts = FsOptions::DO_READDIRPLUS | FsOptions::READDIRPLUS_AUTO;
        // !cfg.do_import means we are under vfs, in which case capable is already
        // negotiated and must be honored.

        if (!self.cfg.do_import || self.cfg.writeback)
            && capable.contains(FsOptions::WRITEBACK_CACHE)
        {
            opts |= FsOptions::WRITEBACK_CACHE;
            self.writeback.store(true, Ordering::Relaxed);
        }
        if (!self.cfg.do_import || self.cfg.no_open)
            && capable.contains(FsOptions::ZERO_MESSAGE_OPEN)
        {
            opts |= FsOptions::ZERO_MESSAGE_OPEN;
            // We can't support FUSE_ATOMIC_O_TRUNC with no_open
            opts.remove(FsOptions::ATOMIC_O_TRUNC);
            self.no_open.store(true, Ordering::Relaxed);
        }
        if (!self.cfg.do_import || self.cfg.no_opendir)
            && capable.contains(FsOptions::ZERO_MESSAGE_OPENDIR)
        {
            opts |= FsOptions::ZERO_MESSAGE_OPENDIR;
            self.no_opendir.store(true, Ordering::Relaxed);
        }
        if (!self.cfg.do_import || self.cfg.killpriv_v2)
            && capable.contains(FsOptions::HANDLE_KILLPRIV_V2)
        {
            opts |= FsOptions::HANDLE_KILLPRIV_V2;
            self.killpriv_v2.store(true, Ordering::Relaxed);
        }

        if capable.contains(FsOptions::PERFILE_DAX) {
            opts |= FsOptions::PERFILE_DAX;
            self.perfile_dax.store(true, Ordering::Relaxed);
        }

        Ok(opts)
    }

    #[cfg(target_os = "macos")]
    fn init(&self, _capable: FsOptions) -> io::Result<FsOptions> {
        if self.cfg.do_import {
            self.import()?;
        }

        let opts = FsOptions::ASYNC_READ | FsOptions::BIG_WRITES | FsOptions::ATOMIC_O_TRUNC;

        if !self.cfg.do_import || self.cfg.writeback {
            self.writeback.store(true, Ordering::Relaxed);
        }
        if !self.cfg.do_import || self.cfg.no_open {
            self.no_open.store(true, Ordering::Relaxed);
        }
        if !self.cfg.do_import || self.cfg.no_opendir {
            self.no_opendir.store(true, Ordering::Relaxed);
        }

        Ok(opts)
    }

    fn destroy(&self) {
        self.handle_map.clear();
        self.inode_map.clear();

        if let Err(e) = self.import() {
            error!("fuse: failed to destroy instance, {:?}", e);
        };
    }

    fn statfs(&self, _ctx: &Context, inode: Inode) -> io::Result<StatVfs> {
        let mut out = MaybeUninit::<StatVfs>::zeroed();
        let data = self.inode_map.get(inode)?;
        let file = data.get_file()?;

        // Safe because this will only modify `out` and we check the return value.
        #[cfg(target_os = "linux")]
        match unsafe { libc::fstatvfs64(file.as_raw_fd(), out.as_mut_ptr()) } {
            // Safe because the kernel guarantees that `out` has been initialized.
            0 => Ok(unsafe { out.assume_init() }),
            _ => Err(io::Error::last_os_error()),
        }
        #[cfg(target_os = "macos")]
        match unsafe { libc::fstatvfs(file.as_raw_fd(), out.as_mut_ptr()) } {
            // Safe because the kernel guarantees that `out` has been initialized.
            0 => Ok(unsafe { out.assume_init() }),
            _ => Err(io::Error::last_os_error()),
        }
    }

    fn lookup(&self, _ctx: &Context, parent: Inode, name: &CStr) -> io::Result<Entry> {
        // Don't use is_safe_path_component(), allow "." and ".." for NFS export support
        if name.to_bytes_with_nul().contains(&SLASH_ASCII) {
            return Err(einval());
        }
        self.do_lookup(parent, name)
    }

    fn forget(&self, _ctx: &Context, inode: Inode, count: u64) {
        let mut inodes = self.inode_map.get_map_mut();

        self.forget_one(&mut inodes, inode, count)
    }

    fn batch_forget(&self, _ctx: &Context, requests: Vec<(Inode, u64)>) {
        let mut inodes = self.inode_map.get_map_mut();

        for (inode, count) in requests {
            self.forget_one(&mut inodes, inode, count)
        }
    }

    fn opendir(
        &self,
        _ctx: &Context,
        inode: Inode,
        flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions)> {
        if self.no_opendir.load(Ordering::Relaxed) {
            info!("fuse: opendir is not supported.");
            Err(enosys())
        } else {
            self.do_open(inode, flags | (libc::O_DIRECTORY as u32), 0)
                .map(|(a, b, _)| (a, b))
        }
    }

    fn releasedir(
        &self,
        _ctx: &Context,
        inode: Inode,
        _flags: u32,
        handle: Handle,
    ) -> io::Result<()> {
        self.do_release(inode, handle)
    }

    fn mkdir(
        &self,
        ctx: &Context,
        parent: Inode,
        name: &CStr,
        mode: u32,
        umask: u32,
    ) -> io::Result<Entry> {
        self.validate_path_component(name)?;

        let data = self.inode_map.get(parent)?;

        let res = {
            let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;

            let file = data.get_file()?;
            // Safe because this doesn't modify any memory and we check the return value.
            #[cfg(target_os = "macos")]
            unsafe {
                libc::mkdirat(
                    file.as_raw_fd(),
                    name.as_ptr(),
                    (mode & !umask) as libc::mode_t,
                )
            }
            #[cfg(target_os = "linux")]
            unsafe {
                libc::mkdirat(file.as_raw_fd(), name.as_ptr(), mode & !umask)
            }
        };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }

        self.do_lookup(parent, name)
    }

    fn rmdir(&self, _ctx: &Context, parent: Inode, name: &CStr) -> io::Result<()> {
        self.validate_path_component(name)?;
        self.do_unlink(parent, name, libc::AT_REMOVEDIR)
    }

    fn readdir(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry) -> io::Result<usize>,
    ) -> io::Result<()> {
        if self.no_readdir.load(Ordering::Relaxed) {
            return Ok(());
        }
        self.do_readdir(inode, handle, size, offset, &mut |mut dir_entry, _dir| {
            dir_entry.ino = {
                // Safe because do_readdir() has ensured dir_entry.name is a
                // valid [u8] generated by CStr::to_bytes().
                let name = unsafe {
                    CStr::from_bytes_with_nul_unchecked(std::slice::from_raw_parts(
                        &dir_entry.name[0],
                        dir_entry.name.len() + 1,
                    ))
                };

                let entry = self.do_lookup(inode, name)?;
                let mut inodes = self.inode_map.get_map_mut();
                self.forget_one(&mut inodes, entry.inode, 1);
                entry.inode
            };

            add_entry(dir_entry)
        })
    }

    fn readdirplus(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, Entry) -> io::Result<usize>,
    ) -> io::Result<()> {
        if self.no_readdir.load(Ordering::Relaxed) {
            return Ok(());
        }
        self.do_readdir(inode, handle, size, offset, &mut |mut dir_entry, _dir| {
            // Safe because do_readdir() has ensured dir_entry.name is a
            // valid [u8] generated by CStr::to_bytes().
            let name = unsafe {
                CStr::from_bytes_with_nul_unchecked(std::slice::from_raw_parts(
                    &dir_entry.name[0],
                    dir_entry.name.len() + 1,
                ))
            };
            let entry = self.do_lookup(inode, name)?;
            let ino = entry.inode;
            dir_entry.ino = entry.attr.st_ino;

            add_entry(dir_entry, entry).map(|r| {
                // true when size is not large enough to hold entry.
                if r == 0 {
                    // Release the refcount acquired by self.do_lookup().
                    let mut inodes = self.inode_map.get_map_mut();
                    self.forget_one(&mut inodes, ino, 1);
                }
                r
            })
        })
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

    fn release(
        &self,
        _ctx: &Context,
        inode: Inode,
        _flags: u32,
        handle: Handle,
        _flush: bool,
        _flock_release: bool,
        _lock_owner: Option<u64>,
    ) -> io::Result<()> {
        if self.no_open.load(Ordering::Relaxed) {
            Err(enosys())
        } else {
            self.do_release(inode, handle)
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
                // Cap restored when _killpriv is dropped
                #[cfg(target_os = "linux")]
                let _killpriv = if self.killpriv_v2.load(Ordering::Relaxed)
                    && (args.fuse_flags & FOPEN_IN_KILL_SUIDGID != 0)
                {
                    self::drop_cap_fsetid()?
                } else {
                    None
                };

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

    fn unlink(&self, _ctx: &Context, parent: Inode, name: &CStr) -> io::Result<()> {
        self.validate_path_component(name)?;
        self.do_unlink(parent, name, 0)
    }

    #[cfg(any(feature = "vhost-user-fs", feature = "virtiofs"))]
    fn setupmapping(
        &self,
        _ctx: &Context,
        inode: Inode,
        _handle: Handle,
        foffset: u64,
        len: u64,
        flags: u64,
        moffset: u64,
        vu_req: &mut dyn FsCacheReqHandler,
    ) -> io::Result<()> {
        debug!(
            "fuse: setupmapping ino {:?} foffset 0x{:x} len 0x{:x} flags 0x{:x} moffset 0x{:x}",
            inode, foffset, len, flags, moffset
        );

        let open_flags = if (flags & virtio_fs::SetupmappingFlags::WRITE.bits()) != 0 {
            libc::O_RDWR
        } else {
            libc::O_RDONLY
        };

        let file = self.open_inode(inode, open_flags)?;
        (*vu_req).map(foffset, moffset, len, flags, file.as_raw_fd())
    }

    #[cfg(any(feature = "vhost-user-fs", feature = "virtiofs"))]
    fn removemapping(
        &self,
        _ctx: &Context,
        _inode: Inode,
        requests: Vec<virtio_fs::RemovemappingOne>,
        vu_req: &mut dyn FsCacheReqHandler,
    ) -> io::Result<()> {
        (*vu_req).unmap(requests)
    }

    fn read(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        w: &mut dyn ZeroCopyWriter,
        size: u32,
        offset: u64,
        _lock_owner: Option<u64>,
        flags: u32,
    ) -> io::Result<usize> {
        let data = self.get_data(handle, inode, libc::O_RDONLY)?;

        // Manually implement File::try_clone() by borrowing fd of data.file instead of dup().
        // It's safe because the `data` variable's lifetime spans the whole function,
        // so data.file won't be closed.
        let f = unsafe { File::from_raw_fd(data.borrow_fd().as_raw_fd()) };

        self.check_fd_flags(data.clone(), f.as_raw_fd(), flags)?;

        let mut f = ManuallyDrop::new(f);

        w.write_from(&mut *f, size as usize, offset)
    }

    fn write(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        r: &mut dyn ZeroCopyReader,
        size: u32,
        offset: u64,
        _lock_owner: Option<u64>,
        _delayed_write: bool,
        flags: u32,
        #[cfg(target_os = "linux")] fuse_flags: u32,
        #[cfg(target_os = "macos")] _fuse_flags: u32,
    ) -> io::Result<usize> {
        let data = self.get_data(handle, inode, libc::O_RDWR)?;

        // Manually implement File::try_clone() by borrowing fd of data.file instead of dup().
        // It's safe because the `data` variable's lifetime spans the whole function,
        // so data.file won't be closed.
        let f = unsafe { File::from_raw_fd(data.borrow_fd().as_raw_fd()) };

        self.check_fd_flags(data.clone(), f.as_raw_fd(), flags)?;

        if self.seal_size.load(Ordering::Relaxed) {
            #[cfg(target_os = "linux")]
            let st = stat_fd(&f, None)?;

            #[cfg(target_os = "macos")]
            let st = stat(&f)?.st;
            self.seal_size_check(Opcode::Write, st.st_size as u64, offset, size as u64, 0)?;
        }

        let mut f = ManuallyDrop::new(f);

        // Cap restored when _killpriv is dropped
        #[cfg(target_os = "linux")]
        let _killpriv =
            if self.killpriv_v2.load(Ordering::Relaxed) && (fuse_flags & WRITE_KILL_PRIV != 0) {
                self::drop_cap_fsetid()?
            } else {
                None
            };

        r.read_to(&mut *f, size as usize, offset)
    }

    fn getattr(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Option<Handle>,
    ) -> io::Result<(LibcStat, Duration)> {
        self.do_getattr(inode, handle)
    }

    fn setattr(
        &self,
        _ctx: &Context,
        inode: Inode,
        attr: LibcStat,
        handle: Option<Handle>,
        valid: SetattrValid,
    ) -> io::Result<(LibcStat, Duration)> {
        let inode_data = self.inode_map.get(inode)?;

        enum Data {
            Handle(Arc<HandleData>),
            ProcPath(CString),
        }

        let file = inode_data.get_file()?;
        #[cfg(target_os = "linux")]
        let data = if self.no_open.load(Ordering::Relaxed) {
            let pathname = CString::new(format!("{}", file.as_raw_fd()))
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            Data::ProcPath(pathname)
        } else {
            // If we have a handle then use it otherwise get a new fd from the inode.
            if let Some(handle) = handle {
                let hd = self.handle_map.get(handle, inode)?;
                Data::Handle(hd)
            } else {
                let pathname = CString::new(format!("{}", file.as_raw_fd()))
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
                Data::ProcPath(pathname)
            }
        };

        #[cfg(target_os = "macos")]
        let data = if self.no_open.load(Ordering::Relaxed) {
            let pathname = inode_data.get_path()?;
            Data::ProcPath(pathname)
        } else {
            // If we have a handle then use it otherwise get a new fd from the inode.
            if let Some(handle) = handle {
                let hd = self.handle_map.get(handle, inode)?;
                Data::Handle(hd)
            } else {
                let pathname = inode_data.get_path()?;
                Data::ProcPath(pathname)
            }
        };

        if valid.contains(SetattrValid::SIZE) && self.seal_size.load(Ordering::Relaxed) {
            return Err(io::Error::from_raw_os_error(libc::EPERM));
        }

        if valid.contains(SetattrValid::MODE) {
            // Safe because this doesn't modify any memory and we check the return value.
            let res = unsafe {
                match data {
                    Data::Handle(ref h) => libc::fchmod(h.borrow_fd().as_raw_fd(), attr.st_mode),
                    #[cfg(target_os = "linux")]
                    Data::ProcPath(ref p) => {
                        libc::fchmodat(self.proc_self_fd.as_raw_fd(), p.as_ptr(), attr.st_mode, 0)
                    }
                    #[cfg(target_os = "macos")]
                    Data::ProcPath(ref p) => libc::chmod(p.as_ptr(), attr.st_mode),
                }
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
        }

        if valid.intersects(SetattrValid::UID | SetattrValid::GID) {
            let uid = if valid.contains(SetattrValid::UID) {
                attr.st_uid
            } else {
                // Cannot use -1 here because these are unsigned values.
                u32::MAX
            };
            let gid = if valid.contains(SetattrValid::GID) {
                attr.st_gid
            } else {
                // Cannot use -1 here because these are unsigned values.
                u32::MAX
            };

            // Safe because this is a constant value and a valid C string.
            let empty = unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) };

            // Safe because this doesn't modify any memory and we check the return value.
            #[cfg(target_os = "linux")]
            let res = unsafe {
                libc::fchownat(
                    file.as_raw_fd(),
                    empty.as_ptr(),
                    uid,
                    gid,
                    libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
                )
            };
            #[cfg(target_os = "macos")]
            let res = unsafe {
                libc::fchownat(
                    file.as_raw_fd(),
                    empty.as_ptr(),
                    uid,
                    gid,
                    libc::AT_SYMLINK_NOFOLLOW,
                )
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
        }

        if valid.contains(SetattrValid::SIZE) {
            // Cap restored when _killpriv is dropped
            #[cfg(target_os = "linux")]
            let _killpriv = if self.killpriv_v2.load(Ordering::Relaxed)
                && valid.contains(SetattrValid::KILL_SUIDGID)
            {
                self::drop_cap_fsetid()?
            } else {
                None
            };

            // Safe because this doesn't modify any memory and we check the return value.
            let res = match data {
                Data::Handle(ref h) => unsafe {
                    libc::ftruncate(h.borrow_fd().as_raw_fd(), attr.st_size)
                },
                _ => {
                    // There is no `ftruncateat` so we need to get a new fd and truncate it.
                    let f = self.open_inode(inode, libc::O_NONBLOCK | libc::O_RDWR)?;
                    unsafe { libc::ftruncate(f.as_raw_fd(), attr.st_size) }
                }
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
        }

        if valid.intersects(SetattrValid::ATIME | SetattrValid::MTIME) {
            let mut tvs = [
                libc::timespec {
                    tv_sec: 0,
                    tv_nsec: libc::UTIME_OMIT,
                },
                libc::timespec {
                    tv_sec: 0,
                    tv_nsec: libc::UTIME_OMIT,
                },
            ];

            if valid.contains(SetattrValid::ATIME_NOW) {
                tvs[0].tv_nsec = libc::UTIME_NOW;
            } else if valid.contains(SetattrValid::ATIME) {
                tvs[0].tv_sec = attr.st_atime;
                tvs[0].tv_nsec = attr.st_atime_nsec;
            }

            if valid.contains(SetattrValid::MTIME_NOW) {
                tvs[1].tv_nsec = libc::UTIME_NOW;
            } else if valid.contains(SetattrValid::MTIME) {
                tvs[1].tv_sec = attr.st_mtime;
                tvs[1].tv_nsec = attr.st_mtime_nsec;
            }

            // Safe because this doesn't modify any memory and we check the return value.
            let res = match data {
                Data::Handle(ref h) => unsafe {
                    libc::futimens(h.borrow_fd().as_raw_fd(), tvs.as_ptr())
                },
                #[cfg(target_os = "linux")]
                Data::ProcPath(ref p) => unsafe {
                    libc::utimensat(self.proc_self_fd.as_raw_fd(), p.as_ptr(), tvs.as_ptr(), 0)
                },
                #[cfg(target_os = "macos")]
                Data::ProcPath(ref p) => {
                    let tvs = [
                        libc::timeval {
                            tv_sec: tvs[0].tv_sec,
                            tv_usec: (tvs[0].tv_nsec / 1000) as i32,
                        },
                        libc::timeval {
                            tv_sec: tvs[1].tv_sec,
                            tv_usec: (tvs[1].tv_nsec / 1000) as i32,
                        },
                    ];
                    unsafe { libc::utimes(p.as_ptr(), tvs.as_ptr()) }
                }
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
        }

        self.do_getattr(inode, handle)
    }

    fn rename(
        &self,
        _ctx: &Context,
        olddir: Inode,
        oldname: &CStr,
        newdir: Inode,
        newname: &CStr,
        #[cfg(target_os = "linux")] flags: u32,
        #[cfg(target_os = "macos")] _flags: u32,
    ) -> io::Result<()> {
        self.validate_path_component(oldname)?;
        self.validate_path_component(newname)?;

        let old_inode = self.inode_map.get(olddir)?;
        let new_inode = self.inode_map.get(newdir)?;
        let old_file = old_inode.get_file()?;
        let new_file = new_inode.get_file()?;

        // Safe because this doesn't modify any memory and we check the return value.
        // TODO: Switch to libc::renameat2 once https://github.com/rust-lang/libc/pull/1508 lands
        // and we have glibc 2.28.
        #[cfg(target_os = "linux")]
        let res = unsafe {
            libc::syscall(
                libc::SYS_renameat2,
                old_file.as_raw_fd(),
                oldname.as_ptr(),
                new_file.as_raw_fd(),
                newname.as_ptr(),
                flags,
            )
        };

        #[cfg(target_os = "macos")]
        let res = unsafe {
            libc::renameat(
                old_file.as_raw_fd(),
                oldname.as_ptr(),
                new_file.as_raw_fd(),
                newname.as_ptr(),
            )
        };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn mknod(
        &self,
        ctx: &Context,
        parent: Inode,
        name: &CStr,
        mode: u32,
        rdev: u32,
        umask: u32,
    ) -> io::Result<Entry> {
        self.validate_path_component(name)?;

        let data = self.inode_map.get(parent)?;
        #[cfg(target_os = "linux")]
        let file = data.get_file()?;
        #[cfg(target_os = "macos")]
        let pathname = data.get_path()?;

        let res = {
            let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;

            // Safe because this doesn't modify any memory and we check the return value.
            #[cfg(target_os = "linux")]
            unsafe {
                libc::mknodat(
                    file.as_raw_fd(),
                    name.as_ptr(),
                    (mode & !umask) as libc::mode_t,
                    u64::from(rdev),
                )
            }
            #[cfg(target_os = "macos")]
            unsafe {
                libc::mknod(
                    pathname.as_ptr(),
                    (mode & !umask) as libc::mode_t,
                    rdev as i32,
                )
            }
        };
        if res < 0 {
            Err(io::Error::last_os_error())
        } else {
            self.do_lookup(parent, name)
        }
    }

    fn link(
        &self,
        _ctx: &Context,
        inode: Inode,
        newparent: Inode,
        newname: &CStr,
    ) -> io::Result<Entry> {
        self.validate_path_component(newname)?;

        let data = self.inode_map.get(inode)?;
        let new_inode = self.inode_map.get(newparent)?;
        let file = data.get_file()?;
        let new_file = new_inode.get_file()?;

        // Safe because this is a constant value and a valid C string.
        let empty = unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) };

        // Safe because this doesn't modify any memory and we check the return value.
        #[cfg(target_os = "linux")]
        let res = unsafe {
            libc::linkat(
                file.as_raw_fd(),
                empty.as_ptr(),
                new_file.as_raw_fd(),
                newname.as_ptr(),
                libc::AT_EMPTY_PATH,
            )
        };
        #[cfg(target_os = "macos")]
        let res = unsafe {
            libc::linkat(
                file.as_raw_fd(),
                empty.as_ptr(),
                new_file.as_raw_fd(),
                newname.as_ptr(),
                libc::AT_FDCWD,
            )
        };
        if res == 0 {
            self.do_lookup(newparent, newname)
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn symlink(
        &self,
        ctx: &Context,
        linkname: &CStr,
        parent: Inode,
        name: &CStr,
    ) -> io::Result<Entry> {
        self.validate_path_component(name)?;

        let data = self.inode_map.get(parent)?;

        let res = {
            let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;

            let file = data.get_file()?;
            // Safe because this doesn't modify any memory and we check the return value.
            unsafe { libc::symlinkat(linkname.as_ptr(), file.as_raw_fd(), name.as_ptr()) }
        };
        if res == 0 {
            self.do_lookup(parent, name)
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn readlink(&self, _ctx: &Context, inode: Inode) -> io::Result<Vec<u8>> {
        // Safe because this is a constant value and a valid C string.
        let empty = unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) };
        let mut buf = Vec::<u8>::with_capacity(libc::PATH_MAX as usize);
        let data = self.inode_map.get(inode)?;
        let file = data.get_file()?;

        // Safe because this will only modify the contents of `buf` and we check the return value.
        let res = unsafe {
            libc::readlinkat(
                file.as_raw_fd(),
                empty.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_char,
                libc::PATH_MAX as usize,
            )
        };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }

        // Safe because we trust the value returned by kernel.
        unsafe { buf.set_len(res as usize) };

        Ok(buf)
    }

    fn flush(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        _lock_owner: u64,
    ) -> io::Result<()> {
        if self.no_open.load(Ordering::Relaxed) {
            return Err(enosys());
        }

        let data = self.handle_map.get(handle, inode)?;

        // Since this method is called whenever an fd is closed in the client, we can emulate that
        // behavior by doing the same thing (dup-ing the fd and then immediately closing it). Safe
        // because this doesn't modify any memory and we check the return values.
        unsafe {
            let newfd = libc::dup(data.borrow_fd().as_raw_fd());
            if newfd < 0 {
                return Err(io::Error::last_os_error());
            }

            if libc::close(newfd) < 0 {
                Err(io::Error::last_os_error())
            } else {
                Ok(())
            }
        }
    }

    fn fsync(
        &self,
        _ctx: &Context,
        inode: Inode,
        #[cfg(target_os = "linux")] datasync: bool,
        #[cfg(target_os = "macos")] _datasync: bool,
        handle: Handle,
    ) -> io::Result<()> {
        let data = self.get_data(handle, inode, libc::O_RDONLY)?;
        let fd = data.borrow_fd();

        // Safe because this doesn't modify any memory and we check the return value.
        #[cfg(target_os = "linux")]
        let res = unsafe {
            if datasync {
                libc::fdatasync(fd.as_raw_fd())
            } else {
                libc::fsync(fd.as_raw_fd())
            }
        };
        #[cfg(target_os = "macos")]
        let res = unsafe { libc::fsync(fd.as_raw_fd()) };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn fsyncdir(
        &self,
        ctx: &Context,
        inode: Inode,
        datasync: bool,
        handle: Handle,
    ) -> io::Result<()> {
        self.fsync(ctx, inode, datasync, handle)
    }

    fn access(&self, ctx: &Context, inode: Inode, mask: u32) -> io::Result<()> {
        let data = self.inode_map.get(inode)?;
        #[cfg(target_os = "linux")]
        let st = stat_fd(&data.get_file()?, None)?;
        #[cfg(target_os = "macos")]
        let st = stat(&data.get_file()?)?.st;
        let mode = mask as i32 & (libc::R_OK | libc::W_OK | libc::X_OK);

        if mode == libc::F_OK {
            // The file exists since we were able to call `stat(2)` on it.
            return Ok(());
        }

        if (mode & libc::R_OK) != 0
            && ctx.uid != 0
            && (st.st_uid != ctx.uid || st.st_mode & 0o400 == 0)
            && (st.st_gid != ctx.gid || st.st_mode & 0o040 == 0)
            && st.st_mode & 0o004 == 0
        {
            return Err(io::Error::from_raw_os_error(libc::EACCES));
        }

        if (mode & libc::W_OK) != 0
            && ctx.uid != 0
            && (st.st_uid != ctx.uid || st.st_mode & 0o200 == 0)
            && (st.st_gid != ctx.gid || st.st_mode & 0o020 == 0)
            && st.st_mode & 0o002 == 0
        {
            return Err(io::Error::from_raw_os_error(libc::EACCES));
        }

        // root can only execute something if it is executable by one of the owner, the group, or
        // everyone.
        if (mode & libc::X_OK) != 0
            && (ctx.uid != 0 || st.st_mode & 0o111 == 0)
            && (st.st_uid != ctx.uid || st.st_mode & 0o100 == 0)
            && (st.st_gid != ctx.gid || st.st_mode & 0o010 == 0)
            && st.st_mode & 0o001 == 0
        {
            return Err(io::Error::from_raw_os_error(libc::EACCES));
        }

        Ok(())
    }

    fn setxattr(
        &self,
        _ctx: &Context,
        inode: Inode,
        name: &CStr,
        value: &[u8],
        flags: u32,
    ) -> io::Result<()> {
        if !self.cfg.xattr {
            return Err(enosys());
        }

        let data = self.inode_map.get(inode)?;
        #[cfg(target_os = "linux")]
        let file = data.get_file()?;
        #[cfg(target_os = "linux")]
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        #[cfg(target_os = "macos")]
        let pathname = data.get_path()?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this doesn't modify any memory and we check the return value.
        #[cfg(target_os = "linux")]
        let res = unsafe {
            libc::setxattr(
                pathname.as_ptr(),
                name.as_ptr(),
                value.as_ptr() as *const libc::c_void,
                value.len(),
                flags as libc::c_int,
            )
        };
        #[cfg(target_os = "macos")]
        let res = unsafe {
            libc::setxattr(
                pathname.as_ptr(),
                name.as_ptr(),
                value.as_ptr() as *const libc::c_void,
                value.len(),
                0,
                flags as libc::c_int,
            )
        };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn getxattr(
        &self,
        _ctx: &Context,
        inode: Inode,
        name: &CStr,
        size: u32,
    ) -> io::Result<GetxattrReply> {
        if !self.cfg.xattr {
            return Err(enosys());
        }

        let data = self.inode_map.get(inode)?;
        #[cfg(target_os = "linux")]
        let file = data.get_file()?;
        let mut buf = Vec::<u8>::with_capacity(size as usize);
        #[cfg(target_os = "linux")]
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd(),))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        #[cfg(target_os = "macos")]
        let pathname = data.get_path()?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this will only modify the contents of `buf`.
        #[cfg(target_os = "linux")]
        let res = unsafe {
            libc::getxattr(
                pathname.as_ptr(),
                name.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_void,
                size as libc::size_t,
            )
        };
        #[cfg(target_os = "macos")]
        let res = unsafe {
            libc::getxattr(
                pathname.as_ptr(),
                name.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_void,
                size as libc::size_t,
                0,
                0,
            )
        };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }

        if size == 0 {
            Ok(GetxattrReply::Count(res as u32))
        } else {
            // Safe because we trust the value returned by kernel.
            unsafe { buf.set_len(res as usize) };
            Ok(GetxattrReply::Value(buf))
        }
    }

    fn listxattr(&self, _ctx: &Context, inode: Inode, size: u32) -> io::Result<ListxattrReply> {
        if !self.cfg.xattr {
            return Err(enosys());
        }

        let data = self.inode_map.get(inode)?;
        #[cfg(target_os = "linux")]
        let file = data.get_file()?;
        let mut buf = Vec::<u8>::with_capacity(size as usize);
        #[cfg(target_os = "linux")]
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        #[cfg(target_os = "macos")]
        let pathname = data.get_path()?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this will only modify the contents of `buf`.
        #[cfg(target_os = "linux")]
        let res = unsafe {
            libc::listxattr(
                pathname.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_char,
                size as libc::size_t,
            )
        };
        #[cfg(target_os = "macos")]
        let res = unsafe {
            libc::listxattr(
                pathname.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_char,
                size as libc::size_t,
                0,
            )
        };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }

        if size == 0 {
            Ok(ListxattrReply::Count(res as u32))
        } else {
            // Safe because we trust the value returned by kernel.
            unsafe { buf.set_len(res as usize) };
            Ok(ListxattrReply::Names(buf))
        }
    }

    fn removexattr(&self, _ctx: &Context, inode: Inode, name: &CStr) -> io::Result<()> {
        if !self.cfg.xattr {
            return Err(enosys());
        }

        let data = self.inode_map.get(inode)?;
        #[cfg(target_os = "linux")]
        let file = data.get_file()?;
        #[cfg(target_os = "linux")]
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        #[cfg(target_os = "macos")]
        let pathname = data.get_path()?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this doesn't modify any memory and we check the return value.
        #[cfg(target_os = "linux")]
        let res = unsafe { libc::removexattr(pathname.as_ptr(), name.as_ptr()) };
        #[cfg(target_os = "macos")]
        let res = unsafe { libc::removexattr(pathname.as_ptr(), name.as_ptr(), 0) };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    #[cfg(target_os = "linux")]
    fn fallocate(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> io::Result<()> {
        // Let the Arc<HandleData> in scope, otherwise fd may get invalid.
        let data = self.get_data(handle, inode, libc::O_RDWR)?;
        let fd = data.borrow_fd();

        if self.seal_size.load(Ordering::Relaxed) {
            let st = stat_fd(&fd, None)?;
            self.seal_size_check(
                Opcode::Fallocate,
                st.st_size as u64,
                offset,
                length,
                mode as i32,
            )?;
        }

        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe {
            libc::fallocate64(
                fd.as_raw_fd(),
                mode as libc::c_int,
                offset as libc::off64_t,
                length as libc::off64_t,
            )
        };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn lseek(
        &self,
        _ctx: &Context,
        inode: Inode,
        handle: Handle,
        offset: u64,
        whence: u32,
    ) -> io::Result<u64> {
        // Let the Arc<HandleData> in scope, otherwise fd may get invalid.
        let data = self.handle_map.get(handle, inode)?;

        // Acquire the lock to get exclusive access, otherwise it may break do_readdir().
        let (_guard, file) = data.get_file_mut();

        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe { libc::lseek(file.as_raw_fd(), offset as OffT, whence as libc::c_int) };
        if res < 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(res as u64)
        }
    }
}
