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

use super::os_compat::LinuxDirent64;
use super::util::{stat_fd, sync_fd};
use super::*;
use crate::abi::fuse_abi::{CreateIn, Opcode, FOPEN_IN_KILL_SUIDGID, WRITE_KILL_PRIV};
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
            let mut new_flags = self.get_writeback_open_flags(flags);
            if !self.cfg.allow_direct_io && flags & libc::O_DIRECT != 0 {
                new_flags &= !libc::O_DIRECT;
            }
            data.open_file(new_flags | libc::O_CLOEXEC, &self.proc_self_fd)
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

    /// Skip entries in a getdents64 buffer up to and including the entry whose
    /// `d_off` equals `offset`.  After this returns, `buf` starts with the entry
    /// immediately after the matched one.  Returns `true` if the target cookie
    /// was found, `false` otherwise.
    fn skip_to_cookie(buf: &mut Vec<u8>, offset: u64) -> bool {
        let mut cur: usize = 0;
        let mut found = false;
        let mut target_reclen: usize = 0;
        while cur + size_of::<LinuxDirent64>() <= buf.len() {
            let front = &buf[cur..cur + size_of::<LinuxDirent64>()];
            let dirent64 = LinuxDirent64::from_slice(front)
                .expect("fuse: unable to get LinuxDirent64 from slice");
            let reclen = dirent64.d_reclen as usize;
            // Defend against a malformed getdents64 buffer: a record shorter
            // than the header would loop forever.
            if reclen < size_of::<LinuxDirent64>() {
                break;
            }
            if dirent64.d_off as u64 == offset {
                found = true;
                target_reclen = reclen;
                break;
            }
            cur += reclen;
        }

        if found {
            cur += target_reclen;
            buf.drain(..cur);
        }
        found
    }

    /// Return the `d_off` of the last dirent in a `getdents64` buffer, or
    /// `None` if the buffer is empty.
    fn last_cookie_in_buf(mut buf: &[u8]) -> Option<u64> {
        let mut last = None;
        while buf.len() >= size_of::<LinuxDirent64>() {
            let dirent64 = LinuxDirent64::from_slice(&buf[..size_of::<LinuxDirent64>()])
                .expect("fuse: unable to get LinuxDirent64 from slice");
            let reclen = dirent64.d_reclen as usize;
            // Defend against a malformed getdents64 buffer: a record shorter
            // than the header would loop forever and an oversized one would
            // index out of bounds below.
            if reclen < size_of::<LinuxDirent64>() || reclen > buf.len() {
                break;
            }
            last = Some(dirent64.d_off as u64);
            buf = &buf[reclen..];
        }
        last
    }

    /// Consume the cookie cached for `handle` and report whether it equals
    /// `offset`.  A match means the persistent directory fd is already
    /// positioned right after that entry and the next `getdents64` can start
    /// without an `lseek64`.  The entry is removed either way: a cookie that
    /// doesn't match the requested offset is stale and must not be reused.
    ///
    /// In `no_opendir` mode every READDIR works on a fresh fd at position 0,
    /// so there is no position to remember and the cache must not be used.
    fn consume_cached_cookie(&self, handle: Handle, offset: u64) -> bool {
        if self.no_opendir.load(Ordering::Relaxed) {
            return false;
        }
        self.handle_map
            .remove_cookie(handle)
            .is_some_and(|cookie| cookie == offset)
    }

    /// Record the position of the directory fd of `handle`: the `d_off` of the last dirent in
    /// `buf`, i.e. right after the last entry returned by `getdents64`.  A subsequent resume
    /// from that cookie can then skip the `lseek64`/scan (see `consume_cached_cookie`).  Does
    /// nothing for an empty `buf` (end-of-directory) or in `no_opendir` mode, where directory
    /// fds are never reused.
    fn cache_cookie(&self, handle: Handle, buf: &[u8]) {
        if self.no_opendir.load(Ordering::Relaxed) {
            return;
        }
        if let Some(cookie) = Self::last_cookie_in_buf(buf) {
            self.handle_map.set_cookie(handle, cookie);
        }
    }

    fn do_readdir(
        &self,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, RawFd) -> io::Result<usize>,
    ) -> io::Result<()> {
        if size == 0 {
            return Ok(());
        }

        let mut buf = Vec::<u8>::with_capacity(size as usize);
        let data = self.get_dirdata(handle, inode, libc::O_RDONLY)?;

        {
            // Since we are going to work with the kernel offset, we have to acquire the file lock
            // for both the `lseek64` and `getdents64` syscalls to ensure that no other thread
            // changes the kernel offset while we are using it.
            let (guard, dir) = data.get_file_mut();

            // Fast path: if the guest resumes from exactly the cookie recorded by the previous
            // call, the fd is already positioned right after that entry and the `lseek64` below
            // can be skipped entirely — O(1) instead of O(n) for sequential readdir.
            let cookie_hit = self.consume_cached_cookie(handle, offset);

            // NFSv4 directory cookies (`nfs_cookie4`, RFC 7530) are unsigned 64-bit and roughly
            // half exceed `INT64_MAX`. When the guest resumes a readdir from such a cookie, the
            // `u64` -> `off64_t` cast produces a negative value and the host kernel's
            // `nfs_llseek_dir()` rejects it with `EINVAL`. In that case fall back to a linear scan
            // from the beginning, skipping past the target cookie so the caller receives exactly the
            // entries it has not seen yet.
            let seek_ok = if cookie_hit {
                true
            } else if offset > i64::MAX as u64 {
                false
            } else {
                // Safe because this doesn't modify any memory and we check the return value.
                let res = unsafe {
                    libc::lseek64(dir.as_raw_fd(), offset as libc::off64_t, libc::SEEK_SET)
                };
                if res >= 0 {
                    true
                } else {
                    let err = io::Error::last_os_error();
                    // Only the "offset too large" case is recoverable here.
                    if err.raw_os_error() != Some(libc::EINVAL) {
                        return Err(err);
                    }
                    false
                }
            };

            if seek_ok {
                // Safe because the kernel guarantees that it will only write to `buf` and we check
                // the return value.
                let res = unsafe {
                    libc::syscall(
                        libc::SYS_getdents64,
                        dir.as_raw_fd(),
                        buf.as_mut_ptr() as *mut LinuxDirent64,
                        size as libc::c_int,
                    )
                };
                if res < 0 {
                    return Err(io::Error::last_os_error());
                }
                // Safe because we trust the value returned by kernel.
                unsafe { buf.set_len(res as usize) };
            } else {
                // Fallback for cookies the kernel cannot `lseek()` to: rewind and walk batches with
                // `getdents64` until the entry whose `d_off == offset` is consumed, then return the
                // entries after it. We never re-seek nor discard an already-read batch, so no
                // entries are lost.
                //
                // Safe because this doesn't modify any memory and we check the return value.
                let res = unsafe { libc::lseek64(dir.as_raw_fd(), 0, libc::SEEK_SET) };
                if res < 0 {
                    return Err(io::Error::last_os_error());
                }

                let mut found = false;
                loop {
                    // Safe because the kernel guarantees that it will only write to `buf` and we
                    // check the return value.
                    let res = unsafe {
                        libc::syscall(
                            libc::SYS_getdents64,
                            dir.as_raw_fd(),
                            buf.as_mut_ptr() as *mut LinuxDirent64,
                            size as libc::c_int,
                        )
                    };
                    if res < 0 {
                        return Err(io::Error::last_os_error());
                    }
                    // Safe because we trust the value returned by kernel.
                    unsafe { buf.set_len(res as usize) };

                    if res == 0 {
                        // EOF: either the target cookie was never found (the entry is gone or the
                        // cookie was stale) or it was the very last entry of the directory. Return
                        // an empty buffer so the guest stops iterating instead of looping forever.
                        break;
                    }

                    if found {
                        // Already past the target entry, this batch is the reply.
                        break;
                    }

                    if Self::skip_to_cookie(&mut buf, offset) {
                        // Consumed everything up to and including the target entry. If it was the
                        // last record of this batch, fetch the next one: returning an empty reply
                        // here would falsely signal end-of-directory.
                        found = true;
                        if !buf.is_empty() {
                            break;
                        }
                    } else {
                        buf.clear();
                    }
                }
            }

            // Both paths leave the fd right after the last entry in `buf`; remember that
            // position so a resume from its cookie can skip the `lseek64`/scan entirely.
            // The guest can only ask to resume from that cookie if it consumed every entry up
            // to it, in which case this position is exactly right; if some entries were not
            // delivered (reply buffer full) the cookie is never requested and the cached
            // value just goes unused.
            self.cache_cookie(handle, &buf);

            // Explicitly drop the lock so that it's not held while we fill in the fuse buffer.
            mem::drop(guard);
        }

        let mut rem = &buf[..];
        let orig_rem_len = rem.len();
        while !rem.is_empty() {
            // We only use debug asserts here because these values are coming from the kernel and we
            // trust them implicitly.
            debug_assert!(
                rem.len() >= size_of::<LinuxDirent64>(),
                "fuse: not enough space left in `rem`"
            );

            let (front, back) = rem.split_at(size_of::<LinuxDirent64>());

            let dirent64 = LinuxDirent64::from_slice(front)
                .expect("fuse: unable to get LinuxDirent64 from slice");

            let namelen = dirent64.d_reclen as usize - size_of::<LinuxDirent64>();
            debug_assert!(
                namelen <= back.len(),
                "fuse: back is smaller than `namelen`"
            );

            let name = &back[..namelen];
            let res = if name.starts_with(CURRENT_DIR_CSTR) || name.starts_with(PARENT_DIR_CSTR) {
                // We don't want to report the "." and ".." entries. However, returning `Ok(0)` will
                // break the loop so return `Ok` with a non-zero value instead.
                Ok(1)
            } else {
                // The Sys_getdents64 in kernel will pad the name with '\0'
                // bytes up to 8-byte alignment, so @name may contain a few null
                // terminators.  This causes an extra lookup from fuse when
                // called by readdirplus, because kernel path walking only takes
                // name without null terminators, the dentry with more than 1
                // null terminators added by readdirplus doesn't satisfy the
                // path walking.
                let name = bytes_to_cstr(name)
                    .map_err(|e| {
                        error!("fuse: do_readdir: {:?}", e);
                        einval()
                    })?
                    .to_bytes();

                add_entry(
                    DirEntry {
                        ino: dirent64.d_ino,
                        offset: dirent64.d_off as u64,
                        type_: u32::from(dirent64.d_ty),
                        name,
                    },
                    data.borrow_fd().as_raw_fd(),
                )
            };

            debug_assert!(
                rem.len() >= dirent64.d_reclen as usize,
                "fuse: rem is smaller than `d_reclen`"
            );

            match res {
                Ok(0) => break,
                Ok(_) => rem = &rem[dirent64.d_reclen as usize..],
                // If there's an error, we can only signal it if we haven't
                // stored any entries yet - otherwise we'd end up with wrong
                // lookup counts for the entries that are already in the
                // buffer. So we return what we've collected until that point.
                Err(e) if rem.len() == orig_rem_len => return Err(e),
                Err(_) => return Ok(()),
            }
        }

        Ok(())
    }

    fn do_open(
        &self,
        inode: Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions, Option<u32>)> {
        let killpriv = if self.killpriv_v2.load(Ordering::Relaxed)
            && (fuse_flags & FOPEN_IN_KILL_SUIDGID != 0)
        {
            self::drop_cap_fsetid()?
        } else {
            None
        };
        let file = self.open_inode(inode, flags as i32)?;
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
                if flags & (libc::O_DIRECTORY as u32) == 0 {
                    opts |= OpenOptions::DIRECT_IO;
                } else {
                    opts |= OpenOptions::CACHE_DIR | OpenOptions::KEEP_CACHE;
                }
            }
            CachePolicy::Always => {
                opts |= OpenOptions::KEEP_CACHE;
                if flags & (libc::O_DIRECTORY as u32) != 0 {
                    opts |= OpenOptions::CACHE_DIR;
                }
            }
            _ => {}
        };

        Ok((Some(handle), opts, None))
    }

    fn do_getattr(
        &self,
        inode: Inode,
        handle: Option<Handle>,
    ) -> io::Result<(libc::stat64, Duration)> {
        let data = self.inode_map.get(inode).map_err(|e| {
            error!("fuse: do_getattr ino {} Not find err {:?}", inode, e);
            e
        })?;

        // kernel sends 0 as handle in case of no_open, and it depends on fuse server to handle
        // this case correctly.
        let st = match (!self.no_open.load(Ordering::Relaxed), handle) {
            (true, Some(h)) => {
                let hd = self.handle_map.get(h, inode)?;
                stat_fd(hd.get_file(), None)
            }
            _ => data.handle.stat(),
        };

        let st = st.map_err(|e| {
            error!("fuse: do_getattr stat failed ino {} err {:?}", inode, e);
            e
        })?;

        Ok((st, self.cfg.attr_timeout))
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

    fn get_dirdata(
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

    fn destroy(&self) {
        self.handle_map.clear();
        self.inode_map.clear();

        if let Err(e) = self.import() {
            error!("fuse: failed to destroy instance, {:?}", e);
        };
    }

    fn statfs(&self, _ctx: &Context, inode: Inode) -> io::Result<libc::statvfs64> {
        let mut out = MaybeUninit::<libc::statvfs64>::zeroed();
        let data = self.inode_map.get(inode)?;
        let file = data.get_file()?;

        // Safe because this will only modify `out` and we check the return value.
        match unsafe { libc::fstatvfs64(file.as_raw_fd(), out.as_mut_ptr()) } {
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
        if self.no_opendir.load(Ordering::Relaxed) {
            info!("fuse: releasedir is not supported.");
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        } else {
            self.do_release(inode, handle)
        }
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
            unsafe { libc::mkdirat(file.as_raw_fd(), name.as_ptr(), mode & !umask) }
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

            add_entry(dir_entry, entry).inspect(|&r| {
                // true when size is not large enough to hold entry.
                if r == 0 {
                    // Release the refcount acquired by self.do_lookup().
                    let mut inodes = self.inode_map.get_map_mut();
                    self.forget_one(&mut inodes, ino, 1);
                }
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
        fuse_flags: u32,
    ) -> io::Result<usize> {
        let data = self.get_data(handle, inode, libc::O_RDWR)?;

        // Manually implement File::try_clone() by borrowing fd of data.file instead of dup().
        // It's safe because the `data` variable's lifetime spans the whole function,
        // so data.file won't be closed.
        let f = unsafe { File::from_raw_fd(data.borrow_fd().as_raw_fd()) };

        self.check_fd_flags(data.clone(), f.as_raw_fd(), flags)?;

        if self.seal_size.load(Ordering::Relaxed) {
            let st = stat_fd(&f, None)?;
            self.seal_size_check(Opcode::Write, st.st_size as u64, offset, size as u64, 0)?;
        }

        let mut f = ManuallyDrop::new(f);

        // Cap restored when _killpriv is dropped
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
    ) -> io::Result<(libc::stat64, Duration)> {
        self.do_getattr(inode, handle)
    }

    fn setattr(
        &self,
        _ctx: &Context,
        inode: Inode,
        attr: libc::stat64,
        handle: Option<Handle>,
        valid: SetattrValid,
    ) -> io::Result<(libc::stat64, Duration)> {
        let inode_data = self.inode_map.get(inode)?;

        enum Data {
            Handle(Arc<HandleData>),
            ProcPath(CString),
        }

        let file = inode_data.get_file()?;
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

        if valid.contains(SetattrValid::SIZE) && self.seal_size.load(Ordering::Relaxed) {
            return Err(io::Error::from_raw_os_error(libc::EPERM));
        }

        if valid.contains(SetattrValid::MODE) {
            // Safe because this doesn't modify any memory and we check the return value.
            let res = unsafe {
                match data {
                    Data::Handle(ref h) => libc::fchmod(h.borrow_fd().as_raw_fd(), attr.st_mode),
                    Data::ProcPath(ref p) => {
                        libc::fchmodat(self.proc_self_fd.as_raw_fd(), p.as_ptr(), attr.st_mode, 0)
                    }
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
            let res = unsafe {
                libc::fchownat(
                    file.as_raw_fd(),
                    empty.as_ptr(),
                    uid,
                    gid,
                    libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
                )
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
        }

        if valid.contains(SetattrValid::SIZE) {
            // Cap restored when _killpriv is dropped
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
                Data::ProcPath(ref p) => unsafe {
                    libc::utimensat(self.proc_self_fd.as_raw_fd(), p.as_ptr(), tvs.as_ptr(), 0)
                },
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
        flags: u32,
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
        let file = data.get_file()?;

        let res = {
            let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;

            // Safe because this doesn't modify any memory and we check the return value.
            unsafe {
                libc::mknodat(
                    file.as_raw_fd(),
                    name.as_ptr(),
                    (mode & !umask) as libc::mode_t,
                    u64::from(rdev),
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
        let res = unsafe {
            libc::linkat(
                file.as_raw_fd(),
                empty.as_ptr(),
                new_file.as_raw_fd(),
                newname.as_ptr(),
                libc::AT_EMPTY_PATH,
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
        datasync: bool,
        handle: Handle,
    ) -> io::Result<()> {
        let data = self.get_data(handle, inode, libc::O_RDONLY)?;
        let fd = data.borrow_fd();
        sync_fd(&fd, datasync)
    }

    fn fsyncdir(
        &self,
        _ctx: &Context,
        inode: Inode,
        datasync: bool,
        handle: Handle,
    ) -> io::Result<()> {
        let data = self.get_dirdata(handle, inode, libc::O_RDONLY)?;
        let fd = data.borrow_fd();
        sync_fd(&fd, datasync)
    }

    fn access(&self, ctx: &Context, inode: Inode, mask: u32) -> io::Result<()> {
        let data = self.inode_map.get(inode)?;
        let st = stat_fd(&data.get_file()?, None)?;
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
        let file = data.get_file()?;
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe {
            libc::setxattr(
                pathname.as_ptr(),
                name.as_ptr(),
                value.as_ptr() as *const libc::c_void,
                value.len(),
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
        let file = data.get_file()?;
        let mut buf = Vec::<u8>::with_capacity(size as usize);
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd(),))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this will only modify the contents of `buf`.
        let res = unsafe {
            libc::getxattr(
                pathname.as_ptr(),
                name.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_void,
                size as libc::size_t,
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
        let file = data.get_file()?;
        let mut buf = Vec::<u8>::with_capacity(size as usize);
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this will only modify the contents of `buf`.
        let res = unsafe {
            libc::listxattr(
                pathname.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_char,
                size as libc::size_t,
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
        let file = data.get_file()?;
        let pathname = CString::new(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // The f{set,get,remove,list}xattr functions don't work on an fd opened with `O_PATH` so we
        // need to use the {set,get,remove,list}xattr variants.
        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe { libc::removexattr(pathname.as_ptr(), name.as_ptr()) };
        if res == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }

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

        // TODO: `offset as off64_t` truncates high-bit NFS directory cookies
        // the same way as the old do_readdir code.  SEEK_SET with offset >
        // i64::MAX will receive EINVAL from nfs_llseek_dir().
        // Safe because this doesn't modify any memory and we check the return value.
        let res = unsafe {
            libc::lseek(
                file.as_raw_fd(),
                offset as libc::off64_t,
                whence as libc::c_int,
            )
        };
        if res < 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(res as u64)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;

    use super::*;
    use crate::abi::fuse_abi::ROOT_ID;
    use std::path::Path;
    use vmm_sys_util::{tempdir::TempDir, tempfile::TempFile};

    fn prepare_fs_tmpdir() -> (PassthroughFs, TempDir) {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            writeback: true,
            do_import: true,
            no_open: false,
            no_readdir: false,
            inode_file_handles: true,
            xattr: true,
            killpriv_v2: true, //enable killpriv_v2
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();

        // enable all fuse options
        let opt = FsOptions::all();
        fs.init(opt).unwrap();

        (fs, source)
    }

    fn prepare_context() -> Context {
        Context {
            uid: unsafe { libc::getuid() },
            gid: unsafe { libc::getgid() },
            pid: unsafe { libc::getpid() },
            ..Default::default()
        }
    }

    fn create_file_with_sugid(ctx: &Context, fs: &PassthroughFs<()>) -> (Entry, Handle) {
        let fname = CString::new("testfile").unwrap();
        let args = CreateIn {
            flags: libc::O_WRONLY as u32,
            mode: 0o6777,
            umask: 0,
            fuse_flags: 0,
        };
        let (test_entry, handle, _, _) = fs.create(&ctx, ROOT_ID, &fname, args).unwrap();

        (test_entry, handle.unwrap())
    }

    #[test]
    fn test_dir_operations() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let dir = CString::new("testdir").unwrap();
        fs.mkdir(&ctx, ROOT_ID, &dir, 0o755, 0).unwrap();

        let (handle, _) = fs.opendir(&ctx, ROOT_ID, libc::O_RDONLY as u32).unwrap();

        assert!(fs
            .readdir(&ctx, ROOT_ID, handle.unwrap(), 10, 0, &mut |_| Ok(1))
            .is_err());

        assert!(fs
            .readdirplus(&ctx, ROOT_ID, handle.unwrap(), 10, 0, &mut |_, _| Ok(1))
            .is_err());

        assert!(fs.fsyncdir(&ctx, ROOT_ID, true, handle.unwrap()).is_ok());

        assert!(fs.releasedir(&ctx, ROOT_ID, 0, handle.unwrap()).is_ok());
        assert!(fs.rmdir(&ctx, ROOT_ID, &dir).is_ok());
    }

    #[test]
    fn test_link_rename() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let fname = CString::new("testfile").unwrap();
        let args = CreateIn::default();
        let (test_entry, _, _, _) = fs.create(&ctx, ROOT_ID, &fname, args).unwrap();

        let link_name = CString::new("testlink").unwrap();
        fs.link(&ctx, test_entry.inode, ROOT_ID, &link_name)
            .unwrap();

        let new_name = CString::new("newlink").unwrap();
        fs.rename(&ctx, ROOT_ID, &link_name, ROOT_ID, &new_name, 0)
            .unwrap();

        let link_entry = fs.lookup(&ctx, ROOT_ID, &new_name).unwrap();

        assert_eq!(link_entry.inode, test_entry.inode);
    }

    #[test]
    fn test_unlink_delete_file() {
        let (fs, source) = prepare_fs_tmpdir();
        let child_path = TempFile::new_in(source.as_path()).expect("Cannot create temporary file.");

        let ctx = prepare_context();

        let child_str = child_path
            .as_path()
            .file_name()
            .unwrap()
            .to_str()
            .expect("path to string");
        let child = CString::new(child_str).unwrap();

        fs.unlink(&ctx, ROOT_ID, &child).unwrap();

        assert!(!Path::new(child_str).exists())
    }

    #[test]
    // test virtiofs CVE-2020-35517, should not open device file
    fn test_mknod_and_open_device() {
        let (fs, _source) = prepare_fs_tmpdir();

        let ctx = prepare_context();

        let device_name = CString::new("test_device").unwrap();
        let mode = libc::S_IFBLK;
        let mask = 0o777;
        let device_no = libc::makedev(0, 103) as u32;

        let device_entry = fs
            .mknod(&ctx, ROOT_ID, &device_name, mode, device_no, mask)
            .unwrap();
        let (d_st, _) = fs.getattr(&ctx, device_entry.inode, None).unwrap();

        assert_eq!(d_st.st_mode & libc::S_IFMT, libc::S_IFBLK);
        assert_eq!(d_st.st_rdev as u32, device_no);

        // open device should fail because of is_safe_inode check
        let err = fs
            .open(&ctx, device_entry.inode, libc::O_RDWR as u32, 0)
            .is_err();
        assert_eq!(err, true);
    }

    #[test]
    fn test_create_access() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let fname = CString::new("testfile").unwrap();
        let args = CreateIn {
            flags: libc::O_WRONLY as u32,
            mode: 0644,
            umask: 0,
            fuse_flags: 0,
        };
        let (test_entry, _, _, _) = fs.create(&ctx, ROOT_ID, &fname, args).unwrap();

        let mask = (libc::R_OK | libc::W_OK) as u32;
        assert_eq!(fs.access(&ctx, test_entry.inode, mask).is_ok(), true);
        let mask = (libc::R_OK | libc::W_OK | libc::X_OK) as u32;
        assert_eq!(fs.access(&ctx, test_entry.inode, mask).is_ok(), false);
        assert!(fs
            .release(&ctx, test_entry.inode, 0, 0, false, false, Some(0))
            .is_err());
    }

    #[test]
    fn test_symlink_escape_root() {
        let (fs, _source) = prepare_fs_tmpdir();
        let child_path =
            TempFile::new_in(_source.as_path()).expect("Cannot create temporary file.");
        let ctx = prepare_context();

        let eval_sym_dest = CString::new("/root").unwrap();
        let eval_sym_name = CString::new("eval_sym").unwrap();
        let normal_sym_dest = CString::new(child_path.as_path().to_str().unwrap()).unwrap();
        let normal_sym_name = CString::new("normal_sym").unwrap();

        let normal_sym_entry = fs
            .symlink(&ctx, &normal_sym_dest, ROOT_ID, &normal_sym_name)
            .unwrap();

        let eval_sym_entry = fs
            .symlink(&ctx, &eval_sym_dest, ROOT_ID, &eval_sym_name)
            .unwrap();

        let normal_buf = fs.readlink(&ctx, normal_sym_entry.inode).unwrap();
        let eval_buf = fs.readlink(&ctx, eval_sym_entry.inode).unwrap();
        let normal_dest_name = CString::new(String::from_utf8(normal_buf).unwrap()).unwrap();
        let eval_dest_name = CString::new(String::from_utf8(eval_buf).unwrap()).unwrap();

        assert_eq!(normal_dest_name, normal_sym_dest);
        assert_eq!(eval_dest_name, eval_sym_dest);
    }

    #[test]
    fn test_setattr_and_drop_priv() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let (test_entry, _) = create_file_with_sugid(&ctx, &fs);

        let (mut old_att, _) = fs.getattr(&ctx, test_entry.inode, None).unwrap();

        old_att.st_size = 4096;
        let mut valid = SetattrValid::SIZE | SetattrValid::KILL_SUIDGID;
        let (attr_not_drop, _) = fs
            .setattr(&ctx, test_entry.inode, old_att, None, valid)
            .unwrap();
        // during file size change,
        // suid/sgid should be dropped because of killpriv_v2
        assert_eq!(attr_not_drop.st_mode, 0o100777);

        old_att.st_size = 0;
        old_att.st_uid = 1;
        old_att.st_gid = 1;
        old_att.st_atime = 0;
        old_att.st_mtime = 0;
        valid = SetattrValid::SIZE
            | SetattrValid::ATIME
            | SetattrValid::MTIME
            | SetattrValid::UID
            | SetattrValid::GID;

        let (attr, _) = fs
            .setattr(&ctx, test_entry.inode, old_att, None, valid)
            .unwrap();
        // suid/sgid is dropped because chmod is called
        assert_eq!(attr.st_mode, 0o100777);
        assert_eq!(attr.st_size, 0);
    }

    #[test]
    // fallocate missing killpriv logic, should be fixed
    fn test_fallocate_drop_priv() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let (test_entry, handle) = create_file_with_sugid(&ctx, &fs);

        let offset = fs
            .lseek(
                &ctx,
                test_entry.inode,
                handle,
                4096,
                libc::SEEK_SET.try_into().unwrap(),
            )
            .unwrap();
        fs.fallocate(&ctx, test_entry.inode, handle, 0, offset, 4096)
            .unwrap();

        let (att, _) = fs.getattr(&ctx, test_entry.inode, None).unwrap();

        assert_eq!(att.st_size, 8192);
        // suid/sgid not dropped
        assert_eq!(att.st_mode, 0o106777);
    }

    #[test]
    fn test_fsync_flush() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let (test_entry, handle) = create_file_with_sugid(&ctx, &fs);

        assert!(fs.fsync(&ctx, test_entry.inode, false, handle).is_ok());
        assert!(fs.flush(&ctx, test_entry.inode, handle, 0).is_ok());
    }

    #[test]
    fn test_statfs() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();

        let statfs = fs.statfs(&ctx, ROOT_ID).unwrap();
        assert_eq!(statfs.f_namemax, 255);
    }

    #[test]
    fn test_fsync_dir() {
        let (fs, _source) = prepare_fs_tmpdir();
        let ctx = prepare_context();
        fs.no_opendir.store(true, Ordering::Relaxed);

        assert!(fs.fsyncdir(&ctx, ROOT_ID, false, 0).is_ok());
    }

    // -- sidecar cookie cache tests --

    #[test]
    fn cookie_set_and_remove() {
        let map = HandleMap::new();
        assert_eq!(map.remove_cookie(1), None);

        map.set_cookie(1, 42);
        assert_eq!(map.remove_cookie(1), Some(42));

        // Already removed — second remove returns None.
        assert_eq!(map.remove_cookie(1), None);
    }

    #[test]
    fn cookie_overwrite() {
        let map = HandleMap::new();
        map.set_cookie(1, 10);
        map.set_cookie(1, u64::MAX);
        assert_eq!(map.remove_cookie(1), Some(u64::MAX));
    }

    #[test]
    fn cookie_independent_handles() {
        let map = HandleMap::new();
        map.set_cookie(1, 100);
        map.set_cookie(2, 200);
        assert_eq!(map.remove_cookie(1), Some(100));
        assert_eq!(map.remove_cookie(2), Some(200));
    }

    #[test]
    fn cookie_clear_drops_all() {
        let map = HandleMap::new();
        map.set_cookie(1, 10);
        map.set_cookie(2, 20);
        map.clear();
        assert_eq!(map.remove_cookie(1), None);
        assert_eq!(map.remove_cookie(2), None);
    }

    #[test]
    fn cookie_remove_nonexistent_is_noop() {
        let map = HandleMap::new();
        assert_eq!(map.remove_cookie(999), None);
    }

    #[test]
    fn test_readdir_seek_no_opendir() {
        // Regression test for xfstests generic/676: in `no_opendir` mode a
        // fresh fd at position 0 is opened for every READDIR, so resuming
        // from a cookie must never rely on the fd being left in place by a
        // previous call.
        let (fs, source) = prepare_fs_tmpdir();
        let ctx = prepare_context();
        fs.no_opendir.store(true, Ordering::Relaxed);

        let count = 16_usize;
        for i in 0..count {
            std::fs::File::create(source.as_path().join(format!("file{:02}", i)))
                .expect("create file");
        }

        // Read the whole directory, recording (cookie, name) in the order
        // they are returned.
        let mut entries: Vec<(u64, Vec<u8>)> = Vec::new();
        let mut offset = 0_u64;
        for _ in 0..=count + 2 {
            let mut batch = Vec::new();
            fs.readdir(&ctx, ROOT_ID, 0, 8192, offset, &mut |e| {
                batch.push((e.offset, e.name.to_vec()));
                Ok(1)
            })
            .unwrap();
            if batch.is_empty() {
                break;
            }
            offset = batch.last().unwrap().0;
            entries.extend(batch);
        }
        assert_eq!(entries.len(), count);

        // Seek back to every cookie and check that the next entry is the
        // one immediately after it instead of a replay from the start.
        for (idx, (cookie, _)) in entries.clone().into_iter().enumerate() {
            let mut first = None;
            fs.readdir(&ctx, ROOT_ID, 0, 8192, cookie, &mut |e| {
                if first.is_none() {
                    first = Some(e.name.to_vec());
                }
                Ok(1)
            })
            .unwrap();
            if idx + 1 < entries.len() {
                assert_eq!(first, Some(entries[idx + 1].1.clone()));
            } else {
                // Resuming from the last cookie must hit EOF.
                assert_eq!(first, None);
            }
        }
    }
}

#[cfg(test)]
mod readdir_cookie_tests {
    use super::*;
    use std::ffi::CStr;

    /// Build a buffer containing the serialized dirent records described by
    /// `entries`.  Each entry is (d_off, name).  The inode number and type
    /// are dummies.
    fn build_dirent_buf(entries: &[(u64, &[u8])]) -> Vec<u8> {
        let header = size_of::<LinuxDirent64>();
        // Allocate enough for the entries plus padding to 8-byte alignment.
        let mut buf = Vec::new();
        for (off, name) in entries {
            let name_len = name.len() + 1; // include trailing NUL
            let reclen = (header + name_len + 7) & !7;
            let dirent = LinuxDirent64 {
                d_ino: 1,
                d_off: *off as libc::off64_t,
                d_reclen: reclen as libc::c_ushort,
                d_ty: libc::DT_REG as libc::c_uchar,
            };
            let mut entry = dirent.as_slice().to_vec();
            entry.resize(header, 0);
            entry.extend_from_slice(name);
            entry.resize(reclen, 0);
            buf.extend_from_slice(&entry);
        }
        buf
    }

    fn names(buf: &Vec<u8>) -> Vec<String> {
        let mut out = Vec::new();
        let mut pos = 0;
        while pos + size_of::<LinuxDirent64>() <= buf.len() {
            let front = &buf[pos..pos + size_of::<LinuxDirent64>()];
            let dirent = LinuxDirent64::from_slice(front).unwrap();
            let namelen = dirent.d_reclen as usize - size_of::<LinuxDirent64>();
            let name_start = pos + size_of::<LinuxDirent64>();
            let name_slice = &buf[name_start..name_start + namelen];
            let cstr = CStr::from_bytes_until_nul(name_slice).unwrap();
            out.push(String::from_utf8_lossy(cstr.to_bytes()).to_string());
            pos += dirent.d_reclen as usize;
        }
        out
    }

    #[test]
    fn skip_to_cookie_finds_middle_entry() {
        let mut buf = build_dirent_buf(&[(1, b"a"), (2, b"b"), (3, b"c")]);
        assert!(PassthroughFs::<()>::skip_to_cookie(&mut buf, 2));
        assert_eq!(names(&buf), vec!["c".to_string()]);
    }

    #[test]
    fn skip_to_cookie_finds_first_entry() {
        let mut buf = build_dirent_buf(&[(1, b"a"), (2, b"b")]);
        assert!(PassthroughFs::<()>::skip_to_cookie(&mut buf, 1));
        assert_eq!(names(&buf), vec!["b".to_string()]);
    }

    #[test]
    fn skip_to_cookie_finds_last_entry() {
        let mut buf = build_dirent_buf(&[(1, b"a"), (2, b"b")]);
        assert!(PassthroughFs::<()>::skip_to_cookie(&mut buf, 2));
        assert!(buf.is_empty());
    }

    #[test]
    fn skip_to_cookie_not_found() {
        let mut buf = build_dirent_buf(&[(1, b"a"), (2, b"b")]);
        assert!(!PassthroughFs::<()>::skip_to_cookie(&mut buf, 99));
        // Buffer should be left untouched when the cookie is not present.
        assert_eq!(names(&buf), vec!["a".to_string(), "b".to_string()]);
    }

    #[test]
    fn skip_to_cookie_large_cookie() {
        // Simulate the NFS case: a cookie whose high bit is set.
        let large = u64::MAX - 42;
        let mut buf = build_dirent_buf(&[(1, b"a"), (large, b"b"), (3, b"c")]);
        assert!(PassthroughFs::<()>::skip_to_cookie(&mut buf, large));
        assert_eq!(names(&buf), vec!["c".to_string()]);
    }

    #[test]
    fn last_cookie_in_buf_returns_last_d_off() {
        let buf = build_dirent_buf(&[(1, b"a"), (7, b"b"), (u64::MAX - 1, b"c")]);
        assert_eq!(
            PassthroughFs::<()>::last_cookie_in_buf(&buf),
            Some(u64::MAX - 1)
        );

        let buf = build_dirent_buf(&[(5, b"only")]);
        assert_eq!(PassthroughFs::<()>::last_cookie_in_buf(&buf), Some(5));

        assert_eq!(PassthroughFs::<()>::last_cookie_in_buf(&[]), None);
    }

    #[test]
    fn last_cookie_in_buf_malformed_reclen() {
        // A record with a zero reclen must not loop forever; the cookie of
        // the last well-formed entry before it is returned.
        let mut buf = build_dirent_buf(&[(1, b"a"), (7, b"b")]);
        buf[40..42].copy_from_slice(&0u16.to_ne_bytes());
        assert_eq!(PassthroughFs::<()>::last_cookie_in_buf(&buf), Some(1));

        // Same for a reclen extending beyond the buffer: no out-of-bounds
        // access, parsing stops at the malformed record.
        let mut buf = build_dirent_buf(&[(1, b"a"), (7, b"b")]);
        buf[40..42].copy_from_slice(&500u16.to_ne_bytes());
        assert_eq!(PassthroughFs::<()>::last_cookie_in_buf(&buf), Some(1));

        // A zero reclen right in the first record yields no cookie at all.
        let mut buf = build_dirent_buf(&[(1, b"a")]);
        buf[16..18].copy_from_slice(&0u16.to_ne_bytes());
        assert_eq!(PassthroughFs::<()>::last_cookie_in_buf(&buf), None);
    }

    #[test]
    fn skip_to_cookie_malformed_reclen() {
        // A zero reclen must not loop forever; the cookie is simply not found
        // and the buffer is left untouched.
        let mut buf = build_dirent_buf(&[(1, b"a"), (2, b"b")]);
        buf[16..18].copy_from_slice(&0u16.to_ne_bytes());
        let corrupted = buf.clone();
        assert!(!PassthroughFs::<()>::skip_to_cookie(&mut buf, 2));
        assert_eq!(buf, corrupted);
    }
}
