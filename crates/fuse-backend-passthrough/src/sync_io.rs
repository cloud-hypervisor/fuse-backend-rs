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
use fuse_backend_core::abi::fuse_abi::{CreateIn, Opcode, FOPEN_IN_KILL_SUIDGID, WRITE_KILL_PRIV};
#[cfg(feature = "virtiofs")]
use fuse_backend_core::abi::virtio_fs;
#[cfg(feature = "virtiofs")]
use fuse_backend_core::api::filesystem::FsCacheReqHandler;
use fuse_backend_core::api::filesystem::{
    Context, DirEntry, Entry, FileSystem, FsOptions, GetxattrReply, ListxattrReply, OpenOptions,
    SetattrValid, ZeroCopyReader, ZeroCopyWriter,
};
use fuse_backend_core::buffer::pagesize;
use fuse_backend_core::bytes_to_cstr;

/// A byte buffer allocated by `posix_memalign()` and freed with `libc::free()`
/// on drop.
///
/// Pairing the C allocation with an explicit free(), instead of wrapping the
/// pointer in a `Vec` whose deallocator always receives a layout with an
/// alignment of 1, keeps the `GlobalAlloc` contract satisfied no matter which
/// global allocator the embedding crate is built with.
struct AlignedBuf {
    ptr: *mut u8,
    len: usize,
}

impl AlignedBuf {
    fn new(alignment: usize, len: usize) -> io::Result<Self> {
        let mut ptr = std::ptr::null_mut();
        // Safe because `ptr` is a valid out-pointer and the return value is
        // checked, so `ptr` is only read when posix_memalign() succeeded.
        let ret = unsafe { libc::posix_memalign(&mut ptr, alignment, len) };
        if ret != 0 {
            return Err(io::Error::from_raw_os_error(ret));
        }
        Ok(AlignedBuf {
            ptr: ptr as *mut u8,
            len,
        })
    }

    fn as_mut_slice(&mut self) -> &mut [u8] {
        // Safe because posix_memalign() returned a valid allocation of `len`
        // bytes; `u8` has no invalid bit patterns, so it's fine to treat the
        // memory as initialized before it's actually written.
        unsafe { std::slice::from_raw_parts_mut(self.ptr, self.len) }
    }
}

impl Drop for AlignedBuf {
    fn drop(&mut self) {
        // Safe because `ptr` came from posix_memalign() and is passed to
        // free() exactly once, here.
        unsafe { libc::free(self.ptr as *mut libc::c_void) };
    }
}

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
    pub(super) fn ensure_file_flags<'a>(
        &self,
        data: &'a Arc<HandleData>,
        fd: &impl AsRawFd,
        mut flags: u32,
    ) -> io::Result<FileFlagGuard<'a, u32>> {
        let guard = data.open_flags.read().unwrap();
        if *guard & libc::O_DIRECT as u32 == flags & libc::O_DIRECT as u32 {
            return Ok(FileFlagGuard::Reader(guard));
        }
        drop(guard);

        let mut guard = data.open_flags.write().unwrap();
        // Update the O_DIRECT flag if needed
        if *guard & libc::O_DIRECT as u32 != flags & libc::O_DIRECT as u32 {
            if flags & libc::O_DIRECT as u32 != 0 {
                flags = *guard | libc::O_DIRECT as u32;
            } else {
                flags = *guard & !libc::O_DIRECT as u32;
            }
            let ret = unsafe { libc::fcntl(fd.as_raw_fd(), libc::F_SETFL, flags) };
            if ret != 0 {
                return Err(io::Error::last_os_error());
            }
            *guard = flags;
        }

        Ok(FileFlagGuard::Writer(guard))
    }

    /// Serve a write request targeting a file opened with `O_DIRECT`.
    ///
    /// The payload of a fuse WRITE request sits in the request buffer right
    /// after the request headers, an offset the daemon can't control, so it
    /// generally doesn't satisfy the alignment constraints of direct IO
    /// (buffer address, length and file offset must all be multiples of the
    /// device logical block size) and `pwritev()` fails with `EINVAL`.
    /// Stage the payload through a page-aligned buffer instead. That lifts
    /// only the buffer-address constraint: a request whose size or offset is
    /// unaligned still fails with `EINVAL`, the same error the underlying
    /// filesystem reports for it.
    fn write_direct(
        &self,
        f: &File,
        r: &mut dyn ZeroCopyReader,
        size: usize,
        offset: u64,
    ) -> io::Result<usize> {
        use std::os::unix::fs::FileExt;

        if size == 0 {
            return Ok(0);
        }

        // Align the bounce buffer to the runtime page size, which is always a
        // multiple of the device logical block size that O_DIRECT requires,
        // instead of assuming a fixed 4096 (wrong on 16K/64K-page systems).
        let mut buffer = AlignedBuf::new(pagesize(), size)?;
        let buf = buffer.as_mut_slice();

        let mut copied = 0usize;
        while copied < size {
            match r.read(&mut buf[copied..]) {
                Ok(0) => break,
                Ok(n) => copied += n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        let mut written = 0usize;
        while written < copied {
            match f.write_at(&buf[written..copied], offset + written as u64) {
                Ok(0) => break,
                Ok(n) => written += n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(written)
    }

    /// Serve a read request targeting a file opened with `O_DIRECT`.
    ///
    /// The data of a fuse READ reply is appended to the reply right after
    /// the response header, an offset the daemon can't control, so it
    /// generally doesn't satisfy the alignment constraints of direct IO and
    /// `preadv()` fails with `EINVAL`. Stage the data through a page-aligned
    /// buffer instead. That lifts only the buffer-address constraint: a
    /// request whose size or offset is unaligned still fails with `EINVAL`,
    /// the same error the underlying filesystem reports for it.
    fn read_direct(
        &self,
        f: &File,
        w: &mut dyn ZeroCopyWriter,
        size: usize,
        offset: u64,
    ) -> io::Result<usize> {
        use std::os::unix::fs::FileExt;

        if size == 0 {
            return Ok(0);
        }

        // Align the bounce buffer to the runtime page size, which is always a
        // multiple of the device logical block size that O_DIRECT requires,
        // instead of assuming a fixed 4096 (wrong on 16K/64K-page systems).
        let mut buffer = AlignedBuf::new(pagesize(), size)?;
        let buf = buffer.as_mut_slice();

        let mut read_cnt = 0usize;
        while read_cnt < size {
            match f.read_at(&mut buf[read_cnt..], offset + read_cnt as u64) {
                Ok(0) => break,
                Ok(n) => read_cnt += n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        let mut written = 0usize;
        while written < read_cnt {
            match w.write(&buf[written..read_cnt]) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write whole buffer",
                    ))
                }
                Ok(n) => written += n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(written)
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
            let dirent64 = match LinuxDirent64::from_slice(front) {
                Some(d) => d,
                // Defend against a malformed getdents64 buffer.
                None => break,
            };
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
            let dirent64 = match LinuxDirent64::from_slice(&buf[..size_of::<LinuxDirent64>()]) {
                Some(d) => d,
                // Defend against a malformed getdents64 buffer.
                None => break,
            };
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

            let dirent64 = LinuxDirent64::from_slice(front).ok_or_else(einval)?;

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
        // If the client requested O_DIRECT and we honor it, `open_inode()`
        // opened the backing file with O_DIRECT, so the kernel must route IO
        // on this handle through the direct IO path: serving an O_DIRECT fd
        // through the page-cache path fails with EINVAL because the page-cache
        // buffers don't satisfy direct IO alignment requirements.
        if self.cfg.allow_direct_io
            && flags & (libc::O_DIRECT as u32) != 0
            && flags & (libc::O_DIRECTORY as u32) == 0
        {
            opts |= OpenOptions::DIRECT_IO;
        }
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

    pub(super) fn get_data(
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
        // No config option is needed: the handlers unconditionally honor
        // Context.supp_gid, so just mirror what the kernel offers.  This
        // also covers standalone mounts not sitting behind a Vfs, which
        // negotiates the flag on its own.
        if capable.contains(FsOptions::CREATE_SUPP_GROUP) {
            opts |= FsOptions::CREATE_SUPP_GROUP;
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
            let _groups = ScopedSuppGroups::new(ctx.supp_gid)?;
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
            let _groups = ScopedSuppGroups::new(ctx.supp_gid)?;
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

    #[cfg(feature = "virtiofs")]
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

    #[cfg(feature = "virtiofs")]
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
        let fd = data.borrow_fd();

        // Hold the guard over the whole IO operation, so that no other request
        // can change the O_DIRECT flag of the fd while we are using it.
        let _flags_guard = self.ensure_file_flags(&data, &fd, flags)?;

        // Manually implement File::try_clone() by borrowing fd of data.file instead of dup().
        // It's safe because the `data` variable's lifetime spans the whole function,
        // so data.file won't be closed.
        let mut f = unsafe { ManuallyDrop::new(File::from_raw_fd(fd.as_raw_fd())) };

        // The backing file was opened with O_DIRECT (see `open_inode()`), whose
        // alignment constraints the transport buffers don't satisfy, so stage
        // the data through an aligned bounce buffer.
        if self.cfg.allow_direct_io && flags & (libc::O_DIRECT as u32) != 0 {
            return self.read_direct(&f, w, size as usize, offset);
        }

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
        let fd = data.borrow_fd();

        // Hold the guard over the whole IO operation, so that no other request
        // can change the O_DIRECT flag of the fd while we are using it.
        let _flags_guard = self.ensure_file_flags(&data, &fd, flags)?;
        if self.seal_size.load(Ordering::Relaxed) {
            let st = stat_fd(&fd, None)?;
            self.seal_size_check(Opcode::Write, st.st_size as u64, offset, size as u64, 0)?;
        }

        // Cap restored when _killpriv is dropped
        let _killpriv =
            if self.killpriv_v2.load(Ordering::Relaxed) && (fuse_flags & WRITE_KILL_PRIV != 0) {
                self::drop_cap_fsetid()?
            } else {
                None
            };

        // Manually implement File::try_clone() by borrowing fd of data.file instead of dup().
        // It's safe because the `data` variable's lifetime spans the whole function,
        // so data.file won't be closed.
        let mut f = unsafe { ManuallyDrop::new(File::from_raw_fd(fd.as_raw_fd())) };

        // The backing file was opened with O_DIRECT (see `open_inode()`), whose
        // alignment constraints the transport buffers don't satisfy, so stage
        // the payload through an aligned bounce buffer.
        if self.cfg.allow_direct_io && flags & (libc::O_DIRECT as u32) != 0 {
            return self.write_direct(&f, r, size as usize, offset);
        }

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
            let _groups = ScopedSuppGroups::new(ctx.supp_gid)?;
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
            let err = io::Error::last_os_error();
            // linkat() with AT_EMPTY_PATH requires CAP_DAC_READ_SEARCH,
            // which unprivileged daemons don't have, and the kernel reports
            // the missing capability as ENOENT. Retry through /proc/self/fd,
            // following the magic symlink to the file the fd refers to.
            if err.raw_os_error() == Some(libc::ENOENT) {
                // The retry cannot link a symlink itself: following the
                // magic symlink resolves to the link target, so the new
                // name would point at the target instead of the symlink.
                // Report the missing capability instead of linking the
                // wrong file. The file type cannot change for a live
                // inode, so the cached mode is reliable here.
                if (data.mode & libc::S_IFMT) == libc::S_IFLNK {
                    return Err(io::Error::from_raw_os_error(libc::EPERM));
                }
                let oldpath = CString::new(format!("{}", file.as_raw_fd()))
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
                // Safe because this doesn't modify any memory and we check the return value.
                let res = unsafe {
                    libc::linkat(
                        self.proc_self_fd.as_raw_fd(),
                        oldpath.as_ptr(),
                        new_file.as_raw_fd(),
                        newname.as_ptr(),
                        libc::AT_SYMLINK_FOLLOW,
                    )
                };
                if res == 0 {
                    return self.do_lookup(newparent, newname);
                }
                return Err(io::Error::last_os_error());
            }
            Err(err)
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
            let _groups = ScopedSuppGroups::new(ctx.supp_gid)?;
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

    #[cfg(target_os = "linux")]
    #[allow(clippy::too_many_arguments)]
    fn copy_file_range(
        &self,
        _ctx: &Context,
        inode_in: Inode,
        fh_in: Handle,
        offset_in: u64,
        inode_out: Inode,
        fh_out: Handle,
        offset_out: u64,
        len: u64,
        flags: u64,
    ) -> io::Result<u32> {
        // Keep the Arc<HandleData> in scope, otherwise the fds may get invalid.
        let data_in = self.handle_map.get(fh_in, inode_in)?;
        let data_out = self.handle_map.get(fh_out, inode_out)?;

        // The FUSE protocol carries explicit offsets and the reply only reports
        // the copied length, so the backing files' own positions are neither
        // read nor advanced: no need to serialize against lseek() by taking
        // get_file_mut().
        let mut off_in: libc::loff_t = offset_in as libc::loff_t;
        let mut off_out: libc::loff_t = offset_out as libc::loff_t;

        // The WriteOut reply reports the copied length as a u32, so never ask
        // for more than can be answered; the kernel re-requests the remainder.
        let len = len.min(u32::MAX as u64) as usize;

        // Safe because the only memory this modifies is the two offset locals
        // which we own, and we check the return value.
        let res = unsafe {
            libc::syscall(
                libc::SYS_copy_file_range,
                data_in.get_file().as_raw_fd(),
                &mut off_in as *mut libc::loff_t,
                data_out.get_file().as_raw_fd(),
                &mut off_out as *mut libc::loff_t,
                len,
                flags as libc::c_uint,
            )
        };
        if res < 0 {
            Err(io::Error::last_os_error())
        } else {
            Ok(res as u32)
        }
    }
}

#[cfg(test)]
mod tests {
    use std::convert::TryInto;

    use super::*;
    use fuse_backend_core::abi::fuse_abi::ROOT_ID;
    use fuse_backend_core::file_buf::FileVolatileSlice;
    use fuse_backend_core::file_traits::FileReadWriteVolatile;
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

    /// An in-memory sink implementing `ZeroCopyWriter`, to receive the data
    /// staged back out by `read_direct()`.
    struct MemWriter(Vec<u8>);

    impl MemWriter {
        fn new() -> Self {
            MemWriter(Vec::new())
        }
    }

    impl io::Write for MemWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.0.extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl ZeroCopyWriter for MemWriter {
        fn write_from(
            &mut self,
            f: &mut dyn FileReadWriteVolatile,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            if self.0.len() < count {
                self.0.resize(count, 0);
            }
            // Safe because the slice points into `self.0` and doesn't out-live it.
            let slice = unsafe { FileVolatileSlice::from_raw_ptr(self.0.as_mut_ptr(), count) };
            f.read_at_volatile(slice, off)
        }

        fn available_bytes(&self) -> usize {
            usize::MAX
        }
    }

    /// An in-memory source implementing `ZeroCopyReader`, to provide the data
    /// staged through the bounce buffer by `write_direct()`.
    struct MemReader(Vec<u8>);

    impl io::Read for MemReader {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let n = std::cmp::min(buf.len(), self.0.len());
            buf[..n].copy_from_slice(&self.0[..n]);
            self.0.drain(..n);
            Ok(n)
        }
    }

    impl ZeroCopyReader for MemReader {
        fn read_to(
            &mut self,
            f: &mut dyn FileReadWriteVolatile,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            let start = off as usize;
            if start >= self.0.len() {
                return Ok(0);
            }
            let n = std::cmp::min(count, self.0.len() - start);
            // Safe because the buffer is only read from and the slice doesn't
            // out-live `self.0`.
            let slice = unsafe {
                FileVolatileSlice::from_raw_ptr(self.0.as_ptr().add(start) as *mut u8, n)
            };
            f.write_at_volatile(slice, off)
        }
    }

    // A direct IO request has to stage its payload through a page-aligned bounce
    // buffer, because the fuse transport buffer holds the payload at an offset
    // the daemon can't align (right after the request/response headers). Verify
    // both halves of that contract against a real O_DIRECT fd: a raw unaligned
    // access fails with EINVAL, while `write_direct()`/`read_direct()` succeed
    // and round-trip the payload byte for byte.
    //
    // O_DIRECT needs a backing filesystem that supports it; tmpfs (a common
    // /tmp) rejects it at open() with EINVAL, so skip gracefully there rather
    // than fail, to keep the test from being environment-dependent.
    #[test]
    fn test_direct_io_bounce_buffer() {
        use std::os::unix::fs::{FileExt, OpenOptionsExt};

        const BLOCK: usize = 4096;

        let dir = TempDir::new().expect("Cannot create temporary directory.");
        let path = dir.as_path().join("direct_io_file");

        let file = match std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .custom_flags(libc::O_DIRECT)
            .open(&path)
        {
            Ok(f) => f,
            Err(e) if e.raw_os_error() == Some(libc::EINVAL) => {
                eprintln!(
                    "skipping test_direct_io_bounce_buffer: {:?} does not support O_DIRECT",
                    dir.as_path()
                );
                return;
            }
            Err(e) => panic!("unexpected error opening {:?} with O_DIRECT: {}", path, e),
        };

        // A minimal, unprivileged fs instance. The helpers don't consult it, but
        // they hang off `PassthroughFs`, so an instance is needed to call them.
        let fs_cfg = Config {
            root_dir: dir.as_path().to_str().unwrap().to_string(),
            allow_direct_io: true,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();

        // Reproduce the bug: pwrite from a buffer whose address is misaligned by
        // one byte, while the length and file offset stay block-aligned, so only
        // the address violates the O_DIRECT constraint -- exactly like a payload
        // that follows the fuse headers in the transport buffer.
        let backing = vec![0u8; BLOCK + 1];
        match file.write_at(&backing[1..=BLOCK], 0) {
            Err(e) if e.raw_os_error() == Some(libc::EINVAL) => {}
            Ok(_) => {
                eprintln!(
                    "skipping test_direct_io_bounce_buffer: {:?} does not enforce O_DIRECT alignment",
                    dir.as_path()
                );
                return;
            }
            Err(e) => panic!("expected EINVAL from unaligned O_DIRECT pwrite, got: {}", e),
        }

        // The fix: write_direct() stages the payload through an aligned buffer.
        let payload: Vec<u8> = (0..BLOCK).map(|i| (i % 251) as u8).collect();
        let mut reader = MemReader(payload.clone());
        let written = fs.write_direct(&file, &mut reader, BLOCK, 0).unwrap();
        assert_eq!(written, BLOCK);

        // ...and read_direct() stages it back out, byte for byte.
        let mut writer = MemWriter::new();
        let read = fs.read_direct(&file, &mut writer, BLOCK, 0).unwrap();
        assert_eq!(read, BLOCK);
        assert_eq!(writer.0, payload);
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

    // Hard-linking a symlink exercises the privilege split of link():
    // with CAP_DAC_READ_SEARCH the first linkat() succeeds and links the
    // symlink itself, while without it the kernel answers ENOENT and the
    // /proc/self/fd fallback refuses to follow the magic symlink -- it
    // would link the target instead of the symlink -- so the documented
    // EPERM surfaces. Both outcomes are correct; anything else is a bug.
    // The regular-file variant is covered by test_link_rename()
    // (privileged only) and test_link_regular().
    //
    // Unlike prepare_fs_tmpdir(), this builds the fs without inode file
    // handles: open_by_handle_at() needs CAP_DAC_READ_SEARCH as well, and
    // its EPERM would shadow the very code under test here.
    #[test]
    fn test_link_symlink() {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();
        let ctx = prepare_context();

        let target = TempFile::new_in(source.as_path()).expect("Cannot create temporary file.");
        let target_name = target
            .as_path()
            .file_name()
            .unwrap()
            .to_str()
            .expect("path to string");
        let target_c = CString::new(target_name).unwrap();
        let link_name = CString::new("test_symlink_link").unwrap();
        fs.symlink(&ctx, &target_c, ROOT_ID, &link_name).unwrap();

        let sym_entry = fs.lookup(&ctx, ROOT_ID, &link_name).unwrap();
        assert_eq!(sym_entry.attr.st_mode & libc::S_IFMT, libc::S_IFLNK);

        let hard_name = CString::new("test_symlink_hard").unwrap();
        match fs.link(&ctx, sym_entry.inode, ROOT_ID, &hard_name) {
            Ok(entry) => {
                // Privileged: the hard link is the symlink itself, so it
                // shares the inode and still points at the target.
                assert_eq!(entry.inode, sym_entry.inode);
                assert_eq!(entry.attr.st_mode & libc::S_IFMT, libc::S_IFLNK);
                assert_eq!(
                    std::fs::read_link(source.as_path().join("test_symlink_hard")).unwrap(),
                    Path::new(target_name)
                );
            }
            Err(e) => {
                // Unprivileged: a symlink cannot be linked without
                // following it, so the missing capability is reported.
                assert_eq!(e.raw_os_error(), Some(libc::EPERM));
            }
        }
    }

    // Hard-linking a regular file exercises both paths of link(): with
    // CAP_DAC_READ_SEARCH the first linkat() succeeds directly, while
    // without it the kernel answers ENOENT and the retry through
    // /proc/self/fd links the same inode. Either way the new name must
    // be a working hard link of the file; anything else is a bug.
    //
    // Built without inode file handles for the same reason as
    // test_link_symlink(): open_by_handle_at() would fail EPERM first
    // and shadow the code under test.
    #[test]
    fn test_link_regular() {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();
        let ctx = prepare_context();

        let file = TempFile::new_in(source.as_path()).expect("Cannot create temporary file.");
        let file_name = file
            .as_path()
            .file_name()
            .unwrap()
            .to_str()
            .expect("path to string");
        let file_c = CString::new(file_name).unwrap();
        let entry = fs.lookup(&ctx, ROOT_ID, &file_c).unwrap();
        assert_eq!(entry.attr.st_mode & libc::S_IFMT, libc::S_IFREG);

        let link_name = CString::new("test_regular_link").unwrap();
        let link_entry = fs.link(&ctx, entry.inode, ROOT_ID, &link_name).unwrap();
        assert_eq!(link_entry.inode, entry.inode);

        // The link must be real: both names resolve to the same file
        // with the link counted.
        use std::os::unix::fs::MetadataExt;
        let link_path = source.as_path().join("test_regular_link");
        assert_eq!(
            std::fs::metadata(&link_path).unwrap().ino(),
            std::fs::metadata(file.as_path()).unwrap().ino()
        );
        assert_eq!(std::fs::metadata(&link_path).unwrap().nlink(), 2);
    }

    // Copying between two files through copy_file_range(): a full copy with
    // non-zero offsets on both ends, which also grows the destination, and a
    // short copy truncated by the end of the source file.
    //
    // Built without inode file handles like test_link_regular(): under an
    // unprivileged runner open_by_handle_at() would fail EPERM first and
    // shadow the code under test.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_copy_file_range() {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();
        let ctx = prepare_context();

        // An 8KiB source file with recognizable content.
        let content: Vec<u8> = (0..8192u32).map(|i| (i % 251) as u8).collect();
        let src_path = source.as_path().join("copy_src.bin");
        std::fs::write(&src_path, &content).unwrap();

        let dst1_path = source.as_path().join("copy_dst1.bin");
        std::fs::write(&dst1_path, "").unwrap();
        let dst2_path = source.as_path().join("copy_dst2.bin");
        std::fs::write(&dst2_path, "").unwrap();

        let src_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("copy_src.bin").unwrap())
            .unwrap();
        let dst1_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("copy_dst1.bin").unwrap())
            .unwrap();
        let dst2_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("copy_dst2.bin").unwrap())
            .unwrap();
        let (src_handle, _, _) = fs
            .open(&ctx, src_entry.inode, libc::O_RDONLY as u32, 0)
            .unwrap();
        let (dst1_handle, _, _) = fs
            .open(&ctx, dst1_entry.inode, libc::O_WRONLY as u32, 0)
            .unwrap();
        let (dst2_handle, _, _) = fs
            .open(&ctx, dst2_entry.inode, libc::O_WRONLY as u32, 0)
            .unwrap();

        // Full copy: 2KiB from the middle of the source into the middle of
        // the (empty) destination, which grows to hold the data.
        let copied = fs
            .copy_file_range(
                &ctx,
                src_entry.inode,
                src_handle.unwrap(),
                4 * 1024,
                dst1_entry.inode,
                dst1_handle.unwrap(),
                512,
                2 * 1024,
                0,
            )
            .unwrap();
        assert_eq!(copied, 2 * 1024);

        let out = std::fs::read(&dst1_path).unwrap();
        assert_eq!(out.len(), 512 + 2 * 1024);
        assert!(out[..512].iter().all(|&b| b == 0));
        assert_eq!(&out[512..], &content[4 * 1024..6 * 1024]);

        // Short copy: only 1KiB is left in the source past offset 7KiB, so a
        // request for 2KiB reports a truncated result.
        let copied = fs
            .copy_file_range(
                &ctx,
                src_entry.inode,
                src_handle.unwrap(),
                7 * 1024,
                dst2_entry.inode,
                dst2_handle.unwrap(),
                0,
                2 * 1024,
                0,
            )
            .unwrap();
        assert_eq!(copied, 1024);

        let out = std::fs::read(&dst2_path).unwrap();
        assert_eq!(out.len(), 1024);
        assert_eq!(&out[..], &content[7 * 1024..]);

        // The source is untouched.
        assert_eq!(std::fs::read(&src_path).unwrap(), content);
    }

    // The WriteOut reply reports the copied length as a u32, so a request
    // longer than u32::MAX bytes must not fail: the length is capped and the
    // copy stays bounded by what the source holds.  The kernel clamps the
    // request the same way (min(len, UINT_MAX & PAGE_MASK)) before sending
    // it, so this guards the trait method against direct callers.
    //
    // Built without inode file handles like test_link_regular(): under an
    // unprivileged runner open_by_handle_at() would fail EPERM first and
    // shadow the code under test.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_copy_file_range_len_capped_to_reply_size() {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();
        let ctx = prepare_context();

        let content: Vec<u8> = (0..4096u32).map(|i| (i % 251) as u8).collect();
        std::fs::write(source.as_path().join("cap_src.bin"), &content).unwrap();
        std::fs::write(source.as_path().join("cap_dst.bin"), "").unwrap();

        let src_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("cap_src.bin").unwrap())
            .unwrap();
        let dst_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("cap_dst.bin").unwrap())
            .unwrap();
        let (src_handle, _, _) = fs
            .open(&ctx, src_entry.inode, libc::O_RDONLY as u32, 0)
            .unwrap();
        let (dst_handle, _, _) = fs
            .open(&ctx, dst_entry.inode, libc::O_WRONLY as u32, 0)
            .unwrap();

        let copied = fs
            .copy_file_range(
                &ctx,
                src_entry.inode,
                src_handle.unwrap(),
                0,
                dst_entry.inode,
                dst_handle.unwrap(),
                0,
                u32::MAX as u64 + 1,
                0,
            )
            .unwrap();
        assert_eq!(copied, 4096);
        assert_eq!(
            std::fs::read(source.as_path().join("cap_dst.bin")).unwrap(),
            content
        );
    }

    // A handle issued for one inode must not be usable against another: the
    // mismatched pair fails with EBADF before anything is copied.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_copy_file_range_handle_inode_mismatch() {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();
        let ctx = prepare_context();

        std::fs::write(source.as_path().join("mm_src.bin"), [1u8; 64]).unwrap();
        std::fs::write(source.as_path().join("mm_dst.bin"), [0u8; 64]).unwrap();

        let src_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("mm_src.bin").unwrap())
            .unwrap();
        let dst_entry = fs
            .lookup(&ctx, ROOT_ID, &CString::new("mm_dst.bin").unwrap())
            .unwrap();
        let (src_handle, _, _) = fs
            .open(&ctx, src_entry.inode, libc::O_RDONLY as u32, 0)
            .unwrap();
        let (dst_handle, _, _) = fs
            .open(&ctx, dst_entry.inode, libc::O_WRONLY as u32, 0)
            .unwrap();

        // The source handle paired with the destination inode.
        let err = fs
            .copy_file_range(
                &ctx,
                dst_entry.inode,
                src_handle.unwrap(),
                0,
                dst_entry.inode,
                dst_handle.unwrap(),
                0,
                64,
                0,
            )
            .unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::EBADF));

        // Nothing was copied.
        assert_eq!(
            std::fs::read(source.as_path().join("mm_dst.bin")).unwrap(),
            [0u8; 64]
        );
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

// End-to-end readdir/readdirplus coverage against a real backing directory:
// enumeration semantics (batching, cookies, EOF), the readdirplus
// attribute contract, the lookup-refcount ownership of the two handlers,
// the partial-delivery error contract, and the cookie cache lifecycle.
#[cfg(test)]
mod readdir_tests {
    use super::*;
    use fuse_backend_core::abi::fuse_abi::ROOT_ID;
    use vmm_sys_util::tempdir::TempDir;

    /// A passthrough fs over a fresh temporary directory, without inode
    /// file handles: the readdir paths under test are purely path-based,
    /// and `open_by_handle_at()` would only add an unprivileged EPERM
    /// failure mode on hosts where file handles are unavailable.
    fn prepare_fs() -> (PassthroughFs<()>, TempDir) {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let fs_cfg = Config {
            writeback: true,
            do_import: true,
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        // do_import: true, so init() imports the root inode; the ZERO_MESSAGE
        // options are not negotiated because cfg.no_open/no_opendir are false,
        // keeping persistent opendir() handles available to the tests.
        fs.init(FsOptions::all()).unwrap();
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

    /// Create `count` regular files named `f%03d` directly in the backing
    /// directory, bypassing the fs interfaces: the readdir handlers must
    /// pick them up through do_lookup() without any prior interaction, so
    /// the tests can observe exactly the references they take themselves.
    fn create_backing_files(source: &TempDir, count: usize) {
        for i in 0..count {
            std::fs::File::create(source.as_path().join(format!("f{:03}", i)))
                .expect("create file");
        }
    }

    /// One delivered readdir entry.
    struct Dirent {
        offset: u64,
        ino: u64,
        type_: u32,
        name: Vec<u8>,
    }

    /// One delivered readdirplus entry: the dirent fields plus the pieces of
    /// the lookup `Entry` that the readdirplus contract ties together.
    struct DirentPlus {
        dirent: Dirent,
        inode: u64,
        st_ino: u64,
        st_mode: u32,
        st_size: i64,
    }

    /// Drain a whole directory stream through `readdir`, resuming from the
    /// cookie of the last delivered entry until EOF, exactly like the fuse
    /// kernel client does. The batch count is bounded so that a cookie bug
    /// fails the test instead of looping forever.
    fn readdir_all(
        fs: &PassthroughFs<()>,
        ctx: &Context,
        handle: Handle,
        size: u32,
    ) -> Vec<Dirent> {
        let mut out: Vec<Dirent> = Vec::new();
        let mut offset = 0_u64;
        for _ in 0..1024 {
            let mut batch = Vec::new();
            fs.readdir(ctx, ROOT_ID, handle, size, offset, &mut |e| {
                batch.push(Dirent {
                    offset: e.offset,
                    ino: e.ino,
                    type_: e.type_,
                    name: e.name.to_vec(),
                });
                Ok(1)
            })
            .unwrap();
            if batch.is_empty() {
                break;
            }
            offset = batch.last().unwrap().offset;
            out.extend(batch);
        }
        out
    }

    /// Drain a whole directory stream through `readdirplus`, same resume
    /// discipline as `readdir_all()`.
    fn readdirplus_all(
        fs: &PassthroughFs<()>,
        ctx: &Context,
        handle: Handle,
        size: u32,
    ) -> Vec<DirentPlus> {
        let mut out: Vec<DirentPlus> = Vec::new();
        let mut offset = 0_u64;
        for _ in 0..1024 {
            let mut batch = Vec::new();
            fs.readdirplus(ctx, ROOT_ID, handle, size, offset, &mut |e, entry| {
                batch.push(DirentPlus {
                    dirent: Dirent {
                        offset: e.offset,
                        ino: e.ino,
                        type_: e.type_,
                        name: e.name.to_vec(),
                    },
                    inode: entry.inode,
                    st_ino: entry.attr.st_ino,
                    st_mode: entry.attr.st_mode,
                    st_size: entry.attr.st_size,
                });
                Ok(1)
            })
            .unwrap();
            if batch.is_empty() {
                break;
            }
            offset = batch.last().unwrap().dirent.offset;
            out.extend(batch);
        }
        out
    }

    /// Current refcount of `ino` in the inode map, or None when the inode is
    /// not mapped at all.
    fn refcount(fs: &PassthroughFs<()>, ino: Inode) -> Option<u64> {
        fs.inode_map
            .inodes
            .read()
            .unwrap()
            .get(&ino)
            .map(|d| d.refcount.load(std::sync::atomic::Ordering::Acquire))
    }

    fn open_root(fs: &PassthroughFs<()>, ctx: &Context) -> Handle {
        let (handle, _) = fs
            .opendir(ctx, ROOT_ID, libc::O_RDONLY as u32)
            .expect("opendir");
        handle.expect("opendir handle")
    }

    // A directory stream that does not fit into a single reply batch must
    // be delivered completely and exactly once: every resume goes through
    // the cached-cookie fast path of do_readdir(), so this pins both the
    // batch splitting and the cookie bookkeeping of the persistent handle.
    #[test]
    fn readdir_enumerates_all_entries_in_batches() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 64);

        let handle = open_root(&fs, &ctx);
        // A size of 128 bytes holds only a handful of dirents, forcing the
        // stream into ~20 reply batches.
        let entries = readdir_all(&fs, &ctx, handle, 128);

        assert_eq!(entries.len(), 64);
        let mut names: Vec<&Vec<u8>> = entries.iter().map(|e| &e.name).collect();
        names.sort();
        names.dedup();
        assert_eq!(names.len(), 64, "duplicate or lost entries");
        assert!(entries.iter().all(|e| e.offset != 0));
        assert!(
            entries.windows(2).all(|w| w[0].offset < w[1].offset),
            "cookies must strictly increase across the stream"
        );
        assert!(entries.iter().all(|e| e.ino != 0));

        // A second full enumeration of the same handle must be identical:
        // resuming from 0 re-seeks the stream, and the entry order of a
        // getdents64 stream is stable within one fd.
        let again = readdir_all(&fs, &ctx, handle, 128);
        assert_eq!(
            entries
                .iter()
                .map(|e| (e.offset, e.name.clone()))
                .collect::<Vec<_>>(),
            again
                .iter()
                .map(|e| (e.offset, e.name.clone()))
                .collect::<Vec<_>>()
        );

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // The readdirplus contract: the dirent inode must equal the st_ino of
    // the accompanying Entry, the Entry must describe the same file a
    // lookup() of the name returns, and the attributes must be real
    // (correct type and size). Delivered entries must also stay mapped
    // until the client forgets them.
    #[test]
    fn readdirplus_attrs_match_lookup() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        let count = 32;
        for i in 0..count {
            let size = (i as u64) * 17;
            std::fs::write(
                source.as_path().join(format!("f{:03}", i)),
                vec![0u8; size as usize],
            )
            .expect("write file");
        }

        let handle = open_root(&fs, &ctx);
        let entries = readdirplus_all(&fs, &ctx, handle, 8192);
        assert_eq!(entries.len(), count);

        for e in &entries {
            assert_eq!(e.dirent.ino, e.st_ino, "dirent ino must equal attr.st_ino");
            assert_eq!(e.dirent.type_, libc::DT_REG as u32);
            assert_eq!(e.st_mode & libc::S_IFMT, libc::S_IFREG);

            let name = CString::new(e.dirent.name.clone()).unwrap();
            let looked_up = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
            assert_eq!(e.inode, looked_up.inode, "entry inode must match lookup");
            assert_eq!(e.st_ino, looked_up.attr.st_ino);
            assert_eq!(e.st_mode, looked_up.attr.st_mode);
            // Drop the reference the verification lookup took again, so the
            // refcount checks below observe only the readdirplus ones.
            fs.forget(&ctx, looked_up.inode, 1);

            let idx: usize = std::str::from_utf8(&e.dirent.name)
                .unwrap()
                .trim_start_matches('f')
                .parse()
                .unwrap();
            assert_eq!(e.st_size, (idx as i64) * 17);
        }

        // readdirplus delivers entries with the lookup reference retained
        // (the kernel owns it until a FORGET), so every child is mapped
        // with exactly one reference after enumeration.
        for e in &entries {
            assert_eq!(refcount(&fs, e.inode), Some(1));
        }
        // Forgetting the delivered references must drop the mappings.
        for e in &entries {
            fs.forget(&ctx, e.inode, 1);
            assert_eq!(refcount(&fs, e.inode), None);
        }

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // Plain readdir must be reference-neutral: it looks each entry up to
    // learn its inode and immediately forgets that reference again. Files
    // never seen before stay unmapped, and a file the caller holds a
    // reference to keeps exactly that reference.
    #[test]
    fn readdir_releases_lookup_references() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 8);

        // One file with a caller-held reference: its refcount must survive
        // any number of enumerations unchanged.
        let held = CString::new("f003").unwrap();
        let held_entry = fs.lookup(&ctx, ROOT_ID, &held).unwrap();
        assert_eq!(refcount(&fs, held_entry.inode), Some(1));

        let handle = open_root(&fs, &ctx);
        for round in 0..2 {
            let entries = readdir_all(&fs, &ctx, handle, 4096);
            assert_eq!(entries.len(), 8, "round {}", round);

            for e in &entries {
                if e.ino == held_entry.inode {
                    // The pre-existing reference is untouched.
                    assert_eq!(refcount(&fs, e.ino), Some(1));
                } else {
                    // The reference taken by the handler was forgotten.
                    assert_eq!(refcount(&fs, e.ino), None, "round {}", round);
                }
            }
        }

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
        assert_eq!(refcount(&fs, held_entry.inode), Some(1));
    }

    // An entry that does not fit into the reply buffer (add_entry returning
    // 0) is not delivered, so readdirplus must release its lookup reference
    // right away instead of leaking it -- and must not report an error.
    #[test]
    fn readdirplus_buffer_full_forgets_undelivered() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 4);

        let handle = open_root(&fs, &ctx);
        let mut seen = 0;
        let mut first_ino = 0;
        fs.readdirplus(&ctx, ROOT_ID, handle, 8192, 0, &mut |_e, entry| {
            seen += 1;
            first_ino = entry.inode;
            Ok(0)
        })
        .unwrap();
        assert_eq!(seen, 1);

        // The undelivered entry was looked up and forgotten again.
        assert_eq!(refcount(&fs, first_ino), None);
        assert_ne!(first_ino, 0, "an inode must have been observed");

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // Error contract of the reply loop: an error before any entry was
    // stored propagates to the caller; an error after at least one entry
    // was stored returns Ok(()) with the partial delivery, because the
    // entries already handed out cannot be taken back. A fresh stream
    // always begins with "." and "..", which are filtered without the
    // callback, so the propagate case is exercised on a resumed stream
    // whose first record is a real entry.
    #[test]
    fn readdir_error_contract() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 4);

        let handle = open_root(&fs, &ctx);
        let entries = readdir_all(&fs, &ctx, handle, 8192);
        assert_eq!(entries.len(), 4);

        let eio = || io::Error::from_raw_os_error(libc::EIO);
        let err = fs
            .readdir(&ctx, ROOT_ID, handle, 8192, entries[0].offset, &mut |_| {
                Err(eio())
            })
            .unwrap_err();
        assert_eq!(
            err.raw_os_error(),
            Some(libc::EIO),
            "the callback's error must propagate on the first entry"
        );

        let mut delivered = 0;
        fs.readdir(&ctx, ROOT_ID, handle, 8192, 0, &mut |_| {
            delivered += 1;
            if delivered == 1 {
                Ok(1)
            } else {
                Err(eio())
            }
        })
        .unwrap();
        assert_eq!(
            delivered, 2,
            "callbacks: one entry delivered, then the error"
        );

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // An empty directory enumerates to EOF immediately, and size == 0 is
    // answered without touching the directory at all.
    #[test]
    fn readdir_empty_directory() {
        let (fs, _source) = prepare_fs();
        let ctx = prepare_context();

        let handle = open_root(&fs, &ctx);
        assert!(readdir_all(&fs, &ctx, handle, 4096).is_empty());
        assert!(readdirplus_all(&fs, &ctx, handle, 4096).is_empty());

        let mut entries = 0;
        fs.readdir(&ctx, ROOT_ID, handle, 0, 0, &mut |_| {
            entries += 1;
            Ok(1)
        })
        .unwrap();
        assert_eq!(entries, 0, "size == 0 must not enumerate anything");

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // Resuming from a cookie that is not the one cached for the handle (the
    // kernel re-issuing an earlier offset) must reposition the stream via
    // lseek and continue with the following entry: both when the cache is
    // empty and when it holds a stale cookie that must be discarded. A
    // cookie that lseek cannot represent (> i64::MAX, e.g. an NFSv4 cookie)
    // takes the linear scan fallback and terminates at EOF without looping.
    #[test]
    fn readdir_resume_from_mid_stream_cookie() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 16);

        let handle = open_root(&fs, &ctx);
        let entries = readdir_all(&fs, &ctx, handle, 8192);
        assert_eq!(entries.len(), 16);

        // The drain consumed the one-shot cached cookie with its final EOF
        // probe, so the cache is empty: resuming from a mid-stream cookie is
        // a miss against the empty cache and must go through lseek.
        let k = 5;
        let mut first = None;
        fs.readdir(&ctx, ROOT_ID, handle, 8192, entries[k].offset, &mut |e| {
            if first.is_none() {
                first = Some(e.name.to_vec());
            }
            Ok(1)
        })
        .unwrap();
        assert_eq!(first, Some(entries[k + 1].name.clone()));

        // A partial reply leaves the cookie of its last entry cached while
        // the stream is mid-way. Resuming from an earlier cookie mismatches
        // that token: it must be discarded rather than trusted as the fd
        // position, and the stream repositioned via lseek, continuing with
        // the entry after the requested one.
        let mut n = 0;
        fs.readdir(&ctx, ROOT_ID, handle, 128, 0, &mut |_| {
            n += 1;
            Ok(1)
        })
        .unwrap();
        assert!(n > 0 && n < 16, "a 128-byte reply must be a partial batch");
        let mut mismatch_first = None;
        fs.readdir(&ctx, ROOT_ID, handle, 8192, entries[0].offset, &mut |e| {
            if mismatch_first.is_none() {
                mismatch_first = Some(e.name.to_vec());
            }
            Ok(1)
        })
        .unwrap();
        assert_eq!(mismatch_first, Some(entries[1].name.clone()));

        // A cookie beyond i64::MAX cannot be seeked to; the scan fallback
        // walks the directory without finding it and reports EOF.
        let mut entries_after_huge = 0;
        fs.readdir(&ctx, ROOT_ID, handle, 8192, u64::MAX - 1, &mut |_| {
            entries_after_huge += 1;
            Ok(1)
        })
        .unwrap();
        assert_eq!(entries_after_huge, 0, "unknown huge cookie must end at EOF");

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // The d_type bits of the getdents records must reach the client
    // unchanged for the entry kinds a directory can hold.
    #[test]
    fn readdir_reports_entry_types() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 1);
        std::fs::create_dir(source.as_path().join("subdir")).expect("create dir");
        std::os::unix::fs::symlink("f000", source.as_path().join("link")).expect("create symlink");

        let handle = open_root(&fs, &ctx);
        let entries = readdir_all(&fs, &ctx, handle, 8192);

        let by_name = |name: &str| {
            entries
                .iter()
                .find(|e| e.name == name.as_bytes())
                .unwrap_or_else(|| panic!("entry {} missing", name))
        };
        assert_eq!(by_name("f000").type_, libc::DT_REG as u32);
        assert_eq!(by_name("subdir").type_, libc::DT_DIR as u32);
        assert_eq!(by_name("link").type_, libc::DT_LNK as u32);

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // In no_readdir mode both handlers report success without enumerating
    // anything, letting the client fall back to lookup-based iteration.
    #[test]
    fn readdir_disabled_returns_empty() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 4);
        fs.no_readdir.store(true, Ordering::Relaxed);

        let handle = open_root(&fs, &ctx);
        assert!(readdir_all(&fs, &ctx, handle, 4096).is_empty());
        assert!(readdirplus_all(&fs, &ctx, handle, 4096).is_empty());

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
    }

    // releasedir must drop the handle together with the cookie cached for
    // its directory stream, and the released handle must stop working.
    #[test]
    fn releasedir_clears_the_cookie_cache() {
        let (fs, source) = prepare_fs();
        let ctx = prepare_context();
        create_backing_files(&source, 4);

        let handle = open_root(&fs, &ctx);
        // One served batch leaves the cookie of its last entry in the cache.
        // Draining the whole stream would consume the token again: the
        // cached cookie is a one-shot fast path for the next resume, and the
        // final EOF probe of a full enumeration matches it.
        let mut seen = 0;
        fs.readdir(&ctx, ROOT_ID, handle, 4096, 0, &mut |_| {
            seen += 1;
            Ok(1)
        })
        .unwrap();
        assert!(seen > 0);
        assert!(
            !fs.handle_map.cookies.lock().unwrap().is_empty(),
            "a served readdir must have cached a cookie"
        );

        fs.releasedir(&ctx, ROOT_ID, 0, handle).unwrap();
        assert!(
            fs.handle_map.cookies.lock().unwrap().is_empty(),
            "releasedir must drop the cached cookie"
        );
        assert!(fs
            .readdir(&ctx, ROOT_ID, handle, 4096, 0, &mut |_| Ok(1))
            .is_err());
    }
}
