// Copyright 2020 Ant Financial. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use super::*;
use fuse_backend_core::abi::fuse_abi::{stat64, statvfs64};
#[cfg(feature = "virtiofs")]
use fuse_backend_core::abi::virtio_fs;
#[cfg(feature = "virtiofs")]
use fuse_backend_core::api::filesystem::FsCacheReqHandler;

// The errnos `Vfs::copy_file_range()` answers when the kernel should copy the data itself.
// Linux falls back on EXDEV and EOPNOTSUPP for that call only. On ENOSYS it falls back too,
// but stops sending COPY_FILE_RANGE for every mount in this Vfs. FreeBSD falls back only on
// ENOSYS and returns other errors to the caller.
#[cfg(not(target_os = "freebsd"))]
pub(super) const COPY_CROSS_MOUNT: i32 = libc::EXDEV;
#[cfg(not(target_os = "freebsd"))]
pub(super) const COPY_UNSUPPORTED: i32 = libc::EOPNOTSUPP;
#[cfg(target_os = "freebsd")]
pub(super) const COPY_CROSS_MOUNT: i32 = libc::ENOSYS;
#[cfg(target_os = "freebsd")]
pub(super) const COPY_UNSUPPORTED: i32 = libc::ENOSYS;

impl Vfs {
    /// The backend that serves a COPY_FILE_RANGE from `inode_in` to `inode_out`, with their
    /// inodes in it.
    pub(super) fn copy_file_range_fs(
        &self,
        inode_in: VfsInode,
        inode_out: VfsInode,
    ) -> Result<(ArcBackFs, VfsInode, VfsInode)> {
        // The pseudo fs has only directories, and the kernel never copies those.
        let (Right(fs), idata_in) = self.get_real_rootfs(inode_in)? else {
            return Err(Error::from_raw_os_error(libc::EISDIR));
        };
        let (Right(_), idata_out) = self.get_real_rootfs(inode_out)? else {
            return Err(Error::from_raw_os_error(libc::EISDIR));
        };

        if idata_in.fs_idx() != idata_out.fs_idx() {
            return Err(Error::from_raw_os_error(COPY_CROSS_MOUNT));
        }
        Ok((fs, idata_in, idata_out))
    }
}

/// The error for a COPY_FILE_RANGE that the backend failed with `e`.
pub(super) fn copy_file_range_error(e: Error) -> Error {
    match e.raw_os_error() {
        Some(libc::ENOSYS) => Error::from_raw_os_error(COPY_UNSUPPORTED),
        _ => e,
    }
}

impl FileSystem for Vfs {
    type Inode = VfsInode;
    type Handle = VfsHandle;

    fn init(&self, opts: FsOptions) -> Result<FsOptions> {
        if self.initialized() {
            error!("vfs is already initialized");
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        let mut n_opts = *self.opts.load().deref().deref();
        {
            // The kernel ignores FUSE_PASSTHROUGH along with FUSE_WRITEBACK_CACHE, and the
            // backing ids come from open replies. So negotiated passthrough overrides the
            // writeback cache and no_open.
            if (n_opts.out_opts & opts).contains(FsOptions::PASSTHROUGH) {
                info!("vfs: kernel passthrough negotiated, writeback cache and no_open off");
                n_opts.no_writeback = true;
                n_opts.no_open = false;
            }
            if n_opts.no_open {
                n_opts.no_open = !(opts & FsOptions::ZERO_MESSAGE_OPEN).is_empty();
                if n_opts.no_open {
                    // We can't support FUSE_ATOMIC_O_TRUNC with no_open: opens
                    // never reach us, so an O_TRUNC open can't truncate here.
                    // Only strip it when no_open actually survives negotiation
                    // though — a kernel that doesn't offer zero-message open
                    // keeps atomic O_TRUNC handling (the backends negotiate
                    // the same way, and macFUSE offers ATOMIC_O_TRUNC but
                    // never zero-message open).
                    n_opts.out_opts.remove(FsOptions::ATOMIC_O_TRUNC);
                }
            } else {
                n_opts.out_opts.remove(FsOptions::ZERO_MESSAGE_OPEN);
            }
            if n_opts.no_opendir {
                n_opts.no_opendir = !(opts & FsOptions::ZERO_MESSAGE_OPENDIR).is_empty();
            } else {
                n_opts.out_opts.remove(FsOptions::ZERO_MESSAGE_OPENDIR);
            }
            if n_opts.no_writeback {
                n_opts.out_opts.remove(FsOptions::WRITEBACK_CACHE);
            }
            if !n_opts.killpriv_v2 {
                n_opts.out_opts.remove(FsOptions::HANDLE_KILLPRIV_V2);
            }
        }
        n_opts.in_opts = opts;

        n_opts.out_opts &= opts;
        self.opts.store(Arc::new(n_opts));
        {
            // Serialize mount operations. Do not expect poisoned lock here.
            // Ensure that every backend fs only get init()ed once.
            let _guard = self.lock.lock().unwrap();
            let superblocks = self.superblocks.load();

            for fs in superblocks.iter().flatten() {
                fs.init(n_opts.out_opts)?;
            }
            self.initialized.store(true, Ordering::Release);
        }

        Ok(n_opts.out_opts)
    }

    fn destroy(&self) {
        if self.initialized() {
            let superblocks = self.superblocks.load();

            for fs in superblocks.iter().flatten() {
                fs.destroy();
            }

            self.initialized.store(false, Ordering::Release);
        }
    }

    fn lookup(&self, ctx: &Context, parent: VfsInode, name: &CStr) -> Result<Entry> {
        // Don't use is_safe_path_component(), allow "." and ".." for NFS export support
        if name.to_bytes_with_nul().contains(&SLASH_ASCII) {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => self.lookup_pseudo(fs, idata, ctx, name),
            (Right(fs), idata) => {
                // parent is in an underlying rootfs
                let entry = fs.lookup(ctx, idata.ino(), name)?;
                // lookup success, hash it to a real fuse inode
                self.convert_backend_entry(idata, entry)
            }
        }
    }

    fn forget(&self, ctx: &Context, inode: VfsInode, count: u64) {
        match self.get_real_rootfs(inode) {
            Ok(real_rootfs) => match real_rootfs {
                (Left(fs), idata) => fs.forget(ctx, idata.ino(), count),
                (Right(fs), idata) => fs.forget(ctx, idata.ino(), count),
            },
            Err(e) => {
                // When a directory is umount and invalidate entry, a forget request is triggered,
                // which cannot be forwarded to the backend file system. This is expected, and
                // comes once for every inode the kernel had cached, so log it at debug.
                debug!(
                    "vfs::forget: failed to get_real_rootfs {:?}, inode: {:?}, 
                       maybe it is possible that the vfs submount was dropped by umount, 
                       which is reasonable.",
                    e, inode
                );
            }
        }
    }

    fn getattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: Option<VfsHandle>,
    ) -> Result<(stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getattr(ctx, idata.ino(), handle),
            (Right(fs), idata) => fs
                .getattr(ctx, idata.ino(), handle)
                .map(|(attr, duration)| (self.convert_attr(idata, attr), duration)),
        }
    }

    fn setattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        attr: stat64,
        handle: Option<u64>,
        valid: SetattrValid,
    ) -> Result<(stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setattr(ctx, idata.ino(), attr, handle, valid),
            (Right(fs), idata) => {
                let mut attr = attr;
                self.remap_attr_id(idata.fs_idx(), false, &mut attr);
                fs.setattr(ctx, idata.ino(), attr, handle, valid)
                    .map(|(attr, duration)| (self.convert_attr(idata, attr), duration))
            }
        }
    }

    fn readlink(&self, ctx: &Context, inode: VfsInode) -> Result<Vec<u8>> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.readlink(ctx, idata.ino()),
            (Right(fs), idata) => fs.readlink(ctx, idata.ino()),
        }
    }

    fn symlink(
        &self,
        ctx: &Context,
        linkname: &CStr,
        parent: VfsInode,
        name: &CStr,
    ) -> Result<Entry> {
        validate_path_component(name)?;

        let ctx = self.ctx_for_mount(ctx, parent.fs_idx());

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.symlink(&ctx, linkname, idata.ino(), name),
            (Right(fs), idata) => fs
                .symlink(&ctx, linkname, idata.ino(), name)
                .and_then(|e| self.convert_backend_entry(idata, e)),
        }
    }

    fn mknod(
        &self,
        ctx: &Context,
        inode: VfsInode,
        name: &CStr,
        mode: u32,
        rdev: u32,
        umask: u32,
    ) -> Result<Entry> {
        validate_path_component(name)?;

        let ctx = self.ctx_for_mount(ctx, inode.fs_idx());

        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.mknod(&ctx, idata.ino(), name, mode, rdev, umask),
            (Right(fs), idata) => fs
                .mknod(&ctx, idata.ino(), name, mode, rdev, umask)
                .and_then(|e| self.convert_backend_entry(idata, e)),
        }
    }

    fn mkdir(
        &self,
        ctx: &Context,
        parent: VfsInode,
        name: &CStr,
        mode: u32,
        umask: u32,
    ) -> Result<Entry> {
        validate_path_component(name)?;

        let ctx = self.ctx_for_mount(ctx, parent.fs_idx());

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.mkdir(&ctx, idata.ino(), name, mode, umask),
            (Right(fs), idata) => fs
                .mkdir(&ctx, idata.ino(), name, mode, umask)
                .and_then(|e| self.convert_backend_entry(idata, e)),
        }
    }

    fn unlink(&self, ctx: &Context, parent: VfsInode, name: &CStr) -> Result<()> {
        validate_path_component(name)?;

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.unlink(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.unlink(ctx, idata.ino(), name),
        }
    }

    fn rmdir(&self, ctx: &Context, parent: VfsInode, name: &CStr) -> Result<()> {
        validate_path_component(name)?;

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
        }
    }

    fn rename(
        &self,
        ctx: &Context,
        olddir: VfsInode,
        oldname: &CStr,
        newdir: VfsInode,
        newname: &CStr,
        flags: u32,
    ) -> Result<()> {
        validate_path_component(oldname)?;
        validate_path_component(newname)?;

        let (root, idata_old, idata_new) = self.get_real_rootfs_pair(olddir, newdir)?;

        match root {
            Left(fs) => fs.rename(
                ctx,
                idata_old.ino(),
                oldname,
                idata_new.ino(),
                newname,
                flags,
            ),
            Right(fs) => fs.rename(
                ctx,
                idata_old.ino(),
                oldname,
                idata_new.ino(),
                newname,
                flags,
            ),
        }
    }

    fn link(
        &self,
        ctx: &Context,
        inode: VfsInode,
        newparent: VfsInode,
        newname: &CStr,
    ) -> Result<Entry> {
        validate_path_component(newname)?;

        let (root, idata_old, idata_new) = self.get_real_rootfs_pair(inode, newparent)?;

        match root {
            Left(fs) => fs.link(ctx, idata_old.ino(), idata_new.ino(), newname),
            Right(fs) => fs
                .link(ctx, idata_old.ino(), idata_new.ino(), newname)
                .and_then(|e| self.convert_backend_entry(idata_new, e)),
        }
    }

    fn open(
        &self,
        ctx: &Context,
        inode: VfsInode,
        flags: u32,
        fuse_flags: u32,
    ) -> Result<(Option<u64>, OpenOptions, Option<u32>)> {
        if self.opts.load().no_open {
            return Err(Error::from_raw_os_error(libc::ENOSYS));
        }
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.open(ctx, idata.ino(), flags, fuse_flags),
            (Right(fs), idata) => fs.open(ctx, idata.ino(), flags, fuse_flags),
        }
    }

    fn create(
        &self,
        ctx: &Context,
        parent: VfsInode,
        name: &CStr,
        args: CreateIn,
    ) -> Result<(Entry, Option<u64>, OpenOptions, Option<u32>)> {
        validate_path_component(name)?;

        let ctx = self.ctx_for_mount(ctx, parent.fs_idx());

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.create(&ctx, idata.ino(), name, args),
            (Right(fs), idata) => {
                fs.create(&ctx, idata.ino(), name, args)
                    .and_then(|(a, b, c, d)| {
                        self.convert_backend_entry(idata, a).map(|a| (a, b, c, d))
                    })
            }
        }
    }

    fn read(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        w: &mut dyn ZeroCopyWriter,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> Result<usize> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                fs.read(ctx, idata.ino(), handle, w, size, offset, lock_owner, flags)
            }
            (Right(fs), idata) => {
                fs.read(ctx, idata.ino(), handle, w, size, offset, lock_owner, flags)
            }
        }
    }

    fn write(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        r: &mut dyn ZeroCopyReader,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> Result<usize> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.write(
                ctx,
                idata.ino(),
                handle,
                r,
                size,
                offset,
                lock_owner,
                delayed_write,
                flags,
                fuse_flags,
            ),
            (Right(fs), idata) => fs.write(
                ctx,
                idata.ino(),
                handle,
                r,
                size,
                offset,
                lock_owner,
                delayed_write,
                flags,
                fuse_flags,
            ),
        }
    }

    fn flush(&self, ctx: &Context, inode: VfsInode, handle: u64, lock_owner: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
            (Right(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
        }
    }

    fn fsync(&self, ctx: &Context, inode: VfsInode, datasync: bool, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
        }
    }

    fn fallocate(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fallocate(ctx, idata.ino(), handle, mode, offset, length),
            (Right(fs), idata) => fs.fallocate(ctx, idata.ino(), handle, mode, offset, length),
        }
    }

    fn release(
        &self,
        ctx: &Context,
        inode: VfsInode,
        flags: u32,
        handle: u64,
        flush: bool,
        flock_release: bool,
        lock_owner: Option<u64>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.release(
                ctx,
                idata.ino(),
                flags,
                handle,
                flush,
                flock_release,
                lock_owner,
            ),
            (Right(fs), idata) => fs.release(
                ctx,
                idata.ino(),
                flags,
                handle,
                flush,
                flock_release,
                lock_owner,
            ),
        }
    }

    fn statfs(&self, ctx: &Context, inode: VfsInode) -> Result<statvfs64> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.statfs(ctx, idata.ino()),
            (Right(fs), idata) => fs.statfs(ctx, idata.ino()),
        }
    }

    fn setxattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        name: &CStr,
        value: &[u8],
        flags: u32,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setxattr(ctx, idata.ino(), name, value, flags),
            (Right(fs), idata) => fs.setxattr(ctx, idata.ino(), name, value, flags),
        }
    }

    fn getxattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        name: &CStr,
        size: u32,
    ) -> Result<GetxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
            (Right(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
        }
    }

    fn listxattr(&self, ctx: &Context, inode: VfsInode, size: u32) -> Result<ListxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
            (Right(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
        }
    }

    fn removexattr(&self, ctx: &Context, inode: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
        }
    }

    fn opendir(
        &self,
        ctx: &Context,
        inode: VfsInode,
        flags: u32,
    ) -> Result<(Option<VfsHandle>, OpenOptions)> {
        if self.opts.load().no_opendir {
            return Err(Error::from_raw_os_error(libc::ENOSYS));
        }
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.opendir(ctx, idata.ino(), flags),
            (Right(fs), idata) => fs.opendir(ctx, idata.ino(), flags),
        }
    }

    fn readdir(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry) -> Result<usize>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                self.readdir_pseudo(fs, idata, ctx, handle, size, offset, add_entry)
            }

            (Right(fs), idata) => fs.readdir(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry| {
                    let new_ino = self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                    dir_entry.ino = new_ino;
                    add_entry(dir_entry)
                },
            ),
        }
    }

    fn readdirplus(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, Entry) -> Result<usize>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                self.readdirplus_pseudo(fs, idata, ctx, handle, size, offset, add_entry)
            }

            (Right(fs), idata) => fs.readdirplus(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry, entry| {
                    let entry = self.convert_backend_entry(idata, entry)?;
                    dir_entry.ino = entry.inode;
                    add_entry(dir_entry, entry)
                },
            ),
        }
    }

    fn fsyncdir(&self, ctx: &Context, inode: VfsInode, datasync: bool, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
        }
    }

    fn releasedir(&self, ctx: &Context, inode: VfsInode, flags: u32, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
            (Right(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
        }
    }

    fn access(&self, ctx: &Context, inode: VfsInode, mask: u32) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.access(ctx, idata.ino(), mask),
            (Right(fs), idata) => fs.access(ctx, idata.ino(), mask),
        }
    }

    fn copy_file_range(
        &self,
        ctx: &Context,
        inode_in: VfsInode,
        fh_in: VfsHandle,
        offset_in: u64,
        inode_out: VfsInode,
        fh_out: VfsHandle,
        offset_out: u64,
        len: u64,
        flags: u64,
    ) -> Result<u32> {
        let (fs, idata_in, idata_out) = self.copy_file_range_fs(inode_in, inode_out)?;
        fs.copy_file_range(
            ctx,
            idata_in.ino(),
            fh_in,
            offset_in,
            idata_out.ino(),
            fh_out,
            offset_out,
            len,
            flags,
        )
        .map_err(copy_file_range_error)
    }

    #[inline]
    fn id_remap(&self, ctx: &mut Context) -> Result<()> {
        // Without an inode there is no way to identify the target mount, so
        // fall back to the global id_mapping.
        self.remap_ctx_ids(ctx, self.id_mapping)
    }

    #[inline]
    fn id_remap_with_nodeid(&self, ctx: &mut Context, nodeid: Self::Inode) -> Result<()> {
        // Use the per-mount mapping identified by the fs_idx encoded in
        // nodeid, falling back to the global mapping for pseudo-fs
        // operations (fs_idx == 0).
        self.remap_ctx_ids(ctx, self.get_effective_id_mapping(nodeid.fs_idx()))
    }

    #[cfg(feature = "virtiofs")]
    fn setupmapping(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        foffset: u64,
        len: u64,
        flags: u64,
        moffset: u64,
        req: &mut dyn FsCacheReqHandler,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                fs.setupmapping(ctx, idata.ino(), handle, foffset, len, flags, moffset, req)
            }
            (Right(fs), idata) => {
                fs.setupmapping(ctx, idata.ino(), handle, foffset, len, flags, moffset, req)
            }
        }
    }

    #[cfg(feature = "virtiofs")]
    fn removemapping(
        &self,
        ctx: &Context,
        inode: VfsInode,
        requests: Vec<virtio_fs::RemovemappingOne>,
        req: &mut dyn FsCacheReqHandler,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.removemapping(ctx, idata.ino(), requests, req),
            (Right(fs), idata) => fs.removemapping(ctx, idata.ino(), requests, req),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::any::Any;

    use super::*;
    use crate::tests::FakeFileSystemOne;
    use std::ffi::CString;

    /// A backend that records its `copy_file_range()` calls. It fails them with `errno`, or
    /// copies `len` bytes when `errno` is 0.
    struct CopyFs {
        errno: i32,
        calls: Arc<Mutex<Vec<[u64; 8]>>>,
    }

    impl FileSystem for CopyFs {
        type Inode = u64;
        type Handle = u64;

        fn copy_file_range(
            &self,
            _ctx: &Context,
            inode_in: u64,
            fh_in: u64,
            offset_in: u64,
            inode_out: u64,
            fh_out: u64,
            offset_out: u64,
            len: u64,
            flags: u64,
        ) -> Result<u32> {
            let args = [
                inode_in, fh_in, offset_in, inode_out, fh_out, offset_out, len, flags,
            ];
            self.calls.lock().unwrap().push(args);
            match self.errno {
                0 => Ok(len as u32),
                errno => Err(Error::from_raw_os_error(errno)),
            }
        }
    }

    #[cfg(feature = "async-io")]
    impl AsyncFileSystem for CopyFs {}

    impl BackendFileSystem for CopyFs {
        fn mount(&self) -> Result<(Entry, u64)> {
            let root = Entry {
                inode: 1,
                ..Default::default()
            };
            Ok((root, 0))
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    /// Mounts a `CopyFs` at `path`, and returns its index and the calls it gets.
    fn mount_copy_fs(vfs: &Vfs, path: &str, errno: i32) -> (VfsIndex, Arc<Mutex<Vec<[u64; 8]>>>) {
        let calls = Arc::new(Mutex::new(Vec::new()));
        let fs = CopyFs {
            errno,
            calls: calls.clone(),
        };
        (vfs.mount(Box::new(fs), path).unwrap(), calls)
    }

    /// Copies 4096 bytes from handle 10 at offset 100 to handle 20 at offset 200.
    fn copy(vfs: &Vfs, inode_in: VfsInode, inode_out: VfsInode) -> Result<u32> {
        let ctx = Context::default();
        vfs.copy_file_range(&ctx, inode_in, 10, 100, inode_out, 20, 200, 4096, 0)
    }

    fn errno(result: Result<u32>) -> Option<i32> {
        result.unwrap_err().raw_os_error()
    }

    #[test]
    fn test_copy_file_range_within_a_mount() {
        let vfs = Vfs::default();
        mount_copy_fs(&vfs, "/a", 0);
        let (b, calls) = mount_copy_fs(&vfs, "/b", 0);

        let copied = copy(&vfs, VfsInode::new(b, 5), VfsInode::new(b, 6)).unwrap();
        assert_eq!(copied, 4096);
        assert_eq!(*calls.lock().unwrap(), [[5, 10, 100, 6, 20, 200, 4096, 0]]);
    }

    #[test]
    fn test_copy_file_range_across_mounts() {
        let vfs = Vfs::default();
        let (a, _) = mount_copy_fs(&vfs, "/a", 0);
        let (b, _) = mount_copy_fs(&vfs, "/b", 0);

        let result = copy(&vfs, VfsInode::new(a, 5), VfsInode::new(b, 5));
        assert_eq!(errno(result), Some(COPY_CROSS_MOUNT));
    }

    #[test]
    fn test_copy_file_range_backend_errors() {
        let vfs = Vfs::default();
        let (a, _) = mount_copy_fs(&vfs, "/a", libc::ENOSYS);
        let (b, _) = mount_copy_fs(&vfs, "/b", libc::EBADF);

        let result = copy(&vfs, VfsInode::new(a, 5), VfsInode::new(a, 6));
        assert_eq!(errno(result), Some(COPY_UNSUPPORTED));
        let result = copy(&vfs, VfsInode::new(b, 5), VfsInode::new(b, 6));
        assert_eq!(errno(result), Some(libc::EBADF));
    }

    #[test]
    fn test_copy_file_range_pseudo_dirs() {
        let vfs = Vfs::default();
        let (idx, _) = mount_copy_fs(&vfs, "/x/y", 0);
        let file = VfsInode::new(idx, 5);

        // The root and /x, inode 2, are pseudo fs directories.
        for dir in [ROOT_ID, 2].map(VfsInode::from) {
            for (inode_in, inode_out) in [(dir, file), (file, dir), (dir, dir)] {
                let result = copy(&vfs, inode_in, inode_out);
                assert_eq!(errno(result), Some(libc::EISDIR));
            }
        }
    }

    #[test]
    fn test_id_remap_reverse_direction_without_underflow() {
        let vfs = Vfs::new(VfsOptions {
            id_mapping: (0, 100000, 65536),
            ..Default::default()
        });

        let mut ctx = Context {
            uid: 100000,
            gid: 100123,
            pid: 1,
            supp_gid: None,
            ..Default::default()
        };

        vfs.id_remap(&mut ctx).unwrap();

        assert_eq!(ctx.uid, 0);
        assert_eq!(ctx.gid, 123);
    }

    #[test]
    fn test_id_remap_with_nodeid_fallback_to_global() {
        let vfs = Vfs::new(VfsOptions {
            id_mapping: (0, 100000, 65536),
            ..Default::default()
        });

        let mut ctx = Context {
            uid: 100000,
            gid: 100123,
            pid: 1,
            supp_gid: None,
            ..Default::default()
        };

        // fs_idx == 0 (pseudo fs) falls back to global mapping
        vfs.id_remap_with_nodeid(&mut ctx, VfsInode::from(0))
            .unwrap();

        assert_eq!(ctx.uid, 0);
        assert_eq!(ctx.gid, 123);
    }

    #[test]
    fn test_remap_ctx_supp_gid() {
        let vfs = Vfs::new(VfsOptions {
            id_mapping: (0, 100000, 65536),
            ..Default::default()
        });

        // An external gid inside the mapped range is translated to the
        // internal (host) namespace.  fs_idx 0 (pseudo fs) falls back to
        // the global mapping.
        let mut ctx = Context {
            uid: 100000,
            gid: 100123,
            pid: 1,
            supp_gid: Some(100123),
            ..Default::default()
        };
        vfs.remap_ctx_supp_gid(&mut ctx, 0);
        assert_eq!(ctx.supp_gid, Some(123));

        // An external gid outside the mapped range has no host counterpart
        // and is dropped instead of being adopted untranslated.
        ctx = Context {
            uid: 100000,
            gid: 100123,
            pid: 1,
            supp_gid: Some(5),
            ..Default::default()
        };
        vfs.remap_ctx_supp_gid(&mut ctx, 0);
        assert_eq!(ctx.supp_gid, None);

        // Without an id mapping the gid passes through unchanged.
        let vfs = Vfs::new(VfsOptions::default());
        ctx = Context {
            uid: 0,
            gid: 0,
            pid: 1,
            supp_gid: Some(123),
            ..Default::default()
        };
        vfs.remap_ctx_supp_gid(&mut ctx, 0);
        assert_eq!(ctx.supp_gid, Some(123));
    }

    #[test]
    fn test_remap_ctx_supplementary_groups() {
        let vfs = Vfs::new(VfsOptions {
            id_mapping: (0, 100000, 65536),
            ..Default::default()
        });

        // Groups inside the mapped range are translated to internal (host)
        // ids in order; groups outside the range have no host counterpart
        // and are dropped instead of being adopted untranslated.
        let mut ctx = Context {
            uid: 100000,
            gid: 100123,
            pid: 1,
            supplementary_groups: Some(vec![100123, 5, 165535, 100124]),
            ..Default::default()
        };
        vfs.id_remap(&mut ctx).unwrap();
        assert_eq!(ctx.supplementary_groups, Some(vec![123, 65535, 124]),);
        assert_eq!(ctx.uid, 0);
        assert_eq!(ctx.gid, 123);

        // An empty list stays empty, and a reversed mapping direction
        // (internal base above the external base) translates without
        // underflow.
        let vfs = Vfs::new(VfsOptions {
            id_mapping: (200000, 100000, 65536),
            ..Default::default()
        });
        let mut ctx = Context {
            uid: 100000,
            gid: 100500,
            pid: 1,
            supplementary_groups: Some(Vec::new()),
            ..Default::default()
        };
        vfs.id_remap(&mut ctx).unwrap();
        assert_eq!(ctx.supplementary_groups, Some(Vec::new()));

        ctx.supplementary_groups = Some(vec![100500, 99999]);
        vfs.id_remap(&mut ctx).unwrap();
        assert_eq!(ctx.supplementary_groups, Some(vec![200500]));

        // Without an id mapping the groups pass through unchanged, and
        // `None` never allocates a list.
        let vfs = Vfs::new(VfsOptions::default());
        let mut ctx = Context {
            uid: 0,
            gid: 0,
            pid: 1,
            supplementary_groups: Some(vec![123]),
            ..Default::default()
        };
        vfs.id_remap(&mut ctx).unwrap();
        assert_eq!(ctx.supplementary_groups, Some(vec![123]));

        ctx.supplementary_groups = None;
        vfs.id_remap(&mut ctx).unwrap();
        assert_eq!(ctx.supplementary_groups, None);
    }

    #[test]
    fn test_xattr_name_with_slash() {
        fn errno<T>(res: Result<T>) -> Option<i32> {
            res.err().and_then(|e| e.raw_os_error())
        }

        let vfs = Vfs::new(VfsOptions::default());
        vfs.mount(Box::new(FakeFileSystemOne {}), "/x").unwrap();
        let ctx = Context::new();
        let x = vfs.lookup(&ctx, ROOT_ID.into(), &CString::new("x").unwrap());
        let inode = x.unwrap().inode.into();

        // Linux allows '/' in xattr names, so the requests reach the file system, whose
        // default handlers answer ENOSYS.
        let name = CString::new("user.a/b").unwrap();
        let enosys = Some(libc::ENOSYS);
        assert_eq!(errno(vfs.setxattr(&ctx, inode, &name, b"v", 0)), enosys);
        assert_eq!(errno(vfs.getxattr(&ctx, inode, &name, 0)), enosys);
        assert_eq!(errno(vfs.removexattr(&ctx, inode, &name)), enosys);
    }
}
