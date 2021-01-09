// Copyright 2020 Ant Financial. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::async_util::AsyncDrive;

impl<D: AsyncDrive> FileSystem for Vfs<D> {
    type Inode = VfsInode;
    type Handle = VfsHandle;

    fn init(&self, opts: FsOptions) -> Result<FsOptions> {
        if self.initialized() {
            error!("vfs is already initialized");
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        let mut n_opts = *self.opts.load().deref().deref();
        if n_opts.no_open {
            n_opts.no_open = !(opts & FsOptions::ZERO_MESSAGE_OPEN).is_empty();
        }
        n_opts.no_opendir = !(opts & FsOptions::ZERO_MESSAGE_OPENDIR).is_empty();
        if n_opts.no_writeback {
            n_opts.out_opts.remove(FsOptions::WRITEBACK_CACHE);
        }
        n_opts.in_opts = opts;

        n_opts.out_opts &= opts;
        self.opts.store(Arc::new(n_opts));
        {
            // Serialize mount operations. Do not expect poisoned lock here.
            // Ensure that every backend fs only get init()ed once.
            let _guard = self.lock.lock().unwrap();
            for (_, fs) in self.superblocks.load().iter() {
                fs.init(n_opts.out_opts)?;
            }
            self.initialized.store(true, Ordering::Release);
        }

        Ok(n_opts.out_opts)
    }

    fn destroy(&self) {
        if self.initialized() {
            self.superblocks
                .load()
                .iter()
                .for_each(|(_, f)| f.destroy());

            // Keep initialized true to avoid being attacked by guest
            // self.initialized.store(false, Ordering::Release);
        }
    }

    fn lookup(&self, ctx: Context, parent: VfsInode, name: &CStr) -> Result<Entry> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => self.lookup_pseudo(fs, idata, ctx, name),
            (Right(fs), idata) => {
                // parent is in an underlying rootfs
                let mut entry = fs.lookup(ctx, idata.ino(), name)?;
                // lookup success, hash it to a real fuse inode
                entry.inode = self.convert_inode(idata.fs_idx(), entry.inode)?;
                Ok(entry)
            }
        }
    }

    fn forget(&self, ctx: Context, inode: VfsInode, count: u64) {
        match self.get_real_rootfs(inode) {
            Ok(real_rootfs) => match real_rootfs {
                (Left(fs), idata) => fs.forget(ctx, idata.ino(), count),
                (Right(fs), idata) => fs.forget(ctx, idata.ino(), count),
            },
            Err(e) => {
                error!("vfs::forget: failed to get_real_rootfs {:?}", e);
            }
        }
    }

    fn getattr(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: Option<VfsHandle>,
    ) -> Result<(libc::stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getattr(ctx, idata.ino(), handle),
            (Right(fs), idata) => fs.getattr(ctx, idata.ino(), handle),
        }
    }

    fn setattr(
        &self,
        ctx: Context,
        inode: VfsInode,
        attr: libc::stat64,
        handle: Option<u64>,
        valid: SetattrValid,
    ) -> Result<(libc::stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setattr(ctx, idata.ino(), attr, handle, valid),
            (Right(fs), idata) => fs.setattr(ctx, idata.ino(), attr, handle, valid),
        }
    }

    fn readlink(&self, ctx: Context, inode: VfsInode) -> Result<Vec<u8>> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.readlink(ctx, idata.ino()),
            (Right(fs), idata) => fs.readlink(ctx, idata.ino()),
        }
    }

    fn symlink(
        &self,
        ctx: Context,
        linkname: &CStr,
        parent: VfsInode,
        name: &CStr,
    ) -> Result<Entry> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.symlink(ctx, linkname, idata.ino(), name),
            (Right(fs), idata) => fs.symlink(ctx, linkname, idata.ino(), name).map(|mut e| {
                e.inode = self.convert_inode(idata.fs_idx(), e.inode)?;
                Ok(e)
            })?,
        }
    }

    fn mknod(
        &self,
        ctx: Context,
        inode: VfsInode,
        name: &CStr,
        mode: u32,
        rdev: u32,
        umask: u32,
    ) -> Result<Entry> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.mknod(ctx, idata.ino(), name, mode, rdev, umask),
            (Right(fs), idata) => {
                fs.mknod(ctx, idata.ino(), name, mode, rdev, umask)
                    .map(|mut e| {
                        e.inode = self.convert_inode(idata.fs_idx(), e.inode)?;
                        Ok(e)
                    })?
            }
        }
    }

    fn mkdir(
        &self,
        ctx: Context,
        parent: VfsInode,
        name: &CStr,
        mode: u32,
        umask: u32,
    ) -> Result<Entry> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.mkdir(ctx, idata.ino(), name, mode, umask),
            (Right(fs), idata) => fs.mkdir(ctx, idata.ino(), name, mode, umask).map(|mut e| {
                e.inode = self.convert_inode(idata.fs_idx(), e.inode)?;
                Ok(e)
            })?,
        }
    }

    fn unlink(&self, ctx: Context, parent: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.unlink(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.unlink(ctx, idata.ino(), name),
        }
    }

    fn rmdir(&self, ctx: Context, parent: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
        }
    }

    fn rename(
        &self,
        ctx: Context,
        olddir: VfsInode,
        oldname: &CStr,
        newdir: VfsInode,
        newname: &CStr,
        flags: u32,
    ) -> Result<()> {
        let (root, idata_old) = self.get_real_rootfs(olddir)?;
        let (_, idata_new) = self.get_real_rootfs(newdir)?;

        if idata_old.fs_idx() != idata_new.fs_idx() {
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }

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
        ctx: Context,
        inode: VfsInode,
        newparent: VfsInode,
        newname: &CStr,
    ) -> Result<Entry> {
        let (root, idata_old) = self.get_real_rootfs(inode)?;
        let (_, idata_new) = self.get_real_rootfs(newparent)?;

        if idata_old.fs_idx() != idata_new.fs_idx() {
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }

        match root {
            Left(fs) => fs.link(ctx, idata_old.ino(), idata_new.ino(), newname),
            Right(fs) => fs
                .link(ctx, idata_old.ino(), idata_new.ino(), newname)
                .map(|mut e| {
                    e.inode = self.convert_inode(idata_new.fs_idx(), e.inode)?;
                    Ok(e)
                })?,
        }
    }

    fn open(
        &self,
        ctx: Context,
        inode: VfsInode,
        flags: u32,
    ) -> Result<(Option<u64>, OpenOptions)> {
        if self.opts.load().no_open {
            Err(Error::from_raw_os_error(libc::ENOSYS))
        } else {
            match self.get_real_rootfs(inode)? {
                (Left(fs), idata) => fs.open(ctx, idata.ino(), flags),
                (Right(fs), idata) => fs
                    .open(ctx, idata.ino(), flags)
                    .map(|(h, opt)| (h.map(Into::into), opt)),
            }
        }
    }

    fn create(
        &self,
        ctx: Context,
        parent: VfsInode,
        name: &CStr,
        mode: u32,
        flags: u32,
        umask: u32,
    ) -> Result<(Entry, Option<u64>, OpenOptions)> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.create(ctx, idata.ino(), name, mode, flags, umask),
            (Right(fs), idata) => {
                fs.create(ctx, idata.ino(), name, mode, flags, umask)
                    .map(|(mut a, b, c)| {
                        a.inode = self.convert_inode(idata.fs_idx(), a.inode)?;
                        Ok((a, b, c))
                    })?
            }
        }
    }

    fn read(
        &self,
        ctx: Context,
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
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        r: &mut dyn ZeroCopyReader,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
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
            ),
        }
    }

    fn flush(&self, ctx: Context, inode: VfsInode, handle: u64, lock_owner: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
            (Right(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
        }
    }

    fn fsync(&self, ctx: Context, inode: VfsInode, datasync: bool, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
        }
    }

    fn fallocate(
        &self,
        ctx: Context,
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
        ctx: Context,
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

    fn statfs(&self, ctx: Context, inode: VfsInode) -> Result<libc::statvfs64> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.statfs(ctx, idata.ino()),
            (Right(fs), idata) => fs.statfs(ctx, idata.ino()),
        }
    }

    fn setxattr(
        &self,
        ctx: Context,
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
        ctx: Context,
        inode: VfsInode,
        name: &CStr,
        size: u32,
    ) -> Result<GetxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
            (Right(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
        }
    }

    fn listxattr(&self, ctx: Context, inode: VfsInode, size: u32) -> Result<ListxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
            (Right(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
        }
    }

    fn removexattr(&self, ctx: Context, inode: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
        }
    }

    fn opendir(
        &self,
        ctx: Context,
        inode: VfsInode,
        flags: u32,
    ) -> Result<(Option<VfsHandle>, OpenOptions)> {
        if self.opts.load().no_opendir {
            Err(Error::from_raw_os_error(libc::ENOSYS))
        } else {
            match self.get_real_rootfs(inode)? {
                (Left(fs), idata) => fs.opendir(ctx, idata.ino(), flags),
                (Right(fs), idata) => fs
                    .opendir(ctx, idata.ino(), flags)
                    .map(|(h, opt)| (h.map(Into::into), opt)),
            }
        }
    }

    fn readdir(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry) -> Result<usize>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                fs.readdir(
                    ctx,
                    idata.ino(),
                    handle,
                    size,
                    offset,
                    &mut |mut dir_entry| {
                        match self.mountpoints.load().get(&dir_entry.ino) {
                            // cross mountpoint, return mount root entry
                            Some(mnt) => {
                                dir_entry.ino = self.convert_inode(mnt.fs_idx, mnt.ino)?;
                            }
                            None => {
                                dir_entry.ino =
                                    self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                            }
                        }
                        add_entry(dir_entry)
                    },
                )
            }

            (Right(fs), idata) => fs.readdir(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry| {
                    dir_entry.ino = self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                    add_entry(dir_entry)
                },
            ),
        }
    }

    fn readdirplus(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, Entry) -> Result<usize>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.readdirplus(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry, mut entry| {
                    match self.mountpoints.load().get(&dir_entry.ino) {
                        Some(mnt) => {
                            // cross mountpoint, return mount root entry
                            dir_entry.ino = self.convert_inode(mnt.fs_idx, mnt.ino)?;
                            entry = mnt.root_entry;
                        }
                        None => {
                            dir_entry.ino = self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                            entry.inode = dir_entry.ino;
                        }
                    }

                    add_entry(dir_entry, entry)
                },
            ),

            (Right(fs), idata) => fs.readdirplus(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry, mut entry| {
                    dir_entry.ino = self.convert_inode(idata.fs_idx(), entry.inode)?;
                    entry.inode = dir_entry.ino;
                    add_entry(dir_entry, entry)
                },
            ),
        }
    }

    fn fsyncdir(&self, ctx: Context, inode: VfsInode, datasync: bool, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
        }
    }

    fn releasedir(&self, ctx: Context, inode: VfsInode, flags: u32, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
            (Right(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
        }
    }

    fn access(&self, ctx: Context, inode: VfsInode, mask: u32) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.access(ctx, idata.ino(), mask),
            (Right(fs), idata) => fs.access(ctx, idata.ino(), mask),
        }
    }
}
