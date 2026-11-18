// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io;

use async_trait::async_trait;

use super::sync_io::copy_file_range_error;
use super::*;

#[async_trait]
impl AsyncFileSystem for Vfs {
    async fn async_lookup(
        &self,
        ctx: &Context,
        parent: <Self as FileSystem>::Inode,
        name: &CStr,
    ) -> Result<Entry> {
        // Don't use is_safe_path_component(), allow "." and ".." for NFS export support
        if name.to_bytes_with_nul().contains(&SLASH_ASCII) {
            return Err(io::Error::from_raw_os_error(libc::EINVAL));
        }

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => self.lookup_pseudo(fs, idata, ctx, name),
            (Right(fs), idata) => {
                // parent is in an underlying rootfs
                let entry = fs.async_lookup(ctx, idata.ino(), name).await?;
                // lookup success, hash it to a real fuse inode
                self.convert_backend_entry(idata, entry)
            }
        }
    }

    async fn async_getattr(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: Option<<Self as FileSystem>::Handle>,
    ) -> Result<(stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getattr(ctx, idata.ino(), handle),
            (Right(fs), idata) => fs
                .async_getattr(ctx, idata.ino(), handle)
                .await
                .map(|(attr, duration)| (self.convert_attr(idata, attr), duration)),
        }
    }

    // Like `statx()`.
    async fn async_statx(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: Option<<Self as FileSystem>::Handle>,
        flags: u32,
        mask: u32,
    ) -> Result<(Statx, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs
                .getattr(ctx, idata.ino(), handle)
                .map(|(attr, duration)| (attr.into(), duration)),
            (Right(fs), idata) => match fs.async_statx(ctx, idata.ino(), handle, flags, mask).await
            {
                Err(e) if e.raw_os_error() == Some(libc::ENOSYS) => fs
                    .async_getattr(ctx, idata.ino(), handle)
                    .await
                    .map(|(attr, duration)| (self.convert_attr(idata, attr).into(), duration)),
                res => res.map(|(sx, duration)| (self.convert_statx(idata, sx), duration)),
            },
        }
    }

    async fn async_setattr(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        attr: stat64,
        handle: Option<<Self as FileSystem>::Handle>,
        valid: SetattrValid,
    ) -> Result<(stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setattr(ctx, idata.ino(), attr, handle, valid),
            (Right(fs), idata) => {
                let mut attr = attr;
                self.remap_attr_id(idata.fs_idx(), false, &mut attr);
                fs.async_setattr(ctx, idata.ino(), attr, handle, valid)
                    .await
                    .map(|(attr, duration)| (self.convert_attr(idata, attr), duration))
            }
        }
    }

    async fn async_open(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> Result<(
        Option<<Self as FileSystem>::Handle>,
        OpenOptions,
        Option<u32>,
    )> {
        if self.opts.load().no_open {
            return Err(Error::from_raw_os_error(libc::ENOSYS));
        }
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.open(ctx, idata.ino(), flags, fuse_flags),
            (Right(fs), idata) => fs.async_open(ctx, idata.ino(), flags, fuse_flags).await,
        }
    }

    async fn async_create(
        &self,
        ctx: &Context,
        parent: <Self as FileSystem>::Inode,
        name: &CStr,
        args: CreateIn,
    ) -> Result<(
        Entry,
        Option<<Self as FileSystem>::Handle>,
        OpenOptions,
        Option<u32>,
    )> {
        validate_path_component(name)?;

        let ctx = self.ctx_for_mount(ctx, parent.fs_idx());

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.create(&ctx, idata.ino(), name, args),
            (Right(fs), idata) => fs
                .async_create(&ctx, idata.ino(), name, args)
                .await
                .and_then(|(a, b, c, d)| {
                    self.convert_backend_entry(idata, a).map(|a| (a, b, c, d))
                }),
        }
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_read(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        w: &mut (dyn AsyncZeroCopyWriter + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> Result<usize> {
        match self.get_real_rootfs(inode)? {
            (Left(_fs), _idata) => Err(io::Error::from_raw_os_error(libc::ENOSYS)),
            (Right(fs), idata) => {
                fs.async_read(ctx, idata.ino(), handle, w, size, offset, lock_owner, flags)
                    .await
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_write(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        r: &mut (dyn AsyncZeroCopyReader + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> Result<usize> {
        match self.get_real_rootfs(inode)? {
            (Left(_fs), _idata) => Err(io::Error::from_raw_os_error(libc::ENOSYS)),
            (Right(fs), idata) => {
                fs.async_write(
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
                )
                .await
            }
        }
    }

    async fn async_fsync(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        datasync: bool,
        handle: <Self as FileSystem>::Handle,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.async_fsync(ctx, idata.ino(), datasync, handle).await,
        }
    }

    async fn async_fallocate(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fallocate(ctx, idata.ino(), handle, mode, offset, length),
            (Right(fs), idata) => {
                fs.async_fallocate(ctx, idata.ino(), handle, mode, offset, length)
                    .await
            }
        }
    }

    async fn async_opendir(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        flags: u32,
    ) -> Result<(Option<<Self as FileSystem>::Handle>, OpenOptions)> {
        if self.opts.load().no_opendir {
            return Err(Error::from_raw_os_error(libc::ENOSYS));
        }
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.opendir(ctx, idata.ino(), flags),
            (Right(fs), idata) => fs.async_opendir(ctx, idata.ino(), flags).await,
        }
    }

    async fn async_readdir(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        size: u32,
        offset: u64,
        add_entry: &mut (dyn FnMut(DirEntry) -> Result<usize> + Send),
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            // The pseudo fs answers right away.
            (Left(fs), idata) => {
                self.readdir_pseudo(fs, idata, ctx, handle, size, offset, add_entry)
            }
            (Right(fs), idata) => {
                fs.async_readdir(
                    ctx,
                    idata.ino(),
                    handle,
                    size,
                    offset,
                    &mut |mut dir_entry| {
                        dir_entry.ino = self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                        add_entry(dir_entry)
                    },
                )
                .await
            }
        }
    }

    async fn async_readdirplus(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        size: u32,
        offset: u64,
        add_entry: &mut (dyn FnMut(DirEntry, Entry) -> Result<usize> + Send),
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                self.readdirplus_pseudo(fs, idata, ctx, handle, size, offset, add_entry)
            }
            (Right(fs), idata) => {
                fs.async_readdirplus(
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
                )
                .await
            }
        }
    }

    async fn async_fsyncdir(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        datasync: bool,
        handle: <Self as FileSystem>::Handle,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.async_fsyncdir(ctx, idata.ino(), datasync, handle).await,
        }
    }

    async fn async_releasedir(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        flags: u32,
        handle: <Self as FileSystem>::Handle,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
            (Right(fs), idata) => fs.async_releasedir(ctx, idata.ino(), flags, handle).await,
        }
    }

    async fn async_readlink(&self, ctx: &Context, inode: VfsInode) -> Result<Vec<u8>> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.readlink(ctx, idata.ino()),
            (Right(fs), idata) => fs.async_readlink(ctx, idata.ino()).await,
        }
    }

    async fn async_symlink(
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
                .async_symlink(&ctx, linkname, idata.ino(), name)
                .await
                .and_then(|e| self.convert_backend_entry(idata, e)),
        }
    }

    async fn async_mknod(
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
                .async_mknod(&ctx, idata.ino(), name, mode, rdev, umask)
                .await
                .and_then(|e| self.convert_backend_entry(idata, e)),
        }
    }

    async fn async_mkdir(
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
                .async_mkdir(&ctx, idata.ino(), name, mode, umask)
                .await
                .and_then(|e| self.convert_backend_entry(idata, e)),
        }
    }

    async fn async_unlink(&self, ctx: &Context, parent: VfsInode, name: &CStr) -> Result<()> {
        validate_path_component(name)?;

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.unlink(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.async_unlink(ctx, idata.ino(), name).await,
        }
    }

    async fn async_rmdir(&self, ctx: &Context, parent: VfsInode, name: &CStr) -> Result<()> {
        validate_path_component(name)?;

        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.async_rmdir(ctx, idata.ino(), name).await,
        }
    }

    async fn async_rename(
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
            Right(fs) => {
                fs.async_rename(
                    ctx,
                    idata_old.ino(),
                    oldname,
                    idata_new.ino(),
                    newname,
                    flags,
                )
                .await
            }
        }
    }

    async fn async_link(
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
                .async_link(ctx, idata_old.ino(), idata_new.ino(), newname)
                .await
                .and_then(|e| self.convert_backend_entry(idata_new, e)),
        }
    }

    async fn async_statfs(&self, ctx: &Context, inode: VfsInode) -> Result<statvfs64> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.statfs(ctx, idata.ino()),
            (Right(fs), idata) => fs.async_statfs(ctx, idata.ino()).await,
        }
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_release(
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
            (Right(fs), idata) => {
                fs.async_release(
                    ctx,
                    idata.ino(),
                    flags,
                    handle,
                    flush,
                    flock_release,
                    lock_owner,
                )
                .await
            }
        }
    }

    async fn async_setxattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        name: &CStr,
        value: &[u8],
        flags: u32,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setxattr(ctx, idata.ino(), name, value, flags),
            (Right(fs), idata) => {
                fs.async_setxattr(ctx, idata.ino(), name, value, flags)
                    .await
            }
        }
    }

    async fn async_getxattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        name: &CStr,
        size: u32,
    ) -> Result<GetxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
            (Right(fs), idata) => fs.async_getxattr(ctx, idata.ino(), name, size).await,
        }
    }

    async fn async_listxattr(
        &self,
        ctx: &Context,
        inode: VfsInode,
        size: u32,
    ) -> Result<ListxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
            (Right(fs), idata) => fs.async_listxattr(ctx, idata.ino(), size).await,
        }
    }

    async fn async_removexattr(&self, ctx: &Context, inode: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.async_removexattr(ctx, idata.ino(), name).await,
        }
    }

    async fn async_flush(
        &self,
        ctx: &Context,
        inode: VfsInode,
        handle: u64,
        lock_owner: u64,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
            (Right(fs), idata) => fs.async_flush(ctx, idata.ino(), handle, lock_owner).await,
        }
    }

    async fn async_access(&self, ctx: &Context, inode: VfsInode, mask: u32) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.access(ctx, idata.ino(), mask),
            (Right(fs), idata) => fs.async_access(ctx, idata.ino(), mask).await,
        }
    }

    // Like `copy_file_range()`.
    async fn async_copy_file_range(
        &self,
        ctx: &Context,
        inode_in: VfsInode,
        fh_in: u64,
        offset_in: u64,
        inode_out: VfsInode,
        fh_out: u64,
        offset_out: u64,
        len: u64,
        flags: u64,
    ) -> Result<u32> {
        let (fs, idata_in, idata_out) = self.copy_file_range_fs(inode_in, inode_out)?;
        fs.async_copy_file_range(
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
        .await
        .map_err(copy_file_range_error)
    }
}

#[cfg(test)]
mod tests {
    use async_trait::async_trait;
    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::buffer::{Reader, Writer};
    use fuse_backend_core::file_traits::FileReadWriteVolatile;

    use super::super::tests::{mount_statx_backends, FakeFileSystemOne};
    use super::*;
    use crate::Vfs;

    use std::any::Any;
    use std::ffi::CString;

    #[tokio::test]
    async fn test_vfs_async_lookup() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs = FakeFileSystemOne {};
        let ctx = Context {
            uid: 0,
            gid: 0,
            pid: 0,
            supp_gid: None,
            ..Default::default()
        };

        assert!(vfs.mount(Box::new(fs), "/x/y").is_ok());

        let handle = tokio::spawn(async move {
            // Lookup inode on pseudo file system.
            let name = CString::new("x").unwrap();
            let future = vfs.async_lookup(&ctx, ROOT_ID.into(), name.as_c_str());
            let entry1 = future.await.unwrap();
            assert_eq!(entry1.inode, 0x2);

            // Lookup inode on mounted file system.
            let entry2 = vfs
                .async_lookup(
                    &ctx,
                    entry1.inode.into(),
                    CString::new("y").unwrap().as_c_str(),
                )
                .await
                .unwrap();
            assert_eq!(entry2.inode, 0x100_0000_0000_0001);

            // lookup for negative result.
            let entry3 = vfs
                .async_lookup(
                    &ctx,
                    entry2.inode.into(),
                    CString::new("z").unwrap().as_c_str(),
                )
                .await
                .unwrap();
            assert_eq!(entry3.inode, 0);
        });
        handle.await.unwrap();
    }

    const DIR_HANDLE: u64 = 7;

    fn check_dir_handle(handle: u64) -> Result<()> {
        if handle == DIR_HANDLE {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(libc::EBADF))
        }
    }

    /// A backend whose root directory, inode 1, holds a file with inode 5. Only the async
    /// handlers answer, after they yield to the runtime once.
    struct AsyncDirFs;

    impl FileSystem for AsyncDirFs {
        type Inode = u64;
        type Handle = u64;
    }

    #[async_trait]
    impl AsyncFileSystem for AsyncDirFs {
        async fn async_opendir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
        ) -> Result<(Option<u64>, OpenOptions)> {
            tokio::task::yield_now().await;
            Ok((Some(DIR_HANDLE), OpenOptions::empty()))
        }

        async fn async_readdir(
            &self,
            _ctx: &Context,
            _inode: u64,
            handle: u64,
            _size: u32,
            offset: u64,
            add_entry: &mut (dyn FnMut(DirEntry) -> Result<usize> + Send),
        ) -> Result<()> {
            tokio::task::yield_now().await;
            check_dir_handle(handle)?;
            if offset == 0 {
                add_entry(DirEntry {
                    ino: 5,
                    offset: 1,
                    type_: libc::DT_REG as u32,
                    name: b"file",
                })?;
            }
            Ok(())
        }

        async fn async_readdirplus(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            size: u32,
            offset: u64,
            add_entry: &mut (dyn FnMut(DirEntry, Entry) -> Result<usize> + Send),
        ) -> Result<()> {
            self.async_readdir(ctx, inode, handle, size, offset, &mut |dir_entry| {
                let mut entry = Entry {
                    inode: dir_entry.ino,
                    ..Default::default()
                };
                entry.attr.st_ino = dir_entry.ino;
                add_entry(dir_entry, entry)
            })
            .await
        }

        async fn async_releasedir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
        ) -> Result<()> {
            tokio::task::yield_now().await;
            check_dir_handle(handle)
        }

        async fn async_readlink(&self, _ctx: &Context, _inode: u64) -> Result<Vec<u8>> {
            tokio::task::yield_now().await;
            Ok(b"target".to_vec())
        }

        async fn async_mkdir(
            &self,
            _ctx: &Context,
            _parent: u64,
            name: &CStr,
            _mode: u32,
            _umask: u32,
        ) -> Result<Entry> {
            tokio::task::yield_now().await;
            match name.to_bytes() {
                b"dir" => Ok(Entry {
                    inode: 6,
                    ..Default::default()
                }),
                _ => Err(io::Error::from_raw_os_error(libc::EEXIST)),
            }
        }

        async fn async_rename(
            &self,
            _ctx: &Context,
            _olddir: u64,
            _oldname: &CStr,
            _newdir: u64,
            _newname: &CStr,
            _flags: u32,
        ) -> Result<()> {
            tokio::task::yield_now().await;
            Ok(())
        }

        async fn async_copy_file_range(
            &self,
            _ctx: &Context,
            _inode_in: u64,
            _fh_in: u64,
            _offset_in: u64,
            _inode_out: u64,
            _fh_out: u64,
            _offset_out: u64,
            len: u64,
            _flags: u64,
        ) -> Result<u32> {
            tokio::task::yield_now().await;
            Ok(len as u32)
        }
    }

    impl BackendFileSystem for AsyncDirFs {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    ..Default::default()
                },
                0,
            ))
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    /// The VFS inode of the root of the first mount.
    const MOUNT_ROOT: u64 = 0x100_0000_0000_0001;
    /// The VFS inode of the file in an `AsyncDirFs` that is the first mount.
    const MOUNT_FILE: u64 = 0x100_0000_0000_0005;

    /// Lists the directory `inode` with READDIR, as the name and inode of each entry. It uses
    /// the handle that `AsyncDirFs` opens, which the pseudo fs ignores.
    async fn list(vfs: &Vfs, inode: u64) -> Vec<(Vec<u8>, u64)> {
        let mut names = Vec::new();
        vfs.async_readdir(
            &Context::default(),
            inode.into(),
            DIR_HANDLE,
            4096,
            0,
            &mut |dir_entry| {
                names.push((dir_entry.name.to_vec(), dir_entry.ino));
                Ok(1)
            },
        )
        .await
        .unwrap();
        names
    }

    /// Like `list()` with READDIRPLUS, as the inode of each entry, the inode and `st_ino` of
    /// its `Entry`, and its owner.
    async fn list_plus(vfs: &Vfs, inode: u64) -> Vec<(u64, u64, u64, u32)> {
        let mut inodes = Vec::new();
        vfs.async_readdirplus(
            &Context::default(),
            inode.into(),
            DIR_HANDLE,
            4096,
            0,
            &mut |dir_entry, entry| {
                let attr = entry.attr;
                inodes.push((dir_entry.ino, entry.inode, attr.st_ino, attr.st_uid));
                Ok(1)
            },
        )
        .await
        .unwrap();
        inodes
    }

    #[tokio::test]
    async fn test_vfs_async_statx() {
        let vfs = Vfs::new(VfsOptions::default());
        let ctx = Context::new();
        let (one, two) = mount_statx_backends(&vfs);
        let mask = STATX_BASIC_STATS | STATX_BTIME;

        let (sx, _) = vfs.async_statx(&ctx, one, None, 0, mask).await.unwrap();
        assert_eq!((sx.mask, sx.ino), (STATX_BASIC_STATS, one.into()));
        let (sx, _) = vfs.async_statx(&ctx, two, None, 0, mask).await.unwrap();
        assert_eq!((sx.mask, sx.ino), (mask, two.into()));
        assert_eq!((sx.uid, sx.btime.tv_sec), (1000, 42));
    }

    #[tokio::test]
    async fn test_vfs_async_readdir_pseudo() {
        let vfs = Vfs::new(VfsOptions::default());
        vfs.mount(Box::new(FakeFileSystemOne {}), "/x/y").unwrap();

        // Spawning checks that the futures, which hold add_entry, are Send.
        let handle = tokio::spawn(async move {
            assert_eq!(list(&vfs, ROOT_ID).await, [(b"x".to_vec(), 2)]);
            // The mountpoint y lists as the root of the mounted file system.
            assert_eq!(list(&vfs, 2).await, [(b"y".to_vec(), MOUNT_ROOT)]);
            let root = MOUNT_ROOT;
            assert_eq!(list_plus(&vfs, 2).await, [(root, root, root, 0)]);
        });
        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_vfs_async_readdir_backend() {
        let vfs = Vfs::new(VfsOptions::default());
        // Map the backend's uid 0 to 1000.
        vfs.mount_with_id_mapping(Box::new(AsyncDirFs), "/x", Some((0, 1000, 1)))
            .unwrap();
        let ctx = Context::default();
        let file = MOUNT_FILE;

        let handle = tokio::spawn(async move {
            assert_eq!(list(&vfs, MOUNT_ROOT).await, [(b"file".to_vec(), file)]);
            assert_eq!(
                list_plus(&vfs, MOUNT_ROOT).await,
                [(file, file, file, 1000)]
            );
            vfs.async_releasedir(&ctx, MOUNT_ROOT.into(), 0, DIR_HANDLE)
                .await
                .unwrap();
        });
        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_vfs_async_opendir() {
        let ctx = Context::default();

        // By default Vfs answers OPENDIR with ENOSYS, so the kernel stops sending it.
        let vfs = Vfs::new(VfsOptions::default());
        vfs.mount(Box::new(AsyncDirFs), "/x").unwrap();
        let err = vfs
            .async_opendir(&ctx, MOUNT_ROOT.into(), 0)
            .await
            .unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ENOSYS));

        let vfs = Vfs::new(VfsOptions {
            no_opendir: false,
            ..Default::default()
        });
        vfs.mount(Box::new(AsyncDirFs), "/x").unwrap();
        let (handle, _) = vfs.async_opendir(&ctx, ROOT_ID.into(), 0).await.unwrap();
        assert_eq!(handle, None);
        let (handle, _) = vfs.async_opendir(&ctx, MOUNT_ROOT.into(), 0).await.unwrap();
        assert_eq!(handle, Some(DIR_HANDLE));
    }

    #[tokio::test]
    async fn test_vfs_async_node_requests() {
        let vfs = Vfs::new(VfsOptions::default());
        vfs.mount(Box::new(AsyncDirFs), "/x").unwrap();
        let ctx = Context::default();
        let name = |s: &str| CString::new(s).unwrap();

        let handle = tokio::spawn(async move {
            let entry = vfs
                .async_mkdir(&ctx, MOUNT_ROOT.into(), &name("dir"), 0o755, 0)
                .await
                .unwrap();
            assert_eq!(entry.inode, 0x100_0000_0000_0006);
            let err = vfs
                .async_mkdir(&ctx, MOUNT_ROOT.into(), &name("a/b"), 0o755, 0)
                .await
                .unwrap_err();
            assert_eq!(err.raw_os_error(), Some(libc::EINVAL));

            let target = vfs.async_readlink(&ctx, MOUNT_FILE.into()).await;
            assert_eq!(target.unwrap(), b"target");

            let (a, b) = (name("a"), name("b"));
            vfs.async_rename(&ctx, MOUNT_ROOT.into(), &a, MOUNT_ROOT.into(), &b, 0)
                .await
                .unwrap();
            // A rename can't leave its file system.
            let err = vfs
                .async_rename(&ctx, MOUNT_ROOT.into(), &a, ROOT_ID.into(), &b, 0)
                .await
                .unwrap_err();
            assert_eq!(err.raw_os_error(), Some(libc::EINVAL));
        });
        handle.await.unwrap();
    }

    #[tokio::test]
    async fn test_vfs_async_xattr_name_with_slash() {
        fn errno<T>(res: Result<T>) -> Option<i32> {
            res.err().and_then(|e| e.raw_os_error())
        }

        let vfs = Vfs::new(VfsOptions::default());
        vfs.mount(Box::new(FakeFileSystemOne {}), "/x").unwrap();
        let ctx = Context::new();
        let x = CString::new("x").unwrap();
        let x = vfs.async_lookup(&ctx, ROOT_ID.into(), &x).await;
        let inode = x.unwrap().inode.into();

        // Linux allows '/' in xattr names, so the requests reach the file system, whose
        // default handlers answer ENOSYS.
        let name = CString::new("user.a/b").unwrap();
        let set = vfs.async_setxattr(&ctx, inode, &name, b"v", 0).await;
        let get = vfs.async_getxattr(&ctx, inode, &name, 0).await;
        let remove = vfs.async_removexattr(&ctx, inode, &name).await;
        let enosys = Some(libc::ENOSYS);
        assert_eq!(errno(set), enosys);
        assert_eq!(errno(get), enosys);
        assert_eq!(errno(remove), enosys);
    }

    #[tokio::test]
    async fn test_vfs_async_copy_file_range() {
        use super::super::sync_io::{COPY_CROSS_MOUNT, COPY_UNSUPPORTED};

        let vfs = Vfs::new(VfsOptions::default());
        vfs.mount(Box::new(AsyncDirFs), "/x").unwrap();
        // FakeFileSystemOne answers ENOSYS.
        vfs.mount(Box::new(FakeFileSystemOne {}), "/y").unwrap();
        let other = |ino: u64| 0x200_0000_0000_0000 | ino;
        let ctx = Context::default();
        let copy = |inode_in: u64, inode_out: u64| {
            vfs.async_copy_file_range(&ctx, inode_in.into(), 1, 0, inode_out.into(), 2, 0, 4096, 0)
        };

        // AsyncDirFs answers only with its async handler.
        assert_eq!(copy(MOUNT_FILE, MOUNT_FILE).await.unwrap(), 4096);
        for (inode_in, inode_out, errno) in [
            (other(5), other(6), COPY_UNSUPPORTED),
            (MOUNT_FILE, other(5), COPY_CROSS_MOUNT),
            (ROOT_ID, MOUNT_FILE, libc::EISDIR),
            (MOUNT_FILE, ROOT_ID, libc::EISDIR),
        ] {
            let err = copy(inode_in, inode_out).await.unwrap_err();
            assert_eq!(err.raw_os_error(), Some(errno));
        }
    }

    // Note: the passthrough integration test driving async requests through
    // the Vfs layer down to a real `PassthroughFs` instance lives in the
    // umbrella crate's `tests/driver_tests.rs`, since it depends on a
    // filesystem driver.

    // A `Writer` that only has to exist: `test_vfs_async_invalid_header` feeds a
    // one-byte reader buffer, so `async_handle_message` fails while decoding the
    // in-header and never writes a reply. Every method is therefore unreachable.
    struct NullWriter;

    impl io::Write for NullWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            Ok(buf.len())
        }
        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl Writer for NullWriter {
        fn write_from_at<F: FileReadWriteVolatile>(
            &mut self,
            _src: F,
            count: usize,
            _off: u64,
        ) -> io::Result<usize> {
            Ok(count)
        }

        fn split_at(&mut self, _offset: usize) -> fuse_backend_core::buffer::Result<Self> {
            Ok(NullWriter)
        }

        fn available_bytes(&self) -> usize {
            usize::MAX
        }

        fn bytes_written(&self) -> usize {
            0
        }

        fn commit(&mut self, _other: Option<&Self>) -> io::Result<usize> {
            Ok(0)
        }
    }

    // Relocated from core's `api::server::async_io` unit tests. It exercises the
    // async server entry point rejecting a malformed header, which needs a
    // concrete `FileSystem` to instantiate `Server`; `Vfs` now lives in this
    // crate, so the test follows it here.
    #[tokio::test]
    async fn test_vfs_async_invalid_header() {
        let vfs = Vfs::default();
        let server = Server::new(vfs);
        let mut r_buf = [0u8];
        let r = Reader::<()>::from_slice(&mut r_buf);
        let w = NullWriter;

        let result = unsafe { server.async_handle_message(r, w, None, None).await };
        assert!(result.is_err());
    }
}
