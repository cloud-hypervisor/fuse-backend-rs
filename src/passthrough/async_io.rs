// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io;

use async_trait::async_trait;

use super::*;
use crate::abi::linux_abi::{OpenOptions, SetattrValid};
use crate::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, FileSystem,
};
use crate::api::CreateIn;
use crate::async_util::{AsyncDrive, AsyncUtil};

//use crate::passthrough::sync_io::set_creds;

impl<D: AsyncDrive + Sync, S: 'static + BitmapSlice + Send + Sync> BackendFileSystem<D, S>
    for PassthroughFs<D, S>
{
    fn mount(&self) -> io::Result<(Entry, u64)> {
        let entry = self.do_lookup(fuse::ROOT_ID, &CString::new(".").unwrap())?;
        Ok((entry, VFS_MAX_INO))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

impl<D: AsyncDrive, S: BitmapSlice + Send + Sync> PassthroughFs<D, S> {
    async fn async_open_file(
        ctx: &Context,
        dfd: i32,
        pathname: &'_ CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<File> {
        let drive = ctx
            .get_drive::<D>()
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        AsyncUtil::open_at(drive, dfd, pathname, flags, mode)
            .await
            .map(|fd| unsafe { File::from_raw_fd(fd as i32) })
    }

    async fn async_open_proc_file(
        &self,
        ctx: &Context,
        pathname: &CStr,
        flags: i32,
    ) -> io::Result<File> {
        Self::async_open_file(ctx, self.proc.as_raw_fd(), pathname, flags, 0).await
    }

    async fn async_open_inode(
        &self,
        ctx: &Context,
        inode: Inode,
        mut flags: i32,
    ) -> io::Result<File> {
        let data = self.inode_map.get(inode)?;
        let file = data.get_file(&self.mount_fds)?;
        let pathname = CString::new(format!("self/fd/{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // When writeback caching is enabled, the kernel may send read requests even if the
        // userspace program opened the file write-only. So we need to ensure that we have opened
        // the file for reading as well as writing.
        let writeback = self.writeback.load(Ordering::Relaxed);
        if writeback && flags & libc::O_ACCMODE == libc::O_WRONLY {
            flags &= !libc::O_ACCMODE;
            flags |= libc::O_RDWR;
        }

        // When writeback caching is enabled the kernel is responsible for handling `O_APPEND`.
        // However, this breaks atomicity as the file may have changed on disk, invalidating the
        // cached copy of the data in the kernel and the offset that the kernel thinks is the end of
        // the file. Just allow this for now as it is the user's responsibility to enable writeback
        // caching only for directories that are not shared. It also means that we need to clear the
        // `O_APPEND` flag.
        if writeback && flags & libc::O_APPEND != 0 {
            flags &= !libc::O_APPEND;
        }

        // We don't really check `flags` because if the kernel can't handle poorly specified flags
        // then we have much bigger problems. Also, clear the `O_NOFOLLOW` flag if it is set since
        // we need to follow the `/proc/self/fd` symlink to get the file.
        self.async_open_proc_file(
            ctx,
            &pathname,
            (flags | libc::O_CLOEXEC) & (!libc::O_NOFOLLOW),
        )
        .await
    }

    async fn async_do_open(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
        _fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions)> {
        // FIXME: handle FOPEN_IN_KILL_SUIDGID properly
        let file = self.async_open_inode(ctx, inode, flags as i32).await?;
        let data = HandleData::new(inode, file);
        let handle = self.next_handle.fetch_add(1, Ordering::Relaxed);

        self.handle_map.insert(handle, data);

        let mut opts = OpenOptions::empty();
        match self.cfg.cache_policy {
            // We only set the direct I/O option on files.
            CachePolicy::Never => opts.set(
                OpenOptions::DIRECT_IO,
                flags & (libc::O_DIRECTORY as u32) == 0,
            ),
            CachePolicy::Always => opts |= OpenOptions::KEEP_CACHE,
            _ => {}
        };

        Ok((Some(handle), opts))
    }

    async fn async_do_getattr(&self, inode: Inode) -> io::Result<(libc::stat64, Duration)> {
        let data = self.inode_map.get(inode).map_err(|e| {
            error!("fuse: do_getattr ino {} Not find err {:?}", inode, e);
            e
        })?;
        let file = data.get_file(&self.mount_fds)?;

        let st = Self::async_stat(file.into_ref(), None).await.map_err(|e| {
            error!(
                "fuse: do_getattr stat failed ino {} fd: {:?} err {:?}",
                inode,
                file.as_raw_fd(),
                e
            );
            e
        })?;

        Ok((st, self.cfg.attr_timeout))
    }

    async fn async_stat(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<libc::stat64> {
        // Safe because this is a constant value and a valid C string.
        let pathname =
            path.unwrap_or_else(|| unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) });
        let mut st = MaybeUninit::<libc::stat64>::zeroed();

        // TODO:
        // Safe because the kernel will only write data in `st` and we check the return value.
        let res = unsafe {
            libc::fstatat64(
                dir.as_raw_fd(),
                pathname.as_ptr(),
                st.as_mut_ptr(),
                libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
            )
        };
        if res >= 0 {
            // Safe because the kernel guarantees that the struct is now fully initialized.
            Ok(unsafe { st.assume_init() })
        } else {
            Err(io::Error::last_os_error())
        }
    }

    async fn async_get_data(
        &self,
        ctx: &Context,
        handle: Handle,
        inode: Inode,
        flags: libc::c_int,
    ) -> io::Result<Arc<HandleData>> {
        let no_open = self.no_open.load(Ordering::Relaxed);
        if !no_open {
            self.handle_map.get(handle, inode)
        } else {
            let file = self.async_open_inode(ctx, inode, flags as i32).await?;
            Ok(Arc::new(HandleData::new(inode, file)))
        }
    }
}

#[async_trait]
#[allow(unused_variables)]
impl<D: AsyncDrive + Sync, S: BitmapSlice + Send + Sync> AsyncFileSystem<D, S>
    for PassthroughFs<D, S>
{
    async fn async_lookup(
        &self,
        ctx: Context,
        parent: <Self as FileSystem<S>>::Inode,
        name: &CStr,
    ) -> io::Result<Entry> {
        let data = self.inode_map.get(parent)?;
        let file = data.get_file(&self.mount_fds)?;
        let f = Self::async_open_file(
            &ctx,
            file.as_raw_fd(),
            name,
            libc::O_PATH | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0,
        )
        .await?;
        let st = Self::async_stat(&f, None).await?;
        let altkey = InodeAltKey::ids_from_stat(&st);

        let mut found = None;
        'search: loop {
            match self.inode_map.get_alt(&altkey) {
                // No existing entry found
                None => break 'search,
                Some(data) => {
                    let curr = data.refcount.load(Ordering::Acquire);
                    // forgot_one() has just destroyed the entry, retry...
                    if curr == 0 {
                        continue 'search;
                    }

                    // Saturating add to avoid integer overflow, it's not realistic to saturate u64.
                    let new = curr.saturating_add(1);

                    // Synchronizes with the forgot_one()
                    if data
                        .refcount
                        .compare_exchange(curr, new, Ordering::AcqRel, Ordering::Acquire)
                        .is_ok()
                    {
                        found = Some(data.inode);
                        break;
                    }
                }
            }
        }

        let inode = if let Some(v) = found {
            v
        } else {
            // There is a possible race here where 2 threads end up adding the same file
            // into the inode list.  However, since each of those will get a unique Inode
            // value and unique file descriptors this shouldn't be that much of a problem.
            let inode = self.next_inode.fetch_add(1, Ordering::Relaxed);
            if inode > VFS_MAX_INO {
                error!("fuse: max inode number reached: {}", VFS_MAX_INO);
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("max inode number reached: {}", VFS_MAX_INO),
                ));
            }
            trace!("fuse: do_lookup new inode {} altkey {:?}", inode, altkey);
            self.inode_map.insert(
                inode,
                altkey,
                InodeData::new(inode, FileOrHandle::File(f), 1, altkey),
            );

            inode
        };

        Ok(Entry {
            inode,
            generation: 0,
            attr: st,
            attr_timeout: self.cfg.attr_timeout,
            entry_timeout: self.cfg.entry_timeout,
        })
    }

    async fn async_getattr(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        handle: Option<<Self as FileSystem<S>>::Handle>,
    ) -> io::Result<(libc::stat64, Duration)> {
        self.async_do_getattr(inode).await
    }

    async fn async_setattr(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        attr: libc::stat64,
        handle: Option<<Self as FileSystem<S>>::Handle>,
        valid: SetattrValid,
    ) -> io::Result<(libc::stat64, Duration)> {
        let inode_data = self.inode_map.get(inode)?;

        enum Data {
            Handle(Arc<HandleData>, RawFd),
            ProcPath(CString),
        }

        let data = if self.no_open.load(Ordering::Relaxed) {
            let file = inode_data.get_file(&self.mount_fds)?;
            let pathname = CString::new(format!("self/fd/{}", file.as_raw_fd()))
                .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
            Data::ProcPath(pathname)
        } else {
            // If we have a handle then use it otherwise get a new fd from the inode.
            if let Some(handle) = handle {
                let hd = self.handle_map.get(handle, inode)?;
                let fd = hd.get_handle_raw_fd();
                Data::Handle(hd, fd)
            } else {
                let file = inode_data.get_file(&self.mount_fds)?;
                let pathname = CString::new(format!("self/fd/{}", file.as_raw_fd()))
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
                Data::ProcPath(pathname)
            }
        };

        if valid.contains(SetattrValid::MODE) {
            // Safe because this doesn't modify any memory and we check the return value.
            let res = unsafe {
                match data {
                    Data::Handle(_, fd) => libc::fchmod(fd, attr.st_mode),
                    Data::ProcPath(ref p) => {
                        libc::fchmodat(self.proc.as_raw_fd(), p.as_ptr(), attr.st_mode, 0)
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
                ::std::u32::MAX
            };
            let gid = if valid.contains(SetattrValid::GID) {
                attr.st_gid
            } else {
                // Cannot use -1 here because these are unsigned values.
                ::std::u32::MAX
            };

            // Safe because this is a constant value and a valid C string.
            let empty = unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) };
            let file = inode_data.get_file(&self.mount_fds)?;

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
            // Safe because this doesn't modify any memory and we check the return value.
            let res = match data {
                Data::Handle(_, fd) => unsafe { libc::ftruncate(fd, attr.st_size) },
                _ => {
                    // There is no `ftruncateat` so we need to get a new fd and truncate it.
                    let f = self
                        .async_open_inode(&ctx, inode, libc::O_NONBLOCK | libc::O_RDWR)
                        .await?;
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
                Data::Handle(_, fd) => unsafe { libc::futimens(fd, tvs.as_ptr()) },
                Data::ProcPath(ref p) => unsafe {
                    libc::utimensat(self.proc.as_raw_fd(), p.as_ptr(), tvs.as_ptr(), 0)
                },
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
        }

        self.async_do_getattr(inode).await
    }

    async fn async_open(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<<Self as FileSystem<S>>::Handle>, OpenOptions)> {
        if self.no_open.load(Ordering::Relaxed) {
            info!("fuse: open is not supported.");
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        } else {
            self.async_do_open(&ctx, inode, flags, fuse_flags).await
        }
    }

    async fn async_create(
        &self,
        ctx: Context,
        parent: <Self as FileSystem<S>>::Inode,
        name: &CStr,
        args: CreateIn,
    ) -> io::Result<(Entry, Option<<Self as FileSystem<S>>::Handle>, OpenOptions)> {
        unimplemented!()
        // TODO: implement
        // let (_uid, _gid) = set_creds(ctx.uid, ctx.gid)?;
        // let data = self.inode_map.get(parent)?;

        // // Safe because this doesn't modify any memory and we check the return value. We don't
        // // really check `flags` because if the kernel can't handle poorly specified flags then we
        // // have much bigger problems.
        // let file = Self::async_open_file(
        //     &ctx,
        //     data.get_raw_fd(),
        //     name,
        //     flags as i32 | libc::O_CREAT | libc::O_CLOEXEC | libc::O_NOFOLLOW,
        //     mode & !(umask & 0o777),
        // )
        // .await?;

        // let entry = self.async_lookup(ctx, parent, name).await?;

        // let ret_handle = if !self.no_open.load(Ordering::Relaxed) {
        //     let handle = self.next_handle.fetch_add(1, Ordering::Relaxed);
        //     let data = HandleData::new(entry.inode, file);

        //     self.handle_map.insert(handle, data);
        //     Some(handle)
        // } else {
        //     None
        // };

        // let mut opts = OpenOptions::empty();
        // match self.cfg.cache_policy {
        //     CachePolicy::Never => opts |= OpenOptions::DIRECT_IO,
        //     CachePolicy::Always => opts |= OpenOptions::KEEP_CACHE,
        //     _ => {}
        // };

        // Ok((entry, ret_handle, opts))
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_read(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        handle: <Self as FileSystem<S>>::Handle,
        w: &mut (dyn AsyncZeroCopyWriter<D, S> + Send),
        size: u32,
        offset: u64,
        _lock_owner: Option<u64>,
        _flags: u32,
    ) -> io::Result<usize> {
        let data = self
            .async_get_data(&ctx, handle, inode, libc::O_RDONLY)
            .await?;
        let drive = ctx
            .get_drive::<D>()
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        w.async_write_from(drive, data.get_handle_raw_fd(), size as usize, offset)
            .await
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_write(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        handle: <Self as FileSystem<S>>::Handle,
        r: &mut (dyn AsyncZeroCopyReader<D, S> + Send),
        size: u32,
        offset: u64,
        _lock_owner: Option<u64>,
        _delayed_write: bool,
        _flags: u32,
        _fuse_flags: u32,
    ) -> io::Result<usize> {
        let data = self
            .async_get_data(&ctx, handle, inode, libc::O_RDWR)
            .await?;
        let drive = ctx
            .get_drive::<D>()
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        // FIXME: handle WRITE_KILL_PRIV properly
        r.async_read_to(drive, data.get_handle_raw_fd(), size as usize, offset)
            .await
    }

    async fn async_fsync(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        datasync: bool,
        handle: <Self as FileSystem<S>>::Handle,
    ) -> io::Result<()> {
        let data = self
            .async_get_data(&ctx, handle, inode, libc::O_RDONLY)
            .await?;

        let drive = ctx
            .get_drive::<D>()
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        AsyncUtil::fsync(drive, data.get_handle_raw_fd(), datasync).await
    }

    async fn async_fallocate(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        handle: <Self as FileSystem<S>>::Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> io::Result<()> {
        // Let the Arc<HandleData> in scope, otherwise fd may get invalid.
        let data = self
            .async_get_data(&ctx, handle, inode, libc::O_RDWR)
            .await?;

        let drive = ctx
            .get_drive::<D>()
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        AsyncUtil::fallocate(drive, data.get_handle_raw_fd(), offset, length, mode).await
    }

    async fn async_fsyncdir(
        &self,
        ctx: Context,
        inode: <Self as FileSystem<S>>::Inode,
        datasync: bool,
        handle: <Self as FileSystem<S>>::Handle,
    ) -> io::Result<()> {
        self.async_fsync(ctx, inode, datasync, handle).await
    }
}
