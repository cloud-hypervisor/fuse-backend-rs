// Copyright (C) 2021-2022 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::ffi::CStr;
use std::io;
use std::mem::size_of;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use vm_memory::ByteValued;

use super::sync_io::{
    add_dirent, parse_create_extensions, release_args, split_setxattr_body, XattrReply,
    RENAME2_FLAGS,
};
use crate::abi::fuse_abi::{
    stat64, AccessIn, AttrOut, CopyFileRangeIn, CreateIn, EntryOut, FallocateIn, FlushIn,
    FsOptions, FsyncIn, GetattrIn, GetxattrIn, GetxattrOut, Kstatfs, LinkIn, LseekIn, LseekOut,
    MkdirIn, MknodIn, Opcode, OpenIn, OpenOut, OutHeader, ReadIn, ReleaseIn, Rename2In, RenameIn,
    SetattrIn, SetattrValid, SetxattrIn, WriteIn, WriteOut, FATTR_FH, GETATTR_FH,
    KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO, READ_LOCKOWNER, WRITE_CACHE, WRITE_LOCKOWNER,
};
use crate::api::filesystem::FsCacheReqHandler;
use crate::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, DirEntry, Entry, ZeroCopyReader,
    ZeroCopyWriter,
};
use crate::api::server::{
    decode_version, takes_reply, InitParams, MetricsHook, Server, ServerUtil, SrvContext,
    BUFFER_HEADER_SIZE, MAX_BUFFER_SIZE,
};
use crate::buffer::{Reader, Writer};
use crate::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};
use crate::{bytes_to_cstr, encode_io_error_kind, BitmapSlice, Error, Result};

struct AsyncZcReader<'a, S: BitmapSlice = ()>(Reader<'a, S>);

// The underlying VolatileSlice contains "*mut u8", which is just a pointer to a u8 array.
// Actually we rely on the AsyncExecutor is a single-threaded worker, and we do not really send
// 'Reader' to other threads.
unsafe impl<'a, S: BitmapSlice> Send for AsyncZcReader<'a, S> {}

#[async_trait(?Send)]
impl<'a, S: BitmapSlice> AsyncZeroCopyReader for AsyncZcReader<'a, S> {
    async fn async_read_to(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.async_read_to_at(&*f, count, off).await
    }
}

impl<'a, S: BitmapSlice> ZeroCopyReader for AsyncZcReader<'a, S> {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.read_to_at(f, count, off)
    }
}

impl<'a, S: BitmapSlice> io::Read for AsyncZcReader<'a, S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

struct AsyncZcWriter<W>(W);

// The underlying VolatileSlice contains "*mut u8", which is just a pointer to a u8 array.
// Actually we rely on the AsyncExecutor is a single-threaded worker, and we do not really send
// 'Reader' to other threads.
unsafe impl<W: Writer> Send for AsyncZcWriter<W> {}

#[async_trait(?Send)]
impl<W: Writer> AsyncZeroCopyWriter for AsyncZcWriter<W> {
    async fn async_write_from(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.async_write_from_at(&*f, count, off).await
    }
}

impl<W: Writer> ZeroCopyWriter for AsyncZcWriter<W> {
    fn write_from(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.write_from_at(f, count, off)
    }

    fn available_bytes(&self) -> usize {
        self.0.available_bytes()
    }
}

impl<W: Writer> io::Write for AsyncZcWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

impl<W: Writer> AsyncZcWriter<W> {
    /// Adds a directory entry to a READDIR or READDIRPLUS reply. A closure that calls this
    /// captures the whole writer, so it is `Send` like the writer.
    fn add_dirent(&mut self, max: u32, d: DirEntry, entry: Option<Entry>) -> io::Result<usize> {
        add_dirent(&mut self.0, max, d, entry)
    }
}

impl<F: AsyncFileSystem + Sync> Server<F> {
    /// Main entrance to handle requests from the transport layer.
    ///
    /// It receives Fuse requests from transport layers, parses the request according to Fuse ABI,
    /// invokes filesystem drivers to server the requests, and eventually send back the result to
    /// the transport layer.
    ///
    /// ## Safety
    /// The async io framework borrows underlying buffers from `Reader` and `Writer`, so the caller
    /// must ensure all data buffers managed by the `Reader` and `Writer` are valid until the
    /// `Future` object returned has completed. Other subsystems, such as the transport layer, rely
    /// on the invariant.
    ///
    /// Returns like `handle_message()`.
    pub async unsafe fn async_handle_message<S: BitmapSlice, W: Writer>(
        &self,
        mut r: Reader<'_, S>,
        w: W,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
        hook: Option<&dyn MetricsHook>,
    ) -> Result<usize> {
        let in_header = r.read_obj().map_err(Error::DecodeMessage)?;
        let mut ctx = SrvContext::<F, S, W>::new(in_header, r, w);
        let res = self.async_dispatch(&mut ctx, vu_req, hook).await;
        ctx.reply_on_error(res)
    }

    #[allow(unused_variables)]
    async fn async_dispatch<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
        hook: Option<&dyn MetricsHook>,
    ) -> Result<usize> {
        self.remap_ctx_ids(ctx)?;
        if ctx.in_header.len > (MAX_BUFFER_SIZE + BUFFER_HEADER_SIZE)
            || ctx.w.available_bytes() < size_of::<OutHeader>()
        {
            if !takes_reply(ctx.in_header.opcode) {
                return Err(Error::InvalidMessage(io::Error::from_raw_os_error(
                    libc::EOVERFLOW,
                )));
            }
            return ctx
                .async_reply_error(io::Error::from_raw_os_error(libc::ENOMEM))
                .await;
        }
        let in_header = &ctx.in_header;

        trace!(
            "fuse: new req {:?}: {:?}",
            Opcode::from(in_header.opcode),
            in_header
        );

        if let Some(h) = hook {
            h.collect(in_header);
        }

        let res = match in_header.opcode {
            x if x == Opcode::Lookup as u32 => self.async_lookup(ctx).await,
            x if x == Opcode::Forget as u32 => self.forget(ctx), // No reply.
            x if x == Opcode::Getattr as u32 => self.async_getattr(ctx).await,
            x if x == Opcode::Setattr as u32 => self.async_setattr(ctx).await,
            x if x == Opcode::Readlink as u32 => self.async_readlink(ctx).await,
            x if x == Opcode::Symlink as u32 => self.async_symlink(ctx).await,
            x if x == Opcode::Mknod as u32 => self.async_mknod(ctx).await,
            x if x == Opcode::Mkdir as u32 => self.async_mkdir(ctx).await,
            x if x == Opcode::Unlink as u32 => self.async_unlink(ctx).await,
            x if x == Opcode::Rmdir as u32 => self.async_rmdir(ctx).await,
            x if x == Opcode::Rename as u32 => self.async_rename(ctx).await,
            x if x == Opcode::Link as u32 => self.async_link(ctx).await,
            x if x == Opcode::Open as u32 => self.async_open(ctx).await,
            x if x == Opcode::Read as u32 => self.async_read(ctx).await,
            x if x == Opcode::Write as u32 => self.async_write(ctx).await,
            x if x == Opcode::Statfs as u32 => self.async_statfs(ctx).await,
            x if x == Opcode::Release as u32 => self.async_release(ctx).await,
            x if x == Opcode::Fsync as u32 => self.async_fsync(ctx).await,
            x if x == Opcode::Setxattr as u32 => self.async_setxattr(ctx).await,
            x if x == Opcode::Getxattr as u32 => self.async_getxattr(ctx).await,
            x if x == Opcode::Listxattr as u32 => self.async_listxattr(ctx).await,
            x if x == Opcode::Removexattr as u32 => self.async_removexattr(ctx).await,
            x if x == Opcode::Flush as u32 => self.async_flush(ctx).await,
            x if x == Opcode::Init as u32 => self.init(ctx, |init_params: &InitParams| {
                if let Some(h) = hook {
                    h.on_init_params(init_params);
                }
            }),
            x if x == Opcode::Opendir as u32 => self.async_opendir(ctx).await,
            x if x == Opcode::Readdir as u32 => self.async_do_readdir(ctx, false).await,
            x if x == Opcode::Releasedir as u32 => self.async_releasedir(ctx).await,
            x if x == Opcode::Fsyncdir as u32 => self.async_fsyncdir(ctx).await,
            x if x == Opcode::Getlk as u32 => self.getlk(ctx),
            x if x == Opcode::Setlk as u32 => self.setlk(ctx),
            x if x == Opcode::Setlkw as u32 => self.setlkw(ctx),
            x if x == Opcode::Access as u32 => self.async_access(ctx).await,
            x if x == Opcode::Create as u32 => self.async_create(ctx).await,
            x if x == Opcode::Bmap as u32 => self.bmap(ctx),
            x if x == Opcode::Ioctl as u32 => self.ioctl(ctx),
            x if x == Opcode::Poll as u32 => self.poll(ctx),
            x if x == Opcode::NotifyReply as u32 => self.notify_reply(ctx),
            x if x == Opcode::BatchForget as u32 => self.batch_forget(ctx),
            x if x == Opcode::Fallocate as u32 => self.async_fallocate(ctx).await,
            x if x == Opcode::Readdirplus as u32 => self.async_do_readdir(ctx, true).await,
            x if x == Opcode::Rename2 as u32 => self.async_rename2(ctx).await,
            x if x == Opcode::Lseek as u32 => self.async_lseek(ctx).await,
            x if x == Opcode::CopyFileRange as u32 => self.async_copy_file_range(ctx).await,
            #[cfg(feature = "virtiofs")]
            x if x == Opcode::SetupMapping as u32 => self.setupmapping(ctx, vu_req),
            #[cfg(feature = "virtiofs")]
            x if x == Opcode::RemoveMapping as u32 => self.removemapping(ctx, vu_req),
            // Group reqeusts don't need reply together
            x => match x {
                x if x == Opcode::Interrupt as u32 => {
                    self.interrupt(ctx);
                    Ok(0)
                }
                x if x == Opcode::Destroy as u32 => {
                    self.destroy(ctx);
                    Ok(0)
                }
                _ => {
                    ctx.async_reply_error(io::Error::from_raw_os_error(libc::ENOSYS))
                        .await
                }
            },
        };

        // Pass `None` because current API handler's design does not allow us to catch
        // the `out_header`. Hopefully, we can reach to `out_header` after some
        // refactoring work someday.
        if let Some(h) = hook {
            h.release(None);
        }

        res
    }

    async fn async_lookup<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = Self::parse_name(&buf)?;

        let version = decode_version(self.vers.load(Ordering::Acquire));
        let result = self
            .fs
            .async_lookup(ctx.context(), ctx.nodeid(), name)
            .await;

        match result {
            // before ABI 7.4 inode == 0 was invalid, only ENOENT means negative dentry
            Ok(entry)
                if version.minor < KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO
                    && entry.inode == 0 =>
            {
                ctx.async_reply_error(io::Error::from_raw_os_error(libc::ENOENT))
                    .await
            }
            Ok(entry) => {
                let out = EntryOut::from(entry);
                ctx.async_reply_ok(Some(out), None).await
            }
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_getattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let GetattrIn { flags, fh, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if (flags & GETATTR_FH) != 0 {
            Some(fh.into())
        } else {
            None
        };
        let result = self
            .fs
            .async_getattr(ctx.context(), ctx.nodeid(), handle)
            .await;

        ctx.async_handle_attr_result(result).await
    }

    async fn async_setattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let setattr_in: SetattrIn = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if setattr_in.valid & FATTR_FH != 0 {
            Some(setattr_in.fh.into())
        } else {
            None
        };
        let valid = SetattrValid::from_bits_truncate(setattr_in.valid);
        let st: stat64 = setattr_in.into();
        let result = self
            .fs
            .async_setattr(ctx.context(), ctx.nodeid(), st, handle, valid)
            .await;

        ctx.async_handle_attr_result(result).await
    }

    async fn async_open<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let OpenIn { flags, fuse_flags } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let result = self
            .fs
            .async_open(ctx.context(), ctx.nodeid(), flags, fuse_flags)
            .await;

        match result {
            Ok((handle, opts, passthrough)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    passthrough: passthrough.unwrap_or_default(),
                };

                ctx.async_reply_ok(Some(out), None).await
            }
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_read<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let ReadIn {
            fh,
            offset,
            size,
            read_flags,
            lock_owner,
            flags,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let owner = if read_flags & READ_LOCKOWNER != 0 {
            Some(lock_owner)
        } else {
            None
        };

        // Split the writer into 2 pieces: one for the `OutHeader` and the rest for the data.
        let w2 = match ctx.w.split_at(size_of::<OutHeader>()) {
            Ok(v) => v,
            Err(e) => return Err(Error::FailedToSplitWriter(e)),
        };
        let mut data_writer = AsyncZcWriter(w2);
        let result = self
            .fs
            .async_read(
                ctx.context(),
                ctx.nodeid(),
                fh.into(),
                &mut data_writer,
                size,
                offset,
                owner,
                flags,
            )
            .await;

        match result {
            Ok(count) => ctx.async_reply_with_data(&data_writer.0, count).await,
            Err(e) => ctx.async_reply_error_explicit(e).await,
        }
    }

    async fn async_write<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let WriteIn {
            fh,
            offset,
            size,
            fuse_flags,
            lock_owner,
            flags,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        if size > MAX_BUFFER_SIZE {
            return ctx
                .async_reply_error(io::Error::from_raw_os_error(libc::ENOMEM))
                .await;
        }

        let owner = if fuse_flags & WRITE_LOCKOWNER != 0 {
            Some(lock_owner)
        } else {
            None
        };
        let delayed_write = fuse_flags & WRITE_CACHE != 0;
        let mut data_reader = AsyncZcReader(ctx.take_reader());
        let result = self
            .fs
            .async_write(
                ctx.context(),
                ctx.nodeid(),
                fh.into(),
                &mut data_reader,
                size,
                offset,
                owner,
                delayed_write,
                flags,
                fuse_flags,
            )
            .await;

        match result {
            Ok(count) => {
                let out = WriteOut {
                    size: count as u32,
                    ..Default::default()
                };
                ctx.async_reply_ok(Some(out), None).await
            }
            Err(e) => ctx.async_reply_error_explicit(e).await,
        }
    }

    async fn async_fsync<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;

        match self
            .fs
            .async_fsync(ctx.context(), ctx.nodeid(), datasync, fh.into())
            .await
        {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_opendir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let OpenIn { flags, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let result = self
            .fs
            .async_opendir(ctx.context(), ctx.nodeid(), flags)
            .await;

        match result {
            Ok((handle, opts)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    ..Default::default()
                };

                ctx.async_reply_ok(Some(out), None).await
            }
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_do_readdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        plus: bool,
    ) -> Result<usize> {
        let ReadIn {
            fh, offset, size, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        // The file system's future holds `add_entry`, so the closure has to be `Send`. Wrap
        // the cursor in `AsyncZcWriter`, which is `Send`, as READ does with its data writer.
        let mut cursor = match ctx.dirent_cursor(size)? {
            Some(cursor) => AsyncZcWriter(cursor),
            None => {
                return ctx
                    .async_reply_error(io::Error::from_raw_os_error(libc::ENOMEM))
                    .await
            }
        };
        let result = if plus {
            self.fs
                .async_readdirplus(
                    ctx.context(),
                    ctx.nodeid(),
                    fh.into(),
                    size,
                    offset,
                    &mut |d, e| cursor.add_dirent(size, d, Some(e)),
                )
                .await
        } else {
            self.fs
                .async_readdir(
                    ctx.context(),
                    ctx.nodeid(),
                    fh.into(),
                    size,
                    offset,
                    &mut |d| cursor.add_dirent(size, d, None),
                )
                .await
        };

        match result {
            Ok(()) => {
                ctx.async_reply_with_data(&cursor.0, cursor.0.bytes_written())
                    .await
            }
            Err(e) => ctx.async_reply_error_explicit(e).await,
        }
    }

    async fn async_fsyncdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;
        let result = self
            .fs
            .async_fsyncdir(ctx.context(), ctx.nodeid(), datasync, fh.into())
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_releasedir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let ReleaseIn { fh, flags, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let result = self
            .fs
            .async_releasedir(ctx.context(), ctx.nodeid(), flags, fh.into())
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    /// The name at the start of `buf`.
    fn parse_name(buf: &[u8]) -> Result<&CStr> {
        bytes_to_cstr(buf).inspect_err(|e| debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e))
    }

    /// Sets the supplementary group of `ctx` from the create extensions in `tail`.
    fn set_create_extensions<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        tail: &[u8],
    ) -> Result<()> {
        let options = FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire));
        ctx.context.supp_gid = parse_create_extensions(&options, tail)?;
        Ok(())
    }

    async fn async_readlink<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let result = self.fs.async_readlink(ctx.context(), ctx.nodeid()).await;

        match result {
            Ok(linkname) => ctx.async_reply_ok(None::<u8>, Some(&linkname)).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_symlink<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        // The name and linkname are encoded one after another and separated by a nul character.
        let (name, linkname) = ServerUtil::extract_two_cstrs(&buf)?;
        let tail = &buf[name.to_bytes_with_nul().len() + linkname.to_bytes_with_nul().len()..];
        self.set_create_extensions(ctx, tail)?;

        let result = self
            .fs
            .async_symlink(ctx.context(), linkname, ctx.nodeid(), name)
            .await;

        match result {
            Ok(entry) => ctx.async_reply_ok(Some(EntryOut::from(entry)), None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_mknod<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let MknodIn {
            mode, rdev, umask, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<MknodIn>())?;
        let name = Self::parse_name(&buf)?;
        self.set_create_extensions(ctx, &buf[name.to_bytes_with_nul().len()..])?;

        let result = self
            .fs
            .async_mknod(ctx.context(), ctx.nodeid(), name, mode, rdev, umask)
            .await;

        match result {
            Ok(entry) => ctx.async_reply_ok(Some(EntryOut::from(entry)), None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_mkdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let MkdirIn { mode, umask } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<MkdirIn>())?;
        let name = Self::parse_name(&buf)?;
        self.set_create_extensions(ctx, &buf[name.to_bytes_with_nul().len()..])?;

        let result = self
            .fs
            .async_mkdir(ctx.context(), ctx.nodeid(), name, mode, umask)
            .await;

        match result {
            Ok(entry) => ctx.async_reply_ok(Some(EntryOut::from(entry)), None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_unlink<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = Self::parse_name(&buf)?;

        let result = self
            .fs
            .async_unlink(ctx.context(), ctx.nodeid(), name)
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_rmdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = Self::parse_name(&buf)?;

        let result = self.fs.async_rmdir(ctx.context(), ctx.nodeid(), name).await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_rename<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let RenameIn { newdir, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        self.async_do_rename(ctx, size_of::<RenameIn>(), newdir, 0)
            .await
    }

    async fn async_do_rename<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        msg_size: usize,
        newdir: u64,
        flags: u32,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, msg_size)?;
        let (oldname, newname) = ServerUtil::extract_two_cstrs(&buf)?;

        let result = self
            .fs
            .async_rename(
                ctx.context(),
                ctx.nodeid(),
                oldname,
                newdir.into(),
                newname,
                flags,
            )
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_rename2<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let Rename2In { newdir, flags, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let flags = flags & RENAME2_FLAGS;

        self.async_do_rename(ctx, size_of::<Rename2In>(), newdir, flags)
            .await
    }

    async fn async_link<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let LinkIn { oldnodeid } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<LinkIn>())?;
        let name = Self::parse_name(&buf)?;

        let result = self
            .fs
            .async_link(ctx.context(), oldnodeid.into(), ctx.nodeid(), name)
            .await;

        match result {
            Ok(entry) => ctx.async_reply_ok(Some(EntryOut::from(entry)), None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_statfs<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let result = self.fs.async_statfs(ctx.context(), ctx.nodeid()).await;

        match result {
            Ok(st) => ctx.async_reply_ok(Some(Kstatfs::from(st)), None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_release<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let ReleaseIn {
            fh,
            flags,
            release_flags,
            lock_owner,
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let (flush, flock_release, lock_owner) = release_args(release_flags, lock_owner);

        let result = self
            .fs
            .async_release(
                ctx.context(),
                ctx.nodeid(),
                flags,
                fh.into(),
                flush,
                flock_release,
                lock_owner,
            )
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_setxattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let SetxattrIn { size, flags } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf =
            ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<SetxattrIn>())?;

        let (name, value) = split_setxattr_body(&buf, size)?;
        let name = Self::parse_name(name)?;

        let result = self
            .fs
            .async_setxattr(ctx.context(), ctx.nodeid(), name, value, flags)
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_getxattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let GetxattrIn { size, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let buf =
            ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<GetxattrIn>())?;
        let name = Self::parse_name(&buf)?;

        let result = self
            .fs
            .async_getxattr(ctx.context(), ctx.nodeid(), name, size)
            .await;
        ctx.async_handle_xattr_result(size, result).await
    }

    async fn async_listxattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let GetxattrIn { size, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let result = self
            .fs
            .async_listxattr(ctx.context(), ctx.nodeid(), size)
            .await;
        ctx.async_handle_xattr_result(size, result).await
    }

    async fn async_removexattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = Self::parse_name(&buf)?;

        let result = self
            .fs
            .async_removexattr(ctx.context(), ctx.nodeid(), name)
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_flush<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let FlushIn { fh, lock_owner, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let result = self
            .fs
            .async_flush(ctx.context(), ctx.nodeid(), fh.into(), lock_owner)
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_access<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let AccessIn { mask, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let result = self
            .fs
            .async_access(ctx.context(), ctx.nodeid(), mask)
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_lseek<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let LseekIn {
            fh, offset, whence, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let result = self
            .fs
            .async_lseek(ctx.context(), ctx.nodeid(), fh.into(), offset, whence)
            .await;

        match result {
            Ok(offset) => {
                let out = LseekOut { offset };

                ctx.async_reply_ok(Some(out), None).await
            }
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_copy_file_range<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let CopyFileRangeIn {
            fh_in,
            offset_in,
            nodeid_out,
            fh_out,
            offset_out,
            len,
            flags,
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let result = self
            .fs
            .async_copy_file_range(
                ctx.context(),
                ctx.nodeid(),
                fh_in.into(),
                offset_in,
                nodeid_out.into(),
                fh_out.into(),
                offset_out,
                len,
                flags,
            )
            .await;

        match result {
            Ok(count) => {
                let out = WriteOut {
                    size: count,
                    ..Default::default()
                };

                ctx.async_reply_ok(Some(out), None).await
            }
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_create<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let args: CreateIn = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<CreateIn>())?;
        let name = Self::parse_name(&buf)?;
        self.set_create_extensions(ctx, &buf[name.to_bytes_with_nul().len()..])?;

        let result = self
            .fs
            .async_create(ctx.context(), ctx.nodeid(), name, args)
            .await;

        match result {
            Ok((entry, handle, opts, passthrough)) => {
                let entry_out = EntryOut {
                    nodeid: entry.inode,
                    generation: entry.generation,
                    entry_valid: entry.entry_timeout.as_secs(),
                    attr_valid: entry.attr_timeout.as_secs(),
                    entry_valid_nsec: entry.entry_timeout.subsec_nanos(),
                    attr_valid_nsec: entry.attr_timeout.subsec_nanos(),
                    attr: entry.attr.into(),
                };
                let open_out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    passthrough: passthrough.unwrap_or_default(),
                };

                // Kind of a hack to write both structs.
                ctx.async_reply_ok(Some(entry_out), Some(open_out.as_slice()))
                    .await
            }
            Err(e) => ctx.async_reply_error(e).await,
        }
    }

    async fn async_fallocate<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let FallocateIn {
            fh,
            offset,
            length,
            mode,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let result = self
            .fs
            .async_fallocate(ctx.context(), ctx.nodeid(), fh.into(), mode, offset, length)
            .await;

        match result {
            Ok(()) => ctx.async_reply_ok(None::<u8>, None).await,
            Err(e) => ctx.async_reply_error(e).await,
        }
    }
}

impl<'a, F: AsyncFileSystem, S: BitmapSlice, W: Writer> SrvContext<'a, F, S, W> {
    async fn async_reply_ok<T: ByteValued>(
        &mut self,
        out: Option<T>,
        data: Option<&[u8]>,
    ) -> Result<usize> {
        let data2 = out.as_ref().map(|v| v.as_slice()).unwrap_or(&[]);
        let data3 = data.unwrap_or(&[]);
        let len = size_of::<OutHeader>() + data2.len() + data3.len();
        let header = OutHeader {
            len: len as u32,
            error: 0,
            unique: self.in_header.unique,
        };
        trace!("fuse: new reply {:?}", header);

        self.replied = true;
        let result = match (data2.len(), data3.len()) {
            (0, 0) => self.w.async_write(header.as_slice()).await,
            (0, _) => self.w.async_write2(header.as_slice(), data3).await,
            (_, 0) => self.w.async_write2(header.as_slice(), data2).await,
            (_, _) => self.w.async_write3(header.as_slice(), data2, data3).await,
        };
        result.map_err(Error::EncodeMessage)?;

        debug_assert_eq!(len, self.w.bytes_written());
        Ok(self.w.bytes_written())
    }

    /// Replies with the `data_len` bytes that a READ or READDIR handler wrote to `data_writer`,
    /// the part of the reply buffer after the `OutHeader`. Writes the header and commits it
    /// together with the data.
    async fn async_reply_with_data(&mut self, data_writer: &W, data_len: usize) -> Result<usize> {
        let header = OutHeader {
            len: (size_of::<OutHeader>() + data_len) as u32,
            error: 0,
            unique: self.in_header.unique,
        };

        self.replied = true;
        self.w
            .async_write_all(header.as_slice())
            .await
            .map_err(Error::EncodeMessage)?;
        self.w
            .async_commit(Some(data_writer))
            .await
            .map_err(Error::EncodeMessage)?;
        Ok(header.len as usize)
    }

    async fn async_do_reply_error(&mut self, err: io::Error, internal_err: bool) -> Result<usize> {
        let header = OutHeader {
            len: size_of::<OutHeader>() as u32,
            error: -err
                .raw_os_error()
                .unwrap_or_else(|| encode_io_error_kind(err.kind())),
            unique: self.in_header.unique,
        };

        trace!("fuse: reply error header {:?}, error {:?}", header, err);
        if internal_err {
            error!("fuse: reply error header {:?}, error {:?}", header, err);
        }
        self.replied = true;
        self.w
            .async_write_all(header.as_slice())
            .await
            .map_err(Error::EncodeMessage)?;

        // Commit header if it is buffered otherwise kernel gets nothing back.
        self.w
            .async_commit(None)
            .await
            .map(|_| {
                debug_assert_eq!(header.len as usize, self.w.bytes_written());
                self.w.bytes_written()
            })
            .map_err(Error::EncodeMessage)
    }

    // reply operation error back to fuse client, don't print error message, as they are not
    // server's internal error, and client could deal with them.
    async fn async_reply_error(&mut self, err: io::Error) -> Result<usize> {
        self.async_do_reply_error(err, false).await
    }

    async fn async_reply_error_explicit(&mut self, err: io::Error) -> Result<usize> {
        self.async_do_reply_error(err, true).await
    }

    async fn async_handle_attr_result(
        &mut self,
        result: io::Result<(stat64, Duration)>,
    ) -> Result<usize> {
        match result {
            Ok((st, timeout)) => {
                let out = AttrOut {
                    attr_valid: timeout.as_secs(),
                    attr_valid_nsec: timeout.subsec_nanos(),
                    dummy: 0,
                    attr: st.into(),
                };
                self.async_reply_ok(Some(out), None).await
            }
            Err(e) => self.async_reply_error(e).await,
        }
    }

    /// Replies to a GETXATTR or LISTXATTR whose buffer holds `size` bytes.
    ///
    /// `handle_xattr_result()` in sync_io.rs has the same reply policy with
    /// the sync reply calls. Change the two together.
    async fn async_handle_xattr_result(
        &mut self,
        size: u32,
        result: io::Result<impl Into<XattrReply>>,
    ) -> Result<usize> {
        match result.map(Into::into).and_then(|reply| reply.fit(size)) {
            Ok(XattrReply::Data(data)) => self.async_reply_ok(None::<u8>, Some(&data)).await,
            Ok(XattrReply::Size(size)) => {
                let out = GetxattrOut {
                    size,
                    ..Default::default()
                };
                self.async_reply_ok(Some(out), None).await
            }
            Err(e) => self.async_reply_error(e).await,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::ffi::CStr;
    use std::sync::atomic::AtomicUsize;

    use super::super::test_util::{
        check_malformed, check_oversized, oversized_request, request, request_bodies, request_for,
        MockFS, NoDax, TestWriter, OVERSIZED_OPCODES,
    };
    use super::*;
    use crate::abi::fuse_abi::{statvfs64, Dirent, InHeader, RENAME_NOREPLACE, S_IFCHR};
    use crate::api::filesystem::{Context, FileSystem, GetxattrReply, ListxattrReply, OpenOptions};
    use crate::async_runtime;

    const DIR_HANDLE: u64 = 7;

    /// Lists inode 1, the only directory, from `offset` until `add_entry()` returns 0.
    fn list(
        inode: u64,
        offset: u64,
        mut add_entry: impl FnMut(DirEntry, Entry) -> io::Result<usize>,
    ) -> io::Result<()> {
        if inode != 1 {
            return Err(io::Error::from_raw_os_error(libc::ENOTDIR));
        }
        let names: [&[u8]; 3] = [b"a", b"bb", b"ccc"];
        for (i, name) in names.iter().enumerate().skip(offset as usize) {
            let ino = i as u64 + 2;
            let mut entry = Entry {
                inode: ino,
                generation: 1,
                ..Default::default()
            };
            entry.attr.st_ino = ino;
            entry.attr.st_mode = libc::S_IFREG | 0o644;
            let dir_entry = DirEntry {
                ino,
                offset: i as u64 + 1,
                type_: libc::DT_REG as u32,
                name,
            };
            if add_entry(dir_entry, entry)? == 0 {
                break;
            }
        }
        Ok(())
    }

    /// Checks the handle that `opendir()` hands out.
    fn check_handle(handle: u64) -> io::Result<()> {
        if handle == DIR_HANDLE {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(libc::EBADF))
        }
    }

    const XATTR_VALUE: &[u8] = b"value";

    fn new_entry(inode: u64) -> Entry {
        Entry {
            inode,
            generation: 1,
            ..Default::default()
        }
    }

    /// Creates the directory "dir", with inode 5.
    fn mkdir_entry(name: &CStr) -> io::Result<Entry> {
        match name.to_bytes() {
            b"dir" => Ok(new_entry(5)),
            _ => Err(io::Error::from_raw_os_error(libc::EEXIST)),
        }
    }

    /// Creates the symlink "link" to "target", with inode 6.
    fn symlink_entry(linkname: &CStr, name: &CStr) -> io::Result<Entry> {
        match (linkname.to_bytes(), name.to_bytes()) {
            (b"target", b"link") => Ok(new_entry(6)),
            _ => Err(io::Error::from_raw_os_error(libc::EINVAL)),
        }
    }

    const MKNOD_MODE: u32 = S_IFCHR | 0o666;
    /// Device 1:3.
    const MKNOD_RDEV: u32 = 0x103;

    /// Creates the character device "null" in inode 1, with inode 7.
    fn mknod_entry(
        parent: u64,
        name: &CStr,
        mode: u32,
        rdev: u32,
        umask: u32,
    ) -> io::Result<Entry> {
        match (parent, name.to_bytes(), mode, rdev, umask) {
            (1, b"null", MKNOD_MODE, MKNOD_RDEV, 0o022) => Ok(new_entry(7)),
            _ => Err(io::Error::from_raw_os_error(libc::EINVAL)),
        }
    }

    /// Links inode 2 into inode 1 as "hardlink".
    fn link_entry(inode: u64, newparent: u64, newname: &CStr) -> io::Result<Entry> {
        match (inode, newparent, newname.to_bytes()) {
            (2, 1, b"hardlink") => Ok(new_entry(2)),
            _ => Err(io::Error::from_raw_os_error(libc::EINVAL)),
        }
    }

    /// Removes the file "a" from inode 1.
    fn check_unlink(parent: u64, name: &CStr) -> io::Result<()> {
        match (parent, name.to_bytes()) {
            (1, b"a") => Ok(()),
            _ => Err(io::Error::from_raw_os_error(libc::ENOENT)),
        }
    }

    /// Removes the directory "dir" from inode 1.
    fn check_rmdir(parent: u64, name: &CStr) -> io::Result<()> {
        match (parent, name.to_bytes()) {
            (1, b"dir") => Ok(()),
            _ => Err(io::Error::from_raw_os_error(libc::ENOENT)),
        }
    }

    /// Renames "a" in inode 1 to "b" in inode 5. "b" exists, so RENAME_NOREPLACE fails, and no
    /// other flag is supported.
    fn check_rename(
        olddir: u64,
        oldname: &CStr,
        newdir: u64,
        newname: &CStr,
        flags: u32,
    ) -> io::Result<()> {
        match (olddir, oldname.to_bytes(), newdir, newname.to_bytes()) {
            (1, b"a", 5, b"b") => match flags {
                0 => Ok(()),
                RENAME_NOREPLACE => Err(io::Error::from_raw_os_error(libc::EEXIST)),
                _ => Err(io::Error::from_raw_os_error(libc::EINVAL)),
            },
            _ => Err(io::Error::from_raw_os_error(libc::ENOENT)),
        }
    }

    /// A RENAME body for `names`, to inode 5.
    // On Linux, RenameIn has only `newdir`, so the struct update fills nothing. macOS's RenameIn
    // also has flags and padding.
    #[allow(clippy::needless_update)]
    fn rename_body(names: &[u8]) -> Vec<u8> {
        let rename_in = RenameIn {
            newdir: 5,
            ..Default::default()
        };
        [rename_in.as_slice(), names].concat()
    }

    /// A RENAME2 body for `names`, to inode 5, with `flags`.
    fn rename2_body(names: &[u8], flags: u32) -> Vec<u8> {
        let rename2_in = Rename2In {
            newdir: 5,
            flags,
            ..Default::default()
        };
        [rename2_in.as_slice(), names].concat()
    }

    /// Sets "user.a" to `XATTR_VALUE`.
    fn check_setxattr(name: &CStr, value: &[u8]) -> io::Result<()> {
        match (name.to_bytes(), value) {
            (b"user.a", XATTR_VALUE) => Ok(()),
            _ => Err(io::Error::from_raw_os_error(libc::EINVAL)),
        }
    }

    const XATTR_NAMES: &[u8] = b"user.a\0";

    /// The errno for a missing xattr: ENODATA on Linux, ENOATTR on macOS and FreeBSD, which has
    /// no ENODATA.
    #[cfg(target_os = "linux")]
    const XATTR_ABSENT: libc::c_int = libc::ENODATA;
    #[cfg(not(target_os = "linux"))]
    const XATTR_ABSENT: libc::c_int = libc::ENOATTR;

    /// Inodes that answer GETXATTR and LISTXATTR with the data, or with its length, whatever the
    /// size, and leave the size rules to the server.
    const DATA_INODE: u64 = 3;
    const COUNT_INODE: u64 = 4;

    /// Answers a GETXATTR or LISTXATTR of `inode` for `size` bytes of `data`, with `value(data)`
    /// or `count(length)`. Inode 2 sizes the reply like a real file system: the length for size
    /// 0, the data if it fits, ERANGE otherwise. Other inodes have no xattrs.
    fn xattr_reply<T>(
        inode: u64,
        size: u32,
        data: &[u8],
        value: fn(Vec<u8>) -> T,
        count: fn(u32) -> T,
    ) -> io::Result<T> {
        let len = data.len() as u32;
        match inode {
            DATA_INODE => Ok(value(data.to_vec())),
            COUNT_INODE => Ok(count(len)),
            2 if size == 0 => Ok(count(len)),
            2 if size >= len => Ok(value(data.to_vec())),
            2 => Err(io::Error::from_raw_os_error(libc::ERANGE)),
            _ => Err(io::Error::from_raw_os_error(XATTR_ABSENT)),
        }
    }

    /// Gets "user.a", whose value is `XATTR_VALUE`.
    fn getxattr_reply(inode: u64, name: &CStr, size: u32) -> io::Result<GetxattrReply> {
        if name.to_bytes() != b"user.a" {
            return Err(io::Error::from_raw_os_error(XATTR_ABSENT));
        }
        xattr_reply(
            inode,
            size,
            XATTR_VALUE,
            GetxattrReply::Value,
            GetxattrReply::Count,
        )
    }

    /// Lists `XATTR_NAMES`.
    fn listxattr_reply(inode: u64, size: u32) -> io::Result<ListxattrReply> {
        xattr_reply(
            inode,
            size,
            XATTR_NAMES,
            ListxattrReply::Names,
            ListxattrReply::Count,
        )
    }

    /// Removes "user.a" from inode 2.
    fn check_removexattr(inode: u64, name: &CStr) -> io::Result<()> {
        match (inode, name.to_bytes()) {
            (2, b"user.a") => Ok(()),
            _ => Err(io::Error::from_raw_os_error(XATTR_ABSENT)),
        }
    }

    fn statfs_reply() -> statvfs64 {
        // Safe because statvfs64 is plain data.
        let mut st: statvfs64 = unsafe { std::mem::zeroed() };
        st.f_bsize = 4096;
        st
    }

    const FILE_HANDLE: u64 = 8;
    const LOCK_OWNER: u64 = 0x1234;
    const FILE_SIZE: u64 = 8192;

    /// Flushes `FILE_HANDLE` of inode 2 for `LOCK_OWNER`.
    fn check_flush(inode: u64, handle: u64, lock_owner: u64) -> io::Result<()> {
        match (inode, handle, lock_owner) {
            (2, FILE_HANDLE, LOCK_OWNER) => Ok(()),
            _ => Err(io::Error::from_raw_os_error(libc::EBADF)),
        }
    }

    /// Grants read and write access to inode 2, and nothing else.
    fn check_access(inode: u64, mask: u32) -> io::Result<()> {
        let allowed = (libc::R_OK | libc::W_OK) as u32;
        if inode == 2 && mask & !allowed == 0 {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(libc::EACCES))
        }
    }

    /// Seeks `FILE_HANDLE` of inode 2, a file of `FILE_SIZE` bytes, relative to its end.
    fn lseek_offset(inode: u64, handle: u64, offset: u64, whence: u32) -> io::Result<u64> {
        if (inode, handle, whence) == (2, FILE_HANDLE, libc::SEEK_END as u32) {
            Ok(FILE_SIZE + offset)
        } else {
            Err(io::Error::from_raw_os_error(libc::EINVAL))
        }
    }

    /// Copies 2048 bytes at offset 4096 of `FILE_HANDLE` of inode 2 to offset 512 of handle 9 of
    /// inode 3.
    #[allow(clippy::too_many_arguments)]
    fn copy_len(
        inode_in: u64,
        fh_in: u64,
        offset_in: u64,
        inode_out: u64,
        fh_out: u64,
        offset_out: u64,
        len: u64,
        flags: u64,
    ) -> io::Result<u32> {
        match (
            inode_in, fh_in, offset_in, inode_out, fh_out, offset_out, len, flags,
        ) {
            (2, FILE_HANDLE, 4096, 3, 9, 512, 2048, 0) => Ok(2048),
            _ => Err(io::Error::from_raw_os_error(libc::EINVAL)),
        }
    }

    /// Answers with the sync and the async handlers alike, and counts the calls of each.
    #[derive(Default)]
    struct DirFs {
        sync_calls: AtomicUsize,
        async_calls: AtomicUsize,
    }

    impl DirFs {
        fn calls(&self) -> (usize, usize) {
            (
                self.sync_calls.load(Ordering::Relaxed),
                self.async_calls.load(Ordering::Relaxed),
            )
        }

        fn sync_call(&self) {
            self.sync_calls.fetch_add(1, Ordering::Relaxed);
        }

        /// Counts the call and yields to the runtime, so the server has to wait for the future.
        async fn async_call(&self) {
            self.async_calls.fetch_add(1, Ordering::Relaxed);
            tokio::task::yield_now().await;
        }
    }

    impl FileSystem for DirFs {
        type Inode = u64;
        type Handle = u64;

        fn opendir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions)> {
            self.sync_call();
            Ok((Some(DIR_HANDLE), OpenOptions::CACHE_DIR))
        }

        fn readdir(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: u64,
            _size: u32,
            offset: u64,
            add_entry: &mut dyn FnMut(DirEntry) -> io::Result<usize>,
        ) -> io::Result<()> {
            self.sync_call();
            list(inode, offset, |dir_entry, _| add_entry(dir_entry))
        }

        fn readdirplus(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: u64,
            _size: u32,
            offset: u64,
            add_entry: &mut dyn FnMut(DirEntry, Entry) -> io::Result<usize>,
        ) -> io::Result<()> {
            self.sync_call();
            list(inode, offset, add_entry)
        }

        fn releasedir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
        ) -> io::Result<()> {
            self.sync_call();
            check_handle(handle)
        }

        fn readlink(&self, _ctx: &Context, _inode: u64) -> io::Result<Vec<u8>> {
            self.sync_call();
            Ok(b"target".to_vec())
        }

        fn mkdir(
            &self,
            _ctx: &Context,
            _parent: u64,
            name: &CStr,
            _mode: u32,
            _umask: u32,
        ) -> io::Result<Entry> {
            self.sync_call();
            mkdir_entry(name)
        }

        fn symlink(
            &self,
            _ctx: &Context,
            linkname: &CStr,
            _parent: u64,
            name: &CStr,
        ) -> io::Result<Entry> {
            self.sync_call();
            symlink_entry(linkname, name)
        }

        fn mknod(
            &self,
            _ctx: &Context,
            parent: u64,
            name: &CStr,
            mode: u32,
            rdev: u32,
            umask: u32,
        ) -> io::Result<Entry> {
            self.sync_call();
            mknod_entry(parent, name, mode, rdev, umask)
        }

        fn link(
            &self,
            _ctx: &Context,
            inode: u64,
            newparent: u64,
            newname: &CStr,
        ) -> io::Result<Entry> {
            self.sync_call();
            link_entry(inode, newparent, newname)
        }

        fn unlink(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<()> {
            self.sync_call();
            check_unlink(parent, name)
        }

        fn rmdir(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<()> {
            self.sync_call();
            check_rmdir(parent, name)
        }

        fn rename(
            &self,
            _ctx: &Context,
            olddir: u64,
            oldname: &CStr,
            newdir: u64,
            newname: &CStr,
            flags: u32,
        ) -> io::Result<()> {
            self.sync_call();
            check_rename(olddir, oldname, newdir, newname, flags)
        }

        fn setxattr(
            &self,
            _ctx: &Context,
            _inode: u64,
            name: &CStr,
            value: &[u8],
            _flags: u32,
        ) -> io::Result<()> {
            self.sync_call();
            check_setxattr(name, value)
        }

        fn getxattr(
            &self,
            _ctx: &Context,
            inode: u64,
            name: &CStr,
            size: u32,
        ) -> io::Result<GetxattrReply> {
            self.sync_call();
            getxattr_reply(inode, name, size)
        }

        fn listxattr(&self, _ctx: &Context, inode: u64, size: u32) -> io::Result<ListxattrReply> {
            self.sync_call();
            listxattr_reply(inode, size)
        }

        fn removexattr(&self, _ctx: &Context, inode: u64, name: &CStr) -> io::Result<()> {
            self.sync_call();
            check_removexattr(inode, name)
        }

        fn release(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
            _flush: bool,
            _flock_release: bool,
            _lock_owner: Option<u64>,
        ) -> io::Result<()> {
            self.sync_call();
            check_handle(handle)
        }

        fn statfs(&self, _ctx: &Context, _inode: u64) -> io::Result<statvfs64> {
            self.sync_call();
            Ok(statfs_reply())
        }

        fn flush(
            &self,
            _ctx: &Context,
            inode: u64,
            handle: u64,
            lock_owner: u64,
        ) -> io::Result<()> {
            self.sync_call();
            check_flush(inode, handle, lock_owner)
        }

        fn access(&self, _ctx: &Context, inode: u64, mask: u32) -> io::Result<()> {
            self.sync_call();
            check_access(inode, mask)
        }

        fn lseek(
            &self,
            _ctx: &Context,
            inode: u64,
            handle: u64,
            offset: u64,
            whence: u32,
        ) -> io::Result<u64> {
            self.sync_call();
            lseek_offset(inode, handle, offset, whence)
        }

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
        ) -> io::Result<u32> {
            self.sync_call();
            copy_len(
                inode_in, fh_in, offset_in, inode_out, fh_out, offset_out, len, flags,
            )
        }
    }

    #[async_trait]
    impl AsyncFileSystem for DirFs {
        async fn async_opendir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions)> {
            self.async_call().await;
            Ok((Some(DIR_HANDLE), OpenOptions::CACHE_DIR))
        }

        async fn async_readdir(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: u64,
            _size: u32,
            offset: u64,
            add_entry: &mut (dyn FnMut(DirEntry) -> io::Result<usize> + Send),
        ) -> io::Result<()> {
            self.async_call().await;
            list(inode, offset, |dir_entry, _| add_entry(dir_entry))
        }

        async fn async_readdirplus(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: u64,
            _size: u32,
            offset: u64,
            add_entry: &mut (dyn FnMut(DirEntry, Entry) -> io::Result<usize> + Send),
        ) -> io::Result<()> {
            self.async_call().await;
            list(inode, offset, add_entry)
        }

        async fn async_releasedir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
        ) -> io::Result<()> {
            self.async_call().await;
            check_handle(handle)
        }

        async fn async_readlink(&self, _ctx: &Context, _inode: u64) -> io::Result<Vec<u8>> {
            self.async_call().await;
            Ok(b"target".to_vec())
        }

        async fn async_mkdir(
            &self,
            _ctx: &Context,
            _parent: u64,
            name: &CStr,
            _mode: u32,
            _umask: u32,
        ) -> io::Result<Entry> {
            self.async_call().await;
            mkdir_entry(name)
        }

        async fn async_symlink(
            &self,
            _ctx: &Context,
            linkname: &CStr,
            _parent: u64,
            name: &CStr,
        ) -> io::Result<Entry> {
            self.async_call().await;
            symlink_entry(linkname, name)
        }

        async fn async_mknod(
            &self,
            _ctx: &Context,
            parent: u64,
            name: &CStr,
            mode: u32,
            rdev: u32,
            umask: u32,
        ) -> io::Result<Entry> {
            self.async_call().await;
            mknod_entry(parent, name, mode, rdev, umask)
        }

        async fn async_link(
            &self,
            _ctx: &Context,
            inode: u64,
            newparent: u64,
            newname: &CStr,
        ) -> io::Result<Entry> {
            self.async_call().await;
            link_entry(inode, newparent, newname)
        }

        async fn async_unlink(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<()> {
            self.async_call().await;
            check_unlink(parent, name)
        }

        async fn async_rmdir(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<()> {
            self.async_call().await;
            check_rmdir(parent, name)
        }

        async fn async_rename(
            &self,
            _ctx: &Context,
            olddir: u64,
            oldname: &CStr,
            newdir: u64,
            newname: &CStr,
            flags: u32,
        ) -> io::Result<()> {
            self.async_call().await;
            check_rename(olddir, oldname, newdir, newname, flags)
        }

        async fn async_setxattr(
            &self,
            _ctx: &Context,
            _inode: u64,
            name: &CStr,
            value: &[u8],
            _flags: u32,
        ) -> io::Result<()> {
            self.async_call().await;
            check_setxattr(name, value)
        }

        async fn async_getxattr(
            &self,
            _ctx: &Context,
            inode: u64,
            name: &CStr,
            size: u32,
        ) -> io::Result<GetxattrReply> {
            self.async_call().await;
            getxattr_reply(inode, name, size)
        }

        async fn async_listxattr(
            &self,
            _ctx: &Context,
            inode: u64,
            size: u32,
        ) -> io::Result<ListxattrReply> {
            self.async_call().await;
            listxattr_reply(inode, size)
        }

        async fn async_removexattr(
            &self,
            _ctx: &Context,
            inode: u64,
            name: &CStr,
        ) -> io::Result<()> {
            self.async_call().await;
            check_removexattr(inode, name)
        }

        async fn async_release(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
            _flush: bool,
            _flock_release: bool,
            _lock_owner: Option<u64>,
        ) -> io::Result<()> {
            self.async_call().await;
            check_handle(handle)
        }

        async fn async_statfs(&self, _ctx: &Context, _inode: u64) -> io::Result<statvfs64> {
            self.async_call().await;
            Ok(statfs_reply())
        }

        async fn async_flush(
            &self,
            _ctx: &Context,
            inode: u64,
            handle: u64,
            lock_owner: u64,
        ) -> io::Result<()> {
            self.async_call().await;
            check_flush(inode, handle, lock_owner)
        }

        async fn async_access(&self, _ctx: &Context, inode: u64, mask: u32) -> io::Result<()> {
            self.async_call().await;
            check_access(inode, mask)
        }

        async fn async_lseek(
            &self,
            _ctx: &Context,
            inode: u64,
            handle: u64,
            offset: u64,
            whence: u32,
        ) -> io::Result<u64> {
            self.async_call().await;
            lseek_offset(inode, handle, offset, whence)
        }

        async fn async_copy_file_range(
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
        ) -> io::Result<u32> {
            self.async_call().await;
            copy_len(
                inode_in, fh_in, offset_in, inode_out, fh_out, offset_out, len, flags,
            )
        }
    }

    /// Serves a request for `nodeid` with the sync and with the async server, checks that both
    /// send the same reply, and returns it.
    async fn serve<T: ByteValued>(
        server: &Server<DirFs>,
        opcode: Opcode,
        nodeid: u64,
        body: T,
    ) -> Vec<u8> {
        serve_bytes(server, opcode, nodeid, body.as_slice()).await
    }

    /// Like `serve()`, with the request body in `body`.
    async fn serve_bytes(
        server: &Server<DirFs>,
        opcode: Opcode,
        nodeid: u64,
        body: &[u8],
    ) -> Vec<u8> {
        let mut sync_req = request_for(opcode, nodeid, body);
        let mut sync_reply = vec![0u8; 4096];
        let len = server
            .handle_message(
                Reader::<()>::from_slice(&mut sync_req),
                TestWriter::new(&mut sync_reply),
                None,
                None,
            )
            .unwrap();
        sync_reply.truncate(len);

        let mut async_req = request_for(opcode, nodeid, body);
        let mut async_reply = vec![0u8; 4096];
        let len = unsafe {
            server
                .async_handle_message(
                    Reader::<()>::from_slice(&mut async_req),
                    TestWriter::new(&mut async_reply),
                    None,
                    None,
                )
                .await
                .unwrap()
        };
        assert_eq!(reply_header(&async_reply).len as usize, len);
        async_reply.truncate(len);
        assert_eq!(sync_reply, async_reply);
        async_reply
    }

    fn reply_header(reply: &[u8]) -> OutHeader {
        let mut header = OutHeader::default();
        header
            .as_mut_slice()
            .copy_from_slice(&reply[..size_of::<OutHeader>()]);
        header
    }

    fn reply_error(reply: &[u8]) -> i32 {
        reply_header(reply).error
    }

    /// The `T` that fills `reply` after its header.
    fn reply_out<T: ByteValued + Default>(reply: &[u8]) -> T {
        let mut out = T::default();
        out.as_mut_slice()
            .copy_from_slice(&reply[size_of::<OutHeader>()..]);
        out
    }

    /// The inode of the entry in `reply`.
    fn entry_inode(reply: &[u8]) -> u64 {
        reply_out::<EntryOut>(reply).nodeid
    }

    /// The body of a GETXATTR or LISTXATTR for `size` bytes, before any name.
    fn getxattr_in(size: u32) -> GetxattrIn {
        GetxattrIn {
            size,
            ..Default::default()
        }
    }

    #[tokio::test]
    async fn test_async_opendir_releasedir() {
        let server = Server::new(DirFs::default());

        let reply = serve(&server, Opcode::Opendir, 1, OpenIn::default()).await;
        assert_eq!(server.fs.calls(), (1, 1));
        let out: OpenOut = reply_out(&reply);
        assert_eq!(out.fh, DIR_HANDLE);
        assert_eq!(out.open_flags, OpenOptions::CACHE_DIR.bits());

        let release_in = ReleaseIn {
            fh: DIR_HANDLE,
            ..Default::default()
        };
        let reply = serve(&server, Opcode::Releasedir, 1, release_in).await;
        assert_eq!(server.fs.calls(), (2, 2));
        assert_eq!(reply.len(), size_of::<OutHeader>());
        assert_eq!(reply_error(&reply), 0);

        let release_in = ReleaseIn {
            fh: DIR_HANDLE + 1,
            ..Default::default()
        };
        let reply = serve(&server, Opcode::Releasedir, 1, release_in).await;
        assert_eq!(server.fs.calls(), (3, 3));
        assert_eq!(reply_error(&reply), -libc::EBADF);
    }

    #[tokio::test]
    async fn test_async_readdir() {
        test_async_readdir_replies(Opcode::Readdir, 0).await;
    }

    #[tokio::test]
    async fn test_async_readdirplus() {
        test_async_readdir_replies(Opcode::Readdirplus, size_of::<EntryOut>()).await;
    }

    /// Lists the directory in a few ways, where each entry takes `entry_len` bytes besides its
    /// dirent. Each name is short enough for the dirent to take 32 bytes.
    async fn test_async_readdir_replies(opcode: Opcode, entry_len: usize) {
        let server = Server::new(DirFs::default());
        let header_len = size_of::<OutHeader>();
        let entry_len = entry_len + size_of::<Dirent>() + 8;
        let read_in = |offset, size| ReadIn {
            fh: DIR_HANDLE,
            offset,
            size,
            ..Default::default()
        };

        // The whole directory.
        let reply = serve(&server, opcode, 1, read_in(0, 1024)).await;
        assert_eq!(server.fs.calls(), (1, 1));
        assert_eq!(reply.len(), header_len + 3 * entry_len);

        // The entries after the first one.
        let reply = serve(&server, opcode, 1, read_in(1, 1024)).await;
        assert_eq!(server.fs.calls(), (2, 2));
        assert_eq!(reply.len(), header_len + 2 * entry_len);

        // As many entries as fit in the requested size.
        let size = 2 * entry_len as u32 + 1;
        let reply = serve(&server, opcode, 1, read_in(0, size)).await;
        assert_eq!(server.fs.calls(), (3, 3));
        assert_eq!(reply.len(), header_len + 2 * entry_len);

        // An error from the file system.
        let reply = serve(&server, opcode, 2, read_in(0, 1024)).await;
        assert_eq!(server.fs.calls(), (4, 4));
        assert_eq!(reply_error(&reply), -libc::ENOTDIR);

        // A size that doesn't fit in the reply buffer doesn't reach the file system.
        let reply = serve(&server, opcode, 1, read_in(0, 8192)).await;
        assert_eq!(server.fs.calls(), (4, 4));
        assert_eq!(reply_error(&reply), -libc::ENOMEM);
    }

    #[tokio::test]
    async fn test_async_node_requests() {
        let server = Server::new(DirFs::default());
        let header_len = size_of::<OutHeader>();

        let reply = serve_bytes(&server, Opcode::Readlink, 2, &[]).await;
        assert_eq!(&reply[header_len..], b"target");
        assert_eq!(server.fs.calls(), (1, 1));

        let mkdir_in = MkdirIn {
            mode: 0o755,
            umask: 0,
        };
        let body = [mkdir_in.as_slice(), b"dir\0"].concat();
        let reply = serve_bytes(&server, Opcode::Mkdir, 1, &body).await;
        assert_eq!(entry_inode(&reply), 5);
        let body = [mkdir_in.as_slice(), b"other\0"].concat();
        let reply = serve_bytes(&server, Opcode::Mkdir, 1, &body).await;
        assert_eq!(reply_error(&reply), -libc::EEXIST);
        assert_eq!(server.fs.calls(), (3, 3));

        // The name comes first, then the target.
        let reply = serve_bytes(&server, Opcode::Symlink, 1, b"link\0target\0").await;
        assert_eq!(entry_inode(&reply), 6);
        assert_eq!(server.fs.calls(), (4, 4));

        let reply = serve_bytes(&server, Opcode::Rename, 1, &rename_body(b"a\0b\0")).await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        assert_eq!(server.fs.calls(), (5, 5));

        let setxattr_in = SetxattrIn {
            size: XATTR_VALUE.len() as u32,
            flags: 0,
        };
        let body = [setxattr_in.as_slice(), b"user.a\0", XATTR_VALUE].concat();
        let reply = serve_bytes(&server, Opcode::Setxattr, 2, &body).await;
        assert_eq!(reply_error(&reply), 0);
        assert_eq!(server.fs.calls(), (6, 6));

        let release_in = ReleaseIn {
            fh: DIR_HANDLE,
            ..Default::default()
        };
        let reply = serve(&server, Opcode::Release, 2, release_in).await;
        assert_eq!(reply_error(&reply), 0);
        assert_eq!(server.fs.calls(), (7, 7));

        let reply = serve_bytes(&server, Opcode::Statfs, 1, &[]).await;
        let out: Kstatfs = reply_out(&reply);
        assert_eq!(out.bsize, 4096);
        assert_eq!(server.fs.calls(), (8, 8));
    }

    #[tokio::test]
    async fn test_async_namespace_requests() {
        let server = Server::new(DirFs::default());
        let header_len = size_of::<OutHeader>();

        let mknod_in = MknodIn {
            mode: MKNOD_MODE,
            rdev: MKNOD_RDEV,
            umask: 0o022,
            ..Default::default()
        };
        let body = [mknod_in.as_slice(), b"null\0"].concat();
        let reply = serve_bytes(&server, Opcode::Mknod, 1, &body).await;
        assert_eq!(entry_inode(&reply), 7);
        assert_eq!(server.fs.calls(), (1, 1));

        // The request is for the new parent, and the LinkIn names the inode to link.
        let link_in = LinkIn { oldnodeid: 2 };
        let body = [link_in.as_slice(), b"hardlink\0"].concat();
        let reply = serve_bytes(&server, Opcode::Link, 1, &body).await;
        assert_eq!(entry_inode(&reply), 2);
        assert_eq!(server.fs.calls(), (2, 2));

        let reply = serve_bytes(&server, Opcode::Unlink, 1, b"a\0").await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        let reply = serve_bytes(&server, Opcode::Unlink, 1, b"b\0").await;
        assert_eq!(reply_error(&reply), -libc::ENOENT);
        assert_eq!(server.fs.calls(), (4, 4));

        let reply = serve_bytes(&server, Opcode::Rmdir, 1, b"dir\0").await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        assert_eq!(server.fs.calls(), (5, 5));

        // The server drops the flags it doesn't know, and passes RENAME_NOREPLACE on.
        let unknown_flag = 1 << 31;
        let body = rename2_body(b"a\0b\0", unknown_flag);
        let reply = serve_bytes(&server, Opcode::Rename2, 1, &body).await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        let body = rename2_body(b"a\0b\0", RENAME_NOREPLACE | unknown_flag);
        let reply = serve_bytes(&server, Opcode::Rename2, 1, &body).await;
        assert_eq!(reply_error(&reply), -libc::EEXIST);
        assert_eq!(server.fs.calls(), (7, 7));
    }

    #[tokio::test]
    async fn test_async_xattr_requests() {
        let server = Server::new(DirFs::default());
        let header_len = size_of::<OutHeader>();

        let reply = serve_bytes(&server, Opcode::Removexattr, 2, b"user.a\0").await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        let reply = serve_bytes(&server, Opcode::Removexattr, 2, b"user.b\0").await;
        assert_eq!(reply_error(&reply), -XATTR_ABSENT);
        assert_eq!(server.fs.calls(), (2, 2));

        // Whether the file system or the server sizes the reply, a zero-size probe gets the
        // length, and data longer than the requested size gets ERANGE. A length for a nonzero
        // size gets EINVAL.
        for (opcode, name, data) in [
            (Opcode::Getxattr, &b"user.a\0"[..], XATTR_VALUE),
            (Opcode::Listxattr, &[][..], XATTR_NAMES),
        ] {
            let len = data.len() as u32;
            let length = GetxattrOut {
                size: len,
                ..Default::default()
            };
            for (inode, size, error, out) in [
                (2, 0, 0, length.as_slice()),
                (2, len, 0, data),
                (2, len - 1, libc::ERANGE, &[]),
                (DATA_INODE, 0, 0, length.as_slice()),
                (DATA_INODE, len - 1, libc::ERANGE, &[]),
                (COUNT_INODE, len, libc::EINVAL, &[]),
            ] {
                let body = [getxattr_in(size).as_slice(), name].concat();
                let reply = serve_bytes(&server, opcode, inode, &body).await;
                let case = format!("{opcode:?} of inode {inode} for {size} bytes");
                assert_eq!(reply_error(&reply), -error, "{case}");
                assert_eq!(&reply[header_len..], out, "{case}");
            }
        }
        assert_eq!(server.fs.calls(), (14, 14));
    }

    #[tokio::test]
    async fn test_async_file_requests() {
        let server = Server::new(DirFs::default());
        let header_len = size_of::<OutHeader>();

        let flush_in = FlushIn {
            fh: FILE_HANDLE,
            lock_owner: LOCK_OWNER,
            ..Default::default()
        };
        let reply = serve(&server, Opcode::Flush, 2, flush_in).await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        assert_eq!(server.fs.calls(), (1, 1));

        let access_in = |mask: i32| AccessIn {
            mask: mask as u32,
            ..Default::default()
        };
        let read_write = access_in(libc::R_OK | libc::W_OK);
        let reply = serve(&server, Opcode::Access, 2, read_write).await;
        assert_eq!(reply.len(), header_len);
        assert_eq!(reply_error(&reply), 0);
        let reply = serve(&server, Opcode::Access, 2, access_in(libc::X_OK)).await;
        assert_eq!(reply_error(&reply), -libc::EACCES);
        assert_eq!(server.fs.calls(), (3, 3));

        let lseek_in = LseekIn {
            fh: FILE_HANDLE,
            offset: 100,
            whence: libc::SEEK_END as u32,
            ..Default::default()
        };
        let reply = serve(&server, Opcode::Lseek, 2, lseek_in).await;
        assert_eq!(reply_out::<LseekOut>(&reply).offset, FILE_SIZE + 100);
        assert_eq!(server.fs.calls(), (4, 4));

        let copy_in = CopyFileRangeIn {
            fh_in: FILE_HANDLE,
            offset_in: 4096,
            nodeid_out: 3,
            fh_out: 9,
            offset_out: 512,
            len: 2048,
            flags: 0,
        };
        let reply = serve(&server, Opcode::CopyFileRange, 2, copy_in).await;
        assert_eq!(reply_out::<WriteOut>(&reply).size, 2048);
        assert_eq!(server.fs.calls(), (5, 5));
    }

    const BACKING_ID: u32 = 7;

    struct BackingFs;

    impl FileSystem for BackingFs {
        type Inode = u64;
        type Handle = u64;
    }

    #[allow(unused_variables)]
    #[async_trait]
    impl AsyncFileSystem for BackingFs {
        async fn async_lookup(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            unimplemented!()
        }

        async fn async_getattr(
            &self,
            ctx: &Context,
            inode: u64,
            handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            unimplemented!()
        }

        async fn async_setattr(
            &self,
            ctx: &Context,
            inode: u64,
            attr: stat64,
            handle: Option<u64>,
            valid: SetattrValid,
        ) -> io::Result<(stat64, Duration)> {
            unimplemented!()
        }

        async fn async_open(
            &self,
            ctx: &Context,
            inode: u64,
            flags: u32,
            fuse_flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
            Ok((Some(3), OpenOptions::PASSTHROUGH, Some(BACKING_ID)))
        }

        async fn async_create(
            &self,
            ctx: &Context,
            parent: u64,
            name: &CStr,
            args: CreateIn,
        ) -> io::Result<(Entry, Option<u64>, OpenOptions, Option<u32>)> {
            let entry = Entry {
                inode: 2,
                generation: 0,
                attr: unsafe { std::mem::zeroed() },
                attr_flags: 0,
                attr_timeout: Duration::from_secs(1),
                entry_timeout: Duration::from_secs(1),
            };
            Ok((entry, Some(4), OpenOptions::PASSTHROUGH, Some(BACKING_ID)))
        }

        async fn async_read(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            w: &mut (dyn AsyncZeroCopyWriter + Send),
            size: u32,
            offset: u64,
            lock_owner: Option<u64>,
            flags: u32,
        ) -> io::Result<usize> {
            unimplemented!()
        }

        async fn async_write(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            r: &mut (dyn AsyncZeroCopyReader + Send),
            size: u32,
            offset: u64,
            lock_owner: Option<u64>,
            delayed_write: bool,
            flags: u32,
            fuse_flags: u32,
        ) -> io::Result<usize> {
            unimplemented!()
        }

        async fn async_fsync(
            &self,
            ctx: &Context,
            inode: u64,
            datasync: bool,
            handle: u64,
        ) -> io::Result<()> {
            unimplemented!()
        }

        async fn async_fallocate(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            mode: u32,
            offset: u64,
            length: u64,
        ) -> io::Result<()> {
            unimplemented!()
        }

        async fn async_fsyncdir(
            &self,
            ctx: &Context,
            inode: u64,
            datasync: bool,
            handle: u64,
        ) -> io::Result<()> {
            unimplemented!()
        }
    }

    /// Serves one request for inode 1 with the async server alone, and returns the reply.
    fn serve_backing(opcode: Opcode, body: &[u8]) -> Vec<u8> {
        let header = InHeader {
            len: (size_of::<InHeader>() + body.len()) as u32,
            opcode: opcode as u32,
            unique: 1,
            nodeid: 1,
            ..Default::default()
        };
        let mut read_buf = [header.as_slice(), body].concat();
        let mut write_buf = vec![0u8; 4096];
        let server = Server::new(BackingFs);
        let len = async_runtime::block_on(async {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            unsafe { server.async_handle_message(reader, writer, None, None) }
                .await
                .unwrap()
        });
        write_buf.truncate(len);
        write_buf
    }

    #[test]
    fn test_async_server_doesnt_reply_to_notify_reply() {
        // The request lacks its NotifyRetrieveIn, so it fails to decode.
        let header = InHeader {
            len: size_of::<InHeader>() as u32,
            opcode: Opcode::NotifyReply as u32,
            unique: 42,
            nodeid: 1,
            ..Default::default()
        };
        let mut read_buf = header.as_slice().to_vec();
        let mut write_buf = [0u8; 4096];
        let server = Server::new(BackingFs);
        let res = async_runtime::block_on(async {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            unsafe { server.async_handle_message(reader, writer, None, None) }.await
        });
        assert!(matches!(res, Err(Error::DecodeMessage(_))));
        assert!(write_buf.iter().all(|&b| b == 0));
    }

    #[test]
    fn test_async_open_backing_id() {
        let open_in = OpenIn::default();
        let reply = serve_backing(Opcode::Open, open_in.as_slice());
        assert_eq!(reply.len(), size_of::<OutHeader>() + size_of::<OpenOut>());
        let out = OpenOut::from_slice(&reply[size_of::<OutHeader>()..]).unwrap();
        assert_eq!(out.fh, 3);
        assert_eq!(out.open_flags, OpenOptions::PASSTHROUGH.bits());
        assert_eq!(out.passthrough, BACKING_ID);
    }

    #[test]
    fn test_async_create_backing_id() {
        let create_in = CreateIn::default();
        let body = [create_in.as_slice(), b"file\0"].concat();
        let reply = serve_backing(Opcode::Create, &body);
        let offset = size_of::<OutHeader>() + size_of::<EntryOut>();
        assert_eq!(reply.len(), offset + size_of::<OpenOut>());
        let out = OpenOut::from_slice(&reply[offset..]).unwrap();
        assert_eq!(out.fh, 4);
        assert_eq!(out.open_flags, OpenOptions::PASSTHROUGH.bits());
        assert_eq!(out.passthrough, BACKING_ID);
    }

    #[tokio::test]
    async fn test_async_server_replies_to_malformed_bodies() {
        let server = Server::new(MockFS);
        for (opcode, body) in request_bodies() {
            for len in 0..body.len() {
                let mut req = request(opcode, &body[..len]);
                let mut reply = [0u8; 4096];
                let res = unsafe {
                    server
                        .async_handle_message(
                            Reader::<()>::from_slice(&mut req),
                            TestWriter::new(&mut reply),
                            Some(&mut NoDax),
                            None,
                        )
                        .await
                };
                check_malformed(opcode, len, res, &reply);
            }
        }
    }

    #[tokio::test]
    async fn test_async_server_rejects_oversized_requests() {
        let server = Server::new(MockFS);
        for opcode in OVERSIZED_OPCODES {
            let mut req = oversized_request(opcode);
            let mut reply = [0u8; 4096];
            let res = unsafe {
                server
                    .async_handle_message(
                        Reader::<()>::from_slice(&mut req),
                        TestWriter::new(&mut reply),
                        None,
                        None,
                    )
                    .await
            };
            check_oversized(opcode, res, &reply);
        }
    }
}
