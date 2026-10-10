// Copyright (C) 2021-2022 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io;
use std::mem::size_of;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use vm_memory::ByteValued;

use super::sync_io::{add_dirent, parse_create_extensions};
use crate::abi::fuse_abi::{
    stat64, AttrOut, CreateIn, EntryOut, FallocateIn, FsOptions, FsyncIn, GetattrIn, Opcode,
    OpenIn, OpenOut, OutHeader, ReadIn, ReleaseIn, SetattrIn, SetattrValid, WriteIn, WriteOut,
    FATTR_FH, GETATTR_FH, KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO, READ_LOCKOWNER,
    WRITE_CACHE, WRITE_LOCKOWNER,
};
use crate::api::filesystem::FsCacheReqHandler;
use crate::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, DirEntry, Entry, ZeroCopyReader,
    ZeroCopyWriter,
};
use crate::api::server::{
    decode_version, InitParams, MetricsHook, Server, ServerUtil, SrvContext, BUFFER_HEADER_SIZE,
    MAX_BUFFER_SIZE,
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
        self.0.async_read_to_at(&f, count, off).await
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
        self.0.async_write_from_at(&f, count, off).await
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
    #[allow(unused_variables)]
    pub async unsafe fn async_handle_message<S: BitmapSlice, W: Writer>(
        &self,
        mut r: Reader<'_, S>,
        w: W,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
        hook: Option<&dyn MetricsHook>,
    ) -> Result<usize> {
        let in_header = r.read_obj().map_err(Error::DecodeMessage)?;
        let mut ctx = SrvContext::<F, S, W>::new(in_header, r, w);
        self.remap_ctx_ids(&mut ctx)?;
        if ctx.in_header.len > (MAX_BUFFER_SIZE + BUFFER_HEADER_SIZE)
            || ctx.w.available_bytes() < size_of::<OutHeader>()
        {
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
            x if x == Opcode::Readlink as u32 => self.readlink(ctx),
            x if x == Opcode::Symlink as u32 => self.symlink(ctx),
            x if x == Opcode::Mknod as u32 => self.mknod(ctx),
            x if x == Opcode::Mkdir as u32 => self.mkdir(ctx),
            x if x == Opcode::Unlink as u32 => self.unlink(ctx),
            x if x == Opcode::Rmdir as u32 => self.rmdir(ctx),
            x if x == Opcode::Rename as u32 => self.rename(ctx),
            x if x == Opcode::Link as u32 => self.link(ctx),
            x if x == Opcode::Open as u32 => self.async_open(ctx).await,
            x if x == Opcode::Read as u32 => self.async_read(ctx).await,
            x if x == Opcode::Write as u32 => self.async_write(ctx).await,
            x if x == Opcode::Statfs as u32 => self.statfs(ctx),
            x if x == Opcode::Release as u32 => self.release(ctx),
            x if x == Opcode::Fsync as u32 => self.async_fsync(ctx).await,
            x if x == Opcode::Setxattr as u32 => self.setxattr(ctx),
            x if x == Opcode::Getxattr as u32 => self.getxattr(ctx),
            x if x == Opcode::Listxattr as u32 => self.listxattr(ctx),
            x if x == Opcode::Removexattr as u32 => self.removexattr(ctx),
            x if x == Opcode::Flush as u32 => self.flush(ctx),
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
            x if x == Opcode::Access as u32 => self.access(ctx),
            x if x == Opcode::Create as u32 => self.async_create(ctx).await,
            x if x == Opcode::Bmap as u32 => self.bmap(ctx),
            x if x == Opcode::Ioctl as u32 => self.ioctl(ctx),
            x if x == Opcode::Poll as u32 => self.poll(ctx),
            x if x == Opcode::NotifyReply as u32 => self.notify_reply(ctx),
            x if x == Opcode::BatchForget as u32 => self.batch_forget(ctx),
            x if x == Opcode::Fallocate as u32 => self.async_fallocate(ctx).await,
            #[cfg(target_os = "linux")]
            x if x == Opcode::Readdirplus as u32 => self.async_do_readdir(ctx, true).await,
            #[cfg(target_os = "linux")]
            x if x == Opcode::Rename2 as u32 => self.rename2(ctx),
            #[cfg(target_os = "linux")]
            x if x == Opcode::Lseek as u32 => self.lseek(ctx),
            #[cfg(target_os = "linux")]
            x if x == Opcode::CopyFileRange as u32 => self.copy_file_range(ctx),
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
        mut ctx: SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = match bytes_to_cstr(buf.as_ref()) {
            Ok(name) => name,
            Err(e) => {
                debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
                let _ = ctx
                    .async_reply_error(io::Error::from_raw_os_error(libc::EINVAL))
                    .await;
                return Err(e);
            }
        };

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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
            Err(_e) => return Err(Error::InvalidHeaderLength),
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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
        mut ctx: SrvContext<'_, F, S, W>,
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

    async fn async_create<S: BitmapSlice, W: Writer>(
        &self,
        mut ctx: SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let args: CreateIn = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<CreateIn>())?;
        let name = match bytes_to_cstr(buf.as_ref()) {
            Ok(name) => name,
            Err(e) => {
                debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
                let _ = ctx
                    .async_reply_error(io::Error::from_raw_os_error(libc::EINVAL))
                    .await;
                return Err(e);
            }
        };

        let supp_gid = match parse_create_extensions(
            &FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire)),
            &buf[name.to_bytes_with_nul().len()..],
        ) {
            Ok(supp_gid) => supp_gid,
            Err(e) => {
                let _ = ctx
                    .async_reply_error(io::Error::from_raw_os_error(libc::EINVAL))
                    .await;
                return Err(e);
            }
        };
        ctx.context.supp_gid = supp_gid;

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
        mut ctx: SrvContext<'_, F, S, W>,
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
}

#[cfg(all(test, target_os = "linux"))]
mod tests {
    use std::ffi::CStr;
    use std::sync::atomic::AtomicUsize;

    use super::super::test_util::TestWriter;
    use super::*;
    use crate::abi::fuse_abi::{Dirent, InHeader};
    use crate::api::filesystem::{Context, FileSystem, OpenOptions};
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

    fn release(handle: u64) -> io::Result<()> {
        if handle == DIR_HANDLE {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(libc::EBADF))
        }
    }

    /// Serves the same directory with the sync and the async handlers, and counts the calls
    /// of each.
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
            self.sync_calls.fetch_add(1, Ordering::Relaxed);
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
            self.sync_calls.fetch_add(1, Ordering::Relaxed);
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
            self.sync_calls.fetch_add(1, Ordering::Relaxed);
            list(inode, offset, add_entry)
        }

        fn releasedir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
        ) -> io::Result<()> {
            self.sync_calls.fetch_add(1, Ordering::Relaxed);
            release(handle)
        }
    }

    // Each handler yields to the runtime before it answers, so the server has to wait for
    // the future.
    #[async_trait]
    impl AsyncFileSystem for DirFs {
        async fn async_opendir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions)> {
            self.async_calls.fetch_add(1, Ordering::Relaxed);
            tokio::task::yield_now().await;
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
            self.async_calls.fetch_add(1, Ordering::Relaxed);
            tokio::task::yield_now().await;
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
            self.async_calls.fetch_add(1, Ordering::Relaxed);
            tokio::task::yield_now().await;
            list(inode, offset, add_entry)
        }

        async fn async_releasedir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            handle: u64,
        ) -> io::Result<()> {
            self.async_calls.fetch_add(1, Ordering::Relaxed);
            tokio::task::yield_now().await;
            release(handle)
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
        let in_header = InHeader {
            len: (size_of::<InHeader>() + size_of::<T>()) as u32,
            opcode: opcode as u32,
            unique: 1,
            nodeid,
            ..Default::default()
        };
        let mut req = in_header.as_slice().to_vec();
        req.extend_from_slice(body.as_slice());

        let mut sync_req = req.clone();
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

        let mut async_req = req;
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
        }
        .unwrap();
        async_reply.truncate(len);

        assert_eq!(sync_reply, async_reply);
        async_reply
    }

    fn reply_error(reply: &[u8]) -> i32 {
        let mut header = OutHeader::default();
        header
            .as_mut_slice()
            .copy_from_slice(&reply[..size_of::<OutHeader>()]);
        header.error
    }

    #[tokio::test]
    async fn test_async_opendir_releasedir() {
        let server = Server::new(DirFs::default());

        let reply = serve(&server, Opcode::Opendir, 1, OpenIn::default()).await;
        assert_eq!(server.fs.calls(), (1, 1));
        let mut out = OpenOut::default();
        out.as_mut_slice()
            .copy_from_slice(&reply[size_of::<OutHeader>()..]);
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
}
