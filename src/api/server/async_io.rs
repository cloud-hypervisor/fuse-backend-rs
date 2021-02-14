// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io::{self, IoSlice};
use std::marker::PhantomData;
use std::mem::size_of;
use std::os::unix::io::RawFd;
use std::time::Duration;

use async_trait::async_trait;
use vm_memory::ByteValued;

use super::{Server, ServerUtil, MAX_BUFFER_SIZE};
use crate::abi::linux_abi::*;
use crate::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, ZeroCopyReader,
    ZeroCopyWriter,
};
use crate::async_util::AsyncDrive;
use crate::transport::{FileReadWriteVolatile, FsCacheReqHandler, Reader, Writer};
use crate::{bytes_to_cstr, encode_io_error_kind, Error, Result};

struct AsyncZCReader<'a>(Reader<'a>);

// The underlying VolatileSlice contains "*mut u8", which is just a pointer to a u8 array.
// So safe to send to other threads.
unsafe impl<'a> Send for Reader<'a> {}

#[async_trait]
impl<'a, D: AsyncDrive> AsyncZeroCopyReader<D> for AsyncZCReader<'a> {
    async fn async_read_to(
        &mut self,
        drive: D,
        f: RawFd,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.async_read_to_at(drive, f, count, off).await
    }
}

impl<'a> ZeroCopyReader for AsyncZCReader<'a> {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.read_to_at(f, count, off)
    }
}

impl<'a> io::Read for AsyncZCReader<'a> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

struct AsyncZCWriter<'a>(Writer<'a>);

// The underlying VolatileSlice contains "*mut u8", which is just a pointer to a u8 array.
// So safe to send to other threads.
unsafe impl<'a> Send for Writer<'a> {}

#[async_trait]
impl<'a, D: AsyncDrive + 'static> AsyncZeroCopyWriter<D> for AsyncZCWriter<'a> {
    async fn async_write_from(
        &mut self,
        drive: D,
        f: RawFd,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let writer = &mut self.0;

        writer.async_write_from_at(drive, f, count, off).await
    }
}

impl<'a> ZeroCopyWriter for AsyncZCWriter<'a> {
    fn write_from(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.write_from_at(f, count, off)
    }
}

impl<'a> io::Write for AsyncZCWriter<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
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
    #[allow(clippy::cognitive_complexity)]
    pub async unsafe fn async_handle_message<D: AsyncDrive>(
        &self,
        drive: D,
        mut r: Reader<'_>,
        w: Writer<'_>,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
    ) -> Result<usize> {
        let in_header = r.read_obj().map_err(Error::DecodeMessage)?;
        let ctx = AsyncContext::new(in_header, drive);
        if ctx.in_header.len > MAX_BUFFER_SIZE || w.available_bytes() < size_of::<OutHeader>() {
            return ctx
                .do_reply_error(io::Error::from_raw_os_error(libc::ENOMEM), w, true)
                .await;
        }
        let in_header = &ctx.in_header;

        trace!(
            "fuse: new req {:?}: {:?}",
            Opcode::from(in_header.opcode),
            in_header
        );
        match in_header.opcode {
            x if x == Opcode::Lookup as u32 => self.async_lookup(r, w, ctx).await,
            x if x == Opcode::Forget as u32 => self.forget(in_header, r), // No reply.
            x if x == Opcode::Getattr as u32 => self.async_getattr(r, w, ctx).await,
            x if x == Opcode::Setattr as u32 => self.async_setattr(r, w, ctx).await,
            x if x == Opcode::Readlink as u32 => self.readlink(in_header, w),
            x if x == Opcode::Symlink as u32 => self.symlink(in_header, r, w),
            x if x == Opcode::Mknod as u32 => self.mknod(in_header, r, w),
            x if x == Opcode::Mkdir as u32 => self.mkdir(in_header, r, w),
            x if x == Opcode::Unlink as u32 => self.unlink(in_header, r, w),
            x if x == Opcode::Rmdir as u32 => self.rmdir(in_header, r, w),
            x if x == Opcode::Rename as u32 => self.rename(in_header, r, w),
            x if x == Opcode::Link as u32 => self.link(in_header, r, w),
            x if x == Opcode::Open as u32 => self.async_open(r, w, ctx).await,
            x if x == Opcode::Read as u32 => self.async_read(r, w, ctx).await,
            x if x == Opcode::Write as u32 => self.async_write(r, w, ctx).await,
            x if x == Opcode::Statfs as u32 => self.statfs(in_header, w),
            x if x == Opcode::Release as u32 => self.release(in_header, r, w),
            x if x == Opcode::Fsync as u32 => self.async_fsync(r, w, ctx).await,
            x if x == Opcode::Setxattr as u32 => self.setxattr(in_header, r, w),
            x if x == Opcode::Getxattr as u32 => self.getxattr(in_header, r, w),
            x if x == Opcode::Listxattr as u32 => self.listxattr(in_header, r, w),
            x if x == Opcode::Removexattr as u32 => self.removexattr(in_header, r, w),
            x if x == Opcode::Flush as u32 => self.flush(in_header, r, w),
            x if x == Opcode::Init as u32 => self.init(in_header, r, w),
            x if x == Opcode::Opendir as u32 => self.opendir(in_header, r, w),
            x if x == Opcode::Readdir as u32 => self.readdir(in_header, r, w),
            x if x == Opcode::Releasedir as u32 => self.releasedir(in_header, r, w),
            x if x == Opcode::Fsyncdir as u32 => self.async_fsyncdir(r, w, ctx).await,
            x if x == Opcode::Getlk as u32 => self.getlk(in_header, r, w),
            x if x == Opcode::Setlk as u32 => self.setlk(in_header, r, w),
            x if x == Opcode::Setlkw as u32 => self.setlkw(in_header, r, w),
            x if x == Opcode::Access as u32 => self.access(in_header, r, w),
            x if x == Opcode::Create as u32 => self.async_create(r, w, ctx).await,
            x if x == Opcode::Interrupt as u32 => self.interrupt(in_header),
            x if x == Opcode::Bmap as u32 => self.bmap(in_header, r, w),
            x if x == Opcode::Destroy as u32 => self.destroy(),
            x if x == Opcode::Ioctl as u32 => self.ioctl(in_header, r, w),
            x if x == Opcode::Poll as u32 => self.poll(in_header, r, w),
            x if x == Opcode::NotifyReply as u32 => self.notify_reply(in_header, r, w),
            x if x == Opcode::BatchForget as u32 => self.batch_forget(in_header, r, w),
            x if x == Opcode::Fallocate as u32 => self.async_fallocate(r, w, ctx).await,
            x if x == Opcode::Readdirplus as u32 => self.readdirplus(in_header, r, w),
            x if x == Opcode::Rename2 as u32 => self.rename2(in_header, r, w),
            x if x == Opcode::Lseek as u32 => self.lseek(in_header, r, w),
            #[cfg(feature = "virtiofs")]
            x if x == Opcode::SetupMapping as u32 => self.setupmapping(in_header, r, w, vu_req),
            #[cfg(feature = "virtiofs")]
            x if x == Opcode::RemoveMapping as u32 => self.removemapping(in_header, r, w, vu_req),
            _ => {
                return ctx
                    .reply_error(io::Error::from_raw_os_error(libc::ENOSYS), w)
                    .await
            }
        }
    }

    async fn async_lookup<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, &ctx.in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref())?;
        let result = self
            .fs
            .async_lookup(ctx.context(), ctx.nodeid(), &name)
            .await;

        match result {
            Ok(entry) => {
                let version = self.vers.load();

                // before ABI 7.4 inode == 0 was invalid, only ENOENT means negative dentry
                if version.major == 7
                    && version.minor < KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO
                    && entry.inode == 0
                {
                    let e = io::Error::from_raw_os_error(libc::ENOENT);
                    ctx.reply_error(e, w).await
                } else {
                    let out = EntryOut::from(entry);
                    ctx.reply_ok(Some(out), None, w).await
                }
            }
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_getattr<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let GetattrIn { flags, fh, .. } = r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if (flags & GETATTR_FH) != 0 {
            Some(fh.into())
        } else {
            None
        };
        let result = self
            .fs
            .async_getattr(ctx.context(), ctx.nodeid(), handle)
            .await;

        ctx.handle_attr_result(w, result).await
    }

    async fn async_setattr<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let setattr_in: SetattrIn = r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if setattr_in.valid & FATTR_FH != 0 {
            Some(setattr_in.fh.into())
        } else {
            None
        };
        let valid = SetattrValid::from_bits_truncate(setattr_in.valid);
        let st: libc::stat64 = setattr_in.into();
        let result = self
            .fs
            .async_setattr(ctx.context(), ctx.nodeid(), st, handle, valid)
            .await;

        ctx.handle_attr_result(w, result).await
    }

    async fn async_open<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let OpenIn { flags, .. } = r.read_obj().map_err(Error::DecodeMessage)?;
        let result = self.fs.async_open(ctx.context(), ctx.nodeid(), flags).await;

        match result {
            Ok((handle, opts)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    ..Default::default()
                };
                ctx.reply_ok(Some(out), None, w).await
            }
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_read<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        mut w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let ReadIn {
            fh,
            offset,
            size,
            read_flags,
            lock_owner,
            flags,
            ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        if size > MAX_BUFFER_SIZE {
            return ctx
                .do_reply_error(io::Error::from_raw_os_error(libc::ENOMEM), w, true)
                .await;
        }

        let owner = if read_flags & READ_LOCKOWNER != 0 {
            Some(lock_owner)
        } else {
            None
        };

        // Split the writer into 2 pieces: one for the `OutHeader` and the rest for the data.
        let w2 = match w.split_at(size_of::<OutHeader>()) {
            Ok(v) => v,
            Err(_e) => return Err(Error::InvalidHeaderLength),
        };
        let mut data_writer = AsyncZCWriter(w2);
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
            Ok(count) => {
                // Don't use `reply_ok` because we need to set a custom size length for the
                // header.
                let out = OutHeader {
                    len: (size_of::<OutHeader>() + count) as u32,
                    error: 0,
                    unique: ctx.unique(),
                };

                w.async_write_all(ctx.drive(), out.as_slice())
                    .await
                    .map_err(Error::EncodeMessage)?;
                w.async_commit(ctx.drive(), &[&data_writer.0])
                    .await
                    .map_err(Error::EncodeMessage)?;
                Ok(out.len as usize)
            }
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_write<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let WriteIn {
            fh,
            offset,
            size,
            write_flags,
            lock_owner,
            flags,
            ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        if size > MAX_BUFFER_SIZE {
            return ctx
                .do_reply_error(io::Error::from_raw_os_error(libc::ENOMEM), w, true)
                .await;
        }

        let owner = if write_flags & WRITE_LOCKOWNER != 0 {
            Some(lock_owner)
        } else {
            None
        };
        let delayed_write = write_flags & WRITE_CACHE != 0;
        let mut data_reader = AsyncZCReader(r);
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
            )
            .await;

        match result {
            Ok(count) => {
                let out = WriteOut {
                    size: count as u32,
                    ..Default::default()
                };

                ctx.reply_ok(Some(out), None, w).await
            }
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_fsync<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;

        match self
            .fs
            .async_fsync(ctx.context(), ctx.nodeid(), datasync, fh.into())
            .await
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None, w).await,
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_fsyncdir<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;
        let result = self
            .fs
            .async_fsyncdir(ctx.context(), ctx.nodeid(), datasync, fh.into())
            .await;

        match result {
            Ok(()) => ctx.reply_ok(None::<u8>, None, w).await,
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_create<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let CreateIn {
            flags, mode, umask, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut r, &ctx.in_header, size_of::<CreateIn>())?;
        let name = bytes_to_cstr(&buf)?;
        let result = self
            .fs
            .async_create(ctx.context(), ctx.nodeid(), name, mode, flags, umask)
            .await;

        match result {
            Ok((entry, handle, opts)) => {
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
                    ..Default::default()
                };

                // Kind of a hack to write both structs.
                ctx.reply_ok(Some(entry_out), Some(open_out.as_slice()), w)
                    .await
            }
            Err(e) => ctx.reply_error(e, w).await,
        }
    }

    async fn async_fallocate<D: AsyncDrive>(
        &self,
        mut r: Reader<'_>,
        w: Writer<'_>,
        ctx: AsyncContext<D, F>,
    ) -> Result<usize> {
        let FallocateIn {
            fh,
            offset,
            length,
            mode,
            ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let result = self
            .fs
            .async_fallocate(ctx.context(), ctx.nodeid(), fh.into(), mode, offset, length)
            .await;

        match result {
            Ok(()) => ctx.reply_ok(None::<u8>, None, w).await,
            Err(e) => ctx.reply_error(e, w).await,
        }
    }
}

struct AsyncContext<D, F> {
    drive: D,
    in_header: InHeader,
    phantom: PhantomData<F>,
}

impl<D: AsyncDrive, F: AsyncFileSystem> AsyncContext<D, F> {
    fn new(in_header: InHeader, drive: D) -> Self {
        AsyncContext {
            drive,
            in_header,
            phantom: PhantomData,
        }
    }

    fn context(&self) -> Context {
        let mut ctx = Context::from(&self.in_header);

        // Safe because the AsyncContext has longer lifetime than Context object.
        unsafe { ctx.set_drive(&self.drive) };

        ctx
    }

    fn unique(&self) -> u64 {
        self.in_header.unique
    }

    fn nodeid(&self) -> F::Inode {
        self.in_header.nodeid.into()
    }

    fn drive(&self) -> D {
        self.drive.clone()
    }

    async fn reply_ok<T: ByteValued>(
        &self,
        out: Option<T>,
        data: Option<&[u8]>,
        mut w: Writer<'_>,
    ) -> Result<usize> {
        let mut len = size_of::<OutHeader>();
        if out.is_some() {
            len += size_of::<T>();
        }
        if let Some(ref data) = data {
            len += data.len();
        }

        let header = OutHeader {
            len: len as u32,
            error: 0,
            unique: self.in_header.unique,
        };

        trace!("fuse: new reply {:?}", header);
        let mut buf = Vec::with_capacity(3);
        buf.push(IoSlice::new(header.as_slice()));
        // Need to write out header->out->data sequentially
        if let Some(out) = out {
            buf.push(IoSlice::new(out.as_slice()));
            if let Some(data) = data {
                buf.push(IoSlice::new(data));
            }
            w.async_write_vectored(self.drive(), &buf)
                .await
                .map_err(Error::EncodeMessage)?;
        } else {
            if let Some(data) = data {
                buf.push(IoSlice::new(data));
            }

            w.async_write_vectored(self.drive(), &buf)
                .await
                .map_err(Error::EncodeMessage)?;
        }

        debug_assert_eq!(len, w.bytes_written());
        Ok(w.bytes_written())
    }

    async fn do_reply_error(
        &self,
        err: io::Error,
        mut w: Writer<'_>,
        internal_err: bool,
    ) -> Result<usize> {
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
        w.async_write_all(self.drive(), header.as_slice())
            .await
            .map_err(Error::EncodeMessage)?;

        // Commit header if it is buffered otherwise kernel gets nothing back.
        w.async_commit(self.drive(), &[])
            .await
            .map(|_| {
                debug_assert_eq!(header.len as usize, w.bytes_written());
                w.bytes_written()
            })
            .map_err(Error::EncodeMessage)
    }

    // reply operation error back to fuse client, don't print error message, as they are not
    // server's internal error, and client could deal with them.
    async fn reply_error(&self, err: io::Error, w: Writer<'_>) -> Result<usize> {
        self.do_reply_error(err, w, false).await
    }

    async fn handle_attr_result(
        &self,
        w: Writer<'_>,
        result: io::Result<(libc::stat64, Duration)>,
    ) -> Result<usize> {
        match result {
            Ok((st, timeout)) => {
                let out = AttrOut {
                    attr_valid: timeout.as_secs(),
                    attr_valid_nsec: timeout.subsec_nanos(),
                    dummy: 0,
                    attr: st.into(),
                };
                self.reply_ok(Some(out), None, w).await
            }
            Err(e) => self.reply_error(e, w).await,
        }
    }
}

#[cfg(feature = "fusedev")]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::Vfs;
    use crate::async_util::{AsyncDriver, AsyncExecutor};
    use crate::transport::FuseBuf;

    use futures::executor::block_on;
    use std::os::unix::io::AsRawFd;

    #[test]
    fn test_vfs_async_invalid_header() {
        let vfs = Vfs::<AsyncDriver>::default();
        let server = Server::new(vfs);
        let mut r_buf = [0u8];
        let r = Reader::new(FuseBuf::new(&mut r_buf)).unwrap();
        let file = vmm_sys_util::tempfile::TempFile::new().unwrap();
        let w = Writer::new(file.as_file().as_raw_fd(), 0x1000).unwrap();

        let executor = AsyncExecutor::new(32);
        executor.setup().unwrap();

        let drive = AsyncDriver::default();
        let result = block_on(unsafe { server.async_handle_message(drive, r, w, None) });
        assert!(result.is_err());
    }
}
