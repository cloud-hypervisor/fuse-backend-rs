// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::io::{self, IoSlice, Write};
use std::mem::size_of;
use std::sync::Arc;
use std::time::Duration;

use vm_memory::ByteValued;

use super::{
    Server, ServerUtil, ServerVersion, ZCReader, ZCWriter, DIRENT_PADDING, MAX_BUFFER_SIZE,
    MAX_REQ_PAGES,
};
use crate::abi::linux_abi::*;
#[cfg(feature = "virtiofs")]
use crate::abi::virtio_fs::{RemovemappingIn, RemovemappingOne, SetupmappingIn};
use crate::api::filesystem::{Context, DirEntry, Entry, FileSystem, GetxattrReply, ListxattrReply};
use crate::transport::{FsCacheReqHandler, Reader, Writer};
use crate::{bytes_to_cstr, encode_io_error_kind, Error, Result};

/// Provide concrete backend filesystem a way to catch information/metrics from fuse.
pub trait MetricsHook {
    /// `collect()` will be invoked before the real request is processed
    fn collect(&self, ih: &InHeader);
    /// `release()` will be invoked after the real request is processed
    fn release(&self, oh: Option<&OutHeader>);
}

impl<F: FileSystem + Sync> Server<F> {
    /// Main entrance to handle requests from the transport layer.
    ///
    /// It receives Fuse requests from transport layers, parses the request according to Fuse ABI,
    /// invokes filesystem drivers to server the requests, and eventually send back the result to
    /// the transport layer.
    #[allow(unused_variables)]
    #[allow(clippy::cognitive_complexity)]
    pub fn handle_message(
        &self,
        mut r: Reader,
        w: Writer,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
        hook: Option<&dyn MetricsHook>,
    ) -> Result<usize> {
        let in_header: &InHeader = &r.read_obj().map_err(Error::DecodeMessage)?;
        if in_header.len > MAX_BUFFER_SIZE {
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
        }

        trace!(
            "fuse: new req {:?}: {:?}",
            Opcode::from(in_header.opcode),
            in_header
        );

        hook.map_or((), |h| h.collect(&in_header));

        let r = match in_header.opcode {
            x if x == Opcode::Lookup as u32 => self.lookup(in_header, r, w),
            x if x == Opcode::Forget as u32 => self.forget(in_header, r), // No reply.
            x if x == Opcode::Getattr as u32 => self.getattr(in_header, r, w),
            x if x == Opcode::Setattr as u32 => self.setattr(in_header, r, w),
            x if x == Opcode::Readlink as u32 => self.readlink(in_header, w),
            x if x == Opcode::Symlink as u32 => self.symlink(in_header, r, w),
            x if x == Opcode::Mknod as u32 => self.mknod(in_header, r, w),
            x if x == Opcode::Mkdir as u32 => self.mkdir(in_header, r, w),
            x if x == Opcode::Unlink as u32 => self.unlink(in_header, r, w),
            x if x == Opcode::Rmdir as u32 => self.rmdir(in_header, r, w),
            x if x == Opcode::Rename as u32 => self.rename(in_header, r, w),
            x if x == Opcode::Link as u32 => self.link(in_header, r, w),
            x if x == Opcode::Open as u32 => self.open(in_header, r, w),
            x if x == Opcode::Read as u32 => self.read(in_header, r, w),
            x if x == Opcode::Write as u32 => self.write(in_header, r, w),
            x if x == Opcode::Statfs as u32 => self.statfs(in_header, w),
            x if x == Opcode::Release as u32 => self.release(in_header, r, w),
            x if x == Opcode::Fsync as u32 => self.fsync(in_header, r, w),
            x if x == Opcode::Setxattr as u32 => self.setxattr(in_header, r, w),
            x if x == Opcode::Getxattr as u32 => self.getxattr(in_header, r, w),
            x if x == Opcode::Listxattr as u32 => self.listxattr(in_header, r, w),
            x if x == Opcode::Removexattr as u32 => self.removexattr(in_header, r, w),
            x if x == Opcode::Flush as u32 => self.flush(in_header, r, w),
            x if x == Opcode::Init as u32 => self.init(in_header, r, w),
            x if x == Opcode::Opendir as u32 => self.opendir(in_header, r, w),
            x if x == Opcode::Readdir as u32 => self.readdir(in_header, r, w),
            x if x == Opcode::Releasedir as u32 => self.releasedir(in_header, r, w),
            x if x == Opcode::Fsyncdir as u32 => self.fsyncdir(in_header, r, w),
            x if x == Opcode::Getlk as u32 => self.getlk(in_header, r, w),
            x if x == Opcode::Setlk as u32 => self.setlk(in_header, r, w),
            x if x == Opcode::Setlkw as u32 => self.setlkw(in_header, r, w),
            x if x == Opcode::Access as u32 => self.access(in_header, r, w),
            x if x == Opcode::Create as u32 => self.create(in_header, r, w),
            x if x == Opcode::Interrupt as u32 => self.interrupt(in_header),
            x if x == Opcode::Bmap as u32 => self.bmap(in_header, r, w),
            x if x == Opcode::Destroy as u32 => self.destroy(),
            x if x == Opcode::Ioctl as u32 => self.ioctl(in_header, r, w),
            x if x == Opcode::Poll as u32 => self.poll(in_header, r, w),
            x if x == Opcode::NotifyReply as u32 => self.notify_reply(in_header, r, w),
            x if x == Opcode::BatchForget as u32 => self.batch_forget(in_header, r, w),
            x if x == Opcode::Fallocate as u32 => self.fallocate(in_header, r, w),
            x if x == Opcode::Readdirplus as u32 => self.readdirplus(in_header, r, w),
            x if x == Opcode::Rename2 as u32 => self.rename2(in_header, r, w),
            x if x == Opcode::Lseek as u32 => self.lseek(in_header, r, w),
            #[cfg(feature = "virtiofs")]
            x if x == Opcode::SetupMapping as u32 => self.setupmapping(in_header, r, w, vu_req),
            #[cfg(feature = "virtiofs")]
            x if x == Opcode::RemoveMapping as u32 => self.removemapping(in_header, r, w, vu_req),
            _ => reply_error(
                io::Error::from_raw_os_error(libc::ENOSYS),
                in_header.unique,
                w,
            ),
        };
        // Pass `None` because current API handler's design does not allow us to catch
        // the `out_header`. Hopefully, we can reach to `out_header` after some
        // refactoring work someday.
        hook.map_or((), |h| h.release(None));

        r
    }

    fn lookup(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref())?;
        let version = self.vers.load();
        let result = self
            .fs
            .lookup(Context::from(in_header), in_header.nodeid.into(), &name);

        match result {
            // before ABI 7.4 inode == 0 was invalid, only ENOENT means negative dentry
            Ok(entry)
                if version.minor < KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO
                    && entry.inode == 0 =>
            {
                reply_error(
                    io::Error::from_raw_os_error(libc::ENOENT),
                    in_header.unique,
                    w,
                )
            }
            Ok(entry) => {
                let out = EntryOut::from(entry);

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn forget(&self, in_header: &InHeader, mut r: Reader) -> Result<usize> {
        let ForgetIn { nlookup } = r.read_obj().map_err(Error::DecodeMessage)?;

        self.fs
            .forget(Context::from(in_header), in_header.nodeid.into(), nlookup);

        // There is no reply for forget messages.
        Ok(0)
    }

    fn getattr(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let GetattrIn { flags, fh, .. } = r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if (flags & GETATTR_FH) != 0 {
            Some(fh.into())
        } else {
            None
        };
        let result = self
            .fs
            .getattr(Context::from(in_header), in_header.nodeid.into(), handle);

        handle_attr_result(in_header, w, result)
    }

    fn setattr(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let setattr_in: SetattrIn = r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if setattr_in.valid & FATTR_FH != 0 {
            Some(setattr_in.fh.into())
        } else {
            None
        };
        let valid = SetattrValid::from_bits_truncate(setattr_in.valid);
        let st: libc::stat64 = setattr_in.into();
        let result = self.fs.setattr(
            Context::from(in_header),
            in_header.nodeid.into(),
            st,
            handle,
            valid,
        );

        handle_attr_result(in_header, w, result)
    }

    pub(super) fn readlink(&self, in_header: &InHeader, w: Writer) -> Result<usize> {
        match self
            .fs
            .readlink(Context::from(in_header), in_header.nodeid.into())
        {
            Ok(linkname) => {
                // We need to disambiguate the option type here even though it is `None`.
                reply_ok(None::<u8>, Some(&linkname), in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn symlink(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, in_header, 0)?;
        // The name and linkname are encoded one after another and separated by a nul character.
        let (name, linkname) = ServerUtil::extract_two_cstrs(&buf)?;

        match self.fs.symlink(
            Context::from(in_header),
            linkname,
            in_header.nodeid.into(),
            name,
        ) {
            Ok(entry) => reply_ok(Some(EntryOut::from(entry)), None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn mknod(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let MknodIn {
            mode, rdev, umask, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut r, in_header, size_of::<MknodIn>())?;
        let name = bytes_to_cstr(buf.as_ref())?;

        match self.fs.mknod(
            Context::from(in_header),
            in_header.nodeid.into(),
            name,
            mode,
            rdev,
            umask,
        ) {
            Ok(entry) => reply_ok(Some(EntryOut::from(entry)), None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn mkdir(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let MkdirIn { mode, umask } = r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut r, in_header, size_of::<MkdirIn>())?;
        let name = bytes_to_cstr(buf.as_ref())?;

        match self.fs.mkdir(
            Context::from(in_header),
            in_header.nodeid.into(),
            name,
            mode,
            umask,
        ) {
            Ok(entry) => reply_ok(Some(EntryOut::from(entry)), None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn unlink(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref())?;

        match self
            .fs
            .unlink(Context::from(in_header), in_header.nodeid.into(), name)
        {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn rmdir(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref())?;

        match self
            .fs
            .rmdir(Context::from(in_header), in_header.nodeid.into(), name)
        {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn do_rename(
        &self,
        in_header: &InHeader,
        msg_size: usize,
        newdir: u64,
        flags: u32,
        mut r: Reader,
        w: Writer,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, in_header, msg_size)?;
        let (oldname, newname) = ServerUtil::extract_two_cstrs(&buf)?;

        match self.fs.rename(
            Context::from(in_header),
            in_header.nodeid.into(),
            oldname,
            newdir.into(),
            newname,
            flags,
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn rename(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let RenameIn { newdir } = r.read_obj().map_err(Error::DecodeMessage)?;

        self.do_rename(in_header, size_of::<RenameIn>(), newdir, 0, r, w)
    }

    pub(super) fn rename2(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let Rename2In { newdir, flags, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        let flags = flags & (libc::RENAME_EXCHANGE | libc::RENAME_NOREPLACE) as u32;

        self.do_rename(in_header, size_of::<Rename2In>(), newdir, flags, r, w)
    }

    pub(super) fn link(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let LinkIn { oldnodeid } = r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut r, in_header, size_of::<LinkIn>())?;
        let name = bytes_to_cstr(buf.as_ref())?;

        match self.fs.link(
            Context::from(in_header),
            oldnodeid.into(),
            in_header.nodeid.into(),
            name,
        ) {
            Ok(entry) => reply_ok(Some(EntryOut::from(entry)), None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    fn open(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let OpenIn { flags, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self
            .fs
            .open(Context::from(in_header), in_header.nodeid.into(), flags)
        {
            Ok((handle, opts)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    ..Default::default()
                };

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    fn read(&self, in_header: &InHeader, mut r: Reader, mut w: Writer) -> Result<usize> {
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
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
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
        let mut data_writer = ZCWriter(w2);

        match self.fs.read(
            Context::from(in_header),
            in_header.nodeid.into(),
            fh.into(),
            &mut data_writer,
            size,
            offset,
            owner,
            flags,
        ) {
            Ok(count) => {
                // Don't use `reply_ok` because we need to set a custom size length for the
                // header.
                let out = OutHeader {
                    len: (size_of::<OutHeader>() + count) as u32,
                    error: 0,
                    unique: in_header.unique,
                };

                w.write_all(out.as_slice()).map_err(Error::EncodeMessage)?;
                w.commit(Some(&data_writer.0))
                    .map_err(Error::EncodeMessage)?;
                Ok(out.len as usize)
            }
            Err(e) => reply_error_explicit(e, in_header.unique, w),
        }
    }

    fn write(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
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
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
        }

        let owner = if write_flags & WRITE_LOCKOWNER != 0 {
            Some(lock_owner)
        } else {
            None
        };

        let delayed_write = write_flags & WRITE_CACHE != 0;

        let mut data_reader = ZCReader(r);

        match self.fs.write(
            Context::from(in_header),
            in_header.nodeid.into(),
            fh.into(),
            &mut data_reader,
            size,
            offset,
            owner,
            delayed_write,
            flags,
        ) {
            Ok(count) => {
                let out = WriteOut {
                    size: count as u32,
                    ..Default::default()
                };

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error_explicit(e, in_header.unique, w),
        }
    }

    pub(super) fn statfs(&self, in_header: &InHeader, w: Writer) -> Result<usize> {
        match self
            .fs
            .statfs(Context::from(in_header), in_header.nodeid.into())
        {
            Ok(st) => reply_ok(Some(Kstatfs::from(st)), None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn release(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let ReleaseIn {
            fh,
            flags,
            release_flags,
            lock_owner,
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        let flush = release_flags & RELEASE_FLUSH != 0;
        let flock_release = release_flags & RELEASE_FLOCK_UNLOCK != 0;
        let lock_owner = if flush || flock_release {
            Some(lock_owner)
        } else {
            None
        };

        match self.fs.release(
            Context::from(in_header),
            in_header.nodeid.into(),
            flags,
            fh.into(),
            flush,
            flock_release,
            lock_owner,
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    fn fsync(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;

        match self.fs.fsync(
            Context::from(in_header),
            in_header.nodeid.into(),
            datasync,
            fh.into(),
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn setxattr(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let SetxattrIn { size, flags } = r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut r, in_header, size_of::<SetxattrIn>())?;

        // The name and value and encoded one after another and separated by a '\0' character.
        let split_pos = buf
            .iter()
            .position(|c| *c == b'\0')
            .map(|p| p + 1)
            .ok_or(Error::MissingParameter)?;
        let (name, value) = buf.split_at(split_pos);

        if size != value.len() as u32 {
            return Err(Error::InvalidXattrSize((size, value.len())));
        }

        match self.fs.setxattr(
            Context::from(in_header),
            in_header.nodeid.into(),
            bytes_to_cstr(name)?,
            value,
            flags,
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn getxattr(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let GetxattrIn { size, .. } = r.read_obj().map_err(Error::DecodeMessage)?;
        if size > MAX_BUFFER_SIZE {
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
        }

        let buf = ServerUtil::get_message_body(&mut r, in_header, size_of::<GetxattrIn>())?;
        let name = bytes_to_cstr(buf.as_ref())?;

        match self.fs.getxattr(
            Context::from(in_header),
            in_header.nodeid.into(),
            name,
            size,
        ) {
            Ok(GetxattrReply::Value(val)) => reply_ok(None::<u8>, Some(&val), in_header.unique, w),
            Ok(GetxattrReply::Count(count)) => {
                let out = GetxattrOut {
                    size: count,
                    ..Default::default()
                };

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn listxattr(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        w: Writer,
    ) -> Result<usize> {
        let GetxattrIn { size, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        if size > MAX_BUFFER_SIZE {
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
        }

        match self
            .fs
            .listxattr(Context::from(in_header), in_header.nodeid.into(), size)
        {
            Ok(ListxattrReply::Names(val)) => reply_ok(None::<u8>, Some(&val), in_header.unique, w),
            Ok(ListxattrReply::Count(count)) => {
                let out = GetxattrOut {
                    size: count,
                    ..Default::default()
                };

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn removexattr(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        w: Writer,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut r, in_header, 0)?;
        let name = bytes_to_cstr(&buf)?;

        match self
            .fs
            .removexattr(Context::from(in_header), in_header.nodeid.into(), name)
        {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn flush(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let FlushIn { fh, lock_owner, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.flush(
            Context::from(in_header),
            in_header.nodeid.into(),
            fh.into(),
            lock_owner,
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn init(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let InitIn {
            major,
            minor,
            max_readahead,
            flags,
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        if major < KERNEL_VERSION {
            error!("Unsupported fuse protocol version: {}.{}", major, minor);
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::EPROTO),
                in_header.unique,
                w,
            );
        }

        if major > KERNEL_VERSION {
            // Wait for the kernel to reply back with a 7.X version.
            let out = InitOut {
                major: KERNEL_VERSION,
                minor: KERNEL_MINOR_VERSION,
                ..Default::default()
            };

            return reply_ok(Some(out), None, in_header.unique, w);
        }

        // These fuse features are supported by this server by default.
        let supported = FsOptions::ASYNC_READ
            | FsOptions::PARALLEL_DIROPS
            | FsOptions::BIG_WRITES
            | FsOptions::AUTO_INVAL_DATA
            | FsOptions::ASYNC_DIO
            | FsOptions::HAS_IOCTL_DIR
            | FsOptions::MAX_PAGES
            | FsOptions::EXPLICIT_INVAL_DATA
            | FsOptions::ATOMIC_O_TRUNC;

        let capable = FsOptions::from_bits_truncate(flags);

        match self.fs.init(capable) {
            Ok(want) => {
                let enabled = capable & (want | supported);
                info!(
                    "FUSE INIT major {} minor {}\n in_opts: {:?}\nout_opts: {:?}",
                    major, minor, capable, enabled
                );

                let out = InitOut {
                    major: KERNEL_VERSION,
                    minor: KERNEL_MINOR_VERSION,
                    max_readahead,
                    flags: enabled.bits(),
                    max_background: ::std::u16::MAX,
                    congestion_threshold: (::std::u16::MAX / 4) * 3,
                    max_write: MAX_BUFFER_SIZE,
                    time_gran: 1,             // nanoseconds
                    max_pages: MAX_REQ_PAGES, // 1MB
                    ..Default::default()
                };
                let vers = ServerVersion { major, minor };
                self.vers.store(Arc::new(vers));
                if minor < KERNEL_MINOR_VERSION_INIT_OUT_SIZE {
                    reply_ok(
                        Some(
                            *<[u8; FUSE_COMPAT_INIT_OUT_SIZE]>::from_slice(out.as_slice()).unwrap(),
                        ),
                        None,
                        in_header.unique,
                        w,
                    )
                } else if minor < KERNEL_MINOR_VERSION_INIT_22_OUT_SIZE {
                    reply_ok(
                        Some(
                            *<[u8; FUSE_COMPAT_22_INIT_OUT_SIZE]>::from_slice(out.as_slice())
                                .unwrap(),
                        ),
                        None,
                        in_header.unique,
                        w,
                    )
                } else {
                    reply_ok(Some(out), None, in_header.unique, w)
                }
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn opendir(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let OpenIn { flags, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self
            .fs
            .opendir(Context::from(in_header), in_header.nodeid.into(), flags)
        {
            Ok((handle, opts)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    ..Default::default()
                };

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    fn do_readdir(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        mut w: Writer,
        plus: bool,
    ) -> Result<usize> {
        let ReadIn {
            fh, offset, size, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        if size > MAX_BUFFER_SIZE {
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
        }

        let available_bytes = w.available_bytes();
        if available_bytes < size as usize {
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::ENOMEM),
                in_header.unique,
                w,
            );
        }

        // Skip over enough bytes for the header.
        let mut cursor = match w.split_at(size_of::<OutHeader>()) {
            Ok(v) => v,
            Err(_e) => return Err(Error::InvalidHeaderLength),
        };

        let res = if plus {
            self.fs.readdirplus(
                Context::from(in_header),
                in_header.nodeid.into(),
                fh.into(),
                size,
                offset,
                &mut |d, e| add_dirent(&mut cursor, size, d, Some(e)),
            )
        } else {
            self.fs.readdir(
                Context::from(in_header),
                in_header.nodeid.into(),
                fh.into(),
                size,
                offset,
                &mut |d| add_dirent(&mut cursor, size, d, None),
            )
        };

        if let Err(e) = res {
            reply_error_explicit(e, in_header.unique, w)
        } else {
            // Don't use `reply_ok` because we need to set a custom size length for the
            // header.
            let out = OutHeader {
                len: (size_of::<OutHeader>() + cursor.bytes_written()) as u32,
                error: 0,
                unique: in_header.unique,
            };

            w.write_all(out.as_slice()).map_err(Error::EncodeMessage)?;
            w.commit(Some(&cursor)).map_err(Error::EncodeMessage)?;
            Ok(out.len as usize)
        }
    }

    pub(super) fn readdir(&self, in_header: &InHeader, r: Reader, w: Writer) -> Result<usize> {
        self.do_readdir(in_header, r, w, false)
    }

    pub(super) fn readdirplus(&self, in_header: &InHeader, r: Reader, w: Writer) -> Result<usize> {
        self.do_readdir(in_header, r, w, true)
    }

    pub(super) fn releasedir(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        w: Writer,
    ) -> Result<usize> {
        let ReleaseIn { fh, flags, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.releasedir(
            Context::from(in_header),
            in_header.nodeid.into(),
            flags,
            fh.into(),
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    fn fsyncdir(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;

        match self.fs.fsyncdir(
            Context::from(in_header),
            in_header.nodeid.into(),
            datasync,
            fh.into(),
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn getlk(&self, in_header: &InHeader, mut _r: Reader, w: Writer) -> Result<usize> {
        if let Err(e) = self.fs.getlk() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn setlk(&self, in_header: &InHeader, mut _r: Reader, w: Writer) -> Result<usize> {
        if let Err(e) = self.fs.setlk() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn setlkw(&self, in_header: &InHeader, mut _r: Reader, w: Writer) -> Result<usize> {
        if let Err(e) = self.fs.setlkw() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn access(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let AccessIn { mask, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self
            .fs
            .access(Context::from(in_header), in_header.nodeid.into(), mask)
        {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    fn create(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let CreateIn {
            flags, mode, umask, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut r, in_header, size_of::<CreateIn>())?;
        let name = bytes_to_cstr(&buf)?;

        match self.fs.create(
            Context::from(in_header),
            in_header.nodeid.into(),
            name,
            mode,
            flags,
            umask,
        ) {
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
                reply_ok(
                    Some(entry_out),
                    Some(open_out.as_slice()),
                    in_header.unique,
                    w,
                )
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn interrupt(&self, _in_header: &InHeader) -> Result<usize> {
        Ok(0)
    }

    pub(super) fn bmap(&self, in_header: &InHeader, mut _r: Reader, w: Writer) -> Result<usize> {
        if let Err(e) = self.fs.bmap() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn destroy(&self) -> Result<usize> {
        // No reply to this function.
        self.fs.destroy();

        Ok(0)
    }

    pub(super) fn ioctl(&self, in_header: &InHeader, _r: Reader, w: Writer) -> Result<usize> {
        if let Err(e) = self.fs.ioctl() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn poll(&self, in_header: &InHeader, mut _r: Reader, w: Writer) -> Result<usize> {
        if let Err(e) = self.fs.poll() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn notify_reply(
        &self,
        in_header: &InHeader,
        mut _r: Reader,
        w: Writer,
    ) -> Result<usize> {
        if let Err(e) = self.fs.notify_reply() {
            reply_error(e, in_header.unique, w)
        } else {
            Ok(0)
        }
    }

    pub(super) fn batch_forget(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        w: Writer,
    ) -> Result<usize> {
        let BatchForgetIn { count, .. } = r.read_obj().map_err(Error::DecodeMessage)?;

        if let Some(size) = (count as usize).checked_mul(size_of::<ForgetOne>()) {
            if size > MAX_BUFFER_SIZE as usize {
                return reply_error_explicit(
                    io::Error::from_raw_os_error(libc::ENOMEM),
                    in_header.unique,
                    w,
                );
            }
        } else {
            return reply_error_explicit(
                io::Error::from_raw_os_error(libc::EOVERFLOW),
                in_header.unique,
                w,
            );
        }

        let mut requests = Vec::with_capacity(count as usize);
        for _ in 0..count {
            requests.push(
                r.read_obj::<ForgetOne>()
                    .map(|f| (f.nodeid.into(), f.nlookup))
                    .map_err(Error::DecodeMessage)?,
            );
        }

        self.fs.batch_forget(Context::from(in_header), requests);

        // No reply for forget messages.
        Ok(0)
    }

    fn fallocate(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let FallocateIn {
            fh,
            offset,
            length,
            mode,
            ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.fallocate(
            Context::from(in_header),
            in_header.nodeid.into(),
            fh.into(),
            mode,
            offset,
            length,
        ) {
            Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }

    pub(super) fn lseek(&self, in_header: &InHeader, mut r: Reader, w: Writer) -> Result<usize> {
        let LseekIn {
            fh, offset, whence, ..
        } = r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.lseek(
            Context::from(in_header),
            in_header.nodeid.into(),
            fh.into(),
            offset,
            whence,
        ) {
            Ok(offset) => {
                let out = LseekOut { offset };

                reply_ok(Some(out), None, in_header.unique, w)
            }
            Err(e) => reply_error(e, in_header.unique, w),
        }
    }
}

#[cfg(feature = "virtiofs")]
impl<F: FileSystem + Sync> Server<F> {
    pub(super) fn setupmapping(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        w: Writer,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
    ) -> Result<usize> {
        if let Some(req) = vu_req {
            let SetupmappingIn {
                fh,
                foffset,
                len,
                flags,
                moffset,
            } = r.read_obj().map_err(Error::DecodeMessage)?;

            match self.fs.setupmapping(
                Context::from(in_header),
                in_header.nodeid.into(),
                fh.into(),
                foffset,
                len,
                flags,
                moffset,
                req,
            ) {
                Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
                Err(e) => reply_error(e, in_header.unique, w),
            }
        } else {
            reply_error_explicit(
                io::Error::from_raw_os_error(libc::EINVAL),
                in_header.unique,
                w,
            )
        }
    }

    pub(super) fn removemapping(
        &self,
        in_header: &InHeader,
        mut r: Reader,
        w: Writer,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
    ) -> Result<usize> {
        if let Some(req) = vu_req {
            let RemovemappingIn { count } = r.read_obj().map_err(Error::DecodeMessage)?;

            if let Some(size) = (count as usize).checked_mul(size_of::<RemovemappingOne>()) {
                if size > MAX_BUFFER_SIZE as usize {
                    return reply_error_explicit(
                        io::Error::from_raw_os_error(libc::ENOMEM),
                        in_header.unique,
                        w,
                    );
                }
            } else {
                return reply_error_explicit(
                    io::Error::from_raw_os_error(libc::EOVERFLOW),
                    in_header.unique,
                    w,
                );
            }

            let mut requests = Vec::with_capacity(count as usize);
            for _ in 0..count {
                requests.push(
                    r.read_obj::<RemovemappingOne>()
                        .map_err(Error::DecodeMessage)?,
                );
            }

            match self.fs.removemapping(
                Context::from(in_header),
                in_header.nodeid.into(),
                requests,
                req,
            ) {
                Ok(()) => reply_ok(None::<u8>, None, in_header.unique, w),
                Err(e) => reply_error(e, in_header.unique, w),
            }
        } else {
            reply_error_explicit(
                io::Error::from_raw_os_error(libc::EINVAL),
                in_header.unique,
                w,
            )
        }
    }
}

fn reply_ok<T: ByteValued>(
    out: Option<T>,
    data: Option<&[u8]>,
    unique: u64,
    mut w: Writer,
) -> Result<usize> {
    let data2 = out.as_ref().map(|v| v.as_slice()).unwrap_or(&[]);
    let data3 = data.unwrap_or(&[]);
    let len = size_of::<OutHeader>() + data2.len() + data3.len();
    let header = OutHeader {
        len: len as u32,
        error: 0,
        unique,
    };
    trace!("fuse: new reply {:?}", header);

    match (data2.len(), data3.len()) {
        (0, 0) => w.write(header.as_slice()).map_err(Error::EncodeMessage)?,
        (0, _) => w
            .write_vectored(&[IoSlice::new(header.as_slice()), IoSlice::new(data3)])
            .map_err(Error::EncodeMessage)?,
        (_, 0) => w
            .write_vectored(&[IoSlice::new(header.as_slice()), IoSlice::new(data2)])
            .map_err(Error::EncodeMessage)?,
        (_, _) => w
            .write_vectored(&[
                IoSlice::new(header.as_slice()),
                IoSlice::new(data2),
                IoSlice::new(data3),
            ])
            .map_err(Error::EncodeMessage)?,
    };

    debug_assert_eq!(len, w.bytes_written());
    Ok(w.bytes_written())
}

fn do_reply_error(err: io::Error, unique: u64, mut w: Writer, explicit: bool) -> Result<usize> {
    let header = OutHeader {
        len: size_of::<OutHeader>() as u32,
        error: -err
            .raw_os_error()
            .unwrap_or_else(|| encode_io_error_kind(err.kind())),
        unique,
    };

    if explicit {
        error!("fuse: reply error header {:?}, error {:?}", header, err);
    } else {
        trace!("fuse: reply error header {:?}, error {:?}", header, err);
    }
    w.write_all(header.as_slice())
        .map_err(Error::EncodeMessage)?;

    // Commit header if it is buffered otherwise kernel gets nothing back.
    w.commit(None)
        .map(|_| {
            debug_assert_eq!(header.len as usize, w.bytes_written());
            w.bytes_written()
        })
        .map_err(Error::EncodeMessage)
}

// reply operation error back to fuse client, don't print error message, as they are not server's
// internal error, and client could deal with them.
fn reply_error(err: io::Error, unique: u64, w: Writer) -> Result<usize> {
    do_reply_error(err, unique, w, false)
}

fn reply_error_explicit(err: io::Error, unique: u64, w: Writer) -> Result<usize> {
    do_reply_error(err, unique, w, true)
}

fn handle_attr_result(
    in_header: &InHeader,
    w: Writer,
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
            reply_ok(Some(out), None, in_header.unique, w)
        }
        Err(e) => reply_error(e, in_header.unique, w),
    }
}

fn add_dirent(
    cursor: &mut Writer,
    max: u32,
    d: DirEntry,
    entry: Option<Entry>,
) -> io::Result<usize> {
    if d.name.len() > ::std::u32::MAX as usize {
        return Err(io::Error::from_raw_os_error(libc::EOVERFLOW));
    }

    let dirent_len = size_of::<Dirent>()
        .checked_add(d.name.len())
        .ok_or_else(|| io::Error::from_raw_os_error(libc::EOVERFLOW))?;

    // Directory entries must be padded to 8-byte alignment.  If adding 7 causes
    // an overflow then this dirent cannot be properly padded.
    let padded_dirent_len = dirent_len
        .checked_add(7)
        .map(|l| l & !7)
        .ok_or_else(|| io::Error::from_raw_os_error(libc::EOVERFLOW))?;

    let total_len = if entry.is_some() {
        padded_dirent_len
            .checked_add(size_of::<EntryOut>())
            .ok_or_else(|| io::Error::from_raw_os_error(libc::EOVERFLOW))?
    } else {
        padded_dirent_len
    };

    // Skip the entry if there's no enough space left.
    if (max as usize).saturating_sub(cursor.bytes_written()) < total_len {
        Ok(0)
    } else {
        if let Some(entry) = entry {
            cursor.write_all(EntryOut::from(entry).as_slice())?;
        }

        let dirent = Dirent {
            ino: d.ino,
            off: d.offset,
            namelen: d.name.len() as u32,
            type_: d.type_,
        };

        cursor.write_all(dirent.as_slice())?;
        cursor.write_all(d.name)?;

        // We know that `dirent_len` <= `padded_dirent_len` due to the check above
        // so there's no need for checked arithmetic.
        let padding = padded_dirent_len - dirent_len;
        if padding > 0 {
            cursor.write_all(&DIRENT_PADDING[..padding])?;
        }

        Ok(total_len)
    }
}
