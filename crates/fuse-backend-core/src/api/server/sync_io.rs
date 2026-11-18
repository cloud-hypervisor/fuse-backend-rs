// Copyright (C) 2021-2022 Alibaba Cloud. All rights reserved.
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

#[cfg(feature = "fusedev")]
use std::ffi::CStr;
use std::io::{self, IoSlice, Read};
use std::mem::size_of;
use std::sync::atomic::Ordering;
use std::time::Duration;
use vm_memory::ByteValued;

use super::{
    encode_version, takes_reply, InitParams, MetricsHook, Server, ServerUtil, ServerVersion,
    SrvContext, ZcReader, ZcWriter, BUFFER_HEADER_SIZE, DIRENT_PADDING, MAX_BUFFER_SIZE,
    MAX_REQ_PAGES, MIN_READ_BUFFER,
};
use crate::abi::fuse_abi::*;
#[cfg(feature = "virtiofs")]
use crate::abi::virtio_fs::{RemovemappingIn, RemovemappingOne, SetupmappingIn};
use crate::api::filesystem::FsCacheReqHandler;
use crate::api::filesystem::{
    DirEntry, Entry, FileSystem, GetxattrReply, IoctlData, ListxattrReply,
};
use crate::buffer::{pagesize, Reader, Writer};
use crate::{bytes_to_cstr, encode_io_error_kind, BitmapSlice, Error, Result};

/// Parse the request extensions appended by the kernel after the
/// NUL-terminated name(s) of create/mkdir/symlink/mknod requests, and return
/// the first supplementary group carried by a FUSE_EXT_GROUPS extension.
///
/// The kernel sends that extension only when FUSE_CREATE_SUPP_GROUP has been
/// negotiated and one of the caller's supplementary groups matches the parent
/// directory's group, so that objects created in setgid directories can get
/// the correct group ownership.  See `get_create_supp_group()` and
/// `fuse_ext_size()` in `fs/fuse/dir.c` of the Linux kernel.
///
/// The whole extension chain is validated: unknown extension types are
/// skipped, but truncated, inconsistent, unaligned or trailing-garbage
/// payloads are rejected with EINVAL.
pub(super) fn parse_create_extensions(options: &FsOptions, mut tail: &[u8]) -> Result<Option<u32>> {
    const LINUX_NRGROUPS_MAX: u32 = 65536;

    let einval = || Error::DecodeMessage(io::Error::from_raw_os_error(libc::EINVAL));
    let read_u32 = |buf: &[u8]| {
        let mut bytes = [0u8; 4];
        bytes.copy_from_slice(&buf[0..4]);
        u32::from_ne_bytes(bytes)
    };

    // The first group carried by a FUSE_EXT_GROUPS extension; the upstream
    // kernel currently sends a single one.
    let mut supp_gid = None;

    while tail.len() >= size_of::<ExtHeader>() {
        // struct fuse_ext_header { u32 size; u32 type; }.  The extension may
        // start at an unaligned offset, so read the fields manually.
        let size = read_u32(tail) as usize;
        let ext_type = read_u32(&tail[size_of::<u32>()..]);
        if size < size_of::<ExtHeader>() || size > tail.len() {
            return Err(einval());
        }
        // Extensions are padded to an 8-byte boundary, see FUSE_REC_ALIGN
        // and fuse_ext_size() in the kernel.
        if size & 7 != 0 {
            return Err(einval());
        }

        if ext_type == FUSE_EXT_GROUPS {
            // The kernel only appends this extension when FUSE_CREATE_SUPP_GROUP
            // has been negotiated through INIT; reject it otherwise.
            if !options.contains(FsOptions::CREATE_SUPP_GROUP) {
                return Err(einval());
            }

            let body = &tail[size_of::<ExtHeader>()..size];
            // struct fuse_supp_groups { u32 nr_groups; u32 groups[]; }
            if body.len() < size_of::<SuppGroups>() {
                return Err(einval());
            }
            let nr_groups = read_u32(body);
            if nr_groups == 0 || nr_groups > LINUX_NRGROUPS_MAX {
                return Err(einval());
            }
            // Extensions are padded to an 8-byte boundary, see FUSE_REC_ALIGN
            // and fuse_ext_size() in the kernel.
            let expected = size_of::<SuppGroups>() + size_of::<u32>() * nr_groups as usize;
            if body.len() != ((expected + 7) & !7) {
                return Err(einval());
            }
            if supp_gid.is_none() {
                supp_gid = Some(read_u32(&body[size_of::<SuppGroups>()..]));
            }
        }

        tail = &tail[size..];
    }

    // A trailing chunk shorter than an extension header is a protocol violation.
    if !tail.is_empty() {
        return Err(einval());
    }

    Ok(supp_gid)
}

/// The RENAME2 flags that the server passes on to the file system.
pub(super) const RENAME2_FLAGS: u32 = RENAME_EXCHANGE | RENAME_NOREPLACE | RENAME_WHITEOUT;

/// Splits a SETXATTR body into the name, with its '\0', and the value, which has to be `size`
/// bytes long.
pub(super) fn split_setxattr_body(buf: &[u8], size: u32) -> Result<(&[u8], &[u8])> {
    // The name ends at the first '\0', and the value follows it.
    let split_pos = buf
        .iter()
        .position(|c| *c == b'\0')
        .map(|p| p + 1)
        .ok_or(Error::MissingParameter)?;
    let (name, value) = buf.split_at(split_pos);

    if size != value.len() as u32 {
        return Err(Error::InvalidXattrSize((size, value.len())));
    }
    Ok((name, value))
}

/// The `flush`, `flock_release` and `lock_owner` arguments of `release()` for a RELEASE request.
pub(super) fn release_args(release_flags: u32, lock_owner: u64) -> (bool, bool, Option<u64>) {
    let flush = release_flags & RELEASE_FLUSH != 0;
    let flock_release = release_flags & RELEASE_FLOCK_UNLOCK != 0;
    let lock_owner = (flush || flock_release).then_some(lock_owner);
    (flush, flock_release, lock_owner)
}

/// The server's reply to a GETXATTR or LISTXATTR.
pub(super) enum XattrReply {
    /// The length the caller needs, in a `GetxattrOut`.
    Size(u32),
    /// The value or the name list.
    Data(Vec<u8>),
}

impl From<GetxattrReply> for XattrReply {
    fn from(reply: GetxattrReply) -> Self {
        match reply {
            GetxattrReply::Value(data) => XattrReply::Data(data),
            GetxattrReply::Count(size) => XattrReply::Size(size),
        }
    }
}

impl From<ListxattrReply> for XattrReply {
    fn from(reply: ListxattrReply) -> Self {
        match reply {
            ListxattrReply::Names(data) => XattrReply::Data(data),
            ListxattrReply::Count(size) => XattrReply::Size(size),
        }
    }
}

impl XattrReply {
    /// Applies the xattr size rules for a request whose buffer holds `size` bytes, so that the
    /// kernel accepts the reply.
    pub(super) fn fit(self, size: u32) -> io::Result<Self> {
        match self {
            // A zero size asks only for the length. The kernel has no buffer for the data,
            // expects the needed size in a GetxattrOut, and would reject the data with EINVAL.
            XattrReply::Data(data) if size == 0 => Ok(XattrReply::Size(data.len() as u32)),
            // The kernel reads the data straight into the `size` bytes the caller reserved and
            // rejects a longer reply with EINVAL, so answer with the ERANGE the xattr protocol
            // defines for a buffer too small to hold it.
            XattrReply::Data(data) if data.len() > size as usize => {
                Err(io::Error::from_raw_os_error(libc::ERANGE))
            }
            // A nonzero size asks for the data, and a length reply has none. The kernel would
            // copy the 8-byte GetxattrOut out as the data, so answer with the EINVAL it would
            // reject that reply with.
            XattrReply::Size(_) if size != 0 => Err(io::Error::from_raw_os_error(libc::EINVAL)),
            reply => Ok(reply),
        }
    }
}

impl<F: FileSystem + Sync> Server<F> {
    /// Send the notification `code` with the body `parts` through `w`.
    #[cfg(feature = "fusedev")]
    fn notify<W: Writer>(mut w: W, code: NotifyOpcode, parts: &[&[u8]]) -> Result<usize> {
        let len = size_of::<OutHeader>() + parts.iter().map(|part| part.len()).sum::<usize>();
        if len > u32::MAX as usize {
            return Err(Error::EncodeMessage(io::Error::from_raw_os_error(
                libc::EINVAL,
            )));
        }
        let header = OutHeader {
            len: len as u32,
            unique: 0,
            error: code as i32,
        };
        let mut buffer_writer = w.split_at(0).map_err(Error::FailedToSplitWriter)?;
        buffer_writer
            .write_obj(header)
            .map_err(Error::FailedToWrite)?;
        for part in parts {
            buffer_writer
                .write_all(part)
                .map_err(Error::FailedToWrite)?;
        }
        buffer_writer.commit(None).map_err(Error::InvalidMessage)
    }

    #[cfg(feature = "fusedev")]
    fn notify_entry<W: Writer>(w: W, parent: u64, name: &CStr, flags: u32) -> Result<usize> {
        let entry = NotifyInvalEntryOut {
            parent,
            namelen: name.to_bytes().len() as u32,
            flags,
        };
        Self::notify(
            w,
            NotifyOpcode::InvalEntry,
            &[entry.as_slice(), name.to_bytes_with_nul()],
        )
    }

    #[cfg(feature = "fusedev")]
    /// Use to send notify msg to kernel fuse
    ///
    /// The write waits for the lock of `parent`, which a lookup in it holds until its reply, so
    /// don't call this from a thread that serves requests. Any fd of the connection works.
    pub fn notify_inval_entry<W: Writer>(&self, w: W, parent: u64, name: &CStr) -> Result<usize> {
        Self::notify_entry(w, parent, name, 0)
    }

    /// Expire the kernel's entry for `name` in `parent` without dropping it. The kernel looks the
    /// name up again on its next use, and open files and mounts on the entry stay.
    ///
    /// Fails with `ENOSYS` unless the file system enabled `FsOptions::HAS_EXPIRE_ONLY` at INIT,
    /// because an older kernel would drop the entry. The write waits for the lock of `parent`,
    /// as in `notify_inval_entry()`.
    #[cfg(all(feature = "fusedev", target_os = "linux"))]
    pub fn notify_expire_entry<W: Writer>(&self, w: W, parent: u64, name: &CStr) -> Result<usize> {
        let options = FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire));
        if !options.contains(FsOptions::HAS_EXPIRE_ONLY) {
            return Err(Error::EncodeMessage(io::Error::from_raw_os_error(
                libc::ENOSYS,
            )));
        }
        Self::notify_entry(w, parent, name, EXPIRE_ONLY)
    }

    /// Tell the kernel that `name` in `parent`, the inode `child`, was deleted.
    ///
    /// This drops the entry like `notify_inval_entry()`. If the entry is `child`, the kernel also
    /// unlinks it, so its open files get a link count of 0. The kernel fails with `ENOENT` if it
    /// has no such entry or the entry is another inode, `ENOTEMPTY` for a directory with cached
    /// entries, and `EBUSY` for a mount point. The write waits for the locks of `parent` and
    /// `child`, so don't call this from a thread that serves requests.
    #[cfg(feature = "fusedev")]
    pub fn notify_delete<W: Writer>(
        &self,
        w: W,
        parent: u64,
        child: u64,
        name: &CStr,
    ) -> Result<usize> {
        let delete = NotifyDeleteOut {
            parent,
            child,
            namelen: name.to_bytes().len() as u32,
            padding: 0,
        };
        Self::notify(
            w,
            NotifyOpcode::Delete,
            &[delete.as_slice(), name.to_bytes_with_nul()],
        )
    }

    /// Notify the kernel that an inode's data has been invalidated.
    #[cfg(feature = "fusedev")]
    pub fn notify_inval_inode<W: Writer>(
        &self,
        w: W,
        ino: u64,
        off: u64,
        len: u64,
    ) -> Result<usize> {
        let inode = NotifyInvalInodeOut {
            ino,
            off: off as i64,
            len: len as i64,
        };
        Self::notify(w, NotifyOpcode::InvalInode, &[inode.as_slice()])
    }

    /// Put `data` into the kernel's page cache of the regular file `ino`, at `offset`.
    ///
    /// Reads of the stored range don't reach the file system. The exception is a page that wasn't
    /// cached and that the data covers only in part, unless the data runs from the start of that
    /// page to the end of the file. Data past the end of the file grows it. `w` needs room for
    /// `data` and 40 bytes of headers. The kernel fails with `ENOENT` if it has no inode `ino`.
    #[cfg(feature = "fusedev")]
    pub fn notify_store<W: Writer>(
        &self,
        w: W,
        ino: u64,
        offset: u64,
        data: &[u8],
    ) -> Result<usize> {
        let store = NotifyStoreOut {
            nodeid: ino,
            offset,
            size: data.len() as u32,
            padding: 0,
        };
        Self::notify(w, NotifyOpcode::Store, &[store.as_slice(), data])
    }

    /// Ask the kernel for up to `size` bytes of the regular file `ino` from its page cache,
    /// starting at `offset`.
    ///
    /// The kernel answers with a request that the server passes to `FileSystem::notify_reply()`
    /// along with `unique`. The data ends at the first page that isn't cached, at the end of
    /// the file or at the connection's max write size, so it can be shorter than `size` or
    /// empty. The kernel fails with `ENOENT` if it has no inode `ino`.
    #[cfg(feature = "fusedev")]
    pub fn notify_retrieve<W: Writer>(
        &self,
        w: W,
        unique: u64,
        ino: u64,
        offset: u64,
        size: u32,
    ) -> Result<usize> {
        let retrieve = Notify_Retrieve_Out {
            notify_unique: unique,
            nodeid: ino,
            offset,
            size,
            padding: 0,
        };
        Self::notify(w, NotifyOpcode::Retrieve, &[retrieve.as_slice()])
    }

    #[cfg(feature = "fusedev")]
    /// Send a resend notification message to the kernel via FUSE. This function should be invoked as part of
    /// the crash recovery routine. Given that FUSE initialization does not occur again during recovery,
    /// the capability to support resend notifications may not be automatically detected. It is the responsibility
    /// of the upper layers to verify and persist the kernel's support for this feature upon the initial FUSE setup.
    ///
    /// Resent requests have `UNIQUE_RESEND` set in their unique id, which the reply keeps.
    pub fn notify_resend<W: Writer>(&self, w: W) -> Result<()> {
        Self::notify(w, NotifyOpcode::Resend, &[]).map(|_| ())
    }

    /// Make the kernel look up again every entry it cached before this call (Linux 6.16).
    ///
    /// Older kernels fail with `EINVAL`.
    #[cfg(all(feature = "fusedev", target_os = "linux"))]
    pub fn notify_increment_epoch<W: Writer>(&self, w: W) -> Result<usize> {
        Self::notify(w, NotifyOpcode::IncEpoch, &[])
    }

    /// Ask the kernel to drop the unused entries of `inodes` (Linux 6.17), so that it forgets each
    /// inode that no open file or other entry holds.
    ///
    /// Older kernels fail with `EINVAL`.
    #[cfg(all(feature = "fusedev", target_os = "linux"))]
    pub fn notify_prune<W: Writer>(&self, w: W, inodes: &[u64]) -> Result<usize> {
        let prune = NotifyPruneOut {
            count: inodes.len() as u32,
            padding: 0,
            spare: 0,
        };
        let ids: Vec<u8> = inodes.iter().flat_map(|ino| ino.to_ne_bytes()).collect();
        Self::notify(w, NotifyOpcode::Prune, &[prune.as_slice(), &ids])
    }

    /// Main entrance to handle requests from the transport layer.
    ///
    /// It receives Fuse requests from transport layers, parses the request according to Fuse ABI,
    /// invokes filesystem drivers to server the requests, and eventually send back the result to
    /// the transport layer.
    ///
    /// Returns the size of the reply, 0 for DESTROY and for a request that takes none. A request
    /// that fails before it gets a reply is answered with an error, see
    /// `SrvContext::reply_on_error()`, so an error means that the request needed a reply and
    /// didn't get one, or took none and failed.
    pub fn handle_message<S: BitmapSlice, W: Writer>(
        &self,
        mut r: Reader<'_, S>,
        w: W,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
        hook: Option<&dyn MetricsHook>,
    ) -> Result<usize> {
        let in_header: InHeader = r.read_obj().map_err(Error::DecodeMessage)?;
        let mut ctx = SrvContext::<F, S, W>::new(in_header, r, w);
        let res = self.dispatch(&mut ctx, vu_req, hook);
        ctx.reply_on_error(res)
    }

    #[allow(unused_variables)]
    fn dispatch<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
        hook: Option<&dyn MetricsHook>,
    ) -> Result<usize> {
        let in_header = ctx.in_header;
        self.remap_ctx_ids(ctx)?;
        if ctx.in_header.len > (MAX_BUFFER_SIZE + BUFFER_HEADER_SIZE) {
            if !takes_reply(in_header.opcode) {
                return Err(Error::InvalidMessage(io::Error::from_raw_os_error(
                    libc::EOVERFLOW,
                )));
            }
            return ctx.reply_error(io::Error::from_raw_os_error(libc::ENOMEM));
        }

        trace!(
            "fuse: new req {:?}: {:?}",
            Opcode::from(in_header.opcode),
            in_header
        );

        if let Some(h) = hook {
            h.collect(&in_header);
        }

        let res = match in_header.opcode {
            x if x == Opcode::Lookup as u32 => self.lookup(ctx),
            x if x == Opcode::Forget as u32 => self.forget(ctx), // No reply.
            x if x == Opcode::Getattr as u32 => self.getattr(ctx),
            x if x == Opcode::Setattr as u32 => self.setattr(ctx),
            x if x == Opcode::Readlink as u32 => self.readlink(ctx),
            x if x == Opcode::Symlink as u32 => self.symlink(ctx),
            x if x == Opcode::Mknod as u32 => self.mknod(ctx),
            x if x == Opcode::Mkdir as u32 => self.mkdir(ctx),
            x if x == Opcode::Unlink as u32 => self.unlink(ctx),
            x if x == Opcode::Rmdir as u32 => self.rmdir(ctx),
            x if x == Opcode::Rename as u32 => self.rename(ctx),
            x if x == Opcode::Link as u32 => self.link(ctx),
            x if x == Opcode::Open as u32 => self.open(ctx),
            x if x == Opcode::Read as u32 => self.read(ctx),
            x if x == Opcode::Write as u32 => self.write(ctx),
            x if x == Opcode::Statfs as u32 => self.statfs(ctx),
            x if x == Opcode::Release as u32 => self.release(ctx),
            x if x == Opcode::Fsync as u32 => self.fsync(ctx),
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
            x if x == Opcode::Opendir as u32 => self.opendir(ctx),
            x if x == Opcode::Readdir as u32 => self.readdir(ctx),
            x if x == Opcode::Releasedir as u32 => self.releasedir(ctx),
            x if x == Opcode::Fsyncdir as u32 => self.fsyncdir(ctx),
            x if x == Opcode::Getlk as u32 => self.getlk(ctx),
            x if x == Opcode::Setlk as u32 => self.setlk(ctx),
            x if x == Opcode::Setlkw as u32 => self.setlkw(ctx),
            x if x == Opcode::Access as u32 => self.access(ctx),
            x if x == Opcode::Create as u32 => self.create(ctx),
            x if x == Opcode::Bmap as u32 => self.bmap(ctx),
            x if x == Opcode::Ioctl as u32 => self.ioctl(ctx),
            x if x == Opcode::Poll as u32 => self.poll(ctx),
            x if x == Opcode::NotifyReply as u32 => self.notify_reply(ctx),
            x if x == Opcode::BatchForget as u32 => self.batch_forget(ctx),
            x if x == Opcode::Fallocate as u32 => self.fallocate(ctx),
            x if x == Opcode::Readdirplus as u32 => self.readdirplus(ctx),
            x if x == Opcode::Rename2 as u32 => self.rename2(ctx),
            x if x == Opcode::Lseek as u32 => self.lseek(ctx),
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
                _ => ctx.reply_error(io::Error::from_raw_os_error(libc::ENOSYS)),
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

    fn lookup<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        #[cfg(not(feature = "fuse-t"))]
        let version = super::decode_version(self.vers.load(Ordering::Acquire));
        let result = self.fs.lookup(ctx.context(), ctx.nodeid(), name);

        match result {
            // before ABI 7.4 inode == 0 was invalid, only ENOENT means negative dentry
            #[cfg(not(feature = "fuse-t"))]
            Ok(entry)
                if version.minor < KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO
                    && entry.inode == 0 =>
            {
                ctx.reply_error(io::Error::from_raw_os_error(libc::ENOENT))
            }
            #[cfg(feature = "fuse-t")]
            Ok(entry) if entry.inode == 0 => {
                ctx.reply_error(io::Error::from_raw_os_error(libc::ENOENT))
            }
            Ok(entry) => {
                let out = EntryOut::from(entry);

                ctx.reply_ok(Some(out), None)
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn forget<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let ForgetIn { nlookup } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        self.fs.forget(ctx.context(), ctx.nodeid(), nlookup);

        // There is no reply for forget messages.
        Ok(0)
    }

    fn getattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let GetattrIn { flags, fh, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let handle = if (flags & GETATTR_FH) != 0 {
            Some(fh.into())
        } else {
            None
        };
        let result = self.fs.getattr(ctx.context(), ctx.nodeid(), handle);

        ctx.handle_attr_result(result)
    }

    fn setattr<S: BitmapSlice, W: Writer>(
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
            .setattr(ctx.context(), ctx.nodeid(), st, handle, valid);

        ctx.handle_attr_result(result)
    }

    fn readlink<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        match self.fs.readlink(ctx.context(), ctx.nodeid()) {
            Ok(linkname) => {
                // We need to disambiguate the option type here even though it is `None`.
                ctx.reply_ok(None::<u8>, Some(&linkname))
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    fn symlink<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        // The name and linkname are encoded one after another and separated by a nul character.
        let (name, linkname) = ServerUtil::extract_two_cstrs(&buf)?;
        let supp_gid = parse_create_extensions(
            &FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire)),
            &buf[name.to_bytes_with_nul().len() + linkname.to_bytes_with_nul().len()..],
        )?;
        ctx.context.supp_gid = supp_gid;

        match self.fs.symlink(ctx.context(), linkname, ctx.nodeid(), name) {
            Ok(entry) => ctx.reply_ok(Some(EntryOut::from(entry)), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn mknod<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let MknodIn {
            mode, rdev, umask, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<MknodIn>())?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;
        let supp_gid = parse_create_extensions(
            &FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire)),
            &buf[name.to_bytes_with_nul().len()..],
        )?;
        ctx.context.supp_gid = supp_gid;

        match self
            .fs
            .mknod(ctx.context(), ctx.nodeid(), name, mode, rdev, umask)
        {
            Ok(entry) => ctx.reply_ok(Some(EntryOut::from(entry)), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn mkdir<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let MkdirIn { mode, umask } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<MkdirIn>())?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;
        let supp_gid = parse_create_extensions(
            &FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire)),
            &buf[name.to_bytes_with_nul().len()..],
        )?;
        ctx.context.supp_gid = supp_gid;

        match self
            .fs
            .mkdir(ctx.context(), ctx.nodeid(), name, mode, umask)
        {
            Ok(entry) => ctx.reply_ok(Some(EntryOut::from(entry)), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn unlink<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        match self.fs.unlink(ctx.context(), ctx.nodeid(), name) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn rmdir<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        match self.fs.rmdir(ctx.context(), ctx.nodeid(), name) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn do_rename<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        msg_size: usize,
        newdir: u64,
        flags: u32,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, msg_size)?;
        let (oldname, newname) = ServerUtil::extract_two_cstrs(&buf)?;

        match self.fs.rename(
            ctx.context(),
            ctx.nodeid(),
            oldname,
            newdir.into(),
            newname,
            flags,
        ) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn rename<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let RenameIn { newdir, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        self.do_rename(ctx, size_of::<RenameIn>(), newdir, 0)
    }

    fn rename2<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let Rename2In { newdir, flags, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let flags = flags & RENAME2_FLAGS;

        self.do_rename(ctx, size_of::<Rename2In>(), newdir, flags)
    }

    fn link<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let LinkIn { oldnodeid } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<LinkIn>())?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        match self
            .fs
            .link(ctx.context(), oldnodeid.into(), ctx.nodeid(), name)
        {
            Ok(entry) => ctx.reply_ok(Some(EntryOut::from(entry)), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn open<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let OpenIn { flags, fuse_flags } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.open(ctx.context(), ctx.nodeid(), flags, fuse_flags) {
            Ok((handle, opts, passthrough)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    passthrough: passthrough.unwrap_or_default(),
                };

                ctx.reply_ok(Some(out), None)
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    fn read<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
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
        let mut data_writer = ZcWriter(w2);

        match self.fs.read(
            ctx.context(),
            ctx.nodeid(),
            fh.into(),
            &mut data_writer,
            size,
            offset,
            owner,
            flags,
        ) {
            Ok(count) => ctx.reply_with_data(&data_writer.0, count),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn write<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let WriteIn {
            fh,
            offset,
            size,
            fuse_flags,
            lock_owner,
            flags,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let owner = if fuse_flags & WRITE_LOCKOWNER != 0 {
            Some(lock_owner)
        } else {
            None
        };

        let delayed_write = fuse_flags & WRITE_CACHE != 0;

        let mut data_reader = ZcReader(ctx.take_reader());

        match self.fs.write(
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
        ) {
            Ok(count) => {
                let out = WriteOut {
                    size: count as u32,
                    ..Default::default()
                };

                ctx.reply_ok(Some(out), None)
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    fn statfs<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        match self.fs.statfs(ctx.context(), ctx.nodeid()) {
            Ok(st) => ctx.reply_ok(Some(Kstatfs::from(st)), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn release<S: BitmapSlice, W: Writer>(
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

        match self.fs.release(
            ctx.context(),
            ctx.nodeid(),
            flags,
            fh.into(),
            flush,
            flock_release,
            lock_owner,
        ) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn fsync<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;

        match self
            .fs
            .fsync(ctx.context(), ctx.nodeid(), datasync, fh.into())
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn setxattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let SetxattrIn { size, flags } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf =
            ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<SetxattrIn>())?;

        let (name, value) = split_setxattr_body(&buf, size)?;
        let name = bytes_to_cstr(name).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        match self
            .fs
            .setxattr(ctx.context(), ctx.nodeid(), name, value, flags)
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn getxattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let GetxattrIn { size, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let buf =
            ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<GetxattrIn>())?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        let result = self.fs.getxattr(ctx.context(), ctx.nodeid(), name, size);
        ctx.handle_xattr_result(size, result)
    }

    fn listxattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let GetxattrIn { size, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let result = self.fs.listxattr(ctx.context(), ctx.nodeid(), size);
        ctx.handle_xattr_result(size, result)
    }

    fn removexattr<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, 0)?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;

        match self.fs.removexattr(ctx.context(), ctx.nodeid(), name) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn flush<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let FlushIn { fh, lock_owner, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self
            .fs
            .flush(ctx.context(), ctx.nodeid(), fh.into(), lock_owner)
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn init<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        mut on_init_params: impl FnMut(&InitParams),
    ) -> Result<usize> {
        let InitIn {
            major,
            minor,
            max_readahead,
            flags,
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        if major < KERNEL_VERSION {
            debug!("Unsupported fuse protocol version: {}.{}", major, minor);
            return ctx.reply_error(io::Error::from_raw_os_error(libc::EPROTO));
        }

        if major > KERNEL_VERSION {
            // Wait for the kernel to reply back with a 7.X version.
            let out = InitOut {
                major: KERNEL_VERSION,
                minor: KERNEL_MINOR_VERSION,
                ..Default::default()
            };

            return ctx.reply_ok(Some(out), None);
        }

        #[cfg(any(target_os = "macos", target_os = "freebsd"))]
        let flags_u64 = flags as u64;
        #[cfg(target_os = "linux")]
        let mut flags_u64 = flags as u64;
        #[cfg(target_os = "linux")]
        if flags_u64 & FsOptions::INIT_EXT.bits() != 0 {
            if ctx.r.available_bytes() >= size_of::<InitIn2>() {
                let InitIn2 { flags2, unused: _ } =
                    ctx.r.read_obj().map_err(Error::DecodeMessage)?;
                flags_u64 |= (flags2 as u64) << 32;
            } else {
                // Some kernels set INIT_EXT without appending the InitIn2 payload.
                // Fall back to the legacy 32-bit flag set instead of failing init.
                flags_u64 &= !FsOptions::INIT_EXT.bits();
            }
        }
        let capable = FsOptions::from_bits_truncate(flags_u64);

        match self.fs.init(capable) {
            Ok(want) => {
                let version = ServerVersion { major, minor };
                on_init_params(&InitParams {
                    version: version.clone(),
                    capable,
                    want,
                });

                let readahead = if cfg!(target_os = "macos") {
                    0
                } else {
                    max_readahead
                };

                let enabled = capable & want;
                #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
                let enabled = self.apply_extra_init_flags(capable, enabled);
                // Capability bits 32 and above (FUSE_SECURITY_CTX,
                // FUSE_CREATE_SUPP_GROUP, ...) travel in flags2 of the reply,
                // and the kernel applies flags2 only when the daemon also sets
                // FUSE_INIT_EXT in flags (see process_init_reply() in
                // fs/fuse/inode.c).  Echo the flag whenever any upper bit is
                // enabled, or the kernel would silently drop the whole flags2
                // set.  This stays Linux-only: the extended flag set is a
                // Linux protocol concept, and macFUSE assigns INIT_EXT's bit
                // 30 to its own VOL_RENAME capability, so echoing or parsing
                // it there would corrupt the macFUSE handshake.
                #[cfg(target_os = "linux")]
                let enabled = if enabled.bits() >> 32 != 0 {
                    enabled | FsOptions::INIT_EXT
                } else {
                    enabled
                };
                self.options.store(enabled.bits(), Ordering::Release);
                let enabled_flags = enabled.bits();
                let mut out = InitOut {
                    major: KERNEL_VERSION,
                    minor: KERNEL_MINOR_VERSION,
                    max_readahead: readahead,
                    flags: enabled_flags as u32,
                    max_background: u16::MAX,
                    congestion_threshold: (u16::MAX / 4) * 3,
                    max_write: MIN_READ_BUFFER - BUFFER_HEADER_SIZE,
                    time_gran: 1, // nanoseconds
                    flags2: (enabled_flags >> 32) as u32,
                    ..Default::default()
                };
                if enabled.contains(FsOptions::BIG_WRITES) {
                    out.max_write = MAX_REQ_PAGES as u32 * pagesize() as u32;
                }
                if enabled.contains(FsOptions::MAX_PAGES) {
                    out.max_pages = MAX_REQ_PAGES;
                    out.max_write = MAX_REQ_PAGES as u32 * pagesize() as u32; // 1MB
                }
                if enabled.contains(FsOptions::PASSTHROUGH) {
                    out.max_stack_depth = self.max_stack_depth.load(Ordering::Relaxed);
                }
                #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
                self.record_uring_init(flags_u64, out.max_write, out.max_pages);
                self.vers.store(
                    encode_version(version.major, version.minor),
                    Ordering::Release,
                );
                if minor < KERNEL_MINOR_VERSION_INIT_OUT_SIZE {
                    ctx.reply_ok(
                        Some(
                            *<[u8; FUSE_COMPAT_INIT_OUT_SIZE]>::from_slice(
                                out.as_slice().split_at(FUSE_COMPAT_INIT_OUT_SIZE).0,
                            )
                            .unwrap(),
                        ),
                        None,
                    )
                } else if cfg!(target_os = "macos") || minor < KERNEL_MINOR_VERSION_INIT_22_OUT_SIZE
                {
                    // macFUSE's fuse_init_out never grew past the 24-byte
                    // FUSE_COMPAT_22 shape: its libfuse replies
                    // `arg->minor < 5 ? 8 : sizeof(outarg)` however new a
                    // minor version the client advertises.  That reply size
                    // is wire-visible -- fuse-t 1.2.x reads it to tell
                    // macFUSE-profile daemons from libfuse3 ones, and a
                    // 64-byte Linux-shaped reply makes it negotiate the
                    // libfuse3 profile and parse every later reply with
                    // Linux field offsets, garbling our macFUSE-shaped
                    // fuse_attr (CI caught it reading a directory's mode as
                    // Gid).  So on macOS the full-struct branch below is
                    // unreachable by design.
                    ctx.reply_ok(
                        Some(
                            *<[u8; FUSE_COMPAT_22_INIT_OUT_SIZE]>::from_slice(
                                out.as_slice().split_at(FUSE_COMPAT_22_INIT_OUT_SIZE).0,
                            )
                            .unwrap(),
                        ),
                        None,
                    )
                } else {
                    ctx.reply_ok(Some(out), None)
                }
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    fn opendir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let OpenIn { flags, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.opendir(ctx.context(), ctx.nodeid(), flags) {
            Ok((handle, opts)) => {
                let out = OpenOut {
                    fh: handle.map(Into::into).unwrap_or(0),
                    open_flags: opts.bits(),
                    ..Default::default()
                };

                ctx.reply_ok(Some(out), None)
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    fn do_readdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        plus: bool,
    ) -> Result<usize> {
        let ReadIn {
            fh, offset, size, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        let mut cursor = match ctx.dirent_cursor(size)? {
            Some(cursor) => cursor,
            None => return ctx.reply_error(io::Error::from_raw_os_error(libc::ENOMEM)),
        };

        let res = if plus {
            self.fs.readdirplus(
                ctx.context(),
                ctx.nodeid(),
                fh.into(),
                size,
                offset,
                &mut |d, e| add_dirent(&mut cursor, size, d, Some(e)),
            )
        } else {
            self.fs.readdir(
                ctx.context(),
                ctx.nodeid(),
                fh.into(),
                size,
                offset,
                &mut |d| add_dirent(&mut cursor, size, d, None),
            )
        };

        if let Err(e) = res {
            ctx.reply_error_explicit(e)
        } else {
            ctx.reply_with_data(&cursor, cursor.bytes_written())
        }
    }

    fn readdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        self.do_readdir(ctx, false)
    }

    fn readdirplus<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        self.do_readdir(ctx, true)
    }

    fn releasedir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let ReleaseIn { fh, flags, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self
            .fs
            .releasedir(ctx.context(), ctx.nodeid(), flags, fh.into())
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn fsyncdir<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let FsyncIn {
            fh, fsync_flags, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let datasync = fsync_flags & 0x1 != 0;

        match self
            .fs
            .fsyncdir(ctx.context(), ctx.nodeid(), datasync, fh.into())
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn getlk<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let LkIn {
            fh,
            owner,
            lk,
            lk_flags,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        match self.fs.getlk(
            ctx.context(),
            ctx.nodeid(),
            fh.into(),
            owner,
            lk.into(),
            lk_flags,
        ) {
            Ok(l) => ctx.reply_ok(Some(LkOut { lk: l.into() }), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn setlk<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let LkIn {
            fh,
            owner,
            lk,
            lk_flags,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        match self.fs.setlk(
            ctx.context(),
            ctx.nodeid(),
            fh.into(),
            owner,
            lk.into(),
            lk_flags,
        ) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn setlkw<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let LkIn {
            fh,
            owner,
            lk,
            lk_flags,
            ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        match self.fs.setlk(
            ctx.context(),
            ctx.nodeid(),
            fh.into(),
            owner,
            lk.into(),
            lk_flags,
        ) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn access<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let AccessIn { mask, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.access(ctx.context(), ctx.nodeid(), mask) {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn create<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let args: CreateIn = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        let buf = ServerUtil::get_message_body(&mut ctx.r, &ctx.in_header, size_of::<CreateIn>())?;
        let name = bytes_to_cstr(buf.as_ref()).map_err(|e| {
            debug!("fuse: bytes to cstr error: {:?}, {:?}", buf, e);
            e
        })?;
        let supp_gid = parse_create_extensions(
            &FsOptions::from_bits_truncate(self.options.load(Ordering::Acquire)),
            &buf[name.to_bytes_with_nul().len()..],
        )?;
        ctx.context.supp_gid = supp_gid;

        match self.fs.create(ctx.context(), ctx.nodeid(), name, args) {
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
                ctx.reply_ok(Some(entry_out), Some(open_out.as_slice()))
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn interrupt<S: BitmapSlice, W: Writer>(&self, _ctx: &mut SrvContext<'_, F, S, W>) {}

    pub(super) fn bmap<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let BmapIn {
            block, blocksize, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.bmap(ctx.context(), ctx.nodeid(), block, blocksize) {
            Ok(block) => ctx.reply_ok(Some(BmapOut { block }), None),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn destroy<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) {
        self.fs.destroy();
        if let Err(e) = ctx.reply_ok(None::<u8>, None) {
            warn!("fuse channel reply destroy failed {:?}", e);
        }
    }

    pub(super) fn ioctl<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let IoctlIn {
            fh,
            flags,
            cmd,
            arg: _,
            in_size,
            out_size,
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        // TODO: check fs capability of FUSE_CAP_IOCTL_DIR and return ENOTTY if unsupported.
        let mut buf = IoctlData {
            ..Default::default()
        };
        let in_size = in_size as usize;
        // Make sure we have enough bytes to read the ioctl in buffer.
        if in_size > ctx.r.available_bytes() {
            return ctx.reply_error(io::Error::from_raw_os_error(libc::ENOTTY));
        }
        let mut data = vec![0u8; in_size];
        if in_size > 0 {
            let size = ctx.r.read(&mut data).map_err(Error::DecodeMessage)?;
            if size > 0 {
                buf.data = Some(&data[..size]);
            }
        }
        match self.fs.ioctl(
            ctx.context(),
            ctx.nodeid(),
            fh.into(),
            flags,
            cmd,
            buf,
            out_size,
        ) {
            Ok(res) => ctx.reply_ok(
                Some(IoctlOut {
                    result: res.result,
                    ..Default::default()
                }),
                res.data,
            ),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn poll<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let PollIn {
            fh,
            kh,
            flags,
            events,
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self.fs.poll(
            ctx.context(),
            ctx.nodeid(),
            fh.into(),
            kh.into(),
            flags,
            events,
        ) {
            Ok(revents) => ctx.reply_ok(
                Some(PollOut {
                    revents,
                    padding: 0,
                }),
                None,
            ),
            Err(e) => ctx.reply_error(e),
        }
    }

    pub(super) fn notify_reply<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        // NOTIFY_REPLY takes no reply. It comes under the unique number that the server picked
        // for NOTIFY_RETRIEVE, so a reply could even end another request.
        let NotifyRetrieveIn { offset, size, .. } =
            ctx.r.read_obj().map_err(Error::DecodeMessage)?;
        if size as usize > ctx.r.available_bytes() {
            return Err(Error::DecodeMessage(io::Error::from_raw_os_error(
                libc::EINVAL,
            )));
        }
        let mut data_reader = ZcReader(ctx.take_reader());
        self.fs.notify_reply(
            ctx.context(),
            ctx.nodeid(),
            ctx.unique(),
            offset,
            size,
            &mut data_reader,
        );
        Ok(0)
    }

    pub(super) fn batch_forget<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
    ) -> Result<usize> {
        let BatchForgetIn { count, .. } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        if let Some(size) = (count as usize).checked_mul(size_of::<ForgetOne>()) {
            if size
                > (MAX_BUFFER_SIZE + BUFFER_HEADER_SIZE
                    - size_of::<BatchForgetIn>() as u32
                    - size_of::<InHeader>() as u32) as usize
            {
                return Err(Error::InvalidMessage(io::Error::from_raw_os_error(
                    libc::EOVERFLOW,
                )));
            }
        } else {
            return Err(Error::InvalidMessage(io::Error::from_raw_os_error(
                libc::EOVERFLOW,
            )));
        }

        let mut requests = Vec::with_capacity(count as usize);
        for _ in 0..count {
            requests.push(
                ctx.r
                    .read_obj::<ForgetOne>()
                    .map(|f| (f.nodeid.into(), f.nlookup))
                    .map_err(Error::DecodeMessage)?,
            );
        }

        self.fs.batch_forget(ctx.context(), requests);

        // No reply for forget messages.
        Ok(0)
    }

    fn fallocate<S: BitmapSlice, W: Writer>(
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

        match self
            .fs
            .fallocate(ctx.context(), ctx.nodeid(), fh.into(), mode, offset, length)
        {
            Ok(()) => ctx.reply_ok(None::<u8>, None),
            Err(e) => ctx.reply_error(e),
        }
    }

    fn lseek<S: BitmapSlice, W: Writer>(&self, ctx: &mut SrvContext<'_, F, S, W>) -> Result<usize> {
        let LseekIn {
            fh, offset, whence, ..
        } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

        match self
            .fs
            .lseek(ctx.context(), ctx.nodeid(), fh.into(), offset, whence)
        {
            Ok(offset) => {
                let out = LseekOut { offset };

                ctx.reply_ok(Some(out), None)
            }
            Err(e) => ctx.reply_error(e),
        }
    }

    fn copy_file_range<S: BitmapSlice, W: Writer>(
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

        match self.fs.copy_file_range(
            ctx.context(),
            ctx.nodeid(),
            fh_in.into(),
            offset_in,
            nodeid_out.into(),
            fh_out.into(),
            offset_out,
            len,
            flags,
        ) {
            Ok(count) => {
                let out = WriteOut {
                    size: count,
                    ..Default::default()
                };

                ctx.reply_ok(Some(out), None)
            }
            Err(e) => ctx.reply_error(e),
        }
    }
}

#[cfg(feature = "virtiofs")]
impl<F: FileSystem + Sync> Server<F> {
    pub(super) fn setupmapping<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
    ) -> Result<usize> {
        if let Some(req) = vu_req {
            let SetupmappingIn {
                fh,
                foffset,
                len,
                flags,
                moffset,
            } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

            match self.fs.setupmapping(
                ctx.context(),
                ctx.nodeid(),
                fh.into(),
                foffset,
                len,
                flags,
                moffset,
                req,
            ) {
                Ok(()) => ctx.reply_ok(None::<u8>, None),
                Err(e) => ctx.reply_error(e),
            }
        } else {
            ctx.reply_error(io::Error::from_raw_os_error(libc::EINVAL))
        }
    }

    pub(super) fn removemapping<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<'_, F, S, W>,
        vu_req: Option<&mut dyn FsCacheReqHandler>,
    ) -> Result<usize> {
        if let Some(req) = vu_req {
            let RemovemappingIn { count } = ctx.r.read_obj().map_err(Error::DecodeMessage)?;

            if let Some(size) = (count as usize).checked_mul(size_of::<RemovemappingOne>()) {
                if size > MAX_BUFFER_SIZE as usize {
                    return ctx.reply_error(io::Error::from_raw_os_error(libc::ENOMEM));
                }
            } else {
                return ctx.reply_error(io::Error::from_raw_os_error(libc::EOVERFLOW));
            }

            let mut requests = Vec::with_capacity(count as usize);
            for _ in 0..count {
                requests.push(
                    ctx.r
                        .read_obj::<RemovemappingOne>()
                        .map_err(Error::DecodeMessage)?,
                );
            }

            match self
                .fs
                .removemapping(ctx.context(), ctx.nodeid(), requests, req)
            {
                Ok(()) => ctx.reply_ok(None::<u8>, None),
                Err(e) => ctx.reply_error(e),
            }
        } else {
            ctx.reply_error(io::Error::from_raw_os_error(libc::EINVAL))
        }
    }
}

impl<F: FileSystem, S: BitmapSlice, W: Writer> SrvContext<'_, F, S, W> {
    fn reply_ok<T: ByteValued>(&mut self, out: Option<T>, data: Option<&[u8]>) -> Result<usize> {
        let data2 = out.as_ref().map(|v| v.as_slice()).unwrap_or(&[]);
        let data3 = data.unwrap_or(&[]);
        let len = size_of::<OutHeader>() + data2.len() + data3.len();
        let header = OutHeader {
            len: len as u32,
            error: 0,
            unique: self.unique(),
        };
        trace!("fuse: new reply {:?}", header);

        self.replied = true;
        match (data2.len(), data3.len()) {
            (0, 0) => self
                .w
                .write(header.as_slice())
                .map_err(Error::EncodeMessage)?,
            (0, _) => self
                .w
                .write_vectored(&[IoSlice::new(header.as_slice()), IoSlice::new(data3)])
                .map_err(Error::EncodeMessage)?,
            (_, 0) => self
                .w
                .write_vectored(&[IoSlice::new(header.as_slice()), IoSlice::new(data2)])
                .map_err(Error::EncodeMessage)?,
            (_, _) => self
                .w
                .write_vectored(&[
                    IoSlice::new(header.as_slice()),
                    IoSlice::new(data2),
                    IoSlice::new(data3),
                ])
                .map_err(Error::EncodeMessage)?,
        };

        debug_assert_eq!(len, self.w.bytes_written());
        Ok(self.w.bytes_written())
    }

    fn do_reply_error(&mut self, err: io::Error, explicit: bool) -> Result<usize> {
        let header = OutHeader {
            len: size_of::<OutHeader>() as u32,
            error: -err
                .raw_os_error()
                .unwrap_or_else(|| encode_io_error_kind(err.kind())),
            unique: self.unique(),
        };

        if explicit || err.raw_os_error().is_none() {
            error!("fuse: reply error header {:?}, error {:?}", header, err);
        } else {
            trace!("fuse: reply error header {:?}, error {:?}", header, err);
        }
        self.replied = true;
        self.w
            .write_all(header.as_slice())
            .map_err(Error::EncodeMessage)?;

        // Commit header if it is buffered otherwise kernel gets nothing back.
        self.w
            .commit(None)
            .map(|_| {
                debug_assert_eq!(header.len as usize, self.w.bytes_written());
                self.w.bytes_written()
            })
            .map_err(Error::EncodeMessage)
    }

    // reply operation error back to fuse client, don't print error message, as they are not server's
    // internal error, and client could deal with them.
    fn reply_error(&mut self, err: io::Error) -> Result<usize> {
        self.do_reply_error(err, false)
    }

    fn reply_error_explicit(&mut self, err: io::Error) -> Result<usize> {
        self.do_reply_error(err, true)
    }

    /// Replies with the `data_len` bytes that a READ or READDIR handler wrote to `data_writer`,
    /// the part of the reply buffer after the `OutHeader`. Writes the header and commits it
    /// together with the data.
    fn reply_with_data(&mut self, data_writer: &W, data_len: usize) -> Result<usize> {
        let header = OutHeader {
            len: (size_of::<OutHeader>() + data_len) as u32,
            error: 0,
            unique: self.unique(),
        };

        self.replied = true;
        self.w
            .write_all(header.as_slice())
            .map_err(Error::EncodeMessage)?;
        self.w
            .commit(Some(data_writer))
            .map_err(Error::EncodeMessage)?;
        Ok(header.len as usize)
    }

    /// Answers a request that failed before it got a reply, because FUSE has no request timeout
    /// and the client would wait forever. Returns the size of that reply, as for any other
    /// error reply. A transport treats an error as a request without a reply, and a virtio-fs
    /// device then never returns the descriptor.
    pub(super) fn reply_on_error(&mut self, res: Result<usize>) -> Result<usize> {
        match res {
            Err(e) => match self.fallback_errno(&e) {
                Some(errno) => self.reply_error(io::Error::from_raw_os_error(errno)),
                None => Err(e),
            },
            ok => ok,
        }
    }

    /// Splits the reply buffer of a READDIR or READDIRPLUS request after the `OutHeader`, and
    /// returns the part that `add_dirent()` writes the entries to. Returns `None` if the buffer
    /// can't hold the `size` bytes of entries that the request asks for.
    pub(super) fn dirent_cursor(&mut self, size: u32) -> Result<Option<W>> {
        // The entries go after the reply header.
        if self.w.available_bytes() < size_of::<OutHeader>() + size as usize {
            return Ok(None);
        }

        self.w
            .split_at(size_of::<OutHeader>())
            .map(Some)
            .map_err(Error::FailedToSplitWriter)
    }

    fn handle_attr_result(&mut self, result: io::Result<(stat64, Duration)>) -> Result<usize> {
        match result {
            Ok((st, timeout)) => {
                let out = AttrOut {
                    attr_valid: timeout.as_secs(),
                    attr_valid_nsec: timeout.subsec_nanos(),
                    dummy: 0,
                    attr: st.into(),
                };
                self.reply_ok(Some(out), None)
            }
            Err(e) => self.reply_error(e),
        }
    }

    /// Replies to a GETXATTR or LISTXATTR whose buffer holds `size` bytes.
    ///
    /// `async_handle_xattr_result()` in async_io.rs has the same reply policy
    /// with the async reply calls. Change the two together.
    fn handle_xattr_result(
        &mut self,
        size: u32,
        result: io::Result<impl Into<XattrReply>>,
    ) -> Result<usize> {
        match result.map(Into::into).and_then(|reply| reply.fit(size)) {
            Ok(XattrReply::Data(data)) => self.reply_ok(None::<u8>, Some(&data)),
            Ok(XattrReply::Size(size)) => {
                let out = GetxattrOut {
                    size,
                    ..Default::default()
                };
                self.reply_ok(Some(out), None)
            }
            Err(e) => self.reply_error(e),
        }
    }
}

/// Adds a directory entry, and `entry` for READDIRPLUS, to the reply in `cursor`. Returns the
/// number of bytes added, or 0 if the entry doesn't fit in `max` bytes.
pub(super) fn add_dirent<W: Writer>(
    cursor: &mut W,
    max: u32,
    d: DirEntry,
    entry: Option<Entry>,
) -> io::Result<usize> {
    if d.name.len() > u32::MAX as usize {
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

// The server operation tests only exercise the server side request parsing
// and reply encoding logic, so they run against an empty mock filesystem and
// a writer capturing replies into a plain byte buffer instead of a real
// filesystem driver and transport.
#[cfg(test)]
mod tests {
    use super::super::test_util::{
        check_malformed, check_oversized, oversized_request, request, request_bodies, MockFS,
        NoDax, TestWriter, OVERSIZED_OPCODES,
    };
    use super::*;

    fn prepare_srvcontext<'a, F: FileSystem>(
        read_buf: &'a mut [u8],
        write_buf: &'a mut [u8],
    ) -> SrvContext<'a, F, (), TestWriter<'a>> {
        let reader = Reader::<()>::from_slice(read_buf);
        let writer = TestWriter::new(write_buf);
        let in_header = InHeader::default();
        SrvContext::new(in_header, reader, writer)
    }

    mod tests_parse_extensions {
        use super::super::*;

        fn build_supp_groups_ext(gid: u32) -> Vec<u8> {
            let mut buf = Vec::new();
            let size = (size_of::<ExtHeader>() + size_of::<SuppGroups>() + size_of::<u32>()) as u32;
            buf.extend_from_slice(&size.to_ne_bytes());
            buf.extend_from_slice(&FUSE_EXT_GROUPS.to_ne_bytes());
            buf.extend_from_slice(&1u32.to_ne_bytes());
            buf.extend_from_slice(&gid.to_ne_bytes());
            buf
        }

        fn assert_einval(res: Result<Option<u32>>) {
            match res {
                Err(Error::DecodeMessage(e)) => {
                    assert_eq!(e.raw_os_error(), Some(libc::EINVAL));
                }
                other => panic!("unexpected result: {:?}", other),
            }
        }

        #[test]
        fn test_parse_create_extensions_empty() {
            assert_eq!(
                parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &[]).unwrap(),
                None
            );
        }

        #[test]
        fn test_parse_create_extensions_supp_group() {
            let buf = build_supp_groups_ext(1000);
            assert_eq!(
                parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf).unwrap(),
                Some(1000)
            );
        }

        #[test]
        fn test_parse_create_extensions_skip_unknown() {
            // An unknown extension followed by the supp group extension:
            // extensions are padded to 8 bytes (fuse_ext_size()).
            let mut buf = Vec::new();
            let size = (size_of::<ExtHeader>() + 8) as u32;
            buf.extend_from_slice(&size.to_ne_bytes());
            buf.extend_from_slice(&0u32.to_ne_bytes());
            buf.extend_from_slice(&[0u8; 8]);
            buf.extend_from_slice(&build_supp_groups_ext(1000));

            assert_eq!(
                parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf).unwrap(),
                Some(1000)
            );
        }

        #[test]
        fn test_parse_create_extensions_truncated_header() {
            assert_einval(parse_create_extensions(
                &FsOptions::CREATE_SUPP_GROUP,
                &[0u8; 4],
            ));
        }

        #[test]
        fn test_parse_create_extensions_bad_size() {
            // Extension size smaller than the header.
            let mut buf = Vec::new();
            buf.extend_from_slice(&4u32.to_ne_bytes());
            buf.extend_from_slice(&FUSE_EXT_GROUPS.to_ne_bytes());
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));

            // Extension size exceeding the payload.
            let mut buf = build_supp_groups_ext(1000);
            buf.truncate(8);
            buf[0..4].copy_from_slice(&100u32.to_ne_bytes());
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));
        }

        #[test]
        fn test_parse_create_extensions_bad_nr_groups() {
            // nr_groups is zero.
            let mut buf = build_supp_groups_ext(1000);
            buf[8..12].copy_from_slice(&0u32.to_ne_bytes());
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));

            // Payload size doesn't match nr_groups.
            let mut buf = build_supp_groups_ext(1000);
            buf[8..12].copy_from_slice(&2u32.to_ne_bytes());
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));
        }

        #[test]
        fn test_parse_create_extensions_multi_groups() {
            // A well-formed extension carrying several groups: only the
            // first one is consumed, mirroring virtiofsd.  The kernel
            // currently sends a single matching group.
            let mut buf = Vec::new();
            // ExtHeader plus a body of nr_groups and two gids, padded to
            // a multiple of 8 (FUSE_REC_ALIGN).
            let size = (size_of::<ExtHeader>() + 16) as u32;
            buf.extend_from_slice(&size.to_ne_bytes());
            buf.extend_from_slice(&FUSE_EXT_GROUPS.to_ne_bytes());
            buf.extend_from_slice(&2u32.to_ne_bytes());
            buf.extend_from_slice(&1000u32.to_ne_bytes());
            buf.extend_from_slice(&2000u32.to_ne_bytes());
            buf.extend_from_slice(&[0u8; 4]); // padding
            assert_eq!(
                parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf).unwrap(),
                Some(1000)
            );
        }

        #[test]
        fn test_parse_create_extensions_too_many_groups() {
            // nr_groups exceeding LINUX_NRGROUPS_MAX (65536) is rejected
            // before the payload size is validated.
            let mut buf = Vec::new();
            let size = (size_of::<ExtHeader>() + size_of::<SuppGroups>()) as u32;
            buf.extend_from_slice(&size.to_ne_bytes());
            buf.extend_from_slice(&FUSE_EXT_GROUPS.to_ne_bytes());
            buf.extend_from_slice(&65537u32.to_ne_bytes());
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));
        }

        #[test]
        fn test_parse_create_extensions_not_negotiated() {
            // The supp group extension must be rejected when
            // FUSE_CREATE_SUPP_GROUP hasn't been negotiated.
            let buf = build_supp_groups_ext(1000);
            assert_einval(parse_create_extensions(&FsOptions::empty(), &buf));
            // An empty tail is still fine.
            assert_eq!(
                parse_create_extensions(&FsOptions::empty(), &[]).unwrap(),
                None
            );
        }

        #[test]
        fn test_parse_create_extensions_garbage_after_supp_group() {
            // The whole extension chain is validated: garbage appended
            // after a valid supp group extension is rejected.
            let mut buf = build_supp_groups_ext(1000);
            buf.extend_from_slice(&[0u8; 4]);
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));
        }

        #[test]
        fn test_parse_create_extensions_unaligned_size() {
            // Extension sizes must be multiples of 8 (FUSE_REC_ALIGN),
            // even for unknown extension types.
            let mut buf = Vec::new();
            buf.extend_from_slice(&9u32.to_ne_bytes());
            buf.extend_from_slice(&0u32.to_ne_bytes());
            buf.extend_from_slice(&[0u8; 1]);
            assert_einval(parse_create_extensions(&FsOptions::CREATE_SUPP_GROUP, &buf));
        }
    }

    #[test]
    fn test_server_init() {
        let server = Server::new(MockFS);

        let mut read_buf = [
            0x8u8, 0x0, 0x0, 0x0, // major = 0x0008
            0x0u8, 0x0, 0x0, 0x0, // minor = 0x0008
            0x0, 0x0, 0x0, 0x0, // max_readahead = 0x0000
            0x0, 0x0, 0x0, 0x0, // flags = 0x0000
        ];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server
            .init(&mut ctx, |_| unreachable!("shouldn't be called"))
            .unwrap();
        assert_eq!(res, 80);

        let mut read_buf1 = [
            0x7u8, 0x0, 0x0, 0x0, // major = 0x0007
            0x0u8, 0x0, 0x0, 0x0, // minor = 0x0000
            0x0, 0x0, 0x0, 0x0, // max_readahead = 0x0000
            0x0, 0x0, 0x0, 0x0, // flags = 0x0000
        ];
        let mut write_buf1 = [0u8; 4096];
        let mut ctx1 = prepare_srvcontext(&mut read_buf1, &mut write_buf1);

        let mut init_params_called = false;
        let res = server
            .init(&mut ctx1, |init_params| {
                assert_eq!(init_params.version.major, 0x0007);
                assert_eq!(init_params.version.minor, 0x0000);
                init_params_called = true
            })
            .unwrap();
        assert!(init_params_called);

        assert_eq!(res, 24);
    }

    // The INIT_EXT family below stays Linux-only on purpose: macFUSE assigns
    // bit 30 (INIT_EXT's Linux value) to its own VOL_RENAME capability, so the
    // macOS ABI deliberately does not define the symbol.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_init_ext_without_payload() {
        let server = Server::new(MockFS);

        let mut read_buf = [
            0x7u8, 0x0, 0x0, 0x0, // major = 0x0007
            0x24u8, 0x0, 0x0, 0x0, // minor = 0x0024
            0x0, 0x0, 0x0, 0x0, // max_readahead = 0x0000
            0x0, 0x0, 0x0, 0x40, // flags = INIT_EXT
        ];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let mut init_params_called = false;
        let res = server
            .init(&mut ctx, |init_params| {
                assert_eq!(init_params.version.major, 0x0007);
                assert_eq!(init_params.version.minor, 0x0024);
                assert!(!init_params.capable.contains(FsOptions::INIT_EXT));
                init_params_called = true;
            })
            .unwrap();

        assert!(init_params_called);
        assert_eq!(res, 80);
    }

    // A file system negotiating FUSE_CREATE_SUPP_GROUP (bit 34) when the
    // kernel offers it, like Vfs and PassthroughFs do.  Its other
    // operations keep the default implementations.
    #[cfg(target_os = "linux")]
    struct SuppGroupFs;
    #[cfg(target_os = "linux")]
    impl FileSystem for SuppGroupFs {
        type Inode = u64;
        type Handle = u64;

        fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
            Ok(capable & FsOptions::CREATE_SUPP_GROUP)
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_init_echoes_init_ext_for_64bit_caps() {
        // A kernel >= 6.3 sends the full 64-byte fuse_init_in: INIT_EXT in
        // flags and FUSE_CREATE_SUPP_GROUP in flags2.
        let mut read_buf = [0u8; size_of::<InitIn>() + size_of::<InitIn2>()];
        let init_in = InitIn {
            major: KERNEL_VERSION,
            minor: KERNEL_MINOR_VERSION,
            max_readahead: 0,
            flags: FsOptions::INIT_EXT.bits() as u32,
        };
        read_buf[..size_of::<InitIn>()].copy_from_slice(init_in.as_slice());
        let init_in2 = InitIn2 {
            flags2: (FsOptions::CREATE_SUPP_GROUP.bits() >> 32) as u32,
            unused: [0; 11],
        };
        read_buf[size_of::<InitIn>()..].copy_from_slice(init_in2.as_slice());

        let server = Server::new(SuppGroupFs);
        let mut write_buf = [0u8; 4096];
        let mut ctx = {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            SrvContext::new(InHeader::default(), reader, writer)
        };
        let res = server.init(&mut ctx, |_| {}).unwrap();
        assert_eq!(res, size_of::<OutHeader>() + size_of::<InitOut>());

        // The reply must carry FUSE_CREATE_SUPP_GROUP in flags2 and echo
        // FUSE_INIT_EXT in flags: the kernel applies flags2 only when the
        // echo is present, so without it the capability would be silently
        // dropped and the kernel would never send FUSE_EXT_GROUPS
        // extensions.
        let mut out = InitOut::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[size_of::<OutHeader>()..res]);
        assert_ne!(out.flags & FsOptions::INIT_EXT.bits() as u32, 0);
        assert_ne!(
            out.flags2 & (FsOptions::CREATE_SUPP_GROUP.bits() >> 32) as u32,
            0
        );
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_restore_init() {
        let init_in = InitIn {
            major: KERNEL_VERSION,
            minor: 40,
            max_readahead: 0,
            flags: FsOptions::INIT_EXT.bits() as u32,
        };
        let init_in2 = InitIn2 {
            flags2: ((FsOptions::CREATE_SUPP_GROUP | FsOptions::HAS_RESEND).bits() >> 32) as u32,
            unused: [0; 11],
        };
        let mut read_buf = [init_in.as_slice(), init_in2.as_slice()].concat();
        let mut write_buf = [0u8; 4096];
        let old = Server::new(SuppGroupFs);
        old.init(
            &mut prepare_srvcontext(&mut read_buf, &mut write_buf),
            |_| {},
        )
        .unwrap();
        let (version, options) = old.init_state();
        assert_eq!(version.minor, 40);
        assert!(options.contains(FsOptions::CREATE_SUPP_GROUP | FsOptions::INIT_EXT));

        let new = Server::new(SuppGroupFs);
        assert!(new.init_state().1.is_empty());
        new.restore_init(version.clone(), options);
        assert_eq!(new.init_state(), (version, options));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_reply_keeps_unique_resend() {
        let server = Server::new(MockFS);
        let unique = UNIQUE_RESEND | 42;
        let header = InHeader {
            len: (size_of::<InHeader>() + size_of::<GetattrIn>()) as u32,
            opcode: Opcode::Getattr as u32,
            unique,
            nodeid: ROOT_ID,
            ..Default::default()
        };
        let mut read_buf = [header.as_slice(), GetattrIn::default().as_slice()].concat();
        let mut write_buf = [0u8; 4096];
        let reader = Reader::<()>::from_slice(&mut read_buf);
        let writer = TestWriter::new(&mut write_buf);
        server.handle_message(reader, writer, None, None).unwrap();
        let out = OutHeader::from_slice(&write_buf[..size_of::<OutHeader>()]).unwrap();
        assert_eq!(out.unique, unique);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_init_passthrough() {
        struct PassthroughFs;
        impl FileSystem for PassthroughFs {
            type Inode = u64;
            type Handle = u64;

            fn init(&self, _capable: FsOptions) -> io::Result<FsOptions> {
                Ok(FsOptions::PASSTHROUGH)
            }
        }

        let server = Server::new(PassthroughFs);
        // The kernel turns passthrough off for depths other than 1 and 2.
        assert!(server.set_max_stack_depth(0).is_err());
        assert!(server.set_max_stack_depth(3).is_err());
        server.set_max_stack_depth(2).unwrap();

        let init_in = InitIn {
            major: KERNEL_VERSION,
            minor: 40,
            max_readahead: 0,
            flags: FsOptions::INIT_EXT.bits() as u32,
        };
        let init_in2 = InitIn2 {
            flags2: (FsOptions::PASSTHROUGH.bits() >> 32) as u32,
            unused: [0; 11],
        };
        let mut read_buf = [init_in.as_slice(), init_in2.as_slice()].concat();
        let mut write_buf = [0u8; 4096];
        let mut ctx = {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            SrvContext::new(InHeader::default(), reader, writer)
        };
        let res = server.init(&mut ctx, |_| {}).unwrap();
        assert_eq!(res, size_of::<OutHeader>() + size_of::<InitOut>());

        let out = InitOut::from_slice(&write_buf[size_of::<OutHeader>()..res]).unwrap();
        assert_ne!(out.flags as u64 & FsOptions::INIT_EXT.bits(), 0);
        assert_eq!((out.flags2 as u64) << 32, FsOptions::PASSTHROUGH.bits());
        assert_eq!(out.max_stack_depth, 2);
    }

    #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
    #[test]
    fn test_server_init_uring_bufpool() {
        use crate::abi::fuse_uring::FUSE_HAS_IO_URING_BUFPOOL;

        /// A file system that wants everything the kernel offers.
        struct WantAll;
        impl FileSystem for WantAll {
            type Inode = u64;
            type Handle = u64;
            fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
                Ok(capable)
            }
        }

        // Run INIT with `flags` and `flags2` from the kernel, and return the
        // server and the reply.
        let init = |flags: FsOptions, flags2: u64| {
            let mut read_buf = [0u8; size_of::<InitIn>() + size_of::<InitIn2>()];
            let init_in = InitIn {
                major: KERNEL_VERSION,
                minor: KERNEL_MINOR_VERSION,
                max_readahead: 0,
                flags: (flags | FsOptions::INIT_EXT).bits() as u32,
            };
            read_buf[..size_of::<InitIn>()].copy_from_slice(init_in.as_slice());
            let init_in2 = InitIn2 {
                flags2: ((FsOptions::OVER_IO_URING.bits() | flags2) >> 32) as u32,
                unused: [0; 11],
            };
            read_buf[size_of::<InitIn>()..].copy_from_slice(init_in2.as_slice());
            let server = Server::new(WantAll);
            server.set_uring(true);
            let mut write_buf = [0u8; 4096];
            let res = {
                let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);
                server.init(&mut ctx, |_| {}).unwrap()
            };
            let mut out = InitOut::default();
            out.as_mut_slice()
                .copy_from_slice(&write_buf[size_of::<OutHeader>()..res]);
            (server, out)
        };

        // The kernel's flag for buffer pools isn't an FsOptions flag, but
        // the server still sees it.
        let (server, _) = init(FsOptions::empty(), FUSE_HAS_IO_URING_BUFPOOL);
        assert!(server.uring_bufpool_supported());
        let (server, out) = init(FsOptions::empty(), 0);
        assert!(!server.uring_bufpool_supported());
        // Without FUSE_MAX_PAGES the kernel keeps 32 pages per request.
        assert_eq!(out.max_pages, 0);
        assert_eq!(
            server.uring_payload_size(),
            (MIN_READ_BUFFER as usize)
                .max(out.max_write as usize)
                .max(32 * pagesize())
        );

        // With FUSE_MAX_PAGES the kernel takes max_pages up to its limit.
        let (server, out) = init(FsOptions::MAX_PAGES | FsOptions::BIG_WRITES, 0);
        assert_eq!(out.max_pages, MAX_REQ_PAGES);
        assert_eq!(
            server.uring_payload_size(),
            MAX_REQ_PAGES as usize * pagesize()
        );
        // The kernel's max_pages_limit can't change the size, because the
        // reply's max_write covers max_pages pages.
        assert!(out.max_write as usize >= MAX_REQ_PAGES as usize * pagesize());
    }

    #[cfg(feature = "fusedev-uring")]
    #[test]
    fn test_server_init_uring_negotiation() {
        // Kernel capability set carrying INIT_EXT plus FUSE_OVER_IO_URING
        // (bit 41, i.e. bit 9 of flags2), as sent by kernels >= 6.14:
        // fuse_init_in followed by the full fuse_init_in2.
        let mut read_buf = [0u8; size_of::<InitIn>() + size_of::<InitIn2>()];
        let init_in = InitIn {
            major: KERNEL_VERSION,
            minor: KERNEL_MINOR_VERSION,
            max_readahead: 0,
            flags: (FsOptions::DO_READDIRPLUS | FsOptions::INIT_EXT).bits() as u32,
        };
        read_buf[..size_of::<InitIn>()].copy_from_slice(init_in.as_slice());
        let init_in2 = InitIn2 {
            flags2: (FsOptions::OVER_IO_URING.bits() >> 32) as u32,
            unused: [0; 11],
        };
        read_buf[size_of::<InitIn>()..].copy_from_slice(init_in2.as_slice());

        // With set_uring() the reply must echo FUSE_OVER_IO_URING in
        // flags2 and set FUSE_INIT_EXT in flags, since kernels >= 6.13
        // apply flags2 only when FUSE_INIT_EXT is present.
        let server = Server::new(MockFS);
        server.set_uring(true);
        let mut write_buf = [0u8; 4096];
        let res = {
            let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);
            server.init(&mut ctx, |_| {}).unwrap()
        };
        assert_eq!(res, size_of::<OutHeader>() + size_of::<InitOut>());
        // The reply lands directly in the writer buffer.
        let mut out = InitOut::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[size_of::<OutHeader>()..res]);
        assert_ne!(out.flags & FsOptions::INIT_EXT.bits() as u32, 0);
        assert_ne!(
            out.flags2 & (FsOptions::OVER_IO_URING.bits() >> 32) as u32,
            0
        );
        assert!(server.uring_enabled());

        // Without set_uring() the capability stays off and no upper bit
        // is enabled, so INIT_EXT must not be advertised either.
        let server = Server::new(MockFS);
        let mut write_buf = [0u8; 4096];
        let res = {
            let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);
            server.init(&mut ctx, |_| {}).unwrap()
        };
        let mut out = InitOut::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[size_of::<OutHeader>()..res]);
        assert_eq!(out.flags & FsOptions::INIT_EXT.bits() as u32, 0);
        assert_eq!(out.flags2, 0);
        assert!(!server.uring_enabled());
    }

    #[test]
    fn test_server_write() {
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; 4096];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server.write(&mut ctx).unwrap();
        assert_eq!(res, 16);
    }

    #[test]
    fn test_server_read() {
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; 4096];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server.read(&mut ctx).unwrap();
        assert_eq!(res, 16);
    }

    #[test]
    fn test_server_readdir() {
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; 4096];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server.do_readdir(&mut ctx, true).unwrap();
        assert_eq!(res, 16);
    }

    #[test]
    fn test_server_readdir_needs_room_after_header() {
        let server = Server::new(MockFS);
        let read_in = ReadIn {
            size: 64,
            ..Default::default()
        };

        // The writer holds the 16-byte reply header and 63 bytes, one short
        // of the 64 bytes of entries the request asks for.
        for (room, error) in [(63, libc::ENOMEM), (64, libc::ENOSYS)] {
            let mut read_buf = read_in.as_slice().to_vec();
            let mut write_buf = vec![0u8; size_of::<OutHeader>() + room];
            let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);
            server.do_readdir(&mut ctx, false).unwrap();
            let out = OutHeader::from_slice(&write_buf[..size_of::<OutHeader>()]).unwrap();
            assert_eq!(out.error, -error, "room {room}");
        }
    }

    #[test]
    fn test_server_ioctl() {
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; 4096];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server.ioctl(&mut ctx).unwrap();
        assert!(res > 0);

        // construct IoctlIn with invalid in_size
        let mut read_buf_fail = [
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, //fh = 0
            0x0, 0x0, 0x0, 0x0, //flags = 0
            0x0, 0x0, 0x0, 0x0, //cmd = 0
            0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, //arg = 0
            0x7u8, 0x3u8, 0x0, 0x0, //in_size = 0x307
            0x0, 0x0, 0x0, 0x0, //out_size = 0
        ];
        let mut write_buf_fail = [0u8; 48];
        let mut ctx_fail = prepare_srvcontext(&mut read_buf_fail, &mut write_buf_fail);
        let res = server.ioctl(&mut ctx_fail).unwrap();
        assert!(res > 0);
    }

    #[test]
    fn test_server_batch_forget() {
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; 4096];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);
        // forget should return 0 anyway
        assert_eq!(server.batch_forget(&mut ctx).unwrap(), 0);
    }

    #[test]
    fn test_server_forget() {
        let server = Server::new(MockFS);

        let mut read_buf = [0x1u8, 0x2u8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        assert_eq!(server.forget(&mut ctx).unwrap(), 0);
    }

    #[test]
    #[cfg(all(feature = "fusedev", target_os = "linux"))]
    fn test_server_notify_expire_entry_needs_expire_only() {
        let server = Server::new(MockFS);
        let mut buf = [0u8; 64];
        let name = CStr::from_bytes_with_nul(b"name\0").unwrap();
        match server.notify_expire_entry(TestWriter::new(&mut buf), ROOT_ID, name) {
            Err(Error::EncodeMessage(e)) => assert_eq!(e.raw_os_error(), Some(libc::ENOSYS)),
            other => panic!("unexpected result: {:?}", other),
        }
    }

    #[test]
    fn test_server_copy_file_range() {
        use crate::api::filesystem::Context;

        // Echoes the decoded request back as the copied size, so the whole
        // decode/call/reply wiring can be verified.
        struct CopyFs;
        impl FileSystem for CopyFs {
            type Inode = u64;
            type Handle = u64;

            #[allow(clippy::too_many_arguments)]
            fn copy_file_range(
                &self,
                _ctx: &Context,
                inode_in: Self::Inode,
                fh_in: Self::Handle,
                offset_in: u64,
                inode_out: Self::Inode,
                fh_out: Self::Handle,
                offset_out: u64,
                len: u64,
                flags: u64,
            ) -> io::Result<u32> {
                assert_eq!((inode_in, fh_in, offset_in), (10, 100, 4096));
                assert_eq!((inode_out, fh_out, offset_out), (20, 200, 512));
                assert_eq!((len, flags), (2048, 0));
                Ok(1024)
            }
        }

        let server = Server::new(CopyFs);

        let mut read_buf = [0u8; size_of::<CopyFileRangeIn>()];
        let in_arg = CopyFileRangeIn {
            fh_in: 100,
            offset_in: 4096,
            nodeid_out: 20,
            fh_out: 200,
            offset_out: 512,
            len: 2048,
            flags: 0,
        };
        read_buf.copy_from_slice(in_arg.as_slice());

        let mut write_buf = [0u8; 4096];
        let mut ctx = {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            SrvContext::new(
                InHeader {
                    nodeid: 10,
                    ..Default::default()
                },
                reader,
                writer,
            )
        };

        let res = server.copy_file_range(&mut ctx).unwrap();
        assert_eq!(res, size_of::<OutHeader>() + size_of::<WriteOut>());

        let mut out = WriteOut::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[size_of::<OutHeader>()..res]);
        assert_eq!(out.size, 1024);
        assert_eq!(out.padding, 0);
    }

    #[test]
    fn test_server_copy_file_range_enosys() {
        // The default implementation answers ENOSYS, on which the kernel
        // falls back to its generic read/write copy loop.
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; size_of::<CopyFileRangeIn>()];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server.copy_file_range(&mut ctx).unwrap();
        assert_eq!(res, size_of::<OutHeader>());

        let mut out = OutHeader::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[..size_of::<OutHeader>()]);
        assert_eq!(out.error, -libc::ENOSYS);
    }

    #[test]
    fn test_server_lseek() {
        use crate::api::filesystem::Context;

        // Echoes the decoded request back as the resulting offset, so the
        // whole decode/call/reply wiring can be verified.
        struct LseekFs;
        impl FileSystem for LseekFs {
            type Inode = u64;
            type Handle = u64;

            fn lseek(
                &self,
                _ctx: &Context,
                inode: Self::Inode,
                handle: Self::Handle,
                offset: u64,
                whence: u32,
            ) -> io::Result<u64> {
                assert_eq!(
                    (inode, handle, offset, whence),
                    (10, 100, 4096, libc::SEEK_DATA as u32)
                );
                Ok(8192)
            }
        }

        let server = Server::new(LseekFs);

        // The kernel sends the raw uapi SEEK_* value in LseekIn.whence, which
        // the server must pass to the file system unchanged.
        let mut read_buf = [0u8; size_of::<LseekIn>()];
        let in_arg = LseekIn {
            fh: 100,
            offset: 4096,
            whence: libc::SEEK_DATA as u32,
            padding: 0,
        };
        read_buf.copy_from_slice(in_arg.as_slice());

        let mut write_buf = [0u8; 4096];
        let mut ctx = {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            SrvContext::new(
                InHeader {
                    nodeid: 10,
                    ..Default::default()
                },
                reader,
                writer,
            )
        };

        let res = server.lseek(&mut ctx).unwrap();
        assert_eq!(res, size_of::<OutHeader>() + size_of::<LseekOut>());

        let mut out = LseekOut::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[size_of::<OutHeader>()..res]);
        assert_eq!(out.offset, 8192);
    }

    #[test]
    fn test_server_lseek_enosys() {
        // The default implementation answers ENOSYS, on which the kernel
        // sets fc->no_lseek and falls back to generic_file_llseek().
        let server = Server::new(MockFS);

        let mut read_buf = [0u8; size_of::<LseekIn>()];
        let mut write_buf = [0u8; 4096];
        let mut ctx = prepare_srvcontext(&mut read_buf, &mut write_buf);

        let res = server.lseek(&mut ctx).unwrap();
        assert_eq!(res, size_of::<OutHeader>());

        let mut out = OutHeader::default();
        out.as_mut_slice()
            .copy_from_slice(&write_buf[..size_of::<OutHeader>()]);
        assert_eq!(out.error, -libc::ENOSYS);
    }

    // macOS `GetxattrIn` carries macFUSE's `position` field, so the wire
    // layouts differ; these tests encode the Linux layout.
    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_getxattr() {
        use crate::api::filesystem::Context;
        use std::ffi::CStr;

        // Echoes the requested size back as the value content, so the size
        // routing and the reply encoding can be verified together. The value
        // is always 16 bytes: it fits a request for 16 bytes, is one byte
        // too big for 15, is smaller than a request for 32, and answers a
        // zero-size probe with the length.
        struct GetxattrFs;
        impl FileSystem for GetxattrFs {
            type Inode = u64;
            type Handle = u64;

            fn getxattr(
                &self,
                _ctx: &Context,
                _inode: Self::Inode,
                name: &CStr,
                size: u32,
            ) -> io::Result<GetxattrReply> {
                assert_eq!(name, CStr::from_bytes_with_nul(b"user.foo\0").unwrap());
                Ok(GetxattrReply::Value(vec![size as u8; 16]))
            }
        }

        let server = Server::new(GetxattrFs);

        // A value that fits is replied as is, one that is a byte too big
        // answers ERANGE, and one smaller than the request is replied at
        // its own length, which the kernel accepts and shrinks.
        for (size, error) in [(16, 0), (15, libc::ERANGE), (32, 0)] {
            let mut read_buf = [0u8; size_of::<GetxattrIn>() + b"user.foo\0".len()];
            read_buf[..size_of::<GetxattrIn>()]
                .copy_from_slice(GetxattrIn { size, padding: 0 }.as_slice());
            read_buf[size_of::<GetxattrIn>()..].copy_from_slice(b"user.foo\0");

            let mut write_buf = [0u8; 4096];
            let in_header = InHeader {
                len: (size_of::<InHeader>() + read_buf.len()) as u32,
                nodeid: 10,
                ..Default::default()
            };
            let mut ctx = {
                let reader = Reader::<()>::from_slice(&mut read_buf);
                let writer = TestWriter::new(&mut write_buf);
                SrvContext::new(in_header, reader, writer)
            };

            let res = server.getxattr(&mut ctx).unwrap();
            let out = OutHeader::from_slice(&write_buf[..size_of::<OutHeader>()]).unwrap();
            assert_eq!(out.error, -error, "size {size}");

            if error == 0 {
                assert_eq!(res, size_of::<OutHeader>() + 16);
                assert_eq!(&write_buf[size_of::<OutHeader>()..res], &[size as u8; 16]);
            } else {
                // ERANGE is a header-only error reply.
                assert_eq!(res, size_of::<OutHeader>());
            }
        }

        // A zero-size probe asks for the length only: the server converts
        // the value to the needed size the kernel expects in a GetxattrOut.
        let mut read_buf = [0u8; size_of::<GetxattrIn>() + b"user.foo\0".len()];
        read_buf[..size_of::<GetxattrIn>()].copy_from_slice(
            GetxattrIn {
                size: 0,
                padding: 0,
            }
            .as_slice(),
        );
        read_buf[size_of::<GetxattrIn>()..].copy_from_slice(b"user.foo\0");

        let mut write_buf = [0u8; 4096];
        let in_header = InHeader {
            len: (size_of::<InHeader>() + read_buf.len()) as u32,
            nodeid: 10,
            ..Default::default()
        };
        let mut ctx = {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            SrvContext::new(in_header, reader, writer)
        };

        let res = server.getxattr(&mut ctx).unwrap();
        assert_eq!(res, size_of::<OutHeader>() + size_of::<GetxattrOut>());

        let out = GetxattrOut::from_slice(&write_buf[size_of::<OutHeader>()..res]).unwrap();
        assert_eq!(out.size, 16);
        assert_eq!(out.padding, 0);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_getxattr_count() {
        use crate::api::filesystem::Context;
        use std::ffi::CStr;

        // A count is only a valid answer to a zero-size probe: the server
        // passes it through as GetxattrOut there, and answers a nonzero
        // size with EINVAL, since the count carries no value the kernel
        // could return to the caller.
        struct GetxattrCountFs;
        impl FileSystem for GetxattrCountFs {
            type Inode = u64;
            type Handle = u64;

            fn getxattr(
                &self,
                _ctx: &Context,
                _inode: Self::Inode,
                _name: &CStr,
                _size: u32,
            ) -> io::Result<GetxattrReply> {
                Ok(GetxattrReply::Count(16))
            }
        }

        let server = Server::new(GetxattrCountFs);

        for (size, error) in [(0, 0), (16, libc::EINVAL)] {
            let mut read_buf = [0u8; size_of::<GetxattrIn>() + b"user.foo\0".len()];
            read_buf[..size_of::<GetxattrIn>()]
                .copy_from_slice(GetxattrIn { size, padding: 0 }.as_slice());
            read_buf[size_of::<GetxattrIn>()..].copy_from_slice(b"user.foo\0");

            let mut write_buf = [0u8; 4096];
            let in_header = InHeader {
                len: (size_of::<InHeader>() + read_buf.len()) as u32,
                nodeid: 10,
                ..Default::default()
            };
            let mut ctx = {
                let reader = Reader::<()>::from_slice(&mut read_buf);
                let writer = TestWriter::new(&mut write_buf);
                SrvContext::new(in_header, reader, writer)
            };

            let res = server.getxattr(&mut ctx).unwrap();
            let out = OutHeader::from_slice(&write_buf[..size_of::<OutHeader>()]).unwrap();
            assert_eq!(out.error, -error, "size {size}");

            if error == 0 {
                assert_eq!(res, size_of::<OutHeader>() + size_of::<GetxattrOut>());
                let out = GetxattrOut::from_slice(&write_buf[size_of::<OutHeader>()..res]).unwrap();
                assert_eq!(out.size, 16);
                assert_eq!(out.padding, 0);
            } else {
                // EINVAL is a header-only error reply.
                assert_eq!(res, size_of::<OutHeader>());
            }
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_listxattr() {
        use crate::api::filesystem::Context;

        // Echoes the requested size back as the name list content, so the
        // size routing and the reply encoding can be verified together. The
        // list is always 16 bytes: it fits a request for 16 bytes, is one
        // byte too big for 15, is smaller than a request for 32, and
        // answers a zero-size probe with the length.
        struct ListxattrFs;
        impl FileSystem for ListxattrFs {
            type Inode = u64;
            type Handle = u64;

            fn listxattr(
                &self,
                _ctx: &Context,
                _inode: Self::Inode,
                size: u32,
            ) -> io::Result<ListxattrReply> {
                Ok(ListxattrReply::Names(vec![size as u8; 16]))
            }
        }

        let server = Server::new(ListxattrFs);

        // A list that fits is replied as is, one that is a byte too big
        // answers ERANGE, and one smaller than the request is replied at
        // its own length, which the kernel accepts and shrinks.
        for (size, error) in [(16, 0), (15, libc::ERANGE), (32, 0)] {
            let mut read_buf = [0u8; size_of::<GetxattrIn>()];
            read_buf.copy_from_slice(GetxattrIn { size, padding: 0 }.as_slice());

            let mut write_buf = [0u8; 4096];
            let in_header = InHeader {
                len: (size_of::<InHeader>() + read_buf.len()) as u32,
                nodeid: 10,
                ..Default::default()
            };
            let mut ctx = {
                let reader = Reader::<()>::from_slice(&mut read_buf);
                let writer = TestWriter::new(&mut write_buf);
                SrvContext::new(in_header, reader, writer)
            };

            let res = server.listxattr(&mut ctx).unwrap();
            let out = OutHeader::from_slice(&write_buf[..size_of::<OutHeader>()]).unwrap();
            assert_eq!(out.error, -error, "size {size}");

            if error == 0 {
                assert_eq!(res, size_of::<OutHeader>() + 16);
                assert_eq!(&write_buf[size_of::<OutHeader>()..res], &[size as u8; 16]);
            } else {
                // ERANGE is a header-only error reply.
                assert_eq!(res, size_of::<OutHeader>());
            }
        }

        // A zero-size probe asks for the length only: the server converts
        // the name list to the needed size the kernel expects in a
        // GetxattrOut.
        let mut read_buf = [0u8; size_of::<GetxattrIn>()];
        read_buf.copy_from_slice(
            GetxattrIn {
                size: 0,
                padding: 0,
            }
            .as_slice(),
        );

        let mut write_buf = [0u8; 4096];
        let in_header = InHeader {
            len: (size_of::<InHeader>() + read_buf.len()) as u32,
            nodeid: 10,
            ..Default::default()
        };
        let mut ctx = {
            let reader = Reader::<()>::from_slice(&mut read_buf);
            let writer = TestWriter::new(&mut write_buf);
            SrvContext::new(in_header, reader, writer)
        };

        let res = server.listxattr(&mut ctx).unwrap();
        assert_eq!(res, size_of::<OutHeader>() + size_of::<GetxattrOut>());

        let out = GetxattrOut::from_slice(&write_buf[size_of::<OutHeader>()..res]).unwrap();
        assert_eq!(out.size, 16);
        assert_eq!(out.padding, 0);
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn test_server_listxattr_count() {
        use crate::api::filesystem::Context;

        // A count is only a valid answer to a zero-size probe: the server
        // passes it through as GetxattrOut there, and answers a nonzero
        // size with EINVAL, since the count carries no name list the
        // kernel could return to the caller.
        struct ListxattrCountFs;
        impl FileSystem for ListxattrCountFs {
            type Inode = u64;
            type Handle = u64;

            fn listxattr(
                &self,
                _ctx: &Context,
                _inode: Self::Inode,
                _size: u32,
            ) -> io::Result<ListxattrReply> {
                Ok(ListxattrReply::Count(16))
            }
        }

        let server = Server::new(ListxattrCountFs);

        for (size, error) in [(0, 0), (16, libc::EINVAL)] {
            let mut read_buf = [0u8; size_of::<GetxattrIn>()];
            read_buf.copy_from_slice(GetxattrIn { size, padding: 0 }.as_slice());

            let mut write_buf = [0u8; 4096];
            let in_header = InHeader {
                len: (size_of::<InHeader>() + read_buf.len()) as u32,
                nodeid: 10,
                ..Default::default()
            };
            let mut ctx = {
                let reader = Reader::<()>::from_slice(&mut read_buf);
                let writer = TestWriter::new(&mut write_buf);
                SrvContext::new(in_header, reader, writer)
            };

            let res = server.listxattr(&mut ctx).unwrap();
            let out = OutHeader::from_slice(&write_buf[..size_of::<OutHeader>()]).unwrap();
            assert_eq!(out.error, -error, "size {size}");

            if error == 0 {
                assert_eq!(res, size_of::<OutHeader>() + size_of::<GetxattrOut>());
                let out = GetxattrOut::from_slice(&write_buf[size_of::<OutHeader>()..res]).unwrap();
                assert_eq!(out.size, 16);
                assert_eq!(out.padding, 0);
            } else {
                // EINVAL is a header-only error reply.
                assert_eq!(res, size_of::<OutHeader>());
            }
        }
    }

    #[test]
    fn test_server_replies_to_malformed_bodies() {
        let server = Server::new(MockFS);
        for (opcode, body) in request_bodies() {
            for len in 0..body.len() {
                let mut req = request(opcode, &body[..len]);
                let mut reply = [0u8; 4096];
                let res = server.handle_message(
                    Reader::<()>::from_slice(&mut req),
                    TestWriter::new(&mut reply),
                    Some(&mut NoDax),
                    None,
                );
                check_malformed(opcode, len, res, &reply);
            }
        }
    }

    #[test]
    fn test_server_doesnt_reply_to_notify_reply() {
        // The request lacks its NotifyRetrieveIn, so it fails to decode.
        let server = Server::new(MockFS);
        let header = InHeader {
            len: size_of::<InHeader>() as u32,
            opcode: Opcode::NotifyReply as u32,
            unique: 42,
            nodeid: ROOT_ID,
            ..Default::default()
        };
        let mut read_buf = header.as_slice().to_vec();
        let mut write_buf = [0u8; 4096];
        let res = server.handle_message(
            Reader::<()>::from_slice(&mut read_buf),
            TestWriter::new(&mut write_buf),
            None,
            None,
        );
        assert!(matches!(res, Err(Error::DecodeMessage(_))));
        assert!(write_buf.iter().all(|&b| b == 0));
    }

    #[test]
    fn test_server_notify_reply() {
        use crate::api::filesystem::{Context, ZeroCopyReader};
        use std::sync::Mutex;

        type Retrieved = (u64, u64, u64, Vec<u8>);
        #[derive(Default)]
        struct RetrieveFs(Mutex<Vec<Retrieved>>);
        impl FileSystem for RetrieveFs {
            type Inode = u64;
            type Handle = u64;

            fn notify_reply(
                &self,
                _ctx: &Context,
                inode: u64,
                unique: u64,
                offset: u64,
                size: u32,
                r: &mut dyn ZeroCopyReader,
            ) {
                let mut data = vec![0; size as usize];
                r.read_exact(&mut data).unwrap();
                self.0.lock().unwrap().push((inode, unique, offset, data));
            }
        }

        let server = Server::new(RetrieveFs::default());
        let retrieve_in = NotifyRetrieveIn {
            offset: 4096,
            size: 5,
            ..Default::default()
        };
        let header = InHeader {
            len: (size_of::<InHeader>() + size_of::<NotifyRetrieveIn>() + 5) as u32,
            opcode: Opcode::NotifyReply as u32,
            unique: 7,
            nodeid: 10,
            ..Default::default()
        };
        let mut read_buf = [header.as_slice(), retrieve_in.as_slice(), b"hello"].concat();
        let mut write_buf = [0u8; 4096];
        let res = server.handle_message(
            Reader::<()>::from_slice(&mut read_buf),
            TestWriter::new(&mut write_buf),
            None,
            None,
        );

        assert_eq!(res.unwrap(), 0);
        assert!(write_buf.iter().all(|&b| b == 0));
        assert_eq!(
            *server.fs.0.lock().unwrap(),
            [(10, 7, 4096, b"hello".to_vec())]
        );

        // A size past the end of the request doesn't reach the file system.
        read_buf.pop();
        let res = server.handle_message(
            Reader::<()>::from_slice(&mut read_buf),
            TestWriter::new(&mut write_buf),
            None,
            None,
        );
        assert!(matches!(res, Err(Error::DecodeMessage(_))));
        assert!(write_buf.iter().all(|&b| b == 0));
        assert_eq!(server.fs.0.lock().unwrap().len(), 1);
    }

    #[test]
    fn test_server_rejects_oversized_requests() {
        let server = Server::new(MockFS);
        for opcode in OVERSIZED_OPCODES {
            let mut req = oversized_request(opcode);
            let mut reply = [0u8; 4096];
            let res = server.handle_message(
                Reader::<()>::from_slice(&mut req),
                TestWriter::new(&mut reply),
                None,
                None,
            );
            check_oversized(opcode, res, &reply);
        }
    }

    #[test]
    fn test_server_replies_eio_when_remapping_fails() {
        struct NoRemapFs;
        impl FileSystem for NoRemapFs {
            type Inode = u64;
            type Handle = u64;

            fn id_remap(&self, _ctx: &mut crate::api::filesystem::Context) -> io::Result<()> {
                Err(io::Error::from_raw_os_error(libc::EPERM))
            }
        }

        let server = Server::new(NoRemapFs);
        let mut req = request(Opcode::Getattr, GetattrIn::default().as_slice());
        let mut reply = [0u8; 4096];
        let res = server.handle_message(
            Reader::<()>::from_slice(&mut req),
            TestWriter::new(&mut reply),
            None,
            None,
        );
        assert_eq!(res.unwrap(), size_of::<OutHeader>());
        let out = OutHeader::from_slice(&reply[..size_of::<OutHeader>()]).unwrap();
        assert_eq!(out.error, -libc::EIO);

        // FORGET takes no reply.
        let mut req = request(Opcode::Forget, ForgetIn::default().as_slice());
        let mut reply = [0u8; 4096];
        let res = server.handle_message(
            Reader::<()>::from_slice(&mut req),
            TestWriter::new(&mut reply),
            None,
            None,
        );
        assert!(matches!(res, Err(Error::FailedToRemapID(_))));
        assert!(reply.iter().all(|&b| b == 0));
    }

    #[test]
    fn test_server_sends_one_reply_when_it_fails() {
        // The INIT reply doesn't fit in the buffer, but an error reply would.
        let init_in = InitIn {
            major: KERNEL_VERSION,
            minor: KERNEL_MINOR_VERSION,
            ..Default::default()
        };
        let mut req = request(Opcode::Init, init_in.as_slice());
        let mut reply = [0u8; size_of::<OutHeader>() + 8];
        let res = Server::new(MockFS).handle_message(
            Reader::<()>::from_slice(&mut req),
            TestWriter::new(&mut reply),
            None,
            None,
        );
        assert!(matches!(res, Err(Error::EncodeMessage(_))));
        assert!(reply.iter().all(|&b| b == 0));
    }
}
