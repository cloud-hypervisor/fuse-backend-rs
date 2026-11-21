// SPDX-License-Identifier: Apache-2.0

//! Feeds arbitrary bytes to `Server::handle_message()` and `Server::async_handle_message()`.
//!
//! The input is a sequence of requests. Each takes a 4-byte frame: the number of bytes in the
//! request, little-endian `u16`, and the offset where the reader's first buffer ends, another
//! `u16`, so that the request may span two buffers as it does on io_uring. The request header
//! can claim another length than its frame, as a virtio-fs guest can. A file system that
//! answers from the inode and handle numbers of the request serves them, and a writer that
//! sends like the `/dev/fuse` one records the replies. After each request the harness panics
//! unless:
//!
//! - a request that takes no reply, or has no complete header, got none,
//! - any other request got exactly one reply, with the unique number of the request, a `len`
//!   equal to the bytes sent, an error the kernel accepts, and no body after an error,
//! - a READ, READDIR or READDIRPLUS reply holds at most the size the request asked for, and a
//!   GETXATTR or LISTXATTR reply holds the size if the request asked for 0, and at most the
//!   size otherwise,
//! - and the server returned the size of that reply.

use std::cell::RefCell;
use std::ffi::CStr;
use std::future::Future;
use std::io::{self, IoSlice, Read, Write};
use std::mem::size_of;
use std::pin::pin;
use std::task::{Context as TaskContext, Poll, Waker};
use std::time::Duration;

use fuse_backend_core::abi::fuse_abi::{
    stat64, Attr, CreateIn, GetxattrOut, InHeader, Opcode, OutHeader, MAX_BUFFER_SIZE,
};
use fuse_backend_core::abi::virtio_fs::RemovemappingOne;
use fuse_backend_core::api::filesystem::{
    AsyncFileSystem, Context, DirEntry, Entry, FileLock, FileSystem, FsCacheReqHandler, FsOptions,
    GetxattrReply, IoctlData, ListxattrReply, OpenOptions, SetattrValid, ZeroCopyReader,
    ZeroCopyWriter,
};
use fuse_backend_core::api::server::Server;
use fuse_backend_core::buffer::{self, Reader, Writer};
use fuse_backend_core::file_traits::FileReadWriteVolatile;
use vm_memory::{ByteValued, VolatileSlice};

/// The most requests one input is cut into, so that each run stays short.
const MAX_REQUESTS: usize = 16;

/// The size of the reply buffer, as the `/dev/fuse` transport allocates it.
const REPLY_BUFFER_SIZE: usize = MAX_BUFFER_SIZE as usize + 0x1000;

/// The size of a request frame.
const FRAME_SIZE: usize = 4;

/// Serves the requests in `data` with the sync server, and panics if a reply is wrong.
pub fn serve_sync(data: &[u8]) {
    serve(data, |server, reader, writer| {
        server.handle_message(reader, writer, Some(&mut NoDax), None)
    });
}

/// Serves the requests in `data` with the async server, and panics if a reply is wrong.
pub fn serve_async(data: &[u8]) {
    serve(data, |server, reader, writer| {
        // Safe because the reader and the writer outlive the future, which runs to completion.
        block_on(unsafe { server.async_handle_message(reader, writer, Some(&mut NoDax), None) })
    });
}

fn serve(
    data: &[u8],
    handle: impl Fn(&Server<FuzzFs>, Reader<'_>, MsgWriter<'_>) -> fuse_backend_core::Result<usize>,
) {
    let server = Server::new(FuzzFs);
    let log = RefCell::new(Vec::new());
    let mut data = data.to_vec();
    let mut rest = &mut data[..];
    for _ in 0..MAX_REQUESTS {
        if rest.len() < FRAME_SIZE {
            break;
        }
        let len = u16::from_le_bytes([rest[0], rest[1]]) as usize;
        let split = u16::from_le_bytes([rest[2], rest[3]]) as usize;
        let tail = &mut rest[FRAME_SIZE..];
        let (req, tail) = tail.split_at_mut(len.min(tail.len()));
        rest = tail;
        log.borrow_mut().clear();
        let res = handle(&server, reader(req, split), MsgWriter::new(&log));
        check(req, res, &log.borrow());
    }
}

/// Returns a reader over `buf`, in two buffers if `split` falls inside it.
fn reader(buf: &mut [u8], split: usize) -> Reader<'_> {
    if split == 0 || split >= buf.len() {
        return Reader::from_slice(buf);
    }
    let (first, second) = buf.split_at_mut(split);
    // Safe because the slices borrow `buf` for the lifetime of the reader.
    let slices = [first, second]
        .into_iter()
        .map(|s| unsafe { VolatileSlice::with_bitmap(s.as_mut_ptr(), s.len(), (), None) })
        .collect();
    Reader::from_volatile_slices(slices)
}

/// Reads a `T` from `buf` at `offset`, if `buf` holds one there.
fn read<T: ByteValued + Default>(buf: &[u8], offset: usize) -> Option<T> {
    let bytes = buf.get(offset..offset + size_of::<T>())?;
    let mut val = T::default();
    val.as_mut_slice().copy_from_slice(bytes);
    Some(val)
}

/// Whether the kernel waits for a reply to a request with `opcode`. The server has a list of
/// its own, and this one checks it.
fn takes_reply(opcode: u32) -> bool {
    !matches!(
        Opcode::from(opcode),
        Opcode::Forget | Opcode::BatchForget | Opcode::Interrupt | Opcode::NotifyReply
    )
}

/// Panics unless the server answered `req` as the module documentation says.
fn check(req: &[u8], res: fuse_backend_core::Result<usize>, sent: &[Message]) {
    // Formatted only when a check fails, to keep the fuzzer fast.
    let what = || match read::<InHeader>(req, 0) {
        Some(h) => format!(
            "opcode {} ({:?}), {} bytes",
            h.opcode,
            Opcode::from(h.opcode),
            req.len()
        ),
        None => format!("{} bytes", req.len()),
    };
    let header = match read::<InHeader>(req, 0) {
        Some(header) if takes_reply(header.opcode) => header,
        _ => {
            assert!(sent.is_empty(), "{} got a reply: {sent:?}", what());
            return;
        }
    };
    assert_eq!(
        sent.len(),
        1,
        "{} got {} replies, result {res:?}",
        what(),
        sent.len()
    );
    let reply = &sent[0];
    let out: OutHeader = read(&reply.head, 0).unwrap_or_else(|| panic!("{}: short reply", what()));
    let body = reply.len - size_of::<OutHeader>();
    assert_eq!(out.len as usize, reply.len, "{}: reply length", what());
    assert_eq!(out.unique, header.unique, "{}: reply unique", what());
    // The kernel rejects other errors, and a body after an error, with EINVAL.
    assert!(
        out.error <= 0 && out.error > -512,
        "{}: error {}",
        what(),
        out.error
    );
    assert!(
        out.error == 0 || body == 0,
        "{}: body after an error",
        what()
    );
    // The size field of ReadIn and GetxattrIn, which the reply must fit in.
    let size = |offset| read::<u32>(req, size_of::<InHeader>() + offset).unwrap() as usize;
    match Opcode::from(header.opcode) {
        Opcode::Read | Opcode::Readdir | Opcode::Readdirplus if out.error == 0 => {
            assert!(body <= size(16), "{}: reply too big", what());
        }
        Opcode::Getxattr | Opcode::Listxattr if out.error == 0 => {
            let max = size(0);
            if max == 0 {
                assert_eq!(body, size_of::<GetxattrOut>(), "{}: size reply", what());
            } else {
                assert!(body <= max, "{}: reply too big", what());
            }
        }
        _ => {}
    }
    let len = res.unwrap_or_else(|e| panic!("{} got a reply but failed: {e}", what()));
    // DESTROY replies but returns 0.
    if !matches!(Opcode::from(header.opcode), Opcode::Destroy) {
        assert_eq!(len, reply.len, "{}: returned size", what());
    }
}

/// Runs a future that never waits, as the futures of `FuzzFs` don't.
fn block_on<F: Future>(fut: F) -> F::Output {
    match pin!(fut).poll(&mut TaskContext::from_waker(Waker::noop())) {
        Poll::Ready(out) => out,
        Poll::Pending => panic!("the server waited for a future of FuzzFs"),
    }
}

/// A message sent to the kernel: its first bytes, as many as the reply header takes, and its
/// length. The checks read no more.
#[derive(Debug, Default)]
struct Message {
    head: Vec<u8>,
    len: usize,
}

impl Message {
    fn add(&mut self, buf: &[u8]) {
        let room = size_of::<OutHeader>().saturating_sub(self.head.len());
        self.head.extend_from_slice(&buf[..room.min(buf.len())]);
        self.len += buf.len();
    }
}

/// A writer that sends like the `/dev/fuse` one: each write is a message of its own until the
/// writer is split, and then a commit sends what both parts hold as one message. The messages
/// go to a shared log.
struct MsgWriter<'a> {
    log: &'a RefCell<Vec<Message>>,
    /// What the writer holds for a commit, once split.
    held: Option<Message>,
    /// The bytes this writer may write in all.
    cap: usize,
    /// The bytes written, sent or held.
    written: usize,
}

impl<'a> MsgWriter<'a> {
    fn new(log: &'a RefCell<Vec<Message>>) -> Self {
        MsgWriter {
            log,
            held: None,
            cap: REPLY_BUFFER_SIZE,
            written: 0,
        }
    }

    fn put(&mut self, bufs: &[&[u8]]) -> io::Result<usize> {
        let len = bufs.iter().map(|b| b.len()).sum::<usize>();
        if len > self.cap - self.written {
            return Err(io::Error::from_raw_os_error(libc::ENOSPC));
        }
        let mut sent = Message::default();
        let msg = self.held.as_mut().unwrap_or(&mut sent);
        bufs.iter().for_each(|b| msg.add(b));
        if self.held.is_none() {
            // An empty write goes to /dev/fuse too, which rejects it.
            self.log.borrow_mut().push(sent);
        }
        self.written += len;
        Ok(len)
    }
}

impl Write for MsgWriter<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.put(&[buf])
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        // Like the /dev/fuse writer, which sends nothing for no buffers.
        if bufs.is_empty() {
            return Ok(0);
        }
        let bufs: Vec<&[u8]> = bufs.iter().map(|b| &**b).collect();
        self.put(&bufs)
    }

    fn flush(&mut self) -> io::Result<()> {
        Err(io::Error::other("Writer does not support flush buffer."))
    }
}

impl Writer for MsgWriter<'_> {
    fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        _src: F,
        _count: usize,
        _off: u64,
    ) -> io::Result<usize> {
        // FuzzFs writes its data with `io::Write`.
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    fn split_at(&mut self, offset: usize) -> buffer::Result<Self> {
        // Like the /dev/fuse writer, split at `offset` from the start of the buffer. The
        // server splits before it writes.
        assert_eq!(self.written, 0, "split after a write");
        if offset > self.cap {
            return Err(buffer::Error::SplitOutOfBounds(offset));
        }
        let other = MsgWriter {
            log: self.log,
            held: Some(Message::default()),
            cap: self.cap - offset,
            written: 0,
        };
        self.cap = offset;
        self.held.get_or_insert_with(Message::default);
        Ok(other)
    }

    fn available_bytes(&self) -> usize {
        self.cap - self.written
    }

    fn bytes_written(&self) -> usize {
        self.written
    }

    fn commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        let Some(held) = &mut self.held else {
            return Ok(0);
        };
        let mut msg = std::mem::take(held);
        if let Some(other) = other.and_then(|o| o.held.as_ref()) {
            msg.add(&other.head);
            msg.len += other.len - other.head.len();
        }
        let len = msg.len;
        if len > 0 {
            self.log.borrow_mut().push(msg);
        }
        Ok(len)
    }

    async fn async_write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.put(&[data])
    }

    async fn async_write2(&mut self, data: &[u8], data2: &[u8]) -> io::Result<usize> {
        self.put(&[data, data2])
    }

    async fn async_write3(&mut self, data: &[u8], data2: &[u8], data3: &[u8]) -> io::Result<usize> {
        self.put(&[data, data2, data3])
    }

    async fn async_write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        self.put(&[buf]).map(|_| ())
    }

    async fn async_commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        self.commit(other)
    }
}

/// A DAX window that maps nothing, so that SETUPMAPPING and REMOVEMAPPING get to the file
/// system.
struct NoDax;

impl FsCacheReqHandler for NoDax {
    fn map(
        &mut self,
        _: u64,
        _: u64,
        _: u64,
        _: u64,
        _: std::os::unix::io::RawFd,
    ) -> io::Result<()> {
        Ok(())
    }

    fn unmap(&mut self, _: Vec<RemovemappingOne>) -> io::Result<()> {
        Ok(())
    }
}

/// A file system that answers from the inode and handle numbers in the request, so that the
/// input picks between success and failure and the size of each reply.
struct FuzzFs;

/// Fails one in four numbers.
fn result(n: u64) -> io::Result<()> {
    if n % 4 == 3 {
        Err(io::Error::from_raw_os_error(libc::ENOENT))
    } else {
        Ok(())
    }
}

/// A length up to 64 KiB.
fn len_of(n: u64) -> usize {
    (n >> 2) as usize % 0x10001
}

fn entry(inode: u64) -> Entry {
    Entry {
        inode,
        generation: inode >> 8,
        attr: attr(inode),
        attr_flags: 0,
        attr_timeout: Duration::from_nanos(inode),
        entry_timeout: Duration::from_nanos(inode >> 4),
    }
}

fn attr(inode: u64) -> stat64 {
    Attr {
        ino: inode,
        size: inode,
        mode: (inode as u32 & 0o7777) | libc::S_IFREG,
        ..Default::default()
    }
    .into()
}

/// Lists entries from `offset` until `add` takes no more, `inode % 64` entries at most.
fn list(
    inode: u64,
    offset: u64,
    mut add: impl FnMut(DirEntry, Entry) -> io::Result<usize>,
) -> io::Result<()> {
    static NAME: [u8; 300] = [b'n'; 300];
    result(inode)?;
    for i in offset..offset.saturating_add(inode % 64) {
        let dir_entry = DirEntry {
            ino: i,
            offset: i + 1,
            type_: libc::DT_REG as u32,
            name: &NAME[..1 + (i % 300) as usize],
        };
        if add(dir_entry, entry(i))? == 0 {
            break;
        }
    }
    Ok(())
}

/// The data that READ and IOCTL replies carry.
static DATA: [u8; 0x10000] = [0xa5; 0x10000];

#[allow(unused_variables)]
impl FileSystem for FuzzFs {
    type Inode = u64;
    type Handle = u64;

    fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
        Ok(capable)
    }

    fn lookup(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
        result(parent)?;
        Ok(entry(parent.wrapping_add(name.to_bytes().len() as u64)))
    }

    fn getattr(
        &self,
        ctx: &Context,
        inode: u64,
        handle: Option<u64>,
    ) -> io::Result<(stat64, Duration)> {
        result(inode).map(|()| (attr(inode), Duration::from_secs(1)))
    }

    fn setattr(
        &self,
        ctx: &Context,
        inode: u64,
        attr: stat64,
        handle: Option<u64>,
        valid: SetattrValid,
    ) -> io::Result<(stat64, Duration)> {
        result(inode).map(|()| (attr, Duration::from_secs(1)))
    }

    fn readlink(&self, ctx: &Context, inode: u64) -> io::Result<Vec<u8>> {
        result(inode).map(|()| vec![b'l'; len_of(inode)])
    }

    fn symlink(
        &self,
        ctx: &Context,
        linkname: &CStr,
        parent: u64,
        name: &CStr,
    ) -> io::Result<Entry> {
        result(parent).map(|()| entry(parent + 1))
    }

    fn mknod(
        &self,
        ctx: &Context,
        inode: u64,
        name: &CStr,
        mode: u32,
        rdev: u32,
        umask: u32,
    ) -> io::Result<Entry> {
        result(inode).map(|()| entry(inode + 1))
    }

    fn mkdir(
        &self,
        ctx: &Context,
        parent: u64,
        name: &CStr,
        mode: u32,
        umask: u32,
    ) -> io::Result<Entry> {
        result(parent).map(|()| entry(parent + 1))
    }

    fn unlink(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<()> {
        result(parent)
    }

    fn rmdir(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<()> {
        result(parent)
    }

    fn rename(
        &self,
        ctx: &Context,
        olddir: u64,
        oldname: &CStr,
        newdir: u64,
        newname: &CStr,
        flags: u32,
    ) -> io::Result<()> {
        result(olddir ^ newdir)
    }

    fn link(&self, ctx: &Context, inode: u64, newparent: u64, newname: &CStr) -> io::Result<Entry> {
        result(inode).map(|()| entry(inode))
    }

    fn open(
        &self,
        ctx: &Context,
        inode: u64,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
        result(inode)?;
        let opts = OpenOptions::from_bits_truncate((inode >> 2) as u32);
        Ok((Some(inode), opts, Some((inode >> 32) as u32)))
    }

    fn create(
        &self,
        ctx: &Context,
        parent: u64,
        name: &CStr,
        args: CreateIn,
    ) -> io::Result<(Entry, Option<u64>, OpenOptions, Option<u32>)> {
        result(parent)?;
        let opts = OpenOptions::from_bits_truncate(args.flags);
        Ok((entry(parent + 1), Some(parent), opts, None))
    }

    fn read(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        w: &mut dyn ZeroCopyWriter,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> io::Result<usize> {
        result(handle)?;
        // A short read when the handle asks for one.
        let len = (size as usize)
            .min(len_of(handle) * 16)
            .min(w.available_bytes());
        let mut left = len;
        while left > 0 {
            let n = left.min(DATA.len());
            w.write_all(&DATA[..n])?;
            left -= n;
        }
        Ok(len)
    }

    fn write(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        r: &mut dyn ZeroCopyReader,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<usize> {
        result(handle)?;
        let len = io::copy(&mut r.take(u64::from(size)), &mut io::sink())?;
        Ok(len as usize)
    }

    fn flush(&self, ctx: &Context, inode: u64, handle: u64, lock_owner: u64) -> io::Result<()> {
        result(handle)
    }

    fn fsync(&self, ctx: &Context, inode: u64, datasync: bool, handle: u64) -> io::Result<()> {
        result(handle)
    }

    fn fallocate(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> io::Result<()> {
        result(handle)
    }

    fn release(
        &self,
        ctx: &Context,
        inode: u64,
        flags: u32,
        handle: u64,
        flush: bool,
        flock_release: bool,
        lock_owner: Option<u64>,
    ) -> io::Result<()> {
        result(handle)
    }

    fn setxattr(
        &self,
        ctx: &Context,
        inode: u64,
        name: &CStr,
        value: &[u8],
        flags: u32,
    ) -> io::Result<()> {
        result(inode)
    }

    fn getxattr(
        &self,
        ctx: &Context,
        inode: u64,
        name: &CStr,
        size: u32,
    ) -> io::Result<GetxattrReply> {
        result(inode)?;
        let len = len_of(inode);
        if inode & 1 == 0 {
            Ok(GetxattrReply::Value(vec![b'v'; len]))
        } else {
            Ok(GetxattrReply::Count(len as u32))
        }
    }

    fn listxattr(&self, ctx: &Context, inode: u64, size: u32) -> io::Result<ListxattrReply> {
        result(inode)?;
        let len = len_of(inode);
        if inode & 1 == 0 {
            Ok(ListxattrReply::Names(b"user.a\0".repeat(len / 7)))
        } else {
            Ok(ListxattrReply::Count(len as u32))
        }
    }

    fn removexattr(&self, ctx: &Context, inode: u64, name: &CStr) -> io::Result<()> {
        result(inode)
    }

    fn opendir(
        &self,
        ctx: &Context,
        inode: u64,
        flags: u32,
    ) -> io::Result<(Option<u64>, OpenOptions)> {
        result(inode)?;
        Ok((
            Some(inode),
            OpenOptions::from_bits_truncate((inode >> 2) as u32),
        ))
    }

    fn readdir(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry) -> io::Result<usize>,
    ) -> io::Result<()> {
        list(inode, offset, |d, _| add_entry(d))
    }

    fn readdirplus(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, Entry) -> io::Result<usize>,
    ) -> io::Result<()> {
        list(inode, offset, add_entry)
    }

    fn fsyncdir(&self, ctx: &Context, inode: u64, datasync: bool, handle: u64) -> io::Result<()> {
        result(handle)
    }

    fn releasedir(&self, ctx: &Context, inode: u64, flags: u32, handle: u64) -> io::Result<()> {
        result(handle)
    }

    fn setupmapping(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        foffset: u64,
        len: u64,
        flags: u64,
        moffset: u64,
        vu_req: &mut dyn FsCacheReqHandler,
    ) -> io::Result<()> {
        result(handle)
    }

    fn removemapping(
        &self,
        ctx: &Context,
        inode: u64,
        requests: Vec<RemovemappingOne>,
        vu_req: &mut dyn FsCacheReqHandler,
    ) -> io::Result<()> {
        result(inode)
    }

    fn access(&self, ctx: &Context, inode: u64, mask: u32) -> io::Result<()> {
        result(inode)
    }

    fn lseek(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        offset: u64,
        whence: u32,
    ) -> io::Result<u64> {
        result(handle).map(|()| offset)
    }

    fn copy_file_range(
        &self,
        ctx: &Context,
        inode_in: u64,
        fh_in: u64,
        offset_in: u64,
        inode_out: u64,
        fh_out: u64,
        offset_out: u64,
        len: u64,
        flags: u64,
    ) -> io::Result<u32> {
        result(fh_in).map(|()| len as u32)
    }

    fn getlk(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        owner: u64,
        lock: FileLock,
        flags: u32,
    ) -> io::Result<FileLock> {
        result(handle).map(|()| lock)
    }

    fn setlk(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        owner: u64,
        lock: FileLock,
        flags: u32,
    ) -> io::Result<()> {
        result(handle)
    }

    fn setlkw(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        owner: u64,
        lock: FileLock,
        flags: u32,
    ) -> io::Result<()> {
        result(handle)
    }

    fn ioctl(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        flags: u32,
        cmd: u32,
        data: IoctlData,
        out_size: u32,
    ) -> io::Result<IoctlData<'_>> {
        result(handle)?;
        let len = (out_size as usize).min(DATA.len());
        Ok(IoctlData {
            result: cmd as i32,
            data: Some(&DATA[..len]),
        })
    }

    fn bmap(&self, ctx: &Context, inode: u64, block: u64, blocksize: u32) -> io::Result<u64> {
        result(inode).map(|()| block)
    }

    fn poll(
        &self,
        ctx: &Context,
        inode: u64,
        handle: u64,
        khandle: u64,
        flags: u32,
        events: u32,
    ) -> io::Result<u32> {
        result(handle).map(|()| events)
    }
}

impl AsyncFileSystem for FuzzFs {}

/// Frames `req` for the harness, with a reader that splits it after the header.
pub fn frame(req: &[u8]) -> Vec<u8> {
    let len = (req.len() as u16).to_le_bytes();
    let split = (size_of::<InHeader>() as u16).to_le_bytes();
    [&len[..], &split, req].concat()
}

/// Builds a request with `opcode` and `body` for the root inode.
pub fn request(opcode: Opcode, unique: u64, body: &[u8]) -> Vec<u8> {
    let header = InHeader {
        len: (size_of::<InHeader>() + body.len()) as u32,
        opcode: opcode as u32,
        unique,
        nodeid: 1,
        ..Default::default()
    };
    [header.as_slice(), body].concat()
}

/// Returns a framed, well formed request for each opcode the server knows, and a few
/// sequences, by name, as seeds for the fuzzer.
pub fn seeds() -> Vec<(String, Vec<u8>)> {
    use fuse_backend_core::abi::fuse_abi::*;
    use fuse_backend_core::abi::virtio_fs::{RemovemappingIn, SetupmappingIn};

    fn body<T: ByteValued>(arg: T, tail: &[u8]) -> Vec<u8> {
        [arg.as_slice(), tail].concat()
    }
    let read_in = body(
        ReadIn {
            fh: 0x40,
            size: 4096,
            ..Default::default()
        },
        &[],
    );
    let write_in = WriteIn {
        fh: 0x40,
        size: 16,
        ..Default::default()
    };
    let getxattr_in = GetxattrIn {
        size: 64,
        padding: 0,
    };
    let ioctl_in = IoctlIn {
        in_size: 8,
        out_size: 64,
        ..Default::default()
    };
    let forget_one = ForgetOne::default();
    let bodies = [
        (Opcode::Lookup, b"name\0".to_vec()),
        (Opcode::Forget, body(ForgetIn { nlookup: 1 }, &[])),
        (Opcode::Getattr, body(GetattrIn::default(), &[])),
        (Opcode::Setattr, body(SetattrIn::default(), &[])),
        (Opcode::Readlink, Vec::new()),
        (Opcode::Symlink, b"name\0target\0".to_vec()),
        (Opcode::Mknod, body(MknodIn::default(), b"name\0")),
        (Opcode::Mkdir, body(MkdirIn::default(), b"name\0")),
        (Opcode::Unlink, b"name\0".to_vec()),
        (Opcode::Rmdir, b"name\0".to_vec()),
        (Opcode::Rename, body(RenameIn { newdir: 1 }, b"old\0new\0")),
        (Opcode::Link, body(LinkIn { oldnodeid: 2 }, b"name\0")),
        (Opcode::Open, body(OpenIn::default(), &[])),
        (Opcode::Read, read_in.clone()),
        (Opcode::Write, body(write_in, &[0x5a; 16])),
        (Opcode::Statfs, Vec::new()),
        (Opcode::Release, body(ReleaseIn::default(), &[])),
        (Opcode::Fsync, body(FsyncIn::default(), &[])),
        (
            Opcode::Setxattr,
            body(SetxattrIn { size: 4, flags: 0 }, b"user.a\0abcd"),
        ),
        (Opcode::Getxattr, body(getxattr_in, b"user.a\0")),
        (Opcode::Listxattr, body(getxattr_in, &[])),
        (Opcode::Removexattr, b"user.a\0".to_vec()),
        (Opcode::Flush, body(FlushIn::default(), &[])),
        (Opcode::Opendir, body(OpenIn::default(), &[])),
        (Opcode::Readdir, read_in.clone()),
        (Opcode::Releasedir, body(ReleaseIn::default(), &[])),
        (Opcode::Fsyncdir, body(FsyncIn::default(), &[])),
        (Opcode::Getlk, body(LkIn::default(), &[])),
        (Opcode::Setlk, body(LkIn::default(), &[])),
        (Opcode::Setlkw, body(LkIn::default(), &[])),
        (Opcode::Access, body(AccessIn::default(), &[])),
        (Opcode::Create, body(CreateIn::default(), b"name\0")),
        (Opcode::Interrupt, body(InterruptIn { unique: 2 }, &[])),
        (Opcode::Bmap, body(BmapIn::default(), &[])),
        (Opcode::Destroy, Vec::new()),
        (Opcode::Ioctl, body(ioctl_in, &[0x11; 8])),
        (Opcode::Poll, body(PollIn::default(), &[])),
        (Opcode::NotifyReply, vec![0; 48]),
        (
            Opcode::BatchForget,
            body(
                BatchForgetIn { count: 2, dummy: 0 },
                &[forget_one.as_slice(); 2].concat(),
            ),
        ),
        (Opcode::Fallocate, body(FallocateIn::default(), &[])),
        (Opcode::Readdirplus, read_in),
        (Opcode::Rename2, body(Rename2In::default(), b"old\0new\0")),
        (Opcode::Lseek, body(LseekIn::default(), &[])),
        (Opcode::CopyFileRange, body(CopyFileRangeIn::default(), &[])),
        (Opcode::SetupMapping, body(SetupmappingIn::default(), &[])),
        (
            Opcode::RemoveMapping,
            body(
                RemovemappingIn { count: 1 },
                RemovemappingOne::default().as_slice(),
            ),
        ),
    ];
    let mut seeds: Vec<(String, Vec<u8>)> = bodies
        .into_iter()
        .map(|(opcode, body)| {
            let name = format!("{opcode:?}").to_lowercase();
            (name, frame(&request(opcode, 2, &body)))
        })
        .collect();

    // INIT with every capability in flags2, and then the requests that carry the
    // FUSE_EXT_GROUPS extension, which INIT has to turn on first.
    let init_in = InitIn {
        major: KERNEL_VERSION,
        minor: KERNEL_MINOR_VERSION,
        max_readahead: 0x20000,
        flags: FsOptions::INIT_EXT.bits() as u32,
    };
    let init_in2 = InitIn2 {
        flags2: (FsOptions::all().bits() >> 32) as u32,
        unused: [0; 11],
    };
    let init = frame(&request(
        Opcode::Init,
        1,
        &body(init_in, init_in2.as_slice()),
    ));
    let mut supp_groups = b"name\0\0\0\0".to_vec();
    for word in [16u32, FUSE_EXT_GROUPS, 1, 1000] {
        supp_groups.extend_from_slice(&word.to_ne_bytes());
    }
    seeds.push(("init".to_string(), init.clone()));
    for (name, opcode, arg) in [
        (
            "init_create",
            Opcode::Create,
            body(CreateIn::default(), &[]),
        ),
        ("init_mkdir", Opcode::Mkdir, body(MkdirIn::default(), &[])),
        ("init_mknod", Opcode::Mknod, body(MknodIn::default(), &[])),
    ] {
        let req = request(opcode, 3, &[arg, supp_groups.clone()].concat());
        seeds.push((name.to_string(), [init.clone(), frame(&req)].concat()));
    }
    seeds
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::path::{Path, PathBuf};

    fn fuzz_dir() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("..")
    }

    #[test]
    fn test_seeds() {
        // Checks the seeds and writes them to the corpus of each target, where
        // `cargo fuzz run` starts from.
        let targets = ["server", "async_server"];
        for target in targets {
            fs::create_dir_all(fuzz_dir().join("corpus").join(target)).unwrap();
        }
        for (name, seed) in seeds() {
            serve_sync(&seed);
            serve_async(&seed);
            for target in targets {
                fs::write(fuzz_dir().join("corpus").join(target).join(&name), &seed).unwrap();
            }
        }
    }

    #[test]
    fn test_regressions() {
        // The inputs that once broke the server.
        let mut replayed = 0;
        for entry in fs::read_dir(fuzz_dir().join("regressions")).unwrap() {
            let input = fs::read(entry.unwrap().path()).unwrap();
            serve_sync(&input);
            serve_async(&input);
            replayed += 1;
        }
        assert!(replayed > 0);
    }

    /// A xorshift generator, so that the mutations are the same in every run.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 << 13;
            self.0 ^= self.0 >> 7;
            self.0 ^= self.0 << 17;
            self.0
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    #[test]
    fn test_mutated_seeds() {
        // A small fuzzer for a stable toolchain: mutates the seeds and checks the replies.
        let seeds = seeds();
        let mut rng = Rng(0x2545_f491_4f6c_dd1d);
        for _ in 0..100_000 {
            let mut input = seeds[rng.below(seeds.len())].1.clone();
            if rng.below(4) == 0 {
                input.extend_from_slice(&seeds[rng.below(seeds.len())].1);
            }
            for _ in 0..1 + rng.below(8) {
                let i = rng.below(input.len());
                match rng.below(4) {
                    // Flip the bits of a byte.
                    0 => input[i] ^= rng.next() as u8,
                    // Set a byte to an edge value.
                    1 => input[i] = [0, 1, 0x7f, 0x80, 0xff][rng.below(5)],
                    // Cut the input short.
                    2 => input.truncate(i.max(FRAME_SIZE)),
                    // Change the length in the first request header.
                    _ => {
                        if input.len() >= FRAME_SIZE + 4 {
                            let len = (rng.next() as u32 % 512).to_ne_bytes();
                            input[FRAME_SIZE..FRAME_SIZE + 4].copy_from_slice(&len);
                        }
                    }
                }
            }
            serve_sync(&input);
            serve_async(&input);
        }
    }
}
