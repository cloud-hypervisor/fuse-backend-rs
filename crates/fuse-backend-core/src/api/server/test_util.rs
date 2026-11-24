// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Test doubles shared by the `api::server` unit tests.
//!
//! [`MockFS`] is an empty [`FileSystem`] relying entirely on the trait's
//! default method implementations, and [`TestWriter`] is a [`Writer`] that
//! captures reply messages into a caller supplied byte buffer. Together they
//! let the server operation tests exercise request parsing and reply encoding
//! without depending on transport specific machinery.

use std::cmp;
use std::io::{self, IoSlice};
use std::mem::size_of;
use std::ptr::copy_nonoverlapping;

use vm_memory::{ByteValued, VolatileSlice};

use crate::abi::fuse_abi::*;
#[cfg(feature = "virtiofs")]
use crate::abi::virtio_fs::{RemovemappingIn, RemovemappingOne, SetupmappingIn};
use crate::api::filesystem::FileSystem;
use crate::buffer::{IoBuffers, Result, Writer};
use crate::file_traits::FileReadWriteVolatile;

/// An empty [`FileSystem`] used as backend of the server unit tests.
///
/// Every trait method keeps its default implementation: `init()` succeeds
/// with an empty capability set and all other operations fail with `ENOSYS`,
/// so the tests only exercise the server side reply logic.
pub(crate) struct MockFS;

impl FileSystem for MockFS {
    type Inode = u64;
    type Handle = u64;
}

#[cfg(feature = "async-io")]
impl crate::api::filesystem::AsyncFileSystem for MockFS {}

/// The opcodes to send `oversized_request()` with: one that takes a reply, and those that take
/// none.
pub(crate) const OVERSIZED_OPCODES: [Opcode; 5] = [
    Opcode::Getattr,
    Opcode::Forget,
    Opcode::BatchForget,
    Opcode::Interrupt,
    Opcode::NotifyReply,
];

/// The unique number of the requests from [`request()`] and [`request_for()`].
pub(crate) const UNIQUE: u64 = 42;

/// Builds a request for the root inode with `opcode` and `body`.
pub(crate) fn request(opcode: Opcode, body: &[u8]) -> Vec<u8> {
    request_for(opcode, ROOT_ID, body)
}

/// Builds a request for `nodeid` with `opcode` and `body`.
pub(crate) fn request_for(opcode: Opcode, nodeid: u64, body: &[u8]) -> Vec<u8> {
    let header = InHeader {
        len: (size_of::<InHeader>() + body.len()) as u32,
        opcode: opcode as u32,
        unique: UNIQUE,
        nodeid,
        ..Default::default()
    };
    [header.as_slice(), body].concat()
}

/// Returns a body for each opcode that has one, such that every shorter prefix of it is
/// malformed: a fixed part cut short, a name without its NUL, or a value shorter than its size.
pub(crate) fn request_bodies() -> Vec<(Opcode, Vec<u8>)> {
    fn body<T: ByteValued>(arg: T, tail: &[u8]) -> Vec<u8> {
        [arg.as_slice(), tail].concat()
    }
    let batch_forget_in = BatchForgetIn { count: 1, dummy: 0 };
    let setxattr_in = SetxattrIn { size: 4, flags: 0 };
    let notify_retrieve_in = NotifyRetrieveIn {
        size: 4,
        ..Default::default()
    };
    vec![
        (Opcode::Lookup, b"name\0".to_vec()),
        (Opcode::Forget, body(ForgetIn::default(), &[])),
        (Opcode::Getattr, body(GetattrIn::default(), &[])),
        (Opcode::Setattr, body(SetattrIn::default(), &[])),
        (Opcode::Symlink, b"name\0target\0".to_vec()),
        (Opcode::Mknod, body(MknodIn::default(), b"name\0")),
        (Opcode::Mkdir, body(MkdirIn::default(), b"name\0")),
        (Opcode::Unlink, b"name\0".to_vec()),
        (Opcode::Rmdir, b"name\0".to_vec()),
        (Opcode::Rename, body(RenameIn::default(), b"old\0new\0")),
        (Opcode::Link, body(LinkIn::default(), b"name\0")),
        (Opcode::Open, body(OpenIn::default(), &[])),
        (Opcode::Read, body(ReadIn::default(), &[])),
        (Opcode::Write, body(WriteIn::default(), &[])),
        (Opcode::Release, body(ReleaseIn::default(), &[])),
        (Opcode::Fsync, body(FsyncIn::default(), &[])),
        (Opcode::Setxattr, body(setxattr_in, b"user.a\0abcd")),
        (Opcode::Getxattr, body(GetxattrIn::default(), b"user.a\0")),
        (Opcode::Listxattr, body(GetxattrIn::default(), &[])),
        (Opcode::Removexattr, b"user.a\0".to_vec()),
        (Opcode::Flush, body(FlushIn::default(), &[])),
        (Opcode::Init, body(InitIn::default(), &[])),
        (Opcode::Opendir, body(OpenIn::default(), &[])),
        (Opcode::Readdir, body(ReadIn::default(), &[])),
        (Opcode::Releasedir, body(ReleaseIn::default(), &[])),
        (Opcode::Fsyncdir, body(FsyncIn::default(), &[])),
        (Opcode::Getlk, body(LkIn::default(), &[])),
        (Opcode::Setlk, body(LkIn::default(), &[])),
        (Opcode::Setlkw, body(LkIn::default(), &[])),
        (Opcode::Access, body(AccessIn::default(), &[])),
        (Opcode::Create, body(CreateIn::default(), b"name\0")),
        (Opcode::Interrupt, body(InterruptIn::default(), &[])),
        (Opcode::Bmap, body(BmapIn::default(), &[])),
        (Opcode::Ioctl, body(IoctlIn::default(), &[])),
        (Opcode::Poll, body(PollIn::default(), &[])),
        (Opcode::NotifyReply, body(notify_retrieve_in, b"abcd")),
        (
            Opcode::BatchForget,
            body(batch_forget_in, ForgetOne::default().as_slice()),
        ),
        (Opcode::Fallocate, body(FallocateIn::default(), &[])),
        (Opcode::Readdirplus, body(ReadIn::default(), &[])),
        (Opcode::Rename2, body(Rename2In::default(), b"old\0new\0")),
        (Opcode::Lseek, body(LseekIn::default(), &[])),
        (Opcode::CopyFileRange, body(CopyFileRangeIn::default(), &[])),
        #[cfg(feature = "virtiofs")]
        (Opcode::SetupMapping, body(SetupmappingIn::default(), &[])),
        #[cfg(feature = "virtiofs")]
        (
            Opcode::RemoveMapping,
            body(
                RemovemappingIn { count: 1 },
                RemovemappingOne::default().as_slice(),
            ),
        ),
    ]
}

/// Builds a request with `opcode` whose header claims more bytes than a request can have.
pub(crate) fn oversized_request(opcode: Opcode) -> Vec<u8> {
    let mut req = request(opcode, &[0u8; 64]);
    let header = InHeader {
        len: MAX_BUFFER_SIZE + super::BUFFER_HEADER_SIZE + 1,
        ..*InHeader::from_slice(&req[..size_of::<InHeader>()]).unwrap()
    };
    req[..size_of::<InHeader>()].copy_from_slice(header.as_slice());
    req
}

/// Checks what the server did with `oversized_request(opcode)`: `ENOMEM` if the request takes a
/// reply, and nothing if it takes none.
pub(crate) fn check_oversized(opcode: Opcode, res: crate::Result<usize>, reply: &[u8]) {
    if !super::takes_reply(opcode as u32) {
        assert!(res.is_err(), "{:?}: {:?}", opcode, res);
        assert!(reply.iter().all(|&b| b == 0), "{:?} got a reply", opcode);
    } else {
        let out = OutHeader::from_slice(&reply[..size_of::<OutHeader>()]).unwrap();
        assert_eq!(out.error, -libc::ENOMEM, "{:?}", opcode);
    }
}

/// A virtio-fs DAX window that maps nothing, so that SETUPMAPPING and REMOVEMAPPING get to
/// parse their bodies.
pub(crate) struct NoDax;

#[cfg(not(feature = "virtiofs"))]
impl crate::api::filesystem::FsCacheReqHandler for NoDax {}

#[cfg(feature = "virtiofs")]
impl crate::api::filesystem::FsCacheReqHandler for NoDax {
    fn map(
        &mut self,
        _foffset: u64,
        _moffset: u64,
        _len: u64,
        _flags: u64,
        _fd: std::os::unix::io::RawFd,
    ) -> io::Result<()> {
        Ok(())
    }

    fn unmap(&mut self, _requests: Vec<RemovemappingOne>) -> io::Result<()> {
        Ok(())
    }
}

/// Checks what the server did with a request with `opcode` and a malformed body of `len`
/// bytes: one `EINVAL` reply if the request takes a reply, and none if it takes none.
pub(crate) fn check_malformed(opcode: Opcode, len: usize, res: crate::Result<usize>, reply: &[u8]) {
    let what = format!("{:?} with {} bytes", opcode, len);
    let out_len = size_of::<OutHeader>();
    if !super::takes_reply(opcode as u32) {
        // INTERRUPT doesn't read its body, so it doesn't fail.
        assert!(
            res.is_err() || matches!(opcode, Opcode::Interrupt),
            "{}: {:?}",
            what,
            res
        );
        assert!(reply.iter().all(|&b| b == 0), "{} got a reply", what);
        return;
    }
    // The server returns the number of bytes written, so a second reply would show here.
    assert_eq!(res.ok(), Some(out_len), "{}", what);
    let out = OutHeader::from_slice(&reply[..out_len]).unwrap();
    assert_eq!(
        (out.len as usize, out.error, out.unique),
        (out_len, -libc::EINVAL, UNIQUE),
        "{}",
        what
    );
}

/// A [`Writer`] that captures reply messages into a caller supplied buffer.
///
/// It mirrors the semantics of the virtio-fs writer: writes go straight into
/// the buffer, `commit()` is a no-op returning zero, and `bytes_written()`
/// counts the bytes actually copied, which is what the server reports as the
/// reply size. The async methods do the same and never wait.
pub(crate) struct TestWriter<'a> {
    buffers: IoBuffers<'a, ()>,
}

impl<'a> TestWriter<'a> {
    /// Create a `TestWriter` over a mutable byte buffer.
    pub(crate) fn new(buf: &'a mut [u8]) -> Self {
        // Safe because the `TestWriter` is bound to the lifetime of `buf`.
        let slice = unsafe { VolatileSlice::with_bitmap(buf.as_mut_ptr(), buf.len(), (), None) };
        TestWriter {
            buffers: IoBuffers::new(vec![slice]),
        }
    }

    fn check_available_space(&self, len: usize) -> io::Result<()> {
        if len > self.buffers.available_bytes() {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    self.buffers.available_bytes(),
                    len
                ),
            ))
        } else {
            Ok(())
        }
    }
}

impl io::Write for TestWriter<'_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.check_available_space(buf.len())?;

        self.buffers.consume_for_write(buf.len(), |bufs| {
            let mut rem = buf;
            let mut total = 0;
            for buf in bufs {
                let copy_len = cmp::min(rem.len(), buf.len());

                // Safe because we have already verified that `buf` points to valid memory.
                unsafe { copy_nonoverlapping(rem.as_ptr(), buf.as_ptr(), copy_len) };
                rem = &rem[copy_len..];
                total += copy_len;
            }
            Ok(total)
        })
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        let total: usize = bufs.iter().map(|b| b.len()).sum();
        self.check_available_space(total)?;

        let mut count = 0;
        for buf in bufs.iter().filter(|b| !b.is_empty()) {
            count += self.write(buf)?;
        }
        Ok(count)
    }

    fn flush(&mut self) -> io::Result<()> {
        // Nothing to flush since the writes go straight into the buffer.
        Ok(())
    }
}

impl Writer for TestWriter<'_> {
    fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        _src: F,
        _count: usize,
        _off: u64,
    ) -> io::Result<usize> {
        // The mock filesystem never succeeds, so the zero copy path is
        // never taken by the tests.
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    fn split_at(&mut self, offset: usize) -> Result<Self> {
        self.buffers
            .split_at(offset)
            .map(|buffers| TestWriter { buffers })
    }

    fn available_bytes(&self) -> usize {
        self.buffers.available_bytes()
    }

    fn bytes_written(&self) -> usize {
        self.buffers.bytes_consumed()
    }

    fn commit(&mut self, _other: Option<&Self>) -> io::Result<usize> {
        // Writes go straight into the buffer, so there's nothing to commit.
        Ok(0)
    }

    #[cfg(feature = "async-io")]
    async fn async_write(&mut self, data: &[u8]) -> io::Result<usize> {
        io::Write::write(self, data)
    }

    #[cfg(feature = "async-io")]
    async fn async_write2(&mut self, data: &[u8], data2: &[u8]) -> io::Result<usize> {
        io::Write::write_vectored(self, &[IoSlice::new(data), IoSlice::new(data2)])
    }

    #[cfg(feature = "async-io")]
    async fn async_write3(&mut self, data: &[u8], data2: &[u8], data3: &[u8]) -> io::Result<usize> {
        io::Write::write_vectored(
            self,
            &[IoSlice::new(data), IoSlice::new(data2), IoSlice::new(data3)],
        )
    }

    #[cfg(feature = "async-io")]
    async fn async_write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        io::Write::write_all(self, buf)
    }

    #[cfg(feature = "async-io")]
    async fn async_commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        self.commit(other)
    }
}
