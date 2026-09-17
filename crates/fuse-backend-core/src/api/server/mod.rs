// Copyright (C) 2020-2022 Alibaba Cloud. All rights reserved.
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Fuse API Server to interconnect transport layers with filesystem drivers.
//!
//! The Fuse API server is a adapter layer between transport layers and file system drivers.
//! The main functionalities of the Fuse API server is:
//! * Support different types of transport layers, fusedev, virtio-fs or vhost-user-fs.
//! * Hide different transport layers details from file system drivers.
//! * Parse transport messages according to the Fuse ABI to avoid duplicated message decoding
//!   in every file system driver.
//! * Invoke file system driver handler to serve each request and send the reply.
//!
//! The Fuse API server is performance critical, so it's designed to support multi-threading by
//! adopting interior-mutability. And atomic operations are used to implement interior-mutability.

use std::ffi::CStr;
use std::io::{self, Read};
use std::marker::PhantomData;
use std::mem::size_of;
use std::sync::atomic::AtomicU64;

use crate::abi::fuse_abi::*;
use crate::api::filesystem::{Context, FileSystem, ZeroCopyReader, ZeroCopyWriter};
use crate::buffer::{Reader, Writer};
use crate::file_traits::FileReadWriteVolatile;
use crate::{bytes_to_cstr, BitmapSlice, Error, Result};
#[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
use std::sync::atomic::Ordering;

#[cfg(feature = "async-io")]
mod async_io;
mod sync_io;
// MockFS is only exercised by the linux-only sync_io tests, so parts of the
// module may be unused on other platforms or feature combinations.
#[cfg(test)]
#[allow(dead_code)]
mod test_util;

/// Maximum buffer size of FUSE requests.
#[cfg(target_os = "linux")]
pub const MAX_BUFFER_SIZE: u32 = 1 << 20;
/// Maximum buffer size of FUSE requests.
#[cfg(target_os = "macos")]
pub const MAX_BUFFER_SIZE: u32 = 1 << 25;
const MIN_READ_BUFFER: u32 = 8192;
const BUFFER_HEADER_SIZE: u32 = 0x1000;
const DIRENT_PADDING: [u8; 8] = [0; 8];

/// Maximum number of pages required for FUSE requests.
pub const MAX_REQ_PAGES: u16 = 256; // 1MB

/// Fuse Server to handle requests from the Fuse client and vhost user master.
pub struct Server<F: FileSystem + Sync> {
    fs: F,
    vers: AtomicU64,
    /// Extra capability flags to advertise in the INIT reply, requested
    /// through `set_uring()` (experimental fusedev-uring transport).
    #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
    extra_init_flags: AtomicU64,
    /// Capability flags actually enabled by the INIT exchange.
    #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
    negotiated_init_flags: AtomicU64,
}

impl<F: FileSystem + Sync> Server<F> {
    /// Create a Server instance from a filesystem driver object.
    pub fn new(fs: F) -> Server<F> {
        Server {
            fs,
            vers: AtomicU64::new(encode_version(KERNEL_VERSION, KERNEL_MINOR_VERSION)),
            #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
            extra_init_flags: AtomicU64::new(0),
            #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
            negotiated_init_flags: AtomicU64::new(0),
        }
    }

    /// Request serving FUSE requests over io_uring (experimental).
    ///
    /// Must be called before the session is mounted: the request is carried
    /// by the `FUSE_OVER_IO_URING` capability flag in the INIT reply. The
    /// outcome of the negotiation is reported by `uring_enabled()`, which is
    /// meaningful only after the INIT exchange has completed.
    #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
    pub fn set_uring(&self, enabled: bool) {
        let flags = if enabled {
            FsOptions::OVER_IO_URING.bits()
        } else {
            0
        };
        self.extra_init_flags.store(flags, Ordering::Relaxed);
    }

    /// Report whether the kernel accepted the `FUSE_OVER_IO_URING` capability
    /// during the INIT exchange. Returns false before INIT completes.
    #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
    pub fn uring_enabled(&self) -> bool {
        self.negotiated_init_flags.load(Ordering::Acquire) & FsOptions::OVER_IO_URING.bits() != 0
    }

    /// OR the extra INIT flags requested through `set_uring()` into the
    /// enabled capability set and remember the negotiation outcome.
    #[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
    fn apply_extra_init_flags(&self, capable: FsOptions, enabled: FsOptions) -> FsOptions {
        let extra = FsOptions::from_bits_truncate(self.extra_init_flags.load(Ordering::Relaxed));
        let mut enabled = enabled | (capable & extra);
        // The kernel applies InitOut.flags2 (capability bits 32 and above)
        // only if userspace also sets FUSE_INIT_EXT in the INIT reply, since
        // the "fuse: Apply flags2 only when userspace set the FUSE_INIT_EXT"
        // change in Linux 6.13. FUSE_OVER_IO_URING is bit 41 and therefore
        // travels in flags2, so advertise INIT_EXT whenever any upper bit is
        // enabled or the kernel would silently drop it.
        if enabled.bits() >> 32 != 0 {
            enabled |= FsOptions::INIT_EXT;
        }
        self.negotiated_init_flags
            .store(enabled.bits(), Ordering::Release);
        enabled
    }

    /// Remap the IDs in a request context to the IDs used by the backend
    /// filesystem, based on the inode referenced by the request.
    fn remap_ctx_ids<S: BitmapSlice, W: Writer>(
        &self,
        ctx: &mut SrvContext<F, S, W>,
    ) -> Result<()> {
        let nodeid = ctx.nodeid();
        self.fs
            .id_remap_with_nodeid(&mut ctx.context, nodeid)
            .map_err(|_| Error::FailedToRemapID((ctx.context.uid, ctx.context.gid)))
    }
}

struct ZcReader<'a, S: BitmapSlice = ()>(Reader<'a, S>);

impl<S: BitmapSlice> ZeroCopyReader for ZcReader<'_, S> {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.0.read_to_at(f, count, off)
    }
}

impl<S: BitmapSlice> io::Read for ZcReader<'_, S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.0.read(buf)
    }
}

struct ZcWriter<W>(W);

impl<W: Writer> ZeroCopyWriter for ZcWriter<W> {
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

impl<W: Writer> io::Write for ZcWriter<W> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.write(buf)
    }

    fn flush(&mut self) -> io::Result<()> {
        self.0.flush()
    }
}

/// The major and minor version number of the FUSE ABI
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ServerVersion {
    /// The major version number of the FUSE ABI
    pub major: u32,
    /// The minor version number of the FUSE ABI
    pub minor: u32,
}

/// Pack a `(major, minor)` FUSE ABI version pair into a single `u64`, so the
/// server can publish it with one lock-free atomic store instead of an
/// `ArcSwap`.
#[inline]
fn encode_version(major: u32, minor: u32) -> u64 {
    ((major as u64) << 32) | (minor as u64)
}

/// Unpack a `u64` produced by [`encode_version`] back into a [`ServerVersion`].
///
/// Only read on the LOOKUP hot path, which the sync handler compiles out under
/// `fuse-t`; without `async-io` some feature combinations never call it.
#[allow(dead_code)]
#[inline]
fn decode_version(v: u64) -> ServerVersion {
    ServerVersion {
        major: (v >> 32) as u32,
        minor: (v & 0xffff_ffff) as u32,
    }
}

struct ServerUtil();

impl ServerUtil {
    fn get_message_body<S: BitmapSlice>(
        r: &mut Reader<'_, S>,
        in_header: &InHeader,
        sub_hdr_sz: usize,
    ) -> Result<Vec<u8>> {
        let len = (in_header.len as usize)
            .checked_sub(size_of::<InHeader>())
            .and_then(|l| l.checked_sub(sub_hdr_sz))
            .ok_or(Error::InvalidHeaderLength)?;

        // Allocate buffer without zeroing out the content for performance.
        let mut buf = Vec::<u8>::with_capacity(len);
        // It's safe because read_exact() is called to fill all the allocated buffer.
        #[allow(clippy::uninit_vec)]
        unsafe {
            buf.set_len(len)
        };
        r.read_exact(&mut buf).map_err(Error::DecodeMessage)?;

        Ok(buf)
    }

    fn extract_two_cstrs(buf: &[u8]) -> Result<(&CStr, &CStr)> {
        if let Some(mut pos) = buf.iter().position(|x| *x == 0) {
            let first = CStr::from_bytes_with_nul(&buf[0..=pos]).map_err(Error::InvalidCString)?;
            pos += 1;
            if pos < buf.len() {
                return Ok((first, bytes_to_cstr(&buf[pos..])?));
            }
        }

        Err(Error::DecodeMessage(std::io::Error::from_raw_os_error(
            libc::EINVAL,
        )))
    }
}

/// Holds information of the handshake that happened between kernel and
/// userspace.
pub struct InitParams {
    /// Version of the FUSE ABI
    pub version: ServerVersion,
    /// Indicates the features supported by the kernel module
    pub capable: FsOptions,
    /// Indicates the features that we requested
    pub want: FsOptions,
}

/// Provide concrete backend filesystem a way to catch information/metrics from fuse.
pub trait MetricsHook {
    /// `collect()` will be invoked before the real request is processed
    fn collect(&self, ih: &InHeader);
    /// `on_init_params()` will be called with some agreed connection parameters
    fn on_init_params(&self, _init_params: &InitParams) {}
    /// `release()` will be invoked after the real request is processed
    fn release(&self, oh: Option<&OutHeader>);
}

struct SrvContext<'a, F, S: BitmapSlice, W: Writer> {
    in_header: InHeader,
    context: Context,
    r: Reader<'a, S>,
    w: W,
    phantom: PhantomData<F>,
    phantom2: PhantomData<S>,
}

impl<'a, F: FileSystem, S: BitmapSlice, W: Writer> SrvContext<'a, F, S, W> {
    fn new(in_header: InHeader, r: Reader<'a, S>, w: W) -> Self {
        let context = Context::from(&in_header);

        SrvContext {
            in_header,
            context,
            r,
            w,
            phantom: PhantomData,
            phantom2: PhantomData,
        }
    }

    fn context(&self) -> &Context {
        &self.context
    }

    fn unique(&self) -> u64 {
        self.in_header.unique
    }

    fn nodeid(&self) -> F::Inode {
        self.in_header.nodeid.into()
    }

    fn take_reader(&mut self) -> Reader<'a, S> {
        let mut reader = Reader::default();

        std::mem::swap(&mut self.r, &mut reader);

        reader
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_cstrs() {
        assert_eq!(
            ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8, 0x0, 0x3, 0x0]).unwrap(),
            (
                CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap(),
                CStr::from_bytes_with_nul(&[0x3u8, 0x0]).unwrap(),
            )
        );
        assert_eq!(
            ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8, 0x0, 0x3, 0x0, 0x0]).unwrap(),
            (
                CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap(),
                CStr::from_bytes_with_nul(&[0x3u8, 0x0]).unwrap(),
            )
        );
        assert_eq!(
            ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8, 0x0, 0x3, 0x0, 0x4]).unwrap(),
            (
                CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap(),
                CStr::from_bytes_with_nul(&[0x3u8, 0x0]).unwrap(),
            )
        );
        assert_eq!(
            ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8, 0x0, 0x0, 0x4]).unwrap(),
            (
                CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap(),
                CStr::from_bytes_with_nul(&[0x0]).unwrap(),
            )
        );

        ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8, 0x0, 0x3]).unwrap_err();
        ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8, 0x0]).unwrap_err();
        ServerUtil::extract_two_cstrs(&[0x1u8, 0x2u8]).unwrap_err();
    }

    #[test]
    fn test_get_message_body() {
        let mut read_buf = [0u8; 4096];

        let mut r = Reader::<()>::from_slice(&mut read_buf);
        let in_header = InHeader {
            len: 0x1000,
            ..Default::default()
        };
        let buf = ServerUtil::get_message_body(&mut r, &in_header, 0).unwrap();
        assert_eq!(buf.len(), 0x1000 - size_of::<InHeader>());

        let mut r = Reader::<()>::from_slice(&mut read_buf);
        let in_header = InHeader {
            len: 0x1000,
            ..Default::default()
        };
        let buf = ServerUtil::get_message_body(&mut r, &in_header, 0x100).unwrap();
        assert_eq!(buf.len(), 0x1000 - size_of::<InHeader>() - 0x100);

        let mut r = Reader::<()>::from_slice(&mut read_buf);
        let in_header = InHeader {
            len: 0x1000,
            ..Default::default()
        };
        // shoutld fail because of invalid sub header size
        assert!(ServerUtil::get_message_body(&mut r, &in_header, 0x1000).is_err());

        let mut r = Reader::<()>::from_slice(&mut read_buf);
        let in_header = InHeader {
            len: 0x1000,
            ..Default::default()
        };
        // shoutld fail because of invalid sub header size
        assert!(ServerUtil::get_message_body(&mut r, &in_header, 0x1001).is_err());
    }
}
