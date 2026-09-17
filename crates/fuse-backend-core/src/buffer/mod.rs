// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Transport-neutral buffer machinery shared by the `api` layer and all transports.
//!
//! This module hosts the pieces that the transport-neutral `api` layer depends
//! on: the [`Reader`] over request buffers, the [`Writer`] trait implemented by
//! each transport's reply writer, the buffer [`Error`] type and the
//! [`pagesize`] helper. Everything is re-exported from `transport`, so existing
//! import paths keep resolving.

use std::any::Any;
use std::collections::VecDeque;
use std::io::{self, Read};
use std::mem::{size_of, MaybeUninit};
use std::ptr::copy_nonoverlapping;
use std::sync::LazyLock;
use std::{cmp, fmt};

use libc::{sysconf, _SC_PAGESIZE};
use vm_memory::{ByteValued, VolatileSlice};

#[cfg(feature = "async-io")]
use crate::file_buf::FileVolatileBuf;
use crate::file_buf::FileVolatileSlice;
#[cfg(feature = "async-io")]
use crate::file_traits::AsyncFileReadWriteVolatile;
use crate::file_traits::FileReadWriteVolatile;
use crate::BitmapSlice;

/// Buffer layer specific error codes.
#[derive(Debug)]
pub enum Error {
    /// Virtio queue descriptor chain overflows.
    DescriptorChainOverflow,
    #[cfg(feature = "virtiofs")]
    /// Failed to find memory region for guest physical address.
    FindMemoryRegion,
    #[cfg(feature = "virtiofs")]
    /// Invalid virtio queue descriptor chain.
    InvalidChain,
    /// Invalid paramater.
    InvalidParameter,
    /// Generic IO error.
    IoError(io::Error),
    /// Out of bounds when splitting VolatileSplice.
    SplitOutOfBounds(usize),
    /// Failed to access volatile memory.
    VolatileMemoryError(vm_memory::VolatileMemoryError),
    #[cfg(feature = "fusedev")]
    /// Session errors
    SessionFailure(String),
    #[cfg(feature = "fusedev-uring")]
    /// FUSE-over-io_uring is not available: the kernel rejected the
    /// `FUSE_OVER_IO_URING` init flag or uring registration failed.
    UringNotSupported,
    #[cfg(feature = "virtiofs")]
    /// Failed to access guest memory.
    GuestMemoryError(vm_memory::GuestMemoryError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            DescriptorChainOverflow => write!(
                f,
                "the combined length of all the buffers in a `DescriptorChain` would overflow"
            ),
            #[cfg(feature = "virtiofs")]
            FindMemoryRegion => write!(f, "no memory region for this address range"),
            #[cfg(feature = "virtiofs")]
            InvalidChain => write!(f, "invalid descriptor chain"),
            InvalidParameter => write!(f, "invalid parameter"),
            IoError(e) => write!(f, "descriptor I/O error: {e}"),
            SplitOutOfBounds(off) => write!(f, "`DescriptorChain` split is out of bounds: {off}"),
            VolatileMemoryError(e) => write!(f, "volatile memory error: {e}"),

            #[cfg(feature = "fusedev")]
            SessionFailure(e) => write!(f, "fuse session failure: {e}"),

            #[cfg(feature = "fusedev-uring")]
            UringNotSupported => write!(
                f,
                "FUSE-over-io_uring is not available on this kernel or was rejected"
            ),

            #[cfg(feature = "virtiofs")]
            GuestMemoryError(e) => write!(f, "descriptor guest memory error: {e}"),
        }
    }
}

impl From<Box<dyn Any + Send>> for Error {
    fn from(value: Box<dyn Any + Send>) -> Self {
        let err = value.downcast::<Error>().unwrap();
        *err
    }
}

/// Specialized version of [std::result::Result] for buffer layer operations.
pub type Result<T> = std::result::Result<T, Error>;

impl std::error::Error for Error {}

/// A list of `VolatileSlice` buffers with tracking of consumed bytes.
///
/// This is the shared buffer machinery behind [`Reader`] and the
/// transport-specific writers. Transports construct it from their own
/// buffers via [`IoBuffers::new`] and drive it through the public
/// consumption/marking methods.
#[derive(Clone)]
pub struct IoBuffers<'a, S> {
    buffers: VecDeque<VolatileSlice<'a, S>>,
    bytes_consumed: usize,
}

impl<S: BitmapSlice> Default for IoBuffers<'_, S> {
    fn default() -> Self {
        IoBuffers {
            buffers: VecDeque::new(),
            bytes_consumed: 0,
        }
    }
}

impl<'a, S: BitmapSlice> IoBuffers<'a, S> {
    /// Create an `IoBuffers` from a list of volatile slices.
    ///
    /// The returned object starts with zero bytes consumed.
    pub fn new(slices: Vec<VolatileSlice<'a, S>>) -> Self {
        IoBuffers {
            buffers: slices.into(),
            bytes_consumed: 0,
        }
    }

    /// Return the number of bytes available for consumption.
    pub fn available_bytes(&self) -> usize {
        // This is guaranteed not to overflow because the total length of the chain
        // is checked during all creations of `IoBuffers` (see
        // `Reader::new()` and `Writer::new()`).
        self.buffers
            .iter()
            .fold(0usize, |count, buf| count + buf.len())
    }

    /// Return the number of bytes already consumed.
    pub fn bytes_consumed(&self) -> usize {
        self.bytes_consumed
    }

    pub(crate) fn allocate_file_volatile_slice(&self, count: usize) -> Vec<FileVolatileSlice<'_>> {
        let mut rem = count;
        let mut bufs: Vec<FileVolatileSlice> = Vec::with_capacity(self.buffers.len());

        for buf in &self.buffers {
            if rem == 0 {
                break;
            }

            // If buffer contains more data than `rem`, truncate buffer to `rem`, otherwise
            // more data is written out and causes data corruption.
            let local_buf = if buf.len() > rem {
                // Safe because we just check rem < buf.len()
                FileVolatileSlice::from_volatile_slice(&buf.subslice(0, rem).unwrap())
            } else {
                FileVolatileSlice::from_volatile_slice(buf)
            };
            bufs.push(local_buf);

            // Don't need check_sub() as we just made sure rem >= local_buf.len()
            rem -= local_buf.len();
        }

        bufs
    }

    #[cfg(feature = "async-io")]
    pub(crate) unsafe fn prepare_io_buf(&self, count: usize) -> Vec<FileVolatileBuf> {
        let mut rem = count;
        let mut bufs = Vec::with_capacity(self.buffers.len());

        for buf in &self.buffers {
            if rem == 0 {
                break;
            }

            // If buffer contains more data than `rem`, truncate buffer to `rem`, otherwise
            // more data is written out and causes data corruption.
            let local_buf = if buf.len() > rem {
                // Safe because we just check rem < buf.len()
                buf.subslice(0, rem).unwrap()
            } else {
                buf.clone()
            };
            // Safe because we just change the interface to access underlying buffers.
            bufs.push(FileVolatileBuf::from_raw_ptr(
                local_buf.ptr_guard_mut().as_ptr(),
                local_buf.len(),
                local_buf.len(),
            ));

            // Don't need check_sub() as we just made sure rem >= local_buf.len()
            rem -= local_buf.len();
        }

        bufs
    }

    /// Prepare async write buffers for at most `count` bytes.
    ///
    /// The returned `FileVolatileBuf` objects start with zero filled bytes,
    /// ready for async reads that fill them; the caller must account the
    /// filled bytes via `mark_dirty()` and `mark_used()`.
    ///
    /// # Safety
    ///
    /// The caller must keep the underlying buffers alive while the returned
    /// `FileVolatileBuf` objects are in use.
    #[cfg(feature = "async-io")]
    pub unsafe fn prepare_mut_io_buf(&self, count: usize) -> Vec<FileVolatileBuf> {
        let mut rem = count;
        let mut bufs = Vec::with_capacity(self.buffers.len());

        for buf in &self.buffers {
            if rem == 0 {
                break;
            }

            // If buffer contains more data than `rem`, truncate buffer to `rem`, otherwise
            // more data is written out and causes data corruption.
            let local_buf = if buf.len() > rem {
                // Safe because we just check rem < buf.len()
                buf.subslice(0, rem).unwrap()
            } else {
                buf.clone()
            };
            bufs.push(FileVolatileBuf::from_raw_ptr(
                local_buf.ptr_guard_mut().as_ptr(),
                0,
                local_buf.len(),
            ));

            // Don't need check_sub() as we just made sure rem >= local_buf.len()
            rem -= local_buf.len();
        }

        bufs
    }

    /// Mark up to `count` bytes as dirty in the underlying bitmaps.
    pub fn mark_dirty(&self, count: usize) {
        let mut rem = count;

        for buf in &self.buffers {
            if rem == 0 {
                break;
            }

            // If buffer contains more data than `rem`, truncate buffer to `rem`, otherwise
            // more data is written out and causes data corruption.
            let local_buf = if buf.len() > rem {
                // Safe because we just check rem < buf.len()
                buf.subslice(0, rem).unwrap()
            } else {
                buf.clone()
            };
            local_buf.bitmap().mark_dirty(0, local_buf.len());

            // Don't need check_sub() as we just made sure rem >= local_buf.len()
            rem -= local_buf.len();
        }
    }

    /// Account `bytes_consumed` bytes as consumed from the buffer list.
    ///
    /// Fully consumed buffers are dropped; a partially consumed buffer is
    /// split so that the remainder stays available.
    pub fn mark_used(&mut self, bytes_consumed: usize) -> io::Result<()> {
        // This can happen if a driver tricks a device into reading/writing more data than
        // fits in a `usize`.
        let total_bytes_consumed =
            self.bytes_consumed
                .checked_add(bytes_consumed)
                .ok_or_else(|| {
                    io::Error::new(io::ErrorKind::InvalidData, Error::DescriptorChainOverflow)
                })?;

        let mut rem = bytes_consumed;
        while let Some(buf) = self.buffers.pop_front() {
            if rem < buf.len() {
                // Split the slice and push the remainder back into the buffer list. Safe because we
                // know that `rem` is not out of bounds due to the check and we checked the bounds
                // on `buf` when we added it to the buffer list.
                self.buffers.push_front(buf.offset(rem).unwrap());
                break;
            }

            // No need for checked math because we know that `buf.size() <= rem`.
            rem -= buf.len();
        }

        self.bytes_consumed = total_bytes_consumed;

        Ok(())
    }

    /// Consumes at most `count` bytes from the `DescriptorChain`. Callers must provide a function
    /// that takes a `&[FileVolatileSlice]` and returns the total number of bytes consumed. This
    /// function guarantees that the combined length of all the slices in the `&[FileVolatileSlice]` is
    /// less than or equal to `count`. `mark_dirty` is used for tracing dirty pages.
    ///
    /// # Errors
    ///
    /// If the provided function returns any error then no bytes are consumed from the buffer and
    /// the error is returned to the caller.
    pub(crate) fn consume<F>(&mut self, mark_dirty: bool, count: usize, f: F) -> io::Result<usize>
    where
        F: FnOnce(&[FileVolatileSlice]) -> io::Result<usize>,
    {
        let bufs = self.allocate_file_volatile_slice(count);
        if bufs.is_empty() {
            Ok(0)
        } else {
            let bytes_consumed = f(&bufs)?;
            if mark_dirty {
                self.mark_dirty(bytes_consumed);
            }
            self.mark_used(bytes_consumed)?;
            Ok(bytes_consumed)
        }
    }

    pub(crate) fn consume_for_read<F>(&mut self, count: usize, f: F) -> io::Result<usize>
    where
        F: FnOnce(&[FileVolatileSlice]) -> io::Result<usize>,
    {
        self.consume(false, count, f)
    }

    /// Consumes for write, marking the consumed bytes dirty.
    ///
    /// Same contract as the private `consume()` with `mark_dirty` set;
    /// exposed for transports (e.g. virtiofs) that consume their writer
    /// buffers from their own crates.
    pub fn consume_for_write<F>(&mut self, count: usize, f: F) -> io::Result<usize>
    where
        F: FnOnce(&[FileVolatileSlice]) -> io::Result<usize>,
    {
        self.consume(true, count, f)
    }

    /// Split the buffer list into two at the given byte offset.
    ///
    /// After the split, `self` keeps the first `offset` bytes and the
    /// returned `IoBuffers` holds the remainder; both start with zero
    /// bytes consumed. Returns an error if `offset` exceeds the available
    /// bytes.
    pub fn split_at(&mut self, offset: usize) -> Result<Self> {
        let mut rem = offset;
        let pos = self.buffers.iter().position(|buf| {
            if rem < buf.len() {
                true
            } else {
                rem -= buf.len();
                false
            }
        });

        if let Some(at) = pos {
            let mut other = self.buffers.split_off(at);

            if rem > 0 {
                // There must be at least one element in `other` because we checked
                // its `size` value in the call to `position` above.
                let front = other.pop_front().expect("empty VecDeque after split");
                self.buffers
                    .push_back(front.subslice(0, rem).map_err(Error::VolatileMemoryError)?);
                other.push_front(front.offset(rem).map_err(Error::VolatileMemoryError)?);
            }

            Ok(IoBuffers {
                buffers: other,
                bytes_consumed: 0,
            })
        } else if rem == 0 {
            Ok(IoBuffers {
                buffers: VecDeque::new(),
                bytes_consumed: 0,
            })
        } else {
            Err(Error::SplitOutOfBounds(offset))
        }
    }
}

/// Reader to access FUSE requests from the transport layer data buffers.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Reader will skip iterating over descriptor chain when first writable
/// descriptor is encountered.
#[derive(Clone)]
pub struct Reader<'a, S = ()> {
    pub(crate) buffers: IoBuffers<'a, S>,
}

impl<S: BitmapSlice> Default for Reader<'_, S> {
    fn default() -> Self {
        Reader {
            buffers: IoBuffers::default(),
        }
    }
}

impl<'a, S: BitmapSlice + Default> Reader<'a, S> {
    /// Construct a new Reader over a mutable byte slice.
    ///
    /// The slice's memory is accessed through a `VolatileSlice` carrying
    /// the default bitmap of `S`, so reads never rely on the slice being
    /// initialized. This is the construction path for transports that
    /// receive requests into plain byte buffers (e.g. `/dev/fuse` reads).
    pub fn from_slice(buf: &'a mut [u8]) -> Self {
        // Safe because Reader has the same lifetime as buf.
        let slice =
            unsafe { VolatileSlice::with_bitmap(buf.as_mut_ptr(), buf.len(), S::default(), None) };
        Reader::from_volatile_slices(vec![slice])
    }
}

impl<'a, S: BitmapSlice> Reader<'a, S> {
    /// Construct a new Reader over a list of volatile slices.
    ///
    /// This is the transport-neutral construction path: transports that
    /// gather request buffers from their own memory sources (e.g. virtio
    /// descriptor chains) build the slice list and hand it over.
    pub fn from_volatile_slices(slices: Vec<VolatileSlice<'a, S>>) -> Self {
        Reader {
            buffers: IoBuffers::new(slices),
        }
    }

    /// Reads an object from the descriptor chain buffer.
    pub fn read_obj<T: ByteValued>(&mut self) -> io::Result<T> {
        let mut obj = MaybeUninit::<T>::uninit();

        // Safe because `MaybeUninit` guarantees that the pointer is valid for
        // `size_of::<T>()` bytes.
        let buf = unsafe {
            ::std::slice::from_raw_parts_mut(obj.as_mut_ptr() as *mut u8, size_of::<T>())
        };

        self.read_exact(buf)?;

        // Safe because any type that implements `ByteValued` can be considered initialized
        // even if it is filled with random data.
        Ok(unsafe { obj.assume_init() })
    }

    /// Reads data from the descriptor chain buffer into a file descriptor.
    /// Returns the number of bytes read from the descriptor chain buffer.
    /// The number of bytes read can be less than `count` if there isn't
    /// enough data in the descriptor chain buffer.
    pub fn read_to<F: FileReadWriteVolatile>(
        &mut self,
        mut dst: F,
        count: usize,
    ) -> io::Result<usize> {
        self.buffers
            .consume_for_read(count, |bufs| dst.write_vectored_volatile(bufs))
    }

    /// Reads data from the descriptor chain buffer into a File at offset `off`.
    /// Returns the number of bytes read from the descriptor chain buffer.
    /// The number of bytes read can be less than `count` if there isn't
    /// enough data in the descriptor chain buffer.
    pub fn read_to_at<F: FileReadWriteVolatile>(
        &mut self,
        mut dst: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.buffers
            .consume_for_read(count, |bufs| dst.write_vectored_at_volatile(bufs, off))
    }

    /// Reads exactly size of data from the descriptor chain buffer into a file descriptor.
    pub fn read_exact_to<F: FileReadWriteVolatile>(
        &mut self,
        mut dst: F,
        mut count: usize,
    ) -> io::Result<()> {
        while count > 0 {
            match self.read_to(&mut dst, count) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::UnexpectedEof,
                        "failed to fill whole buffer",
                    ))
                }
                Ok(n) => count -= n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        Ok(())
    }

    /// Returns number of bytes available for reading.
    ///
    /// May return an error if the combined lengths of all the buffers in the DescriptorChain
    /// would cause an integer overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffers.available_bytes()
    }

    /// Returns number of bytes already read from the descriptor chain buffer.
    pub fn bytes_read(&self) -> usize {
        self.buffers.bytes_consumed()
    }

    /// Splits this `Reader` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to read up to `offset` bytes while the returned
    /// `Reader` can read up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Self> {
        self.buffers
            .split_at(offset)
            .map(|buffers| Reader { buffers })
    }
}

impl<S: BitmapSlice> io::Read for Reader<'_, S> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        self.buffers.consume_for_read(buf.len(), |bufs| {
            let mut rem = buf;
            let mut total = 0;
            for buf in bufs {
                let copy_len = cmp::min(rem.len(), buf.len());

                // Safe because we have already verified that `buf` points to valid memory.
                unsafe {
                    copy_nonoverlapping(buf.as_ptr() as *const u8, rem.as_mut_ptr(), copy_len);
                }
                rem = &mut rem[copy_len..];
                total += copy_len;
            }
            Ok(total)
        })
    }
}

/// Trait for sending FUSE reply messages back to the client, implemented by
/// each transport's concrete writer type.
///
/// This replaces the former `Writer` enum so that the transport-neutral `api`
/// layer is generic over the transport instead of depending on a closed set of
/// transports. It is re-exported from `transport`, so the historical
/// `transport::Writer` import path keeps resolving.
#[cfg_attr(feature = "async-io", async_trait::async_trait(?Send))]
pub trait Writer: io::Write + Sized {
    /// Write data to the reply buffer from a File at offset `off`.
    ///
    /// Return the number of bytes written to the reply buffer.
    fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize>;

    /// Split this `Writer` into two at the given offset in the reply buffer.
    ///
    /// After the split, `self` will be able to write up to `offset` bytes while the returned
    /// `Writer` can write up to `available_bytes() - offset` bytes. Return an error if
    /// `offset > self.available_bytes()`.
    fn split_at(&mut self, offset: usize) -> Result<Self>;

    /// Return number of bytes available for writing.
    fn available_bytes(&self) -> usize;

    /// Return number of bytes already written to the reply buffer.
    fn bytes_written(&self) -> usize;

    /// Commit all internal buffers of self and others.
    fn commit(&mut self, other: Option<&Self>) -> io::Result<usize>;

    /// Write an object to the reply buffer.
    fn write_obj<T: ByteValued>(&mut self, val: T) -> io::Result<()> {
        self.write_all(val.as_slice())
    }

    /// Write data from a buffer into this writer in asynchronous mode.
    ///
    /// Transports without asynchronous IO support may rely on the default
    /// implementation, which fails with `EINVAL`.
    #[cfg(feature = "async-io")]
    async fn async_write(&mut self, _data: &[u8]) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    /// Write data from two buffers into this writer in asynchronous mode.
    ///
    /// Transports without asynchronous IO support may rely on the default
    /// implementation, which fails with `EINVAL`.
    #[cfg(feature = "async-io")]
    async fn async_write2(&mut self, _data: &[u8], _data2: &[u8]) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    /// Write data from three buffers into this writer in asynchronous mode.
    ///
    /// Transports without asynchronous IO support may rely on the default
    /// implementation, which fails with `EINVAL`.
    #[cfg(feature = "async-io")]
    async fn async_write3(
        &mut self,
        _data: &[u8],
        _data2: &[u8],
        _data3: &[u8],
    ) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    /// Attempt to write an entire buffer into this writer in asynchronous mode.
    ///
    /// Transports without asynchronous IO support may rely on the default
    /// implementation, which fails with `EINVAL`.
    #[cfg(feature = "async-io")]
    async fn async_write_all(&mut self, _buf: &[u8]) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    /// Asynchronously write data to the reply buffer from a File at offset `off`.
    ///
    /// Return the number of bytes written to the reply buffer. Transports
    /// without asynchronous IO support may rely on the default implementation,
    /// which fails with `EINVAL`.
    #[cfg(feature = "async-io")]
    async fn async_write_from_at<F: AsyncFileReadWriteVolatile>(
        &mut self,
        _src: &F,
        _count: usize,
        _off: u64,
    ) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    /// Commit all internal buffers of self and others in asynchronous mode.
    ///
    /// Transports without asynchronous IO support may rely on the default
    /// implementation, which fails with `EINVAL`.
    #[cfg(feature = "async-io")]
    async fn async_commit(&mut self, _other: Option<&Self>) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }
}

#[cfg(feature = "async-io")]
mod async_io {
    use super::*;

    impl<'a, S: BitmapSlice> Reader<'a, S> {
        /// Read data from the data buffer into a File at offset `off` in asynchronous mode.
        ///
        /// Return the number of bytes read from the data buffer. The number of bytes read can
        /// be less than `count` if there isn't enough data in the buffer.
        pub async fn async_read_to_at<F: AsyncFileReadWriteVolatile>(
            &mut self,
            dst: &F,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            // Safe because `bufs` doesn't out-live `self`.
            let bufs = unsafe { self.buffers.prepare_io_buf(count) };
            if bufs.is_empty() {
                Ok(0)
            } else {
                let (res, _) = dst.async_write_vectored_at_volatile(bufs, off).await;
                match res {
                    Ok(cnt) => {
                        self.buffers.mark_used(cnt)?;
                        Ok(cnt)
                    }
                    Err(e) => Err(e),
                }
            }
        }
    }
}

static PAGESIZE: LazyLock<usize> = LazyLock::new(|| unsafe { sysconf(_SC_PAGESIZE) as usize });

/// Safe wrapper for `sysconf(_SC_PAGESIZE)`.
#[inline(always)]
pub fn pagesize() -> usize {
    *PAGESIZE
}

#[cfg(test)]
mod tests {
    use super::IoBuffers;
    use std::collections::VecDeque;
    use vm_memory::{
        bitmap::{AtomicBitmap, Bitmap},
        VolatileSlice,
    };

    #[test]
    fn test_io_buffers() {
        let mut buf1 = vec![0x0u8; 16];
        let mut buf2 = vec![0x0u8; 16];
        let mut bufs = VecDeque::new();
        unsafe {
            bufs.push_back(VolatileSlice::new(buf1.as_mut_ptr(), buf1.len()));
            bufs.push_back(VolatileSlice::new(buf2.as_mut_ptr(), buf2.len()));
        }
        let mut buffers = IoBuffers {
            buffers: bufs,
            bytes_consumed: 0,
        };

        assert_eq!(buffers.available_bytes(), 32);
        assert_eq!(buffers.bytes_consumed(), 0);

        assert_eq!(
            buffers.consume_for_read(2, |buf| Ok(buf[0].len())).unwrap(),
            2
        );
        assert_eq!(buffers.available_bytes(), 30);
        assert_eq!(buffers.bytes_consumed(), 2);

        let mut buffers2 = buffers.split_at(10).unwrap();
        assert_eq!(buffers.available_bytes(), 10);
        assert_eq!(buffers.bytes_consumed(), 2);
        assert_eq!(buffers2.available_bytes(), 20);
        assert_eq!(buffers2.bytes_consumed(), 0);

        assert_eq!(
            buffers2
                .consume_for_read(10, |buf| Ok(buf[0].len() + buf[1].len()))
                .unwrap(),
            10
        );
        assert_eq!(
            buffers2
                .consume_for_read(20, |buf| Ok(buf[0].len()))
                .unwrap(),
            10
        );

        let _buffers3 = buffers2.split_at(0).unwrap();
        assert!(buffers2.split_at(1).is_err());
    }

    #[test]
    fn test_mark_dirty() {
        let mut buf1 = vec![0x0u8; 16];
        let bitmap1 = AtomicBitmap::new(16, std::num::NonZero::new(2).unwrap());

        assert_eq!(bitmap1.len(), 8);
        for i in 0..8 {
            assert_eq!(bitmap1.is_bit_set(i), false);
        }

        let mut buf2 = vec![0x0u8; 16];
        let bitmap2 = AtomicBitmap::new(16, std::num::NonZero::new(2).unwrap());
        let mut bufs = VecDeque::new();

        unsafe {
            bufs.push_back(VolatileSlice::with_bitmap(
                buf1.as_mut_ptr(),
                buf1.len(),
                bitmap1.slice_at(0),
                None,
            ));
            bufs.push_back(VolatileSlice::with_bitmap(
                buf2.as_mut_ptr(),
                buf2.len(),
                bitmap2.slice_at(0),
                None,
            ));
        }
        let mut buffers = IoBuffers {
            buffers: bufs,
            bytes_consumed: 0,
        };

        assert_eq!(buffers.available_bytes(), 32);
        assert_eq!(buffers.bytes_consumed(), 0);

        assert_eq!(
            buffers.consume_for_read(8, |buf| Ok(buf[0].len())).unwrap(),
            8
        );

        assert_eq!(buffers.available_bytes(), 24);
        assert_eq!(buffers.bytes_consumed(), 8);

        for i in 0..8 {
            assert_eq!(bitmap1.is_bit_set(i), false);
        }

        assert_eq!(
            buffers
                .consume(true, 16, |buf| Ok(buf[0].len() + buf[1].len()))
                .unwrap(),
            16
        );
        assert_eq!(buffers.available_bytes(), 8);
        assert_eq!(buffers.bytes_consumed(), 24);
        for i in 0..8 {
            if i >= 4 {
                assert_eq!(bitmap1.is_bit_set(i), true);
                continue;
            } else {
                assert_eq!(bitmap1.is_bit_set(i), false);
            }
        }
        for i in 0..8 {
            if i < 4 {
                assert_eq!(bitmap2.is_bit_set(i), true);
            } else {
                assert_eq!(bitmap2.is_bit_set(i), false);
            }
        }
    }
}
