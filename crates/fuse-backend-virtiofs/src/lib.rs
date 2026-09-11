// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and Structs to implement the virtiofs transport driver.
//!
//! Virtio-fs is a shared file system that lets virtual machines access a directory tree
//! on the host. Unlike existing approaches, it is designed to offer local file system
//! semantics and performance. Virtualization allows multiple virtual machines (VMs) to
//! run on a single physical host. Although VMs are isolated and run separate operating
//! system instances, their proximity on the physical host allows for fast shared memory
//! access.
//!
//! Virtio-fs uses FUSE as the foundation. FUSE has no dependencies on a networking stack
//! and exposes a rich native Linux file system interface that allows virtio-fs to act
//! like a local file system. Both the semantics and the performance of communication of
//! co-located VMs are different from the networking model for which remote file systems
//! were designed.
//!
//! Unlike traditional FUSE where the file system daemon runs in userspace, the virtio-fs
//! daemon runs on the host. A VIRTIO device carries FUSE messages and provides extensions
//! for advanced features not available in traditional FUSE.
//! The main extension to the FUSE protocol is the virtio-fs DAX Window, which supports
//! memory mapping the contents of files. The virtio-fs VIRTIO device implements this
//! as a shared memory region exposed through a PCI/MMIO BAR. This feature is
//! virtualization-specific and is not available outside of virtio-fs.
//!
//! Although virtio-fs uses FUSE as the protocol, it does not function as a new transport
//! for existing FUSE applications. It is not possible to run existing FUSE file systems
//! unmodified because virtio-fs has a different security model and extends the FUSE protocol.
//! Existing FUSE file systems trust the client because it is the kernel. There would be no
//! reason for the kernel to attack the file system since the kernel already has full control
//! of the host. In virtio-fs the client is the untrusted VM and the file system daemon must
//! not trust it. Therefore, virtio-fs server uses a hardened FUSE implementation that does
//! not trust the client.

use std::cmp;
use std::collections::VecDeque;
use std::io::{self, IoSlice, Write};
use std::ops::Deref;
use std::ptr::copy_nonoverlapping;

use virtio_queue::DescriptorChain;
use vm_memory::bitmap::{BitmapSlice, MS};
use vm_memory::{Address, ByteValued, GuestMemory, GuestMemoryRegion, MemoryRegionAddress};

use fuse_backend_core::buffer::{Error, IoBuffers, Reader, Result, Writer};
#[cfg(feature = "async-io")]
use fuse_backend_core::file_traits::AsyncFileReadWriteVolatile;
use fuse_backend_core::file_traits::FileReadWriteVolatile;

/// Extension trait for constructing core `Reader`s from virtio descriptor
/// chains.
///
/// Defined as a trait (rather than an inherent impl on [`Reader`]) because
/// `Reader` is defined by the transport-neutral buffer layer, and inherent
/// impls are only allowed in the defining crate.
pub trait VirtioFsReaderExt<'a> {
    /// Construct a new Reader wrapper over `desc_chain`.
    fn from_descriptor_chain<M>(
        mem: &'a M::Target,
        desc_chain: DescriptorChain<M>,
    ) -> Result<Reader<'a, MS<'a, M::Target>>>
    where
        M: Deref,
        M::Target: GuestMemory + Sized;
}

impl<'a> VirtioFsReaderExt<'a> for Reader<'a> {
    fn from_descriptor_chain<M>(
        mem: &'a M::Target,
        desc_chain: DescriptorChain<M>,
    ) -> Result<Reader<'a, MS<'a, M::Target>>>
    where
        M: Deref,
        M::Target: GuestMemory + Sized,
    {
        let mut total_len: usize = 0;
        // Allocate VecDeque with 64 capacity and hope it could hold all slices to avoid expending
        // VecDeque repeatedly.
        let mut buffers = VecDeque::with_capacity(64);
        for desc in desc_chain.readable() {
            // Verify that summing the descriptor sizes does not overflow.
            // This can happen if a driver tricks a device into reading more data than
            // fits in a `usize`.
            total_len = total_len
                .checked_add(desc.len() as usize)
                .ok_or(Error::DescriptorChainOverflow)?;

            let region = mem
                .find_region(desc.addr())
                .ok_or(Error::FindMemoryRegion)?;
            let offset = desc
                .addr()
                .checked_sub(region.start_addr().raw_value())
                .unwrap();

            buffers.push_back(
                region
                    .get_slice(MemoryRegionAddress(offset.raw_value()), desc.len() as usize)
                    .map_err(Error::GuestMemoryError)?,
            );
        }

        Ok(Reader::from_volatile_slices(buffers.into()))
    }
}

/// Provide high-level interface over the sequence of memory regions
/// defined by writable descriptors in the Virtio descriptor chain.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Writer will start iterating the descriptors from the first writable one and will
/// assume that all following descriptors are writable.
#[derive(Clone)]
pub struct VirtioFsWriter<'a, S = ()> {
    buffers: IoBuffers<'a, S>,
}

impl<'a> VirtioFsWriter<'a> {
    /// Construct a new [Writer] wrapper over `desc_chain`.
    pub fn new<M>(
        mem: &'a M::Target,
        desc_chain: DescriptorChain<M>,
    ) -> Result<VirtioFsWriter<'a, MS<'a, M::Target>>>
    where
        M: Deref,
        M::Target: GuestMemory + Sized,
    {
        let mut total_len: usize = 0;
        // Allocate VecDeque with 64 capacity and hope it could hold all slices to avoid expending
        // VecDeque repeatedly.
        let mut buffers = VecDeque::with_capacity(64);
        for desc in desc_chain.writable() {
            // Verify that summing the descriptor sizes does not overflow.
            // This can happen if a driver tricks a device into writing more data than
            // fits in a `usize`.
            total_len = total_len
                .checked_add(desc.len() as usize)
                .ok_or(Error::DescriptorChainOverflow)?;

            let region = mem
                .find_region(desc.addr())
                .ok_or(Error::FindMemoryRegion)?;
            let offset = desc
                .addr()
                .checked_sub(region.start_addr().raw_value())
                .unwrap();

            buffers.push_back(
                region
                    .get_slice(MemoryRegionAddress(offset.raw_value()), desc.len() as usize)
                    .map_err(Error::GuestMemoryError)?,
            )
        }

        Ok(VirtioFsWriter {
            buffers: IoBuffers::new(buffers.into()),
        })
    }
}

impl<'a, S: BitmapSlice> VirtioFsWriter<'a, S> {
    /// Write an object to the descriptor chain buffer.
    pub fn write_obj<T: ByteValued>(&mut self, val: T) -> io::Result<()> {
        self.write_all(val.as_slice())
    }

    /// Write data to the descriptor chain buffer from a file descriptor.
    ///
    /// Return the number of bytes written to the descriptor chain buffer.
    pub fn write_from<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
    ) -> io::Result<usize> {
        self.check_available_space(count, 0, 0)?;
        self.buffers
            .consume_for_write(count, |bufs| src.read_vectored_volatile(bufs))
    }

    /// Write data to the descriptor chain buffer from a File at offset `off`.
    ///
    /// Return the number of bytes written to the descriptor chain buffer.
    pub fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.check_available_space(count, 0, 0)?;
        self.buffers
            .consume_for_write(count, |bufs| src.read_vectored_at_volatile(bufs, off))
    }

    /// Write all data to the descriptor chain buffer from a file descriptor.
    pub fn write_all_from<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        mut count: usize,
    ) -> io::Result<()> {
        self.check_available_space(count, 0, 0)?;
        while count > 0 {
            match self.write_from(&mut src, count) {
                Ok(0) => {
                    return Err(io::Error::new(
                        io::ErrorKind::WriteZero,
                        "failed to write whole buffer",
                    ))
                }
                Ok(n) => count -= n,
                Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }

        Ok(())
    }

    /// Return number of bytes available for writing.
    ///
    /// May return an error if the combined lengths of all the buffers in the DescriptorChain would
    /// cause an overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffers.available_bytes()
    }

    /// Return number of bytes already written to the descriptor chain buffer.
    pub fn bytes_written(&self) -> usize {
        self.buffers.bytes_consumed()
    }

    /// Split this `Writer` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to write up to `offset` bytes while the returned
    /// `Writer` can write up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Self> {
        self.buffers
            .split_at(offset)
            .map(|buffers| VirtioFsWriter { buffers })
    }

    /// Commit all internal buffers of self and others
    ///
    /// This is provided just to be compatible with fusedev
    pub fn commit(&mut self, _other: Option<&VirtioFsWriter<'a, S>>) -> io::Result<usize> {
        Ok(0)
    }

    fn check_available_space(&self, len1: usize, len2: usize, len3: usize) -> io::Result<()> {
        let len = len1
            .checked_add(len2)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "buffer size is too big"))?;
        let len = len
            .checked_add(len3)
            .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "buffer size is too big"))?;
        if len > self.available_bytes() {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    self.available_bytes(),
                    len
                ),
            ))
        } else {
            Ok(())
        }
    }
}

impl<S: BitmapSlice> io::Write for VirtioFsWriter<'_, S> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.check_available_space(buf.len(), 0, 0)?;

        self.buffers.consume_for_write(buf.len(), |bufs| {
            let mut rem = buf;
            let mut total = 0;
            for buf in bufs {
                let copy_len = cmp::min(rem.len(), buf.len());

                // Safe because we have already verified that `buf` points to valid memory.
                unsafe {
                    copy_nonoverlapping(rem.as_ptr(), buf.as_ptr(), copy_len);
                }
                rem = &rem[copy_len..];
                total += copy_len;
            }
            Ok(total)
        })
    }

    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        self.check_available_space(bufs.iter().fold(0, |acc, x| acc + x.len()), 0, 0)?;

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

#[cfg_attr(feature = "async-io", async_trait::async_trait(?Send))]
impl<'a, S: BitmapSlice> Writer for VirtioFsWriter<'a, S> {
    // All methods forward to the inherent methods of the same name; the
    // explicit `VirtioFsWriter::` prefix keeps the forwarding unambiguous and
    // makes removing an inherent method a compile error instead of silent
    // infinite recursion.
    fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        VirtioFsWriter::write_from_at(self, src, count, off)
    }

    fn split_at(&mut self, offset: usize) -> Result<Self> {
        VirtioFsWriter::split_at(self, offset)
    }

    fn available_bytes(&self) -> usize {
        VirtioFsWriter::available_bytes(self)
    }

    fn bytes_written(&self) -> usize {
        VirtioFsWriter::bytes_written(self)
    }

    fn commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        VirtioFsWriter::commit(self, other)
    }

    #[cfg(feature = "async-io")]
    async fn async_write(&mut self, data: &[u8]) -> io::Result<usize> {
        VirtioFsWriter::async_write(self, data).await
    }

    #[cfg(feature = "async-io")]
    async fn async_write2(&mut self, data: &[u8], data2: &[u8]) -> io::Result<usize> {
        VirtioFsWriter::async_write2(self, data, data2).await
    }

    #[cfg(feature = "async-io")]
    async fn async_write3(&mut self, data: &[u8], data2: &[u8], data3: &[u8]) -> io::Result<usize> {
        VirtioFsWriter::async_write3(self, data, data2, data3).await
    }

    #[cfg(feature = "async-io")]
    async fn async_write_all(&mut self, buf: &[u8]) -> io::Result<()> {
        VirtioFsWriter::async_write_all(self, buf).await
    }

    #[cfg(feature = "async-io")]
    async fn async_write_from_at<F: AsyncFileReadWriteVolatile>(
        &mut self,
        src: &F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        VirtioFsWriter::async_write_from_at(self, src, count, off).await
    }

    #[cfg(feature = "async-io")]
    async fn async_commit(&mut self, other: Option<&Self>) -> io::Result<usize> {
        VirtioFsWriter::async_commit(self, other).await
    }
}

// For Virtio-fs, the output is written to memory buffer, so no need for async io at all.
// Just relay the operation to corresponding sync io handler.
#[cfg(feature = "async-io")]
mod async_io {
    use super::*;
    use fuse_backend_core::file_traits::AsyncFileReadWriteVolatile;

    impl<'a, S: BitmapSlice> VirtioFsWriter<'a, S> {
        /// Write data from a buffer into this writer in asynchronous mode.
        pub async fn async_write(&mut self, data: &[u8]) -> io::Result<usize> {
            self.write(data)
        }

        /// Write data from two buffers into this writer in asynchronous mode.
        pub async fn async_write2(&mut self, data: &[u8], data2: &[u8]) -> io::Result<usize> {
            self.check_available_space(data.len(), data2.len(), 0)?;
            let mut cnt = self.write(data)?;
            cnt += self.write(data2)?;

            Ok(cnt)
        }

        /// Write data from three buffers into this writer in asynchronous mode.
        pub async fn async_write3(
            &mut self,
            data: &[u8],
            data2: &[u8],
            data3: &[u8],
        ) -> io::Result<usize> {
            self.check_available_space(data.len(), data2.len(), data3.len())?;
            let mut cnt = self.write(data)?;
            cnt += self.write(data2)?;
            cnt += self.write(data3)?;

            Ok(cnt)
        }

        /// Attempts to write an entire buffer into this writer in asynchronous mode.
        pub async fn async_write_all(&mut self, buf: &[u8]) -> io::Result<()> {
            self.write_all(buf)
        }

        /// Writes data to the descriptor chain buffer from a File at offset `off`.
        /// Returns the number of bytes written to the descriptor chain buffer.
        pub async fn async_write_from_at<F: AsyncFileReadWriteVolatile>(
            &mut self,
            src: &F,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            self.check_available_space(count, 0, 0)?;
            // Safe because `bufs` doesn't out-live `self`.
            let bufs = unsafe { self.buffers.prepare_mut_io_buf(count) };
            if bufs.is_empty() {
                Ok(0)
            } else {
                let (res, _) = src.async_read_vectored_at_volatile(bufs, off).await;
                match res {
                    Ok(cnt) => {
                        self.buffers.mark_dirty(cnt);
                        self.buffers.mark_used(cnt)?;
                        Ok(cnt)
                    }
                    Err(e) => Err(e),
                }
            }
        }

        /// Commit all internal buffers of self and others
        /// We need this because the lifetime of others is usually shorter than self.
        pub async fn async_commit(
            &mut self,
            other: Option<&VirtioFsWriter<'a, S>>,
        ) -> io::Result<usize> {
            self.commit(other)
        }
    }
}
