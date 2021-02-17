// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! Traits and Structs to implement the virtio-fs Fuse transport layer.
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
use std::fmt;
use std::io::{self, IoSlice, Write};
#[cfg(feature = "async-io")]
use std::os::unix::io::RawFd;
use std::ptr::copy_nonoverlapping;

use vm_memory::{ByteValued, GuestMemory, GuestMemoryError, VolatileMemoryError, VolatileSlice};
use vm_virtio::{DescriptorChain, Error as QueueError};

use super::{FileReadWriteVolatile, IoBuffers, Reader};

mod fs_cache_req_handler;
pub use self::fs_cache_req_handler::FsCacheReqHandler;

#[cfg(feature = "async-io")]
use crate::async_util::{AsyncDrive, AsyncUtil};

/// Error codes for Virtio queue related operations.
#[derive(Debug)]
pub enum Error {
    /// Virtio queue descriptor chain overflows.
    DescriptorChainOverflow,
    /// Failed to find memory region for guest physical address.
    FindMemoryRegion,
    /// Failed to access guest memory.
    GuestMemoryError(GuestMemoryError),
    /// Invalid virtio queue descriptor chain.
    InvalidChain,
    /// Invalid Indirect Virtio descriptors.
    ConvertIndirectDescriptor(QueueError),
    /// Generic IO error.
    IoError(io::Error),
    /// Out of bounds when splitting VolatileSplice.
    SplitOutOfBounds(usize),
    /// Failed to access volatile memory.
    VolatileMemoryError(VolatileMemoryError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Error::*;

        match self {
            ConvertIndirectDescriptor(e) => write!(f, "invalid indirect descriptor: {}", e),
            DescriptorChainOverflow => write!(
                f,
                "the combined length of all the buffers in a `DescriptorChain` would overflow"
            ),
            FindMemoryRegion => write!(f, "no memory region for this address range"),
            GuestMemoryError(e) => write!(f, "descriptor guest memory error: {}", e),
            InvalidChain => write!(f, "invalid descriptor chain"),
            IoError(e) => write!(f, "descriptor I/O error: {}", e),
            SplitOutOfBounds(off) => write!(f, "`DescriptorChain` split is out of bounds: {}", off),
            VolatileMemoryError(e) => write!(f, "volatile memory error: {}", e),
        }
    }
}

/// Result for Virtio queue related operations.
pub type Result<T> = std::result::Result<T, Error>;

impl std::error::Error for Error {}

impl<'a> Reader<'a> {
    /// Construct a new Reader wrapper over `desc_chain`.
    pub fn new<M: GuestMemory>(
        mem: &'a M,
        desc_chain: DescriptorChain<'a, M>,
    ) -> Result<Reader<'a>> {
        let mut total_len: usize = 0;
        let chain = if desc_chain.is_indirect() {
            desc_chain
                .new_from_indirect()
                .map_err(Error::ConvertIndirectDescriptor)?
        } else {
            desc_chain
        };
        let buffers = chain
            .readable()
            .map(|desc| {
                // Verify that summing the descriptor sizes does not overflow.
                // This can happen if a driver tricks a device into reading more data than
                // fits in a `usize`.
                total_len = total_len
                    .checked_add(desc.len() as usize)
                    .ok_or(Error::DescriptorChainOverflow)?;

                mem.get_slice(desc.addr(), desc.len() as usize)
                    .map_err(Error::GuestMemoryError)
            })
            .collect::<Result<VecDeque<VolatileSlice<'a>>>>()?;

        Ok(Reader {
            buffers: IoBuffers {
                buffers,
                bytes_consumed: 0,
            },
        })
    }
}

/// Provides high-level interface over the sequence of memory regions
/// defined by writable descriptors in the descriptor chain.
///
/// Note that virtio spec requires driver to place any device-writable
/// descriptors after any device-readable descriptors (2.6.4.2 in Virtio Spec v1.1).
/// Writer will start iterating the descriptors from the first writable one and will
/// assume that all following descriptors are writable.
#[derive(Clone)]
pub struct Writer<'a> {
    buffers: IoBuffers<'a>,
}

impl<'a> Writer<'a> {
    /// Construct a new Writer wrapper over `desc_chain`.
    pub fn new<M: GuestMemory>(
        mem: &'a M,
        desc_chain: DescriptorChain<'a, M>,
    ) -> Result<Writer<'a>> {
        let mut total_len: usize = 0;
        let chain = if desc_chain.is_indirect() {
            desc_chain
                .new_from_indirect()
                .map_err(Error::ConvertIndirectDescriptor)?
        } else {
            desc_chain
        };
        let buffers = chain
            .writable()
            .map(|desc| {
                // Verify that summing the descriptor sizes does not overflow.
                // This can happen if a driver tricks a device into writing more data than
                // fits in a `usize`.
                total_len = total_len
                    .checked_add(desc.len() as usize)
                    .ok_or(Error::DescriptorChainOverflow)?;

                mem.get_slice(desc.addr(), desc.len() as usize)
                    .map_err(Error::GuestMemoryError)
            })
            .collect::<Result<VecDeque<VolatileSlice<'a>>>>()?;

        Ok(Writer {
            buffers: IoBuffers {
                buffers,
                bytes_consumed: 0,
            },
        })
    }

    /// Writes an object to the descriptor chain buffer.
    pub fn write_obj<T: ByteValued>(&mut self, val: T) -> io::Result<()> {
        self.write_all(val.as_slice())
    }

    /// Writes data to the descriptor chain buffer from a file descriptor.
    /// Returns the number of bytes written to the descriptor chain buffer.
    pub fn write_from<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
    ) -> io::Result<usize> {
        self.check_available_space(count)?;
        self.buffers
            .consume(count, |bufs| src.read_vectored_volatile(bufs))
    }

    /// Writes data to the descriptor chain buffer from a File at offset `off`.
    /// Returns the number of bytes written to the descriptor chain buffer.
    pub fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.check_available_space(count)?;
        self.buffers
            .consume(count, |bufs| src.read_vectored_at_volatile(bufs, off))
    }

    /// Writes all data to the descriptor chain buffer from a file descriptor.
    pub fn write_all_from<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        mut count: usize,
    ) -> io::Result<()> {
        self.check_available_space(count)?;
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

    /// Returns number of bytes available for writing.  May return an error if the combined
    /// lengths of all the buffers in the DescriptorChain would cause an overflow.
    pub fn available_bytes(&self) -> usize {
        self.buffers.available_bytes()
    }

    /// Returns number of bytes already written to the descriptor chain buffer.
    pub fn bytes_written(&self) -> usize {
        self.buffers.bytes_consumed()
    }

    /// Splits this `Writer` into two at the given offset in the `DescriptorChain` buffer.
    /// After the split, `self` will be able to write up to `offset` bytes while the returned
    /// `Writer` can write up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Writer<'a>> {
        self.buffers
            .split_at(offset)
            .map(|buffers| Writer { buffers })
    }

    /// Commit all internal buffers of self and others
    /// This is provided just to be compatible with fusedev
    pub fn commit(&mut self, _other: Option<&Writer<'a>>) -> io::Result<usize> {
        Ok(0)
    }

    fn check_available_space(&self, sz: usize) -> io::Result<()> {
        if sz > self.available_bytes() {
            Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    self.available_bytes(),
                    sz
                ),
            ))
        } else {
            Ok(())
        }
    }
}

impl<'a> io::Write for Writer<'a> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.check_available_space(buf.len())?;

        self.buffers.consume(buf.len(), |bufs| {
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
        self.check_available_space(bufs.iter().fold(0, |acc, x| acc + x.len()))?;

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

// For virtio-fs, the output is written to memory buffer, so need for async io.
// Just relay the operation to corresponding sync io handler.
#[cfg(feature = "async-io")]
mod async_io {
    use super::*;

    impl<'a> Reader<'a> {
        /// Reads data from the descriptor chain buffer into a File at offset `off`.
        /// Returns the number of bytes read from the descriptor chain buffer.
        /// The number of bytes read can be less than `count` if there isn't
        /// enough data in the descriptor chain buffer.
        pub async fn async_read_to_at<D: AsyncDrive>(
            &mut self,
            drive: D,
            dst: RawFd,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            let bufs = self.buffers.allocate_io_slice(count);
            if bufs.is_empty() {
                Ok(0)
            } else {
                let result = AsyncUtil::write_vectored(drive, dst, &bufs, off).await?;
                self.buffers.mark_used(result)?;
                Ok(result)
            }
        }
    }

    impl<'a> Writer<'a> {
        /// Write data from a buffer into this writer in asynchronous mode.
        pub async fn async_write<D: AsyncDrive>(
            &mut self,
            _drive: D,
            data: &[u8],
        ) -> io::Result<usize> {
            self.write(data)
        }

        /// Write data from two buffers into this writer in asynchronous mode.
        pub async fn async_write2<D: AsyncDrive>(
            &mut self,
            _drive: D,
            data: &[u8],
            data2: &[u8],
        ) -> io::Result<usize> {
            let len = data.len() + data2.len();
            self.check_available_space(len)?;

            let mut cnt = self.write(data)?;
            cnt += self.write(data2)?;

            Ok(cnt)
        }

        /// Write data from two buffers into this writer in asynchronous mode.
        pub async fn async_write3<D: AsyncDrive>(
            &mut self,
            _drive: D,
            data: &[u8],
            data2: &[u8],
            data3: &[u8],
        ) -> io::Result<usize> {
            let len = data.len() + data2.len() + data3.len();
            self.check_available_space(len)?;

            let mut cnt = self.write(data)?;
            cnt += self.write(data2)?;
            cnt += self.write(data3)?;

            Ok(cnt)
        }

        /*
        /// Write data from a group of buffers into this writer in asynchronous mode, skipping empty
        /// buffers.
        pub async fn async_write_vectored<D: AsyncDrive>(
            &mut self,
            _drive: D,
            bufs: &[IoSlice<'_>],
        ) -> io::Result<usize> {
            self.write_vectored(bufs)
        }
         */

        /// Attempts to write an entire buffer into this writer in asynchronous mode.
        pub async fn async_write_all<D: AsyncDrive>(
            &mut self,
            _drive: D,
            buf: &[u8],
        ) -> io::Result<()> {
            self.write_all(buf)
        }

        /// Writes data to the descriptor chain buffer from a File at offset `off`.
        /// Returns the number of bytes written to the descriptor chain buffer.
        pub async fn async_write_from_at<D: AsyncDrive>(
            &mut self,
            drive: D,
            src: RawFd,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            self.check_available_space(count)?;
            let mut bufs = self.buffers.allocate_mut_io_slice(count);
            if bufs.is_empty() {
                Ok(0)
            } else {
                let result = AsyncUtil::read_vectored(drive, src, &mut bufs, off).await?;
                self.buffers.mark_used(count)?;
                Ok(result)
            }
        }

        /// Commit all internal buffers of self and others
        /// We need this because the lifetime of others is usually shorter than self.
        pub async fn async_commit<D: AsyncDrive>(
            &mut self,
            _drive: D,
            other: Option<&Writer<'a>>,
        ) -> io::Result<usize> {
            self.commit(other)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Seek, SeekFrom, Write};
    use vm_memory::{Address, ByteValued, Bytes, GuestAddress, GuestMemoryMmap, Le16, Le32, Le64};
    use vmm_sys_util::tempfile::TempFile;

    const VIRTQ_DESC_F_NEXT: u16 = 0x1;
    const VIRTQ_DESC_F_WRITE: u16 = 0x2;

    #[derive(Copy, Clone, PartialEq, Eq)]
    pub enum DescriptorType {
        Readable,
        Writable,
    }

    #[derive(Copy, Clone, Debug, Default)]
    #[repr(C)]
    struct virtq_desc {
        addr: Le64,
        len: Le32,
        flags: Le16,
        next: Le16,
    }

    // Safe because it only has data and has no implicit padding.
    unsafe impl ByteValued for virtq_desc {}

    /// Test utility function to create a descriptor chain in guest memory.
    pub fn create_descriptor_chain(
        memory: &GuestMemoryMmap,
        descriptor_array_addr: GuestAddress,
        mut buffers_start_addr: GuestAddress,
        descriptors: Vec<(DescriptorType, u32)>,
        spaces_between_regions: u32,
    ) -> Result<DescriptorChain<GuestMemoryMmap>> {
        let descriptors_len = descriptors.len();
        for (index, (type_, size)) in descriptors.into_iter().enumerate() {
            let mut flags = 0;
            if let DescriptorType::Writable = type_ {
                flags |= VIRTQ_DESC_F_WRITE;
            }
            if index + 1 < descriptors_len {
                flags |= VIRTQ_DESC_F_NEXT;
            }

            let index = index as u16;
            let desc = virtq_desc {
                addr: buffers_start_addr.raw_value().into(),
                len: size.into(),
                flags: flags.into(),
                next: (index + 1).into(),
            };

            let offset = size + spaces_between_regions;
            buffers_start_addr = buffers_start_addr
                .checked_add(u64::from(offset))
                .ok_or(Error::InvalidChain)?;

            let _ = memory.write_obj(
                desc,
                descriptor_array_addr
                    .checked_add(u64::from(index) * std::mem::size_of::<virtq_desc>() as u64)
                    .ok_or(Error::InvalidChain)?,
            );
        }

        DescriptorChain::checked_new(memory, descriptor_array_addr, 0x100, 0)
            .ok_or(Error::InvalidChain)
    }

    #[test]
    fn reader_test_simple_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 8),
                (Readable, 16),
                (Readable, 18),
                (Readable, 64),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");
        assert_eq!(reader.available_bytes(), 106);
        assert_eq!(reader.bytes_read(), 0);

        let mut buffer = [0 as u8; 64];
        if let Err(_) = reader.read_exact(&mut buffer) {
            panic!("read_exact should not fail here");
        }

        assert_eq!(reader.available_bytes(), 42);
        assert_eq!(reader.bytes_read(), 64);

        match reader.read(&mut buffer) {
            Err(_) => panic!("read should not fail here"),
            Ok(length) => assert_eq!(length, 42),
        }

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 106);
    }

    #[test]
    fn writer_test_simple_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Writable, 8),
                (Writable, 16),
                (Writable, 18),
                (Writable, 64),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        assert_eq!(writer.available_bytes(), 106);
        assert_eq!(writer.bytes_written(), 0);

        let mut buffer = [0 as u8; 64];
        if let Err(_) = writer.write_all(&mut buffer) {
            panic!("write_all should not fail here");
        }

        assert_eq!(writer.available_bytes(), 42);
        assert_eq!(writer.bytes_written(), 64);

        let mut buffer = [0 as u8; 42];
        match writer.write(&mut buffer) {
            Err(_) => panic!("write should not fail here"),
            Ok(length) => assert_eq!(length, 42),
        }

        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 106);
    }

    #[test]
    fn reader_test_incompatible_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 8)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");
        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 0);

        assert!(reader.read_obj::<u8>().is_err());

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 0);
    }

    #[test]
    fn writer_test_incompatible_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 8)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 0);

        assert!(writer.write_obj(0u8).is_err());

        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 0);
    }

    #[test]
    fn reader_writer_shared_chain() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain.clone()).expect("failed to create Reader");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        assert_eq!(reader.bytes_read(), 0);
        assert_eq!(writer.bytes_written(), 0);

        let mut buffer = Vec::with_capacity(200);

        assert_eq!(
            reader
                .read_to_end(&mut buffer)
                .expect("read should not fail here"),
            128
        );

        // The writable descriptors are only 68 bytes long.
        writer
            .write_all(&buffer[..68])
            .expect("write should not fail here");

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 128);
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 68);
    }

    #[test]
    fn reader_writer_shattered_object() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let secret: Le32 = 0x12345678.into();

        // Create a descriptor chain with memory regions that are properly separated.
        let chain_writer = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 1), (Writable, 1), (Writable, 1), (Writable, 1)],
            123,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain_writer).expect("failed to create Writer");
        assert!(writer.flush().is_ok());
        if let Err(_) = writer.write_obj(secret) {
            panic!("write_obj should not fail here");
        }
        assert!(writer.flush().is_ok());

        // Now create new descriptor chain pointing to the same memory and try to read it.
        let chain_reader = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 1), (Readable, 1), (Readable, 1), (Readable, 1)],
            123,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain_reader).expect("failed to create Reader");
        match reader.read_obj::<Le32>() {
            Err(_) => panic!("read_obj should not fail here"),
            Ok(read_secret) => assert_eq!(read_secret, secret),
        }
    }

    #[test]
    fn reader_unexpected_eof() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 256), (Readable, 256)],
            0,
        )
        .expect("create_descriptor_chain failed");

        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let mut buf = Vec::with_capacity(1024);
        buf.resize(1024, 0);

        assert_eq!(
            reader
                .read_exact(&mut buf[..])
                .expect_err("read more bytes than available")
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
    }

    #[test]
    fn split_border() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let other = reader.split_at(32).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 32);
        assert_eq!(other.available_bytes(), 96);
    }

    #[test]
    fn split_middle() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let other = reader.split_at(24).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 24);
        assert_eq!(other.available_bytes(), 104);
    }

    #[test]
    fn split_end() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let other = reader.split_at(128).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 128);
        assert_eq!(other.available_bytes(), 0);
    }

    #[test]
    fn split_beginning() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let other = reader.split_at(0).expect("failed to split Reader");
        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(other.available_bytes(), 128);
    }

    #[test]
    fn split_outofbounds() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![
                (Readable, 16),
                (Readable, 16),
                (Readable, 96),
                (Writable, 64),
                (Writable, 1),
                (Writable, 3),
            ],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        if let Ok(_) = reader.split_at(256) {
            panic!("successfully split Reader with out of bounds offset");
        }
    }

    #[test]
    fn read_full() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 16), (Readable, 16), (Readable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Reader");

        let mut buf = vec![0u8; 64];
        assert_eq!(
            reader.read(&mut buf[..]).expect("failed to read to buffer"),
            48
        );
    }

    #[test]
    fn write_full() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 16), (Writable, 16), (Writable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        let buf = vec![0xdeu8; 40];
        assert_eq!(
            writer.write(&buf[..]).expect("failed to write from buffer"),
            40
        );
        assert_eq!(writer.available_bytes(), 8);
        assert_eq!(writer.bytes_written(), 40);

        // Write more data than capacity
        writer.write(&buf[..]).unwrap_err();
        assert_eq!(writer.available_bytes(), 8);
        assert_eq!(writer.bytes_written(), 40);
    }

    #[test]
    fn write_vectored() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 16), (Writable, 16), (Writable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        let buf = vec![0xdeu8; 48];
        let slices = [
            IoSlice::new(&buf[..32]),
            IoSlice::new(&buf[32..40]),
            IoSlice::new(&buf[40..]),
        ];
        assert_eq!(
            writer
                .write_vectored(&slices)
                .expect("failed to write from buffer"),
            48
        );
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 48);

        // Write more data than capacity
        let buf = vec![0xdeu8; 40];
        writer.write(&buf[..]).unwrap_err();
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 48);
    }

    #[test]
    fn read_exact_to() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 16), (Readable, 16), (Readable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Writer");

        let mut file = TempFile::new().unwrap().into_file();
        reader
            .read_exact_to(&mut file, 47)
            .expect("failed to read to file");

        assert_eq!(reader.available_bytes(), 1);
        assert_eq!(reader.bytes_read(), 47);
    }

    #[test]
    fn read_to_at() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Readable, 16), (Readable, 16), (Readable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut reader = Reader::new(&memory, chain).expect("failed to create Writer");

        let mut file = TempFile::new().unwrap().into_file();
        assert_eq!(
            reader
                .read_to_at(&mut file, 48, 16)
                .expect("failed to read to file"),
            48
        );

        assert_eq!(reader.available_bytes(), 0);
        assert_eq!(reader.bytes_read(), 48);
    }

    #[test]
    fn write_all_from() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 16), (Writable, 16), (Writable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];
        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        writer
            .write_all_from(&mut file, 47)
            .expect("failed to write from buffer");

        assert_eq!(writer.available_bytes(), 1);
        assert_eq!(writer.bytes_written(), 47);
    }

    #[test]
    fn write_from_at() {
        use DescriptorType::*;

        let memory_start_addr = GuestAddress(0x0);
        let memory = GuestMemoryMmap::from_ranges(&vec![(memory_start_addr, 0x10000)]).unwrap();

        let chain = create_descriptor_chain(
            &memory,
            GuestAddress(0x0),
            GuestAddress(0x100),
            vec![(Writable, 16), (Writable, 16), (Writable, 16)],
            0,
        )
        .expect("create_descriptor_chain failed");
        let mut writer = Writer::new(&memory, chain).expect("failed to create Writer");

        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];
        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        assert_eq!(
            writer
                .write_from_at(&mut file, 48, 16)
                .expect("failed to write from buffer"),
            48
        );

        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 48);
    }
}
