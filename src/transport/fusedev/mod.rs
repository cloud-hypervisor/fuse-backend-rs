// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Traits and Structs to implement the /dev/fuse transport layer.

use std::collections::VecDeque;
use std::fmt;
use std::io::{self, IoSlice, Write};
use std::marker::PhantomData;

use libc::c_int;
use nix::sys::uio::{pwrite, writev, IoVec};

use vm_memory::{VolatileMemory, VolatileMemoryError, VolatileSlice};

use super::{FileReadWriteVolatile, IoBuffers, Reader};

/// Error codes for Virtio queue related operations.
#[derive(Debug)]
pub enum Error {
    /// Virtio queue descriptor chain overflows.
    DescriptorChainOverflow,
    /// Failed to find memory region for guest physical address.
    FindMemoryRegion,
    /// Invalid virtio queue descriptor chain.
    InvalidChain,
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
            DescriptorChainOverflow => write!(
                f,
                "the combined length of all the buffers in a `DescriptorChain` would overflow"
            ),
            FindMemoryRegion => write!(f, "no memory region for this address range"),
            InvalidChain => write!(f, "invalid descriptor chain"),
            IoError(e) => write!(f, "descriptor I/O error: {}", e),
            SplitOutOfBounds(off) => write!(f, "`DescriptorChain` split is out of bounds: {}", off),
            VolatileMemoryError(e) => write!(f, "volatile memory error: {}", e),
        }
    }
}

/// Result for fusedev transport driver related operations.
pub type Result<T> = std::result::Result<T, Error>;

impl std::error::Error for Error {}

/// Fake trait to simplify implementation when vhost-user-fs is not used.
pub trait FsCacheReqHandler {}

/// A buffer reference wrapper for fuse requests.
#[derive(Debug)]
pub struct FuseBuf<'a> {
    mem: &'a mut [u8],
}

impl<'a> FuseBuf<'a> {
    /// Construct a new fuse request buffer wrapper.
    pub fn new(mem: &'a mut [u8]) -> FuseBuf<'a> {
        FuseBuf { mem }
    }
}

impl<'a> Reader<'a> {
    /// Construct a new Reader wrapper over `desc_chain`.
    ///
    /// 'request`: Fuse request from clients read from /dev/fuse
    pub fn new(buf: FuseBuf<'a>) -> Result<Reader<'a>> {
        let mut buffers: VecDeque<VolatileSlice<'a>> = VecDeque::new();
        // Safe because Reader has the same lifetime with buf.
        buffers.push_back(unsafe { VolatileSlice::new(buf.mem.as_mut_ptr(), buf.mem.len()) });

        Ok(Reader {
            buffers: IoBuffers {
                buffers,
                bytes_consumed: 0,
            },
        })
    }
}

/// A writer for fuse request. There are a few special properties to follow:
/// 1. A fuse device request MUST be written to the fuse device in one shot.
/// 2. If the writer is splitted, a final commit() MUST be called to issue the
///    device write operation.
/// 3. Concurrency, caller should not write to the writer concurrently.
#[derive(Debug, PartialEq, Eq)]
pub struct Writer<'a> {
    fd: c_int,
    max_size: usize,
    bytes_written: usize,
    // buf used to support splitted writer.
    // For split writers, we write to internal buffer upon write and construct
    // use writev write to fd upon flush.
    buf: Option<Vec<u8>>,
    // phantom used to keep lifetime so that we keep in sync with virtiofs
    phantom: PhantomData<&'a u8>,
}

impl<'a> Writer<'a> {
    /// Construct a new Writer
    pub fn new(fd: c_int, max_size: usize) -> Result<Writer<'a>> {
        Ok(Writer {
            fd,
            max_size,
            bytes_written: 0,
            buf: None,
            phantom: PhantomData,
        })
    }

    /// Splits this `Writer` into two at the given offset in the buffer.
    /// After the split, `self` will be able to write up to `offset` bytes while the returned
    /// `Writer` can write up to `available_bytes() - offset` bytes.  Returns an error if
    /// `offset > self.available_bytes()`.
    pub fn split_at(&mut self, offset: usize) -> Result<Writer<'a>> {
        if self.max_size < offset {
            return Err(Error::SplitOutOfBounds(offset));
        }
        // Need to set buf for self for the first split
        if self.buf.is_none() {
            self.buf = Some(Vec::new());
        }
        let max_size = self.max_size - offset;
        self.max_size = offset;
        Ok(Writer {
            fd: self.fd,
            max_size,
            bytes_written: 0,
            buf: Some(Vec::new()),
            phantom: PhantomData,
        })
    }

    /// Commit all internal buffers of self and others
    /// We need this because the lifetime of others is usually shorter than
    /// self.
    pub fn commit(&mut self, others: &[&Writer<'a>]) -> io::Result<usize> {
        if self.buf.is_none() {
            return Ok(0);
        }

        let mut buf: Vec<IoVec<&[u8]>> = Vec::new();
        if let Some(data) = &&self.buf {
            buf.push(IoVec::from_slice(data))
        }
        for other in others {
            if let Some(data) = &other.buf {
                buf.push(IoVec::from_slice(data));
            }
        }

        if !buf.is_empty() {
            return writev(self.fd, buf.as_slice()).map_err(|e| {
                error! {"fail to write to fuse device on commit: {}", e};
                io::Error::new(io::ErrorKind::Other, format!("{}", e))
            });
        }
        Ok(0)
    }
    /// Returns number of bytes already written to the internal buffer.
    /// Only available after a split.
    pub fn bytes_written(&self) -> usize {
        if let Some(data) = &self.buf {
            return data.len();
        }
        self.bytes_written
    }

    /// Returns number of bytes available for writing.  May return an error if the combined
    /// lengths of all the buffers in the DescriptorChain would cause an overflow.
    pub fn available_bytes(&self) -> usize {
        self.max_size - self.bytes_written()
    }

    fn account_written(&mut self, count: usize) {
        self.max_size -= count;
        self.bytes_written += count;
    }

    /// Writes data to the writer from a File at offset `off`.
    /// Returns the number of bytes written to the writer.
    /// The number of bytes written can be less than `count` if
    /// there isn't enough data in the writer.
    pub fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        mut count: usize,
        off: u64,
    ) -> io::Result<usize> {
        if count > self.available_bytes() {
            count = self.available_bytes();
        }
        let mut buf = Vec::with_capacity(count);
        count = src.read_vectored_at_volatile(
            // Safe because we have made sure buf has at least count capacity above
            unsafe { &[VolatileSlice::new(buf.as_mut_ptr(), count)] },
            off,
        )?;

        // Safe because we have just allocated larger count
        unsafe { buf.set_len(count) };

        if let Some(data) = &mut self.buf {
            self.buf = Some([&data[..], &mut buf[..count]].concat());
            self.account_written(count);
        } else {
            // write to fd
            return self.write(&buf[..count]);
        }
        Ok(count)
    }
}

impl<'a> io::Write for Writer<'a> {
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        if data.len() > self.available_bytes() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    self.max_size,
                    data.len()
                ),
            ));
        }
        if let Some(buf) = &mut self.buf {
            // write to internal buf
            let len = data.len();
            buf.extend_from_slice(data);
            self.account_written(len);
            Ok(len)
        } else {
            // write to fd, can only happen once per instance
            if self.fd <= 0 {
                return Err(io::Error::from_raw_os_error(libc::EINVAL));
            }
            pwrite(self.fd, data, 0)
                .and_then(|x| {
                    self.account_written(x);
                    Ok(x)
                })
                .map_err(|e| {
                    error! {"fail to write to fuse device fd {}: {}, {:?}", self.fd, e, data};
                    io::Error::new(io::ErrorKind::Other, format!("{}", e))
                })
        }
    }

    // default write_vectored only writes the first non-empty IoSlice. Override it.
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        if let Some(data) = &mut self.buf {
            let mut count = 0;
            let _ = bufs.iter().filter(|b| !b.is_empty()).map(|b| {
                data.extend_from_slice(b);
                count += b.len()
            });
            Ok(count)
        } else {
            let buf: Vec<IoVec<&[u8]>> = bufs
                .iter()
                .filter(|b| !b.is_empty())
                .map(|b| IoVec::from_slice(b))
                .collect();

            if buf.is_empty() {
                return Ok(0);
            }
            writev(self.fd, buf.as_slice())
                .and_then(|x| {
                    self.account_written(x);
                    Ok(x)
                })
                .map_err(|e| {
                    error! {"fail to write to fuse device on commit: {}", e};
                    io::Error::new(io::ErrorKind::Other, format!("{}", e))
                })
        }
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
