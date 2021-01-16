// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Traits and Structs to implement the /dev/fuse Fuse transport layer.

use std::collections::VecDeque;
use std::fmt;
use std::io::{self, IoSlice, Write};
use std::marker::PhantomData;
#[cfg(feature = "async-io")]
use std::os::unix::io::RawFd;

use libc::c_int;
use nix::sys::uio::{pwrite, writev, IoVec};

use vm_memory::{ByteValued, VolatileMemory, VolatileMemoryError, VolatileSlice};

use super::{FileReadWriteVolatile, IoBuffers, Reader};

#[cfg(feature = "async-io")]
use crate::async_util::{AsyncDrive, AsyncUtil};

mod session;
pub use session::*;

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
    /// Session errors
    SessionFailure(String),
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
            SessionFailure(e) => write!(f, "fuse session failure: {}", e),
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
/// 2. If the writer is split, a final commit() MUST be called to issue the
///    device write operation.
/// 3. Concurrency, caller should not write to the writer concurrently.
#[derive(Debug, PartialEq, Eq)]
pub struct Writer<'a> {
    fd: c_int,
    max_size: usize,
    bytes_written: usize,
    // buf used to support split writer.
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
            self.buf = Some(Vec::with_capacity(offset));
        }
        let max_size = self.max_size - offset;
        self.max_size = offset;
        Ok(Writer {
            fd: self.fd,
            max_size,
            bytes_written: 0,
            buf: Some(Vec::with_capacity(max_size)),
            phantom: PhantomData,
        })
    }

    /// Commit all internal buffers of self and others
    /// We need this because the lifetime of others is usually shorter than self.
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
                e.as_errno()
                    .map(|r| io::Error::from_raw_os_error(r as i32))
                    .unwrap_or_else(|| io::Error::new(io::ErrorKind::Other, format!("{}", e)))
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
        self.bytes_written += count;
    }

    /// Writes an object to the writer.
    pub fn write_obj<T: ByteValued>(&mut self, val: T) -> io::Result<()> {
        self.write_all(val.as_slice())
    }

    /// Writes data to the writer from a file descriptor.
    /// Returns the number of bytes written to the writer.
    pub fn write_from<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        count: usize,
    ) -> io::Result<usize> {
        self.check_available_space(count)?;

        let mut buf = Vec::with_capacity(count);
        let cnt = src.read_vectored_volatile(
            // Safe because we have made sure buf has at least count capacity above
            unsafe { &[VolatileSlice::new(buf.as_mut_ptr(), count)] },
        )?;

        // Safe because we have just allocated larger count
        unsafe { buf.set_len(cnt) };

        if let Some(data) = &mut self.buf {
            self.buf = Some([&data[..], &mut buf[..cnt]].concat());
            self.account_written(cnt);
            Ok(cnt)
        } else {
            // write to fd
            self.write(&buf[..cnt])
        }
    }

    /// Writes data to the writer from a File at offset `off`.
    /// Returns the number of bytes written to the writer.
    pub fn write_from_at<F: FileReadWriteVolatile>(
        &mut self,
        mut src: F,
        mut count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.check_available_space(count)?;

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
            Ok(count)
        } else {
            // write to fd
            self.write(&buf[..count])
        }
    }

    /// Writes all data to the writer from a file descriptor.
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
    fn write(&mut self, data: &[u8]) -> io::Result<usize> {
        self.check_available_space(data.len())?;
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
                .map(|x| {
                    self.account_written(x);
                    x
                })
                .map_err(|e| {
                    error! {"fail to write to fuse device fd {}: {}, {:?}", self.fd, e, data};
                    io::Error::new(io::ErrorKind::Other, format!("{}", e))
                })
        }
    }

    // default write_vectored only writes the first non-empty IoSlice. Override it.
    fn write_vectored(&mut self, bufs: &[IoSlice<'_>]) -> io::Result<usize> {
        self.check_available_space(bufs.iter().fold(0, |acc, x| acc + x.len()))?;

        if let Some(data) = &mut self.buf {
            let count = bufs.iter().filter(|b| !b.is_empty()).fold(0, |acc, b| {
                data.extend_from_slice(b);
                acc + b.len()
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
                .map(|x| {
                    self.account_written(x);
                    x
                })
                .map_err(|e| {
                    error! {"fail to write to fuse device on commit: {}", e};
                    io::Error::new(io::ErrorKind::Other, format!("{}", e))
                })
        }
    }

    /// As this writer can associate multiple writers by splitting, `flush()` can't
    /// flush them all. Disable it!
    fn flush(&mut self) -> io::Result<()> {
        Err(io::Error::new(
            io::ErrorKind::Other,
            "Writer does not support flush buffer.",
        ))
    }
}

#[cfg(feature = "async-io")]
mod async_io {
    use super::*;
    use futures::io::IoSliceMut;

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
            drive: D,
            data: &[u8],
        ) -> io::Result<usize> {
            self.check_available_space(data.len())?;

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
                AsyncUtil::write(drive, self.fd, data, 0)
                    .await
                    .map(|x| {
                        self.account_written(x);
                        x
                    })
                    .map_err(|e| {
                        error! {"fail to write to fuse device fd {}: {}, {:?}", self.fd, e, data};
                        io::Error::new(io::ErrorKind::Other, format!("{}", e))
                    })
            }
        }

        /// Write data from a group of buffers into this writer in asynchronous mode, skipping empty
        /// buffers.
        pub async fn async_write_vectored<D: AsyncDrive>(
            &mut self,
            drive: D,
            bufs: &[IoSlice<'_>],
        ) -> io::Result<usize> {
            self.check_available_space(bufs.iter().fold(0, |acc, x| acc + x.len()))?;

            if let Some(data) = &mut self.buf {
                let count = bufs.iter().filter(|b| !b.is_empty()).fold(0, |acc, b| {
                    data.extend_from_slice(b);
                    acc + b.len()
                });
                Ok(count)
            } else {
                if bufs.is_empty() {
                    Ok(0)
                } else {
                    AsyncUtil::write_vectored(drive, self.fd, bufs, 0)
                        .await
                        .map(|x| {
                            self.account_written(x);
                            x
                        })
                        .map_err(|e| {
                            error! {"fail to write to fuse device on commit: {}", e};
                            io::Error::new(io::ErrorKind::Other, format!("{}", e))
                        })
                }
            }
        }

        /// Attempts to write an entire buffer into this writer in asynchronous mode.
        pub async fn async_write_all<D: AsyncDrive>(
            &mut self,
            drive: D,
            mut buf: &[u8],
        ) -> io::Result<()> {
            while !buf.is_empty() {
                match self.async_write(drive.clone(), buf).await {
                    Ok(0) => {
                        return Err(io::Error::new(
                            io::ErrorKind::WriteZero,
                            "failed to write whole buffer",
                        ));
                    }
                    Ok(n) => buf = &buf[n..],
                    Err(ref e) if e.kind() == io::ErrorKind::Interrupted => {}
                    Err(e) => return Err(e),
                }
            }

            Ok(())
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

            let drive2 = drive.clone();
            let mut buf = Vec::with_capacity(count);
            // safe because capacity is @count.
            unsafe { buf.set_len(count) };

            let count =
                AsyncUtil::read_vectored(drive2, src, &[IoSliceMut::new(&mut buf)], off).await?;

            // Safe because we have just allocated larger count
            unsafe { buf.set_len(count) };

            if let Some(data) = &mut self.buf {
                self.buf = Some([&data[..], &mut buf[..count]].concat());
                self.account_written(count);
                Ok(count)
            } else {
                // write to fd
                AsyncUtil::write(drive, self.fd, &buf[..count], 0).await
            }
        }

        /// Commit all internal buffers of self and others
        /// We need this because the lifetime of others is usually shorter than self.
        pub async fn async_commit<D: AsyncDrive>(
            &mut self,
            drive: D,
            others: &[&Writer<'a>],
        ) -> io::Result<usize> {
            if self.buf.is_none() {
                return Ok(0);
            }

            // TODO: remove one extra Vec allocation. One here, another in AsyncUtil::write_vectored().
            let mut bufs = Vec::new();
            if let Some(data) = self.buf.as_ref() {
                bufs.push(IoSlice::new(data))
            }
            for other in others {
                if let Some(data) = &other.buf {
                    bufs.push(IoSlice::new(data))
                }
            }

            if !bufs.is_empty() {
                AsyncUtil::write_vectored(drive, self.fd, &bufs, 0).await
            } else {
                Ok(0)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Read, Seek, SeekFrom, Write};
    use std::os::unix::io::AsRawFd;
    use vmm_sys_util::tempfile::TempFile;

    #[cfg(feature = "async-io")]
    use futures::executor::{block_on, ThreadPool};
    #[cfg(feature = "async-io")]
    use futures::task::SpawnExt;
    #[cfg(feature = "async-io")]
    use ringbahn::drive::demo::DemoDriver;

    #[test]
    fn reader_test_simple_chain() {
        let mut buf = [0u8; 106];
        let mut reader = Reader::new(FuseBuf::new(&mut buf)).unwrap();

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
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 106).unwrap();

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
    fn writer_test_split_chain() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 108).unwrap();
        let writer2 = writer.split_at(106).unwrap();

        assert_eq!(writer.available_bytes(), 106);
        assert_eq!(writer.bytes_written(), 0);
        assert_eq!(writer2.available_bytes(), 2);
        assert_eq!(writer2.bytes_written(), 0);

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
    fn reader_unexpected_eof() {
        let mut buf = [0u8; 106];
        let mut reader = Reader::new(FuseBuf::new(&mut buf)).unwrap();

        let mut buf2 = Vec::with_capacity(1024);
        buf2.resize(1024, 0);

        assert_eq!(
            reader
                .read_exact(&mut buf2[..])
                .expect_err("read more bytes than available")
                .kind(),
            io::ErrorKind::UnexpectedEof
        );
    }

    #[test]
    fn reader_split_border() {
        let mut buf = [0u8; 128];
        let mut reader = Reader::new(FuseBuf::new(&mut buf)).unwrap();
        let other = reader.split_at(32).expect("failed to split Reader");

        assert_eq!(reader.available_bytes(), 32);
        assert_eq!(other.available_bytes(), 96);
    }

    #[test]
    fn reader_split_outofbounds() {
        let mut buf = [0u8; 128];
        let mut reader = Reader::new(FuseBuf::new(&mut buf)).unwrap();

        if let Ok(_) = reader.split_at(256) {
            panic!("successfully split Reader with out of bounds offset");
        }
    }

    #[test]
    fn writer_simple_commit_header() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 106).unwrap();

        assert_eq!(writer.available_bytes(), 106);

        writer.write(&[0x1u8; 4]).unwrap();
        assert_eq!(writer.available_bytes(), 102);
        assert_eq!(writer.bytes_written(), 4);

        let buf = vec![0xdeu8; 64];
        let slices = [
            IoSlice::new(&buf[..32]),
            IoSlice::new(&buf[32..48]),
            IoSlice::new(&buf[48..]),
        ];
        assert_eq!(
            writer
                .write_vectored(&slices)
                .expect("failed to write from buffer"),
            64
        );
        assert!(writer.flush().is_err());

        writer.commit(&[]).unwrap();
    }

    #[test]
    fn writer_split_commit_header() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 106).unwrap();
        let mut other = writer.split_at(4).expect("failed to split Writer");

        assert_eq!(writer.available_bytes(), 4);
        assert_eq!(other.available_bytes(), 102);

        writer.write(&[0x1u8; 4]).unwrap();
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 4);

        let buf = vec![0xdeu8; 64];
        let slices = [
            IoSlice::new(&buf[..32]),
            IoSlice::new(&buf[32..48]),
            IoSlice::new(&buf[48..]),
        ];
        assert_eq!(
            other
                .write_vectored(&slices)
                .expect("failed to write from buffer"),
            64
        );
        assert!(writer.flush().is_err());

        writer.commit(&[]).unwrap();
    }

    #[test]
    fn writer_split_commit_all() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 106).unwrap();
        let mut other = writer.split_at(4).expect("failed to split Writer");

        assert_eq!(writer.available_bytes(), 4);
        assert_eq!(other.available_bytes(), 102);

        writer.write(&[0x1u8; 4]).unwrap();
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 4);

        let buf = vec![0xdeu8; 64];
        let slices = [
            IoSlice::new(&buf[..32]),
            IoSlice::new(&buf[32..48]),
            IoSlice::new(&buf[48..]),
        ];
        assert_eq!(
            other
                .write_vectored(&slices)
                .expect("failed to write from buffer"),
            64
        );

        writer.commit(&[&other]).unwrap();
    }

    #[test]
    fn read_full() {
        let mut buf2 = [0u8; 48];
        let mut reader = Reader::new(FuseBuf::new(&mut buf2)).unwrap();
        let mut buf = vec![0u8; 64];

        assert_eq!(
            reader.read(&mut buf[..]).expect("failed to read to buffer"),
            48
        );
    }

    #[test]
    fn write_full() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 48).unwrap();

        let buf = vec![0xdeu8; 64];
        writer.write(&buf[..]).unwrap_err();

        let buf = vec![0xdeu8; 48];
        assert_eq!(
            writer.write(&buf[..]).expect("failed to write from buffer"),
            48
        );
    }

    #[test]
    fn write_vectored() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 48).unwrap();

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
    }

    #[test]
    fn read_obj() {
        let mut buf2 = [0u8; 9];
        let mut reader = Reader::new(FuseBuf::new(&mut buf2)).unwrap();

        let _val: u64 = reader.read_obj().expect("failed to read to file");

        assert_eq!(reader.available_bytes(), 1);
        assert_eq!(reader.bytes_read(), 8);
        assert!(reader.read_obj::<u64>().is_err());
    }

    #[test]
    fn read_exact_to() {
        let mut buf2 = [0u8; 48];
        let mut reader = Reader::new(FuseBuf::new(&mut buf2)).unwrap();
        let mut file = TempFile::new().unwrap().into_file();

        reader
            .read_exact_to(&mut file, 47)
            .expect("failed to read to file");

        assert_eq!(reader.available_bytes(), 1);
        assert_eq!(reader.bytes_read(), 47);
    }

    #[test]
    fn read_to_at() {
        let mut buf2 = [0u8; 48];
        let mut reader = Reader::new(FuseBuf::new(&mut buf2)).unwrap();
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
    fn write_obj() {
        let file1 = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file1.as_raw_fd(), 48).unwrap();
        let val = 0x1u64;

        writer.write_obj(val).expect("failed to write from buffer");
        assert_eq!(writer.available_bytes(), 40);
    }

    #[test]
    fn write_all_from() {
        let file1 = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file1.as_raw_fd(), 48).unwrap();
        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];

        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        writer
            .write_all_from(&mut file, 47)
            .expect("failed to write from buffer");
        assert_eq!(writer.available_bytes(), 1);
        assert_eq!(writer.bytes_written(), 47);

        // Write more data than capacity
        writer.write_all_from(&mut file, 2).unwrap_err();
        assert_eq!(writer.available_bytes(), 1);
        assert_eq!(writer.bytes_written(), 47);
    }

    #[test]
    fn write_all_from_split() {
        let file1 = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file1.as_raw_fd(), 58).unwrap();
        let _other = writer.split_at(48).unwrap();
        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];

        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        writer
            .write_all_from(&mut file, 47)
            .expect("failed to write from buffer");
        assert_eq!(writer.available_bytes(), 1);
        assert_eq!(writer.bytes_written(), 47);

        // Write more data than capacity
        writer.write_all_from(&mut file, 2).unwrap_err();
        assert_eq!(writer.available_bytes(), 1);
        assert_eq!(writer.bytes_written(), 47);
    }

    #[test]
    fn write_from_at() {
        let file1 = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file1.as_raw_fd(), 48).unwrap();
        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];

        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        assert_eq!(
            writer
                .write_from_at(&mut file, 40, 16)
                .expect("failed to write from buffer"),
            40
        );
        assert_eq!(writer.available_bytes(), 8);
        assert_eq!(writer.bytes_written(), 40);

        // Write more data than capacity
        writer.write_from_at(&mut file, 40, 16).unwrap_err();
        assert_eq!(writer.available_bytes(), 8);
        assert_eq!(writer.bytes_written(), 40);
    }

    #[test]
    fn write_from_at_split() {
        let file1 = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file1.as_raw_fd(), 58).unwrap();
        let _other = writer.split_at(48).unwrap();
        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];

        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        assert_eq!(
            writer
                .write_from_at(&mut file, 40, 16)
                .expect("failed to write from buffer"),
            40
        );
        assert_eq!(writer.available_bytes(), 8);
        assert_eq!(writer.bytes_written(), 40);

        // Write more data than capacity
        writer.write_from_at(&mut file, 40, 16).unwrap_err();
        assert_eq!(writer.available_bytes(), 8);
        assert_eq!(writer.bytes_written(), 40);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn async_read_to_at() {
        let file = TempFile::new().unwrap().into_file();
        let fd = file.as_raw_fd();

        let executor = ThreadPool::new().unwrap();
        let handle = executor
            .spawn_with_handle(async move {
                let mut buf2 = [0u8; 48];
                let mut reader = Reader::new(FuseBuf::new(&mut buf2)).unwrap();

                let drive = DemoDriver::default();
                reader.async_read_to_at(drive, fd, 48, 16).await
            })
            .unwrap();

        let result = block_on(handle).unwrap();
        assert_eq!(result, 48);
        // assert_eq!(reader.available_bytes(), 0);
        // assert_eq!(reader.bytes_read(), 48);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn async_write() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 48).unwrap();

        let executor = ThreadPool::new().unwrap();
        let handle = executor
            .spawn_with_handle(async move {
                let drive = DemoDriver::default();

                let buf = vec![0xdeu8; 64];
                writer.async_write(drive, &buf[..]).await
            })
            .unwrap();

        // expect errors
        block_on(handle).unwrap_err();


        let mut writer2 = Writer::new(file.as_raw_fd(), 48).unwrap();
        let handle = executor
            .spawn_with_handle(async move {
                let drive = DemoDriver::default();

                let buf = vec![0xdeu8; 48];
                writer2.async_write(drive, &buf[..]).await
            })
            .unwrap();

        let result = block_on(handle).unwrap();
        assert_eq!(result, 48);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn async_write_vectored() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 48).unwrap();

        let executor = ThreadPool::new().unwrap();
        let handle = executor
            .spawn_with_handle(async move {
                let drive = DemoDriver::default();

                let buf = vec![0xdeu8; 48];
                let slices = [
                    IoSlice::new(&buf[..32]),
                    IoSlice::new(&buf[32..40]),
                    IoSlice::new(&buf[40..]),
                ];

                writer.async_write_vectored(drive, &slices).await
            })
            .unwrap();

        let result = block_on(handle).unwrap();
        assert_eq!(result, 48);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn async_write_from_at() {
        let file1 = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file1.as_raw_fd(), 48).unwrap();
        let mut file = TempFile::new().unwrap().into_file();
        let buf = vec![0xdeu8; 64];

        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();
        let fd = file.as_raw_fd();

        let executor = ThreadPool::new().unwrap();
        let handle = executor
            .spawn_with_handle(async move {
                let drive = DemoDriver::default();

                writer.async_write_from_at(drive, fd, 40, 16).await
            })
            .unwrap();

        let result = block_on(handle).unwrap();
        assert_eq!(result, 40);
    }

    #[cfg(feature = "async-io")]
    #[test]
    fn async_writer_split_commit_all() {
        let file = TempFile::new().unwrap().into_file();
        let mut writer = Writer::new(file.as_raw_fd(), 106).unwrap();
        let mut other = writer.split_at(4).expect("failed to split Writer");

        assert_eq!(writer.available_bytes(), 4);
        assert_eq!(other.available_bytes(), 102);

        writer.write(&[0x1u8; 4]).unwrap();
        assert_eq!(writer.available_bytes(), 0);
        assert_eq!(writer.bytes_written(), 4);

        let buf = vec![0xdeu8; 64];
        let slices = [
            IoSlice::new(&buf[..32]),
            IoSlice::new(&buf[32..48]),
            IoSlice::new(&buf[48..]),
        ];
        assert_eq!(
            other
                .write_vectored(&slices)
                .expect("failed to write from buffer"),
            64
        );

        let executor = ThreadPool::new().unwrap();
        let handle = executor
            .spawn_with_handle(async move {
                let drive = DemoDriver::default();

                writer.async_commit(drive, &[&other]).await
            })
            .unwrap();

        let _result = block_on(handle).unwrap();
    }
}
