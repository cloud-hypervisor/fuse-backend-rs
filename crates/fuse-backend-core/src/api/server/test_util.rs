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
use std::ptr::copy_nonoverlapping;

use vm_memory::VolatileSlice;

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

/// A [`Writer`] that captures reply messages into a caller supplied buffer.
///
/// It mirrors the semantics of the virtio-fs writer: writes go straight into
/// the buffer, `commit()` is a no-op returning zero, and `bytes_written()`
/// counts the bytes actually copied, which is what the server reports as the
/// reply size.
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

#[cfg_attr(feature = "async-io", async_trait::async_trait(?Send))]
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
}
