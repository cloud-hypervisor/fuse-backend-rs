// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Utility traits and structs to support rust async io.

use std::ffi::CStr;
use std::io;
use std::io::{IoSlice, IoSliceMut};
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::Deref;
use std::os::unix::io::RawFd;

use nix::fcntl::OFlag;
use nix::sys::stat::{mode_t, Mode};
use ringbahn::{
    event::{OpenAt, ReadVectored, Write, WriteVectored},
    Drive,
};
use vm_memory::VolatileSlice;

pub use ringbahn::{drive::demo::DemoDriver as AsyncDriver, Submission};

/// A helper trait to simplify generic type declaration
pub trait AsyncDrive: Drive + Clone + Send + 'static {}

impl<T: Drive + Clone + Send + 'static> AsyncDrive for T {}

/// Utility struct to support asynchronous io for file descriptors.
pub struct AsyncUtil<D> {
    phantom: PhantomData<D>,
}

impl<D: AsyncDrive> AsyncUtil<D> {
    /// Asynchronously open a file name `pathname` at directory `dfd`.
    pub async fn open_at(
        drive: D,
        dfd: i32,
        pathname: &'_ CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<u32> {
        let mode = if flags & libc::O_CREAT == libc::O_CREAT {
            Mode::from_bits(0)
        } else {
            Mode::from_bits(mode as mode_t)
        };
        let mode = mode.ok_or(io::Error::from_raw_os_error(libc::EINVAL))?;
        let flags = OFlag::from_bits(flags);
        let flags = flags.ok_or(io::Error::from_raw_os_error(libc::EINVAL))?;

        let event = OpenAt {
            path: pathname.to_owned(),
            dir_fd: dfd,
            flags,
            mode,
        };
        let (_event, result) = Submission::new(event, drive).await;

        result
    }

    /// Asynchronously read from the file into vectored data buffers.
    pub async fn read_vectored(
        drive: D,
        fd: RawFd,
        bufs: &[IoSliceMut<'_>],
        offset: u64,
    ) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs: Vec<Box<[u8]>> = bufs
            .iter()
            .filter(|b| !b.is_empty())
            .map(|b| unsafe { Box::from_raw(b.deref() as *const [u8] as *mut [u8]) })
            .collect();
        let bufs = bufs.into();

        let event = ReadVectored { fd, bufs, offset };
        let (ReadVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake Box<[Box<[u8]>> object, otherwise it will cause double-free.
        let mut vec: Vec<Box<[u8]>> = bufs.into();
        unsafe { vec.set_len(0) };

        result.map(|v| v as usize)
    }

    /// Asynchronously write out vectored data buffers to the file.
    pub async fn read_to_volatile_slices(
        drive: D,
        fd: RawFd,
        slices: &[VolatileSlice<'_>],
        offset: u64,
    ) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs: Vec<Box<[u8]>> = slices
            .iter()
            .filter(|b| b.is_empty())
            .map(|&b| unsafe { Vec::from_raw_parts(b.as_ptr(), b.len(), b.len()).into() })
            .collect();
        let bufs = bufs.into();

        let event = ReadVectored { fd, bufs, offset };
        let (ReadVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake Box<[Box<[u8]>> object, otherwise it will cause double-free.
        let mut vec: Vec<Box<[u8]>> = bufs.into();
        unsafe { vec.set_len(0) };

        result.map(|v| v as usize)
    }

    /// Asynchronously write out data buffer to the file.
    pub async fn write(drive: D, fd: RawFd, data: &[u8], offset: u64) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let buf = unsafe { Box::from_raw(data as *const [u8] as *mut [u8]) };

        let event = Write { fd, buf, offset };
        let (Write { buf, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake [Box<[u8]> object, otherwise it will cause double-free.
        ManuallyDrop::new(buf);

        result.map(|v| v as usize)
    }

    /// Asynchronously write out vectored data buffers to the file.
    pub async fn write_vectored(
        drive: D,
        fd: RawFd,
        bufs: &[IoSlice<'_>],
        offset: u64,
    ) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs: Vec<Box<[u8]>> = bufs
            .iter()
            .filter(|b| !b.is_empty())
            .map(|b| unsafe { Box::from_raw(b.deref() as *const [u8] as *mut [u8]) })
            .collect();
        let bufs = bufs.into();

        let event = WriteVectored { fd, bufs, offset };
        let (WriteVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake Box<[Box<[u8]>> object, otherwise it will cause double-free.
        let mut vec: Vec<Box<[u8]>> = bufs.into();
        unsafe { vec.set_len(0) };

        result.map(|v| v as usize)
    }

    /// Asynchronously write out vectored data buffers to the file.
    pub async fn write_from_volatile_slices(
        drive: D,
        fd: RawFd,
        slices: &[VolatileSlice<'_>],
        offset: u64,
    ) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs: Vec<Box<[u8]>> = slices
            .iter()
            .filter(|b| b.is_empty())
            .map(|&b| unsafe { Vec::from_raw_parts(b.as_ptr(), b.len(), b.len()).into() })
            .collect();
        let bufs = bufs.into();

        let event = WriteVectored { fd, bufs, offset };
        let (WriteVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake Box<[Box<[u8]>> object, otherwise it will cause double-free.
        let mut vec: Vec<Box<[u8]>> = bufs.into();
        unsafe { vec.set_len(0) };

        result.map(|v| v as usize)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::io::{Read, Seek};
    use std::os::unix::io::AsRawFd;

    use futures::executor::{block_on, ThreadPool};
    use futures::io::SeekFrom;
    use futures::task::SpawnExt;
    use ringbahn::drive::demo::DemoDriver;

    #[test]
    fn test_async_write() {
        let file = vmm_sys_util::tempfile::TempFile::new().unwrap();
        let executor = ThreadPool::new().unwrap();
        let fd = file.as_file().as_raw_fd();

        let handle = executor
            .spawn_with_handle(async move {
                let buf = [
                    0x1u8, 0x2u8, 0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8,
                ];
                let drive = DemoDriver::default();
                let task = AsyncUtil::write(drive, fd, &buf, 1);

                task.await
            })
            .unwrap();
        let result = block_on(handle).unwrap();
        assert_eq!(result, 9);

        let buf = [
            0x1u8, 0x2u8, 0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8,
        ];
        let mut buf2 = [0x0u8; 10];
        file.as_file().seek(SeekFrom::Start(0)).unwrap();
        file.as_file().read(&mut buf2).unwrap();
        assert_eq!(buf, buf2[1..]);
        assert_eq!(buf2[0], 0);
    }

    #[test]
    fn test_async_write_vectored() {
        let file = vmm_sys_util::tempfile::TempFile::new().unwrap();
        let executor = ThreadPool::new().unwrap();
        let fd = file.as_file().as_raw_fd();

        let handle = executor
            .spawn_with_handle(async move {
                let buf = [
                    0x1u8, 0x2u8, 0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8,
                ];
                let buf2 = [
                    0x1u8, 0x2u8, 0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8,
                ];
                let bufs = vec![IoSlice::new(&buf), IoSlice::new(&buf2)];
                let drive = DemoDriver::default();
                let task = AsyncUtil::write_vectored(drive, fd, &bufs, 1);

                task.await
            })
            .unwrap();
        let result = block_on(handle).unwrap();
        assert_eq!(result, 18);

        let buf = [
            0x1u8, 0x2u8, 0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8,
        ];
        let mut buf2 = [0x0u8; 10];
        file.as_file().seek(SeekFrom::Start(0)).unwrap();
        file.as_file().read(&mut buf2).unwrap();
        assert_eq!(buf, buf2[1..10]);
        assert_eq!(buf, buf2[10..=18]);
        assert_eq!(buf2[0], 0);
    }
}
