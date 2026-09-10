// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! `File` to wrap over `tokio::fs::File` and `tokio-uring::fs::File`.

use std::any::Any;
use std::fmt::{Debug, Formatter};
use std::io::{ErrorKind, IoSlice, IoSliceMut};
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::path::Path;
use std::sync::Arc;

use crate::async_runtime::{RuntimeType, RUNTIME_TYPE};
use crate::file_buf::FileVolatileBuf;
use crate::{off64_t, preadv64, pwritev64};

/// An adapter enum to support both tokio and tokio-uring asynchronous `File`.
pub enum File {
    /// Tokio asynchronous `File`.
    Tokio(tokio::fs::File),
    #[cfg(target_os = "linux")]
    /// Tokio-uring asynchronous `File`.
    Uring(tokio_uring::fs::File),
    /// A file descriptor borrowed from another object.
    ///
    /// The `_guard` reference must keep the descriptor valid for the whole
    /// lifetime of the `File` object. Unlike the other variants, dropping
    /// this object doesn't close the file descriptor.
    Borrowed {
        /// The borrowed file descriptor.
        fd: RawFd,
        /// A reference keeping the file descriptor valid.
        _guard: Arc<dyn Any>,
    },
}

impl File {
    /// Asynchronously open a file.
    pub async fn async_open<P: AsRef<Path>>(
        path: P,
        write: bool,
        create: bool,
    ) -> std::io::Result<Self> {
        match *RUNTIME_TYPE {
            RuntimeType::Tokio => tokio::fs::OpenOptions::new()
                .read(true)
                .write(write)
                .create(create)
                .open(path)
                .await
                .map(File::Tokio),
            #[cfg(target_os = "linux")]
            RuntimeType::Uring => tokio_uring::fs::OpenOptions::new()
                .read(true)
                .write(write)
                .create(create)
                .open(path)
                .await
                .map(File::Uring),
        }
    }

    /// Wrap an existing `std::fs::File` object into an asynchronous `File` object.
    ///
    /// The returned object takes ownership of `file` and closes the underlying file
    /// descriptor when dropped.
    pub fn from_std_file(file: std::fs::File) -> Self {
        match *RUNTIME_TYPE {
            RuntimeType::Tokio => File::Tokio(tokio::fs::File::from_std(file)),
            #[cfg(target_os = "linux")]
            RuntimeType::Uring => File::Uring(tokio_uring::fs::File::from_std(file)),
        }
    }

    /// Borrow an existing file descriptor to serve asynchronous IO.
    ///
    /// The returned object doesn't own the descriptor and doesn't close it
    /// when dropped: `guard` must keep the descriptor valid for as long as
    /// the returned object, and any IO submitted through it, lives.
    pub fn borrow_fd(fd: RawFd, guard: Arc<dyn Any>) -> Self {
        File::Borrowed { fd, _guard: guard }
    }

    /// Asynchronously read data at `offset` into the buffer.
    pub async fn async_read_at(
        &self,
        buf: FileVolatileBuf,
        offset: u64,
    ) -> (std::io::Result<usize>, FileVolatileBuf) {
        match self {
            File::Tokio(f) => {
                // tokio::fs:File doesn't support read_at() yet.
                //f.read_at(buf, offset).await,
                let mut bufs = [buf];
                let res = preadv(f.as_raw_fd(), &mut bufs, offset);
                (res, bufs[0])
            }
            #[cfg(target_os = "linux")]
            File::Uring(f) => f.read_at(buf, offset).await,
            File::Borrowed { fd, .. } => {
                #[cfg(target_os = "linux")]
                if matches!(*RUNTIME_TYPE, RuntimeType::Uring) {
                    // Safe because `fd` is valid for the lifetime of this
                    // object, and the wrapper is forgotten on drop (including
                    // cancellation of the IO) so it never closes the
                    // borrowed descriptor.
                    let file = unsafe { tokio_uring::fs::File::from_raw_fd(*fd) };
                    return ForgetOnDrop::new(file).read_at(buf, offset).await;
                }
                let mut bufs = [buf];
                let res = preadv(*fd, &mut bufs, offset);
                (res, bufs[0])
            }
        }
    }

    /// Asynchronously read data at `offset` into buffers.
    pub async fn async_readv_at(
        &self,
        mut bufs: Vec<FileVolatileBuf>,
        offset: u64,
    ) -> (std::io::Result<usize>, Vec<FileVolatileBuf>) {
        match self {
            File::Tokio(f) => {
                // tokio::fs:File doesn't support read_at() yet.
                //f.read_at(buf, offset).await,
                let res = preadv(f.as_raw_fd(), &mut bufs, offset);
                (res, bufs)
            }
            #[cfg(target_os = "linux")]
            File::Uring(f) => f.readv_at(bufs, offset).await,
            File::Borrowed { fd, .. } => {
                #[cfg(target_os = "linux")]
                if matches!(*RUNTIME_TYPE, RuntimeType::Uring) {
                    // Safe because `fd` is valid for the lifetime of this
                    // object, and the wrapper is forgotten on drop (including
                    // cancellation of the IO) so it never closes the
                    // borrowed descriptor.
                    let file = unsafe { tokio_uring::fs::File::from_raw_fd(*fd) };
                    return ForgetOnDrop::new(file).readv_at(bufs, offset).await;
                }
                let res = preadv(*fd, &mut bufs, offset);
                (res, bufs)
            }
        }
    }

    /// Asynchronously write data at `offset` from the buffer.
    pub async fn async_write_at(
        &self,
        buf: FileVolatileBuf,
        offset: u64,
    ) -> (std::io::Result<usize>, FileVolatileBuf) {
        match self {
            File::Tokio(f) => {
                // tokio::fs:File doesn't support read_at() yet.
                //f.read_at(buf, offset).await,
                let bufs = [buf];
                let res = pwritev(f.as_raw_fd(), &bufs, offset);
                (res, bufs[0])
            }
            #[cfg(target_os = "linux")]
            File::Uring(f) => f.write_at(buf, offset).await,
            File::Borrowed { fd, .. } => {
                #[cfg(target_os = "linux")]
                if matches!(*RUNTIME_TYPE, RuntimeType::Uring) {
                    // Safe because `fd` is valid for the lifetime of this
                    // object, and the wrapper is forgotten on drop (including
                    // cancellation of the IO) so it never closes the
                    // borrowed descriptor.
                    let file = unsafe { tokio_uring::fs::File::from_raw_fd(*fd) };
                    return ForgetOnDrop::new(file).write_at(buf, offset).await;
                }
                let bufs = [buf];
                let res = pwritev(*fd, &bufs, offset);
                (res, bufs[0])
            }
        }
    }

    /// Asynchronously write data at `offset` from buffers.
    pub async fn async_writev_at(
        &self,
        bufs: Vec<FileVolatileBuf>,
        offset: u64,
    ) -> (std::io::Result<usize>, Vec<FileVolatileBuf>) {
        match self {
            File::Tokio(f) => {
                // tokio::fs:File doesn't support read_at() yet.
                //f.read_at(buf, offset).await,
                let res = pwritev(f.as_raw_fd(), &bufs, offset);
                (res, bufs)
            }
            #[cfg(target_os = "linux")]
            File::Uring(f) => f.writev_at(bufs, offset).await,
            File::Borrowed { fd, .. } => {
                #[cfg(target_os = "linux")]
                if matches!(*RUNTIME_TYPE, RuntimeType::Uring) {
                    // Safe because `fd` is valid for the lifetime of this
                    // object, and the wrapper is forgotten on drop (including
                    // cancellation of the IO) so it never closes the
                    // borrowed descriptor.
                    let file = unsafe { tokio_uring::fs::File::from_raw_fd(*fd) };
                    return ForgetOnDrop::new(file).writev_at(bufs, offset).await;
                }
                let res = pwritev(*fd, &bufs, offset);
                (res, bufs)
            }
        }
    }

    /// Get metadata about the file.
    pub fn metadata(&self) -> std::io::Result<std::fs::Metadata> {
        // Safe because we have manually forget() the `file` object below.
        let file = unsafe { std::fs::File::from_raw_fd(self.as_raw_fd()) };
        let res = file.metadata();
        std::mem::forget(file);
        res
    }

    /// Try to clone the file object.
    pub async fn async_try_clone(&self) -> std::io::Result<Self> {
        match self {
            File::Tokio(f) => f.try_clone().await.map(File::Tokio),
            #[cfg(target_os = "linux")]
            File::Uring(f) => {
                // Safe because file.as_raw_fd() is valid RawFd and we have checked the result.
                let fd = unsafe { libc::dup(f.as_raw_fd()) };
                if fd < 0 {
                    Err(std::io::Error::last_os_error())
                } else {
                    // Safe because we dup a new raw fd.
                    Ok(File::Uring(unsafe {
                        tokio_uring::fs::File::from_raw_fd(fd)
                    }))
                }
            }
            File::Borrowed { fd, _guard } => Ok(File::Borrowed {
                fd: *fd,
                _guard: _guard.clone(),
            }),
        }
    }
}

impl AsRawFd for File {
    fn as_raw_fd(&self) -> RawFd {
        match self {
            File::Tokio(f) => f.as_raw_fd(),
            #[cfg(target_os = "linux")]
            File::Uring(f) => f.as_raw_fd(),
            File::Borrowed { fd, .. } => *fd,
        }
    }
}

impl Debug for File {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let fd = self.as_raw_fd();
        write!(f, "Async File {}", fd)
    }
}

/// A wrapper which forgets its content instead of dropping it.
///
/// Used to wrap file objects created from borrowed descriptors, so that the
/// descriptor is never closed, even when the asynchronous IO is cancelled
/// and the future dropped in flight.
#[cfg(target_os = "linux")]
struct ForgetOnDrop<T>(Option<T>);

#[cfg(target_os = "linux")]
impl<T> ForgetOnDrop<T> {
    fn new(value: T) -> Self {
        ForgetOnDrop(Some(value))
    }
}

#[cfg(target_os = "linux")]
impl<T> std::ops::Deref for ForgetOnDrop<T> {
    type Target = T;

    fn deref(&self) -> &T {
        self.0.as_ref().expect("value already consumed")
    }
}

#[cfg(target_os = "linux")]
impl<T> Drop for ForgetOnDrop<T> {
    fn drop(&mut self) {
        if let Some(value) = self.0.take() {
            std::mem::forget(value);
        }
    }
}

/// A simple wrapper over posix `preadv` to deal with `FileVolatileBuf`.
pub fn preadv(fd: RawFd, bufs: &mut [FileVolatileBuf], offset: u64) -> std::io::Result<usize> {
    let iov: Vec<IoSliceMut> = bufs.iter().map(|v| v.io_slice_mut()).collect();

    loop {
        // SAFETY: it is ABI compatible, a pointer cast here is valid
        let res = unsafe {
            preadv64(
                fd,
                iov.as_ptr() as *const libc::iovec,
                iov.len() as libc::c_int,
                offset as off64_t,
            )
        };

        if res >= 0 {
            let mut count = res as usize;
            for buf in bufs.iter_mut() {
                let cnt = std::cmp::min(count, buf.cap() - buf.len());
                unsafe { buf.set_size(buf.len() + cnt) };
                count -= cnt;
                if count == 0 {
                    break;
                }
            }
            assert_eq!(count, 0);
            return Ok(res as usize);
        } else {
            let e = std::io::Error::last_os_error();
            // Retry if the IO is interrupted by signal.
            if e.kind() != ErrorKind::Interrupted {
                return Err(e);
            }
        }
    }
}

/// A simple wrapper over posix `pwritev` to deal with `FileVolatileBuf`.
pub fn pwritev(fd: RawFd, bufs: &[FileVolatileBuf], offset: u64) -> std::io::Result<usize> {
    let iov: Vec<IoSlice> = bufs.iter().map(|v| v.io_slice()).collect();

    loop {
        // SAFETY: it is ABI compatible, a pointer cast here is valid
        let res = unsafe {
            pwritev64(
                fd,
                iov.as_ptr() as *const libc::iovec,
                iov.len() as libc::c_int,
                offset as off64_t,
            )
        };

        if res >= 0 {
            return Ok(res as usize);
        } else {
            let e = std::io::Error::last_os_error();
            // Retry if the IO is interrupted by signal.
            if e.kind() != ErrorKind::Interrupted {
                return Err(e);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::async_runtime::block_on;
    use tempfile::TempDir;

    #[test]
    fn test_new_async_file() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf().join("test.txt");
        std::fs::write(&path, b"test").unwrap();

        let file = block_on(async { File::async_open(&path, false, false).await.unwrap() });
        assert!(file.as_raw_fd() >= 0);
        drop(file);
    }

    #[test]
    fn test_from_std_file() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf().join("test.txt");
        std::fs::write(&path, b"test").unwrap();

        let file = File::from_std_file(std::fs::File::open(&path).unwrap());
        assert!(file.as_raw_fd() >= 0);
        let md = file.metadata().unwrap();
        assert!(md.is_file());

        block_on(async {
            let mut buffer = [0u8; 4];
            let buf = unsafe { FileVolatileBuf::new(&mut buffer) };
            let (res, buf) = file.async_read_at(buf, 0).await;
            assert_eq!(res.unwrap(), 4);
            assert_eq!(buf.len(), 4);
            assert_eq!(&buffer, b"test");
        });
    }

    #[test]
    fn test_async_file_metadata() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf();
        std::fs::write(path.join("test.txt"), b"test").unwrap();
        let file = block_on(async {
            File::async_open(path.join("test.txt"), false, false)
                .await
                .unwrap()
        });

        let md = file.metadata().unwrap();
        assert!(md.is_file());
        let md = file.metadata().unwrap();
        assert!(md.is_file());

        drop(file);
    }

    #[test]
    fn test_async_read_at() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf();
        std::fs::write(path.join("test.txt"), b"test").unwrap();

        block_on(async {
            let file = File::async_open(path.join("test.txt"), false, false)
                .await
                .unwrap();

            let mut buffer = [0u8; 3];
            let buf = unsafe { FileVolatileBuf::new(&mut buffer) };
            let (res, buf) = file.async_read_at(buf, 0).await;
            assert_eq!(res.unwrap(), 3);
            assert_eq!(buf.len(), 3);
            let buf = unsafe { FileVolatileBuf::new(&mut buffer) };
            let (res, buf) = file.async_read_at(buf, 2).await;
            assert_eq!(res.unwrap(), 2);
            assert_eq!(buf.len(), 2);
        });
    }

    #[test]
    fn test_async_readv_at() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf();
        std::fs::write(path.join("test.txt"), b"test").unwrap();

        block_on(async {
            let file = File::async_open(path.join("test.txt"), false, false)
                .await
                .unwrap();

            let mut buffer = [0u8; 3];
            let buf = unsafe { FileVolatileBuf::new(&mut buffer) };
            let mut buffer2 = [0u8; 3];
            let buf2 = unsafe { FileVolatileBuf::new(&mut buffer2) };
            let bufs = vec![buf, buf2];
            let (res, bufs) = file.async_readv_at(bufs, 0).await;

            assert_eq!(res.unwrap(), 4);
            assert_eq!(bufs[0].len(), 3);
            assert_eq!(bufs[1].len(), 1);
        });
    }

    #[test]
    fn test_async_write_at() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf();

        block_on(async {
            let file = File::async_open(path.join("test.txt"), true, true)
                .await
                .unwrap();

            let buffer = b"test";
            let buf = unsafe {
                FileVolatileBuf::from_raw_ptr(
                    buffer.as_ptr() as *mut u8,
                    buffer.len(),
                    buffer.len(),
                )
            };
            let (res, buf) = file.async_write_at(buf, 0).await;
            assert_eq!(res.unwrap(), 4);
            assert_eq!(buf.len(), 4);

            let res = std::fs::read_to_string(path.join("test.txt")).unwrap();
            assert_eq!(&res, "test");
        });
    }

    #[test]
    fn test_async_writev_at() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf();

        block_on(async {
            let file = File::async_open(path.join("test.txt"), true, true)
                .await
                .unwrap();

            let buffer = b"tes";
            let buf = unsafe {
                FileVolatileBuf::from_raw_ptr(
                    buffer.as_ptr() as *mut u8,
                    buffer.len(),
                    buffer.len(),
                )
            };
            let buffer2 = b"t";
            let buf2 = unsafe {
                FileVolatileBuf::from_raw_ptr(
                    buffer2.as_ptr() as *mut u8,
                    buffer2.len(),
                    buffer2.len(),
                )
            };
            let bufs = vec![buf, buf2];
            let (res, bufs) = file.async_writev_at(bufs, 0).await;

            assert_eq!(res.unwrap(), 4);
            assert_eq!(bufs[0].len(), 3);
            assert_eq!(bufs[1].len(), 1);

            let res = std::fs::read_to_string(path.join("test.txt")).unwrap();
            assert_eq!(&res, "test");
        });
    }

    #[test]
    fn test_borrow_fd() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf().join("test.txt");
        std::fs::write(&path, b"test").unwrap();

        // `owner` keeps the descriptor valid while the borrowed file lives.
        let mut owner = std::fs::File::open(&path).unwrap();
        let file = File::borrow_fd(owner.as_raw_fd(), Arc::new(()));

        block_on(async {
            let mut buffer = [0u8; 4];
            let buf = unsafe { FileVolatileBuf::new(&mut buffer) };
            let (res, buf) = file.async_read_at(buf, 0).await;
            assert_eq!(res.unwrap(), 4);
            assert_eq!(buf.len(), 4);
            assert_eq!(&buffer, b"test");
        });

        // Dropping the borrowed file must not close the descriptor.
        drop(file);
        let mut buffer = [0u8; 4];
        assert_eq!(std::io::Read::read(&mut owner, &mut buffer).unwrap(), 4);
        assert_eq!(&buffer, b"test");
    }

    #[test]
    fn test_async_try_clone() {
        let dir = TempDir::new().unwrap();
        let path = dir.path().to_path_buf();

        block_on(async {
            let file = File::async_open(path.join("test.txt"), true, true)
                .await
                .unwrap();

            let file2 = file.async_try_clone().await.unwrap();
            drop(file);

            let buffer = b"test";
            let buf = unsafe {
                FileVolatileBuf::from_raw_ptr(
                    buffer.as_ptr() as *mut u8,
                    buffer.len(),
                    buffer.len(),
                )
            };
            let (res, buf) = file2.async_write_at(buf, 0).await;
            assert_eq!(res.unwrap(), 4);
            assert_eq!(buf.len(), 4);
        });
    }
}
