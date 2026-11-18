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
        /// Whether IO on the descriptor goes through io_uring. Resolved from
        /// the runtime type when the descriptor is borrowed, see `borrow_fd()`.
        io_uring: bool,
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
        // Resolve the IO engine once, here, instead of on every IO: the
        // runtime type is fixed on first use, and reading it now fixes it,
        // so per-request lookups would return the same answer.
        #[cfg(target_os = "linux")]
        let io_uring = matches!(*RUNTIME_TYPE, RuntimeType::Uring);
        #[cfg(not(target_os = "linux"))]
        let io_uring = false;

        File::Borrowed {
            fd,
            io_uring,
            _guard: guard,
        }
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
            File::Borrowed { fd, _guard, .. } => {
                #[cfg(target_os = "linux")]
                if self.uses_io_uring() {
                    return uring_borrowed::read_at(*fd, _guard, buf, offset).await;
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
            File::Borrowed { fd, _guard, .. } => {
                #[cfg(target_os = "linux")]
                if self.uses_io_uring() {
                    return uring_borrowed::readv_at(*fd, _guard, bufs, offset).await;
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
            File::Uring(f) => f.write_at(buf, offset).submit().await,
            File::Borrowed { fd, _guard, .. } => {
                #[cfg(target_os = "linux")]
                if self.uses_io_uring() {
                    return uring_borrowed::write_at(*fd, _guard, buf, offset).await;
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
            File::Borrowed { fd, _guard, .. } => {
                #[cfg(target_os = "linux")]
                if self.uses_io_uring() {
                    return uring_borrowed::writev_at(*fd, _guard, bufs, offset).await;
                }
                let res = pwritev(*fd, &bufs, offset);
                (res, bufs)
            }
        }
    }

    /// Whether IO on this file goes through io_uring rather than blocking syscalls.
    ///
    /// For a borrowed descriptor, this is what `borrow_fd()` resolved from the
    /// runtime type when the descriptor was borrowed.
    pub(crate) fn uses_io_uring(&self) -> bool {
        match self {
            File::Tokio(_) => false,
            #[cfg(target_os = "linux")]
            File::Uring(_) => true,
            File::Borrowed { io_uring, .. } => *io_uring,
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
            File::Borrowed {
                fd,
                io_uring,
                _guard,
            } => Ok(File::Borrowed {
                fd: *fd,
                io_uring: *io_uring,
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

/// io_uring reads and writes on a borrowed descriptor.
///
/// A `tokio_uring::fs::File` would close the descriptor when dropped, and
/// forgetting it instead leaks the `Rc` it allocates, so these submit the
/// operations to tokio-uring directly. Each operation keeps its buffers, its
/// iovecs and the descriptor's guard until the kernel completes it, even if
/// its future is dropped first.
#[cfg(target_os = "linux")]
mod uring_borrowed {
    use std::any::Any;
    use std::io;
    use std::marker::PhantomData;
    use std::os::unix::io::RawFd;
    use std::sync::Arc;

    use io_uring::{cqueue, opcode, squeue, types};
    use tokio_uring::buf::{IoBuf, IoBufMut};
    use tokio_uring::{OneshotOutputTransform, UnsubmittedOneshot};

    use super::mark_filled;
    use crate::file_buf::FileVolatileBuf;

    /// What an operation keeps alive until it completes.
    struct Data<B> {
        bufs: B,
        _iovecs: Vec<libc::iovec>,
        _guard: Arc<dyn Any>,
    }

    /// Gives the buffers back with the result.
    struct Complete<B>(PhantomData<B>);

    impl<B> OneshotOutputTransform for Complete<B> {
        type Output = (io::Result<usize>, B);
        type StoredData = Data<B>;

        fn transform_oneshot_output(self, data: Data<B>, cqe: cqueue::Entry) -> Self::Output {
            let res = cqe.result();
            if res < 0 {
                (Err(io::Error::from_raw_os_error(-res)), data.bufs)
            } else {
                (Ok(res as usize), data.bufs)
            }
        }
    }

    async fn submit<B: Unpin + 'static>(
        sqe: squeue::Entry,
        bufs: B,
        iovecs: Vec<libc::iovec>,
        guard: &Arc<dyn Any>,
    ) -> (io::Result<usize>, B) {
        let data = Data {
            bufs,
            _iovecs: iovecs,
            _guard: guard.clone(),
        };
        UnsubmittedOneshot::new(data, Complete(PhantomData), sqe)
            .submit()
            .await
    }

    pub(super) async fn read_at(
        fd: RawFd,
        guard: &Arc<dyn Any>,
        mut buf: FileVolatileBuf,
        offset: u64,
    ) -> (io::Result<usize>, FileVolatileBuf) {
        let sqe = opcode::Read::new(
            types::Fd(fd),
            buf.stable_mut_ptr(),
            buf.bytes_total() as u32,
        )
        .offset(offset)
        .build();
        let (res, mut buf) = submit(sqe, buf, Vec::new(), guard).await;
        if let Ok(n) = res {
            // Safe because the kernel wrote `n` bytes from the start of the buffer.
            unsafe { buf.set_init(n) };
        }
        (res, buf)
    }

    pub(super) async fn readv_at(
        fd: RawFd,
        guard: &Arc<dyn Any>,
        bufs: Vec<FileVolatileBuf>,
        offset: u64,
    ) -> (io::Result<usize>, Vec<FileVolatileBuf>) {
        let iovecs: Vec<libc::iovec> = bufs
            .iter()
            .map(|b| {
                let slice = b.io_slice_mut();
                libc::iovec {
                    iov_base: slice.as_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                }
            })
            .collect();
        let sqe = opcode::Readv::new(types::Fd(fd), iovecs.as_ptr(), iovecs.len() as u32)
            .offset(offset)
            .build();
        let (res, mut bufs) = submit(sqe, bufs, iovecs, guard).await;
        if let Ok(n) = res {
            mark_filled(&mut bufs, n);
        }
        (res, bufs)
    }

    pub(super) async fn write_at(
        fd: RawFd,
        guard: &Arc<dyn Any>,
        buf: FileVolatileBuf,
        offset: u64,
    ) -> (io::Result<usize>, FileVolatileBuf) {
        let sqe = opcode::Write::new(types::Fd(fd), buf.stable_ptr(), buf.bytes_init() as u32)
            .offset(offset)
            .build();
        submit(sqe, buf, Vec::new(), guard).await
    }

    pub(super) async fn writev_at(
        fd: RawFd,
        guard: &Arc<dyn Any>,
        bufs: Vec<FileVolatileBuf>,
        offset: u64,
    ) -> (io::Result<usize>, Vec<FileVolatileBuf>) {
        let iovecs: Vec<libc::iovec> = bufs
            .iter()
            .map(|b| {
                let slice = b.io_slice();
                libc::iovec {
                    iov_base: slice.as_ptr() as *mut libc::c_void,
                    iov_len: slice.len(),
                }
            })
            .collect();
        let sqe = opcode::Writev::new(types::Fd(fd), iovecs.as_ptr(), iovecs.len() as u32)
            .offset(offset)
            .build();
        submit(sqe, bufs, iovecs, guard).await
    }
}

/// The most buffers one `preadv()` or `pwritev()` call accepts.
#[cfg(target_os = "linux")]
const IOV_MAX: usize = libc::UIO_MAXIOV as usize;
/// The most buffers one `preadv()` or `pwritev()` call accepts.
#[cfg(target_os = "macos")]
const IOV_MAX: usize = libc::IOV_MAX as usize;
/// The most buffers one `preadv()` or `pwritev()` call accepts. FreeBSD's
/// sys/uio.h caps iovec counts at UIO_MAXIOV (1024), which libc does not
/// expose as a constant.
#[cfg(target_os = "freebsd")]
const IOV_MAX: usize = 1024;

/// Transfer `chunks` in order with one call of `io` each, and return the total count. Each
/// chunk comes with its full length, and `io` gets the file offset of the chunk. It stops after
/// a short transfer. Like a single call, it returns the count transferred so far if a later call
/// fails.
fn transfer_chunks<C>(
    chunks: impl Iterator<Item = (C, usize)>,
    offset: u64,
    mut io: impl FnMut(C, u64) -> std::io::Result<usize>,
) -> std::io::Result<usize> {
    let mut count = 0;
    for (chunk, len) in chunks {
        match io(chunk, offset + count as u64) {
            Ok(n) => {
                count += n;
                if n < len {
                    break;
                }
            }
            Err(_) if count > 0 => break,
            Err(e) => return Err(e),
        }
    }
    Ok(count)
}

/// A simple wrapper over posix `preadv` to deal with `FileVolatileBuf`.
///
/// It fills the buffers in order and sets their sizes. With more than `IOV_MAX` buffers, it
/// calls `preadv` once per `IOV_MAX` buffers, and stops after a short read. Like a single call,
/// it returns the count read so far if a later call fails.
pub fn preadv(fd: RawFd, bufs: &mut [FileVolatileBuf], offset: u64) -> std::io::Result<usize> {
    let chunks = bufs.chunks_mut(IOV_MAX).map(|chunk| {
        let space = chunk.iter().map(|b| b.cap() - b.len()).sum();
        (chunk, space)
    });
    transfer_chunks(chunks, offset, |chunk, offset| {
        preadv_once(fd, chunk, offset)
    })
}

/// Mark the `count` bytes a vectored read put into `bufs`, buffer by buffer.
fn mark_filled(bufs: &mut [FileVolatileBuf], mut count: usize) {
    for buf in bufs.iter_mut() {
        let cnt = std::cmp::min(count, buf.cap() - buf.len());
        unsafe { buf.set_size(buf.len() + cnt) };
        count -= cnt;
        if count == 0 {
            break;
        }
    }
    assert_eq!(count, 0);
}

fn preadv_once(fd: RawFd, bufs: &mut [FileVolatileBuf], offset: u64) -> std::io::Result<usize> {
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
            mark_filled(bufs, res as usize);
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
///
/// It writes the data of the buffers in order. With more than `IOV_MAX` buffers, it calls
/// `pwritev` once per `IOV_MAX` buffers, and stops after a short write. Like a single call,
/// it returns the count written so far if a later call fails.
pub fn pwritev(fd: RawFd, bufs: &[FileVolatileBuf], offset: u64) -> std::io::Result<usize> {
    let chunks = bufs
        .chunks(IOV_MAX)
        .map(|chunk| (chunk, chunk.iter().map(|b| b.len()).sum()));
    transfer_chunks(chunks, offset, |chunk, offset| {
        pwritev_once(fd, chunk, offset)
    })
}

fn pwritev_once(fd: RawFd, bufs: &[FileVolatileBuf], offset: u64) -> std::io::Result<usize> {
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

    #[cfg(target_os = "linux")]
    #[test]
    fn test_borrowed_fd_uring_read_keeps_guard_after_drop() {
        use std::future::Future;
        use std::task::Poll;

        let mut fds = [0; 2];
        assert_eq!(unsafe { libc::pipe(fds.as_mut_ptr()) }, 0);
        let rd = unsafe { std::fs::File::from_raw_fd(fds[0]) };
        let wr = unsafe { std::fs::File::from_raw_fd(fds[1]) };
        let guard = Arc::new(());
        let file = File::borrow_fd(rd.as_raw_fd(), guard.clone());
        let writer = File::borrow_fd(wr.as_raw_fd(), Arc::new(()));
        if !file.uses_io_uring() {
            return;
        }
        let mut mem = [0u8; 4];

        block_on(async {
            // The pipe is empty, so the read stays in flight.
            let mut read =
                Box::pin(file.async_read_at(unsafe { FileVolatileBuf::new(&mut mem) }, 0));
            let pending =
                std::future::poll_fn(|cx| Poll::Ready(read.as_mut().poll(cx).is_pending()));
            assert!(pending.await);
            drop(read);
            assert_eq!(Arc::strong_count(&guard), 3);

            // Once the kernel completes the read, the runtime drops the guard. The
            // runtime reaps completions while it waits for the writes.
            for _ in 0..1000 {
                let mut data = *b"test";
                let buf = unsafe { FileVolatileBuf::new_with_data(&mut data, 4) };
                assert_eq!(writer.async_write_at(buf, 0).await.0.unwrap(), 4);
                if Arc::strong_count(&guard) == 2 {
                    break;
                }
            }
            assert_eq!(Arc::strong_count(&guard), 2);
        });
        assert_eq!(&mem, b"test");
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
