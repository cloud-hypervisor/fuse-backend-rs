// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Utility traits and structs to support rust async io.

use std::cell::RefCell;
use std::ffi::CStr;
use std::future::Future;
use std::io;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::os::unix::io::RawFd;
use std::pin::Pin;
use std::sync::{
    atomic::{AtomicU32, Ordering},
    Arc, Mutex,
};
use std::task::{Context, Poll};
use std::time::Duration;

use futures::{
    executor::LocalPool,
    ready,
    task::{LocalSpawnExt, SpawnError},
};
use iou::{CompletionQueue, IoUring, Registrar, SQEs, SetupFeatures, SetupFlags, SubmissionQueue};
use nix::{
    fcntl::{FallocateFlags, OFlag},
    sys::stat::{mode_t, Mode},
};
use ringbahn::{
    drive::{complete, Completion},
    event::{Fallocate, Fsync, OpenAt, Read, ReadVectored, Write, WriteVectored},
    Drive,
};

use iou::sqe::FsyncFlags;
use vm_memory::VolatileSlice;

pub use ringbahn::Submission;

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
        let mode = mode.ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;
        let flags = OFlag::from_bits(flags);
        let flags = flags.ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        let event = OpenAt {
            path: pathname.to_owned(),
            dir_fd: dfd,
            flags,
            mode,
        };
        let (_event, result) = Submission::new(event, drive).await;

        result
    }

    /// Asynchronously fsync on a file descriptor `fd`.
    pub async fn fsync(drive: D, fd: i32, datasync: bool) -> io::Result<()> {
        let flags = if datasync {
            FsyncFlags::FSYNC_DATASYNC
        } else {
            FsyncFlags::empty()
        };

        let event = Fsync { fd, flags };
        let (_event, result) = Submission::new(event, drive).await;

        result.map(|_| ())
    }

    /// Asynchronously fallocate on a file descriptor.
    pub async fn fallocate(
        drive: D,
        fd: i32,
        offset: u64,
        size: u64,
        flags: u32,
    ) -> io::Result<()> {
        let flags = FallocateFlags::from_bits(flags as i32);
        let flags = flags.ok_or_else(|| io::Error::from_raw_os_error(libc::EINVAL))?;

        let event = Fallocate {
            fd,
            offset,
            size,
            flags,
        };
        let (_event, result) = Submission::new(event, drive).await;

        result.map(|_| ())
    }

    /// Asynchronously read data into buffer from the file.
    pub async fn read(drive: D, fd: RawFd, data: &mut [u8], offset: u64) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let buf = unsafe { Box::from_raw(data as *const [u8] as *mut [u8]) };

        let event = Read { fd, buf, offset };
        let (Read { buf, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake [Box<[u8]> object, otherwise it will cause double-free.
        std::mem::forget(buf);

        result.map(|v| v as usize)
    }

    /// Asynchronously read from the file into vectored data buffers.
    pub async fn read_vectored<T>(
        drive: D,
        fd: RawFd,
        bufs: &mut [T],
        offset: u64,
    ) -> io::Result<usize>
    where
        T: DerefMut<Target = [u8]>,
    {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs: Vec<Box<[u8]>> = bufs
            .iter_mut()
            .filter(|b| !b.is_empty())
            .map(|b| unsafe { Box::from_raw(b.deref_mut()) })
            .collect();
        let bufs = bufs.into();

        let event = ReadVectored { fd, bufs, offset };
        let (ReadVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake Box<[Box<[u8]>> object, otherwise it will cause double-free.
        let mut vec: Vec<Box<[u8]>> = bufs.into();
        unsafe { vec.set_len(0) };

        result.map(|v| v as usize)
    }

    /// Asynchronously read from the file into vectored data buffers.
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
        std::mem::forget(buf);

        result.map(|v| v as usize)
    }

    /// Asynchronously write out two data buffers to the file.
    pub async fn write2(
        drive: D,
        fd: RawFd,
        data: &[u8],
        data2: &[u8],
        offset: u64,
    ) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs = [
            unsafe { Box::from_raw(data as *const [u8] as *mut [u8]) },
            unsafe { Box::from_raw(data2 as *const [u8] as *mut [u8]) },
        ];
        let bufs = bufs.to_vec().into_boxed_slice();

        let event = WriteVectored { fd, bufs, offset };
        let (WriteVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake [Box<[u8]> object, otherwise it will cause double-free.
        std::mem::forget(bufs);

        result.map(|v| v as usize)
    }

    /// Asynchronously write out three data buffers to the file.
    pub async fn write3(
        drive: D,
        fd: RawFd,
        data: &[u8],
        data2: &[u8],
        data3: &[u8],
        offset: u64,
    ) -> io::Result<usize> {
        // Safe because we just transform the interface to access the underlying data buffers.
        let bufs = [
            unsafe { Box::from_raw(data as *const [u8] as *mut [u8]) },
            unsafe { Box::from_raw(data2 as *const [u8] as *mut [u8]) },
            unsafe { Box::from_raw(data3 as *const [u8] as *mut [u8]) },
        ];
        let bufs = bufs.to_vec().into_boxed_slice();

        let event = WriteVectored { fd, bufs, offset };
        let (WriteVectored { bufs, .. }, result) = Submission::new(event, drive).await;

        // Manually tear down the fake [Box<[u8]> object, otherwise it will cause double-free.
        std::mem::forget(bufs);

        result.map(|v| v as usize)
    }

    /// Asynchronously write out vectored data buffers to the file.
    pub async fn write_vectored<T>(
        drive: D,
        fd: RawFd,
        bufs: &[T],
        offset: u64,
    ) -> io::Result<usize>
    where
        T: Deref<Target = [u8]>,
    {
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

thread_local! {
    static ASYNC_EXECUTOR: RefCell<Option<AsyncDriver>> = RefCell::new(None);
}

/// Asynchronous IO driver to support the `ringbahn` async io framework.
#[derive(Clone)]
pub struct AsyncDriver {
    sq: Arc<Mutex<SubmissionQueue<'static>>>,
}

impl AsyncDriver {
    fn poll_submit_inner(sq: &mut SubmissionQueue<'_>) -> Poll<io::Result<u32>> {
        loop {
            match sq.submit() {
                Ok(n) => return Poll::Ready(Ok(n)),
                Err(err) => {
                    if err.raw_os_error().map_or(false, |code| code == libc::EBUSY) {
                        // Rest for a while waiting for kernel to handle pending io_uring requests.
                        std::thread::sleep(Duration::from_micros(1));
                    } else {
                        return Poll::Ready(Err(err));
                    }
                }
            }
        }
    }
}

impl Drive for AsyncDriver {
    fn poll_prepare<'cx>(
        self: Pin<&mut Self>,
        ctx: &mut Context<'cx>,
        count: u32,
        prepare: impl FnOnce(SQEs<'_>, &mut Context<'cx>) -> Completion<'cx>,
    ) -> Poll<Completion<'cx>> {
        let mut sq = self.sq.lock().unwrap();

        loop {
            match sq.prepare_sqes(count) {
                Some(sqs) => return Poll::Ready(prepare(sqs, ctx)),
                None => {
                    let _ = ready!(Self::poll_submit_inner(&mut *sq));
                }
            }
        }
    }

    fn poll_submit(self: Pin<&mut Self>, _ctx: &mut Context<'_>) -> Poll<std::io::Result<u32>> {
        let mut sq = self.sq.lock().unwrap();

        Self::poll_submit_inner(&mut *sq)
    }
}

impl Default for AsyncDriver {
    fn default() -> Self {
        ASYNC_EXECUTOR.with(|driver| {
            // AsyncExecutor::setup() must be called to initialize the driver.
            driver.borrow().as_ref().unwrap().clone()
        })
    }
}

/// Single-threaded asynchronous IO executor based on Linux io_uring.
#[allow(dead_code)]
pub struct AsyncExecutor {
    executor: LocalPool,
    ring: *const IoUring,
    sq: Arc<Mutex<SubmissionQueue<'static>>>,
    cq: CompletionQueue<'static>,
    reg: Registrar<'static>,
}

impl AsyncExecutor {
    /// Create a new asynchronous IO executor.
    pub fn new(entries: u32) -> Self {
        let flags = SetupFlags::empty();
        let features = SetupFeatures::NODROP;
        let ring = Box::new(IoUring::new_with_flags(entries, flags, features).unwrap());
        let ring = Box::leak(ring);
        let ring_ptr = ring as *const IoUring;
        let (sq, cq, reg) = ring.queues();

        AsyncExecutor {
            executor: LocalPool::new(),
            ring: ring_ptr,
            sq: Arc::new(Mutex::new(sq)),
            cq,
            reg,
        }
    }

    /// Initialize thread local variable `ASYNC_EXECUTOR`.
    pub fn setup(&self) -> std::io::Result<()> {
        ASYNC_EXECUTOR.with(|driver| {
            let mut val = driver.borrow_mut();
            if val.is_some() {
                Err(std::io::Error::from_raw_os_error(libc::EBUSY))
            } else {
                *val = Some(self.driver());
                Ok(())
            }
        })
    }

    /// Get an instance of `AsyncDriver`.
    pub fn driver(&self) -> AsyncDriver {
        AsyncDriver {
            sq: self.sq.clone(),
        }
    }

    /// Spawns a future that will be run to completion.
    pub fn spawn<Fut>(&self, future: Fut) -> Result<(), SpawnError>
    where
        Fut: Future<Output = ()> + 'static,
    {
        self.executor.spawner().spawn_local(future)
    }

    /// Execute the asynchronous io loop once.
    pub fn run_once(&mut self, wait_for_io_uring: bool) -> std::io::Result<()> {
        // Wait for at least one completion descriptor.
        if wait_for_io_uring {
            self.cq.wait(1)?;
        }

        // Handle all pending completion descriptors.
        while let Some(cqe) = self.cq.peek_for_cqe() {
            complete(cqe);
        }

        // Poll all pending Futures.
        self.executor.run_until_stalled();

        Ok(())
    }
}

impl Drop for AsyncExecutor {
    fn drop(&mut self) {
        // One reference for ASYNC_EXECUTOR, another for self.sq
        assert_eq!(Arc::strong_count(&self.sq), 2);

        let _ring = unsafe { Box::from_raw(self.ring as *mut IoUring) };
    }
}

/// Struct to track asynchronous IO executor and task state.
#[derive(Clone)]
pub struct AsyncExecutorState(Arc<AtomicU32>);

impl Default for AsyncExecutorState {
    fn default() -> Self {
        Self::new()
    }
}

impl AsyncExecutorState {
    /// Create a new state object.

    pub fn new() -> Self {
        AsyncExecutorState(Arc::new(AtomicU32::new(0)))
    }

    /// Start to quiesce the executor/tasks.
    pub fn quiesce(&self) {
        let _ = self
            .0
            .compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst);
    }

    /// Check whether the executor is in quiescing state.
    pub fn quiescing(&self) -> bool {
        self.0.load(Ordering::Relaxed) != 0
    }

    /// Check whether the executor/tasks has been quiesced.
    pub fn quiesced(&self, cnt: u32) -> bool {
        cnt > 0 && self.0.load(Ordering::Relaxed) == cnt
    }

    /// Report that one instance has reached queisce state.
    pub fn report(&self) {
        self.0.fetch_add(1, Ordering::SeqCst);
    }

    /// Reset to default state.
    pub fn reset(&self) {
        self.0.store(0, Ordering::Release)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::io::{IoSlice, IoSliceMut, Read, Seek, Write};
    use std::os::unix::io::AsRawFd;

    use futures::executor::{block_on, ThreadPool};
    use futures::io::SeekFrom;
    use futures::task::SpawnExt;
    use ringbahn::drive::demo::DemoDriver;
    use vmm_sys_util::tempfile::TempFile;

    #[test]
    fn test_async_read() {}

    #[test]
    fn test_async_read_vectored() {
        let file = vmm_sys_util::tempfile::TempFile::new().unwrap();
        let buf = [
            0x1u8, 0x1u8, 0x2u8, 0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8, 0x1u8, 0x2u8,
            0x3u8, 0x4u8, 0x5u8, 0x6u8, 0x7u8, 0x8u8, 0x9u8,
        ];
        file.as_file().write(&buf).unwrap();
        let fd = file.as_file().as_raw_fd();

        let executor = ThreadPool::new().unwrap();

        let handle = executor
            .spawn_with_handle(async move {
                let mut bufs = [0u8; 18];

                let drive = DemoDriver::default();
                AsyncUtil::read_vectored(drive, fd, &mut [IoSliceMut::new(&mut bufs)], 1).await

                //task.await
            })
            .unwrap();
        let result = block_on(handle).unwrap();
        assert_eq!(result, 18);
    }

    #[test]
    fn test_async_write() {
        let file = vmm_sys_util::tempfile::TempFile::new().unwrap();
        let fd = file.as_file().as_raw_fd();
        let executor = ThreadPool::new().unwrap();

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
        let mut buf2 = [0x0u8; 19];
        file.as_file().seek(SeekFrom::Start(0)).unwrap();
        file.as_file().read(&mut buf2).unwrap();
        assert_eq!(buf, buf2[1..10]);
        assert_eq!(buf, buf2[10..=18]);
        assert_eq!(buf2[0], 0);
    }

    #[test]
    fn test_async_state() {
        let state = AsyncExecutorState::new();

        assert_eq!(state.quiescing(), false);
        assert_eq!(state.quiesced(0), false);

        state.quiesce();
        assert_eq!(state.quiescing(), true);
        assert_eq!(state.quiesced(3), false);

        state.report();
        assert_eq!(state.quiescing(), true);
        assert_eq!(state.quiesced(3), false);

        state.report();
        assert_eq!(state.quiescing(), true);
        assert_eq!(state.quiesced(3), true);

        state.reset();
        assert_eq!(state.quiescing(), false);
    }

    #[test]
    fn test_async_executor() {
        let file = TempFile::new().unwrap();
        let fd = file.as_file().as_raw_fd();
        let count = Arc::new(AtomicU32::new(0));
        let count1 = count.clone();
        let count2 = count.clone();

        let mut executor = AsyncExecutor::new(32);
        executor.setup().unwrap();

        let cb = || async move {
            let drive = AsyncDriver::default();
            let buf = [0x1u8, 0x2u8, 0x3u8, 0x4u8];
            AsyncUtil::write(drive, fd, &buf, 0).await.unwrap();
            count1.fetch_add(1, Ordering::SeqCst);
        };
        executor.spawn(cb()).unwrap();
        executor.run_once(false).unwrap();
        executor.run_once(true).unwrap();

        let drive = executor.driver();
        let cb = || async move {
            let buf = [0x1u8, 0x2u8, 0x3u8, 0x4u8];
            let mut buf2 = [0x0u8, 0x0u8, 0x0u8, 0x0u8];
            AsyncUtil::read(drive, fd, &mut buf2, 0).await.unwrap();
            assert_eq!(buf, buf2);
            count2.fetch_add(1, Ordering::SeqCst);
        };
        executor.spawn(cb()).unwrap();
        executor.run_once(false).unwrap();
        executor.run_once(true).unwrap();

        assert_eq!(count.load(Ordering::Acquire), 2);
    }
}
