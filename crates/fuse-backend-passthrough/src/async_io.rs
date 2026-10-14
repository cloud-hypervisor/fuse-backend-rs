// Copyright (C) 2021-2022 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Asynchronous IO support for `PassthroughFs`.
//!
//! READ and WRITE requests are served with native asynchronous IO: the data
//! is transferred directly between the transport buffer and the backing file
//! through the runtime's asynchronous file interface (io_uring when
//! available), without going through the blocking synchronous handlers.
//! Two classes of requests are exceptions and relayed to the synchronous
//! handlers instead: O_DIRECT requests, whose alignment constraints the
//! transport buffer can't satisfy (the synchronous handler stages them
//! through a page-aligned bounce buffer), and WRITE_KILL_PRIV requests,
//! whose CAP_FSETID handling must not span an `.await` point.
//!
//! The remaining operations are relayed to the synchronous handlers, which
//! execute blocking syscalls. By default they run inline in the context of
//! the asynchronous runtime, which is single-threaded: a blocking syscall
//! stalls the processing of all other requests. Calling
//! `PassthroughFs::enable_async_thread_pool(true)` instead offloads them to
//! the runtime's blocking thread pool, so the async task can keep receiving
//! and dispatching requests while the syscalls execute in parallel on pool
//! threads.
//!
//! The thread pool also serves READ and WRITE when their IO would block the
//! runtime thread. These are the relayed READ and WRITE requests, and on the
//! tokio runtime also READ cache misses and every WRITE. A pool thread runs
//! the synchronous handler on its own copy of the data, see `read_on_pool()`
//! and `write_on_pool()`.
//!
//! # Runtime requirement
//!
//! The native asynchronous IO path must be driven by this crate's async
//! `Runtime` (`fuse_backend_core::async_runtime`). On Linux with io_uring,
//! the default, that is a tokio-uring runtime, whose operations panic when
//! polled outside its context. So on another executor, such as a plain tokio
//! runtime, the first native WRITE or READ cache miss panics. Serve the
//! filesystem with a transport that drives this crate's `Runtime`, as
//! `AsyncFuseServing` does, or choose the tokio runtime with
//! `async_runtime::set_runtime_type()` or `FUSE_BACKEND_RS_ASYNC_RUNTIME=tokio`.
//! Its `preadv`/`pwritev` calls work in any runtime context, but block the
//! runtime thread on cache misses unless the thread pool is enabled.

use std::future::Future;
use std::io;
use std::pin::Pin;

use async_trait::async_trait;

use super::util::stat_fd;
use super::*;
use fuse_backend_core::abi::fuse_abi::{
    CreateIn, Opcode, OpenOptions, SetattrValid, WRITE_KILL_PRIV,
};
use fuse_backend_core::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, FileSystem, ZeroCopyReader,
    ZeroCopyWriter,
};
use fuse_backend_core::async_file::File as AsyncFile;
use fuse_backend_core::async_runtime::{self, Runtime};
use fuse_backend_core::buffer::pagesize;
use fuse_backend_core::file_buf::FileVolatileSlice;
use fuse_backend_core::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    /// Create a Passthrough file system instance shared between threads.
    ///
    /// A shared instance can offload its synchronous handlers to the
    /// blocking thread pool, see `enable_async_thread_pool()`. A file
    /// system created with `PassthroughFs::new()` always serves its async
    /// requests inline.
    pub fn new_shared(cfg: Config) -> io::Result<Arc<Self>> {
        let mut fs = Self::new(cfg)?;

        Ok(Arc::new_cyclic(|weak| {
            fs.shared_ref = weak.clone();
            fs
        }))
    }

    /// Enable or disable offloading the synchronous handlers to the
    /// runtime's blocking thread pool.
    ///
    /// When disabled (the default), the asynchronous handlers execute the
    /// synchronous handlers inline in the context of the asynchronous
    /// runtime. When enabled, the synchronous handlers are offloaded to the
    /// runtime's blocking thread pool instead, so the async task can keep
    /// receiving and dispatching requests while the blocking syscalls
    /// execute in parallel on pool threads. Note that the offloading
    /// requires the file system to be created with `new_shared()`,
    /// requests of other instances are served inline.
    ///
    /// The blocking pool is a tokio runtime property configured when the
    /// runtime is created, this method only selects between the two modes
    /// of operation.
    ///
    /// When enabled, `async_read()` and `async_write()` also use the pool for
    /// requests that would otherwise block the runtime thread. These are the
    /// O_DIRECT and WRITE_KILL_PRIV requests, which they relay to the
    /// synchronous handlers, and on the tokio runtime also READ cache misses
    /// and every WRITE. On a file system without `RWF_NOWAIT`, such as tmpfs,
    /// overlayfs or FUSE, every READ counts as a cache miss. Pool threads
    /// can't access the transport buffers, so the data takes one more copy.
    /// With io_uring, cache misses and WRITE requests stay on native
    /// asynchronous IO.
    ///
    /// If a request future is dropped, for example for a takeover, a request
    /// that no pool thread has started yet doesn't run. One that already runs
    /// completes, and the kernel may send it again after the takeover. So a
    /// WRITE to a file opened with `O_APPEND` can land twice. To avoid that,
    /// stop the serving task through its state flag, which answers the
    /// requests in flight before it returns.
    pub fn enable_async_thread_pool(&self, enable: bool) {
        self.async_thread_pool_enabled
            .store(enable, Ordering::Relaxed);
    }

    /// Create an asynchronous file object for the file referenced by a
    /// handle, to serve READ/WRITE requests with native asynchronous IO.
    ///
    /// The fd of the handle is borrowed for the duration of the IO: the
    /// asynchronous file object holds a reference to the handle data, which
    /// keeps the descriptor valid until the request completes, even if the
    /// handle is released in the meantime. This avoids the `dup()`/`close()`
    /// syscall pair of owning an independent descriptor per request.
    // The asynchronous IO engine (io_uring) is bound to the thread polling
    // it, so asynchronous file objects are neither `Send` nor `Sync`; they
    // are only used within the single-threaded async runtime context.
    #[allow(clippy::arc_with_non_send_sync)]
    fn async_file_from_data(
        &self,
        data: &Arc<HandleData>,
        flags: u32,
    ) -> io::Result<Arc<dyn AsyncFileReadWriteVolatile>> {
        let fd = data.borrow_fd().as_raw_fd();
        // Reconcile the O_DIRECT flag of the shared file description before
        // the request is served with native asynchronous IO. The guard is
        // dropped right away instead of being held over the IO like the
        // synchronous handlers do: the zero-copy future must stay `Send`,
        // and the asynchronous engines submit with the flags in effect at
        // submission time.
        drop(self.ensure_file_flags(data, &data.borrow_fd(), flags)?);

        Ok(Arc::new(AsyncFile::borrow_fd(fd, data.clone())))
    }

    /// The shared file system to offload blocking handlers to, if the thread
    /// pool is enabled and the file system was created with `new_shared()`.
    fn pool_fs(&self) -> Option<Arc<Self>> {
        if self.async_thread_pool_enabled.load(Ordering::Relaxed) {
            self.shared_ref.upgrade()
        } else {
            None
        }
    }

    /// Try to serve a buffered READ request inline with `preadv2(RWF_NOWAIT)`,
    /// without going through the asynchronous IO engine.
    ///
    /// Returns the number of bytes served inline, and whether the remaining
    /// bytes need real IO (`true`) or the request is already complete
    /// (`false`: the whole size was served, EOF was reached, or the size was
    /// zero). On a miss the writer's position is left exactly after the bytes
    /// served inline, so the asynchronous fallback can continue from there.
    ///
    /// `RWF_NOWAIT` turns the cache-resident case -- the common one -- into a
    /// single inline syscall, avoiding the asynchronous submission/completion
    /// round trip that dominates the cost of instantly-completing requests.
    /// Cache-missing requests fail with `EAGAIN` instead of blocking and are
    /// handed to the native asynchronous path by the caller. Kernels or
    /// filesystems without `RWF_NOWAIT` support (`EINVAL`/`ENOSYS`/
    /// `EOPNOTSUPP`) degrade the same way, so the fast path never breaks
    /// correctness, it can only fail to engage.
    fn read_nowait(
        &self,
        data: &Arc<HandleData>,
        w: &mut (dyn AsyncZeroCopyWriter + Send),
        count: usize,
        mut offset: u64,
        flags: u32,
    ) -> io::Result<(usize, bool)> {
        let fd = data.borrow_fd();

        // Hold the guard over the inline reads, like the synchronous handler
        // does, so no other request can flip the O_DIRECT bit meanwhile.
        let _flags_guard = self.ensure_file_flags(data, &fd, flags)?;

        let mut file = NowaitFile { fd };
        let mut served = 0usize;
        while served < count {
            match w.write_from(&mut file, count - served, offset) {
                // EOF: the file is shorter than the request, nothing to relay.
                Ok(0) => return Ok((served, false)),
                Ok(n) => {
                    served += n;
                    offset += n as u64;
                }
                Err(e)
                    if matches!(
                        e.raw_os_error(),
                        Some(libc::EAGAIN)
                            | Some(libc::EINVAL)
                            | Some(libc::ENOSYS)
                            | Some(libc::EOPNOTSUPP)
                    ) =>
                {
                    return Ok((served, true));
                }
                Err(e) => return Err(e),
            }
        }

        Ok((served, false))
    }
}

// The pool closures own `Arc<Self>`, which needs `S: 'static`.
impl<S: BitmapSlice + Send + Sync + 'static> PassthroughFs<S> {
    /// Run `f` with `fs` and a copy of `ctx` on the blocking thread pool, and
    /// wait for its result.
    ///
    /// If this future is dropped before a pool thread starts `f`, for example
    /// when `FuseDevTask::poll_handler()` is dropped for a takeover, `f`
    /// doesn't run. The kernel sends the request again after a takeover, and
    /// a late run of the old copy could undo newer requests, such as a WRITE
    /// to the same range. If a pool thread already runs `f`, it finishes,
    /// like an io_uring operation that the kernel has already started.
    async fn run_on_pool<T, F>(fs: Arc<Self>, ctx: &Context, f: F) -> io::Result<T>
    where
        T: Send + 'static,
        F: FnOnce(Arc<Self>, Context) -> io::Result<T> + Send + 'static,
    {
        let ctx = ctx.clone();
        let mut task = AbortOnDrop(Runtime::spawn_blocking(move || f(fs, ctx)));
        join_blocking(&mut task.0).await
    }

    /// Like `run_on_pool()`, for a handler that creates state the kernel has
    /// to release, such as a lookup count or a handle. If this future is
    /// dropped while a pool thread runs `f`, nobody receives its result, and
    /// `undo` releases that state on whichever thread drops the result.
    async fn run_on_pool_undo<T, F, U>(fs: Arc<Self>, ctx: &Context, f: F, undo: U) -> io::Result<T>
    where
        T: Send + 'static,
        F: FnOnce(&Self, Context) -> io::Result<T> + Send + 'static,
        U: FnOnce(&Self, T) + Send + 'static,
    {
        Self::run_on_pool(fs, ctx, move |fs, ctx| {
            let value = f(&fs, ctx)?;
            Ok(Unclaimed(Some((value, move |value| undo(&fs, value)))))
        })
        .await
        .map(Unclaimed::claim)
    }

    /// Serve a READ with `do_read()` on the blocking thread pool, and copy
    /// the data into `w`.
    ///
    /// `w` writes into a transport buffer that the request owns, and nothing
    /// keeps that buffer alive after the request future is dropped, for
    /// example for a takeover. So the pool thread never sees `w`. It reads
    /// into a buffer that the closure owns and returns it through the
    /// `JoinHandle`. The runtime thread then copies it into `w`, while this
    /// future, and so `w`, is still alive. If the future is dropped first, a
    /// pool task that already runs reads into its own buffer and frees it,
    /// see `run_on_pool()`. `data`, the handle data that the caller looked
    /// up, keeps the file descriptor open until the read returns.
    ///
    /// The server doesn't bound the size of a READ, so a READ larger than the
    /// room in `w` fails before the pool task allocates for it, as the
    /// transports' writers would fail it.
    async fn read_on_pool(
        fs: Arc<Self>,
        ctx: &Context,
        data: Arc<HandleData>,
        w: &mut (dyn AsyncZeroCopyWriter + Send),
        size: u32,
        offset: u64,
        flags: u32,
    ) -> io::Result<usize> {
        if size as usize > w.available_bytes() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!(
                    "data out of range, available {} requested {}",
                    w.available_bytes(),
                    size
                ),
            ));
        }
        let buf = Self::run_on_pool(fs, ctx, move |fs, _ctx| {
            let mut buf = PoolBuf::new(size as usize)?;
            fs.do_read(&data, &mut buf, size, offset, flags, true)?;
            Ok(buf)
        })
        .await?;
        w.write_all(buf.data())?;
        Ok(buf.len)
    }

    /// Copy the payload of a WRITE out of `r`, and serve the WRITE with
    /// `do_write()` on the blocking thread pool.
    ///
    /// The copy runs on the runtime thread before the pool task starts, so
    /// the pool thread never accesses the transport buffer behind `r`, which
    /// the request owns, see `read_on_pool()`. If this future is dropped
    /// before a pool thread starts the WRITE, it doesn't run, and one that
    /// already runs finishes, see `run_on_pool()`.
    #[allow(clippy::too_many_arguments)]
    async fn write_on_pool(
        fs: Arc<Self>,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        r: &mut (dyn AsyncZeroCopyReader + Send),
        size: u32,
        offset: u64,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<usize> {
        let mut buf = PoolBuf::new(size as usize)?;
        r.read_to(&mut PayloadSink(&mut buf), size as usize, 0)?;
        Self::run_on_pool(fs, ctx, move |fs, _ctx| {
            let data = fs.get_data(handle, inode, libc::O_RDWR)?;
            fs.do_write(&data, &mut buf, size, offset, flags, fuse_flags, true)
        })
        .await
    }
}

// `BackendFileSystem` is implemented for `Arc<FS>` by a blanket impl in
// `fuse-backend_core::api::filesystem`, so a shared instance created with
// `new_shared()` can be mounted to a `Vfs` directly; `as_any()` exposes the
// wrapped instance, keeping downcasts identical for both forms.

/// Await the result of a task offloaded to the blocking thread pool.
///
/// Panics of the blocking task are propagated, a cancelled task is reported
/// as an `Other` io error.
async fn join_blocking<T>(handle: &mut tokio::task::JoinHandle<io::Result<T>>) -> io::Result<T> {
    match handle.await {
        Ok(res) => res,
        Err(e) if e.is_panic() => std::panic::resume_unwind(e.into_panic()),
        Err(e) => Err(io::Error::other(e)),
    }
}

/// A task on the blocking thread pool that is aborted when this is dropped.
/// Aborting stops a task that no pool thread has started yet, and does
/// nothing to one that runs or has finished.
struct AbortOnDrop<T>(tokio::task::JoinHandle<T>);

impl<T> Drop for AbortOnDrop<T> {
    fn drop(&mut self) {
        self.0.abort();
    }
}

/// The result of a pool task, which runs its undo function if it's dropped
/// before `claim()`, see `PassthroughFs::run_on_pool_undo()`. If the task
/// ends after its `JoinHandle` was dropped, tokio drops the result on the
/// pool thread. Otherwise the thread that drops the `JoinHandle` drops it.
struct Unclaimed<T, U: FnOnce(T)>(Option<(T, U)>);

impl<T, U: FnOnce(T)> Unclaimed<T, U> {
    fn claim(mut self) -> T {
        self.0.take().unwrap().0
    }
}

impl<T, U: FnOnce(T)> Drop for Unclaimed<T, U> {
    fn drop(&mut self) {
        if let Some((value, undo)) = self.0.take() {
            undo(value);
        }
    }
}

/// The asynchronous zero-copy traits (`AsyncZeroCopyReader`/`AsyncZeroCopyWriter`)
/// return `!Send` futures, but `AsyncFileSystem` requires `Send` futures. The
/// zero-copy buffers borrow transport memory and the asynchronous IO engines
/// (io_uring) are bound to the thread polling them, so the data path relies
/// on the async runtime being a single-threaded worker anyway, cf. the
/// `unsafe impl Send` for the transport adapters in `api/server/async_io.rs`.
/// Mark the zero-copy futures as `Send` on the same grounds.
#[repr(transparent)]
struct SendZeroCopyFuture<F>(F);

// Safe because the async runtime executing the zero-copy path is a
// single-threaded worker, so the future is never moved between threads.
unsafe impl<F> Send for SendZeroCopyFuture<F> {}

impl<F: Future> Future for SendZeroCopyFuture<F> {
    type Output = F::Output;

    fn poll(
        self: Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        // Safe because `SendZeroCopyFuture` is `repr(transparent)`.
        unsafe { self.map_unchecked_mut(|s: &mut Self| &mut s.0) }.poll(cx)
    }
}

/// A read-only view of a handle's fd that serves positioned reads with
/// `preadv2()` and the `RWF_NOWAIT` flag.
///
/// `RWF_NOWAIT` copies whatever the page cache already holds and fails with
/// `EAGAIN` as soon as the read would have to wait for IO, so an inline read
/// through this adapter never blocks the runtime thread. Only the positioned
/// read side of [`FileReadWriteVolatile`] is implemented; the write side is
/// out of scope for the READ fast path and always fails with `EINVAL`.
struct NowaitFile<'a> {
    fd: BorrowedFd<'a>,
}

impl FileReadWriteVolatile for NowaitFile<'_> {
    fn read_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    fn write_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    fn read_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> io::Result<usize> {
        let iov = libc::iovec {
            iov_base: slice.as_ptr() as *mut libc::c_void,
            iov_len: slice.len(),
        };

        // Safe: the iovec points into `slice`, which the caller guarantees to
        // be valid for the duration of the call, and the kernel only writes
        // within its bounds.
        let ret = unsafe {
            libc::preadv2(
                self.fd.as_raw_fd(),
                &iov,
                1,
                offset as libc::off_t,
                libc::RWF_NOWAIT,
            )
        };
        if ret >= 0 {
            Ok(ret as usize)
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn read_vectored_at_volatile(
        &mut self,
        bufs: &[FileVolatileSlice],
        offset: u64,
    ) -> io::Result<usize> {
        if bufs.len() == 1 {
            return self.read_at_volatile(bufs[0], offset);
        }

        let iovecs: Vec<libc::iovec> = bufs
            .iter()
            .map(|s| libc::iovec {
                iov_base: s.as_ptr() as *mut libc::c_void,
                iov_len: s.len(),
            })
            .collect();

        // Safe: the iovecs point into `bufs`, which the caller guarantees to
        // be valid for the duration of the call.
        let ret = unsafe {
            libc::preadv2(
                self.fd.as_raw_fd(),
                iovecs.as_ptr(),
                iovecs.len() as libc::c_int,
                offset as libc::off_t,
                libc::RWF_NOWAIT,
            )
        };
        if ret >= 0 {
            Ok(ret as usize)
        } else {
            Err(io::Error::last_os_error())
        }
    }

    fn write_at_volatile(&mut self, _slice: FileVolatileSlice, _offset: u64) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }
}

/// A page-aligned buffer that a pool thread owns in place of a transport
/// buffer, see `PassthroughFs::read_on_pool()` and `write_on_pool()`. The
/// alignment lets an O_DIRECT request do its IO on it directly, without the
/// bounce buffer of `read_direct()` and `write_direct()`. A READ fills the
/// buffer up to its capacity. A WRITE copies its payload in and then reads
/// it out from `pos`.
struct PoolBuf {
    /// Holds the data from the first page boundary in its spare capacity.
    mem: Vec<u8>,
    /// Offset of the first page boundary in `mem`.
    start: usize,
    /// Size of the buffer that the caller asked for.
    capacity: usize,
    len: usize,
    pos: usize,
}

impl PoolBuf {
    /// Fails with ENOMEM if it can't allocate `capacity` bytes, where
    /// `Vec::with_capacity()` would abort the process. It allocates a page
    /// more than `capacity`, so the buffer can start at a page boundary.
    fn new(capacity: usize) -> io::Result<Self> {
        let enomem = || io::Error::from_raw_os_error(libc::ENOMEM);
        let page = pagesize();
        let mut mem = Vec::new();
        mem.try_reserve_exact(capacity.checked_add(page).ok_or_else(enomem)?)
            .map_err(|_| enomem())?;
        let addr = mem.as_ptr() as usize;
        let start = addr.next_multiple_of(page) - addr;
        Ok(PoolBuf {
            mem,
            start,
            capacity,
            len: 0,
            pos: 0,
        })
    }

    fn data(&self) -> &[u8] {
        // SAFETY: `start + len` is within the vector's capacity, and the
        // first `len` bytes from `start` are initialized.
        unsafe { std::slice::from_raw_parts(self.mem.as_ptr().add(self.start), self.len) }
    }

    /// The page-aligned start of the buffer.
    fn as_mut_ptr(&mut self) -> *mut u8 {
        // SAFETY: `start` is less than a page, and the vector has a page more
        // capacity than the buffer.
        unsafe { self.mem.as_mut_ptr().add(self.start) }
    }

    fn spare_len(&self) -> usize {
        self.capacity - self.len
    }

    /// Append up to `len` bytes from `src`, as many as fit, and return the
    /// count.
    ///
    /// # Safety
    ///
    /// `src` must be valid for reads of `len` bytes, and must not point into
    /// this buffer.
    unsafe fn append(&mut self, src: *const u8, len: usize) -> usize {
        let n = std::cmp::min(len, self.spare_len());
        std::ptr::copy_nonoverlapping(src, self.as_mut_ptr().add(self.len), n);
        self.len += n;
        n
    }
}

impl io::Write for PoolBuf {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // SAFETY: `buf` is valid for reads and doesn't point into `self`,
        // which is borrowed mutably.
        Ok(unsafe { self.append(buf.as_ptr(), buf.len()) })
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl ZeroCopyWriter for PoolBuf {
    fn write_from(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let count = std::cmp::min(count, self.spare_len());
        // SAFETY: the slice covers spare capacity of the buffer, which stays
        // valid during the read. The read only writes to it, so its bytes
        // don't need to be initialized.
        let slice =
            unsafe { FileVolatileSlice::from_raw_ptr(self.as_mut_ptr().add(self.len), count) };
        // Retry a read that a signal interrupted, as the native path does.
        let n = loop {
            match f.read_at_volatile(slice, off) {
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                res => break res?,
            }
        };
        // The read initialized the first `n` bytes of the slice. This runs
        // only in `PassthroughFs::do_read()`, where `f` is a `std::fs::File`
        // that reads with `pread()`, which returns the count it wrote.
        self.len += std::cmp::min(n, count);
        Ok(n)
    }

    fn available_bytes(&self) -> usize {
        self.spare_len()
    }
}

impl io::Read for PoolBuf {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = std::cmp::min(buf.len(), self.len - self.pos);
        buf[..n].copy_from_slice(&self.data()[self.pos..self.pos + n]);
        self.pos += n;
        Ok(n)
    }
}

impl ZeroCopyReader for PoolBuf {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let count = std::cmp::min(count, self.len - self.pos);
        if count == 0 {
            return Ok(0);
        }
        // SAFETY: the slice covers initialized bytes of the buffer, which
        // stays valid during the write, and a write only reads from it.
        let slice =
            unsafe { FileVolatileSlice::from_raw_ptr(self.as_mut_ptr().add(self.pos), count) };
        // Retry a write that a signal interrupted, as the native path does.
        let n = loop {
            match f.write_at_volatile(slice, off) {
                Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                res => break res?,
            }
        };
        self.pos += std::cmp::min(n, count);
        Ok(n)
    }
}

/// A file that appends the data written to it to a `PoolBuf`, so that
/// `PassthroughFs::write_on_pool()` copies the payload of a WRITE out of the
/// request with one call. It takes no more than the buffer's capacity, and
/// ignores the file offsets.
struct PayloadSink<'a>(&'a mut PoolBuf);

impl PayloadSink<'_> {
    fn append(&mut self, bufs: &[FileVolatileSlice]) -> usize {
        let mut count = 0;
        for buf in bufs {
            // SAFETY: whoever created `buf` guarantees that it's valid for
            // reads of `buf.len()` bytes. It doesn't point into the pool
            // buffer, which `self` borrows mutably.
            let n = unsafe { self.0.append(buf.as_ptr(), buf.len()) };
            count += n;
            if n < buf.len() {
                break;
            }
        }
        count
    }
}

impl FileReadWriteVolatile for PayloadSink<'_> {
    fn read_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    fn write_volatile(&mut self, slice: FileVolatileSlice) -> io::Result<usize> {
        Ok(self.append(&[slice]))
    }

    fn write_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> io::Result<usize> {
        Ok(self.append(bufs))
    }

    fn read_at_volatile(&mut self, _slice: FileVolatileSlice, _offset: u64) -> io::Result<usize> {
        Err(io::Error::from_raw_os_error(libc::EINVAL))
    }

    fn write_at_volatile(&mut self, slice: FileVolatileSlice, _offset: u64) -> io::Result<usize> {
        Ok(self.append(&[slice]))
    }

    fn write_vectored_at_volatile(
        &mut self,
        bufs: &[FileVolatileSlice],
        _offset: u64,
    ) -> io::Result<usize> {
        Ok(self.append(bufs))
    }
}

/// Relay a synchronous handler to the runtime's blocking thread pool if
/// `pool_fs()` returns a file system to offload it to, and run it inline
/// otherwise. `$capture` rebinds the borrowed request arguments to owned
/// copies which can be moved into the pool closure, and `$pool_fn` is a
/// `move` closure taking the file system and the request context by value.
/// A handler whose result holds a lookup count or a handle passes `undo`,
/// which releases them if the request is dropped, see `run_on_pool_undo()`.
/// Its `$pool_fn` and `undo` borrow the file system instead.
macro_rules! async_relay {
    ($self:expr, $ctx:expr, [$($capture:tt)*], $inline_call:expr, $pool_fn:expr $(, undo: $undo:expr)?) => {
        match $self.pool_fs() {
            Some(fs) => {
                $($capture)*
                async_relay!(@pool fs, $ctx, $pool_fn $(, $undo)?).await
            }
            None => $inline_call,
        }
    };
    (@pool $fs:ident, $ctx:expr, $pool_fn:expr) => {
        Self::run_on_pool($fs, $ctx, $pool_fn)
    };
    (@pool $fs:ident, $ctx:expr, $pool_fn:expr, $undo:expr) => {
        Self::run_on_pool_undo($fs, $ctx, $pool_fn, $undo)
    };
}

// The undo functions of requests that were dropped before their reply.
// `release()` and `forget()` ignore the context.

/// Release a handle that `open()` or `create()` returned.
fn undo_open<S: BitmapSlice + Send + Sync>(
    fs: &PassthroughFs<S>,
    inode: Inode,
    handle: Option<Handle>,
) {
    if let Some(handle) = handle {
        let _ = fs.release(&Context::default(), inode, 0, handle, false, false, None);
    }
}

/// Drop the lookup count that `lookup()` or `create()` took.
fn undo_lookup<S: BitmapSlice + Send + Sync>(fs: &PassthroughFs<S>, inode: Inode) {
    fs.forget(&Context::default(), inode, 1);
}

impl<S: BitmapSlice + Send + Sync + 'static> BackendFileSystem for PassthroughFs<S> {
    fn mount(&self) -> io::Result<(Entry, u64)> {
        let entry = self.do_lookup(fuse::ROOT_ID, &CString::new(".").unwrap())?;
        Ok((entry, VFS_MAX_INO))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

#[async_trait]
impl<S: BitmapSlice + Send + Sync + 'static> AsyncFileSystem for PassthroughFs<S> {
    async fn async_lookup(
        &self,
        ctx: &Context,
        parent: <Self as FileSystem>::Inode,
        name: &CStr,
    ) -> io::Result<Entry> {
        async_relay!(
            self,
            ctx,
            [let name = name.to_owned();],
            self.lookup(ctx, parent, name),
            move |fs: &Self, ctx: Context| fs.lookup(&ctx, parent, &name),
            undo: |fs: &Self, entry: Entry| undo_lookup(fs, entry.inode)
        )
    }

    async fn async_getattr(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: Option<<Self as FileSystem>::Handle>,
    ) -> io::Result<(libc::stat64, Duration)> {
        async_relay!(
            self,
            ctx,
            [],
            self.getattr(ctx, inode, handle),
            move |fs: Arc<Self>, ctx: Context| fs.getattr(&ctx, inode, handle)
        )
    }

    async fn async_setattr(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        attr: libc::stat64,
        handle: Option<<Self as FileSystem>::Handle>,
        valid: SetattrValid,
    ) -> io::Result<(libc::stat64, Duration)> {
        async_relay!(
            self,
            ctx,
            [],
            self.setattr(ctx, inode, attr, handle, valid),
            move |fs: Arc<Self>, ctx: Context| fs.setattr(&ctx, inode, attr, handle, valid)
        )
    }

    async fn async_open(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<<Self as FileSystem>::Handle>, OpenOptions)> {
        async_relay!(
            self,
            ctx,
            [],
            self.open(ctx, inode, flags, fuse_flags)
                .map(|(handle, opts, _)| (handle, opts)),
            move |fs: &Self, ctx: Context| {
                fs.open(&ctx, inode, flags, fuse_flags)
                    .map(|(handle, opts, _)| (handle, opts))
            },
            undo: move |fs: &Self, (handle, _)| undo_open(fs, inode, handle)
        )
    }

    async fn async_create(
        &self,
        ctx: &Context,
        parent: <Self as FileSystem>::Inode,
        name: &CStr,
        args: CreateIn,
    ) -> io::Result<(Entry, Option<<Self as FileSystem>::Handle>, OpenOptions)> {
        async_relay!(
            self,
            ctx,
            [let name = name.to_owned();],
            self.create(ctx, parent, name, args)
                .map(|(entry, handle, opts, _)| (entry, handle, opts)),
            move |fs: &Self, ctx: Context| {
                fs.create(&ctx, parent, &name, args)
                    .map(|(entry, handle, opts, _)| (entry, handle, opts))
            },
            undo: |fs: &Self, (entry, handle, _): (Entry, _, _)| {
                undo_open(fs, entry.inode, handle);
                undo_lookup(fs, entry.inode);
            }
        )
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_read(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        w: &mut (dyn AsyncZeroCopyWriter + Send),
        size: u32,
        offset: u64,
        _lock_owner: Option<u64>,
        flags: u32,
    ) -> io::Result<usize> {
        // O_DIRECT requests go to the synchronous `do_read()`. The native
        // asynchronous path submits IO directly into the transport buffer,
        // whose payload offset right after the reply header doesn't satisfy
        // the alignment constraints of direct IO (buffer address, length and
        // file offset must all be multiples of the logical block size), so
        // ext4 and XFS reject it with `EINVAL`. `do_read()` stages the data
        // through a page-aligned bounce buffer instead (`read_direct()`), and
        // blocks the thread it runs on for the duration of the read.
        // With the thread pool enabled, that's a pool thread, which reads
        // into its page-aligned buffer without a bounce buffer, see
        // `read_on_pool()`, and otherwise the runtime thread.
        let data = self.get_data(handle, inode, libc::O_RDONLY)?;
        if flags & (libc::O_DIRECT as u32) != 0 {
            return match self.pool_fs() {
                Some(fs) => Self::read_on_pool(fs, ctx, data, w, size, offset, flags).await,
                None => self.do_read(&data, w, size, offset, flags, false),
            };
        }

        // Buffered requests first try an inline non-blocking read: the
        // page cache serves them without a round trip through the
        // asynchronous IO engine.
        let (served, miss) = self.read_nowait(&data, w, size as usize, offset, flags)?;
        if !miss {
            return Ok(served);
        }

        // On a cache miss on the tokio runtime, whose file IO would block the
        // runtime thread, serve the remainder on the thread pool if it's
        // enabled. It continues where the inline attempt stopped.
        if async_runtime::runtime_type().file_io_blocks() {
            if let Some(fs) = self.pool_fs() {
                let n = Self::read_on_pool(
                    fs,
                    ctx,
                    data,
                    w,
                    size - served as u32,
                    offset + served as u64,
                    flags,
                )
                .await?;
                return Ok(served + n);
            }
        }

        // Cache miss: serve the remainder with native asynchronous IO,
        // continuing at the writer's position and the file offset where
        // the inline attempt stopped.
        let file = self.async_file_from_data(&data, flags)?;
        let n = SendZeroCopyFuture(w.async_write_from(
            file,
            size as usize - served,
            offset + served as u64,
        ))
        .await?;
        Ok(served + n)
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_write(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        r: &mut (dyn AsyncZeroCopyReader + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<usize> {
        // O_DIRECT requests are relayed to the synchronous handler for the
        // same alignment reason as `async_read()` above (`write_direct()`
        // stages the payload through a page-aligned bounce buffer).
        // WRITE_KILL_PRIV requests are relayed too: the synchronous handler
        // drops CAP_FSETID around the underlying write and restores it right
        // after, whereas the native path would hold the capability-dropped
        // state across `.await` points, so a concurrent non-killpriv write
        // issued while this future is suspended could run with the capability
        // already dropped and lose the setgid bit it must preserve.
        // With the thread pool enabled, a pool thread serves these relayed
        // requests, and on the tokio runtime every WRITE, with `do_write()`
        // from its page-aligned buffer, which needs no bounce buffer, see
        // `write_on_pool()`. `do_write()` drops and restores CAP_FSETID on
        // the pool thread, with no `.await` in between.
        let relay = flags & (libc::O_DIRECT as u32) != 0
            || (self.killpriv_v2.load(Ordering::Relaxed) && fuse_flags & WRITE_KILL_PRIV != 0);
        if relay || async_runtime::runtime_type().file_io_blocks() {
            if let Some(fs) = self.pool_fs() {
                return Self::write_on_pool(
                    fs, ctx, inode, handle, r, size, offset, flags, fuse_flags,
                )
                .await;
            }
        }
        if relay {
            return self.write(
                ctx,
                inode,
                handle,
                r,
                size,
                offset,
                lock_owner,
                delayed_write,
                flags,
                fuse_flags,
            );
        }

        let data = self.get_data(handle, inode, libc::O_RDWR)?;

        if self.seal_size.load(Ordering::Relaxed) {
            let st = stat_fd(data.get_file(), None)?;
            self.seal_size_check(Opcode::Write, st.st_size as u64, offset, size as u64, 0)?;
        }

        // Borrow the fd of the handle for the duration of the write: the
        // asynchronous file object holds a reference to the handle data,
        // which keeps the descriptor valid until the request completes,
        // avoiding the `dup()`/`close()` syscall pair per request.
        let file = self.async_file_from_data(&data, flags)?;

        // Serve the request with native asynchronous IO: the transport
        // transfers the data directly between its buffer and the file.
        SendZeroCopyFuture(r.async_read_to(file, size as usize, offset)).await
    }

    async fn async_fsync(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        datasync: bool,
        handle: <Self as FileSystem>::Handle,
    ) -> io::Result<()> {
        async_relay!(
            self,
            ctx,
            [],
            self.fsync(ctx, inode, datasync, handle),
            move |fs: Arc<Self>, ctx: Context| fs.fsync(&ctx, inode, datasync, handle)
        )
    }

    async fn async_fallocate(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        handle: <Self as FileSystem>::Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> io::Result<()> {
        async_relay!(
            self,
            ctx,
            [],
            self.fallocate(ctx, inode, handle, mode, offset, length),
            move |fs: Arc<Self>, ctx: Context| fs
                .fallocate(&ctx, inode, handle, mode, offset, length)
        )
    }

    async fn async_fsyncdir(
        &self,
        ctx: &Context,
        inode: <Self as FileSystem>::Inode,
        datasync: bool,
        handle: <Self as FileSystem>::Handle,
    ) -> io::Result<()> {
        async_relay!(
            self,
            ctx,
            [],
            self.fsyncdir(ctx, inode, datasync, handle),
            move |fs: Arc<Self>, ctx: Context| fs.fsyncdir(&ctx, inode, datasync, handle)
        )
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::Ordering;
    use std::sync::Arc;

    use super::*;
    use fuse_backend_core::abi::fuse_abi::ROOT_ID;
    use fuse_backend_core::api::filesystem::{FsOptions, ZeroCopyReader, ZeroCopyWriter};
    use fuse_backend_core::async_runtime;
    use fuse_backend_core::file_buf::{FileVolatileBuf, FileVolatileSlice};
    use fuse_backend_core::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};
    use vmm_sys_util::tempdir::TempDir;

    /// An in-memory sink implementing `AsyncZeroCopyWriter`, to receive data
    /// from `async_read()`.
    struct MemWriter(Vec<u8>);

    impl MemWriter {
        fn new() -> Self {
            MemWriter(Vec::new())
        }
    }

    impl io::Write for MemWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.0.extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl ZeroCopyWriter for MemWriter {
        fn write_from(
            &mut self,
            f: &mut dyn FileReadWriteVolatile,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            if self.0.len() < count {
                self.0.resize(count, 0);
            }
            // Safe because the slice points into `self.0` and doesn't out-live it.
            // The file offset only selects the read position within `f`; received
            // data is always placed at the start of the buffer.
            let slice = unsafe { FileVolatileSlice::from_raw_ptr(self.0.as_mut_ptr(), count) };
            f.read_at_volatile(slice, off)
        }

        fn available_bytes(&self) -> usize {
            usize::MAX
        }
    }

    #[async_trait(?Send)]
    impl AsyncZeroCopyWriter for MemWriter {
        async fn async_write_from(
            &mut self,
            f: Arc<dyn AsyncFileReadWriteVolatile>,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            if self.0.len() < count {
                self.0.resize(count, 0);
            }
            // Safe because the buffer points into `self.0` and doesn't out-live it.
            let buf = unsafe { FileVolatileBuf::from_raw_ptr(self.0.as_mut_ptr(), 0, count) };
            let (res, _) = f.async_read_at_volatile(buf, off).await;
            // Received data is always placed at the start of the buffer.
            if let Ok(n) = &res {
                self.0.truncate(*n);
            }
            res
        }
    }

    /// An in-memory source implementing `AsyncZeroCopyReader`, to provide data
    /// to `async_write()`.
    struct MemReader(Vec<u8>);

    impl io::Read for MemReader {
        fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
            let n = std::cmp::min(buf.len(), self.0.len());
            buf[..n].copy_from_slice(&self.0[..n]);
            self.0.drain(..n);
            Ok(n)
        }
    }

    impl ZeroCopyReader for MemReader {
        fn read_to(
            &mut self,
            f: &mut dyn FileReadWriteVolatile,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            let start = off as usize;
            if start >= self.0.len() {
                return Ok(0);
            }
            let n = std::cmp::min(count, self.0.len() - start);
            // Safe because the buffer is only read from and the slice doesn't
            // out-live `self.0`.
            let slice = unsafe {
                FileVolatileSlice::from_raw_ptr(self.0.as_ptr().add(start) as *mut u8, n)
            };
            f.write_at_volatile(slice, off)
        }
    }

    #[async_trait(?Send)]
    impl AsyncZeroCopyReader for MemReader {
        async fn async_read_to(
            &mut self,
            f: Arc<dyn AsyncFileReadWriteVolatile>,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            let start = off as usize;
            if start >= self.0.len() {
                return Ok(0);
            }
            let n = std::cmp::min(count, self.0.len() - start);
            // Safe because the buffer is only read from and doesn't out-live
            // `self.0`.
            let buf = unsafe {
                FileVolatileBuf::from_raw_ptr(self.0.as_ptr().add(start) as *mut u8, n, n)
            };
            let (res, _) = f.async_write_at_volatile(buf, off).await;
            res
        }
    }

    fn prepare_async_fs() -> (PassthroughFs<()>, TempDir) {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let cfg = Config {
            root_dir: source.as_path().to_str().unwrap().to_string(),
            do_import: true,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();

        (fs, source)
    }

    fn prepare_async_fs_shared(enable_pool: bool) -> (Arc<PassthroughFs<()>>, TempDir) {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let cfg = Config {
            root_dir: source.as_path().to_str().unwrap().to_string(),
            do_import: true,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new_shared(cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();
        if enable_pool {
            fs.enable_async_thread_pool(true);
        }

        (fs, source)
    }

    fn prepare_context() -> Context {
        Context {
            uid: unsafe { libc::getuid() },
            gid: unsafe { libc::getgid() },
            pid: unsafe { libc::getpid() },
            ..Default::default()
        }
    }

    #[test]
    fn test_backend_filesystem_mount() {
        let (fs, _source) = prepare_async_fs();

        let (entry, max_ino) = BackendFileSystem::mount(&fs).unwrap();
        assert_eq!(entry.inode, ROOT_ID);
        assert!(max_ino > 0);
    }

    #[test]
    fn test_async_lookup_getattr_setattr() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        let path = source.as_path().join("testfile");
        std::fs::write(&path, b"hello").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let sync_entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
            assert_eq!(entry.inode, sync_entry.inode);
            assert_eq!(entry.attr.st_size, 5);

            let (attr, _) = fs.async_getattr(&ctx, entry.inode, None).await.unwrap();
            assert_eq!(attr.st_size, 5);

            // Truncate the file to 2 bytes through async_setattr().
            let mut new_attr = attr;
            new_attr.st_size = 2;
            let (attr, _) = fs
                .async_setattr(&ctx, entry.inode, new_attr, None, SetattrValid::SIZE)
                .await
                .unwrap();
            assert_eq!(attr.st_size, 2);
        });

        assert_eq!(std::fs::metadata(&path).unwrap().len(), 2);
    }

    /// A writer double driving the hybrid READ dispatch hermetically: it
    /// stands in for both the transport writer and the file being read, so
    /// the tests decide which path serves which chunk instead of depending
    /// on kernel and filesystem behavior (a real cache miss needs an
    /// uncached page, and tmpfs fails buffered `RWF_NOWAIT` reads with
    /// `EOPNOTSUPP`, which would merely exercise the fallback).
    ///
    /// `write_from()` serves from `source` at `off`, up to `inline_budget`
    /// bytes in total, and then fails with `EAGAIN` like a page cache that
    /// runs dry; `async_write_from()` serves the remainder like the
    /// asynchronous engine completing real IO. Both append at the current
    /// position, mirroring the transport writer's continuation semantics
    /// that the hybrid relies on, and every call is recorded in `events`.
    struct PathRecorder {
        /// File content that reads are served from.
        source: Vec<u8>,
        /// Total number of bytes `write_from()` serves before failing with
        /// `EAGAIN`; `usize::MAX` never fails, so the inline path always
        /// completes.
        inline_budget: usize,
        /// Bytes served by `write_from()` so far.
        inline_served: usize,
        /// Bytes received so far.
        data: Vec<u8>,
        /// (`inline`/`inline-eagain`/`inline-eof`/`async`, count, offset) per call.
        events: Vec<(&'static str, usize, u64)>,
    }

    impl PathRecorder {
        fn new(source: &[u8], inline_budget: usize) -> Self {
            PathRecorder {
                source: source.to_vec(),
                inline_budget,
                inline_served: 0,
                data: Vec::new(),
                events: Vec::new(),
            }
        }
    }

    impl io::Write for PathRecorder {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.data.extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl ZeroCopyWriter for PathRecorder {
        fn write_from(
            &mut self,
            _f: &mut dyn FileReadWriteVolatile,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            let start = off as usize;
            // Reading past the end of the source is EOF, like a short read
            // from a file smaller than the request.
            if start >= self.source.len() {
                self.events.push(("inline-eof", 0, off));
                return Ok(0);
            }
            // The scripted page cache runs dry after `inline_budget` bytes.
            if self.inline_served >= self.inline_budget {
                self.events.push(("inline-eagain", count, off));
                return Err(io::Error::from_raw_os_error(libc::EAGAIN));
            }
            let n = std::cmp::min(count, self.inline_budget - self.inline_served);
            let n = std::cmp::min(n, self.source.len() - start);
            self.inline_served += n;
            self.events.push(("inline", n, off));
            self.data.extend_from_slice(&self.source[start..start + n]);
            Ok(n)
        }

        fn available_bytes(&self) -> usize {
            usize::MAX
        }
    }

    #[async_trait(?Send)]
    impl AsyncZeroCopyWriter for PathRecorder {
        async fn async_write_from(
            &mut self,
            f: Arc<dyn AsyncFileReadWriteVolatile>,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            // Read the file, so the tests see the data the native path reads.
            let mut buf = vec![0u8; count];
            // Safe because `vbuf` doesn't outlive `buf`.
            let vbuf = unsafe { FileVolatileBuf::from_raw_ptr(buf.as_mut_ptr(), 0, count) };
            let (res, _) = f.async_read_at_volatile(vbuf, off).await;
            let n = res?;
            self.events.push(("async", n, off));
            self.data.extend_from_slice(&buf[..n]);
            Ok(n)
        }
    }

    #[test]
    fn test_nowait_file() {
        let source = TempDir::new().unwrap();
        let path = source.as_path().join("testfile");
        std::fs::write(&path, b"hello world").unwrap();
        let file = std::fs::File::open(&path).unwrap();
        // Safe: `fd` doesn't out-live `file`.
        let mut f = NowaitFile {
            fd: unsafe { BorrowedFd::borrow_raw(file.as_raw_fd()) },
        };
        let mut buf = [0u8; 11];
        // Safe: the slice points into `buf` and doesn't out-live it.
        let slice = unsafe { FileVolatileSlice::from_raw_ptr(buf.as_mut_ptr(), 11) };
        match f.read_at_volatile(slice, 0) {
            // Whether the non-blocking read engages is a filesystem property
            // (tmpfs fails with EOPNOTSUPP, disk filesystems serve warm
            // pages), so both outcomes are valid. On success the wrapper must
            // report the count and deliver the data at the slice.
            Ok(n) => {
                assert_eq!(n, 11);
                assert_eq!(&buf, b"hello world");
            }
            Err(e) => assert!(matches!(
                e.raw_os_error(),
                Some(libc::EAGAIN)
                    | Some(libc::EINVAL)
                    | Some(libc::ENOSYS)
                    | Some(libc::EOPNOTSUPP)
            )),
        }
    }

    #[test]
    fn test_async_read_fast_path() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"hello world").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDONLY as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            // A cache-resident read must be served inline in one shot, without
            // a round trip through the asynchronous IO engine.
            let mut w = PathRecorder::new(b"hello world", usize::MAX);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    11,
                    0,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, 11);
            assert_eq!(w.data, b"hello world");
            assert_eq!(w.events, [("inline", 11, 0)]);
        });
    }

    #[test]
    fn test_async_read_fast_path_offset() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"hello world").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDONLY as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            let mut w = PathRecorder::new(b"hello world", usize::MAX);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    5,
                    6,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, 5);
            assert_eq!(w.data, b"world");
            assert_eq!(w.events, [("inline", 5, 6)]);
        });
    }

    #[test]
    fn test_async_read_fast_path_eof() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"hello").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDONLY as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            // A request larger than the file is a short read terminated by an
            // inline EOF, without waking the asynchronous engine: the first
            // call serves the whole file, the second returns zero.
            let mut w = PathRecorder::new(b"hello", usize::MAX);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    10,
                    0,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, 5);
            assert_eq!(w.data, b"hello");
            assert_eq!(w.events, [("inline", 5, 0), ("inline-eof", 0, 5)]);
        });
    }

    #[test]
    fn test_async_read_nowait_miss_fallback() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"abcdefghij").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDONLY as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            // The inline path is scripted to fail with EAGAIN right away, so
            // the whole request is served by the native asynchronous path.
            let mut w = PathRecorder::new(b"abcdefghij", 0);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    10,
                    0,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, 10);
            assert_eq!(w.data, b"abcdefghij");
            assert_eq!(w.events, [("inline-eagain", 10, 0), ("async", 10, 0)]);
        });
    }

    #[test]
    fn test_async_read_nowait_partial_fallback() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"abcdefghij").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDONLY as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            // The inline path serves the first 3 bytes and then misses: the
            // asynchronous fallback must continue at the writer's position
            // and at the file offset where the inline attempt stopped, not
            // overwrite the bytes already served.
            let mut w = PathRecorder::new(b"abcdefghij", 3);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    10,
                    0,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, 10);
            assert_eq!(w.data, b"abcdefghij");
            assert_eq!(
                w.events,
                [("inline", 3, 0), ("inline-eagain", 7, 3), ("async", 7, 3)]
            );
        });
    }

    #[test]
    fn test_async_open_read() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"hello world").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDONLY as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            // Read 5 bytes at offset 6 to also cover offset handling.
            let mut w = MemWriter::new();
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    5,
                    6,
                    None,
                    libc::O_RDONLY as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, 5);
            assert_eq!(&w.0, b"world");
        });
    }

    #[test]
    fn test_async_create_write_fsync() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();

        async_runtime::block_on(async {
            let name = CString::new("newfile").unwrap();
            let args = CreateIn {
                flags: (libc::O_RDWR | libc::O_CREAT | libc::O_TRUNC) as u32,
                mode: 0o644,
                umask: 0,
                fuse_flags: 0,
            };
            let (entry, handle, _opts) = fs.async_create(&ctx, ROOT_ID, &name, args).await.unwrap();
            let handle = handle.unwrap();

            let mut r = MemReader(b"async data".to_vec());
            let n = fs
                .async_write(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut r,
                    10,
                    0,
                    None,
                    false,
                    libc::O_RDWR as u32,
                    0,
                )
                .await
                .unwrap();
            assert_eq!(n, 10);

            fs.async_fsync(&ctx, entry.inode, true, handle)
                .await
                .unwrap();
        });

        let content = std::fs::read(source.as_path().join("newfile")).unwrap();
        assert_eq!(&content, b"async data");
    }

    /// Whether the file system of `dir` supports O_DIRECT. Prints why `test`
    /// skips if it doesn't.
    fn supports_direct_io(dir: &TempDir, test: &str) -> bool {
        use std::os::unix::fs::OpenOptionsExt;

        let path = dir.as_path().join("direct_io_probe");
        match std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(true)
            .custom_flags(libc::O_DIRECT)
            .open(&path)
        {
            Ok(_) => {
                std::fs::remove_file(&path).unwrap();
                true
            }
            Err(e) if e.raw_os_error() == Some(libc::EINVAL) => {
                eprintln!(
                    "skipping {}: {:?} does not support O_DIRECT",
                    test,
                    dir.as_path()
                );
                false
            }
            Err(e) => panic!("unexpected error opening {:?} with O_DIRECT: {}", path, e),
        }
    }

    // O_DIRECT and WRITE_KILL_PRIV requests are relayed to the synchronous
    // handlers (see `async_read()`/`async_write()`): the synchronous handler
    // stages direct-IO payloads through a page-aligned bounce buffer, which
    // the native asynchronous path can't -- its IO goes straight into the
    // transport buffer, which alignment-enforcing filesystems reject with
    // EINVAL. The relay must keep such requests working. O_DIRECT needs a
    // backing filesystem that supports it; tmpfs (a common /tmp) rejects it
    // at open() with EINVAL, so skip gracefully there rather than fail, to
    // keep the test from being environment-dependent.
    #[test]
    fn test_async_direct_io_relayed() {
        const BLOCK: usize = 4096;
        const KILLPRIV_BLOCK: usize = 512;

        let dir = TempDir::new().expect("Cannot create temporary directory.");
        if !supports_direct_io(&dir, "test_async_direct_io_relayed") {
            return;
        }

        // `do_import: false` enables killpriv_v2 at init(), so the
        // WRITE_KILL_PRIV leg below takes the relay too. The root inode
        // still needs an explicit `import()`: `init()` only imports
        // automatically when `do_import` is set. Only HANDLE_KILLPRIV_V2 is
        // negotiated: `FsOptions::all()` would also enable the zero-message
        // options (negotiable exactly because `do_import` is false), and
        // ZERO_MESSAGE_OPEN makes `create()` reply without a handle.
        let cfg = Config {
            root_dir: dir.as_path().to_str().unwrap().to_string(),
            do_import: false,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::HANDLE_KILLPRIV_V2).unwrap();
        assert!(fs.killpriv_v2.load(Ordering::Relaxed));

        let ctx = prepare_context();
        let name = CString::new("async_direct_file").unwrap();
        let killpriv_payload: Vec<u8> = (0..KILLPRIV_BLOCK).map(|i| (i % 241) as u8).collect();

        async_runtime::block_on(async {
            let args = CreateIn {
                flags: (libc::O_RDWR | libc::O_CREAT | libc::O_TRUNC | libc::O_DIRECT) as u32,
                mode: 0o600,
                umask: 0,
                fuse_flags: 0,
            };
            let (entry, handle, _opts) = fs.async_create(&ctx, ROOT_ID, &name, args).await.unwrap();
            let handle = handle.unwrap();

            // A direct-IO write: relayed to `write_direct()`, which stages
            // the payload through an aligned bounce buffer. The native path
            // would submit IO straight into the transport buffer and fail
            // with EINVAL on alignment-enforcing filesystems.
            let payload: Vec<u8> = (0..BLOCK).map(|i| (i % 251) as u8).collect();
            let mut r = MemReader(payload.clone());
            let n = fs
                .async_write(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut r,
                    BLOCK as u32,
                    0,
                    None,
                    false,
                    libc::O_DIRECT as u32,
                    0,
                )
                .await
                .unwrap();
            assert_eq!(n, BLOCK);

            // A direct-IO read: relayed to `read_direct()`. The double
            // records which path served it: neither the inline hybrid nor
            // the native asynchronous engine may run (`write_from()` and
            // `async_write_from()` push an event), only the synchronous
            // relay through `io::Write` may deliver data.
            let mut w = PathRecorder::new(&[], usize::MAX);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    BLOCK as u32,
                    0,
                    None,
                    libc::O_DIRECT as u32,
                )
                .await
                .unwrap();
            assert_eq!(n, BLOCK);
            assert_eq!(w.data, payload);
            assert!(w.events.is_empty());

            // A WRITE_KILL_PRIV write on a second, buffered file takes the
            // relay as well, and must keep working (the capability drop is
            // a no-op without CAP_FSETID).
            let killpriv_name = CString::new("async_killpriv_file").unwrap();
            let args = CreateIn {
                flags: (libc::O_RDWR | libc::O_CREAT | libc::O_TRUNC) as u32,
                mode: 0o600,
                umask: 0,
                fuse_flags: 0,
            };
            let (killpriv_entry, killpriv_handle, _opts) = fs
                .async_create(&ctx, ROOT_ID, &killpriv_name, args)
                .await
                .unwrap();
            let killpriv_handle = killpriv_handle.unwrap();

            let mut r = MemReader(killpriv_payload.clone());
            let n = fs
                .async_write(
                    &ctx,
                    killpriv_entry.inode,
                    killpriv_handle,
                    &mut r,
                    KILLPRIV_BLOCK as u32,
                    0,
                    None,
                    false,
                    libc::O_RDWR as u32,
                    WRITE_KILL_PRIV,
                )
                .await
                .unwrap();
            assert_eq!(n, KILLPRIV_BLOCK);
        });

        let content = std::fs::read(dir.as_path().join("async_killpriv_file")).unwrap();
        assert_eq!(content, killpriv_payload);
    }

    // With the thread pool, O_DIRECT requests do their IO on the pool's
    // page-aligned buffer, without a bounce buffer. An unaligned buffer would
    // fail with EINVAL.
    // The O_DIRECT tests skip on file systems without direct IO, so check
    // the alignment that they rely on here.
    #[test]
    fn test_pool_buf_page_aligned() {
        for size in [0, 1, 4096, 1 << 20] {
            let mut buf = PoolBuf::new(size).unwrap();
            assert_eq!(buf.as_mut_ptr() as usize % pagesize(), 0);
            assert_eq!(buf.available_bytes(), size);
        }
        assert!(PoolBuf::new(usize::MAX).is_err());
    }

    #[test]
    fn test_async_pool_direct_io() {
        const BLOCK: usize = 4096;

        let (fs, dir) = prepare_async_fs_shared(true);
        if !supports_direct_io(&dir, "test_async_pool_direct_io") {
            return;
        }
        let ctx = prepare_context();
        let name = CString::new("direct_file").unwrap();
        let flags = libc::O_DIRECT as u32;
        let payload: Vec<u8> = (0..2 * BLOCK).map(|i| (i % 251) as u8).collect();

        async_runtime::block_on(async {
            let args = CreateIn {
                flags: (libc::O_RDWR | libc::O_CREAT | libc::O_DIRECT) as u32,
                mode: 0o600,
                umask: 0,
                fuse_flags: 0,
            };
            let (entry, handle, _opts) = fs.async_create(&ctx, ROOT_ID, &name, args).await.unwrap();
            let handle = handle.unwrap();

            for (i, block) in payload.chunks(BLOCK).enumerate() {
                let mut r = MemReader(block.to_vec());
                let off = (i * BLOCK) as u64;
                let n = fs
                    .async_write(
                        &ctx,
                        entry.inode,
                        handle,
                        &mut r,
                        BLOCK as u32,
                        off,
                        None,
                        false,
                        flags,
                        0,
                    )
                    .await
                    .unwrap();
                assert_eq!(n, BLOCK);
            }

            let mut w = PathRecorder::new(&[], usize::MAX);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    2 * BLOCK as u32,
                    0,
                    None,
                    flags,
                )
                .await
                .unwrap();
            assert_eq!(n, 2 * BLOCK);
            assert_eq!(w.data, payload);
            assert!(w.events.is_empty());
        });
    }

    #[test]
    fn test_async_fallocate() {
        let (fs, source) = prepare_async_fs();
        let ctx = prepare_context();
        let path = source.as_path().join("testfile");
        std::fs::write(&path, b"").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDWR as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();

            fs.async_fallocate(&ctx, entry.inode, handle, 0, 0, 4096)
                .await
                .unwrap();
        });

        assert_eq!(std::fs::metadata(&path).unwrap().len(), 4096);
    }

    // Exercise the blocking thread pool path: the file system is created
    // with `new_shared()` and the async thread pool is enabled, so the
    // relayed handlers run on pool threads instead of inline.
    #[test]
    fn test_async_pool_lookup_getattr() {
        let (fs, source) = prepare_async_fs_shared(true);
        let ctx = prepare_context();
        let path = source.as_path().join("testfile");
        std::fs::write(&path, b"hello").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let sync_entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
            assert_eq!(entry.inode, sync_entry.inode);
            assert_eq!(entry.attr.st_size, 5);

            let (attr, _) = fs.async_getattr(&ctx, entry.inode, None).await.unwrap();
            assert_eq!(attr.st_size, 5);
        });
    }

    #[test]
    fn test_async_pool_create_open_fallocate() {
        let (fs, source) = prepare_async_fs_shared(true);
        let ctx = prepare_context();

        async_runtime::block_on(async {
            let name = CString::new("newfile").unwrap();
            let args = CreateIn {
                flags: (libc::O_RDWR | libc::O_CREAT | libc::O_TRUNC) as u32,
                mode: 0o644,
                umask: 0,
                fuse_flags: 0,
            };
            let (entry, handle, _opts) = fs.async_create(&ctx, ROOT_ID, &name, args).await.unwrap();
            let handle = handle.unwrap();
            fs.async_fsync(&ctx, entry.inode, true, handle)
                .await
                .unwrap();

            let (handle, _opts) = fs
                .async_open(&ctx, entry.inode, libc::O_RDWR as u32, 0)
                .await
                .unwrap();
            let handle = handle.unwrap();
            fs.async_fallocate(&ctx, entry.inode, handle, 0, 0, 4096)
                .await
                .unwrap();
        });

        assert_eq!(
            std::fs::metadata(source.as_path().join("newfile"))
                .unwrap()
                .len(),
            4096
        );
    }

    /// The number of file descriptors of this process that refer to `path`.
    fn fds_to(path: &std::path::Path) -> usize {
        std::fs::read_dir("/proc/self/fd")
            .unwrap()
            .filter_map(|e| std::fs::read_link(e.ok()?.path()).ok())
            .filter(|p| p == path)
            .count()
    }

    /// Wait until `cond` holds, for up to 10 seconds.
    fn wait_for(cond: impl Fn() -> bool) {
        let deadline = std::time::Instant::now() + Duration::from_secs(10);
        while !cond() {
            assert!(std::time::Instant::now() < deadline);
            std::thread::sleep(Duration::from_millis(1));
        }
    }

    /// Start `request` and drop it while a pool thread serves it. The thread
    /// opens `path` and then waits for the lock that `guard` holds.
    async fn drop_while_running<F: Future, G>(request: F, path: &std::path::Path, guard: G) {
        let mut request = Box::pin(request);
        let fds = fds_to(path);
        let pending = std::future::poll_fn(|cx| {
            std::task::Poll::Ready(request.as_mut().poll(cx).is_pending())
        });
        assert!(pending.await);
        wait_for(|| fds_to(path) > fds);
        drop(request);
        drop(guard);
    }

    // An OPEN or CREATE that is dropped while a pool thread serves it, for
    // example for a takeover, releases the handle and the lookup count it
    // created.
    #[test]
    fn test_async_pool_dropped_open_create() {
        let (fs, source) = prepare_async_fs_shared(true);
        let ctx = prepare_context();
        let path = source.as_path().canonicalize().unwrap().join("file");
        std::fs::write(&path, b"").unwrap();
        let name = CString::new("file").unwrap();
        let inode = fs.lookup(&ctx, ROOT_ID, &name).unwrap().inode;
        let released = || {
            fs.handle_map.handles.read().unwrap().is_empty()
                && fs
                    .inode_map
                    .get(inode)
                    .unwrap()
                    .refcount
                    .load(Ordering::Acquire)
                    == 1
        };
        let flags = libc::O_RDWR as u32;
        let args = CreateIn {
            flags,
            mode: 0o600,
            umask: 0,
            fuse_flags: 0,
        };

        // Dropping the runtime waits for its pool threads, so one runtime
        // serves both requests.
        async_runtime::block_on(async {
            let open = fs.async_open(&ctx, inode, flags, 0);
            drop_while_running(open, &path, fs.handle_map.handles.read().unwrap()).await;
            wait_for(released);
            let create = fs.async_create(&ctx, ROOT_ID, &name, args);
            drop_while_running(create, &path, fs.handle_map.handles.read().unwrap()).await;
            wait_for(released);
        });
    }

    // A LOOKUP of a new inode that is dropped while a pool thread serves it
    // drops the lookup count it took.
    #[test]
    fn test_async_pool_dropped_lookup() {
        let (fs, source) = prepare_async_fs_shared(true);
        let ctx = prepare_context();
        let path = source.as_path().canonicalize().unwrap().join("file");
        std::fs::write(&path, b"").unwrap();
        let name = CString::new("file").unwrap();
        let fds = fds_to(&path);

        async_runtime::block_on(async {
            // The pool thread opens the file and then waits for the inode
            // map to insert the new inode.
            let lookup = fs.async_lookup(&ctx, ROOT_ID, &name);
            drop_while_running(lookup, &path, fs.inode_map.inodes.read().unwrap()).await;
            // The pool thread closes its file descriptor when the lookup
            // returns, or when the undo removes the inode it inserted.
            wait_for(|| fds_to(&path) == fds);
            // Once the undo has run, each lookup here takes the only count.
            wait_for(|| {
                let entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
                let data = fs.inode_map.get(entry.inode).unwrap();
                let count = data.refcount.load(Ordering::Acquire);
                fs.forget(&ctx, entry.inode, 1);
                count == 1
            });
        });
    }

    // With the thread pool enabled, READ and WRITE work on either runtime.
    // On tokio the pool serves the cache miss and the WRITE, which
    // tests/thread_pool.rs checks. With io_uring the native path serves them.
    // The pool serves the WRITE_KILL_PRIV write on both.
    #[test]
    fn test_async_pool_read_write() {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        // Negotiating HANDLE_KILLPRIV_V2 needs `do_import: false`.
        let cfg = Config {
            root_dir: source.as_path().to_str().unwrap().to_string(),
            do_import: false,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new_shared(cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::HANDLE_KILLPRIV_V2).unwrap();
        fs.enable_async_thread_pool(true);
        let ctx = prepare_context();
        let payload: Vec<u8> = (0..20000u32).map(|i| (i % 251) as u8).collect();
        // The WRITE_KILL_PRIV write replaces what the first write stored.
        let first: Vec<u8> = payload.iter().rev().copied().collect();
        let flags = libc::O_RDWR as u32;

        async_runtime::block_on(async {
            let name = CString::new("newfile").unwrap();
            let args = CreateIn {
                flags: (libc::O_RDWR | libc::O_CREAT | libc::O_TRUNC) as u32,
                mode: 0o644,
                umask: 0,
                fuse_flags: 0,
            };
            let (entry, handle, _opts) = fs.async_create(&ctx, ROOT_ID, &name, args).await.unwrap();
            let handle = handle.unwrap();

            for (fuse_flags, data) in [(0, &first), (WRITE_KILL_PRIV, &payload)] {
                let mut r = MemReader(data.clone());
                let n = fs
                    .async_write(
                        &ctx,
                        entry.inode,
                        handle,
                        &mut r,
                        payload.len() as u32,
                        0,
                        None,
                        false,
                        flags,
                        fuse_flags,
                    )
                    .await
                    .unwrap();
                assert_eq!(n, payload.len());
            }

            // The inline attempt misses right away.
            let mut w = PathRecorder::new(&payload, 0);
            let n = fs
                .async_read(
                    &ctx,
                    entry.inode,
                    handle,
                    &mut w,
                    payload.len() as u32,
                    0,
                    None,
                    flags,
                )
                .await
                .unwrap();
            assert_eq!(n, payload.len());
            assert_eq!(w.data, payload);
            // With io_uring the native path serves the miss, and on tokio the pool does.
            let native = !async_runtime::runtime_type().file_io_blocks();
            assert_eq!(w.events.iter().any(|e| e.0 == "async"), native);
        });

        assert_eq!(
            std::fs::read(source.as_path().join("newfile")).unwrap(),
            payload
        );
    }

    // A shared instance with the thread pool disabled serves its requests
    // inline.
    #[test]
    fn test_async_shared_pool_disabled() {
        let (fs, source) = prepare_async_fs_shared(false);
        let ctx = prepare_context();
        std::fs::write(source.as_path().join("testfile"), b"hello").unwrap();
        let name = CString::new("testfile").unwrap();

        async_runtime::block_on(async {
            let entry = fs.async_lookup(&ctx, ROOT_ID, &name).await.unwrap();
            let (attr, _) = fs.async_getattr(&ctx, entry.inode, None).await.unwrap();
            assert_eq!(attr.st_size, 5);
        });
    }

    // Regression test for async_fsyncdir() in `no_opendir` mode: the request must
    // be relayed to sync `fsyncdir()` (which reopens the directory inode) instead
    // of `fsync()` (which would fail to find a directory handle in the handle map).
    #[test]
    fn test_async_fsyncdir_no_opendir() {
        let (fs, _source) = prepare_async_fs();
        let ctx = prepare_context();
        fs.no_opendir.store(true, Ordering::Relaxed);

        async_runtime::block_on(fs.async_fsyncdir(&ctx, ROOT_ID, false, 0)).unwrap();
    }
}
