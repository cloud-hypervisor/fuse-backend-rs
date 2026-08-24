// Copyright (C) 2021-2022 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Asynchronous IO support for `PassthroughFs`.
//!
//! The asynchronous interface is implemented by relaying operations to the
//! synchronous io handlers, which execute blocking syscalls. By default the
//! handlers run inline in the context of the asynchronous runtime, which is
//! single-threaded: a blocking syscall stalls the processing of all other
//! requests. Calling `PassthroughFs::enable_async_thread_pool(true)`
//! instead offloads the handlers to the runtime's blocking thread pool,
//! so the async task can keep receiving and dispatching requests while
//! the syscalls execute in parallel on pool threads. An io_uring based
//! implementation may be added in the future.

use std::io;

use async_trait::async_trait;

use super::*;
use fuse_backend_core::abi::fuse_abi::{CreateIn, OpenOptions, SetattrValid};
use fuse_backend_core::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, FileSystem,
};
use fuse_backend_core::async_runtime::Runtime;

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
    /// `async_read()` and `async_write()` always execute inline, because
    /// the zero-copy reader and writer borrow the request and reply
    /// buffers of the fuse transport, which can't be moved to a pool
    /// thread.
    pub fn enable_async_thread_pool(&self, enable: bool) {
        self.async_thread_pool_enabled
            .store(enable, Ordering::Relaxed);
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
async fn join_blocking<T>(handle: tokio::task::JoinHandle<io::Result<T>>) -> io::Result<T> {
    match handle.await {
        Ok(res) => res,
        Err(e) if e.is_panic() => std::panic::resume_unwind(e.into_panic()),
        Err(e) => Err(io::Error::other(e)),
    }
}

/// Relay a synchronous handler according to the `async_thread_pool_enabled`
/// setting: offload it to the runtime's blocking thread pool if the setting
/// is enabled and the file system was created with `PassthroughFs::new_shared()`
/// (so the handler can hold a reference to it across threads), otherwise
/// execute it inline. `$capture` rebinds the borrowed request arguments to
/// owned copies which can be moved into the pool closure, and `$pool_fn`
/// is a `move` closure taking the file system and the request context by
/// value.
macro_rules! async_relay {
    ($self:expr, $ctx:expr, [$($capture:tt)*], $inline_call:expr, $pool_fn:expr) => {
        match $self.shared_ref.upgrade() {
            Some(fs) if $self.async_thread_pool_enabled.load(Ordering::Relaxed) => {
                let ctx = *$ctx;
                $($capture)*
                join_blocking(Runtime::spawn_blocking(move || ($pool_fn)(fs, ctx))).await
            }
            _ => $inline_call,
        }
    };
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
            move |fs: Arc<Self>, ctx: Context| fs.lookup(&ctx, parent, &name)
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
            move |fs: Arc<Self>, ctx: Context| {
                fs.open(&ctx, inode, flags, fuse_flags)
                    .map(|(handle, opts, _)| (handle, opts))
            }
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
            move |fs: Arc<Self>, ctx: Context| {
                fs.create(&ctx, parent, &name, args)
                    .map(|(entry, handle, opts, _)| (entry, handle, opts))
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
        lock_owner: Option<u64>,
        flags: u32,
    ) -> io::Result<usize> {
        // The writer borrows the reply buffer of the fuse transport, so the
        // request can't be offloaded to the blocking thread pool and is
        // always served inline.
        self.read(ctx, inode, handle, w, size, offset, lock_owner, flags)
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
        // The reader borrows the request buffer of the fuse transport, so the
        // request can't be offloaded to the blocking thread pool and is
        // always served inline.
        self.write(
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
        )
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
    use fuse_backend_core::file_buf::FileVolatileSlice;
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
            _f: Arc<dyn AsyncFileReadWriteVolatile>,
            _count: usize,
            _off: u64,
        ) -> io::Result<usize> {
            unreachable!("the synchronous delegation never uses the async zero-copy path")
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
            _f: Arc<dyn AsyncFileReadWriteVolatile>,
            _count: usize,
            _off: u64,
        ) -> io::Result<usize> {
            unreachable!("the synchronous delegation never uses the async zero-copy path")
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
