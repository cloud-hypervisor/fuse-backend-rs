// SPDX-License-Identifier: Apache-2.0

//! These tests read files of several sizes from a mount that sends READ replies with splice(2),
//! once with files that splice and once with files that can't, and check what the reads return.
//! `SyncFuseServing` serves the mount, and with `async-io` also `AsyncFuseServing`, on the
//! runtime that `FUSE_BACKEND_RS_ASYNC_RUNTIME` selects. Mounting needs root or fusermount3, and
//! the tests skip without either.

#[cfg(target_os = "linux")]
mod splice {
    use std::ffi::CStr;
    use std::fs::{File, OpenOptions as FileOptions};
    use std::io::{self, Read};
    use std::os::unix::fs::{FileExt, OpenOptionsExt};
    use std::os::unix::io::{AsRawFd, RawFd};
    use std::os::unix::net::UnixStream;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    use fuse_backend_core::abi::fuse_abi::{stat64, OpenOptions, ROOT_ID};
    use fuse_backend_core::api::filesystem::{Context, Entry, FileSystem, ZeroCopyWriter};
    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::file_buf::FileVolatileSlice;
    use fuse_backend_core::file_traits::FileReadWriteVolatile;
    use fuse_backend_fusedev::{FuseSession, SyncFuseServing, SyncServingConfig};
    use vmm_sys_util::tempdir::TempDir;

    const MIB: usize = 1 << 20;

    /// The test files and their sizes. `large` takes several READs of the largest size a READ
    /// can have, and `sparse` has a hole of 2 MiB between two pages of data.
    const FILES: [(&str, usize); 5] = [
        ("empty", 0),
        ("small", 100),
        ("unaligned", 5000),
        ("large", 3 * MIB + 123),
        ("sparse", 2 * MIB + 8192),
    ];

    /// Create the test files in `dir`, and return them with their contents.
    fn create_files(dir: &Path) -> Vec<(Arc<File>, Vec<u8>)> {
        FILES
            .iter()
            .map(|&(name, len)| {
                let mut data: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
                let path = dir.join(name);
                let file = File::create(&path).unwrap();
                if name == "sparse" {
                    data[4096..len - 4096].fill(0);
                    file.write_all_at(&data[..4096], 0).unwrap();
                    file.write_all_at(&data[len - 4096..], (len - 4096) as u64)
                        .unwrap();
                } else {
                    file.write_all_at(&data, 0).unwrap();
                }
                (Arc::new(File::open(&path).unwrap()), data)
            })
            .collect()
    }

    /// What the transport did with the files of a `SpliceFs`.
    #[derive(Default)]
    struct Stats {
        /// How many times the transport asked for the file descriptor of a file.
        fd_calls: AtomicUsize,
        /// How many times the transport read a file into memory.
        copies: AtomicUsize,
    }

    /// Serves the files of `create_files()`: each by its name, from the page cache, and by its
    /// name with `.direct`, with direct IO. Reads go through `ZeroCopyWriter::write_from()`, and
    /// with `async_write_from` through `AsyncZeroCopyWriter::async_write_from()`.
    struct SpliceFs {
        files: Vec<(Arc<File>, Vec<u8>)>,
        /// A socket that `raw_fd()` returns instead of the file, so that splice() fails.
        unspliceable: Option<UnixStream>,
        #[cfg_attr(not(feature = "async-io"), allow(dead_code))]
        async_write_from: bool,
        stats: Arc<Stats>,
    }

    /// The file that `SpliceFs` hands to the transport.
    struct ReadFile {
        file: Arc<File>,
        /// What `raw_fd()` returns, which the `SpliceFs` keeps open.
        fd: RawFd,
        stats: Arc<Stats>,
    }

    impl ReadFile {
        fn fd(&self) -> Option<RawFd> {
            self.stats.fd_calls.fetch_add(1, Ordering::Relaxed);
            Some(self.fd)
        }
    }

    impl FileReadWriteVolatile for ReadFile {
        fn raw_fd(&self) -> Option<RawFd> {
            self.fd()
        }

        fn read_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        fn write_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        fn read_at_volatile(&mut self, slice: FileVolatileSlice, off: u64) -> io::Result<usize> {
            self.stats.copies.fetch_add(1, Ordering::Relaxed);
            self.file.try_clone()?.read_at_volatile(slice, off)
        }

        fn write_at_volatile(&mut self, _slice: FileVolatileSlice, _off: u64) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }
    }

    impl SpliceFs {
        /// The index in `files` of `inode`, and whether it's the direct IO name.
        fn file_of(inode: u64) -> (usize, bool) {
            ((inode as usize - 2) / 2, inode % 2 == 1)
        }

        fn read_file(&self, inode: u64) -> ReadFile {
            let file = self.files[Self::file_of(inode).0].0.clone();
            ReadFile {
                fd: self
                    .unspliceable
                    .as_ref()
                    .map_or(file.as_raw_fd(), |s| s.as_raw_fd()),
                file,
                stats: self.stats.clone(),
            }
        }

        fn stat(&self, inode: u64) -> stat64 {
            let mut st: stat64 = unsafe { std::mem::zeroed() };
            st.st_ino = inode;
            st.st_nlink = 1;
            if inode == ROOT_ID {
                st.st_mode = libc::S_IFDIR | 0o755;
            } else {
                st.st_mode = libc::S_IFREG | 0o444;
                st.st_size = self.files[Self::file_of(inode).0].1.len() as i64;
            }
            st
        }
    }

    #[allow(unused_variables)]
    impl FileSystem for SpliceFs {
        type Inode = u64;
        type Handle = u64;

        fn lookup(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            let name = name.to_str().unwrap();
            let (base, direct) = match name.strip_suffix(".direct") {
                Some(base) => (base, 1),
                None => (name, 0),
            };
            let index = FILES
                .iter()
                .position(|&(n, _)| n == base)
                .ok_or_else(|| io::Error::from_raw_os_error(libc::ENOENT))?;
            let inode = 2 + 2 * index as u64 + direct;
            Ok(Entry {
                inode,
                generation: 0,
                attr: self.stat(inode),
                attr_flags: 0,
                attr_timeout: Duration::from_secs(60),
                entry_timeout: Duration::from_secs(60),
            })
        }

        fn getattr(
            &self,
            ctx: &Context,
            inode: u64,
            handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            Ok((self.stat(inode), Duration::from_secs(60)))
        }

        fn open(
            &self,
            ctx: &Context,
            inode: u64,
            flags: u32,
            fuse_flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
            let opts = match Self::file_of(inode).1 {
                true => OpenOptions::DIRECT_IO,
                false => OpenOptions::empty(),
            };
            Ok((Some(inode), opts, None))
        }

        fn read(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            w: &mut dyn ZeroCopyWriter,
            size: u32,
            offset: u64,
            lock_owner: Option<u64>,
            flags: u32,
        ) -> io::Result<usize> {
            w.write_from(&mut self.read_file(inode), size as usize, offset)
        }

        fn release(
            &self,
            ctx: &Context,
            inode: u64,
            flags: u32,
            handle: u64,
            flush: bool,
            flock_release: bool,
            lock_owner: Option<u64>,
        ) -> io::Result<()> {
            Ok(())
        }
    }

    /// A way to read a whole file.
    type ReadFn = fn(&Path) -> io::Result<Vec<u8>>;

    /// Read the file at `path` with `O_DIRECT`.
    fn read_direct(path: &Path) -> io::Result<Vec<u8>> {
        let mut file = FileOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECT)
            .open(path)?;
        let mut out = Vec::new();
        file.read_to_end(&mut out)?;
        Ok(out)
    }

    /// Mount a session that splices READ replies, serve it with `serve`, and read every file
    /// through the page cache, with `O_DIRECT` and with direct IO. Checks what the reads return,
    /// and returns the statistics of the file system, or `None` if it can't mount.
    fn read_files<S>(
        unspliceable: Option<UnixStream>,
        async_write_from: bool,
        serve: impl FnOnce(FuseSession, Arc<SpliceFs>) -> S,
    ) -> Option<Arc<Stats>> {
        let src = TempDir::new().unwrap();
        let fs = Arc::new(SpliceFs {
            files: create_files(src.as_path()),
            unspliceable,
            async_write_from,
            stats: Arc::default(),
        });
        let mnt = TempDir::new().unwrap();
        let mut se = FuseSession::new(mnt.as_path(), "splice_test", "", true).unwrap();
        se.set_allow_other(false);
        se.set_splice_write(true);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return None;
        }
        let serving = serve(se, fs.clone());

        for (&(name, _), (_, data)) in FILES.iter().zip(&fs.files) {
            let reads: [(String, ReadFn); 3] = [
                (name.to_string(), |p| std::fs::read(p)),
                (name.to_string(), read_direct),
                (format!("{name}.direct"), |p| std::fs::read(p)),
            ];
            for (path, read) in reads {
                let path: PathBuf = mnt.as_path().join(path);
                let (tx, rx) = channel();
                let p = path.clone();
                thread::spawn(move || tx.send(read(&p)));
                let read = rx
                    .recv_timeout(Duration::from_secs(30))
                    .unwrap_or_else(|_| panic!("reading {:?} hangs", path))
                    .unwrap();
                assert!(read == *data, "{:?} returned other data", path);
            }
        }
        drop(serving);
        Some(fs.stats.clone())
    }

    /// Serve with one sync worker, so that its pipes serve every READ.
    fn serve_sync(se: FuseSession, fs: Arc<SpliceFs>) -> SyncFuseServing<Arc<SpliceFs>> {
        let cfg = SyncServingConfig {
            workers: 1,
            blocking: false,
        };
        SyncFuseServing::new(se, Arc::new(Server::new(fs)), cfg).unwrap()
    }

    /// Whether this process can grow a pipe to 2 MiB, which a READ of 1 MiB needs.
    fn big_pipes() -> bool {
        let (_r, w) = nix::unistd::pipe().unwrap();
        nix::fcntl::fcntl(&w, nix::fcntl::FcntlArg::F_SETPIPE_SZ(2 * MIB as i32)).is_ok()
    }

    /// Check that the transport spliced every READ.
    fn assert_spliced(stats: &Stats) {
        assert!(stats.fd_calls.load(Ordering::Relaxed) > 0);
        if big_pipes() {
            assert_eq!(stats.copies.load(Ordering::Relaxed), 0);
        } else {
            eprintln!("pipes can't hold a READ of 1 MiB, so those READs were copied");
        }
    }

    /// Check that the transport asked for a descriptor `fd_calls` times, and copied the READs.
    /// With one, the first READ failed to splice, and the transport copied from then on.
    fn assert_copied(stats: &Stats, fd_calls: usize) {
        assert_eq!(stats.fd_calls.load(Ordering::Relaxed), fd_calls);
        assert!(stats.copies.load(Ordering::Relaxed) > FILES.len());
    }

    #[test]
    fn test_splice_read_replies() {
        if let Some(stats) = read_files(None, false, serve_sync) {
            assert_spliced(&stats);
        }
    }

    #[test]
    fn test_splice_read_replies_fall_back() {
        let sock = UnixStream::pair().unwrap().0;
        if let Some(stats) = read_files(Some(sock), false, serve_sync) {
            assert_copied(&stats, 1);
        }
    }

    #[cfg(feature = "async-io")]
    mod async_io {
        use std::future::Future;
        use std::pin::Pin;
        use std::task::{Context as TaskContext, Poll};

        use async_trait::async_trait;
        use fuse_backend_core::api::filesystem::{AsyncFileSystem, AsyncZeroCopyWriter};
        use fuse_backend_core::async_file::File as AsyncFile;
        use fuse_backend_core::async_runtime;
        use fuse_backend_core::file_buf::FileVolatileBuf;
        use fuse_backend_core::file_traits::AsyncFileReadWriteVolatile;
        use fuse_backend_fusedev::{AsyncFuseServing, AsyncServingConfig};

        use super::*;

        #[async_trait(?Send)]
        impl AsyncFileReadWriteVolatile for ReadFile {
            fn raw_fd(&self) -> Option<RawFd> {
                self.fd()
            }

            async fn async_read_at_volatile(
                &self,
                buf: FileVolatileBuf,
                off: u64,
            ) -> (io::Result<usize>, FileVolatileBuf) {
                self.stats.copies.fetch_add(1, Ordering::Relaxed);
                let file = AsyncFile::borrow_fd(self.file.as_raw_fd(), self.file.clone());
                file.async_read_at(buf, off).await
            }

            async fn async_read_vectored_at_volatile(
                &self,
                bufs: Vec<FileVolatileBuf>,
                _off: u64,
            ) -> (io::Result<usize>, Vec<FileVolatileBuf>) {
                (Err(io::Error::from_raw_os_error(libc::ENOSYS)), bufs)
            }

            async fn async_write_at_volatile(
                &self,
                buf: FileVolatileBuf,
                _off: u64,
            ) -> (io::Result<usize>, FileVolatileBuf) {
                (Err(io::Error::from_raw_os_error(libc::ENOSYS)), buf)
            }

            async fn async_write_vectored_at_volatile(
                &self,
                bufs: Vec<FileVolatileBuf>,
                _off: u64,
            ) -> (io::Result<usize>, Vec<FileVolatileBuf>) {
                (Err(io::Error::from_raw_os_error(libc::ENOSYS)), bufs)
            }
        }

        /// The future of `async_write_from()` isn't `Send`, which `AsyncFileSystem` needs.
        struct AssertSend<F>(F);

        // SAFETY: a worker of `AsyncFuseServing` serves each request on its own thread, as
        // `PassthroughFs` relies on too.
        unsafe impl<F> Send for AssertSend<F> {}

        impl<F: Future + Unpin> Future for AssertSend<F> {
            type Output = F::Output;

            fn poll(mut self: Pin<&mut Self>, cx: &mut TaskContext<'_>) -> Poll<F::Output> {
                Pin::new(&mut self.0).poll(cx)
            }
        }

        #[async_trait]
        impl AsyncFileSystem for SpliceFs {
            #[allow(clippy::too_many_arguments)]
            async fn async_read(
                &self,
                ctx: &Context,
                inode: u64,
                handle: u64,
                w: &mut (dyn AsyncZeroCopyWriter + Send),
                size: u32,
                offset: u64,
                lock_owner: Option<u64>,
                flags: u32,
            ) -> io::Result<usize> {
                if !self.async_write_from {
                    return self.read(ctx, inode, handle, w, size, offset, lock_owner, flags);
                }
                let file: Arc<dyn AsyncFileReadWriteVolatile> = Arc::new(self.read_file(inode));
                AssertSend(w.async_write_from(file, size as usize, offset)).await
            }
        }

        /// Serve with one async worker.
        fn serve_async(se: FuseSession, fs: Arc<SpliceFs>) -> AsyncFuseServing<Arc<SpliceFs>> {
            let cfg = AsyncServingConfig {
                workers: 1,
                max_inflight: 0,
            };
            AsyncFuseServing::new(se, Arc::new(Server::new(fs)), cfg).unwrap()
        }

        /// Whether `async_write_from()` splices on the runtime of this process. It does where
        /// the read it replaces would block the runtime thread too.
        fn async_splices() -> bool {
            async_runtime::runtime_type().file_io_blocks()
        }

        #[test]
        fn test_async_splice_read_replies() {
            let Some(stats) = read_files(None, true, serve_async) else {
                return;
            };
            if async_splices() {
                assert_spliced(&stats);
            } else {
                assert_copied(&stats, 0);
            }
        }

        #[test]
        fn test_async_splice_read_replies_from_sync_handler() {
            if let Some(stats) = read_files(None, false, serve_async) {
                assert_spliced(&stats);
            }
        }

        #[test]
        fn test_async_splice_read_replies_fall_back() {
            for async_write_from in [false, true] {
                let sock = UnixStream::pair().unwrap().0;
                let Some(stats) = read_files(Some(sock), async_write_from, serve_async) else {
                    return;
                };
                // The requests in flight share the switch that turns splicing off.
                let tries = !async_write_from || async_splices();
                assert_copied(&stats, tries as usize);
            }
        }
    }
}
