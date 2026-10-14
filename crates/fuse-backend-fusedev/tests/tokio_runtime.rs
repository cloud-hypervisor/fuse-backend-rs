// SPDX-License-Identifier: Apache-2.0

//! These tests serve a mount with `FuseDevTask` on a tokio runtime they build themselves, or
//! without any tokio runtime. The crate fixes the runtime type once per process, so these tests
//! run in a binary of their own. Mounting needs root or fusermount3, and the tests skip without
//! either.

#[cfg(all(target_os = "linux", feature = "async-io"))]
mod tokio_runtime {
    use std::ffi::CStr;
    use std::fs::File;
    use std::io;
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::io::AsRawFd;
    use std::path::Path;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::mpsc::{channel, Receiver};
    use std::sync::{Arc, Condvar, Mutex};
    use std::thread;
    use std::time::Duration;

    use async_trait::async_trait;
    use fuse_backend_core::abi::fuse_abi::{stat64, CreateIn, FsOptions, OpenOptions, ROOT_ID};
    use fuse_backend_core::api::filesystem::{
        AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, Entry, FileSystem,
        SetattrValid, ZeroCopyWriter,
    };
    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::async_runtime::{self, RuntimeType};
    use fuse_backend_fusedev::{
        FuseDevTask, FuseDevWriter, FuseSession, SyncFuseServing, SyncServingConfig,
    };
    use fuse_backend_passthrough::{Config, PassthroughFs};
    use tokio::sync::{oneshot, Semaphore};
    use vmm_sys_util::tempdir::TempDir;

    /// CPU time used by the calling thread.
    fn thread_cpu_time() -> Duration {
        let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
        assert_eq!(
            unsafe { libc::getrusage(libc::RUSAGE_THREAD, &mut usage) },
            0
        );
        let tv = |t: libc::timeval| Duration::new(t.tv_sec as u64, t.tv_usec as u32 * 1000);
        tv(usage.ru_utime) + tv(usage.ru_stime)
    }

    /// Drive `future` on the calling thread, without a tokio runtime.
    fn block_on_without_tokio<F: std::future::Future>(future: F) -> F::Output {
        use std::task::{Context, Poll, Wake, Waker};

        struct Unpark(thread::Thread);
        impl Wake for Unpark {
            fn wake(self: Arc<Self>) {
                self.0.unpark();
            }
        }

        let mut future = std::pin::pin!(future);
        let waker = Waker::from(Arc::new(Unpark(thread::current())));
        let mut cx = Context::from_waker(&waker);
        loop {
            if let Poll::Ready(output) = future.as_mut().poll(&mut cx) {
                return output;
            }
            thread::park();
        }
    }

    #[test]
    fn test_fuse_dev_task_without_tokio_runtime() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"served without tokio").unwrap();
        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        let server = Arc::new(Server::new(fs));

        let mnt = TempDir::new().unwrap();
        let mut se = FuseSession::new(mnt.as_path(), "tokio_runtime_test", "", false).unwrap();
        se.set_allow_other(false);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return;
        }
        let file = se.clone_fuse_file().unwrap();
        let buf_size = se.bufsize();

        // Without a tokio runtime the task can't wait for requests, but it still serves them.
        let handle = thread::spawn(move || {
            let state = Arc::new(AtomicBool::new(false));
            let mut task = FuseDevTask::new(buf_size, file, server, state);
            block_on_without_tokio(task.poll_handler());
        });
        let path = mnt.as_path().join("hello");
        let read = in_thread(move || std::fs::read(path)).recv_timeout(Duration::from_secs(5));
        se.umount().unwrap();
        let served = handle.join();
        assert!(
            served.is_ok(),
            "poll_handler() panicked without a tokio runtime"
        );
        assert_eq!(read.unwrap().unwrap(), b"served without tokio");
    }

    #[test]
    fn test_fuse_dev_task_stops_while_idle() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let src = TempDir::new().unwrap();
        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        let server = Arc::new(Server::new(fs));

        let mnt = TempDir::new().unwrap();
        let Some(mut se) = mount(mnt.as_path()) else {
            return;
        };
        let file = se.clone_fuse_file().unwrap();
        let buf_size = se.bufsize();

        let state = Arc::new(AtomicBool::new(false));
        let task_state = state.clone();
        let (tx, rx) = channel();
        let handle = thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap();
            let mut task = FuseDevTask::new(buf_size, file, server, task_state);
            rt.block_on(task.poll_handler());
            tx.send(()).unwrap();
        });

        std::fs::read_dir(mnt.as_path()).unwrap().for_each(drop);
        // The connection stays up, so only the state flag can stop the idle task.
        state.store(true, Ordering::Release);
        let stopped = rx.recv_timeout(Duration::from_secs(5));
        se.umount().unwrap();
        handle.join().unwrap();
        assert!(stopped.is_ok(), "the idle task ignored its state flag");
    }

    #[test]
    fn test_fuse_dev_task_on_tokio() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let src = TempDir::new().unwrap();
        std::fs::write(src.as_path().join("hello"), b"served by tokio").unwrap();
        let fs = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        let server = Arc::new(Server::new(fs));

        let mnt = TempDir::new().unwrap();
        let Some(mut se) = mount(mnt.as_path()) else {
            return;
        };
        let file = se.clone_fuse_file().unwrap();
        let buf_size = se.bufsize();

        let (tx, rx) = channel();
        let handle = thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap();
            let state = Arc::new(AtomicBool::new(false));
            let mut task = FuseDevTask::new_with_max_inflight(buf_size, file, server, state, 4);
            rt.block_on(task.poll_handler());
            tx.send(thread_cpu_time()).unwrap();
        });

        assert_eq!(
            std::fs::read(mnt.as_path().join("hello")).unwrap(),
            b"served by tokio"
        );
        // An idle task waits for requests instead of retrying reads in a loop.
        thread::sleep(Duration::from_millis(500));

        // Unmounting tears the connection down, which must wake the task.
        se.umount().unwrap();
        let cpu = rx.recv_timeout(Duration::from_secs(5)).unwrap();
        handle.join().unwrap();
        assert!(
            cpu < Duration::from_millis(200),
            "serving used {:?} of CPU",
            cpu
        );
    }

    fn mount(mountpoint: &Path) -> Option<FuseSession> {
        let mut se = FuseSession::new(mountpoint, "tokio_runtime_test", "", false).unwrap();
        se.set_allow_other(false);
        match se.mount() {
            Ok(()) => Some(se),
            Err(e) => {
                eprintln!("can't mount ({}), skipping", e);
                None
            }
        }
    }

    /// Run `f` in a thread of its own and send its result.
    fn in_thread<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> Receiver<T> {
        let (tx, rx) = channel();
        thread::spawn(move || {
            let _ = tx.send(f());
        });
        rx
    }

    const FAST: u64 = 2;
    const SLOW: u64 = 3;

    /// A root directory with the files `fast` and `slow`. Looking up `slow` waits for a permit
    /// from `gate`, or forever with `stall`.
    #[derive(Default)]
    struct TestFs {
        gate: Option<Arc<Semaphore>>,
        stall: bool,
        fast_lookups: AtomicUsize,
        has_resend: AtomicBool,
    }

    fn stat(inode: u64) -> stat64 {
        let mut st: stat64 = unsafe { std::mem::zeroed() };
        st.st_ino = inode;
        st.st_nlink = 1;
        st.st_mode = if inode == ROOT_ID {
            libc::S_IFDIR | 0o755
        } else {
            libc::S_IFREG | 0o444
        };
        st
    }

    fn entry(inode: u64) -> Entry {
        Entry {
            inode,
            generation: 0,
            attr: stat(inode),
            attr_flags: 0,
            attr_timeout: Duration::from_secs(60),
            entry_timeout: Duration::from_secs(60),
        }
    }

    fn enosys<T>() -> io::Result<T> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    impl FileSystem for TestFs {
        type Inode = u64;
        type Handle = u64;

        fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
            self.has_resend
                .store(capable.contains(FsOptions::HAS_RESEND), Ordering::Relaxed);
            // Without PARALLEL_DIROPS, the kernel serializes lookups in a directory.
            Ok(capable & (FsOptions::HAS_RESEND | FsOptions::PARALLEL_DIROPS))
        }
    }

    #[allow(unused_variables)]
    #[async_trait]
    impl AsyncFileSystem for TestFs {
        async fn async_lookup(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            match name.to_bytes() {
                b"fast" => {
                    self.fast_lookups.fetch_add(1, Ordering::Relaxed);
                    Ok(entry(FAST))
                }
                b"slow" => {
                    if self.stall {
                        std::future::pending::<()>().await;
                    }
                    if let Some(gate) = &self.gate {
                        gate.acquire().await.unwrap().forget();
                    }
                    Ok(entry(SLOW))
                }
                _ => Err(io::Error::from_raw_os_error(libc::ENOENT)),
            }
        }

        async fn async_getattr(
            &self,
            ctx: &Context,
            inode: u64,
            handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            Ok((stat(inode), Duration::from_secs(60)))
        }

        async fn async_setattr(
            &self,
            ctx: &Context,
            inode: u64,
            attr: stat64,
            handle: Option<u64>,
            valid: SetattrValid,
        ) -> io::Result<(stat64, Duration)> {
            enosys()
        }

        async fn async_open(
            &self,
            ctx: &Context,
            inode: u64,
            flags: u32,
            fuse_flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions)> {
            enosys()
        }

        async fn async_create(
            &self,
            ctx: &Context,
            parent: u64,
            name: &CStr,
            args: CreateIn,
        ) -> io::Result<(Entry, Option<u64>, OpenOptions)> {
            enosys()
        }

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
            enosys()
        }

        async fn async_write(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            r: &mut (dyn AsyncZeroCopyReader + Send),
            size: u32,
            offset: u64,
            lock_owner: Option<u64>,
            delayed_write: bool,
            flags: u32,
            fuse_flags: u32,
        ) -> io::Result<usize> {
            enosys()
        }

        async fn async_fsync(
            &self,
            ctx: &Context,
            inode: u64,
            datasync: bool,
            handle: u64,
        ) -> io::Result<()> {
            enosys()
        }

        async fn async_fallocate(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            mode: u32,
            offset: u64,
            length: u64,
        ) -> io::Result<()> {
            enosys()
        }

        async fn async_fsyncdir(
            &self,
            ctx: &Context,
            inode: u64,
            datasync: bool,
            handle: u64,
        ) -> io::Result<()> {
            enosys()
        }
    }

    /// Serve `file` with `server` on a tokio runtime of its own until the task returns or `stop`
    /// completes. Stopping drops the requests in flight.
    fn serve<F: AsyncFileSystem + Send + Sync + 'static>(
        file: File,
        buf_size: usize,
        server: Arc<Server<F>>,
        stop: oneshot::Receiver<()>,
    ) -> thread::JoinHandle<()> {
        thread::spawn(move || {
            let rt = tokio::runtime::Builder::new_current_thread()
                .enable_all()
                .build()
                .unwrap();
            let state = Arc::new(AtomicBool::new(false));
            let mut task = FuseDevTask::new_with_max_inflight(buf_size, file, server, state, 4);
            rt.block_on(async {
                tokio::select! {
                    _ = task.poll_handler() => {}
                    _ = stop => {}
                }
            });
        })
    }

    #[test]
    fn test_fuse_dev_task_concurrent_lookups_and_notify() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let mnt = TempDir::new().unwrap();
        let Some(mut se) = mount(mnt.as_path()) else {
            return;
        };
        let gate = Arc::new(Semaphore::new(0));
        let fs = Arc::new(TestFs {
            gate: Some(gate.clone()),
            ..Default::default()
        });
        let server = Arc::new(Server::new(fs.clone()));
        let (_stop_tx, stop) = oneshot::channel();
        let handle = serve(
            se.clone_fuse_file().unwrap(),
            se.bufsize(),
            server.clone(),
            stop,
        );

        let path = mnt.as_path().join("slow");
        let slow = in_thread(move || std::fs::metadata(path).unwrap().ino());
        thread::sleep(Duration::from_millis(100));

        // A lookup waiting in the file system doesn't hold up the others.
        let fast = std::fs::metadata(mnt.as_path().join("fast")).unwrap();
        assert_eq!(fast.ino(), FAST);
        assert!(slow.try_recv().is_err());
        gate.add_permits(1);
        assert_eq!(slow.recv_timeout(Duration::from_secs(5)).unwrap(), SLOW);

        // Invalidate the cached entry while the task serves, so the next stat looks it up again.
        assert_eq!(fs.fast_lookups.load(Ordering::Relaxed), 1);
        let notify_file = se.clone_fuse_file().unwrap();
        let mut buf = vec![0u8; 0x1000];
        let writer = FuseDevWriter::<()>::new(notify_file.as_raw_fd(), &mut buf).unwrap();
        server
            .notify_inval_entry(
                writer,
                ROOT_ID,
                CStr::from_bytes_with_nul(b"fast\0").unwrap(),
            )
            .unwrap();
        std::fs::metadata(mnt.as_path().join("fast")).unwrap();
        assert_eq!(fs.fast_lookups.load(Ordering::Relaxed), 2);

        se.umount().unwrap();
        handle.join().unwrap();
    }

    #[test]
    fn test_fuse_dev_task_takeover() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let mnt = TempDir::new().unwrap();
        let Some(mut se) = mount(mnt.as_path()) else {
            return;
        };
        let buf_size = se.bufsize();

        // The old server stalls on `slow` and stops with the lookup in flight.
        let old_fs = Arc::new(TestFs {
            stall: true,
            ..Default::default()
        });
        let old = Arc::new(Server::new(old_fs.clone()));
        // The kernel ends the requests read from a file description when it is closed. A
        // takeover passes that description to the new server, so the test keeps it open.
        let file = se.clone_fuse_file().unwrap();
        let (stop_tx, stop) = oneshot::channel();
        let old_handle = serve(file.try_clone().unwrap(), buf_size, old.clone(), stop);

        std::fs::metadata(mnt.as_path().join("fast")).unwrap();
        if !old_fs.has_resend.load(Ordering::Relaxed) {
            eprintln!("kernel without FUSE_NOTIFY_RESEND, skipping");
            se.umount().unwrap();
            drop(stop_tx);
            old_handle.join().unwrap();
            return;
        }
        let path = mnt.as_path().join("slow");
        let slow = in_thread(move || std::fs::metadata(path).unwrap().ino());
        thread::sleep(Duration::from_millis(100));
        stop_tx.send(()).unwrap();
        old_handle.join().unwrap();
        let (version, options) = old.init_state();
        assert!(options.contains(FsOptions::HAS_RESEND));

        // The new server serves the same connection without INIT and gets the lookup again. The
        // test sends the resend before the new server reads, so the kernel doesn't send again a
        // request that the new server is handling.
        let new = Arc::new(Server::new(Arc::new(TestFs::default())));
        new.restore_init(version, options);
        let mut buf = vec![0u8; 0x1000];
        let writer = FuseDevWriter::<()>::new(file.as_raw_fd(), &mut buf).unwrap();
        new.notify_resend(writer).unwrap();
        let (_stop_tx, stop) = oneshot::channel();
        let new_handle = serve(file.try_clone().unwrap(), buf_size, new.clone(), stop);
        assert_eq!(slow.recv_timeout(Duration::from_secs(5)).unwrap(), SLOW);

        se.umount().unwrap();
        new_handle.join().unwrap();
    }

    /// Size of the files of `SlowFs`.
    const SLOW_FS_FILE_SIZE: usize = 64 << 10;

    /// The content of the files of `SlowFs`.
    fn slow_fs_data() -> Vec<u8> {
        (0..SLOW_FS_FILE_SIZE).map(|i| (i % 251) as u8).collect()
    }

    /// A root directory with the files `fast` and `slow`, which `SyncFuseServing` serves. Reading
    /// `slow` waits until the gate opens. The files are direct IO, so every read reaches the file
    /// system.
    #[derive(Default)]
    struct SlowFs {
        gate: Mutex<bool>,
        opened: Condvar,
        slow_reads: AtomicUsize,
        has_resend: AtomicBool,
    }

    impl SlowFs {
        fn open_gate(&self) {
            *self.gate.lock().unwrap() = true;
            self.opened.notify_all();
        }

        /// Wait until `n` reads of `slow` have started.
        fn wait_for_slow_reads(&self, n: usize) {
            for _ in 0..500 {
                if self.slow_reads.load(Ordering::Acquire) >= n {
                    return;
                }
                thread::sleep(Duration::from_millis(10));
            }
            panic!("the file system got no read of slow");
        }

        fn stat(inode: u64) -> stat64 {
            let mut st = stat(inode);
            if inode != ROOT_ID {
                st.st_size = SLOW_FS_FILE_SIZE as i64;
            }
            st
        }
    }

    #[allow(unused_variables)]
    impl FileSystem for SlowFs {
        type Inode = u64;
        type Handle = u64;

        fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
            self.has_resend
                .store(capable.contains(FsOptions::HAS_RESEND), Ordering::Relaxed);
            Ok(FsOptions::empty())
        }

        fn lookup(&self, ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            let inode = match name.to_bytes() {
                b"fast" => FAST,
                b"slow" => SLOW,
                _ => return Err(io::Error::from_raw_os_error(libc::ENOENT)),
            };
            Ok(Entry {
                attr: Self::stat(inode),
                ..entry(inode)
            })
        }

        fn forget(&self, ctx: &Context, inode: u64, count: u64) {}

        fn getattr(
            &self,
            ctx: &Context,
            inode: u64,
            handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            Ok((Self::stat(inode), Duration::from_secs(60)))
        }

        fn open(
            &self,
            ctx: &Context,
            inode: u64,
            flags: u32,
            fuse_flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
            Ok((Some(inode), OpenOptions::DIRECT_IO, None))
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
            if inode == SLOW {
                self.slow_reads.fetch_add(1, Ordering::AcqRel);
                let mut open = self.gate.lock().unwrap();
                while !*open {
                    open = self.opened.wait(open).unwrap();
                }
            }
            let data = slow_fs_data();
            let start = std::cmp::min(offset as usize, data.len());
            let end = std::cmp::min(start + size as usize, data.len());
            w.write_all(&data[start..end])?;
            Ok(end - start)
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

    /// A mounted `SlowFs`, and an unserved mount for a `PassthroughFs` of it. Dropping it opens
    /// the gate first, so a failing test doesn't leave reads waiting. Then the fields drop in
    /// order, so the upper mount, and the files that `fs` holds open in the lower mount, go away
    /// before the lower mount.
    struct SlowFsStack {
        upper_se: FuseSession,
        fs: Arc<PassthroughFs<()>>,
        _lower: SyncFuseServing<Arc<SlowFs>>,
        slow_fs: Arc<SlowFs>,
    }

    impl Drop for SlowFsStack {
        fn drop(&mut self) {
            self.slow_fs.open_gate();
        }
    }

    /// Mount a `SlowFs` at `lower`, served by threads of its own, and create a `PassthroughFs`
    /// of it with the blocking thread pool enabled, for a mount at `upper`.
    fn mount_passthrough_of_slow_fs(lower: &Path, upper: &Path) -> Option<SlowFsStack> {
        let slow_fs = Arc::new(SlowFs::default());
        let lower_se = mount(lower)?;
        let serving = SyncFuseServing::new(
            lower_se,
            Arc::new(Server::new(slow_fs.clone())),
            SyncServingConfig {
                workers: 4,
                blocking: false,
            },
        )
        .unwrap();
        let fs = PassthroughFs::<()>::new_shared(Config {
            root_dir: lower.to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        fs.import().unwrap();
        fs.enable_async_thread_pool(true);
        let upper_se = mount(upper)?;
        Some(SlowFsStack {
            upper_se,
            fs,
            _lower: serving,
            slow_fs,
        })
    }

    /// With the thread pool, a READ that waits for the backing file doesn't hold up the other
    /// requests on the current-thread runtime.
    #[test]
    fn test_passthrough_pool_serves_while_read_waits() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let lower = TempDir::new().unwrap();
        let upper = TempDir::new().unwrap();
        let Some(mut stack) = mount_passthrough_of_slow_fs(lower.as_path(), upper.as_path()) else {
            return;
        };
        let (_stop_tx, stop) = oneshot::channel();
        let handle = serve(
            stack.upper_se.clone_fuse_file().unwrap(),
            stack.upper_se.bufsize(),
            Arc::new(Server::new(stack.fs.clone())),
            stop,
        );

        let path = upper.as_path().join("slow");
        let slow = in_thread(move || std::fs::read(path));
        stack.slow_fs.wait_for_slow_reads(1);
        // Without the pool, the runtime thread waits for the gate, which opens 2s from now.
        let backstop = stack.slow_fs.clone();
        thread::spawn(move || {
            thread::sleep(Duration::from_secs(2));
            backstop.open_gate();
        });
        let start = std::time::Instant::now();
        let fast = std::fs::read(upper.as_path().join("fast")).unwrap();
        let elapsed = start.elapsed();
        eprintln!("reading fast while slow waits took {:?}", elapsed);
        assert_eq!(fast, slow_fs_data());
        assert!(
            elapsed < Duration::from_secs(1),
            "reading fast took {:?}",
            elapsed
        );
        assert!(slow.try_recv().is_err());

        stack.slow_fs.open_gate();
        let slow = slow.recv_timeout(Duration::from_secs(5)).unwrap().unwrap();
        assert_eq!(slow, slow_fs_data());

        stack.upper_se.umount().unwrap();
        handle.join().unwrap();
    }

    /// A server that stops with a READ waiting on a pool thread frees the request's buffer while
    /// the pool thread still reads. The pool thread reads into a buffer of its own, and a new
    /// server answers the READ that the kernel sends again.
    #[test]
    fn test_passthrough_pool_read_survives_takeover() {
        async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

        let lower = TempDir::new().unwrap();
        let upper = TempDir::new().unwrap();
        let Some(mut stack) = mount_passthrough_of_slow_fs(lower.as_path(), upper.as_path()) else {
            return;
        };
        // `import()` stat'ed the root of the lower mount, which waited for its INIT.
        if !stack.slow_fs.has_resend.load(Ordering::Relaxed) {
            eprintln!("kernel without FUSE_NOTIFY_RESEND, skipping");
            return;
        }
        let buf_size = stack.upper_se.bufsize();
        // The kernel ends the requests read from a file description when it is closed, so the
        // test keeps the one the old server reads from, as a takeover passes it to the new one.
        let file = stack.upper_se.clone_fuse_file().unwrap();
        let old = Arc::new(Server::new(stack.fs.clone()));
        let (stop_tx, stop) = oneshot::channel();
        let old_handle = serve(file.try_clone().unwrap(), buf_size, old.clone(), stop);

        let path = upper.as_path().join("slow");
        let slow = in_thread(move || std::fs::read(path));
        stack.slow_fs.wait_for_slow_reads(1);
        // Dropping poll_handler() frees the request buffers. The runtime then waits for its pool
        // threads when it shuts down, so the old serving thread ends only after the gate opens.
        stop_tx.send(()).unwrap();
        thread::sleep(Duration::from_millis(100));

        let new = Arc::new(Server::new(stack.fs.clone()));
        let (version, options) = old.init_state();
        new.restore_init(version, options);
        let mut buf = vec![0u8; 0x1000];
        let writer = FuseDevWriter::<()>::new(file.as_raw_fd(), &mut buf).unwrap();
        new.notify_resend(writer).unwrap();
        let (_stop_tx, stop) = oneshot::channel();
        let new_handle = serve(file.try_clone().unwrap(), buf_size, new, stop);
        stack.slow_fs.wait_for_slow_reads(2);

        stack.slow_fs.open_gate();
        let slow = slow.recv_timeout(Duration::from_secs(5)).unwrap().unwrap();
        assert_eq!(slow, slow_fs_data());
        old_handle.join().unwrap();

        stack.upper_se.umount().unwrap();
        new_handle.join().unwrap();
    }
}
