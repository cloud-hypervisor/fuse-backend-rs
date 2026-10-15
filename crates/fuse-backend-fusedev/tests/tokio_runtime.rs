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
    use std::os::unix::io::AsRawFd;
    use std::path::Path;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    use async_trait::async_trait;
    use fuse_backend_core::abi::fuse_abi::{stat64, CreateIn, FsOptions, OpenOptions, ROOT_ID};
    use fuse_backend_core::api::filesystem::{
        AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, Entry, FileSystem,
        SetattrValid,
    };
    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::async_runtime::{self, RuntimeType};
    use fuse_backend_fusedev::{FuseDevTask, FuseDevWriter, FuseSession};
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
        let (tx, rx) = channel();
        let path = mnt.as_path().join("hello");
        let reader = thread::spawn(move || {
            let _ = tx.send(std::fs::read(path));
        });
        let read = rx.recv_timeout(Duration::from_secs(5));
        se.umount().unwrap();
        let served = handle.join();
        reader.join().unwrap();
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

    /// Stat `path` in a thread of its own and send the inode number.
    fn stat_in_thread(path: std::path::PathBuf) -> std::sync::mpsc::Receiver<u64> {
        let (tx, rx) = channel();
        thread::spawn(move || {
            use std::os::unix::fs::MetadataExt;
            let _ = tx.send(std::fs::metadata(path).unwrap().ino());
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
        ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
            enosys()
        }

        async fn async_create(
            &self,
            ctx: &Context,
            parent: u64,
            name: &CStr,
            args: CreateIn,
        ) -> io::Result<(Entry, Option<u64>, OpenOptions, Option<u32>)> {
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
    fn serve(
        file: File,
        buf_size: usize,
        server: Arc<Server<Arc<TestFs>>>,
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

        let slow = stat_in_thread(mnt.as_path().join("slow"));
        thread::sleep(Duration::from_millis(100));

        // A lookup waiting in the file system doesn't hold up the others.
        use std::os::unix::fs::MetadataExt;
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
        let slow = stat_in_thread(mnt.as_path().join("slow"));
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
}
