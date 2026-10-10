// SPDX-License-Identifier: Apache-2.0

//! These tests serve a mount with `FuseDevTask` on a tokio runtime they build themselves, or
//! without any tokio runtime. The crate fixes the runtime type once per process, so these tests
//! run in a binary of their own. Mounting needs root or fusermount3, and the tests skip without
//! either.

#[cfg(all(target_os = "linux", feature = "async-io"))]
mod tokio_runtime {
    use std::sync::atomic::AtomicBool;
    use std::sync::mpsc::channel;
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::async_runtime::{self, RuntimeType};
    use fuse_backend_fusedev::{FuseDevTask, FuseSession};
    use fuse_backend_passthrough::{Config, PassthroughFs};
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
        let mut se = FuseSession::new(mnt.as_path(), "tokio_runtime_test", "", false).unwrap();
        se.set_allow_other(false);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return;
        }
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
        state.store(true, std::sync::atomic::Ordering::Release);
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
        let mut se = FuseSession::new(mnt.as_path(), "tokio_runtime_test", "", false).unwrap();
        se.set_allow_other(false);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return;
        }
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
}
