// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

//! End-to-end smoke test for the asynchronous IO path: requests are sent by
//! the kernel through a real fuse device and served by `FuseDevTask` running
//! on the async runtime.

#[cfg(all(feature = "fusedev", feature = "async-io", target_os = "linux"))]
mod fusedev_async_tests {
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    use vmm_sys_util::tempdir::TempDir;

    use fuse_backend_rs::api::{server::Server, Vfs, VfsOptions};
    use fuse_backend_rs::async_runtime::Runtime;
    use fuse_backend_rs::passthrough::{Config, PassthroughFs};
    use fuse_backend_rs::transport::{FuseDevTask, FuseSession};

    /// Umount the fuse session when dropped, so the mount doesn't leak even
    /// if the test panics.
    struct SessionGuard(Option<FuseSession>);

    impl Drop for SessionGuard {
        fn drop(&mut self) {
            if let Some(se) = self.0.as_mut() {
                let _ = se.umount();
            }
        }
    }

    /// A minimal logger dumping library log messages to stdout, otherwise
    /// `error!()`/`trace!()` messages from the library would be silently
    /// dropped and failures would be undebuggable in CI.
    struct StdoutLogger;

    impl log::Log for StdoutLogger {
        fn enabled(&self, _metadata: &log::Metadata) -> bool {
            true
        }

        fn log(&self, record: &log::Record) {
            println!(
                "[{}] {}: {}",
                record.level(),
                record.target(),
                record.args()
            );
        }

        fn flush(&self) {}
    }

    static LOGGER: StdoutLogger = StdoutLogger;

    /// Mount a `PassthroughFs` through the async path (`FuseDevTask` driven
    /// by the async runtime), perform real file IO against the mountpoint,
    /// and check the results in the backing directory.
    #[test]
    #[ignore] // it depends on privileged mode to pass through /dev/fuse
    fn integration_test_async_passthrough_io() {
        run_async_passthrough_io(false);
    }

    /// Same as `integration_test_async_passthrough_io()`, but the async
    /// handlers offload the synchronous work to the runtime's blocking
    /// thread pool.
    #[test]
    #[ignore] // it depends on privileged mode to pass through /dev/fuse
    fn integration_test_async_passthrough_io_thread_pool() {
        run_async_passthrough_io(true);
    }

    fn run_async_passthrough_io(thread_pool: bool) {
        // All tests in this binary share the same logger, and installing
        // it multiple times is harmless.
        let _ = log::set_logger(&LOGGER);
        log::set_max_level(log::LevelFilter::Trace);

        let src = TempDir::new().unwrap();
        let mnt = TempDir::new().unwrap();

        // Build the filesystem and attach it to a Vfs instance. In thread
        // pool mode create a shared instance, so the async handlers can
        // offload the synchronous work to the runtime's blocking thread
        // pool.
        let cfg = Config {
            root_dir: src.as_path().to_str().unwrap().to_string(),
            do_import: false,
            ..Default::default()
        };
        let vfs = Vfs::new(VfsOptions::default());
        if thread_pool {
            let fs = PassthroughFs::<()>::new_shared(cfg).unwrap();
            fs.import().unwrap();
            fs.enable_async_thread_pool(true);
            vfs.mount(Box::new(fs), "/").unwrap();
        } else {
            let fs = PassthroughFs::<()>::new(cfg).unwrap();
            fs.import().unwrap();
            vfs.mount(Box::new(fs), "/").unwrap();
        }
        let server = Arc::new(Server::new(Arc::new(vfs)));

        // Mount the fuse session and start an async task to serve requests.
        let mut se = FuseSession::new(mnt.as_path(), "async_passthru", "", false).unwrap();
        se.mount().unwrap();
        let mut guard = SessionGuard(Some(se));
        let se = guard.0.as_mut().unwrap();
        let state = Arc::new(AtomicBool::new(false));
        // The kernel requires the read buffer to have capacity for the
        // negotiated `max_write` plus a header, otherwise reads from
        // /dev/fuse fail with `EINVAL` once the INIT handshake is done,
        // see kernel commit "fuse: require /dev/fuse reads to have enough
        // buffer capacity".
        let buf_size = (fuse_backend_rs::api::server::MAX_BUFFER_SIZE + 0x1000) as usize;
        let mut task = FuseDevTask::new(
            buf_size,
            se.clone_fuse_file().unwrap(),
            server,
            state.clone(),
        );

        // Perform real IO through the mountpoint from a helper thread while
        // the async runtime drives `poll_handler()` on this thread. The
        // helper thread notifies `io_notify` once it's done, to wake up the
        // async driver.
        let io_notify = Arc::new(tokio::sync::Notify::new());
        let io_thread = {
            let mnt_path = mnt.as_path().to_path_buf();
            let src_path = src.as_path().to_path_buf();
            let io_notify = io_notify.clone();
            std::thread::spawn(move || {
                // Give the task a moment to start polling the fuse device.
                std::thread::sleep(std::time::Duration::from_millis(100));

                let data = b"hello async fusedev";
                let mnt_file = mnt_path.join("file.txt");

                // Create & write: lookup/create/open/write/release
                std::fs::write(&mnt_file, data).unwrap();
                // Data must show up in the backing directory.
                assert_eq!(std::fs::read(src_path.join("file.txt")).unwrap(), data);

                // Read back through the mount: lookup/open/read/release
                assert_eq!(std::fs::read(&mnt_file).unwrap(), data);

                // Append to exercise writes on an existing handle.
                let mut f = std::fs::OpenOptions::new()
                    .append(true)
                    .open(&mnt_file)
                    .unwrap();
                std::io::Write::write_all(&mut f, b" more").unwrap();
                f.sync_all().unwrap();
                drop(f);
                assert_eq!(
                    std::fs::read(src_path.join("file.txt")).unwrap(),
                    b"hello async fusedev more" as &[u8]
                );

                // Create a directory and list it.
                std::fs::create_dir(mnt_path.join("subdir")).unwrap();
                assert!(src_path.join("subdir").is_dir());
                let names: Vec<String> = std::fs::read_dir(&mnt_path)
                    .unwrap()
                    .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
                    .collect();
                assert!(names.contains(&"file.txt".to_string()));
                assert!(names.contains(&"subdir".to_string()));

                // Remove file and directory.
                std::fs::remove_file(&mnt_file).unwrap();
                std::fs::remove_dir(mnt_path.join("subdir")).unwrap();
                assert!(!src_path.join("file.txt").exists());
                assert!(!src_path.join("subdir").exists());

                // Tell the driver that the IO has completed.
                io_notify.notify_one();
            })
        };

        // A watchdog thread signals timeout if the IO thread doesn't
        // complete in time, given that `tokio/time` is not enabled by
        // the `async-io` feature.
        let timeout = Arc::new(AtomicBool::new(false));
        {
            let timeout = timeout.clone();
            let io_notify = io_notify.clone();
            std::thread::spawn(move || {
                std::thread::sleep(std::time::Duration::from_secs(60));
                timeout.store(true, Ordering::Release);
                io_notify.notify_one();
            });
        }
        let rt = Runtime::new();
        let se = guard.0.as_mut().unwrap();
        let timed_out = rt.block_on(async move {
            // Run `poll_handler()` as a separate task instead of driving it
            // inline from a busy loop: with the tokio-uring runtime, io_uring
            // submission queue entries are handed to the kernel when the
            // runtime parks, and a busy-waiting driver starves the scheduler
            // and prevents requests from being submitted to the kernel.
            let mut poller = Runtime::spawn(async move { task.poll_handler().await });

            // Wait for the IO thread to complete, or the watchdog to fire.
            tokio::select! {
                res = &mut poller => {
                    res.expect("the async fuse task panicked");
                    panic!("the async fuse task terminated unexpectedly");
                }
                _ = io_notify.notified() => {}
            }

            // Tear the session down from within the runtime: `umount()`
            // makes the pending read on the fuse device fail with
            // `ENODEV`, so `poll_handler()` exits cleanly before the
            // task and its buffers are dropped, and unblocks any IO
            // still stuck in the kernel with `ECONNREFUSED`.
            se.umount().unwrap();
            (&mut poller).await.expect("the async fuse task panicked");

            let timed_out = timeout.load(Ordering::Acquire);
            if timed_out {
                // The helper thread got aborted with ECONNREFUSED.
                let _ = io_thread.join();
            } else {
                io_thread.join().expect("the IO helper thread panicked");
            }
            timed_out
        });
        assert!(!timed_out, "timeout waiting for async fuse IO to complete");
    }
}
