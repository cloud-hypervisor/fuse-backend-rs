// SPDX-License-Identifier: Apache-2.0

//! These tests drop io_uring IO in flight. Each runs in a child process, because the wrong
//! outcome aborts the process or writes into freed memory. They run in a binary of their own,
//! which never mounts FUSE. A child forked from a process that serves FUSE mounts inherits their
//! devices and files, and exec can hang on the FLUSH of an inherited file.

#[cfg(all(target_os = "linux", feature = "async-io"))]
mod dropped_io {
    use std::future::Future;
    use std::io::Write;
    use std::os::unix::io::{AsRawFd, RawFd};
    use std::os::unix::process::ExitStatusExt;
    use std::pin::Pin;
    use std::process::ExitStatus;
    use std::sync::Arc;
    use std::task::Poll;
    use std::time::{Duration, Instant};

    use async_trait::async_trait;
    use fuse_backend_core::abi::fuse_abi::{InHeader, Opcode, ReadIn};
    use fuse_backend_core::api::filesystem::{
        AsyncFileSystem, AsyncZeroCopyWriter, Context, FileSystem,
    };
    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::async_file::File;
    use fuse_backend_core::async_runtime;
    use fuse_backend_core::file_traits::AsyncFileReadWriteVolatile;
    use fuse_backend_fusedev::{FuseDevTask, FuseDevWriter};
    use fuse_backend_passthrough::{Config, PassthroughFs};
    use futures_util::FutureExt;
    use vm_memory::ByteValued;
    use vmm_sys_util::tempfile::TempFile;

    /// Names the test that a child process runs.
    const CHILD: &str = "FUSEDEV_TEST_DROPPED_IO_CHILD";
    /// The exit code of a child process without io_uring.
    const NO_URING: i32 = 2;

    /// Run the test `name` of this module in a child process, and return how it ended,
    /// or `None` if io_uring isn't available.
    fn run_child(name: &str) -> Option<ExitStatus> {
        let mut child = std::process::Command::new(std::env::current_exe().unwrap())
            .args([
                "--exact",
                // The test's path without the crate name.
                &format!("{}::{name}", module_path!().split_once("::").unwrap().1),
                "--nocapture",
            ])
            .env(CHILD, name)
            .stdout(std::process::Stdio::piped())
            .spawn()
            .unwrap();
        let deadline = Instant::now() + Duration::from_secs(60);
        let status = loop {
            if let Some(status) = child.try_wait().unwrap() {
                break status;
            }
            if Instant::now() > deadline {
                // Don't wait for a child that SIGKILL doesn't end.
                let _ = child.kill();
                panic!("the child process hung");
            }
            std::thread::sleep(Duration::from_millis(10));
        };
        if status.code() == Some(NO_URING) {
            eprintln!("io_uring isn't available, skipping");
            return None;
        }
        // A filter that matches no test also exits with success.
        let mut out = String::new();
        std::io::Read::read_to_string(&mut child.stdout.take().unwrap(), &mut out).unwrap();
        assert!(
            !status.success() || out.contains("test result: ok. 1 passed"),
            "the child didn't run {}: {}",
            name,
            out
        );
        Some(status)
    }

    /// Whether this process is the child that runs the test `name`. If so, keep it
    /// from dumping core and select tokio-uring. If not, run `name` in a child process
    /// and pass how it ended to `check`.
    fn in_child(name: &str, check: impl FnOnce(ExitStatus)) -> bool {
        if std::env::var_os(CHILD).is_none_or(|child| child != name) {
            if let Some(status) = run_child(name) {
                check(status);
            }
            return false;
        }
        // Safe because it only keeps an abort from dumping core.
        unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 0 as libc::c_ulong) };
        if async_runtime::set_runtime_type(async_runtime::RuntimeType::Uring).is_err() {
            std::process::exit(NO_URING);
        }
        true
    }

    /// Checks that a child process exited normally.
    fn exited(status: ExitStatus) {
        assert!(status.success(), "child {}", status);
    }

    /// An open makes the runtime submit what's queued, and returns once it completes.
    async fn settle() {
        File::async_open("/dev/null", false, false).await.unwrap();
    }

    /// A copy that waits in the kernel and is dropped must not let the kernel write into
    /// the reused buffer later, so the drop aborts the process.
    #[test]
    fn copy() {
        let aborted =
            |status: ExitStatus| assert_eq!(status.signal(), Some(libc::SIGABRT), "child {status}");
        if !in_child("copy", aborted) {
            return;
        }
        let (rx, tx) = nix::unistd::pipe().unwrap();
        let src = File::from_std_file(rx.into());
        let mut tx = std::fs::File::from(tx);
        let out = TempFile::new().unwrap().into_file();

        let mut buf = vec![0u8; 64];
        async_runtime::block_on(async {
            {
                let mut writer = FuseDevWriter::<()>::new(out.as_raw_fd(), &mut buf).unwrap();
                let mut copy = Box::pin(writer.async_write_from_at(&src, 8, 0));
                // The pipe is empty, so the read waits in the kernel.
                assert!(copy.as_mut().now_or_never().is_none());
                settle().await;
                // Give up on the copy, like a handler whose select took another branch.
                drop(copy);
            }
            // The next request reuses the buffer.
            buf.fill(0xaa);
            tx.write_all(b"too late").unwrap();
            settle().await;
        });
        assert!(
            buf.iter().all(|&b| b == 0xaa),
            "the kernel wrote into the buffer after the drop"
        );
    }

    /// A `FuseDevTask` that waits for a request and is dropped through `select!`, like
    /// on shutdown, must neither abort nor let the kernel write into freed memory.
    #[test]
    fn idle_task() {
        if !in_child("idle_task", exited) {
            return;
        }
        // A pipe stands in for the fuse device.
        let (rx, tx) = nix::unistd::pipe().unwrap();
        let rx = std::fs::File::from(rx);
        let unread = rx.try_clone().unwrap();
        let mut tx = std::fs::File::from(tx);
        let fs = PassthroughFs::<()>::new(Config::default()).unwrap();
        let mut task = FuseDevTask::new(4096, rx, Arc::new(Server::new(fs)), Arc::default());

        let canary = async_runtime::block_on(async {
            tokio::select! {
                biased;
                _ = task.poll_handler() => panic!("poll_handler() returned"),
                // The shutdown, once the task's read waits in the kernel.
                _ = settle() => {}
            }
            // A freed request buffer would likely come back here.
            let canary = vec![0xaau8; 4096];
            tx.write_all(b"a request").unwrap();
            settle().await;
            canary
        });
        // The dropped read took the request into the buffer that it owns.
        let err = std::io::Read::read(&mut &unread, &mut [0u8; 16]).unwrap_err();
        assert_eq!(err.kind(), std::io::ErrorKind::WouldBlock);
        assert!(
            canary.iter().all(|&b| b == 0xaa),
            "the kernel wrote into freed memory"
        );
    }

    /// A file system whose READ copies from `pipe`, which stays empty until the test
    /// writes into it. With `forget`, the READ starts the copy and forgets it.
    struct PipeReadFs {
        pipe: RawFd,
        forget: bool,
    }

    impl FileSystem for PipeReadFs {
        type Inode = u64;
        type Handle = u64;
    }

    /// Lets a `Send` handler await a copy, like `PassthroughFs` does.
    struct AssertSend<F>(F);

    // Safe because the runtime polls the future on one thread.
    unsafe impl<F> Send for AssertSend<F> {}

    impl<F: Future + Unpin> Future for AssertSend<F> {
        type Output = F::Output;

        fn poll(mut self: Pin<&mut Self>, cx: &mut std::task::Context<'_>) -> Poll<F::Output> {
            self.0.poll_unpin(cx)
        }
    }

    #[async_trait]
    impl AsyncFileSystem for PipeReadFs {
        async fn async_read(
            &self,
            _ctx: &Context,
            _inode: u64,
            _handle: u64,
            w: &mut (dyn AsyncZeroCopyWriter + Send),
            size: u32,
            _offset: u64,
            _lock_owner: Option<u64>,
            _flags: u32,
        ) -> std::io::Result<usize> {
            // The copy takes an `Arc`, and the file stays on the runtime's thread.
            #[allow(clippy::arc_with_non_send_sync)]
            let pipe: Arc<dyn AsyncFileReadWriteVolatile> =
                Arc::new(File::borrow_fd(self.pipe, Arc::new(())));
            let mut copy = AssertSend(w.async_write_from(pipe, size as usize, 0));
            if !self.forget {
                return copy.await;
            }
            assert!((&mut copy).now_or_never().is_none());
            std::mem::forget(copy);
            Ok(0)
        }
    }

    /// Let a `FuseDevTask` serve a READ with `PipeReadFs` until its copy waits in the
    /// kernel, drop the task through `select!` like on shutdown, and then let the copy
    /// complete. Check that the kernel didn't write into freed memory, and return how
    /// many requests the task leaked.
    fn drop_task_with_copy(forget: bool) -> usize {
        // A pipe stands in for the fuse device, and another one for the file to read.
        let (dev_rx, dev_tx) = nix::unistd::pipe().unwrap();
        let (data_rx, data_tx) = nix::unistd::pipe().unwrap();
        let mut data_tx = std::fs::File::from(data_tx);
        let fs = PipeReadFs {
            pipe: data_rx.as_raw_fd(),
            forget,
        };
        let server = Arc::new(Server::new(fs));
        let mut task = FuseDevTask::new(1024, dev_rx.into(), server, Arc::default());

        let header = InHeader {
            len: (std::mem::size_of::<InHeader>() + std::mem::size_of::<ReadIn>()) as u32,
            opcode: Opcode::Read as u32,
            unique: 1,
            nodeid: 1,
            ..Default::default()
        };
        let read = ReadIn {
            size: 8,
            ..Default::default()
        };
        let request = [header.as_slice(), read.as_slice()].concat();
        // Keep the device open, so that the task waits for the next request.
        let mut dev_tx = std::fs::File::from(dev_tx);
        dev_tx.write_all(&request).unwrap();

        let canaries = async_runtime::block_on(async {
            tokio::select! {
                biased;
                _ = task.poll_handler() => panic!("poll_handler() returned"),
                // The shutdown, once the handler's copy waits in the kernel.
                _ = async { settle().await; settle().await } => {}
            }
            // A freed request buffer would likely come back as one of these.
            let canaries: Vec<_> = (0..16).map(|_| vec![0xaau8; 1024]).collect();
            data_tx.write_all(b"too late").unwrap();
            settle().await;
            canaries
        });
        assert!(
            canaries.concat().iter().all(|&b| b == 0xaa),
            "the kernel wrote into freed memory"
        );
        task.leaked_requests()
    }

    /// A `FuseDevTask` dropped while a handler's copy into its request buffer is in
    /// flight must leak that request instead of aborting or letting the kernel write
    /// into freed memory.
    #[test]
    fn busy_task() {
        if !in_child("busy_task", exited) {
            return;
        }
        assert_eq!(drop_task_with_copy(false), 1);
    }

    /// A request whose handler forgets its copy completes while the copy is in flight,
    /// so the task must leak its buffer instead of reusing it.
    #[test]
    fn forgotten_copy() {
        if !in_child("forgotten_copy", exited) {
            return;
        }
        assert_eq!(drop_task_with_copy(true), 1);
    }
}
