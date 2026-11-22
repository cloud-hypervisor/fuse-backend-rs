// SPDX-License-Identifier: Apache-2.0

//! These tests move the copy of a READ reply to another thread while its io_uring read into the
//! reply buffer is in flight, which aborts the process. Each runs in a child process. They run
//! in a binary of their own, which never mounts FUSE. A child forked from a process that serves
//! FUSE mounts inherits their devices and files, and exec can hang on the FLUSH of an inherited
//! file.

#[cfg(all(target_os = "linux", feature = "async-io"))]
mod moved_io {
    use std::io::{self, Write};
    use std::os::unix::io::{AsRawFd, RawFd};
    use std::os::unix::process::ExitStatusExt;
    use std::panic::AssertUnwindSafe;
    use std::process::{Command, Stdio};
    use std::sync::Arc;
    use std::task::{Context as TaskContext, Waker};
    use std::thread;
    use std::time::{Duration, Instant};

    use async_trait::async_trait;
    use fuse_backend_core::abi::fuse_abi::{InHeader, Opcode, OutHeader, ReadIn};
    use fuse_backend_core::api::filesystem::{
        AsyncFileSystem, AsyncZeroCopyWriter, Context, FileSystem,
    };
    use fuse_backend_core::api::server::Server;
    use fuse_backend_core::async_file::File;
    use fuse_backend_core::async_runtime::{self, RuntimeType};
    use fuse_backend_core::file_traits::AsyncFileReadWriteVolatile;
    use fuse_backend_fusedev::{FuseBuf, FuseDevReaderExt, FuseDevWriter, Reader};
    use futures_util::FutureExt;
    use vm_memory::ByteValued;
    use vmm_sys_util::tempfile::TempFile;

    /// Names the test that a child process runs.
    const CHILD: &str = "FUSEDEV_TEST_MOVED_IO_CHILD";
    /// The file that the child maps as its reply buffer.
    const REPLY_FILE: &str = "FUSEDEV_TEST_MOVED_IO_REPLY";
    /// The exit code of a child process without io_uring.
    const NO_URING: i32 = 2;
    const REPLY_SIZE: usize = 4096;
    /// What the reply buffer holds before the request.
    const CANARY: u8 = 0xaa;
    /// What the child prints before it moves the copy, and once the request ended.
    const MOVING: &str = "moving the copy";
    const ENDED: &str = "the request ended";

    /// Run the test `name` in a child process, which serves a READ whose copy a scoped thread
    /// treats as `how` says, see `move_copy()`. Check that the child aborted after it moved the
    /// copy and before the request ended, and that nothing wrote into the reply data.
    fn check_aborts(name: &str, how: Move) {
        if std::env::var_os(CHILD).is_some_and(|child| child == name) {
            // Safe because it only keeps an abort from dumping core.
            unsafe { libc::prctl(libc::PR_SET_DUMPABLE, 0 as libc::c_ulong) };
            log::set_logger(&StderrLog).unwrap();
            log::set_max_level(log::LevelFilter::Error);
            if async_runtime::set_runtime_type(RuntimeType::Uring).is_err() {
                std::process::exit(NO_URING);
            }
            return move_copy(how);
        }
        let reply = TempFile::new().unwrap();
        reply.as_file().write_all(&[CANARY; REPLY_SIZE]).unwrap();
        let output = TempFile::new().unwrap();
        let to_output = || Stdio::from(output.as_file().try_clone().unwrap());
        let mut child = Command::new(std::env::current_exe().unwrap())
            .args(["--exact", &format!("moved_io::{name}"), "--nocapture"])
            .env(CHILD, name)
            .env(REPLY_FILE, reply.as_path())
            .stdout(to_output())
            .stderr(to_output())
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
                let output = std::fs::read_to_string(output.as_path()).unwrap_or_default();
                panic!("the child process hung: {}", output);
            }
            thread::sleep(Duration::from_millis(10));
        };
        if status.code() == Some(NO_URING) {
            eprintln!("io_uring isn't available, skipping");
            return;
        }
        let output = std::fs::read_to_string(output.as_path()).unwrap();
        let reply = std::fs::read(reply.as_path()).unwrap();
        let data = &reply[std::mem::size_of::<OutHeader>()..];
        assert!(
            data.iter().all(|&b| b == CANARY),
            "the kernel wrote into the reply buffer after the request ended: \"{}\"",
            data[..16].escape_ascii()
        );
        assert_eq!(
            status.signal(),
            Some(libc::SIGABRT),
            "child {status}: {output}"
        );
        assert!(
            output.contains(MOVING) && !output.contains(ENDED),
            "{}",
            output
        );
        assert!(
            output.contains("off the serving thread while the file's asynchronous IO"),
            "{}",
            output
        );
    }

    /// Prints the errors that the crates log, such as why the process aborts.
    struct StderrLog;

    impl log::Log for StderrLog {
        fn enabled(&self, _metadata: &log::Metadata) -> bool {
            true
        }

        fn log(&self, record: &log::Record) {
            eprintln!("{}", record.args());
        }

        fn flush(&self) {}
    }

    /// An open makes the runtime submit what's queued, and returns once it completes.
    async fn settle() {
        File::async_open("/dev/null", false, false).await.unwrap();
    }

    /// What the scoped thread does with the copy.
    #[derive(Clone, Copy)]
    enum Move {
        Poll,
        Drop,
    }

    /// A file system whose READ starts its copy from `pipe`, which stays empty, on the serving
    /// thread, and then moves the copy to a scoped thread, which polls or drops it.
    struct MoveCopyFs {
        pipe: RawFd,
        how: Move,
    }

    impl FileSystem for MoveCopyFs {
        type Inode = u64;
        type Handle = u64;
    }

    #[async_trait]
    impl AsyncFileSystem for MoveCopyFs {
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
        ) -> io::Result<usize> {
            // The copy takes an `Arc`, and the file stays on the serving thread.
            #[allow(clippy::arc_with_non_send_sync)]
            let pipe: Arc<dyn AsyncFileReadWriteVolatile> =
                Arc::new(File::borrow_fd(self.pipe, Arc::new(())));
            let mut copy = w.async_write_from(pipe, size as usize, 0);
            assert!((&mut copy).now_or_never().is_none());
            // Once the runtime submits it, the read waits in the kernel for the pipe.
            async_runtime::spawn(settle()).await.unwrap();
            println!("{MOVING}");
            let how = self.how;
            thread::scope(|s| {
                s.spawn(move || match how {
                    Move::Poll => {
                        let _ = copy
                            .as_mut()
                            .poll(&mut TaskContext::from_waker(Waker::noop()));
                    }
                    Move::Drop => drop(copy),
                });
            });
            Ok(0)
        }
    }

    /// Serve a READ with `MoveCopyFs`, with the reply buffer in the file that the parent
    /// passed. Once the request ends, which it must not while the copy's read is in flight,
    /// give the read its data and let it complete.
    fn move_copy(how: Move) {
        let reply_file = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .open(std::env::var_os(REPLY_FILE).unwrap())
            .unwrap();
        // Safe because the mapping is new, and the process never unmaps it.
        let map = unsafe {
            libc::mmap(
                std::ptr::null_mut(),
                REPLY_SIZE,
                libc::PROT_READ | libc::PROT_WRITE,
                libc::MAP_SHARED,
                reply_file.as_raw_fd(),
                0,
            )
        };
        assert_ne!(map, libc::MAP_FAILED);
        // Safe because the mapping covers `REPLY_SIZE` bytes, and only the writer uses it.
        let reply = unsafe { std::slice::from_raw_parts_mut(map.cast::<u8>(), REPLY_SIZE) };

        let (rx, tx) = nix::unistd::pipe().unwrap();
        let mut tx = std::fs::File::from(tx);
        let server = Server::new(MoveCopyFs {
            pipe: rx.as_raw_fd(),
            how,
        });
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
        let mut request = [header.as_slice(), read.as_slice()].concat();
        let reader = Reader::<()>::from_fuse_buffer(FuseBuf::new(&mut request)).unwrap();
        // Where the reply goes.
        let dev = TempFile::new().unwrap().into_file();
        let writer = FuseDevWriter::<()>::new(dev.as_raw_fd(), reply).unwrap();

        async_runtime::block_on(async {
            // Safe because the buffers outlive the process.
            let request = unsafe { server.async_handle_message(reader, writer, None, None) };
            // Like a server that survives a handler's panic.
            let _ = AssertUnwindSafe(request).catch_unwind().await;
            println!("{ENDED}");
            tx.write_all(b"too late").unwrap();
            settle().await;
        });
    }

    /// Polling a copy on a scoped thread while the read that it started on the serving thread
    /// is in flight must not let the request end, so it aborts the process.
    #[test]
    fn poll_moved_copy() {
        check_aborts("poll_moved_copy", Move::Poll);
    }

    /// Dropping a copy on a scoped thread while the read that it started on the serving thread
    /// is in flight must not let the request end, so it aborts the process.
    #[test]
    fn drop_moved_copy() {
        check_aborts("drop_moved_copy", Move::Drop);
    }
}
