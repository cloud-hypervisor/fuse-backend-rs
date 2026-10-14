// SPDX-License-Identifier: Apache-2.0

//! Mounts file systems whose open files pass through to backing files. A test file system with
//! one file is served by the sync server and, with `async-io`, by `FuseDevTask`, and a
//! `PassthroughFs` serves a file opened with O_DIRECT. Needs root in the initial user namespace
//! and a kernel with CONFIG_FUSE_PASSTHROUGH, and is skipped without them.

#[cfg(all(feature = "fusedev", target_os = "linux"))]
mod fusedev_tests {
    use std::ffi::CStr;
    use std::fs::File;
    use std::io::{self, Write};
    use std::os::unix::fs::{FileExt, MetadataExt, OpenOptionsExt};
    use std::os::unix::io::{AsRawFd, BorrowedFd};
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::thread::{self, JoinHandle};
    use std::time::Duration;

    use fuse_backend_rs::abi::fuse_abi::{
        stat64, FsOptions, InHeader, Opcode, OpenOptions, OutHeader, ROOT_ID,
    };
    use fuse_backend_rs::api::filesystem::{Context, Entry, FileSystem};
    use fuse_backend_rs::api::server::{MetricsHook, Server};
    use fuse_backend_rs::passthrough::{BackingFiles, Config, PassthroughFs};
    use fuse_backend_rs::transport::{fuse_backing_close, fuse_backing_open, FuseSession};
    use vmm_sys_util::tempdir::TempDir;
    use vmm_sys_util::tempfile::TempFile;

    const FILE_ID: u64 = 2;

    struct Fs {
        backing: File,
        fuse_file: File,
        passthrough: AtomicBool,
    }

    impl Fs {
        fn stat(&self, inode: u64) -> io::Result<stat64> {
            let mut st: stat64 = unsafe { std::mem::zeroed() };
            st.st_ino = inode;
            st.st_nlink = 1;
            if inode == ROOT_ID {
                st.st_mode = libc::S_IFDIR | 0o755;
            } else if inode == FILE_ID {
                st.st_mode = libc::S_IFREG | 0o444;
                st.st_size = self.backing.metadata()?.size() as i64;
            } else {
                return Err(io::Error::from_raw_os_error(libc::ENOENT));
            }
            Ok(st)
        }
    }

    impl FileSystem for Fs {
        type Inode = u64;
        type Handle = u64;

        fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
            self.passthrough
                .store(capable.contains(FsOptions::PASSTHROUGH), Ordering::Relaxed);
            Ok(FsOptions::PASSTHROUGH)
        }

        fn lookup(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            if parent != ROOT_ID || name.to_bytes() != b"file" {
                return Err(io::Error::from_raw_os_error(libc::ENOENT));
            }
            Ok(Entry {
                inode: FILE_ID,
                generation: 0,
                attr: self.stat(FILE_ID)?,
                attr_flags: 0,
                attr_timeout: Duration::from_secs(1),
                entry_timeout: Duration::from_secs(1),
            })
        }

        fn getattr(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            Ok((self.stat(inode)?, Duration::from_secs(1)))
        }

        fn open(
            &self,
            _ctx: &Context,
            _inode: u64,
            _flags: u32,
            _fuse_flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
            let id = fuse_backing_open(&self.fuse_file, self.backing.as_raw_fd())?;
            Ok((None, OpenOptions::PASSTHROUGH, Some(id)))
        }
    }

    /// Mount a session and return it with its mount point and a clone of its FUSE device, or
    /// return `None` when not root.
    fn mount_session(readonly: bool) -> Option<(FuseSession, TempDir, File)> {
        if unsafe { libc::geteuid() } != 0 {
            eprintln!("not root, skipping");
            return None;
        }
        let mountpoint = TempDir::new().unwrap();
        let mut se = FuseSession::new(mountpoint.as_path(), "passthrough", "", readonly).unwrap();
        se.mount().unwrap();
        let fuse_file = se.get_fuse_file().unwrap().try_clone().unwrap();
        Some((se, mountpoint, fuse_file))
    }

    /// Mount a filesystem with one file, or return `None` when not root.
    fn mount() -> Option<(Arc<Fs>, FuseSession, TempDir)> {
        let (se, mountpoint, fuse_file) = mount_session(true)?;
        let mut backing = TempFile::new().unwrap().into_file();
        backing.write_all(b"passed through").unwrap();
        let fs = Arc::new(Fs {
            backing,
            fuse_file,
            passthrough: AtomicBool::new(false),
        });
        Some((fs, se, mountpoint))
    }

    /// Counts the READ and WRITE requests the server handles.
    #[derive(Default)]
    struct DataRequests(AtomicUsize);

    impl MetricsHook for DataRequests {
        fn collect(&self, ih: &InHeader) {
            if ih.opcode == Opcode::Read as u32 || ih.opcode == Opcode::Write as u32 {
                self.0.fetch_add(1, Ordering::Relaxed);
            }
        }

        fn release(&self, _oh: Option<&OutHeader>) {}
    }

    /// Serve the requests of `se` with the sync server on a thread, counting the READ and WRITE
    /// requests.
    fn serve<F: FileSystem + Send + Sync + 'static>(
        se: &FuseSession,
        fs: Arc<F>,
    ) -> (JoinHandle<()>, Arc<DataRequests>) {
        let server = Server::new(fs);
        server.set_max_stack_depth(2).unwrap();
        let requests = Arc::new(DataRequests::default());
        let hook = requests.clone();
        let mut ch = se.new_channel().unwrap();
        let handle = thread::spawn(move || {
            while let Ok(Some((reader, writer))) = ch.get_request() {
                if server
                    .handle_message(reader, writer, None, Some(&*hook))
                    .is_err()
                {
                    break;
                }
            }
        });
        (handle, requests)
    }

    fn stop(mut se: FuseSession, handle: JoinHandle<()>) {
        se.umount().unwrap();
        se.wake().unwrap();
        handle.join().unwrap();
    }

    /// Read the file, or return `None` if the kernel doesn't offer passthrough.
    fn read_file(fs: &Fs, mountpoint: &TempDir) -> Option<io::Result<Vec<u8>>> {
        // Stat blocks until the kernel finishes INIT.
        std::fs::metadata(mountpoint.as_path()).unwrap();
        if fs.passthrough.load(Ordering::Relaxed) {
            Some(std::fs::read(mountpoint.as_path().join("file")))
        } else {
            None
        }
    }

    /// Pass the result of using a file to `ok`. Skip on `None`, when the kernel doesn't offer
    /// passthrough, and on EPERM, when the process can't register backing files.
    fn check_with<T>(result: Option<io::Result<T>>, ok: impl FnOnce(T)) {
        match result {
            Some(Ok(value)) => ok(value),
            // Registering a backing file needs CAP_SYS_ADMIN in the initial user namespace, which
            // root in another one, such as from `unshare -r`, doesn't have.
            Some(Err(e)) if e.raw_os_error() == Some(libc::EPERM) => {
                eprintln!("no CAP_SYS_ADMIN in the initial user namespace, skipping")
            }
            Some(Err(e)) => panic!("failed to use the file: {}", e),
            None => eprintln!("kernel without FUSE passthrough, skipping"),
        }
    }

    fn check(result: Option<io::Result<Vec<u8>>>) {
        // The default `read` returns ENOSYS, so the data can only come from the backing file.
        check_with(result, |data| assert_eq!(data, b"passed through"));
    }

    #[test]
    fn integration_kernel_passthrough() {
        let Some((fs, se, mountpoint)) = mount() else {
            return;
        };
        let (handle, _) = serve(&se, fs.clone());
        let result = read_file(&fs, &mountpoint);
        stop(se, handle);
        check(result);
    }

    /// Registers backing files on a FUSE device and counts the registrations.
    struct DeviceFiles {
        fuse_file: File,
        opened: AtomicUsize,
    }

    impl BackingFiles for DeviceFiles {
        fn open(&self, fd: BorrowedFd<'_>) -> io::Result<u32> {
            let id = fuse_backing_open(&self.fuse_file, fd.as_raw_fd())?;
            self.opened.fetch_add(1, Ordering::Relaxed);
            Ok(id)
        }

        fn close(&self, backing_id: u32) -> io::Result<()> {
            fuse_backing_close(&self.fuse_file, backing_id)
        }
    }

    #[repr(align(4096))]
    struct Block([u8; 4096]);

    /// An O_DIRECT open of a `PassthroughFs` file passes reads and writes through to the host
    /// file instead of sending them to the server.
    #[test]
    fn integration_kernel_passthrough_o_direct() {
        let source = TempDir::new().unwrap();
        let host_path = source.as_path().join("file");
        std::fs::write(&host_path, [1u8; 4096]).unwrap();
        // tmpfs supports O_DIRECT only since Linux 6.6.
        match std::fs::OpenOptions::new()
            .read(true)
            .custom_flags(libc::O_DIRECT)
            .open(&host_path)
        {
            Ok(_) => {}
            Err(e) if e.raw_os_error() == Some(libc::EINVAL) => {
                eprintln!("no O_DIRECT in {:?}, skipping", source.as_path());
                return;
            }
            Err(e) => panic!("failed to open {:?} with O_DIRECT: {}", host_path, e),
        }

        let Some((se, mountpoint, fuse_file)) = mount_session(false) else {
            return;
        };
        let files = Arc::new(DeviceFiles {
            fuse_file,
            opened: AtomicUsize::new(0),
        });
        let mut fs = PassthroughFs::<()>::new(Config {
            root_dir: source.as_path().to_string_lossy().to_string(),
            allow_direct_io: true,
            ..Default::default()
        })
        .unwrap();
        fs.set_backing_files(files.clone());
        let (handle, requests) = serve(&se, Arc::new(fs));

        // Read the first block and write a second one. No other file is open, so the server
        // handles no READ or WRITE at all if the handle passes through.
        let result = std::fs::OpenOptions::new()
            .read(true)
            .write(true)
            .custom_flags(libc::O_DIRECT)
            .open(mountpoint.as_path().join("file"))
            .and_then(|file| {
                let mut block = Block([0; 4096]);
                file.read_exact_at(&mut block.0, 0)?;
                file.write_all_at(&Block([2; 4096]).0, 4096)?;
                Ok(block)
            });
        // Without passthrough the open succeeds without registering the file.
        let result = match result {
            Ok(_) if files.opened.load(Ordering::Relaxed) == 0 => None,
            result => Some(result),
        };
        let data_requests = requests.0.load(Ordering::Relaxed);

        stop(se, handle);
        check_with(result, |block| {
            assert_eq!(block.0, [1; 4096]);
            assert_eq!(data_requests, 0);
            let data = std::fs::read(&host_path).unwrap();
            assert_eq!(data[4096..], [2; 4096]);
        });
    }

    #[cfg(feature = "async-io")]
    mod async_io {
        use std::ffi::CStr;
        use std::io;
        use std::sync::atomic::AtomicBool;
        use std::sync::Arc;
        use std::thread;
        use std::time::Duration;

        use async_trait::async_trait;
        use fuse_backend_rs::abi::fuse_abi::{stat64, CreateIn, OpenOptions};
        use fuse_backend_rs::api::filesystem::{
            AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, Entry, FileSystem,
            SetattrValid,
        };
        use fuse_backend_rs::api::server::Server;
        use fuse_backend_rs::async_runtime::{self, Runtime, RuntimeType};
        use fuse_backend_rs::transport::FuseDevTask;

        use super::{check, mount, read_file, Fs};

        fn enosys<T>() -> io::Result<T> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        #[allow(unused_variables)]
        #[async_trait]
        impl AsyncFileSystem for Fs {
            async fn async_lookup(
                &self,
                ctx: &Context,
                parent: u64,
                name: &CStr,
            ) -> io::Result<Entry> {
                self.lookup(ctx, parent, name)
            }

            async fn async_getattr(
                &self,
                ctx: &Context,
                inode: u64,
                handle: Option<u64>,
            ) -> io::Result<(stat64, Duration)> {
                self.getattr(ctx, inode, handle)
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
                self.open(ctx, inode, flags, fuse_flags)
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

        #[test]
        fn integration_kernel_passthrough_async() {
            let Some((fs, mut se, mountpoint)) = mount() else {
                return;
            };
            async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();

            let server = Arc::new(Server::new(fs.clone()));
            server.set_max_stack_depth(2).unwrap();
            let file = se.clone_fuse_file().unwrap();
            let buf_size = se.bufsize();
            let handle = thread::spawn(move || {
                let state = Arc::new(AtomicBool::new(false));
                let mut task = FuseDevTask::new_with_max_inflight(buf_size, file, server, state, 4);
                Runtime::new().block_on(task.poll_handler());
            });

            let result = read_file(&fs, &mountpoint);

            se.umount().unwrap();
            handle.join().unwrap();
            check(result);
        }
    }
}
