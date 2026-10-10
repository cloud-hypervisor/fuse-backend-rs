// SPDX-License-Identifier: Apache-2.0

//! Mounts a filesystem with one file whose reads are passed through to a backing file, served
//! by the sync server and, with `async-io`, by `FuseDevTask`. Needs root and a kernel with
//! CONFIG_FUSE_PASSTHROUGH, and is skipped without them.

#[cfg(all(feature = "fusedev", target_os = "linux"))]
mod fusedev_tests {
    use std::ffi::CStr;
    use std::fs::File;
    use std::io::{self, Write};
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::io::AsRawFd;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::{Arc, OnceLock};
    use std::thread;
    use std::time::Duration;

    use fuse_backend_rs::abi::fuse_abi::{stat64, FsOptions, OpenOptions, ROOT_ID};
    use fuse_backend_rs::api::filesystem::{Context, Entry, FileSystem};
    use fuse_backend_rs::api::server::Server;
    use fuse_backend_rs::transport::{fuse_backing_open, FuseSession};
    use vmm_sys_util::tempdir::TempDir;
    use vmm_sys_util::tempfile::TempFile;

    const FILE_ID: u64 = 2;

    struct Fs {
        backing: File,
        fuse_file: OnceLock<File>,
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
            let id = fuse_backing_open(self.fuse_file.get().unwrap(), self.backing.as_raw_fd())?;
            Ok((None, OpenOptions::PASSTHROUGH, Some(id)))
        }
    }

    /// Mount a filesystem with one file, or return `None` when not root.
    fn mount() -> Option<(Arc<Fs>, FuseSession, TempDir)> {
        if unsafe { libc::geteuid() } != 0 {
            eprintln!("not root, skipping");
            return None;
        }

        let mut backing = TempFile::new().unwrap().into_file();
        backing.write_all(b"passed through").unwrap();
        let fs = Arc::new(Fs {
            backing,
            fuse_file: OnceLock::new(),
            passthrough: AtomicBool::new(false),
        });

        let mountpoint = TempDir::new().unwrap();
        let mut se = FuseSession::new(mountpoint.as_path(), "passthrough", "", true).unwrap();
        se.mount().unwrap();
        let fuse_file = se.get_fuse_file().unwrap().try_clone().unwrap();
        fs.fuse_file.set(fuse_file).unwrap();
        Some((fs, se, mountpoint))
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

    fn check(result: Option<io::Result<Vec<u8>>>) {
        match result {
            // The default `read` returns ENOSYS, so the data can only come from the backing file.
            Some(data) => assert_eq!(data.unwrap(), b"passed through"),
            None => eprintln!("kernel without FUSE passthrough, skipping"),
        }
    }

    #[test]
    fn integration_kernel_passthrough() {
        let Some((fs, mut se, mountpoint)) = mount() else {
            return;
        };

        let server = Arc::new(Server::new(fs.clone()));
        server.set_max_stack_depth(2).unwrap();
        let mut ch = se.new_channel().unwrap();
        let handle = thread::spawn(move || {
            while let Ok(Some((reader, writer))) = ch.get_request() {
                if server.handle_message(reader, writer, None, None).is_err() {
                    break;
                }
            }
        });

        let result = read_file(&fs, &mountpoint);

        se.umount().unwrap();
        se.wake().unwrap();
        handle.join().unwrap();
        check(result);
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
