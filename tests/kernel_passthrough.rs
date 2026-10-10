// SPDX-License-Identifier: Apache-2.0

//! Mounts a filesystem with one file whose reads are passed through to a backing file. Needs
//! root and a kernel with CONFIG_FUSE_PASSTHROUGH, and is skipped without them.

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

    #[test]
    fn integration_kernel_passthrough() {
        if unsafe { libc::geteuid() } != 0 {
            eprintln!("not root, skipping");
            return;
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

        // Stat blocks until the kernel finishes INIT.
        std::fs::metadata(mountpoint.as_path()).unwrap();
        let result = if fs.passthrough.load(Ordering::Relaxed) {
            Some(std::fs::read(mountpoint.as_path().join("file")))
        } else {
            None
        };

        se.umount().unwrap();
        se.wake().unwrap();
        handle.join().unwrap();

        match result {
            // The default `read` returns ENOSYS, so the data can only come from the backing file.
            Some(data) => assert_eq!(data.unwrap(), b"passed through"),
            None => eprintln!("kernel without FUSE passthrough, skipping"),
        }
    }
}
