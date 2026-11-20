// SPDX-License-Identifier: Apache-2.0

//! These tests read files of several sizes from a mount that sends READ replies with splice(2),
//! once with files that splice and once with files that can't, and check what the reads return.
//! Mounting needs root or fusermount3, and the tests skip without either.

#[cfg(target_os = "linux")]
mod splice {
    use std::ffi::CStr;
    use std::fs::File;
    use std::io;
    use std::os::unix::fs::FileExt;
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
    fn create_files(dir: &Path) -> Vec<(File, Vec<u8>)> {
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
                (File::open(&path).unwrap(), data)
            })
            .collect()
    }

    /// Serves the files of `create_files()`: each by its name, from the page cache, and by its
    /// name with `.direct`, with direct IO. Reads go through `ZeroCopyWriter::write_from()`.
    struct SpliceFs {
        files: Vec<(File, Vec<u8>)>,
        /// A socket that `raw_fd()` returns instead of the file, so that splice() fails.
        unspliceable: Option<UnixStream>,
        /// How many times the transport asked for the file descriptor of a file.
        fd_calls: AtomicUsize,
        /// How many times the transport read a file into memory.
        copies: AtomicUsize,
    }

    /// The file that `SpliceFs` hands to `write_from()`.
    struct ReadFile<'a> {
        fs: &'a SpliceFs,
        file: &'a File,
    }

    impl FileReadWriteVolatile for ReadFile<'_> {
        fn raw_fd(&self) -> Option<RawFd> {
            self.fs.fd_calls.fetch_add(1, Ordering::Relaxed);
            match &self.fs.unspliceable {
                Some(sock) => Some(sock.as_raw_fd()),
                None => Some(self.file.as_raw_fd()),
            }
        }

        fn read_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        fn write_volatile(&mut self, _slice: FileVolatileSlice) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        fn read_at_volatile(&mut self, slice: FileVolatileSlice, off: u64) -> io::Result<usize> {
            self.fs.copies.fetch_add(1, Ordering::Relaxed);
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
            let file = &self.files[Self::file_of(inode).0].0;
            w.write_from(&mut ReadFile { fs: self, file }, size as usize, offset)
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

    /// Serve the test files from a mount with splicing on, with one worker so that its pipes
    /// serve every READ, and read every file through the page cache and with direct IO. Checks
    /// what the reads return, and returns the file system, or `None` if it can't mount.
    fn read_files(unspliceable: Option<UnixStream>) -> Option<Arc<SpliceFs>> {
        let src = TempDir::new().unwrap();
        let fs = Arc::new(SpliceFs {
            files: create_files(src.as_path()),
            unspliceable,
            fd_calls: AtomicUsize::new(0),
            copies: AtomicUsize::new(0),
        });
        let mnt = TempDir::new().unwrap();
        let mut se = FuseSession::new(mnt.as_path(), "splice_test", "", true).unwrap();
        se.set_allow_other(false);
        se.set_splice_write(true);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return None;
        }
        let cfg = SyncServingConfig {
            workers: 1,
            blocking: false,
        };
        let serving = SyncFuseServing::new(se, Arc::new(Server::new(fs.clone())), cfg).unwrap();

        for (&(name, _), (_, data)) in FILES.iter().zip(&fs.files) {
            for path in [name.to_string(), format!("{name}.direct")] {
                let path: PathBuf = mnt.as_path().join(path);
                let (tx, rx) = channel();
                let p = path.clone();
                thread::spawn(move || tx.send(std::fs::read(p)));
                let read = rx
                    .recv_timeout(Duration::from_secs(30))
                    .unwrap_or_else(|_| panic!("reading {:?} hangs", path))
                    .unwrap();
                assert!(read == *data, "{:?} returned other data", path);
            }
        }
        drop(serving);
        Some(fs)
    }

    /// Whether this process can grow a pipe to 2 MiB, which a READ of 1 MiB needs.
    fn big_pipes() -> bool {
        let (_r, w) = nix::unistd::pipe().unwrap();
        nix::fcntl::fcntl(&w, nix::fcntl::FcntlArg::F_SETPIPE_SZ(2 * MIB as i32)).is_ok()
    }

    #[test]
    fn test_splice_read_replies() {
        let Some(fs) = read_files(None) else {
            return;
        };
        assert!(fs.fd_calls.load(Ordering::Relaxed) > 0);
        if big_pipes() {
            assert_eq!(fs.copies.load(Ordering::Relaxed), 0);
        } else {
            eprintln!("pipes can't hold a READ of 1 MiB, so those READs were copied");
        }
    }

    #[test]
    fn test_splice_read_replies_fall_back() {
        let Some(fs) = read_files(Some(UnixStream::pair().unwrap().0)) else {
            return;
        };
        // The first READ fails to splice, and the worker copies from then on.
        assert_eq!(fs.fd_calls.load(Ordering::Relaxed), 1);
        assert!(fs.copies.load(Ordering::Relaxed) > FILES.len());
    }
}
