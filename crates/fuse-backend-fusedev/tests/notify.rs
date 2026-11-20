// SPDX-License-Identifier: Apache-2.0

//! These tests send notifications to a mount that `SyncFuseServing` or `AsyncFuseServing` serves
//! and check what the kernel does with them. Mounting needs root or fusermount3, and the tests
//! skip without either.

#[cfg(target_os = "linux")]
mod notify {
    use std::ffi::CStr;
    use std::fs::File;
    use std::io;
    use std::os::unix::fs::FileExt;
    use std::os::unix::io::AsRawFd;
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::mpsc::{channel, Receiver, Sender};
    use std::sync::Arc;
    use std::time::Duration;

    use fuse_backend_core::abi::fuse_abi::{stat64, FsOptions, ROOT_ID};
    #[cfg(feature = "async-io")]
    use fuse_backend_core::api::filesystem::AsyncFileSystem;
    use fuse_backend_core::api::filesystem::{
        Context, Entry, FileSystem, ZeroCopyReader, ZeroCopyWriter,
    };
    use fuse_backend_core::api::server::Server;
    #[cfg(feature = "async-io")]
    use fuse_backend_core::async_runtime;
    use fuse_backend_core::{Error, Result};
    #[cfg(feature = "async-io")]
    use fuse_backend_fusedev::{AsyncFuseServing, AsyncServingConfig};
    use fuse_backend_fusedev::{
        FuseDevWriter, FuseServing, FuseSession, SyncFuseServing, SyncServingConfig,
    };
    #[cfg(feature = "uring")]
    use fuse_backend_fusedev::{UringConfig, UringFuseServing};
    use vmm_sys_util::tempdir::TempDir;

    const FILE: u64 = 2;
    const GONE: u64 = 3;
    /// The size of `file` and `gone`, and the max write size the server negotiates by default,
    /// which bounds a retrieve.
    const SIZE: usize = 4096;
    /// The byte that reads of `file` return.
    const READ_BYTE: u8 = 0xaa;

    /// What `TestFs::notify_reply()` got: inode, unique, offset and data.
    type Retrieved = (u64, u64, u64, Vec<u8>);

    /// A root directory with the files `file` and `gone`, which disappears once `deleted` is set.
    /// Every entry and attribute stays valid for a minute.
    struct TestFs {
        file_lookups: AtomicUsize,
        reads: AtomicUsize,
        deleted: AtomicBool,
        forgets: Sender<u64>,
        retrieved: Sender<Retrieved>,
    }

    fn stat(inode: u64) -> io::Result<stat64> {
        let mut st: stat64 = unsafe { std::mem::zeroed() };
        st.st_ino = inode;
        st.st_nlink = 1;
        match inode {
            ROOT_ID => st.st_mode = libc::S_IFDIR | 0o755,
            FILE | GONE => {
                st.st_mode = libc::S_IFREG | 0o644;
                st.st_size = SIZE as i64;
            }
            _ => return Err(io::Error::from_raw_os_error(libc::ENOENT)),
        }
        Ok(st)
    }

    impl FileSystem for TestFs {
        type Inode = u64;
        type Handle = u64;

        fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
            Ok(capable & FsOptions::HAS_EXPIRE_ONLY)
        }

        fn lookup(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            let inode = match (parent, name.to_bytes()) {
                (ROOT_ID, b"file") => {
                    self.file_lookups.fetch_add(1, Ordering::Relaxed);
                    FILE
                }
                (ROOT_ID, b"gone") if !self.deleted.load(Ordering::Relaxed) => GONE,
                _ => return Err(io::Error::from_raw_os_error(libc::ENOENT)),
            };
            Ok(Entry {
                inode,
                generation: 0,
                attr: stat(inode)?,
                attr_flags: 0,
                attr_timeout: Duration::from_secs(60),
                entry_timeout: Duration::from_secs(60),
            })
        }

        fn forget(&self, _ctx: &Context, inode: u64, _count: u64) {
            let _ = self.forgets.send(inode);
        }

        fn getattr(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            Ok((stat(inode)?, Duration::from_secs(60)))
        }

        fn read(
            &self,
            _ctx: &Context,
            _inode: u64,
            _handle: u64,
            w: &mut dyn ZeroCopyWriter,
            size: u32,
            offset: u64,
            _lock_owner: Option<u64>,
            _flags: u32,
        ) -> io::Result<usize> {
            self.reads.fetch_add(1, Ordering::Relaxed);
            let len = (size as usize).min(SIZE.saturating_sub(offset as usize));
            w.write(&vec![READ_BYTE; len])
        }

        fn notify_reply(
            &self,
            _ctx: &Context,
            inode: u64,
            unique: u64,
            offset: u64,
            size: u32,
            r: &mut dyn ZeroCopyReader,
        ) {
            let mut data = vec![0; size as usize];
            r.read_exact(&mut data).unwrap();
            let _ = self.retrieved.send((inode, unique, offset, data));
        }
    }

    #[cfg(feature = "async-io")]
    impl AsyncFileSystem for TestFs {}

    /// A mounted `TestFs` and the layer that serves it.
    struct Mount {
        fs: Arc<TestFs>,
        server: Arc<Server<Arc<TestFs>>>,
        forgets: Receiver<u64>,
        retrieved: Receiver<Retrieved>,
        // Unmounts before `dir` goes.
        serving: Box<dyn FuseServing>,
        dir: TempDir,
    }

    /// Mount `se` and serve it with `server`, or return `None` if that fails.
    type Serve = fn(FuseSession, Arc<Server<Arc<TestFs>>>) -> Option<Box<dyn FuseServing>>;

    fn mount(mut se: FuseSession) -> Option<FuseSession> {
        se.set_allow_other(false);
        match se.mount() {
            Ok(()) => Some(se),
            Err(e) => {
                eprintln!("can't mount ({}), skipping", e);
                None
            }
        }
    }

    fn sync_serving(
        se: FuseSession,
        server: Arc<Server<Arc<TestFs>>>,
    ) -> Option<Box<dyn FuseServing>> {
        let se = mount(se)?;
        let serving = SyncFuseServing::new(se, server, SyncServingConfig::default()).unwrap();
        Some(Box::new(serving))
    }

    #[cfg(feature = "uring")]
    fn uring_serving(
        se: FuseSession,
        server: Arc<Server<Arc<TestFs>>>,
    ) -> Option<Box<dyn FuseServing>> {
        server.set_uring(true);
        let se = mount(se)?;
        match UringFuseServing::new(se, server, UringConfig::default()) {
            Ok(serving) => Some(Box::new(serving)),
            Err(fuse_backend_fusedev::Error::UringNotSupported) => {
                eprintln!("FUSE-over-io_uring is not available, skipping");
                None
            }
            Err(e) => panic!("uring serving failed: {}", e),
        }
    }

    #[cfg(feature = "async-io")]
    fn async_serving(
        se: FuseSession,
        server: Arc<Server<Arc<TestFs>>>,
    ) -> Option<Box<dyn FuseServing>> {
        let se = mount(se)?;
        let serving = AsyncFuseServing::new(se, server, AsyncServingConfig::default()).unwrap();
        Some(Box::new(serving))
    }

    impl Mount {
        /// Mount a `TestFs` that `SyncFuseServing` serves, or return `None` if mounting fails.
        fn new() -> Option<Mount> {
            Mount::with(sync_serving)
        }

        fn with(serve: Serve) -> Option<Mount> {
            let dir = TempDir::new().unwrap();
            let se = FuseSession::new(dir.as_path(), "notify_test", "", false).unwrap();
            let (forget_tx, forgets) = channel();
            let (retrieve_tx, retrieved) = channel();
            let fs = Arc::new(TestFs {
                file_lookups: AtomicUsize::new(0),
                reads: AtomicUsize::new(0),
                deleted: AtomicBool::new(false),
                forgets: forget_tx,
                retrieved: retrieve_tx,
            });
            let server = Arc::new(Server::new(fs.clone()));
            let serving = serve(se, server.clone())?;
            Some(Mount {
                fs,
                server,
                forgets,
                retrieved,
                serving,
                dir,
            })
        }

        fn path(&self, name: &str) -> PathBuf {
            self.dir.as_path().join(name)
        }

        fn file_lookups(&self) -> usize {
            self.fs.file_lookups.load(Ordering::Relaxed)
        }

        /// Pass `send` a writer to the FUSE device.
        fn notify(
            &self,
            send: impl FnOnce(&Server<Arc<TestFs>>, FuseDevWriter<'_>) -> Result<usize>,
        ) -> Result<usize> {
            let mut buf = vec![0u8; 2 * SIZE];
            let fd = self.serving.session().get_fuse_file().unwrap().as_raw_fd();
            send(&self.server, FuseDevWriter::new(fd, &mut buf).unwrap())
        }

        /// Like `notify()`, but run `send` on an async runtime.
        #[cfg(feature = "async-io")]
        fn async_notify(
            &self,
            send: impl AsyncFnOnce(&Server<Arc<TestFs>>, FuseDevWriter<'_>) -> Result<usize>,
        ) -> Result<usize> {
            self.notify(|s, w| async_runtime::block_on(send(s, w)))
        }
    }

    /// The error number a notification failed with.
    fn errno(result: &Result<usize>) -> Option<i32> {
        match result {
            Err(Error::InvalidMessage(e)) | Err(Error::EncodeMessage(e)) => e.raw_os_error(),
            _ => None,
        }
    }

    fn name(name: &[u8]) -> &CStr {
        CStr::from_bytes_with_nul(name).unwrap()
    }

    /// The path of the open file `file`, as /proc shows it.
    fn proc_path(file: &File) -> String {
        std::fs::read_link(format!("/proc/self/fd/{}", file.as_raw_fd()))
            .unwrap()
            .to_string_lossy()
            .into_owned()
    }

    #[test]
    fn test_notify_store_and_retrieve() {
        if let Some(m) = Mount::new() {
            store_and_retrieve(m);
        }
    }

    /// Over io_uring, the request with the retrieved data has an empty header area and carries
    /// its arguments in the payload.
    #[cfg(feature = "uring")]
    #[test]
    fn test_notify_store_and_retrieve_over_uring() {
        if let Some(m) = Mount::with(uring_serving) {
            store_and_retrieve(m);
        }
    }

    fn store_and_retrieve(m: Mount) {
        let file = File::open(m.path("file")).unwrap();
        let data: Vec<u8> = (0..SIZE).map(|i| (i % 251) as u8).collect();

        // Reads of the stored data come from the page cache.
        m.notify(|s, w| s.notify_store(w, FILE, 0, &data)).unwrap();
        let mut read = vec![0u8; SIZE];
        file.read_exact_at(&mut read, 0).unwrap();
        assert_eq!(read, data);
        assert_eq!(m.fs.reads.load(Ordering::Relaxed), 0);

        // The kernel sends the cached data back.
        m.notify(|s, w| s.notify_retrieve(w, 42, FILE, 0, SIZE as u32))
            .unwrap();
        let (inode, unique, offset, retrieved) =
            m.retrieved.recv_timeout(Duration::from_secs(5)).unwrap();
        assert_eq!((inode, unique, offset), (FILE, 42, 0));
        assert!(
            retrieved == data,
            "retrieved {} other bytes",
            retrieved.len()
        );

        // The kernel has no inode 99.
        let result = m.notify(|s, w| s.notify_store(w, 99, 0, b"x"));
        assert_eq!(errno(&result), Some(libc::ENOENT));
    }

    /// `store_and_retrieve()` with the async helpers, on a mount that `AsyncFuseServing` serves.
    #[cfg(feature = "async-io")]
    #[test]
    fn test_async_notify_store_and_retrieve() {
        let Some(m) = Mount::with(async_serving) else {
            return;
        };
        let file = File::open(m.path("file")).unwrap();
        let data: Vec<u8> = (0..SIZE).map(|i| (i % 251) as u8).collect();

        m.async_notify(async |s, w| s.async_notify_store(w, FILE, 0, &data).await)
            .unwrap();
        let mut read = vec![0u8; SIZE];
        file.read_exact_at(&mut read, 0).unwrap();
        assert_eq!(read, data);
        assert_eq!(m.fs.reads.load(Ordering::Relaxed), 0);

        m.async_notify(async |s, w| s.async_notify_retrieve(w, 42, FILE, 0, SIZE as u32).await)
            .unwrap();
        let (inode, unique, offset, retrieved) =
            m.retrieved.recv_timeout(Duration::from_secs(5)).unwrap();
        assert_eq!((inode, unique, offset), (FILE, 42, 0));
        assert!(
            retrieved == data,
            "retrieved {} other bytes",
            retrieved.len()
        );

        let result = m.async_notify(async |s, w| s.async_notify_store(w, 99, 0, b"x").await);
        assert_eq!(errno(&result), Some(libc::ENOENT));
    }

    #[test]
    fn test_notify_delete() {
        let Some(m) = Mount::new() else {
            return;
        };
        let file = File::open(m.path("gone")).unwrap();

        m.fs.deleted.store(true, Ordering::Relaxed);
        m.notify(|s, w| s.notify_delete(w, ROOT_ID, GONE, name(b"gone\0")))
            .unwrap();

        // The kernel unlinked its inode and looks the name up again.
        let mut st: libc::stat = unsafe { std::mem::zeroed() };
        assert_eq!(unsafe { libc::fstat(file.as_raw_fd(), &mut st) }, 0);
        assert_eq!(st.st_nlink, 0);
        let err = std::fs::metadata(m.path("gone")).unwrap_err();
        assert_eq!(err.kind(), io::ErrorKind::NotFound);
    }

    #[test]
    fn test_notify_expire_entry() {
        let Some(m) = Mount::new() else {
            return;
        };
        let file = File::open(m.path("file")).unwrap();
        let path = proc_path(&file);
        std::fs::metadata(m.path("file")).unwrap();
        assert_eq!(m.file_lookups(), 1);

        // The kernel keeps the entry but looks the name up again.
        let result = m.notify(|s, w| s.notify_expire_entry(w, ROOT_ID, name(b"file\0")));
        if errno(&result) == Some(libc::ENOSYS) {
            eprintln!("kernel without FUSE_HAS_EXPIRE_ONLY, skipping");
            return;
        }
        result.unwrap();
        assert_eq!(proc_path(&file), path);
        std::fs::metadata(m.path("file")).unwrap();
        assert_eq!(m.file_lookups(), 2);

        // Invalidating the entry drops it.
        m.notify(|s, w| s.notify_inval_entry(w, ROOT_ID, name(b"file\0")))
            .unwrap();
        assert_eq!(proc_path(&file), format!("{} (deleted)", path));
    }

    #[test]
    fn test_notify_increment_epoch() {
        let Some(m) = Mount::new() else {
            return;
        };
        std::fs::metadata(m.path("file")).unwrap();
        std::fs::metadata(m.path("file")).unwrap();
        assert_eq!(m.file_lookups(), 1);

        let result = m.notify(|s, w| s.notify_increment_epoch(w));
        if errno(&result) == Some(libc::EINVAL) {
            eprintln!("kernel without FUSE_NOTIFY_INC_EPOCH, skipping");
            return;
        }
        result.unwrap();
        std::fs::metadata(m.path("file")).unwrap();
        assert_eq!(m.file_lookups(), 2);
    }

    #[test]
    fn test_notify_prune() {
        let Some(m) = Mount::new() else {
            return;
        };
        std::fs::metadata(m.path("file")).unwrap();
        assert!(m.forgets.recv_timeout(Duration::from_millis(100)).is_err());

        // Nothing holds the inode, so the kernel forgets it.
        let result = m.notify(|s, w| s.notify_prune(w, &[FILE]));
        if errno(&result) == Some(libc::EINVAL) {
            eprintln!("kernel without FUSE_NOTIFY_PRUNE, skipping");
            return;
        }
        result.unwrap();
        assert_eq!(
            m.forgets.recv_timeout(Duration::from_secs(5)).unwrap(),
            FILE
        );
    }
}
