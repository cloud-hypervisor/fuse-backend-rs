// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Tests exercising the Vfs layer together with real filesystem drivers.
//!
//! Unlike the unit tests embedded in the `api` modules of `fuse-backend-core`,
//! these tests depend on a concrete driver, so they live in the umbrella
//! crate's integration tests — the only place where both the Vfs API and the
//! `passthrough` driver are visible. They only use the public crate API.

/// Vfs save/restore round trips with real `PassthroughFs` backends mounted,
/// including index allocation state and per-mount restore.
#[cfg(all(
    target_os = "linux",
    feature = "persist",
    any(feature = "fusedev", feature = "virtiofs", feature = "passthrough")
))]
mod vfs_persist {
    use fuse_backend_rs::api::filesystem::{FileSystem, FsOptions};
    use fuse_backend_rs::api::{Vfs, VfsIndex, VfsOptions};
    use fuse_backend_rs::passthrough::{Config, PassthroughFs};

    fn new_backend_fs() -> Box<PassthroughFs<()>> {
        let fs_cfg = Config::default();
        let fs = PassthroughFs::<()>::new(fs_cfg.clone()).unwrap();
        fs.import().unwrap();
        Box::new(fs)
    }

    #[test]
    fn test_vfs_save_restore_with_backend_fs() {
        // create new vfs
        let vfs = &Vfs::new(VfsOptions::default());
        let paths = ["/a", "/a/b", "/a/b/c", "/b", "/b/a/c", "/d"];
        // record the backend fs and their VfsIndexes
        let backend_fs_list: Vec<(&str, VfsIndex)> = paths
            .iter()
            .map(|path| {
                let fs = new_backend_fs();
                let idx = vfs.mount(fs, path).unwrap();

                (path.to_owned(), idx)
            })
            .collect();

        // save the vfs state using Snapshot
        let mut buf = vfs.save_to_bytes().unwrap();

        // restore the vfs state
        let restored_vfs = &Vfs::new(VfsOptions::default());
        restored_vfs.restore_from_bytes(&mut buf).unwrap();
        // restore the backend fs
        backend_fs_list.into_iter().for_each(|(path, idx)| {
            let fs = new_backend_fs();
            vfs.restore_mount(fs, idx, path).unwrap();
        });

        // check the vfs and restored_vfs
        assert_eq!(vfs.initialized(), restored_vfs.initialized());
        for path in paths.iter() {
            let inode = vfs.get_root_pseudofs().path_walk(path).unwrap();
            let restored_inode = restored_vfs.get_root_pseudofs().path_walk(path).unwrap();
            assert_eq!(inode, restored_inode);
        }

        // The fs index allocation state must match as well: both instances
        // have consumed the same number of indexes, so a new mount on either
        // must be handed the same index.
        let idx = vfs.mount(new_backend_fs(), "/new").unwrap();
        let restored_idx = restored_vfs.mount(new_backend_fs(), "/new").unwrap();
        assert_eq!(idx, restored_idx);
    }

    #[test]
    fn test_vfs_save_restore_with_backend_fs_with_initialized() {
        // create new vfs
        let vfs = &Vfs::new(VfsOptions::default());
        let paths = ["/a", "/a/b", "/a/b/c", "/b", "/b/a/c", "/d"];
        let backend_fs_list: Vec<(&str, VfsIndex)> = paths
            .iter()
            .map(|path| {
                let fs = new_backend_fs();
                let idx = vfs.mount(fs, path).unwrap();

                (path.to_owned(), idx)
            })
            .collect();
        vfs.init(FsOptions::ASYNC_READ).unwrap();
        assert!(vfs.initialized());

        // save the vfs state using Snapshot
        let mut buf = vfs.save_to_bytes().unwrap();

        // restore the vfs state
        let restored_vfs = &Vfs::new(VfsOptions::default());
        restored_vfs.restore_from_bytes(&mut buf).unwrap();

        // restore the backend fs
        backend_fs_list.into_iter().for_each(|(path, idx)| {
            let fs = new_backend_fs();
            vfs.restore_mount(fs, idx, path).unwrap();
        });

        // check the vfs and restored_vfs
        assert!(vfs.initialized());
        assert!(restored_vfs.initialized());
        for path in paths.iter() {
            let inode = vfs.get_root_pseudofs().path_walk(path).unwrap();
            let restored_inode = restored_vfs.get_root_pseudofs().path_walk(path).unwrap();
            assert_eq!(inode, restored_inode);
        }

        // The fs index allocation state must match as well.
        let idx = vfs.mount(new_backend_fs(), "/new").unwrap();
        let restored_idx = restored_vfs.mount(new_backend_fs(), "/new").unwrap();
        assert_eq!(idx, restored_idx);
    }
}

/// Async Vfs operations driven down to a real `PassthroughFs` instance.
#[cfg(all(
    target_os = "linux",
    feature = "async-io",
    any(feature = "fusedev", feature = "virtiofs", feature = "passthrough")
))]
mod vfs_async {
    use std::ffi::CString;
    use std::io;
    use std::sync::Arc;

    use async_trait::async_trait;

    use fuse_backend_rs::api::filesystem::{
        AsyncFileSystem, AsyncZeroCopyWriter, Context, FileSystem, FsOptions, ZeroCopyWriter,
        ROOT_ID,
    };
    use fuse_backend_rs::api::{Vfs, VfsOptions};
    use fuse_backend_rs::file_buf::FileVolatileSlice;
    use fuse_backend_rs::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};
    use fuse_backend_rs::passthrough::{Config, PassthroughFs};

    /// An in-memory sink implementing `AsyncZeroCopyWriter`, to receive data
    /// from `async_read()`.
    struct MemWriter(Vec<u8>);

    impl io::Write for MemWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.0.extend_from_slice(buf);
            Ok(buf.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl ZeroCopyWriter for MemWriter {
        fn write_from(
            &mut self,
            f: &mut dyn FileReadWriteVolatile,
            count: usize,
            off: u64,
        ) -> io::Result<usize> {
            if self.0.len() < count {
                self.0.resize(count, 0);
            }
            // Safe because the slice points into `self.0` and doesn't out-live it.
            // The file offset only selects the read position within `f`; received
            // data is always placed at the start of the buffer.
            let slice = unsafe { FileVolatileSlice::from_raw_ptr(self.0.as_mut_ptr(), count) };
            f.read_at_volatile(slice, off)
        }

        fn available_bytes(&self) -> usize {
            usize::MAX
        }
    }

    #[async_trait(?Send)]
    impl AsyncZeroCopyWriter for MemWriter {
        async fn async_write_from(
            &mut self,
            _f: Arc<dyn AsyncFileReadWriteVolatile>,
            _count: usize,
            _off: u64,
        ) -> io::Result<usize> {
            unreachable!("the synchronous delegation never uses the async zero-copy path")
        }
    }

    // Integration test: drive async requests through the Vfs layer down to a
    // real `PassthroughFs` instance, covering inode remapping on the way.
    #[tokio::test]
    async fn test_vfs_async_passthrough() {
        let source = tempfile::tempdir().unwrap();
        std::fs::write(source.path().join("testfile"), b"hello vfs").unwrap();

        let cfg = Config {
            root_dir: source.path().to_str().unwrap().to_string(),
            do_import: true,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::all()).unwrap();

        // Disable zero-message open/opendir so that `async_open()` and
        // `async_read()` are actually exercised through the Vfs layer.
        let vfs = Vfs::new(VfsOptions {
            no_open: false,
            no_opendir: false,
            ..Default::default()
        });
        vfs.mount(Box::new(fs), "/").unwrap();

        let ctx = Context {
            uid: unsafe { libc::getuid() },
            gid: unsafe { libc::getgid() },
            pid: unsafe { libc::getpid() },
            ..Default::default()
        };

        // Lookup the file through the Vfs layer.
        let name = CString::new("testfile").unwrap();
        let entry = vfs
            .async_lookup(&ctx, ROOT_ID.into(), name.as_c_str())
            .await
            .unwrap();
        assert_ne!(entry.inode, 0);

        let (attr, _) = vfs
            .async_getattr(&ctx, entry.inode.into(), None)
            .await
            .unwrap();
        assert_eq!(attr.st_size, 9);

        // Open and read the file back through the Vfs layer.
        let (handle, _opts) = vfs
            .async_open(&ctx, entry.inode.into(), libc::O_RDONLY as u32, 0)
            .await
            .unwrap();
        let handle = handle.unwrap();
        let mut w = MemWriter(Vec::new());
        let n = vfs
            .async_read(
                &ctx,
                entry.inode.into(),
                handle,
                &mut w,
                9,
                0,
                None,
                libc::O_RDONLY as u32,
            )
            .await
            .unwrap();
        assert_eq!(n, 9);
        assert_eq!(&w.0, b"hello vfs");
    }
}
