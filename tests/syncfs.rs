// SPDX-License-Identifier: Apache-2.0

//! Mounts a `PassthroughFs` on its own and behind a `Vfs`, with and without asking for
//! `FsOptions::HAS_SYNCFS`. Each run calls `syncfs(2)` on the mount and checks that SYNCFS
//! reaches the server only if the flag was negotiated. Since Linux 7.4 the kernel offers the
//! flag to a server that opened /dev/fuse with CAP_SYS_ADMIN in the initial user namespace.
//! Needs root, and is skipped without it.

#[cfg(all(feature = "fusedev", target_os = "linux"))]
mod fusedev_tests {
    use std::fs::File;
    use std::os::unix::io::AsRawFd;
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;
    use std::{io, thread};

    use fuse_backend_rs::abi::fuse_abi::{FsOptions, InHeader, Opcode, OutHeader};
    use fuse_backend_rs::api::filesystem::FileSystem;
    use fuse_backend_rs::api::server::{InitParams, MetricsHook, Server};
    use fuse_backend_rs::api::{Vfs, VfsOptions};
    use fuse_backend_rs::passthrough::{Config, PassthroughFs};
    use fuse_backend_rs::transport::FuseSession;
    use vmm_sys_util::tempdir::TempDir;

    /// Records whether the kernel offered `HAS_SYNCFS` and counts the SYNCFS requests.
    #[derive(Default)]
    struct SyncfsHook {
        offered: AtomicBool,
        requests: AtomicUsize,
    }

    impl MetricsHook for SyncfsHook {
        fn collect(&self, ih: &InHeader) {
            if ih.opcode == Opcode::Syncfs as u32 {
                self.requests.fetch_add(1, Ordering::Relaxed);
            }
        }

        fn release(&self, _oh: Option<&OutHeader>) {}

        fn on_init_params(&self, init_params: &InitParams) {
            let offered = init_params.capable.contains(FsOptions::HAS_SYNCFS);
            self.offered.store(offered, Ordering::Relaxed);
        }
    }

    /// Serve `fs` on a new mount, run `syncfs(2)` on it, and check that SYNCFS reached the
    /// server only if `HAS_SYNCFS` was negotiated, which needs `asked` and the kernel's offer.
    fn check_syncfs<F: FileSystem + Send + Sync + 'static>(fs: F, asked: bool) {
        if unsafe { libc::geteuid() } != 0 {
            eprintln!("not root, skipping");
            return;
        }
        let mountpoint = TempDir::new().unwrap();
        let mut se = FuseSession::new(mountpoint.as_path(), "syncfs", "", false).unwrap();
        se.mount().unwrap();
        let server = Arc::new(Server::new(fs));
        let hook = Arc::new(SyncfsHook::default());
        let mut ch = se.new_channel().unwrap();
        let handle = {
            let (server, hook) = (server.clone(), hook.clone());
            thread::spawn(move || {
                while let Ok(Some((reader, writer))) = ch.get_request() {
                    if server
                        .handle_message(reader, writer, None, Some(&*hook))
                        .is_err()
                    {
                        break;
                    }
                }
            })
        };

        // Opening the root waits for INIT. Check errors only after the unmount, so that a
        // failure doesn't leave the mount behind.
        let synced = File::open(mountpoint.as_path()).and_then(|root| {
            // SAFETY: syncfs() takes no pointers, and `root` is open for the call.
            match unsafe { libc::syncfs(root.as_raw_fd()) } {
                0 => Ok(()),
                _ => Err(io::Error::last_os_error()),
            }
        });
        let negotiated = server.init_state().1.contains(FsOptions::HAS_SYNCFS);
        let offered = hook.offered.load(Ordering::Relaxed);
        let requests = hook.requests.load(Ordering::Relaxed);
        se.umount().unwrap();
        se.wake().unwrap();
        handle.join().unwrap();

        synced.unwrap();
        if asked && !offered {
            eprintln!("the kernel doesn't offer FUSE_HAS_SYNCFS, checking only that none arrives");
        }
        assert_eq!(negotiated, asked && offered, "asked {asked}");
        assert_eq!(
            requests > 0,
            negotiated,
            "asked {asked}, {requests} requests"
        );
    }

    #[test]
    fn integration_syncfs_passthrough() {
        let source = TempDir::new().unwrap();
        for asked in [false, true] {
            let fs = PassthroughFs::<()>::new(Config {
                root_dir: source.as_path().to_string_lossy().to_string(),
                syncfs: asked,
                ..Default::default()
            })
            .unwrap();
            check_syncfs(fs, asked);
        }
    }

    #[test]
    fn integration_syncfs_vfs() {
        let source = TempDir::new().unwrap();
        for asked in [false, true] {
            let fs = PassthroughFs::<()>::new(Config {
                root_dir: source.as_path().to_string_lossy().to_string(),
                do_import: false,
                ..Default::default()
            })
            .unwrap();
            fs.import().unwrap();
            let mut opts = VfsOptions::default();
            opts.out_opts.set(FsOptions::HAS_SYNCFS, asked);
            let vfs = Vfs::new(opts);
            vfs.mount(Box::new(fs), "/").unwrap();
            check_syncfs(vfs, asked);
        }
    }
}
