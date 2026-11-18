// SPDX-License-Identifier: Apache-2.0

//! A file system keeps the kernel's handle from a POLL request and wakes the waiting poll(2)
//! later. Mounting needs root or fusermount3, and the test skips without either.

#[cfg(target_os = "linux")]
mod poll {
    use std::ffi::CStr;
    use std::fs::File;
    use std::io;
    use std::os::unix::io::AsRawFd;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::mpsc::{channel, Sender};
    use std::sync::Arc;
    use std::thread;
    use std::time::Duration;

    use fuse_backend_core::abi::fuse_abi::{stat64, POLL_SCHEDULE_NOTIFY, ROOT_ID};
    use fuse_backend_core::api::filesystem::{Context, Entry, FileSystem};
    use fuse_backend_core::api::server::Server;
    use fuse_backend_fusedev::{
        FuseDevWriter, FuseServing, FuseSession, SyncFuseServing, SyncServingConfig,
    };
    use vmm_sys_util::tempdir::TempDir;

    const EVENTS: u64 = 2;

    /// A root directory with the file `events`, which is readable once `ready` is set. When a
    /// poll waits for it, the file system sends the kernel's handle to `waiting`.
    struct EventFs {
        ready: AtomicBool,
        waiting: Sender<u64>,
    }

    fn stat(inode: u64) -> stat64 {
        let mut st: stat64 = unsafe { std::mem::zeroed() };
        st.st_ino = inode;
        st.st_nlink = 1;
        st.st_mode = if inode == ROOT_ID {
            libc::S_IFDIR | 0o755
        } else {
            libc::S_IFREG | 0o444
        };
        st
    }

    impl FileSystem for EventFs {
        type Inode = u64;
        type Handle = u64;

        fn lookup(&self, _ctx: &Context, parent: u64, name: &CStr) -> io::Result<Entry> {
            if parent != ROOT_ID || name.to_bytes() != b"events" {
                return Err(io::Error::from_raw_os_error(libc::ENOENT));
            }
            Ok(Entry {
                inode: EVENTS,
                generation: 0,
                attr: stat(EVENTS),
                attr_flags: 0,
                attr_timeout: Duration::from_secs(60),
                entry_timeout: Duration::from_secs(60),
            })
        }

        fn getattr(
            &self,
            _ctx: &Context,
            inode: u64,
            _handle: Option<u64>,
        ) -> io::Result<(stat64, Duration)> {
            Ok((stat(inode), Duration::from_secs(60)))
        }

        fn poll(
            &self,
            _ctx: &Context,
            _inode: u64,
            _handle: u64,
            khandle: u64,
            flags: u32,
            events: u32,
        ) -> io::Result<u32> {
            if self.ready.load(Ordering::Acquire) {
                return Ok(events & libc::POLLIN as u32);
            }
            if flags & POLL_SCHEDULE_NOTIFY != 0 {
                let _ = self.waiting.send(khandle);
            }
            Ok(0)
        }
    }

    #[test]
    fn test_poll_wakeup() {
        let dir = TempDir::new().unwrap();
        let mut se = FuseSession::new(dir.as_path(), "poll_test", "", false).unwrap();
        se.set_allow_other(false);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return;
        }
        let (waiting_tx, waiting) = channel();
        let fs = Arc::new(EventFs {
            ready: AtomicBool::new(false),
            waiting: waiting_tx,
        });
        let server = Arc::new(Server::new(fs.clone()));
        let serving =
            SyncFuseServing::new(se, server.clone(), SyncServingConfig::default()).unwrap();

        let file = File::open(dir.as_path().join("events")).unwrap();
        let (polled_tx, polled) = channel();
        thread::spawn(move || {
            let mut pfd = libc::pollfd {
                fd: file.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            };
            let n = unsafe { libc::poll(&mut pfd, 1, 10_000) };
            let _ = polled_tx.send((n, pfd.revents));
        });

        // Nothing is ready, so poll(2) waits and the file system gets the kernel's handle.
        let kh = waiting.recv_timeout(Duration::from_secs(5)).unwrap();
        assert!(polled.recv_timeout(Duration::from_millis(100)).is_err());

        fs.ready.store(true, Ordering::Release);
        let mut buf = [0u8; 64];
        let fuse_fd = serving.session().get_fuse_file().unwrap().as_raw_fd();
        let w = FuseDevWriter::<()>::new(fuse_fd, &mut buf).unwrap();
        server.notify_poll_wakeup(w, kh).unwrap();
        assert_eq!(
            polled.recv_timeout(Duration::from_secs(5)).unwrap(),
            (1, libc::POLLIN)
        );
    }
}
