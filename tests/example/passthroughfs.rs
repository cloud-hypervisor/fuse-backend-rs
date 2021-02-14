// Copyright 2021 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

use std::io::Result;
use std::path::Path;
use std::sync::Arc;
use std::thread;

use vmm_sys_util::eventfd::EventFd;

use fuse_backend_rs::api::{server::Server, Vfs, VfsOptions};
use fuse_backend_rs::async_util::AsyncDriver;
use fuse_backend_rs::passthrough::{Config, PassthroughFs};
use fuse_backend_rs::transport::fusedev::{FuseChannel, FuseSession};

/// A fusedev daemon example
pub struct Daemon {
    mountpoint: String,
    server: Arc<Server<Arc<Vfs<AsyncDriver>>>>,
    thread_cnt: u32,
    event_fd: EventFd,
    session: Option<FuseSession>,
}

impl Daemon {
    /// Creates a fusedev daemon instance
    pub fn new(src: &str, mountpoint: &str, thread_cnt: u32) -> Result<Self> {
        // create vfs
        let vfs = Vfs::new(VfsOptions {
            no_open: false,
            no_opendir: false,
            ..Default::default()
        });

        // create passthrough fs
        let mut cfg = Config::default();
        cfg.root_dir = src.to_string();
        cfg.do_import = false;
        let fs = PassthroughFs::new(cfg).unwrap();
        fs.import().unwrap();

        // attach passthrough fs to vfs root
        vfs.mount(Box::new(fs), "/").unwrap();

        Ok(Daemon {
            mountpoint: mountpoint.to_string(),
            server: Arc::new(Server::new(Arc::new(vfs))),
            thread_cnt,
            event_fd: EventFd::new(0).unwrap(),
            session: None,
        })
    }

    /// Mounts a fusedev daemon to the mountpoint, then start service threads to handle
    /// FUSE requests.
    pub fn mount(&mut self) -> Result<()> {
        let mut se = FuseSession::new(Path::new(&self.mountpoint), "passthru_example", "").unwrap();
        se.mount().unwrap();
        for _ in 0..self.thread_cnt {
            let server = FuseServer {
                server: self.server.clone(),
                ch: se.new_channel(self.event_fd.try_clone().unwrap()).unwrap(),
            };
            let _thread = thread::Builder::new()
                .name("fuse_server".to_string())
                .spawn(move || {
                    info!("new fuse thread");
                    let _ = server.svc_loop();
                    warn!("fuse service thread exits");
                })
                .unwrap();
        }
        self.session = Some(se);
        Ok(())
    }

    /// Umounts and destroies a fusedev daemon
    pub fn umount(&mut self) -> Result<()> {
        if let Some(mut se) = self.session.take() {
            se.umount().unwrap();
        }
        self.event_fd.write(1)?;
        Ok(())
    }
}

impl Drop for Daemon {
    fn drop(&mut self) {
        let _ = self.umount();
    }
}

struct FuseServer {
    server: Arc<Server<Arc<Vfs<AsyncDriver>>>>,
    ch: FuseChannel,
}

impl FuseServer {
    fn svc_loop(&self) -> Result<()> {
        let mut buf = vec![0x0u8; 1024 * 1024];

        // Given error EBADF, it means kernel has shut down this session.
        let _ebadf = std::io::Error::from_raw_os_error(libc::EBADF);
        loop {
            if let Some(reader) = self
                .ch
                .get_reader(&mut buf)
                .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?
            {
                let writer = self
                    .ch
                    .get_writer()
                    .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?;
                if let Err(e) = self.server.handle_message(reader, writer, None, None) {
                    match e {
                        fuse_backend_rs::Error::EncodeMessage(_ebadf) => {
                            break;
                        }
                        _ => {
                            error!("Handling fuse message failed");
                            continue;
                        }
                    }
                }
            } else {
                info!("fuse server exits");
                break;
            }
        }
        Ok(())
    }
}
