// Copyright 2021 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

use log::{error, info, warn};
use std::io::Result;
use std::path::Path;
use std::sync::Arc;
use std::thread;

use fuse_backend_rs::api::{server::Server, Vfs, VfsOptions};
use fuse_backend_rs::passthrough::{Config, PassthroughFs};
use fuse_backend_rs::transport::{FuseChannel, FuseSession};
#[cfg(target_os = "linux")]
use nix::mount::MsFlags;

/// A fusedev daemon example
#[allow(dead_code)]
pub struct Daemon {
    mountpoint: String,
    server: Arc<Server<Arc<Vfs>>>,
    thread_cnt: u32,
    session: Option<FuseSession>,
    #[cfg(target_os = "linux")]
    mount_flags: Option<MsFlags>,
}

#[allow(dead_code)]
impl Daemon {
    /// Creates a fusedev daemon instance
    pub fn new(src: &str, mountpoint: &str, thread_cnt: u32) -> Result<Self> {
        // create vfs
        let vfs = Vfs::new(VfsOptions {
            #[cfg(not(target_os = "macos"))]
            no_open: false,
            #[cfg(not(target_os = "macos"))]
            no_opendir: false,
            ..Default::default()
        });

        // create passthrough fs
        let cfg = Config {
            root_dir: src.to_string(),
            do_import: false,
            // The macOS e2e test exercises the xattr family through the
            // mount; on Linux the config stays at the historical default.
            xattr: cfg!(target_os = "macos"),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();

        // attach passthrough fs to vfs root
        vfs.mount(Box::new(fs), "/").unwrap();

        Ok(Daemon {
            mountpoint: mountpoint.to_string(),
            server: Arc::new(Server::new(Arc::new(vfs))),
            thread_cnt,
            session: None,
            #[cfg(target_os = "linux")]
            mount_flags: None,
        })
    }

    /// Set custom mount flags to pass to the session
    #[cfg(target_os = "linux")]
    pub fn set_mount_flags(&mut self, flags: MsFlags) {
        self.mount_flags = Some(flags);
    }

    /// Mounts a fusedev daemon to the mountpoint, then start service threads to handle
    /// FUSE requests.
    pub fn mount(&mut self) -> Result<()> {
        let mut se =
            FuseSession::new(Path::new(&self.mountpoint), "passthru_example", "", false).unwrap();

        #[cfg(target_os = "linux")]
        if let Some(flags) = self.mount_flags {
            se.set_mount_flags(flags);
        }

        se.mount().unwrap();
        for _ in 0..self.thread_cnt {
            let mut server = FuseServer {
                server: self.server.clone(),
                ch: se.new_channel().unwrap(),
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
        // fuse-t mounts in the background: block until the mount is up.
        // Printed around the wait so a hung first mount pinpoints itself in
        // the CI log — the helper forked and exec'd, and this is the last
        // line before the fuse-t mount status byte arrives (or never does).
        #[cfg(all(target_os = "macos", feature = "fuse-t"))]
        println!("fuse-t helper started; waiting for the mount to come up");
        #[cfg(all(target_os = "macos", feature = "fuse-t"))]
        se.wait_mount().unwrap();
        println!("mount is up");
        self.session = Some(se);
        Ok(())
    }

    /// Umounts and destroies a fusedev daemon
    pub fn umount(&mut self) -> Result<()> {
        if let Some(mut se) = self.session.take() {
            se.umount().unwrap();
            se.wake().unwrap();
        }
        Ok(())
    }
}

impl Drop for Daemon {
    fn drop(&mut self) {
        let _ = self.umount();
    }
}

struct FuseServer {
    server: Arc<Server<Arc<Vfs>>>,
    ch: FuseChannel,
}

impl FuseServer {
    fn svc_loop(&mut self) -> Result<()> {
        // Given error EBADF, it means kernel has shut down this session.
        let _ebadf = std::io::Error::from_raw_os_error(libc::EBADF);
        loop {
            if let Some((reader, writer)) = self
                .ch
                .get_request()
                .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?
            {
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
