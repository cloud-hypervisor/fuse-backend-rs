use fuse_backend_rs::transport::FuseDevWriter;
use fuse_backend_rs::transport::Writer;
use log::{error, info, warn, LevelFilter};
use std::env;
use std::fs;
use std::io::{Error, Result};
use std::path::Path;
use std::sync::Arc;
use std::thread;

use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};

use fuse_backend_rs::api::{server::Server, Vfs, VfsOptions};
use fuse_backend_rs::passthrough::{Config, PassthroughFs};
use fuse_backend_rs::transport::{FuseChannel, FuseSession};
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};

use simple_logger::SimpleLogger;

/// A fusedev daemon example
#[allow(dead_code)]
pub struct Daemon {
    mountpoint: String,
    server: Arc<Server<Arc<Vfs>>>,
    thread_cnt: u32,
    session: Option<FuseSession>,
}

#[allow(dead_code)]
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
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();

        // attach passthrough fs to vfs root
        vfs.mount(Box::new(fs), "/").unwrap();

        Ok(Daemon {
            mountpoint: mountpoint.to_string(),
            server: Arc::new(Server::new(Arc::new(vfs))),
            thread_cnt,
            session: None,
        })
    }

    /// Mounts a fusedev daemon to the mountpoint, then start service threads to handle
    /// FUSE requests.
    pub fn mount(&mut self) -> Result<()> {
        let mut se =
            FuseSession::new(Path::new(&self.mountpoint), "testpassthrough", "", false).unwrap();
        se.mount().unwrap();
        
        se.with_writer(|writer| {
            self.server.notify_resend(writer).unwrap();
        });

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
                if let Err(e) = self
                    .server
                    .handle_message(reader, writer.into(), None, None)
                {
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

struct Args {
    src: String,
    dest: String,
}

fn help() {
    println!("Usage:\n   passthrough <src> <dest>\n");
}

fn parse_args() -> Result<Args> {
    let args = env::args().collect::<Vec<String>>();
    let cmd_args = Args {
        src: args[1].clone(),
        dest: args[2].clone(),
    };
    if cmd_args.src.len() == 0 || cmd_args.dest.len() == 0 {
        help();
        return Err(Error::from_raw_os_error(libc::EINVAL));
    }
    Ok(cmd_args)
}

fn main() -> Result<()> {
    SimpleLogger::new()
        .with_level(LevelFilter::Info)
        .init()
        .unwrap();
    let args = parse_args().unwrap();

    // Check if src exists, create dir if not.
    let src = Path::new(args.src.as_str());
    let src_dir = src.to_str().unwrap();
    if src.exists() {
        if !src.is_dir() {
            error!("src {} is not a directory", src_dir);
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
    } else {
        fs::create_dir_all(src_dir).unwrap();
    }

    let dest = Path::new(args.dest.as_str());
    let dest_dir = dest.to_str().unwrap();
    if dest.exists() {
        if !dest.is_dir() {
            error!("dest {} is not a directory", dest_dir);
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
    } else {
        fs::create_dir_all(dest_dir).unwrap();
    }
    info!(
        "test passthroughfs src {:?} mountpoint {}",
        src_dir, dest_dir
    );

    let mut daemon = Daemon::new(src_dir, dest_dir, 2).unwrap();
    daemon.mount().unwrap();

    // main thread
    let mut signals = Signals::new(TERM_SIGNALS).unwrap();
    for _sig in signals.forever() {
        break;
    }

    daemon.umount().unwrap();

    Ok(())
}
