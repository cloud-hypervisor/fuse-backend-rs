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
use fuse_backend_rs::transport::{FuseChannelExt, FuseSession, FuseSessionExt as _};

use simple_logger::SimpleLogger;

/// A fusedev daemon example
#[allow(dead_code)]
pub struct Daemon {
    mountpoint: String,
    server: Arc<Server<Arc<Vfs>>>,
    thread_cnt: u32,
    // Use blocking fuse channels instead of the default epoll-based ones.
    blocking: bool,
    session: Option<FuseSession>,
}

pub enum PassthroughFsError {
    FuseError(fuse_backend_rs::Error),
    TransportError(fuse_backend_rs::transport::Error),
}

impl From<fuse_backend_rs::transport::Error> for PassthroughFsError {
    fn from(e: fuse_backend_rs::transport::Error) -> Self {
        PassthroughFsError::TransportError(e)
    }
}

#[allow(dead_code)]
impl Daemon {
    /// Creates a fusedev daemon instance
    pub fn new(src: &str, mountpoint: &str, thread_cnt: u32, blocking: bool) -> Result<Self> {
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
            blocking,
            session: None,
        })
    }

    /// Mounts a fusedev daemon to the mountpoint, then start service threads to handle
    /// FUSE requests.
    pub fn mount(&mut self) -> Result<()> {
        let mut se =
            FuseSession::new(Path::new(&self.mountpoint), "testpassthrough", "", false).unwrap();
        se.mount().unwrap();

        // Ask the kernel to resend pending requests, if any. This is
        // best-effort: FUSE_NOTIFY_RESEND was added in kernel 6.9 and older
        // kernels reject it with EINVAL, which used to abort the daemon at
        // startup. There is nothing to resend right after the connection is
        // established, so a failure here is harmless.
        let _ = se.try_with_writer(|writer| {
            self.server
                .notify_resend(writer)
                .map_err(PassthroughFsError::FuseError)
        });

        for _ in 0..self.thread_cnt {
            if self.blocking {
                spawn_fuse_server(
                    self.server.clone(),
                    se.new_blocking_channel().unwrap(),
                    true,
                );
            } else {
                spawn_fuse_server(self.server.clone(), se.new_channel().unwrap(), false);
            }
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

struct FuseServer<C> {
    server: Arc<Server<Arc<Vfs>>>,
    ch: C,
}

impl<C: FuseChannelExt> FuseServer<C> {
    fn svc_loop(&mut self) -> Result<()> {
        loop {
            if let Some((reader, writer)) = self
                .ch
                .next_request()
                .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?
            {
                if let Err(e) = self.server.handle_message(reader, writer, None, None) {
                    match e {
                        // EncodeMessage means the kernel has shut down the session.
                        fuse_backend_rs::Error::EncodeMessage(_) => break,
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

/// Spawn one service thread that drives `ch` until the session is torn down.
fn spawn_fuse_server<C>(server: Arc<Server<Arc<Vfs>>>, ch: C, blocking: bool)
where
    C: FuseChannelExt + Send + 'static,
{
    let mut fuse_server = FuseServer { server, ch };
    thread::Builder::new()
        .name("fuse_server".to_string())
        .spawn(move || {
            if blocking {
                info!("new fuse thread (blocking)");
            } else {
                info!("new fuse thread");
            }
            let _ = fuse_server.svc_loop();
            warn!("fuse service thread exits");
        })
        .unwrap();
}

struct Args {
    src: String,
    dest: String,
    threads: u32,
    blocking: bool,
}

fn help() {
    println!(
        "Usage:\n   passthrough <src> <dest> [threads] [blocking]\n   threads: service thread count (default 2)\n   blocking: true|false, use blocking fuse channels (default false)\n"
    );
}

fn parse_args() -> Result<Args> {
    let args = env::args().collect::<Vec<String>>();
    if args.len() < 3 {
        help();
        return Err(Error::from_raw_os_error(libc::EINVAL));
    }
    let threads: u32 = if args.len() >= 4 {
        args[3].parse().map_err(|_| {
            help();
            Error::from_raw_os_error(libc::EINVAL)
        })?
    } else {
        // Preserve the historical default: the daemon used to hardcode 2 threads,
        // so callers that pass no thread count (e.g. xfstests_pathr.sh) keep their
        // original parallelism.
        2
    };
    let blocking = if args.len() >= 5 {
        args[4].parse().map_err(|_| {
            help();
            Error::from_raw_os_error(libc::EINVAL)
        })?
    } else {
        false
    };
    let cmd_args = Args {
        src: args[1].clone(),
        dest: args[2].clone(),
        threads,
        blocking,
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

    let mut daemon = Daemon::new(src_dir, dest_dir, args.threads, args.blocking).unwrap();
    daemon.mount().unwrap();

    // main thread
    let mut signals = Signals::new(TERM_SIGNALS).unwrap();
    for _sig in signals.forever() {
        break;
    }

    daemon.umount().unwrap();

    Ok(())
}
