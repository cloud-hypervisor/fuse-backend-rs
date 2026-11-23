use log::{error, info, warn, LevelFilter};
use std::env;
use std::fs;
use std::io::{Error, Result};
use std::os::fd::{AsRawFd, BorrowedFd};
use std::path::Path;
use std::sync::{Arc, OnceLock};
use std::thread;
use std::time::Duration;

use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};

use fuse_backend_rs::abi::fuse_abi::FsOptions;
use fuse_backend_rs::api::{server::Server, Vfs, VfsOptions};
use fuse_backend_rs::async_runtime::{set_runtime_type, RuntimeType};
use fuse_backend_rs::passthrough::{BackingFiles, Config, PassthroughFs};
use fuse_backend_rs::transport::{
    fuse_backing_close, fuse_backing_open, AsyncFuseServing, AsyncServingConfig, FuseChannelExt,
    FuseServing, FuseSession, FuseSessionExt as _, SyncFuseServing, SyncServingConfig, UringConfig,
    UringFuseServing,
};

use simple_logger::SimpleLogger;

/// A serving layer of the library to use instead of the daemon's own service threads.
#[derive(Clone, Copy, Debug, PartialEq)]
enum Serving {
    Sync,
    Async,
    Uring,
}

/// Registers backing files on the FUSE device of the session, which is only
/// known once it is mounted.
#[derive(Default)]
struct FuseBackingFiles {
    fuse_file: OnceLock<fs::File>,
}

impl BackingFiles for FuseBackingFiles {
    fn open(&self, fd: BorrowedFd<'_>) -> Result<u32> {
        fuse_backing_open(self.fuse_file.get().unwrap(), fd.as_raw_fd())
    }

    fn close(&self, backing_id: u32) -> Result<()> {
        fuse_backing_close(self.fuse_file.get().unwrap(), backing_id)
    }
}

/// A fusedev daemon example
#[allow(dead_code)]
pub struct Daemon {
    mountpoint: String,
    server: Arc<Server<Arc<Vfs>>>,
    thread_cnt: u32,
    // Use blocking fuse channels instead of the default epoll-based ones.
    blocking: bool,
    serving: Option<Serving>,
    backing_files: Option<Arc<FuseBackingFiles>>,
    session: Option<FuseSession>,
    serving_layer: Option<Box<dyn FuseServing>>,
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
    fn new(args: &Args) -> Result<Self> {
        // create vfs
        let mut opts = VfsOptions {
            no_open: false,
            no_opendir: false,
            no_writeback: args.no_writeback,
            ..Default::default()
        };
        if args.kernel_passthrough {
            opts.out_opts |= FsOptions::PASSTHROUGH;
        }
        let vfs = Vfs::new(opts);

        // create passthrough fs
        let cfg = Config {
            root_dir: args.src.clone(),
            do_import: false,
            ..Default::default()
        };
        let mut fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();
        let backing_files = args
            .kernel_passthrough
            .then(|| Arc::new(FuseBackingFiles::default()));
        if let Some(files) = &backing_files {
            fs.set_backing_files(files.clone());
        }

        // attach passthrough fs to vfs root
        vfs.mount(Box::new(fs), "/").unwrap();

        let server = Arc::new(Server::new(Arc::new(vfs)));
        if args.serving == Some(Serving::Uring) {
            // The capability goes into the INIT reply, so request it before mounting.
            server.set_uring(true);
        }
        if backing_files.is_some() {
            // Allow a source directory on a stacked file system such as overlayfs.
            server.set_max_stack_depth(2)?;
        }

        Ok(Daemon {
            mountpoint: args.dest.clone(),
            server,
            thread_cnt: args.threads,
            blocking: args.blocking,
            serving: args.serving,
            backing_files,
            session: None,
            serving_layer: None,
        })
    }

    /// Mounts a fusedev daemon to the mountpoint, then start service threads to handle
    /// FUSE requests.
    pub fn mount(&mut self) -> Result<()> {
        let mut se =
            FuseSession::new(Path::new(&self.mountpoint), "testpassthrough", "", false).unwrap();
        se.mount().unwrap();
        if let Some(files) = &self.backing_files {
            let fuse_file = se.get_fuse_file().unwrap().try_clone()?;
            files.fuse_file.set(fuse_file).unwrap();
        }

        match self.serving {
            None => self.spawn_service_threads(se),
            Some(serving) => self.serving_layer = Some(self.new_serving_layer(serving, se)?),
        }
        if self.backing_files.is_some() {
            self.check_kernel_passthrough()?;
        }
        Ok(())
    }

    fn new_serving_layer(&self, serving: Serving, se: FuseSession) -> Result<Box<dyn FuseServing>> {
        let workers = self.thread_cnt as usize;
        let server = self.server.clone();
        Ok(match serving {
            Serving::Sync => {
                let cfg = SyncServingConfig {
                    workers,
                    blocking: self.blocking,
                };
                Box::new(SyncFuseServing::new(se, server, cfg).map_err(Error::other)?)
            }
            Serving::Async => {
                let cfg = AsyncServingConfig {
                    workers,
                    ..Default::default()
                };
                Box::new(AsyncFuseServing::new(se, server, cfg).map_err(Error::other)?)
            }
            Serving::Uring => {
                let cfg = UringConfig {
                    workers,
                    ..Default::default()
                };
                Box::new(UringFuseServing::new(se, server, cfg).map_err(Error::other)?)
            }
        })
    }

    /// Fail unless the kernel enabled passthrough at INIT. Otherwise the daemon would serve
    /// the IO itself.
    fn check_kernel_passthrough(&self) -> Result<()> {
        // The kernel sends INIT right after the mount.
        for _ in 0..500 {
            let (_, opts) = self.server.init_state();
            if opts.contains(FsOptions::PASSTHROUGH) {
                return Ok(());
            }
            if !opts.is_empty() {
                return Err(Error::other(
                    "the kernel did not enable passthrough at INIT",
                ));
            }
            thread::sleep(Duration::from_millis(10));
        }
        Err(Error::other(
            "no INIT request within 5 seconds of the mount",
        ))
    }

    fn spawn_service_threads(&mut self, mut se: FuseSession) {
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
    }

    /// Umounts and destroies a fusedev daemon
    pub fn umount(&mut self) -> Result<()> {
        if let Some(mut se) = self.session.take() {
            se.umount().unwrap();
            se.wake().unwrap();
        }
        // Dropping a serving layer unmounts the session and joins its threads.
        self.serving_layer = None;
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
    serving: Option<Serving>,
    runtime: Option<RuntimeType>,
    no_writeback: bool,
    kernel_passthrough: bool,
}

fn help() {
    println!(
        "Usage:
   passthrough <src> <dest> [threads] [blocking] [options]
   threads: service thread count (default 2)
   blocking: true|false, use blocking fuse channels (default false)
Options:
   --serving sync|async|uring: serve with SyncFuseServing, AsyncFuseServing or
      UringFuseServing instead of the daemon's own service threads
   --runtime tokio|uring: the async runtime of --serving async (default: tokio-uring
      if io_uring works, tokio otherwise)
   --no-writeback: turn the FUSE writeback cache off
   --kernel-passthrough: let the kernel pass reads, writes and mmap of open files
      through to the source files (Linux 6.9+), turns the writeback cache off
"
    );
}

fn parse_args() -> Result<Args> {
    let invalid = || {
        help();
        Error::from_raw_os_error(libc::EINVAL)
    };
    let args = env::args().collect::<Vec<String>>();
    if args[1..].iter().any(|a| a == "-h" || a == "--help") {
        help();
        std::process::exit(0);
    }
    if args.len() < 3 {
        return Err(invalid());
    }
    let mut res = Args {
        src: args[1].clone(),
        dest: args[2].clone(),
        // Preserve the historical default: the daemon used to hardcode 2 threads,
        // so callers that pass no thread count (e.g. xfstests_pathr.sh) keep their
        // original parallelism.
        threads: 2,
        blocking: false,
        serving: None,
        runtime: None,
        no_writeback: false,
        kernel_passthrough: false,
    };
    let mut positional = 0;
    let mut rest = args[3..].iter();
    while let Some(arg) = rest.next() {
        match arg.as_str() {
            "--serving" => {
                res.serving = Some(match rest.next().map(String::as_str) {
                    Some("sync") => Serving::Sync,
                    Some("async") => Serving::Async,
                    Some("uring") => Serving::Uring,
                    _ => return Err(invalid()),
                })
            }
            "--runtime" => {
                res.runtime = match rest.next().map(String::as_str) {
                    Some("tokio") => Some(RuntimeType::Tokio),
                    Some("uring") => Some(RuntimeType::Uring),
                    _ => return Err(invalid()),
                }
            }
            "--no-writeback" => res.no_writeback = true,
            "--kernel-passthrough" => {
                res.kernel_passthrough = true;
                // The kernel ignores FUSE_PASSTHROUGH along with the writeback cache.
                res.no_writeback = true;
            }
            _ if positional == 0 => {
                res.threads = arg.parse().map_err(|_| invalid())?;
                positional += 1;
            }
            _ if positional == 1 => {
                res.blocking = arg.parse().map_err(|_| invalid())?;
                positional += 1;
            }
            _ => return Err(invalid()),
        }
    }
    if res.src.is_empty() || res.dest.is_empty() {
        return Err(invalid());
    }
    // Blocking channels only exist on the classic synchronous transport, and
    // the runtime only drives the asynchronous serving layer.
    if (res.blocking && matches!(res.serving, Some(Serving::Async | Serving::Uring)))
        || (res.runtime.is_some() && res.serving != Some(Serving::Async))
    {
        return Err(invalid());
    }
    Ok(res)
}

fn main() -> Result<()> {
    SimpleLogger::new()
        .with_level(LevelFilter::Info)
        .init()
        .unwrap();
    let args = parse_args().unwrap();
    // Fix the runtime type before anything creates a runtime or an async file.
    if let Some(runtime) = args.runtime {
        set_runtime_type(runtime)?;
    }

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
        "test passthroughfs src {:?} mountpoint {} serving {:?} runtime {:?} writeback {} \
         kernel passthrough {}",
        src_dir, dest_dir, args.serving, args.runtime, !args.no_writeback, args.kernel_passthrough,
    );

    let mut daemon = Daemon::new(&args).unwrap();
    daemon.mount().unwrap();

    // main thread
    let mut signals = Signals::new(TERM_SIGNALS).unwrap();
    for _sig in signals.forever() {
        break;
    }

    daemon.umount().unwrap();

    Ok(())
}
