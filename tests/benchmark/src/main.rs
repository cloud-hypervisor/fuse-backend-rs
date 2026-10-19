// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

//! A minimal fusedev passthrough daemon used to benchmark the synchronous
//! and asynchronous IO paths with external tools such as fio.
//!
//! Usage: `fuse-backend-rs-benchmark <src> <mountpoint> [--async|--uring] [--threads N] [--sync-blocking] [--uring-bufs N] [--uring-zero-copy] [--no-backing-direct-io]`
//!
//! - default (sync) mode: requests are served by `N` worker threads of the
//!   `SyncFuseServing` serving layer, each reading from its own fuse channel
//!   (the classic multi-threaded design); `--sync-blocking` selects blocking
//!   channels cloned with `FUSE_DEV_IOC_CLONE` instead of epoll-based ones.
//! - `--async` mode: requests are served by `N` asynchronous workers
//!   (`AsyncFuseServing`), each running a `FuseDevTask` on its own async
//!   runtime (tokio-uring when io_uring is available) and its own
//!   `/dev/fuse` file description.
//! - `--uring` mode: requests are served through the FUSE-over-io_uring
//!   transport (`UringFuseServing`, experimental, requires kernel 6.14+);
//!   `N` limits the number of io_uring worker threads. `--uring-bufs N`
//!   sets `UringConfig::bufs_per_queue`, the number of buffers in each
//!   queue's buffer pool on kernels with buffer pools. `0` gives every ring
//!   entry a buffer of its own. `--uring-zero-copy` serves reads and writes
//!   with zero-copy (`UringConfig::zero_copy` and
//!   `Config::uring_zero_copy`), which needs CAP_SYS_ADMIN.
//!
//! `--no-backing-direct-io` opens the backing files without O_DIRECT even when
//! the client asks for it (`Config::allow_direct_io = false`). Requests of a
//! client that opens with O_DIRECT still reach the daemon as direct IO, and
//! opens without O_DIRECT on the backing file can use zero-copy.

#[cfg(target_os = "linux")]
mod daemon {
    use std::env;
    use std::fs;
    use std::io::{Error, Result};
    use std::path::Path;
    use std::sync::Arc;

    use log::{error, info, LevelFilter};
    use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
    use simple_logger::SimpleLogger;

    use fuse_backend_rs::api::server::Server;
    use fuse_backend_rs::api::{Vfs, VfsOptions};
    use fuse_backend_rs::passthrough::{Config, PassthroughFs};
    use fuse_backend_rs::transport::{
        AsyncFuseServing, AsyncServingConfig, FuseSession, SyncFuseServing, SyncServingConfig,
        UringConfig, UringFuseServing,
    };

    struct Args {
        src: String,
        dest: String,
        as_async: bool,
        as_uring: bool,
        sync_blocking: bool,
        thread_cnt: u32,
        uring_bufs: usize,
        uring_zero_copy: bool,
        backing_direct_io: bool,
    }

    fn help() {
        println!(
            "Usage:\n   fuse-backend-rs-benchmark <src> <mountpoint> [--async|--uring] [--threads N] [--sync-blocking] [--uring-bufs N] [--uring-zero-copy] [--no-backing-direct-io]\n"
        );
    }

    fn parse_args() -> Result<Args> {
        let args = env::args().collect::<Vec<String>>();
        if args.len() < 3 {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        let mut res = Args {
            src: args[1].clone(),
            dest: args[2].clone(),
            as_async: false,
            as_uring: false,
            sync_blocking: false,
            thread_cnt: 4,
            uring_bufs: UringConfig::default().bufs_per_queue,
            uring_zero_copy: false,
            backing_direct_io: true,
        };
        let mut idx = 3;
        while idx < args.len() {
            match args[idx].as_str() {
                "--async" => res.as_async = true,
                "--uring" => res.as_uring = true,
                "--sync-blocking" => res.sync_blocking = true,
                "--threads" => {
                    idx += 1;
                    if idx >= args.len() {
                        help();
                        return Err(Error::from_raw_os_error(libc::EINVAL));
                    }
                    res.thread_cnt = args[idx].parse().map_err(|_| {
                        help();
                        Error::from_raw_os_error(libc::EINVAL)
                    })?;
                }
                "--uring-zero-copy" => res.uring_zero_copy = true,
                "--no-backing-direct-io" => res.backing_direct_io = false,
                "--uring-bufs" => {
                    idx += 1;
                    res.uring_bufs =
                        args.get(idx).and_then(|v| v.parse().ok()).ok_or_else(|| {
                            help();
                            Error::from_raw_os_error(libc::EINVAL)
                        })?;
                }
                _ => {
                    help();
                    return Err(Error::from_raw_os_error(libc::EINVAL));
                }
            }
            idx += 1;
        }
        if res.src.is_empty() || res.dest.is_empty() || res.thread_cnt == 0 {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        // The blocking knob only configures the sync transport.
        if res.sync_blocking && (res.as_async || res.as_uring) {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        if res.as_async && res.as_uring {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        Ok(res)
    }

    fn create_server(
        src: &str,
        uring_zero_copy: bool,
        allow_direct_io: bool,
    ) -> Arc<Server<Arc<Vfs>>> {
        let vfs = Vfs::new(VfsOptions {
            no_open: false,
            no_opendir: false,
            ..Default::default()
        });

        let cfg = Config {
            root_dir: src.to_string(),
            do_import: false,
            uring_zero_copy,
            allow_direct_io,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();

        vfs.mount(Box::new(fs), "/").unwrap();
        Arc::new(Server::new(Arc::new(vfs)))
    }

    /// Serve requests with `thread_cnt` synchronous worker threads until a
    /// termination signal is received.
    fn run_sync(server: Arc<Server<Arc<Vfs>>>, se: FuseSession, thread_cnt: u32, blocking: bool) {
        let cfg = SyncServingConfig {
            workers: thread_cnt as usize,
            blocking,
        };
        let serving = match SyncFuseServing::new(se, server, cfg) {
            Ok(serving) => serving,
            Err(e) => {
                error!("failed to start the sync serving layer: {}", e);
                std::process::exit(1);
            }
        };

        let mut signals = Signals::new(TERM_SIGNALS).unwrap();
        signals.forever().next();
        // Dropping the serving layer unmounts the session and joins all
        // serving threads.
        drop(serving);
    }

    /// Serve requests with `thread_cnt` asynchronous workers until a
    /// termination signal is received.
    fn run_async(server: Arc<Server<Arc<Vfs>>>, se: FuseSession, thread_cnt: u32) {
        let cfg = AsyncServingConfig {
            workers: thread_cnt as usize,
            ..Default::default()
        };
        let serving = match AsyncFuseServing::new(se, server, cfg) {
            Ok(serving) => serving,
            Err(e) => {
                error!("failed to start the async serving layer: {}", e);
                std::process::exit(1);
            }
        };

        let mut signals = Signals::new(TERM_SIGNALS).unwrap();
        signals.forever().next();
        // Dropping the serving layer unmounts the session and joins all
        // serving threads.
        drop(serving);
    }

    /// Serve requests through the FUSE-over-io_uring transport until a
    /// termination signal is received. Requires kernel 6.14+ with the
    /// fuse module parameter enable_uring turned on; `UringFuseServing::new()`
    /// fails otherwise.
    fn run_uring(
        server: Arc<Server<Arc<Vfs>>>,
        se: FuseSession,
        thread_cnt: u32,
        bufs_per_queue: usize,
        zero_copy: bool,
    ) {
        // set_uring() must be called before the INIT handshake, which
        // UringFuseServing::new() performs on the mounted session.
        server.set_uring(true);
        let cfg = UringConfig {
            workers: thread_cnt as usize,
            entries_per_queue: 16,
            bufs_per_queue,
            zero_copy,
        };
        let serving = match UringFuseServing::new(se, server, cfg) {
            Ok(serving) => serving,
            Err(e) => {
                error!(
                    "failed to start the FUSE-over-io_uring transport \
                     (requires kernel 6.14+ with the fuse module parameter \
                     enable_uring turned on): {}",
                    e
                );
                std::process::exit(1);
            }
        };

        let mut signals = Signals::new(TERM_SIGNALS).unwrap();
        signals.forever().next();
        // Dropping the serving layer unmounts the session and joins all
        // serving threads.
        drop(serving);
    }

    pub fn main() -> Result<()> {
        SimpleLogger::new()
            .with_level(LevelFilter::Info)
            .init()
            .unwrap();
        let args = parse_args()?;

        for dir in [&args.src, &args.dest] {
            let path = Path::new(dir);
            if path.exists() {
                if !path.is_dir() {
                    error!("{} is not a directory", dir);
                    return Err(Error::from_raw_os_error(libc::EINVAL));
                }
            } else {
                fs::create_dir_all(path)?;
            }
        }
        info!(
            "passthrough src {} mountpoint {} mode {} threads {}",
            args.src,
            args.dest,
            if args.as_uring {
                "uring"
            } else if args.as_async {
                "async"
            } else if args.sync_blocking {
                "sync-blocking"
            } else {
                "sync"
            },
            args.thread_cnt,
        );

        let server = create_server(&args.src, args.uring_zero_copy, args.backing_direct_io);
        let mut se = FuseSession::new(Path::new(&args.dest), "bench_passthru", "", false).unwrap();
        se.mount().unwrap();

        if args.as_uring {
            run_uring(
                server,
                se,
                args.thread_cnt,
                args.uring_bufs,
                args.uring_zero_copy,
            );
        } else if args.as_async {
            run_async(server, se, args.thread_cnt);
        } else {
            run_sync(server, se, args.thread_cnt, args.sync_blocking);
        }

        Ok(())
    }
}

#[cfg(target_os = "linux")]
fn main() -> std::io::Result<()> {
    daemon::main()
}

#[cfg(not(target_os = "linux"))]
fn main() {
    eprintln!("the benchmark daemon only works on Linux");
}
