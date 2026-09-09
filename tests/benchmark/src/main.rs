// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

//! A minimal fusedev passthrough daemon used to benchmark the synchronous
//! and asynchronous IO paths with external tools such as fio.
//!
//! Usage: `fuse-backend-rs-benchmark <src> <mountpoint> [--async|--uring] [--threads N]`
//!
//! - default (sync) mode: requests are served by `N` worker threads, each
//!   reading from its own fuse channel (the classic multi-threaded design).
//! - `--async` mode: requests are served by a single `FuseDevTask` running
//!   on the async runtime (tokio-uring when io_uring is available).
//! - `--uring` mode: requests are served through the FUSE-over-io_uring
//!   transport (`UringFuseServing`, experimental, requires kernel 6.14+);
//!   `N` limits the number of io_uring worker threads.

#[cfg(target_os = "linux")]
mod daemon {
    use std::env;
    use std::fs;
    use std::io::{Error, Result};
    use std::path::Path;
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;
    use std::thread;

    use log::{error, info, warn, LevelFilter};
    use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
    use simple_logger::SimpleLogger;

    use fuse_backend_rs::api::{
        server::{Server, MAX_BUFFER_SIZE},
        Vfs, VfsOptions,
    };
    use fuse_backend_rs::async_runtime::Runtime;
    use fuse_backend_rs::passthrough::{Config, PassthroughFs};
    use fuse_backend_rs::transport::{
        FuseChannel, FuseDevTask, FuseSession, UringConfig, UringFuseServing,
    };

    struct Args {
        src: String,
        dest: String,
        as_async: bool,
        as_uring: bool,
        thread_cnt: u32,
        threads_set: bool,
    }

    fn help() {
        println!(
            "Usage:\n   fuse-backend-rs-benchmark <src> <mountpoint> [--async|--uring] [--threads N]\n"
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
            thread_cnt: 4,
            threads_set: false,
        };
        let mut idx = 3;
        while idx < args.len() {
            match args[idx].as_str() {
                "--async" => res.as_async = true,
                "--uring" => res.as_uring = true,
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
                    res.threads_set = true;
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
        if res.as_async && res.as_uring {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        Ok(res)
    }

    fn create_server(src: &str) -> Arc<Server<Arc<Vfs>>> {
        let vfs = Vfs::new(VfsOptions {
            no_open: false,
            no_opendir: false,
            ..Default::default()
        });

        let cfg = Config {
            root_dir: src.to_string(),
            do_import: false,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();

        vfs.mount(Box::new(fs), "/").unwrap();
        Arc::new(Server::new(Arc::new(vfs)))
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

    /// Serve requests with `thread_cnt` synchronous worker threads until a
    /// termination signal is received.
    fn run_sync(server: Arc<Server<Arc<Vfs>>>, mut se: FuseSession, thread_cnt: u32) {
        for _ in 0..thread_cnt {
            let mut worker = FuseServer {
                server: server.clone(),
                ch: se.new_channel().unwrap(),
            };
            thread::Builder::new()
                .name("fuse_server".to_string())
                .spawn(move || {
                    let _ = worker.svc_loop();
                    warn!("fuse service thread exits");
                })
                .unwrap();
        }

        let mut signals = Signals::new(TERM_SIGNALS).unwrap();
        signals.forever().next();
        se.umount().unwrap();
        se.wake().unwrap();
    }

    /// Serve requests with a single asynchronous `FuseDevTask` until a
    /// termination signal is received.
    fn run_async(server: Arc<Server<Arc<Vfs>>>, mut se: FuseSession) {
        let fuse_file = se.clone_fuse_file().unwrap();

        // The signal handler thread tears the session down: umounting makes
        // the pending read on the fuse device fail with ENODEV, which
        // terminates the async task. The thread is detached on purpose:
        // poll_handler() may return without a signal (e.g. the session is
        // unmounted externally) while the thread is still waiting for one.
        let _shutdown = thread::spawn(move || {
            let mut signals = Signals::new(TERM_SIGNALS).unwrap();
            signals.forever().next();
            if let Err(e) = se.umount() {
                error!("failed to umount fuse session: {}", e);
            }
        });

        let state = Arc::new(AtomicBool::new(false));
        // The buffer must be able to hold the largest request (the
        // negotiated `max_write` plus a header), otherwise reads from
        // /dev/fuse fail with EINVAL once the INIT handshake is done,
        // see kernel commit "fuse: require /dev/fuse reads to have
        // enough buffer capacity".
        let mut task = FuseDevTask::new(
            (MAX_BUFFER_SIZE + 0x1000) as usize,
            fuse_file,
            server,
            state.clone(),
        );
        Runtime::new().block_on(task.poll_handler());
        info!("async fuse task exited");

        state.store(true, Ordering::Release);
    }

    /// Serve requests through the FUSE-over-io_uring transport until a
    /// termination signal is received. Requires kernel 6.14+ with the
    /// fuse module parameter enable_uring turned on; `UringFuseServing::new()`
    /// fails otherwise.
    fn run_uring(server: Arc<Server<Arc<Vfs>>>, se: FuseSession, thread_cnt: u32) {
        // set_uring() must be called before the INIT handshake, which
        // UringFuseServing::new() performs on the mounted session.
        server.set_uring(true);
        let cfg = UringConfig {
            workers: thread_cnt as usize,
            entries_per_queue: 16,
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
            } else {
                "sync"
            },
            args.thread_cnt,
        );

        let server = create_server(&args.src);
        let mut se = FuseSession::new(Path::new(&args.dest), "bench_passthru", "", false).unwrap();
        se.mount().unwrap();

        if args.as_async && args.threads_set {
            warn!(
                "--threads {} is ignored in async mode, requests are served by a single task",
                args.thread_cnt
            );
        }

        if args.as_uring {
            run_uring(server, se, args.thread_cnt);
        } else if args.as_async {
            run_async(server, se);
        } else {
            run_sync(server, se, args.thread_cnt);
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
