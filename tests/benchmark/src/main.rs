// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

//! A minimal fusedev passthrough daemon used to benchmark the synchronous
//! and asynchronous IO paths with external tools such as fio.
//!
//! Usage: `fuse-backend-rs-benchmark <src> <mountpoint> [--async] [--uring] [--threads N]
//! [--sync-blocking] [--thread-pool] [--uring-bufs N] [--uring-zero-copy]
//! [--no-backing-direct-io] [--kernel-passthrough] [--no-writeback] [--delay-us N] [--splice]`
//!
//! - default (sync) mode: requests are served by `N` worker threads of the
//!   `SyncFuseServing` serving layer, each reading from its own fuse channel
//!   (the classic multi-threaded design); `--sync-blocking` selects blocking
//!   channels cloned with `FUSE_DEV_IOC_CLONE` instead of epoll-based ones.
//! - `--async` mode: requests are served by `N` asynchronous workers
//!   (`AsyncFuseServing`), each running a `FuseDevTask` on its own async
//!   runtime (tokio-uring when io_uring is available) and its own
//!   `/dev/fuse` file description. `--thread-pool` lets `PassthroughFs`
//!   offload blocking work to the runtime's blocking thread pool, see
//!   `PassthroughFs::enable_async_thread_pool()`.
//! - `--uring` mode: requests are served through the FUSE-over-io_uring
//!   transport (`UringFuseServing`, experimental, requires kernel 6.14+);
//!   `N` limits the number of io_uring worker threads. `--uring-bufs N`
//!   sets `UringConfig::bufs_per_queue`, the number of buffers in each
//!   queue's buffer pool on kernels with buffer pools. `0` gives every ring
//!   entry a buffer of its own. `--uring-zero-copy` serves reads and writes
//!   with zero-copy (`UringConfig::zero_copy` and
//!   `Config::uring_zero_copy`), which needs CAP_SYS_ADMIN.
//! - `--uring --async` mode: requests are served through FUSE-over-io_uring
//!   with the asynchronous handlers (`UringFuseServing::new_async`), and
//!   each of the `N` workers keeps several requests in flight.
//!
//! `--no-backing-direct-io` opens the backing files without O_DIRECT even when
//! the client asks for it (`Config::allow_direct_io = false`). Requests of a
//! client that opens with O_DIRECT still reach the daemon as direct IO, and
//! opens without O_DIRECT on the backing file can use zero-copy.
//!
//! `--kernel-passthrough` makes the kernel pass reads, writes and mmap of open
//! files through to the source files (Linux 6.9+, needs `CAP_SYS_ADMIN`), so
//! that they never reach the daemon. The kernel doesn't allow it with the
//! writeback cache, so it also turns the writeback cache off.
//!
//! `--no-writeback` turns the writeback cache off without enabling kernel
//! passthrough, to tell the effects of the two apart.
//!
//! `--delay-us N` makes every LOOKUP and READ wait `N` microseconds before
//! it is served, like a backend that fetches from a remote store. The
//! synchronous handlers block their thread for that time, the asynchronous
//! ones sleep without blocking it.
//!
//! `--splice` makes the sync mode send READ replies with `splice(2)`, see
//! `FuseSession::set_splice_write()`.

#[cfg(target_os = "linux")]
mod delay;

#[cfg(target_os = "linux")]
mod daemon {
    use std::env;
    use std::fs;
    use std::io::{Error, Result};
    use std::os::fd::{AsRawFd, BorrowedFd};
    use std::path::Path;
    use std::sync::{Arc, OnceLock};
    use std::time::Duration;

    use log::{error, info, LevelFilter};
    use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
    use simple_logger::SimpleLogger;

    use fuse_backend_rs::abi::fuse_abi::FsOptions;
    use fuse_backend_rs::api::filesystem::AsyncFileSystem;
    use fuse_backend_rs::api::server::Server;
    use fuse_backend_rs::api::{Vfs, VfsOptions};
    use fuse_backend_rs::passthrough::{BackingFiles, Config, PassthroughFs};

    use fuse_backend_rs::transport::{
        fuse_backing_close, fuse_backing_open, AsyncFuseServing, AsyncServingConfig, FuseSession,
        SyncFuseServing, SyncServingConfig, UringConfig, UringFuseServing,
    };

    use crate::delay::DelayFs;

    struct Args {
        src: String,
        dest: String,
        as_async: bool,
        as_uring: bool,
        sync_blocking: bool,
        thread_pool: bool,
        kernel_passthrough: bool,
        no_writeback: bool,
        splice: bool,
        thread_cnt: u32,
        uring_bufs: usize,
        uring_zero_copy: bool,
        backing_direct_io: bool,
        delay: Duration,
    }

    impl Args {
        /// The name of the serving mode, as the benchmark script calls it.
        fn mode(&self) -> &'static str {
            match (self.as_uring, self.as_async) {
                (true, true) => "uring_async",
                (true, false) => "uring",
                (false, true) => "async",
                (false, false) if self.sync_blocking => "sync-blocking",
                (false, false) => "sync",
            }
        }
    }

    /// Registers backing files on the FUSE device of the session, which is
    /// only known once it is mounted.
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

    fn help() {
        println!(
            "Usage:\n   fuse-backend-rs-benchmark <src> <mountpoint> [--async] [--uring] [--threads N] [--sync-blocking] [--thread-pool] [--uring-bufs N] [--uring-zero-copy] [--no-backing-direct-io] [--kernel-passthrough] [--no-writeback] [--delay-us N] [--splice]\n"
        );
    }

    /// Parse the value of the option at `args[idx]`.
    fn option_value<T: std::str::FromStr>(args: &[String], idx: usize) -> Result<T> {
        args.get(idx).and_then(|v| v.parse().ok()).ok_or_else(|| {
            help();
            Error::from_raw_os_error(libc::EINVAL)
        })
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
            thread_pool: false,
            kernel_passthrough: false,
            no_writeback: false,
            splice: false,
            thread_cnt: 4,
            uring_bufs: UringConfig::default().bufs_per_queue,
            uring_zero_copy: false,
            backing_direct_io: true,
            delay: Duration::ZERO,
        };
        let mut idx = 3;
        while idx < args.len() {
            match args[idx].as_str() {
                "--async" => res.as_async = true,
                "--uring" => res.as_uring = true,
                "--sync-blocking" => res.sync_blocking = true,
                "--thread-pool" => res.thread_pool = true,
                "--kernel-passthrough" => res.kernel_passthrough = true,
                "--no-writeback" => res.no_writeback = true,
                "--splice" => res.splice = true,
                "--threads" => {
                    idx += 1;
                    res.thread_cnt = option_value(&args, idx)?;
                }
                "--delay-us" => {
                    idx += 1;
                    res.delay = Duration::from_micros(option_value(&args, idx)?);
                }
                "--uring-zero-copy" => res.uring_zero_copy = true,
                "--no-backing-direct-io" => res.backing_direct_io = false,
                "--uring-bufs" => {
                    idx += 1;
                    res.uring_bufs = option_value(&args, idx)?;
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
        // The blocking and splice knobs only configure the sync transport.
        if (res.sync_blocking || res.splice) && (res.as_async || res.as_uring) {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        // The blocking thread pool belongs to the async runtime.
        if res.thread_pool && !res.as_async {
            help();
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        Ok(res)
    }

    fn create_vfs(
        src: &str,
        thread_pool: bool,
        uring_zero_copy: bool,
        allow_direct_io: bool,
        backing_files: Option<Arc<FuseBackingFiles>>,
        no_writeback: bool,
    ) -> Arc<Vfs> {
        let mut opts = VfsOptions {
            no_open: false,
            no_opendir: false,
            // The Vfs turns the writeback cache off when the kernel offers passthrough. Keep it off
            // on other kernels too, so that this mode measures the same as --no-writeback there.
            no_writeback: no_writeback || backing_files.is_some(),
            ..Default::default()
        };
        if backing_files.is_some() {
            opts.out_opts |= FsOptions::PASSTHROUGH;
        }
        let vfs = Vfs::new(opts);

        let cfg = Config {
            root_dir: src.to_string(),
            do_import: false,
            uring_zero_copy,
            allow_direct_io,
            ..Default::default()
        };
        let mut fs = PassthroughFs::<()>::new(cfg).unwrap();
        fs.import().unwrap();
        if let Some(files) = backing_files {
            fs.set_backing_files(files);
        }
        // Offloading to the thread pool needs a file system shared between threads.
        let fs = fs.into_shared();
        fs.enable_async_thread_pool(thread_pool);
        vfs.mount(Box::new(fs), "/").unwrap();
        Arc::new(vfs)
    }

    /// Serve with `serving` until a termination signal is received, or exit
    /// if `what` failed to start.
    fn run_until_signal<T, E: std::fmt::Display>(serving: std::result::Result<T, E>, what: &str) {
        let serving = match serving {
            Ok(serving) => serving,
            Err(e) => {
                error!("failed to start {what}: {e}");
                std::process::exit(1);
            }
        };
        let mut signals = Signals::new(TERM_SIGNALS).unwrap();
        signals.forever().next();
        // Dropping the serving layer unmounts the session and joins all
        // serving threads.
        drop(serving);
    }

    /// Serve with the serving layer `args` selects until a termination
    /// signal is received.
    fn serve<F: AsyncFileSystem + Send + Sync + 'static>(
        server: Arc<Server<F>>,
        se: FuseSession,
        args: &Args,
    ) {
        if args.kernel_passthrough {
            // Allow a source directory on a stacked file system such as overlayfs.
            server.set_max_stack_depth(2).unwrap();
        }
        let workers = args.thread_cnt as usize;
        if args.as_uring {
            // set_uring() must be called before the INIT handshake, which
            // UringFuseServing performs on the mounted session.
            server.set_uring(true);
            let cfg = UringConfig {
                workers,
                entries_per_queue: 16,
                bufs_per_queue: args.uring_bufs,
                zero_copy: args.uring_zero_copy,
            };
            let serving = if args.as_async {
                UringFuseServing::new_async(se, server, cfg)
            } else {
                UringFuseServing::new(se, server, cfg)
            };
            run_until_signal(
                serving,
                "the FUSE-over-io_uring transport (requires kernel 6.14+ with the fuse \
                 module parameter enable_uring turned on)",
            );
        } else if args.as_async {
            let cfg = AsyncServingConfig {
                workers,
                ..Default::default()
            };
            run_until_signal(
                AsyncFuseServing::new(se, server, cfg),
                "the async serving layer",
            );
        } else {
            let cfg = SyncServingConfig {
                workers,
                blocking: args.sync_blocking,
            };
            run_until_signal(
                SyncFuseServing::new(se, server, cfg),
                "the sync serving layer",
            );
        }
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
            "passthrough src {} mountpoint {} mode {} threads {} thread pool {} kernel passthrough {} writeback {} delay {:?} splice {}",
            args.src,
            args.dest,
            args.mode(),
            args.thread_cnt,
            args.thread_pool,
            args.kernel_passthrough,
            !(args.no_writeback || args.kernel_passthrough),
            args.delay,
            args.splice,
        );

        let backing_files = args
            .kernel_passthrough
            .then(|| Arc::new(FuseBackingFiles::default()));
        let vfs = create_vfs(
            &args.src,
            args.thread_pool,
            args.uring_zero_copy,
            args.backing_direct_io,
            backing_files.clone(),
            args.no_writeback,
        );
        let mut se = FuseSession::new(Path::new(&args.dest), "bench_passthru", "", false).unwrap();
        se.set_splice_write(args.splice);
        se.mount().unwrap();
        if let Some(files) = backing_files {
            let fuse_file = se.get_fuse_file().unwrap().try_clone()?;
            files.fuse_file.set(fuse_file).unwrap();
        }

        // Serve the Vfs directly without a delay, so those numbers stay
        // comparable with runs from before the delay option.
        if args.delay.is_zero() {
            serve(Arc::new(Server::new(vfs)), se, &args);
        } else {
            serve(
                Arc::new(Server::new(DelayFs::new(vfs, args.delay))),
                se,
                &args,
            );
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
