// SPDX-License-Identifier: Apache-2.0

//! Tests of `AsyncServingConfig::block_while_idle`. One reads the context switches and the CPU
//! time of `AsyncFuseServing`'s worker threads by their names, so the tests run in a binary of
//! their own, one at a time. Mounting needs root or fusermount3, and the tests skip without
//! either.

#![cfg(all(target_os = "linux", feature = "async-io"))]

mod common;

mod async_serving {
    use std::fs;
    use std::sync::{Arc, Mutex};
    use std::thread;
    use std::time::{Duration, Instant};

    use fuse_backend_core::api::server::Server;
    use fuse_backend_fusedev::{AsyncFuseServing, AsyncServingConfig, FuseSession};
    use fuse_backend_passthrough::{Config, PassthroughFs};
    use vmm_sys_util::tempdir::TempDir;

    const WORKERS: usize = 8;

    /// Held by each test, so that `workers_usage()` sees only its test's workers.
    static ONE_AT_A_TIME: Mutex<()> = Mutex::new(());

    /// The voluntary context switches and the CPU time of the serving layer's workers.
    fn workers_usage() -> (u64, Duration) {
        let mut workers = 0;
        let mut switches = 0;
        let mut cpu = Duration::ZERO;
        for task in fs::read_dir("/proc/self/task").unwrap() {
            let task = task.unwrap().path();
            let comm = fs::read_to_string(task.join("comm")).unwrap_or_default();
            if !comm.starts_with("fuse-async-") {
                continue;
            }
            workers += 1;
            let status = fs::read_to_string(task.join("status")).unwrap();
            switches += status
                .lines()
                .find_map(|l| l.strip_prefix("voluntary_ctxt_switches:"))
                .and_then(|n| n.trim().parse::<u64>().ok())
                .unwrap();
            let schedstat = fs::read_to_string(task.join("schedstat")).unwrap();
            let ns = schedstat.split_whitespace().next().unwrap();
            cpu += Duration::from_nanos(ns.parse().unwrap());
        }
        // Without the workers, the test would count nothing and pass.
        assert_eq!(workers, WORKERS, "found {} worker threads", workers);
        (switches, cpu)
    }

    #[test]
    fn test_async_serving_wakes_one_idle_worker() {
        let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
        let src = TempDir::new().unwrap();
        let passthrough = PassthroughFs::<()>::new(Config {
            root_dir: src.as_path().to_string_lossy().to_string(),
            do_import: false,
            ..Default::default()
        })
        .unwrap();
        passthrough.import().unwrap();
        let server = Arc::new(Server::new(passthrough));

        let mnt = TempDir::new().unwrap();
        let mut se = FuseSession::new(mnt.as_path(), "async_serving_test", "", false).unwrap();
        se.set_allow_other(false);
        if let Err(e) = se.mount() {
            eprintln!("can't mount ({}), skipping", e);
            return;
        }
        let cfg = AsyncServingConfig {
            workers: WORKERS,
            max_inflight: 0,
            block_while_idle: true,
        };
        let _serving = AsyncFuseServing::new(se, server, cfg).unwrap();

        // The kernel doesn't cache a failed lookup, so each one is a request.
        let missing = mnt.as_path().join("missing");
        assert!(fs::metadata(&missing).is_err());

        let (idle_switches, cpu) = workers_usage();
        let start = Instant::now();
        thread::sleep(Duration::from_secs(1));
        let (now_switches, now_cpu) = workers_usage();
        let idle = now_cpu - cpu;
        assert!(
            idle < Duration::from_millis(100),
            "{} idle workers used {:?} of CPU in 1s",
            WORKERS,
            idle
        );
        // Idle workers still switch out when they let their runtime run.
        let ticks_per_sec = (now_switches - idle_switches) as f64 / start.elapsed().as_secs_f64();

        // A worker switches out once per request it wakes up for, so a request that wakes
        // every idle worker costs about `WORKERS` switches.
        const LOOKUPS: u64 = 1000;
        let (switches, _) = workers_usage();
        let start = Instant::now();
        for _ in 0..LOOKUPS {
            assert!(fs::metadata(&missing).is_err());
        }
        let ticks = (ticks_per_sec * start.elapsed().as_secs_f64()) as u64;
        let switches = (workers_usage().0 - switches).saturating_sub(ticks);
        assert!(
            switches < LOOKUPS * WORKERS as u64 / 2,
            "{} workers switched out {} times for {} lookups, not counting {} ticks",
            WORKERS,
            switches,
            LOOKUPS,
            ticks
        );
    }

    #[test]
    fn test_async_serving_blocking_worker_lets_runtime_run() {
        let _one = ONE_AT_A_TIME.lock().unwrap_or_else(|e| e.into_inner());
        super::common::check_busy_worker_lets_runtime_run(AsyncServingConfig {
            workers: 1,
            max_inflight: 0,
            block_while_idle: true,
        });
    }
}
