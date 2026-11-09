# fuse-backend-rs vs fuser: Performance Comparison

This document summarizes a controlled performance comparison between
**fuse-backend-rs** (this repository, `feat/uring-fuse` branch passthrough
daemon) and **fuser** (0.15.1 for the fio matrix, 0.18 for the cache-miss
microbenchmark), performed on oxs-dev (Alibaba Cloud Linux,
kernel 5.10.134). It includes the measurement methodology, four fairness
normalizations that were required to obtain valid data, the final numbers
with multi-round stability verification, and root-cause analysis of every
observed difference.

## TL;DR

- **Single-thread sequential I/O: the two libraries perform the same**
  (within ±12%). Neither has a per-request processing advantage for large
  block reads/writes.
- **Concurrent throughput is at parity — but only since fuser 0.17.** The
  fio matrix (fuser 0.15, single dispatch thread) showed +120% to +540%
  wins for fuse-backend-rs at 8 threads. After upgrading the fuser daemon
  to 0.18 and enabling `Config::n_threads` + `Config::clone_fd`
  (per-worker `FUSE_DEV_IOC_CLONE` fds, added in fuser 0.17), fuser scales
  the same way and the controlled microbenchmark shows the two libraries
  within 2% of each other at equal worker counts.
- **4k random writes favor fuse-backend-rs at all thread counts** (+24% to
  +123%), mainly due to zero-copy receive (payload goes straight into
  `pwritev` without an intermediate buffer). *(Measured against fuser
  0.15 single-thread; not re-measured against multi-threaded fuser 0.18.)*
- **4k random reads: fuser leads a single client by ~10-15%** (61.5k vs
  ~52-56k ops/s in a controlled cache-miss microbenchmark, 5 interleaved
  rounds). At 4 concurrent clients fuser-0.18-clonefd (183.9k) and the
  backend's blocking channels (179.5-181.1k) are statistically tied; the
  backend's epoll channels trail by 14-18%.
- **Metadata create (single-thread) favors fuser** (~1.9x in a clean
  microbenchmark). Root cause is request/syscall volume, not credential
  switching (disproved by A/B test).

## Test Environment

| Item | Value |
|------|-------|
| Host | oxs-dev, 96 cores |
| Kernel | 5.10.134-007.ali5000.al8.x86_64 |
| Backing storage | tmpfs (`/tmp`) — all results are cache-resident |
| fuse-backend-rs | `feat/uring-fuse` branch, `tests/passthrough` daemon, N workers |
| fuser | 0.15.1 with `features = ["abi-7-31"]` (fio matrix); 0.18 with `n_threads` + `clone_fd` (microbenchmark), `tests/passthrough-fuser` daemon |
| Client | fio 3.34, 10s per workload; Python in-process loop for create microbench |
| Workloads | filecreate, randread-4k, randwrite-4k, seqread-128k, seqwrite-128k |
| Thread counts | 1 / 2 / 4 / 8 (daemon worker threads; fio client parallelism matches) |

### Threading models under test

- **fuse-backend-rs**: N worker threads all block on `read(/dev/fuse)`; the
  kernel wakes one per request. Requests are processed concurrently.
- **fuser 0.15** (fio matrix): `Session::run()` is a single read-dispatch
  loop and all `Filesystem` trait methods take `&mut self`, so request
  handling is serialized by the borrow checker. The `-t N` argument has no
  effect — it always processes one request at a time.
- **fuser 0.18** (microbenchmark): since 0.17 the trait takes `&self`
  (`Send + Sync` filesystems) and `Config::n_threads` spawns N event-loop
  threads; with `Config::clone_fd` each thread reads from its own
  `FUSE_DEV_IOC_CLONE` fd — structurally the same model as the backend's
  `BlockingFuseChannel`.

## Fairness Normalizations

Initial comparisons produced wildly misleading numbers. Four asymmetries had
to be discovered and fixed before any conclusion was valid:

### 1. fuser test implementation used seek + read/write

The first version of the fuser passthrough daemon used
`File::seek()` + `read()/write()` (two syscalls per operation). Normalized
to `FileExt::read_at()/write_at()` (pread/pwrite, single syscall) to match
fuse-backend-rs's `read_at`/zero-copy write path.

### 2. FUSE writeback cache asymmetry

fuse-backend-rs's `PassthroughFs::init()` unconditionally negotiates
`FUSE_WRITEBACK_CACHE` when `do_import = false` (the test daemon's
configuration). The kernel then acknowledges buffered writes from the page
cache without contacting the daemon — measured write latency dropped to
2.2μs, below any physical `/dev/fuse` round-trip. fuser 0.15's
`KernelConfig` exposes no API to enable writeback cache, so the option
cannot be matched from that side.

Fix: `VfsOptions { no_writeback: true }` in the test daemon. Verified with
a smoke test: write latency rose from 2.2μs to 11.8μs (real round-trip).

Without this fix, random-write numbers were inflated by 3-10x (e.g. single
thread randwrite-4k showed "+331%" which collapsed to the true +24%~+38%
after normalization).

### 3. fuser ABI fallback splits large writes into 4k (major finding)

Even after fixes 1-2, sequential writes remained ~172% slower on fuser.
strace revealed the kernel was delivering each 128k write as **32 separate
4k FUSE WRITE requests** (8MB test write = 2048 × `pwrite64(4096)` for
fuser vs 64 × `pwritev(131072)` for fuse-backend-rs). Reads were
unaffected, ruling out a connection-level limit.

Root cause: fuser's cargo features default to `["libfuse"]` only. Without
any `abi-7-x` feature, fuser falls back to **protocol 7.8**, whose
`fuse_init_out` struct layout has no `max_background`/`time_gran`/
`max_pages` fields. The kernel (which parses the modern layout) reads
`max_write` from the wrong offset and caps writes accordingly. Debug log
evidence:

```
INIT response: ABI 7.8, flags 0x1, max write 1048576   # broken
INIT response: ABI 7.31, flags 0x400021, max write 1048576   # after fix
```

Fix: `fuser = { version = "0.15", features = ["abi-7-31"] }`. After the
fix, writes arrived as single 128k requests and single-thread seqwrite
went from +172% to **-3.6% (parity)** — the entire gap was this ABI bug.

This is worth reporting upstream: a fuser user who does not explicitly
enable an `abi-7-x` feature silently loses several-fold large-write
throughput. *(Fixed in fuser ≥0.17: the `abi-7-x` cargo features were
removed in favor of runtime ABI negotiation, so this trap no longer
exists there — it still applies to 0.15/0.16.)*

### 4. Client-side measurement pollution

Early create microbenchmarks used `for i in $(seq 1 N); do touch ...; done`
loops. strace of the client showed user/sys time dominated by
fork/exec of `touch` (~600μs+ per file), drowning the daemon-side cost.
Replaced with a Python in-process `os.open(O_CREAT|O_EXCL)` loop.

## Final Results

IOPS, positive diff = fuse-backend-rs faster. Single-run values; see
"Stability Verification" below for 3-round confirmation.

| Workload | Threads | backend | fuser | Diff |
|----------|--------:|--------:|------:|-----:|
| filecreate | 1 | 9.0 | 10.5 | -14.5% |
| filecreate | 4 | 6.0 | 10.5 | -42.6% |
| filecreate | 8 | 3.6 | 8.5 | -56.9% |
| randread-4k | 1 | 82,559 | 90,841 | -9.1% |
| randread-4k | 2 | 132,648 | 149,656 | -11.4% |
| randread-4k | 4 | 199,963 | 152,970 | +30.7% |
| randread-4k | 8 | 191,683 | 134,920 | +42.1% |
| randwrite-4k | 1 | 76,929 | 53,343 | +44.2% |
| randwrite-4k | 4 | 164,438 | 105,210 | +56.3% |
| randwrite-4k | 8 | 207,555 | 105,136 | +97.4% |
| seqread-128k | 1 | 13,102 | 12,611 | +3.9% |
| seqread-128k | 4 | 46,295 | 13,381 | +246.0% |
| seqread-128k | 8 | 83,801 | 13,565 | +517.8% |
| seqwrite-128k | 1 | 7,605 | 7,889 | -3.6% |
| seqwrite-128k | 4 | 26,229 | 13,082 | +100.5% |
| seqwrite-128k | 8 | 40,569 | 14,105 | +187.6% |

Peak sequential bandwidth at 8 threads: **10.5 GB/s** (backend, seqread)
vs **1.7 GB/s** (fuser). Latency under 8-thread concurrency follows the
same pattern (e.g. seqwrite-128k: 180μs vs 552μs).

## Stability Verification (3 full rounds)

The complete matrix was repeated 3 times (120 result files). Spread column
= (max-min)/mean within the 3 rounds.

| Workload | Threads | backend mean (spread) | fuser mean (spread) | Direction consistent? |
|----------|--------:|----------------------:|--------------------:|:---------------------:|
| seqread-128k | 1 | 12,770 (6%) | 12,342 (7%) | parity, all rounds |
| seqread-128k | 8 | 87,742 (0%) | 13,671 (5%) | +523/+561/+542% |
| seqwrite-128k | 1 | 8,197 (3%) | 7,333 (20%) | parity, all rounds |
| seqwrite-128k | 8 | 47,052 (8%) | 14,821 (12%) | +181/+234/+242% |
| randwrite-4k | 1 | 70,056 (13%) | 53,442 (2%) | +38/+31/+24% |
| randwrite-4k | 8 | 221,199 (7%) | 99,259 (21%) | +95/+130/+150% |
| randread-4k | 1 | 67,215 (33%) | 83,159 (21%) | -10/-18/-30% |
| randread-4k | 2 | 120,341 (8%) | 145,950 (3%) | -18/-21/-14% |
| randread-4k | 4 | 191,434 (3%) | 145,849 (7%) | +24/+33/+38% |
| randread-4k | 8 | 199,823 (1%) | 144,505 (9%) | +46/+32/+37% |
| filecreate | 1 | 9 (9%) | 8 (47%) | sign flips (-15/+28/+22%) |

Conclusions on stability:

- Sequential workloads and multi-thread wins are **highly reproducible**
  (spread ≤ 12%, direction identical every round).
- Single-thread randread shows the real (previously underestimated) spread
  of the backend: 81,825 → 59,649 across rounds. fuser is both faster and
  more stable at low concurrency.
- **The fio filecreate workload is invalid for this comparison**: with
  `--nrfiles=5000 --runtime=10` each 10s run produces only ~60-110 create
  operations (~100ms each in fio's file lifecycle), so the result flips
  sign between rounds. See the microbenchmark below instead.

## Cache-Miss Microbenchmark: Three-Way Controlled Comparison

The fio randread results above are contaminated by the kernel page cache:
depending on workload ordering, a varying fraction of reads is served from
the fuse page cache without ever reaching the daemon (any result showing
latency below the ~12μs round-trip floor is invalid). To compare the three
request-reception models cleanly, a dedicated microbenchmark was built:

- Client: Python loop, per iteration `fadvise(POSIX_FADV_DONTNEED)` on the
  target page then `pread(4k)` — every read is forced to miss the cache
  and reach the daemon (the eviction/refault tax applies identically to
  all compared modes).
- Daemon configurations compared (10 per round): fuse-backend-rs **epoll
  channel** (`FuseChannel`) with 1/2/4 workers, fuse-backend-rs **blocking
  channel** (`BlockingFuseChannel`, a blocking read on a
  `FUSE_DEV_IOC_CLONE` fd) with 1/2/4 workers, **fuser 0.18** with
  `n_threads` = 1/2/4 (clone_fd enabled, i.e. one `FUSE_DEV_IOC_CLONE` fd
  per event-loop thread — structurally identical to the backend's blocking
  channel), and **fuser 0.18 without clone_fd** (4 threads sharing one
  `/dev/fuse` fd) at 4 workers.
- 40,000 iterations per run; 5 rounds with all ten configurations
  interleaved within each round, so host-state drift affects all modes
  equally.

### Results (ops/s, 5-round mean)

Single client:

| Implementation | ops/s | stddev | spread | lat (μs) |
|----------------|------:|-------:|-------:|---------:|
| fuser 0.18, 1 thread | 61,521 | 2,228 | 9% | 14.5 |
| fuser 0.18, 2 threads | 59,395 | 5,355 | 21% | 15.2 |
| backend blocking, 4 workers | 56,285 | 5,430 | 23% | 15.8 |
| backend blocking, 1 worker | 54,325 | 5,913 | 22% | 16.4 |
| fuser 0.18, 4 threads | 53,213 | 5,558 | 23% | 17.1 |
| backend epoll, 1 worker | 51,573 | 6,574 | 25% | 17.5 |
| backend epoll, 2 workers | 51,390 | 4,819 | 19% | 17.4 |
| fuser 0.18 no-clonefd, 4 threads | 50,472 | 1,604 | 7% | 18.0 |
| backend blocking, 2 workers | 48,973 | 1,655 | 8% | 18.3 |
| backend epoll, 4 workers | 47,461 | 5,675 | 24% | 19.2 |

4 concurrent clients:

| Implementation | ops/s | stddev | spread | diff vs fuser w4 |
|----------------|------:|-------:|-------:|-----------------:|
| fuser 0.18, 4 threads | 183,877 | 5,795 | 8% | — |
| backend blocking, 4 workers | 181,068 | 4,490 | 6% | -1.5% |
| fuser 0.18, 2 threads | 180,527 | 1,765 | 3% | -1.8% |
| backend blocking, 2 workers | 179,549 | 4,111 | 6% | -2.4% |
| fuser 0.18 no-clonefd, 4 threads | 175,122 | 5,468 | 8% | -4.8% |
| backend epoll, 2 workers | 158,919 | 5,551 | 8% | -13.6% |
| backend epoll, 4 workers | 150,441 | 3,662 | 6% | -18.2% |
| fuser 0.18, 1 thread | 125,171 | 4,166 | 8% | -31.9% |
| backend blocking, 1 worker | 118,950 | 2,081 | 4% | -35.3% |
| backend epoll, 1 worker | 107,646 | 801 | 2% | -41.5% |

### Conclusions

- **Single client**: fuser with one event-loop thread leads by ~10-15%
  (61.5k vs 52-56k) and is the most stable (9% spread vs 19-25%). Extra
  threads hurt a single client on every implementation (more scheduling
  hops, no extra work to parallelize). The earlier fio-based "-10% to
  -30%" gap overestimated fuser's advantage — under controlled conditions
  it is ~10-15%.
- **4 clients, single worker**: all three reception models collapse to
  their serialized rate: fuser 125.2k ≈ backend blocking 119.0k
  (-35% vs the multi-worker peak) > backend epoll 107.6k. The epoll
  channel's per-request `epoll_wait` costs ~11% against a plain blocking
  `read` when one worker serves everything.
- **4 clients, multi-worker**: fuser-0.18-with-clonefd (183.9k) and the
  backend's blocking channels (179.5-181.1k) are **statistically tied**
  (within 2.4%, overlapping stddevs) — the two models are structurally
  identical (N threads, each blocking on its own `FUSE_DEV_IOC_CLONE` fd)
  and perform identically. Epoll channels peak at 158.9k (2 workers,
  -13.6%) and regress to 150.4k at 4 workers (-18.2%): with a shared fd,
  workers contend on the same queue and the extra `epoll_wait` per
  request; blocking channels show no such regression.
- **clone_fd within fuser is worth ~5%**: 4 threads sharing one
  `/dev/fuse` fd reach 175.1k vs 183.9k with per-thread cloned fds
  (-4.8%) — shared-fd readers still scale (the kernel serializes wakeups
  efficiently), but per-thread fds remove the last contention point.
- The bimodal ~±25% run-to-run variance seen on the backend single-client
  runs also appears for fuser, confirming it is host-level noise
  (scheduling/frequency), not a library property.

## Root-Cause Analysis

### Single-thread parity for large-block I/O

After all normalizations, single-thread 128k sequential reads and writes
land within ±12%. This shows:

- fuse-backend-rs's `Vfs → Server → PassthroughFs` dispatch chain adds
  negligible per-request overhead.
- Both libraries' data paths reduce to one `pwritev`/`preadv` (or splice)
  per request once max_write negotiation and syscall counts are aligned.

### 4k random writes: fuse-backend-rs leads everywhere

+24% to +123% across thread counts, reproduced every round. The single
thread delta comes from the zero-copy receive path: the payload in the
`/dev/fuse` receive buffer is written straight to the backing file with one
`pwritev` (no intermediate copy into a Rust `Vec`), while fuser copies the
write payload during request parsing.

### Concurrency: reception model, not library, decides everything

With **fuser 0.15** (single dispatch thread), throughput was capped at
roughly its single-stream rate (~145-160k IOPS for 4k randread, ~1.6-1.7
GB/s sequential) while latency grew with client parallelism (552μs at
8-thread seqwrite) — hence the +120% to +540% fio-matrix wins for the
multi-worker backend.

Since **fuser 0.17** this is no longer a library difference but a
configuration one: `Config::n_threads` + `Config::clone_fd` give fuser the
same model as the backend's blocking channels (N threads, each blocking on
its own `FUSE_DEV_IOC_CLONE` fd), and the controlled microbenchmark shows
the two within 2.4% of each other at equal worker counts. What still
decides concurrent throughput is the **reception model**:

- Per-thread blocking reads on cloned fds: best (180-184k at 4 clients).
- Multiple threads sharing one fd (fuser without clone_fd, or the
  backend's epoll channel): 5-18% behind, and the epoll channel regresses
  when going from 2 to 4 workers due to queue contention plus the
  per-request `epoll_wait` syscall.
- A single worker of any model: ~35% behind the multi-worker peak.

fuse-backend-rs workers scale near-linearly until the client side
saturates (seqread plateaus around 8 threads at ~10.5 GB/s on this host);
multi-threaded fuser 0.18 was not re-measured on the large-block fio
workloads, but the reception-model parity above suggests the fio-matrix
concurrency wins would largely disappear.

### 4k random reads at low concurrency: fuser wins (revised)

fio showed -10% to -30% at 1-2 threads, but that measurement mixes
daemon-served reads with cache-served reads. The cache-miss
microbenchmark above pins the true gap at ~10-15% for a single client
(fuser 0.18 single thread 61.5k vs backend 52-56k): fuse-backend-rs pays
per-request `epoll_wait` + `read` in the transport loop (epoll channel) or
worker wakeup/scheduling overhead (blocking channel), while fuser's single
event-loop thread does a plain blocking `read()`. At ≥2 concurrent clients
the picture reverses by configuration, not by library: multi-worker
blocking channels and multi-threaded fuser-with-clonefd are tied at the
top (~180-184k), and the backend's epoll channel trails by 14-18%.

### Metadata create: 1.9x slower, request volume is the cause

Clean microbenchmark (Python in-process loop, 10000 × `open(O_CREAT|O_EXCL)`,
single daemon worker, 3 rounds):

| Daemon | μs/file |
|--------|--------:|
| fuse-backend-rs | 57 |
| fuse-backend-rs (set_creds removed) | 66 |
| fuser | 30 |

A/B test removing all `set_creds()` calls showed **no improvement** —
credential switching is not the bottleneck here (even with the non-root
"restore failed" error logging). strace per 1000 creates:

| Metric | backend | fuser |
|--------|--------:|------:|
| Total syscalls | 23,020 | 14,007 |
| FUSE requests (read count) | 5,000 (5/create) | 4,002 (4/create) |
| Request reception | `epoll_wait` + `read` each | blocking `read` |
| openat | 3,000 | 1,000 |
| Extras | dup, newfstatat, statx, 2× close | chmod, fsync |

The create path difference comes from more round trips (separate LOOKUP /
GETATTR / FLUSH handling on top of CREATE/RELEASE) and more syscalls per
request, not from credential handling.

## Hypotheses Disproved During This Study

| Hypothesis | Verdict | Evidence |
|------------|---------|----------|
| Write gap is library quality | ❌ | Was writeback cache + fuser ABI bug; parity after fixes |
| "Single-thread reads are identical" | ⚠️ partial | True only for large sequential reads; fuser leads 4k randread at ≤2 threads |
| filecreate gap is credential switching | ❌ | A/B with set_creds removed: no change; syscall accounting shows request volume |
| fuser can run multi-threaded | ❌ for 0.15, ✅ since 0.17 | 0.15: `Session::run()` never spawns, `&mut self` trait serializes processing. 0.17+: `&self` trait + `Config::n_threads` + `Config::clone_fd`; verified at parity with the backend's blocking channels |
| fio filecreate is a usable metadata benchmark | ❌ | ~90 ops per 10s run; sign flips between rounds |

## Remaining Asymmetries

- `max_background`: backend negotiates 65535, fuser answers 16 (no setter
  API in fuser 0.15). Only affects asynchronous background requests.
- Tests ran as non-root: backend logs "failed to change credentials back to
  root" per metadata request (proven not to affect throughput, but present).
- tmpfs backing: all numbers are cache-resident; cold-cache behavior is not
  covered (oxs-dev cannot evict page cache).

## Reproduction

Scripts live under `tests/scripts/`:

- `bench_library_compare.sh` — full matrix (5 workloads × the thread counts
  in `THREADS_LIST` × 2 daemons), fio-based. The backend side is the
  `tests/benchmark` daemon run with `--no-writeback`, and the fuser side is
  `tests/passthrough-fuser`; the same script runs from a GitHub CI runner
  (label `run-fuser-compare` on the PR), where cross-daemon deltas from the
  same job are the signal and absolute numbers are not comparable across
  runners
- `bench_multi_round.sh` — wrapper running N rounds into separate result
  directories
- `parse_multi_round.py` — per-round IOPS + mean + spread aggregation
- `micro_create_clean.sh` — Python in-process create microbenchmark
- `count_create_syscalls.sh` — daemon syscall accounting via `strace -c`
- `probe_write_syscalls.sh` / `probe_read_splitting.sh` — request-size
  verification (detects kernel-side write splitting)
- `micro_read_ab.py` — cache-miss 4k random read microbenchmark (fadvise
  DONTNEED per read, guarantees every request reaches the daemon)
- `bench_micro_3way.sh` / `parse_micro_3way.py` — interleaved runs of all
  10 daemon configurations (backend epoll/blocking × 1/2/4 workers, fuser
  0.18 × 1/2/4 threads with clone_fd, fuser 0.18 × 4 threads without)
  with mean/stddev/spread aggregation

The `passthrough-fuser` daemon takes `--threads N` (mapped to
`Config::n_threads`, default 1) and `--no-clone-fd` (disables
`Config::clone_fd`, so all event-loop threads share one `/dev/fuse` fd).

Requirements on the test host: fio, fusermount3, fuse3 headers
(fuser links libfuse via pkg-config), strace, python3. Build
`passthrough-fuser` with `PKG_CONFIG_PATH` pointing at fuse3.

## Takeaways

1. For single-threaded sequential workloads, choosing between the two
   libraries makes little difference.
2. For concurrent workloads the **reception model** matters more than the
   library: per-thread blocking reads on `FUSE_DEV_IOC_CLONE` fds (backend
   blocking channels, fuser ≥0.17 with `n_threads` + `clone_fd`) are tied
   at the top; shared-fd multi-thread setups trail by 5-18%; a single
   worker of any model trails by ~35%. The backend's up-to-~6x fio-matrix
   concurrency wins were measured against single-threaded fuser 0.15 and
   do not apply to multi-threaded fuser.
3. For latency-sensitive single-client 4k-random-read services, fuser's
   lean single-thread loop leads by ~10-15% (controlled measurement);
   keep the daemon at one worker/thread for that workload.
4. If using fuser 0.15/0.16: always enable an `abi-7-x` cargo feature, or
   large writes will be silently split (fixed by runtime ABI negotiation
   in ≥0.17). If using fuser ≥0.17 for concurrency: enable both
   `n_threads` and `clone_fd`.
5. If using fuse-backend-rs as non-root for metadata-heavy workloads: the
   create path's extra round trips (not credential switching) are where
   improvements should target.
