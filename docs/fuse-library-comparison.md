# fuse-backend-rs vs fuser: Performance Comparison

This document summarizes a controlled performance comparison between
**fuse-backend-rs** (this repository, `feat/uring-fuse` branch passthrough
daemon) and **fuser 0.15.1**, performed on oxs-dev (Alibaba Cloud Linux,
kernel 5.10.134). It includes the measurement methodology, four fairness
normalizations that were required to obtain valid data, the final numbers
with 3-round stability verification, and root-cause analysis of every
observed difference.

## TL;DR

- **Single-thread sequential I/O: the two libraries perform the same**
  (within ±12%). Neither has a per-request processing advantage for large
  block reads/writes.
- **Concurrent throughput is an architectural gap.** fuse-backend-rs scales
  near-linearly with worker threads (+120% to +540% at 8 threads); fuser is
  capped by its single dispatch thread regardless of client parallelism.
- **4k random writes favor fuse-backend-rs at all thread counts** (+24% to
  +123%), mainly due to zero-copy receive (payload goes straight into
  `pwritev` without an intermediate buffer).
- **4k random reads favor fuser at 1-2 threads** (consistent -10% to -30%
  for fuse-backend-rs), where the multi-worker machinery costs more than it
  saves; fuse-backend-rs wins back the lead at ≥4 threads.
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
| fuser | 0.15.1 with `features = ["abi-7-31"]`, `tests/passthrough-fuser` daemon |
| Client | fio 3.34, 10s per workload; Python in-process loop for create microbench |
| Workloads | filecreate, randread-4k, randwrite-4k, seqread-128k, seqwrite-128k |
| Thread counts | 1 / 2 / 4 / 8 (daemon worker threads; fio client parallelism matches) |

### Threading models under test

- **fuse-backend-rs**: N worker threads all block on `read(/dev/fuse)`; the
  kernel wakes one per request. Requests are processed concurrently.
- **fuser**: `Session::run()` is a single read-dispatch loop and all
  `Filesystem` trait methods take `&mut self`, so request handling is
  serialized by the borrow checker. The `-t N` argument has no effect on
  fuser's parallelism — it always processes one request at a time.

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
throughput.

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

### Concurrency: dispatch model decides everything

fuser's single dispatch thread caps throughput at roughly its single-stream
rate (~145-160k IOPS for 4k randread, ~1.6-1.7 GB/s sequential) while its
latency grows with client parallelism (552μs at 8-thread seqwrite).
fuse-backend-rs workers scale near-linearly until the client side saturates
(seqread plateaus around 8 threads at ~10.5 GB/s on this host).

### 4k random reads at low concurrency: fuser wins

Consistent across all 3 rounds (-10% to -30% at 1-2 threads). At low
concurrency, fuse-backend-rs pays for the multi-worker machinery without
benefiting from parallelism: per-request `epoll_wait` + `read` in the
transport loop and worker wakeup/scheduling overhead. The single-threaded
fuser loop does a plain blocking `read()`. At ≥4 concurrent clients the
situation reverses (+24% to +46% for fuse-backend-rs).

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
| fuser can run multi-threaded | ❌ | `Session::run()` never spawns; `&mut self` trait methods serialize processing |
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

- `bench_library_compare.sh` — full matrix (5 workloads × 4 thread counts ×
  2 daemons), fio-based
- `bench_multi_round.sh` — wrapper running N rounds into separate result
  directories
- `parse_multi_round.py` — per-round IOPS + mean + spread aggregation
- `micro_create_clean.sh` — Python in-process create microbenchmark
- `count_create_syscalls.sh` — daemon syscall accounting via `strace -c`
- `probe_write_syscalls.sh` / `probe_read_splitting.sh` — request-size
  verification (detects kernel-side write splitting)

Requirements on the test host: fio, fusermount3, fuse3 headers
(fuser links libfuse via pkg-config), strace, python3. Build
`passthrough-fuser` with `PKG_CONFIG_PATH` pointing at fuse3.

## Takeaways

1. For single-threaded sequential workloads, choosing between the two
   libraries makes little difference.
2. For concurrent workloads, fuse-backend-rs's multi-worker model is the
   decisive advantage (up to ~6x throughput at 8 threads).
3. For latency-sensitive single-threaded 4k-random-read services, fuser's
   leaner loop currently has a measurable edge.
4. If using fuser: always enable an `abi-7-x` cargo feature, or large
   writes will be silently split.
5. If using fuse-backend-rs as non-root for metadata-heavy workloads: the
   create path's extra round trips (not credential switching) are where
   improvements should target.
