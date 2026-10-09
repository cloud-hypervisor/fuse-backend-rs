# fuse-backend-rs benchmark tooling

Tooling to compare the performance of the synchronous, asynchronous and
io_uring IO paths, complementing the functional tests. Two levels are
provided:

## 1. Micro-benchmark (framework overhead)

`benches/sync_vs_async_microbench.rs` measures per-operation latency of
`PassthroughFs` through the synchronous `FileSystem` interface versus the
delegated `AsyncFileSystem` interface, without the kernel fuse transport in
the loop.

Covered operations: `lookup`, `getattr`, `open+read(4KB)+release`,
`open+write(4KB)+release`, `create+release+unlink`.

```sh
cd tests/benchmark
cargo bench
```

Note that the async numbers include the runtime dispatch cost
(`Runtime::block_on()` per operation). These numbers quantify the overhead
of delegation itself; they do not predict end-to-end throughput, because the
fuse transport and request concurrency dominate there.

## 2. End-to-end comparison with fio

`tests/scripts/bench_sync_async.sh` mounts the `fuse-backend-rs-benchmark`
daemon once per mode — sync mode (N worker threads, one fuse channel each),
async mode (N asynchronous workers through `AsyncFuseServing`, each with
its own `/dev/fuse` file description and async runtime, tokio-uring when
io_uring is available) and uring mode (the experimental
FUSE-over-io_uring transport, requires kernel 6.14+ and is skipped
otherwise) — and runs identical fio workloads:

- sequential read/write with 1MB requests
- random read/write with 4KB requests
- metadata operations (file create/delete)
- directory enumeration (readdir): fio has no readdir engine, so the
  `bench_readdir.py` helper walks the mountpoint with `os.scandir()`
  (getdents64) between the filecreate and filedelete workloads, when the
  directory holds `NRFILES` entries, and reports entries/s as `iops` in
  the same JSON job shape. Enumeration is one strictly sequential request
  chain per stream (each getdents64 resumes from the cookie of the previous
  reply), so the rate is latency-bound and does not scale with `THREADS`.

```sh
sudo tests/scripts/bench_sync_async.sh      # needs fio + jq + python3 + fuse mount rights
THREADS=8 RUNTIME=60 sudo -E tests/scripts/bench_sync_async.sh
```

The script builds the daemon in release mode; when invoking it with `sudo`,
build once as a regular user first (`cd tests/benchmark && cargo build
--release`) to avoid root-owned artifacts in the workspace `target/`
directory.

The fio results are written in JSON format to a temporary results directory
(printed at the start, `<dir>/<mode>-<workload>.json`), and a side-by-side
summary is printed at the end. The default execution order is sync then
async; the second mode benefits from a warmer page cache, so cross-check
with `MODES="async sync"`. The uring mode is included with
`MODES="sync async uring"`.

To quantify the difference between the transports, collect each mode's
results and compare the collected files — `bench_compare.py` is
mode-agnostic, so any two collected files can be diffed (positive deltas
mean the second file outperformed the first):

```sh
MODES="sync async uring" sudo -E tests/scripts/bench_sync_async.sh
python3 tests/scripts/bench_compare.py collect <results-dir> sync  sync.json
python3 tests/scripts/bench_compare.py collect <results-dir> uring uring.json
# uring vs sync: positive deltas mean uring won that workload
python3 tests/scripts/bench_compare.py compare sync.json uring.json
```

Both transports run on the same machine back-to-back, so environment
effects mostly cancel out; for confidence run once per `MODES` order.

## 3. Continuous benchmarking in CI

The `Benchmark` workflow (`.github/workflows/benchmark.yml`) runs the fio
comparison on GitHub-hosted runners for a matrix of sync/async/uring modes
and 1/8 threads; the uring mode is skipped on runners whose kernel is
older than 6.14:

- Pull requests: add the `run-benchmark` label to trigger a benchmark run.
  The merge base and the PR are built and benchmarked back to back *in the
  same job*, and the two result sets are compared in the job summary of the
  workflow run (Actions tab). The execution order of the two variants is
  alternated between the thread counts to spread runner drift across them.
  The merge base predates the uring transport, so the baseline comparison
  covers only sync and async; the PR's uring numbers are instead compared
  cross-mode against the sync/async numbers of the same run, which needs
  no baseline.
- Pushes to master and manual dispatches run a single benchmark for
  reference; no baseline is stored.

An earlier revision compared each PR run against a baseline recorded on a
different runner (the orphan branch `bench-results`). That approach turned
out to be unusable: GitHub-hosted runners are shared VMs whose performance
fluctuates by tens of percent, so even code paths the PR did not touch
regularly showed "regressions" of 20% and more. Comparing two variants on
the same runner cancels most of that noise.

`tests/scripts/bench_compare.py` normalizes the fio JSON files
(`collect`) and prints the markdown comparison table (`compare`); it can
also be used to compare two local runs:

```sh
python3 tests/scripts/bench_compare.py collect /tmp/run1 sync run1-sync.json
python3 tests/scripts/bench_compare.py compare base.json run1-sync.json
```

Note that GitHub-hosted runners are shared VMs with significant noise, so
the comparison is advisory and never blocks merging. Regressions beyond
the threshold should be re-checked on bare metal before acting on them;
a dedicated runner may be used later by changing the workflow `runs-on`
value.

Several measures keep the measurements stable: the data workloads use a
2 second fio ramp phase to exclude cold-start effects, a `sync` flushes
writeback between workloads, the metadata workloads create/delete
50000 files each so that they run long enough to measure reliably, and
the readdir helper discards its own 2 second ramp phase before measuring.
Because the metadata workloads still fluctuate more than the data ones
even on bare metal, they are flagged with a looser threshold (25% versus
10%).

## Interpretation

The async path currently delegates all operations to the synchronous
handlers and serves requests from one `FuseDevTask` per worker thread, so
it scales with `--threads` like the sync path: at equal worker counts the
two transports are at parity on buffered data workloads, and the async mode
keeps scaling as workers are added. Metadata operations are dominated by
the per-request handler cost instead. A native io_uring hot path is
tracked as follow-up work (#188).

## Limitations

- Linux only: the `async-io` feature depends on io-uring/tokio.
- The benchmark daemon disables `no_open`/`no_opendir` to exercise the
  full open/handle paths.
