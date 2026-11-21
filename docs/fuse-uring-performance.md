# FUSE-over-io_uring Performance Analysis

This document analyzes the performance characteristics of the FUSE-over-io_uring
transport implementation, including known regressions and upstream optimization
progress.

## Benchmark Summary

### Metadata Operations: Significant Wins

| Workload | 1-thread | 8-thread |
|----------|----------|----------|
| filecreate | +150-216% | +276-277% |
| filedelete | -15 to +8% | +41-46% |
| randread-4k | +1-3% | +63% |
| randwrite-4k | +5-16% | -22 to -24% |

The uring transport excels at metadata operations because it eliminates the
per-request syscall overhead (read/write on `/dev/fuse`). With 8 threads,
filecreate achieves **3.7x** throughput compared to sync.

### Sequential I/O: Known Regression

| Workload | 1-thread | 8-thread |
|----------|----------|----------|
| seqread | -44 to +5% | **-37%** |
| seqwrite | -1 to -15% | **-28 to -34%** |

The sequential I/O regression is a **known upstream limitation**, not a bug in
this implementation. See "Root Cause Analysis" below.

## Root Cause Analysis

### What It's NOT

1. **Not memcpy overhead**: The scatter Reader/Writer optimization eliminates
   all userspace copies. Both classic and uring paths use identical kernel-side
   copy functions (`fuse_copy_args`, `fuse_copy_out_args`).

2. **Not missing readahead**: Readahead is handled at the VFS layer
   (`fs/fuse/file.c:fuse_readahead`), completely independent of the transport.
   Both classic and uring paths benefit equally.

3. **Not pipeline depth**: Increasing `entries_per_queue` from 4 to 16 had
   zero impact on sequential I/O performance.

### What It Is

The regression stems from two optimizations that were present in RFC v1/v2
but removed in later versions pending upstream subsystem changes:

#### 1. `__wake_on_current_cpu` (Scheduler Dependency)

RFC v1 had an optimization to wake the waiting thread on the **same CPU core**
where the request was processed, avoiding cross-core cache line bouncing.

From Bernd Schubert's v3 changelog:
> "Removed the `__wake_on_current_cpu` optimization (for now as that needs to
> go through another subsystem/tree), removing it means a significant
> performance drop"

This requires scheduler changes that haven't been accepted upstream yet.

#### 2. Direct Ring Submission (Locking Issues)

RFC v1/v2 submitted requests directly from the task that created them,
avoiding the `io_uring_cmd_complete_in_task()` workqueue deferral.

This was removed due to teardown race conditions and lock ordering violations.
The current implementation defers to a workqueue, adding latency.

### RFC v1 Benchmark Comparison

Bernd Schubert's RFC v1 benchmarks (2024, with optimizations present) showed:

| Workload | /dev/fuse | uring | Gain |
|----------|-----------|-------|------|
| 128K paged reads (1 job) | 1117 MB/s | 1921 MB/s | **1.72x** |
| 128K paged reads (8 jobs) | 6273 MB/s | 10855 MB/s | **1.73x** |
| 1024K DIO reads (4 jobs) | 3823 MB/s | 15022 MB/s | **3.58x** |

Current kernels (6.14-7.2) lack these optimizations, resulting in the
regression we observe.

## Upstream Optimization Progress

### Linux 7.3: Buffer Pools + Zero-Copy (Merged)

**Author**: Joanne Koong  
**Status**: Merged for Linux 7.3 (August 2026)

- **Buffer pools**: Kernel-managed shared memory pool instead of per-entry
  dedicated buffers. Reduces memory overhead significantly.

- **Zero-copy**: Server can directly access client pages (pinned user pages
  for DIO, page cache folios for buffered I/O) without intermediary copies.
  Requires `CAP_SYS_ADMIN`.

Benchmark results from Joanne's patch series (bs=1M):

| Workload | Before | After | Gain |
|----------|--------|-------|------|
| direct randreads | ~2100 MB/s | ~2600 MB/s | +20% |
| buffered randreads | ~1900 MB/s | ~2400 MB/s | +25% |
| buffered randwrites | 950 MB/s | 1050 MB/s | +10% |

### Pending: `__wake_on_current_cpu`

**Status**: Blocked on scheduler subsystem changes

This optimization will eliminate cross-core wakeup latency for sequential I/O.

### Pending: Direct Ring Submission

**Status**: Will be re-submitted after core work stabilizes

This will eliminate the workqueue deferral overhead.

## Buffer pools

Before Linux 7.3, every ring entry registers a payload buffer of the
connection's maximum payload size, 1 MiB with the default INIT reply. With
16 entries per queue on a machine with 24 possible CPUs, that is 384
buffers, and a workload that keeps many requests in flight on every CPU
touches all of them.

On Linux 7.3 and later, `UringFuseServing` gives each queue a pool of
`UringConfig::bufs_per_queue` buffers with `FUSE_IO_URING_CMD_ADD_QUEUE`
and `FUSE_IO_URING_CMD_ADD_BUFPOOL` before any entry registers. The kernel
lends a buffer to an entry while it serves a request that has a payload or
a reply body, and reports the buffer's offset in the entry header. A
request waits in the kernel while all buffers of its queue are busy. A
kernel before 7.3 doesn't offer buffer pools at INIT, and its entries keep
a buffer each. If the kernel offered them and a command fails, the mount
fails.

Memory and throughput of the benchmark daemon with `--uring`, 4 workers
and 16 entries per queue, on a 24-CPU machine with Linux 7.3-rc7. The
workload is random 1 MiB direct reads with libaio at depth 16, from one
fio job pinned to each CPU, for 8 seconds. The two settings alternated
three times:

| Buffers per queue | VmSize | VmRSS after | Read throughput |
|-------------------|--------|-------------|-----------------|
| own per entry | 1492 MiB | 393 MiB | 1518-1728 MiB/s |
| 4 | 431 MiB | 106 MiB | 1588-1709 MiB/s |

VmSize also counts the request and reply scratch areas of each entry,
which are as large as its own payload buffer, so a pooled entry saves
those too. Random 4 KiB reads in the same setup ran at 44.5k to 46.8k
IOPS with and without pools. VmRSS counts only the pages that requests
touched, so workloads with fewer requests in flight use far less memory
than this.

## Zero-copy

On Linux 7.3 and later, a queue with a buffer pool can also serve reads
and writes with zero-copy. The kernel then registers the client's pages
of a READ or WRITE in the server's io_uring buffer table instead of
copying them into a payload buffer, and the server moves the data
between those pages and a file with `IORING_OP_READ_FIXED` and
`IORING_OP_WRITE_FIXED`. It needs CAP_SYS_ADMIN, and the file system
asks for it per open with `OpenOptions::IO_URING_ZERO_COPY`.

With `UringConfig::zero_copy`, `UringFuseServing` adds the queues with
`FUSE_URING_ZERO_COPY` and gives each worker ring an empty buffer table
with a slot per entry. A zero-copy READ gets a reply body that only the
transport can fill, and `write_from()` runs `READ_FIXED` from the file
into the slot. A zero-copy WRITE gets a `Reader` whose data only the
transport can move, and `read_to()` runs `WRITE_FIXED` from the slot
into the file. Both run on the worker's ring and wait for the result
there, because the kernel registered the pages in that ring's table. If the
kernel refuses zero-copy, `UringFuseServing` adds the queues without it.

A file system that reads or writes zero-copy data through memory, or
with a file that has no descriptor, still works, but slower. The worker
then copies the data through a memory file that it keeps mapped. It runs
`WRITE_FIXED` from the client pages into the file and hands over the
mapped bytes, or fills the mapping and runs `READ_FIXED` from the file
into the client pages.

The table shows the throughput of the benchmark daemon with `--uring
--no-backing-direct-io`, 4 workers and 16 entries per queue, on a 24-CPU
machine with Linux 7.3-rc7, serving 4 files of 1 GiB from a tmpfs as
root. fio ran direct random IO with libaio, 4 jobs at depth 16, for 8
seconds, and the two settings alternated three times:

| Workload | Copy | Zero-copy |
|----------|------|-----------|
| 1 MiB reads | 9966-10651 MiB/s | 13896-15202 MiB/s |
| 1 MiB writes | 8164-9070 MiB/s | 12299-12883 MiB/s |
| 128 KiB reads | 15579-17626 MiB/s | 15565-17028 MiB/s |
| 128 KiB writes | 12700-14037 MiB/s | 11911-13249 MiB/s |

Zero-copy saves the copy of the payload, which matters for large
requests. At 128 KiB the two runs overlap.

## Splicing READ replies on /dev/fuse

The classic `/dev/fuse` transport can send a READ reply with `splice(2)`
when the file system hands it the data in a file with a descriptor, see
`FuseSession::set_splice_write()`. The kernel then copies the data once,
from the file's pages into the FUSE request, instead of the server reading
it into its reply buffer first. `AsyncFuseServing` splices in
`ZeroCopyWriter::write_from()` on both runtimes, and in
`AsyncZeroCopyWriter::async_write_from()` only on tokio, where the read it
replaces blocks the runtime thread too. `PassthroughFs` serves page-cache
hits with an inline `RWF_NOWAIT` read that copies, so it splices only the
READs that this read can't serve: cache misses, and files on tmpfs, which
has no `RWF_NOWAIT`.

Throughput and daemon CPU time per GiB of `AsyncFuseServing` with 4
workers and `PassthroughFs` with `cache=never`, serving 4 files of 1 GiB
from a tmpfs as root on Linux 7.3.1 on a 96-core machine. fio ran 4 jobs
with psync for 10 seconds, and the table shows medians of three runs. With
the thread pool, `PassthroughFs` reads tmpfs on a pool thread into a
buffer of its own, so its READs still copy. On tokio-uring
`PassthroughFs` reads through the ring, so they copy too. `PassthroughFs`
doesn't ask for `FsOptions::MAX_PAGES`, so the kernel splits the reads of
1 MiB into READs of 128 KiB.

| Runtime | Workload | Copy | Splice |
|---------|----------|------|--------|
| tokio | 128 KiB sequential | 7230 MiB/s, 344 ms/GiB | 8086 MiB/s, 269 ms/GiB |
| tokio | 1 MiB sequential | 7384 MiB/s, 343 ms/GiB | 8285 MiB/s, 269 ms/GiB |
| tokio | 4 KiB random | 1183 MiB/s, 3120 ms/GiB | 1182 MiB/s, 3132 ms/GiB |
| tokio, thread pool | 128 KiB sequential | 5037 MiB/s, 589 ms/GiB | 5092 MiB/s, 577 ms/GiB |
| tokio-uring | 128 KiB sequential | 6150 MiB/s, 392 ms/GiB | 6235 MiB/s, 380 ms/GiB |

A build that also splices in `async_write_from()` on tokio-uring read
128 KiB at 8148 MiB/s and 256 ms/GiB in the same setup, against 6186 MiB/s
and 372 ms/GiB copying. io_uring hands reads of files without
`FMODE_NOWAIT`, such as tmpfs files, to its worker threads, and the splice
avoids that. But `splice(2)` has no `RWF_NOWAIT`. It waits for uncached
data on the runtime thread, and the other requests of the worker wait with
it.

Cold reads show that. 4 workers served 16 files of 1 GiB on XFS, on two
striped gp3 volumes, after `echo 3 > /proc/sys/vm/drop_caches`. 16 fio jobs
read every 128 KiB block of the files once, at random, with psync. The
table shows medians of three runs. The splice row of tokio-uring comes from
the build above. With the splice, each worker waits for one read at a time,
as on tokio. Read directly with `O_DIRECT`, the volumes take about 1 ms
per read of 128 KiB and give 500 MiB/s to 4 jobs and 1988 MiB/s to 16.
Readahead on the files brings some blocks in before fio asks for them, so
the reads through FUSE go faster than that.

| Runtime | READs | MiB/s | p99 |
|---------|-------|-------|-----|
| tokio-uring | io_uring reads | 3032 | 2212 µs |
| tokio-uring | splice | 877 | 4686 µs |
| tokio | splice | 879 | 4620 µs |
| tokio | `preadv()` | 871 | 4751 µs |

## Implementation Notes

### Current State

This implementation targets the stable FUSE_URING protocol 7.42 (kernel 6.14+),
and uses the buffer pools of protocol 7.46 (kernel 7.3) when the kernel has them:

- Scatter Reader/Writer eliminates all userspace memcpy
- Per-CPU queue model with configurable entries_per_queue
- Buffer pools with configurable bufs_per_queue, see "Buffer pools" above
- Zero-copy for opens that ask for it, see "Zero-copy" above
- Fallback to classic `/dev/fuse` for notifications/interrupts

### Future Work

1. **Async zero-copy**: `ZeroCopySource` and the zero-copy reply wait
   synchronously on the worker's ring, which suits the synchronous
   handlers. Serving `AsyncFileSystem` handlers over io_uring needs
   asynchronous versions.

### Tuning Recommendations

- `entries_per_queue`: Default is 4. Increasing to 16+ does not help
  sequential I/O (bottleneck is elsewhere), but may help high-concurrency
  metadata workloads.

- `bufs_per_queue`: Default is 4. On Linux 7.3 and later it caps the
  requests with a payload or reply body that one queue serves at once, and
  with it the memory of the payload buffers.

- Thread count: The per-CPU queue model means optimal performance when
  worker threads match available CPU cores.

## References

- Bernd Schubert's fuse-over-io_uring patch series:
  https://lore.kernel.org/io-uring/20241209-fuse-uring-for-6-10-rfc4-v8-0-d9f9f2642be3@ddn.com/

- Joanne Koong's buffer pools + zero-copy:
  https://lwn.net/Articles/1049130/

- Kernel documentation:
  https://docs.kernel.org/filesystems/fuse/fuse-io-uring.html
