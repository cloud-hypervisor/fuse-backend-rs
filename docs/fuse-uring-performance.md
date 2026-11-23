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

### Sequential I/O

| Workload | 1-thread | 8-thread |
|----------|----------|----------|
| seqread | -44 to +5% | **-37%** |
| seqwrite | -1 to -15% | **-28 to -34%** |

These numbers predate the fix in "Queue ownership" below, which removed
most of the seqwrite regression. The rest of the sequential I/O gap may come
from the upstream changes described in "Root Cause Analysis".

## Queue ownership

The kernel puts each request on the queue of the CPU that sends it. With the
writeback cache, the flusher thread sends the WRITEs, from one CPU at a time.
The workers used to own whole queues, so the worker that owned that CPU's
queue served every WRITE while the others waited for requests. Over a few
seconds the flusher moves between CPUs, so the per-thread CPU time looked
evenly spread, but at any moment one worker was writing.

Profiling a 4-job 1 MiB seqwrite through the writeback cache with 4 workers
showed the uring workers spending most of their samples in
`io_cqring_wait`, waiting for requests, while the sync threads were busy in
`ext4_buffered_write_iter`. `UringFuseServing` now spreads the entries of
every queue over the workers, and the kernel hands a request to any free
entry of its queue, so a queue that gets more requests than one worker can
serve reaches the other workers too. In that profile run, seqwrite went
from 3.99 GiB/s to 5.79 GiB/s, against 6.83 GiB/s for sync. The workers now
contend on the backing file's inode lock, as the sync threads do.

The kernel doesn't know which workers are busy, though. A request can land
on a free entry of a worker that is still serving a slow request of another
queue, and wait for it while other workers idle.

## Root Cause Analysis

### What It's NOT

1. **Not memcpy overhead**: The scatter Reader/Writer optimization eliminates
   all userspace copies. Both classic and uring paths use identical kernel-side
   copy functions (`fuse_copy_args`, `fuse_copy_out_args`).

2. **Not missing readahead**: Readahead is handled at the VFS layer
   (`fs/fuse/file.c:fuse_readahead`), completely independent of the transport.
   Both classic and uring paths benefit equally.

3. **Not pipeline depth**: Increasing `entries_per_queue` from 4 to 16 had
   zero impact on sequential I/O performance, when each worker owned whole
   queues.

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

When this was measured, each entry also had request and reply scratch
areas as large as its own payload buffer, which VmSize counts. Entries now
keep 168 bytes of scratch. Random 4 KiB reads in the same setup ran at
44.5k to 46.8k IOPS with and without pools. VmRSS counts only the pages
that requests touched, so workloads with fewer requests in flight use far
less memory than this.

The kernel hands a request to the entry of its queue that became free last,
and once its buffers are busy, an entry that commits takes the next waiting
request with the buffer it already holds. So the entries that get the
buffers first keep them under load. The workers register their entries in
rounds, so that those entries belong to different workers. Without the
rounds, 1 MiB reads in the setup above ran at 530 to 937 MiB/s, because the
worker that registered last served every queue alone.

A first version of the rounds had every queue register in the same order
of workers, so the entries that keep the buffers of a queue belonged to
the same workers in every queue. With fewer buffers than workers, the
other workers had nothing to do. So each queue registers the last entry
of each of its workers in a round of its own, after its other entries,
and consecutive queues end on different workers. The benchmark
daemon served PassthroughFs over a tmpfs directory with 8 workers and 16
entries per queue, on a 96-CPU machine with Linux 7.3.1. 8 fio jobs, each
pinned to its own CPU, read 1 MiB with O_DIRECT and libaio at depth 16 for
8 seconds. Medians of 3 runs in alternating order:

| Buffers per queue | Reads | No rounds | Same order | Each queue ends elsewhere |
|-------------------|-------|-----------|------------|---------------------------|
| 4 (default) | random | 9.1 GiB/s | 13.4 GiB/s | 39.4 GiB/s |
| 4 (default) | sequential | 12.6 GiB/s | 13.6 GiB/s | 39.8 GiB/s |
| 8 | random | 12.9 GiB/s | 39.1 GiB/s | 39.0 GiB/s |

With the same order, 4 workers served all queues and the others idled.
With 8 buffers, as many as workers, the order made no difference. So the
default of 4 buffers doesn't hold back a mount with more workers than
buffers, as long as several queues are busy, but a single busy queue
still reaches only as many workers as it has buffers.

Spreading the entries costs reads where whole queues gave each busy
queue a worker of its own. In the setup above, with medians of 3 runs:

| Workers | Entries per queue | fio CPUs | Whole queues | Spread |
|---------|-------------------|----------|--------------|--------|
| 8 | 16 | 8 to 15 | 52.9 GiB/s | 46.8 GiB/s |
| 8 | 16 | 8, 15, ..., 57 | 52.4 GiB/s | 43.4 GiB/s |
| 8 | 16 | 8, 16, ..., 64 | 5.8 GiB/s | 43.9 GiB/s |
| 96, one per CPU | 4 | 8 to 15 | 48.9 GiB/s | 124.0 GiB/s |

In the first two layouts, each busy queue had a worker of its own, and
the spread reads 11 to 17% slower for the same reason in both. With
whole queues, requests rarely waited, so each took the lowest free
buffer of its queue and a worker reused one or two buffers. With the
spread, each worker holds buffers of several queues and cycles through
them, and a request costs about a quarter more cycles, half of the extra
in the kernel's `fuse_copy_fill()` getting the buffer pages with
`get_user_pages_fast()`.

When a queue has an entry on every worker, it registers the entry on
the worker that owned it with whole queues last. A queue with one
request at a time then goes to the same worker as before, so no layout
reaches fewer workers. Queues the worker count apart, like those of the
third row, have the same workers, and each gives its other buffers to
different workers than the one before. With fewer entries per queue
than workers, fewer workers than queues, and an entry count that
doesn't divide the worker count, a layout can still reach fewer workers
than whole queues did, with one request in flight per queue, or with
more if each queue has fewer buffers than entries. The default starts a
worker per online CPU, which is usually one per queue.

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
into the file. Both run on the worker's ring, because the kernel
registered the pages in that ring's table. A synchronous handler waits
for the result on the ring. With `UringFuseServing::new_async()`, the
asynchronous handlers call `async_write_from()` and `async_read_to()`,
whose operations carry the index of the request's entry, and the worker
loop wakes the request when the result comes off the ring. If the kernel
refuses zero-copy, `UringFuseServing` adds the queues without it.

A file system that reads or writes zero-copy data through memory, or
with a file that has no descriptor, still works, but slower. The worker
then copies the data through a memory file that it keeps mapped. It runs
`WRITE_FIXED` from the client pages into the file and hands over the
mapped bytes, or fills the mapping and runs `READ_FIXED` from the file
into the client pages. `ZeroCopyWriter::prefers_fd()` tells a file
system that a reply works this way, so `PassthroughFs` gives a zero-copy
READ its file instead of reading page-cache hits inline with
`RWF_NOWAIT`.

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

### Small reads

Zero-copy costs more than copying for small READs, and a server can't
copy just those. `can_zero_copy_req()` in fs/fuse/dev_uring.c takes
every READ and WRITE with pages of an open with
`FOPEN_IO_URING_ZERO_COPY`, whatever its size. The commit of a zero-copy
READ sets `skip_folio_copy`, so the kernel copies no reply into the
client pages.
Each such READ pays for registering the client pages and for a
`READ_FIXED` on the worker's ring. io_uring serves a `READ_FIXED` of a
page-cache hit inline on a file system with `FMODE_NOWAIT`, such as XFS,
and hands it to its worker threads on one without, such as tmpfs.

The benchmark daemon served PassthroughFs with 8 workers, 16 entries per
queue and `--no-backing-direct-io`, on a 96-CPU machine with Linux 7.3.4,
as root, from a tmpfs directory and from an XFS directory with a warm
page cache. fio read 1 GiB files at random with O_DIRECT, from one job or
four, each pinned to its own CPU, with psync at depth 1 or with libaio at
depth 16, for 3 seconds after a 1 second ramp. The `new_async()` rows
on XFS come from a build with `ZeroCopyWriter::prefers_fd()`, which
makes no difference on tmpfs, where `PassthroughFs` doesn't read inline.
The tables have the IOPS of zero-copy against those of copying, medians
of 3 runs in alternating order:

On tmpfs:

| Read size | `new()`, 1 job, depth 1 | `new()`, 4 jobs, depth 16 | `new_async()`, 1 job, depth 1 | `new_async()`, 4 jobs, depth 16 |
|-----------|---|---|---|---|
| 4 KiB | 0.35 | 0.63 | 0.68 | 1.00 |
| 16 KiB | 0.45 | 0.68 | 0.81 | 1.02 |
| 32 KiB | 0.51 | 0.70 | 0.91 | 1.14 |
| 64 KiB | 0.60 | 0.89 | 0.98 | 1.49 |
| 128 KiB | 0.74 | 1.24 | 1.09 | 2.11 |
| 1 MiB | 1.12 | 2.67 | 1.40 | 2.71 |

On XFS:

| Read size | `new()`, 1 job, depth 1 | `new()`, 4 jobs, depth 16 | `new_async()`, 1 job, depth 1 | `new_async()`, 4 jobs, depth 16 |
|-----------|---|---|---|---|
| 4 KiB | 0.98 | 0.71 | 0.87 | 1.03 |
| 16 KiB | 1.03 | 0.74 | 0.94 | 1.06 |
| 32 KiB | 1.16 | 0.96 | 1.00 | 1.10 |
| 64 KiB | 1.22 | 1.23 | 1.10 | 1.22 |
| 128 KiB | 1.29 | 1.56 | 1.24 | 1.37 |
| 1 MiB | 1.61 | 2.71 | 1.61 | 1.74 |

On tmpfs, a zero-copy READ waited for an io_uring worker thread, and
`new()` spent 11.0 µs of CPU time per 4 KiB read with one job instead of
3.3 µs. Its copying reads at depth 1 varied between mounts, from 108k to
222k IOPS at 4 KiB, while the zero-copy ones stayed near 77k. On XFS,
`new()` read as fast with zero-copy as with copying at depth 1. With 4
jobs at depth 16, zero-copy cost `new()` 30% to 37% of its IOPS at 4
KiB on both file systems. Zero-copy paid from 64 KiB on XFS. On tmpfs
it paid from 128 KiB, except with `new()` at depth 1, where it paid only
at 1 MiB. Sequential reads of the same sizes on tmpfs crossed over at the
same sizes.

While a file stays below 64 KiB, none of its READs returns 64 KiB or
more, so with `Config::uring_zero_copy_min_size`, 64 KiB by default,
`PassthroughFs` doesn't ask for zero-copy on a read-only open of it.
Opens with write access ask at any size, because the file can grow.
64 KiB keeps zero-copy where it pays on XFS. On tmpfs, or another file
system without `FMODE_NOWAIT`, a larger minimum fits `new()` better. The
READs of a large file can be small too. If most of them are, serve
without zero-copy.

The test read 2,000 files of 2 KiB, one after the other, from one job or
from four jobs with 500 files each, in the setup above. The files/s and
the daemon's CPU time per file, medians of 3 runs:

| File system | Serving | Jobs | Zero-copy on every open | With the 64 KiB minimum |
|-------------|---------|------|-------------------------|-------------------------|
| tmpfs | `new()` | 1 | 30k/s, 27.4 µs | 31k/s, 24.0 µs |
| tmpfs | `new()` | 4 | 117k/s, 25.0 µs | 122k/s, 22.4 µs |
| tmpfs | `new_async()` | 1 | 27k/s, 38.3 µs | 28k/s, 34.1 µs |
| tmpfs | `new_async()` | 4 | 98k/s, 35.1 µs | 103k/s, 29.8 µs |
| XFS | `new()` | 1 | 31k/s, 23.7 µs | 32k/s, 23.6 µs |
| XFS | `new()` | 4 | 123k/s, 22.3 µs | 127k/s, 22.5 µs |
| XFS | `new_async()` | 1 | 27k/s, 35.6 µs | 28k/s, 34.0 µs |
| XFS | `new_async()` | 4 | 103k/s, 30.0 µs | 98k/s, 29.0 µs |

On tmpfs, the minimum saved 10% to 15% of the daemon's CPU time per
file. Each file also costs a LOOKUP, an OPEN, a FLUSH and a RELEASE, so
its READ is a small part of it. On XFS, the rates stayed within the
spread of the runs, which was up to 5%.

## Implementation Notes

### Current State

This implementation targets the stable FUSE_URING protocol 7.42 (kernel 6.14+),
and uses the buffer pools of protocol 7.46 (kernel 7.3) when the kernel has them:

- Scatter Reader/Writer eliminates all userspace memcpy
- Per-CPU queue model with configurable entries_per_queue
- Buffer pools with configurable bufs_per_queue, see "Buffer pools" above
- Zero-copy for opens that ask for it, see "Zero-copy" above
- Fallback to classic `/dev/fuse` for notifications/interrupts

### Tuning Recommendations

- `entries_per_queue`: Default is 4. The entries of each queue are spread
  over the workers, so a busy queue reaches at most this many workers, and
  never more than `workers`. With buffer pools, requests with a payload or
  reply body also need one of the queue's `bufs_per_queue` buffers. Past the
  worker count, more entries only queue more requests on the same workers.

- `bufs_per_queue`: Default is 4. On Linux 7.3 and later it caps the
  requests with a payload or reply body that one queue serves at once, and
  with it the memory of the payload buffers. With `new_async()`, a request
  keeps its buffer while its handler waits, so `new_async()` gives each
  queue as many buffers as entries. With 16 entries and 4 buffers
  per queue, 4 KiB random writes with the async handlers reached 0.82M
  IOPS, against 1.05M with a buffer per entry. The synchronous handlers
  showed no difference.

- `zero_copy`: Default is off. It costs more than copying for READs
  below 64 KiB on XFS, and on tmpfs below 128 KiB with `new_async()` and
  below 1 MiB with `new()` at depth 1, see "Small reads" above. With
  `PassthroughFs`, `Config::uring_zero_copy_min_size` keeps read-only
  opens of smaller files on copies.

- `workers`: Default is one per CPU. A worker serves the requests of any
  queue it holds entries of, so the count no longer has to match the
  queues. It is capped at `entries_per_queue` times the number of queues.
  Each worker is a thread with its own ring, and with zero-copy also a
  memory file of one payload buffer.

## References

- Bernd Schubert's fuse-over-io_uring patch series:
  https://lore.kernel.org/io-uring/20241209-fuse-uring-for-6-10-rfc4-v8-0-d9f9f2642be3@ddn.com/

- Joanne Koong's buffer pools + zero-copy:
  https://lwn.net/Articles/1049130/

- Kernel documentation:
  https://docs.kernel.org/filesystems/fuse/fuse-io-uring.html
