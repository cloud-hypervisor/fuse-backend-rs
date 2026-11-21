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

With `UringFuseServing::new()`, whose workers serve one request at a time,
that holds fast requests up behind slow ones. The benchmark daemon served
PassthroughFs over a tmpfs directory with 8 workers, 16 entries per queue
and `--no-backing-direct-io`, on a 96-CPU machine with Linux 7.3.1, and
`--delay-us 1000 --delay-prefix slow` made each read of the files named
`slow.*` wait 1 ms. Four fio jobs read 4 KiB at random from 64 MiB files
with psync and O_DIRECT, for 10 seconds after a 2 second ramp: alone, next
to one job that read a slow file the same way, and next to four. The table
has the reads of the four fast jobs, medians of 3 runs in alternating
order:

| Serving | Slow jobs | Fast reads/s | p50 | p99 | p99.9 |
|---------|-----------|--------------|-----|-----|-------|
| `SyncFuseServing` | 0 | 379k | 10 µs | 14 µs | 18 µs |
| | 1 | 381k | 10 µs | 14 µs | 17 µs |
| | 4 | 377k | 10 µs | 15 µs | 17 µs |
| `AsyncFuseServing` | 0 | 157k | 25 µs | 38 µs | 45 µs |
| | 1 | 157k | 24 µs | 38 µs | 46 µs |
| | 4 | 157k | 24 µs | 40 µs | 49 µs |
| `UringFuseServing::new()` | 0 | 525k | 9 µs | 11 µs | 14 µs |
| | 1 | 433k | 8 µs | 11 µs | 1.06 ms |
| | 4 | 163k | 5 µs | 1.06 ms | 1.07 ms |
| same, 1 entry per queue | 4 | 284k | 7 µs | 14 µs | 2.11 ms |
| `UringFuseServing::new_async()` | 0 | 414k | 10 µs | 13 µs | 15 µs |
| | 1 | 411k | 10 µs | 13 µs | 16 µs |
| | 4 | 389k | 10 µs | 13 µs | 16 µs |

Each queue keeps going to the worker that served it last, and the queues
end their registration on different workers, see "Buffer pools" below.
So a slow read holds up the queues of its worker. Next to one slow job,
fewer than 1 in 100 fast reads of `new()` waited as long as a slow read.
Next to four, the fast reads fell to 163k/s, with runs between 92k and
262k depending on the CPUs the jobs ran on, and the slow jobs read 2.9k
times a second in all, against 3.8k with the other serving layers. When
every queue ended its registration on the same worker, as a first
version of the rounds did, all of them went to that worker, and the fast
reads fell to 105k/s next to one slow job and to 27k/s next to four.
With one entry per queue, each queue has a single worker. The fast reads
then ranged from 145k to 305k reads/s, but each CPU can have only one
request in flight. `new_async()` takes new requests while handlers wait,
so the slow reads cost the fast ones nothing, as long as the handlers
don't block the worker thread while they wait. File systems whose
requests can take long, such as those of a remote store, should use
`new_async()`, or `SyncFuseServing` if their handlers are synchronous.

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

### Smaller pools with the async handlers

With `UringFuseServing::new_async()`, a request keeps its buffer while its
handler waits, so by default each queue gets a buffer per entry. A smaller
`bufs_per_queue` caps the pools, and requests that need a buffer wait in
the kernel until a handler of their queue is done.

The benchmark daemon served `--uring --async` with `--no-backing-direct-io`
in the setup of the rounds table above. One workload was the 4 KiB random
writes of `bench_sync_async.sh`, 4 jobs with psync through the writeback
cache. The other was the 1 MiB random reads of the rounds table. Each
ran for 8 seconds. The table has medians of 3 runs in alternating order,
and `new()` with its default of 4 buffers for comparison. The writes and
the reads ran in separate sets of runs, and the reads in another set than
the rounds table, so their column also gives the range of the runs.
`new()` with 4 buffers read 40.2 GiB/s here and 39.4 GiB/s in the
rounds table, inside the range of both:

| Buffers per queue | VmSize | 4 KiB writes | VmRSS | 1 MiB reads | VmRSS |
|-------------------|--------|--------------|-------|-------------|-------|
| 16 (default) | 2137 MiB | 2.20M IOPS | 634 MiB | 33.2 GiB/s (33.2-35.0) | 134 MiB |
| 8 | 1369 MiB | 2.13M IOPS | 392 MiB | 39.6 GiB/s (39.6-41.2) | 70 MiB |
| 4 | 985 MiB | 2.28M IOPS | 183 MiB | 40.8 GiB/s (40.1-40.9) | 38 MiB |
| 2 | 793 MiB | 2.39M IOPS | 88 MiB | 42.4 GiB/s (41.9-42.7) | 22 MiB |
| 1 | 697 MiB | 1.75M IOPS | 174 MiB | 40.8 GiB/s (40.4-41.0) | 14 MiB |
| `new()`, 4 | 985 MiB | 2.31M IOPS | 116 MiB | 40.2 GiB/s (39.0-40.6) | 37 MiB |

Each buffer more per queue adds 96 MiB of VmSize, a payload buffer for
each of the 96 queues. The two workloads reach the daemon differently.
Each read is a READ of 1 MiB from one of the 8 CPUs that fio runs on, and
fills a whole buffer of one of 8 pools, so VmRSS is 8 pools and 6 MiB.
fio's writes only dirty the page cache, and the kernel's flusher threads
write the pages back. In a trace of 7 seconds, the daemon got 334k WRITEs
from 22 CPUs, 15% of them of 1 MiB and half of them of 8 KiB or less. So
the writes fill whole buffers of more pools than the reads do. With 16
buffers, pool pages were 558 of the 587 MiB of VmRSS, the pools of about
35 queues. With 1 or 2 buffers, the pools held 21 and 32 MiB, and most of
VmRSS was the daemon's heap, which varied between runs. The writes into
the page cache keep their pace as long as writeback keeps up, so the
write column shows the pool only once it slows writeback down, as with a
single buffer. An earlier measurement on a 24-CPU machine, with an ext4
directory and 4 workers, had 0.82M IOPS for these writes with 4 buffers
per queue and 1.07M with 16. Here, with an XFS directory and 4 workers, 4
buffers gave 2.36M IOPS and 16 gave 2.42M.

The cost shows when slow requests hold the buffers. Each of 4 CPUs ran two
fio jobs with O_DIRECT. One kept 8 reads of a slow file in flight, each of
which waited 1 ms as in "Queue ownership". The other read 4 KiB of a fast
file, one read at a time. VmRSS stayed under 7 MiB with any pool:

| Buffers per queue | Fast reads/s | p50 | p99 | Slow reads/s |
|-------------------|--------------|-----|-----|--------------|
| 16 (default) | 378k | 10 µs | 16 µs | 31.5k |
| 4 | 3.2k | 1.22 ms | 1.91 ms | 15.8k |
| 1 | 2.1k | 1.02 ms | 8.09 ms | 3.9k |
| `AsyncFuseServing` | 138k | 27 µs | 59 µs | 30.1k |

With 4 buffers, the slow reads of a CPU held all of its queue's buffers,
and each fast read waited for one of them to finish.

Waiting for a buffer doesn't deadlock a file system whose handlers finish
on their own. The kernel lends a buffer to an entry only together with a
request, so a request that waits for a buffer holds no entry, and each
buffer comes back when the handler of its request is done. The entry that
commits takes the queue's next request, with its buffer if that request
needs one. A request without a payload and without a reply body, such as
FSYNC, FLUSH or RELEASE, takes a free entry without a buffer.

Handlers that wait for other requests of the same mount can deadlock,
though. If all buffers of a queue belong to handlers that wait for a
request that needs a buffer too, such as READs of a pipe-like file that
wait for a WRITE from the same CPU, none comes back. The kernel also
serves the waiting requests of a queue in order. An entry that commits
looks only at the first one, so a request that queues behind one that
waits for a buffer waits as well, even if it needs none. A request queues
when it finds no free entry, and a background request, such as most
RELEASEs, always queues. With a buffer per entry, the same happens once
all entries of a queue wait. Such a file system needs a buffer per queue
for each request that can wait there at once, and the default has one for
up to `entries_per_queue` requests. The synchronous handlers of `new()`
block their worker while they wait, so they can hang a mount with any
pool.

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

- `bufs_per_queue`: Default is 4 with `new()` and one per entry with
  `new_async()`. On Linux 7.3 and later it caps the requests with a
  payload or reply body that one queue serves at once, and with it the
  memory of the payload buffers. A busy queue reaches only as many
  workers as it has buffers. With `new_async()`, a request keeps its
  buffer while its handler waits, so slow requests hold up the others of
  their queue. See "Smaller pools with the async handlers" above.

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
