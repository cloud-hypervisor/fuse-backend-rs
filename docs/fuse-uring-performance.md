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

## Ring setup flags

The kernel copies a request into its ring entry in task work of the
worker that owns the ring. With the default ring flags, that work
interrupts the worker, also while it runs a handler. With
`UringConfig::defer_taskrun`, the workers of `UringFuseServing::new()`
create their rings with `IORING_SETUP_SINGLE_ISSUER` and
`IORING_SETUP_DEFER_TASKRUN` (Linux 6.1), so the work waits until the
worker waits for completions, and then runs for all the requests that
arrived meanwhile. A worker creates its ring itself and is the only
thread that submits to it. If the kernel refuses the flags with EINVAL,
the worker creates the ring without them.

The setting is off by default because of a kernel bug. On Linux 7.2.0 to
7.2.13, 7.3.0 and 7.3.1, a thread that waits for completions on such a
ring can miss its wake-up. It then sleeps with work queued until a signal
interrupts the wait, and its requests get no answer. Commit 8257f6ec45ee
("io_uring: don't lose the DEFER_TASKRUN wake up") fixed it in 7.4-rc1,
7.3.2 and 7.2.14. The bug came with d46ab2c98aba
("io_uring: switch local task_work to a mpscq") in 7.2, so older kernels
don't have it.

The table shows the throughput of the benchmark daemon with `--uring
--no-backing-direct-io`, 4 workers and 16 entries per queue, without and
with `--uring-defer-taskrun`, on a 96-CPU machine with Linux 7.3.1,
serving files from a tmpfs as root. fio ran 4 jobs for 8 seconds: direct
random 4 KiB reads of 256 MiB files, with one read in flight per job
(psync) or with libaio at depth 16, and direct sequential 1 MiB reads of
1 GiB files at depth 16. It also created 50000 files per job with the
filecreate engine. The stats came from a program that called `stat()` on
those 200000 files from 4 threads in a fresh mount, so each one sent a
LOOKUP. Each workload got a mount of its own. Medians of 8 runs, 5 for
the reads at depth 1:

| Workload | Default | Deferred | p99, default | p99, deferred |
|----------|---------|----------|--------------|---------------|
| stats | 215k/s | 265k/s | 25 µs | 23 µs |
| creates | 44.3k/s | 44.9k/s | 114 µs | 111 µs |
| 4 KiB reads, depth 1 | 376k IOPS | 471k IOPS | 16 µs | 15 µs |
| 4 KiB reads, depth 16 | 904k IOPS | 885k IOPS | 93 µs | 96 µs |
| 1 MiB reads | 18342 MiB/s | 18327 MiB/s | 4.2 ms | 3.9 ms |
| 1 MiB zero-copy reads | 26702 MiB/s | 26755 MiB/s | 2.8 ms | 2.7 ms |

Requests that a client waits for one at a time got faster. The stats ran
at 205k-247k per second with the default flags and at 240k-293k with
deferred task work, and the reads at depth 1 at 363k-394k and 451k-503k
IOPS. The daemon spent 3.6 µs of CPU time per read at depth 1 instead of
4.1 µs. The other rows stayed within the spread of their runs, and so did
the CPU time per operation and the VmRSS of the daemon. With 96 workers,
one per CPU, the stats went from 217k to 250k per second over 3 runs, and
the creates and 4 KiB reads at depth 16 stayed within the spread. In a
later set of 5 runs per setting, the stats went from 203k to 277k per
second (196k-331k and 270k-363k), and the reads at depth 1 from 417k to
449k IOPS (370k-433k and 434k-559k).

The workers of `UringFuseServing::new_async()` wait for completions in
epoll on the ring fd, and from Linux 6.3 on, the kernel doesn't wake
epoll for deferred task work until commit b88902d8745a ("io_uring: wake
ring pollers for local task_work"), which is in 7.4-rc1, 7.3.2, 7.2.14
and 6.18.60. On 7.3.1, with the flags, the first request after the mount
never got an answer. So they take the setting only on those releases
and later ones of their branches, as uname(2) reports them, and run the
task work themselves when epoll wakes them.

The worker has to run all of that work. An `io_uring_enter()` with
`IORING_ENTER_GETEVENTS` runs at most 20 items of task work, or as many
as the completions it waits for (`IO_LOCAL_TW_DEFAULT_MAX` in Linux
7.3), and the kernel wakes epoll only for work it queues while none is
queued. A worker that ran 20 of a burst of completions and went back to
epoll heard of neither the rest nor anything after it. In a test that wrote files from 4 threads,
that stranded a worker about once in 23 runs. So a worker waits for as
many completions as its ring holds, with a timeout of zero, which runs
all queued work and returns. `IORING_SETUP_TASKRUN_FLAG` can't tell
instead when work is left, because the kernel can set `IORING_SQ_TASKRUN`
after the worker ran the work, and with no work queued, nothing clears
it. A worker that entered the kernel until the flag cleared spun.

A process that serves its own mount can strand itself with deferred task
work. If its workers die while a ring holds a request whose task work
hasn't run, for example because the process gets killed, nothing runs
that work, and a thread of the same process that waits for the request
keeps the ring open, so the process never exits. It stays in D state
until a reboot. A daemon that dies closes its rings, which ends the
requests, so only a process that is its own client can strand itself.
The tests of the transport run their clients in child processes for
that reason. Only the worker may enter such a ring, so zero-copy IO from
another thread, such as a scoped thread of a handler, fails with EEXIST
before it queues anything.

The async workers gain less from the setting than the sync ones. The
table shows the benchmark daemon with `--uring --async
--no-backing-direct-io`, 8 workers and 16 entries per queue, without and
with `--uring-defer-taskrun`, also with `--uring-zero-copy`, serving a
tmpfs as root on a 96-core machine with Linux 7.3.4. `PassthroughFs`
had the fix of #381, so its zero-copy READs read the file with io_uring.
Each setting got a mount of its own per pass, which ran, in order: a
walk of 64 directories of 256 empty files with readdir and fstatat in
the fresh mount; 2,000 files of 2 KiB that one thread, or 4 threads 500
each, opened, read and closed in a loop; direct random reads of 4 KiB
and 64 KiB from 1 GiB files with fio, 1 or 4 jobs, with psync at depth 1
or libaio at depth 16; a direct sequential read of a 64 MiB file in
1 MiB blocks; and 4 jobs reading files of 32 MiB that way. fio ran on 4
CPUs of its own, for 3 seconds after 1 second of ramp. Medians of 3
passes, in alternating order, and the daemon's CPU time per read at
4 KiB and depth 1:

| Workload | Copy | Deferred | Zero-copy | Zero-copy, deferred |
|----------|------|----------|-----------|---------------------|
| walk | 143k/s | 144k/s | 146k/s | 139k/s |
| 2 KiB files, 1 thread | 28.5k/s | 24.4k/s | 24.5k/s | 18.8k/s |
| 2 KiB files, 4 threads | 104k/s | 90.0k/s | 91.5k/s | 75.6k/s |
| 4 KiB, 1 job, depth 1 | 93.4k IOPS | 115k IOPS | 75.3k IOPS | 60.4k IOPS |
| CPU time per read | 11.7 µs | 8.5 µs | 19.0 µs | 17.0 µs |
| 4 KiB, 4 jobs, depth 1 | 350k IOPS | 437k IOPS | 287k IOPS | 241k IOPS |
| 4 KiB, 1 job, depth 16 | 263k IOPS | 256k IOPS | 253k IOPS | 256k IOPS |
| 4 KiB, 4 jobs, depth 16 | 696k IOPS | 683k IOPS | 698k IOPS | 750k IOPS |
| 64 KiB, 1 job, depth 1 | 47.7k IOPS | 43.9k IOPS | 40.4k IOPS | 37.1k IOPS |
| 64 KiB, 4 jobs, depth 16 | 435k IOPS | 437k IOPS | 690k IOPS | 710k IOPS |
| 64 MiB sequential | 6226 MiB/s | 5925 MiB/s | 8583 MiB/s | 8289 MiB/s |
| 4 x 32 MiB | 16094 MiB/s | 18201 MiB/s | 31959 MiB/s | 23149 MiB/s |

Buffered reads of 4 KiB at depth 1 got 23% to 25% faster, at 27% less
CPU time per read. There the loop finds the next request in the same
`io_uring_enter()` that submits the last reply, so it makes 2 syscalls
per read instead of 6 and never waits in epoll. Small files got 13% to
23% slower, zero-copy reads at depth 1 16% to 20%, and 64 KiB reads at
depth 1 8%. The zero-timeout wait above puts the worker to sleep until
the timer interrupt on every enter that finds no work, which costs a
context switch, and those workloads pay it more often than they save.
The 4 x 32 MiB row varies by up to 90% between runs in every setting.

`IORING_SETUP_COOP_TASKRUN` runs the task work when the worker next
enters the kernel, instead of interrupting it with an IPI. With both
kinds of workers, it stayed within the spread of the runs in every
workload above, and so did `IORING_SETUP_SINGLE_ISSUER` alone, over 3
runs each.

## Implementation Notes

### Current State

This implementation targets the stable FUSE_URING protocol 7.42 (kernel 6.14+),
and uses the buffer pools of protocol 7.46 (kernel 7.3) when the kernel has them:

- Scatter Reader/Writer eliminates all userspace memcpy
- Per-CPU queue model with configurable entries_per_queue
- Buffer pools with configurable bufs_per_queue, see "Buffer pools" above
- Zero-copy for opens that ask for it, see "Zero-copy" above
- Deferred task work as an option, see "Ring setup flags" above
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

- `workers`: Default is one per CPU. A worker serves the requests of any
  queue it holds entries of, so the count no longer has to match the
  queues. It is capped at `entries_per_queue` times the number of queues.
  Each worker is a thread with its own ring, and with zero-copy also a
  memory file of one payload buffer.

- `defer_taskrun`: Default is off, because some kernels lose wake-ups
  with it. It speeds up requests that a client sends one at a time with
  `new()`. `new_async()` takes it only on the kernels that wake epoll for
  it, and there it speeds up 4 KiB reads at depth 1 but slows down small
  files. "Ring setup flags" above has the numbers and the kernels.

## References

- Bernd Schubert's fuse-over-io_uring patch series:
  https://lore.kernel.org/io-uring/20241209-fuse-uring-for-6-10-rfc4-v8-0-d9f9f2642be3@ddn.com/

- Joanne Koong's buffer pools + zero-copy:
  https://lwn.net/Articles/1049130/

- Kernel documentation:
  https://docs.kernel.org/filesystems/fuse/fuse-io-uring.html
