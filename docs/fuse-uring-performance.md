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

## Handing a connection over

`UringFuseServing` can't hand its connection to another server the way a
takeover with `Server::restore_init()` and `FUSE_NOTIFY_RESEND` does on
`/dev/fuse`. `Server::restore_init()` fails with
`ErrorKind::Unsupported` for the INIT state of a connection that
negotiated `FUSE_OVER_IO_URING`. Where the connection has to outlive the
server process, serve it from `/dev/fuse` and don't call
`Server::set_uring()`. The rest of this section is what
fs/fuse/dev_uring.c does in Linux 7.3 and, where it differs, in 6.14.

The ring and its queues belong to the connection. 7.3 creates the ring
at INIT (`fuse_uring_conn_init()`, from `fuse_chan_set_initialized()`),
6.14 at the first REGISTER (`fuse_uring_create()`). A queue comes with
the first command for it, and the kernel frees both only with the
connection (`fuse_uring_destruct()`). On 7.3 a queue keeps the payload
buffers of the server that set it up. A second
`FUSE_IO_URING_CMD_ADD_QUEUE` fails with EEXIST
(`fuse_uring_create_queue()`), and `ADD_BUFPOOL` fails with EINVAL on a
queue that has a pool or whose entries brought their own buffers
(`fuse_uring_add_bufpool()`). The kernel cuts pool buffers from the
address the first server gave it (`fuse_uring_select_buffer()`), in the
address space of the server whose entry gets the request, so a later
server would have to map its pools at that address. Kernels before 7.3
have neither command, and every entry brings its own payload buffer.

An entry belongs to the io_uring command that registered or last
committed it, and so to that ring and the thread that submitted the
command. The kernel copies a request into the entry from that thread
(`fuse_uring_send_in_task()` runs as task work of the command). Only the
end of the ring or of the thread takes entries back. It cancels the
commands of the entries that wait for a request
(`io_uring_try_cancel_uring_cmd()` calls `fuse_uring_cancel()`). Since
commit 198f45eeb9f7 ("fuse-uring: fix moving cancelled entry to
ent_in_userspace list"), in 7.2, 7.1.4 and 6.18.39, the kernel frees
those entries. Before, it parks them on the queue's `ent_in_userspace`
list until the connection ends. An entry that holds a request keeps it.
Another process can't commit it, because the commit reads the reply
through the addresses of the old one. `FUSE_NOTIFY_RESEND` doesn't reach
it either, because `fuse_chan_resend()` (`fuse_resend()` in 6.14) only
requeues the requests read from `/dev/fuse` file descriptions.

Once the old entries are gone, the connection stays on io_uring. Until
every queue has an entry, the kernel holds new requests back
(`fuse_block_alloc()`). Then it switches the input queue to the ring
(`fuse_uring_do_register()` sets `ring->ready` and `fiq->ops`) and never
back, and only FORGET and INTERRUPT still go through `/dev/fuse`.
`fuse_uring_queue_fuse_req()` leaves a request that finds no entry on
the queue's `fuse_req_queue`, and a new server that reads `/dev/fuse`
would wait for it forever. A REGISTER on a queue that had entries before
is allowed, because `fuse_uring_register()` reuses the queue, but it
doesn't hand the new entry a waiting request. Only a commit on the same
queue does (`fuse_uring_get_next_fuse_req()`). A failed REGISTER takes
the connection off io_uring (`fuse_uring_cmd()` clears `io_uring`). On
7.3 every later uring command then fails with EOPNOTSUPP, and once the
ring is ready, requests still go to its queues.

So a new server could register entries of its own on the queues, but the
old one loses requests while it stops. While no server serves, the old
server's entries are the only ones. A commit makes its entry the first
one the queue hands a request to, and an entry takes requests until the
kernel cancels its command, which happens only after the last fd and
mapping of the ring are gone. A request copied into an entry after its
worker last looked at the ring gets no reply until the connection ends,
on every kernel. A request handed to the entry once the ring goes away
fails with ECANCELED since commit bea4fe98204b ("fuse-uring: end
fuse_req on io-uring cancel task work"), in 7.2, 7.1.4 and 6.18.39.
Kernels without it complete the command with ECANCELED but leave the
request in the entry without a reply. Kernels without commit
3539b1467e94 ("io_uring: include dying ring in task_work "should cancel"
state"), in 6.17 and 6.16.9, even copy the request in, because their
task work stops only for a thread that exits.

A prototype did that handoff. Its old workers served the requests their
commits fetched, closed their rings, and waited for the kernel to free
them. The new server registered on the queues, mapped the pools at the
old address, and sent a STATFS from each CPU to get the waiting requests
out. It handed a PassthroughFs connection to a new server in the same
process 20 times per run, while threads read a file on the mount with
O_DIRECT, one read at a time each. In 35 of 36 runs, on Linux 7.3.1 with
96 CPUs and in 4-CPU VMs with 7.3.4 and 6.18.63, every reader lost a
read: most reads got no reply until the connection ended, and some
failed with ECANCELED. A client that sends its next request right after
a reply sends one while the workers close their rings. Without traffic,
the prototype lost nothing, but a server can't rely on quiet clients.

A lossless handoff needs the kernel to retire an entry without losing a
request: a commit that doesn't fetch, or another way to quiesce a queue,
or a cancel on ring close that requeues the entry's request instead of
failing it (`fuse_uring_cancel()`, `fuse_uring_send_in_task()`). A
REGISTER that hands out waiting requests (`fuse_uring_do_register()`)
and a `FUSE_NOTIFY_RESEND` that covers the ring queues
(`fuse_chan_resend()`) would make the rest work.

## Implementation Notes

### Current State

This implementation targets the stable FUSE_URING protocol 7.42 (kernel 6.14+),
and uses the buffer pools of protocol 7.46 (kernel 7.3) when the kernel has them:

- Scatter Reader/Writer eliminates all userspace memcpy
- Per-CPU queue model with configurable entries_per_queue
- Buffer pools with configurable bufs_per_queue, see "Buffer pools" above
- Zero-copy for opens that ask for it, see "Zero-copy" above
- No handoff to another server, see "Handing a connection over" above
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
