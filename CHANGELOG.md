# Changelog
## [Unreleased]
### Changed
- [305](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/305): Upgrade `fuse-backend-fusedev` (and the root dev-dependencies)
  from `nix` 0.24 to 0.31.4, the I/O-safety era of the crate: `read`/
  `write`/`pwrite`/`writev`/`fcntl` now take `AsFd`, so the raw fds the
  writers borrow from the session's fuse device file are re-borrowed per
  call (`BorrowedFd::borrow_raw` with SAFETY comments); `socketpair`
  returns owned fds; `SetSockOpt` setters take `AsFd`; `cmsgs()` returns a
  `Result`; `poll` takes a `PollTimeout` and `PollFd::new` a `BorrowedFd`;
  `F_SETFD`/`F_SETFL` moved into `FcntlArg`. The deprecated free
  `epoll_ctl` is replaced with a direct `libc::epoll_ctl` on mio's epoll
  instance (nix's owning `Epoll` type would steal the fd mio still owns),
  and tokio's `AsyncFd` needs `AsRawFd`, which nix 0.31's `TimerFd` no
  longer implements — a small wrapper exposes it again. The modules nix
  0.27+ gates behind non-default features are listed explicitly
  (`event`, `fs`, `ioctl`, `mount`, `poll`, `process`, `signal`, `socket`,
  `time`, `uio`, `user`; `mman` for the root tests). The payoff: nix
  0.31's FreeBSD support is Tier 1, and with it `fuse-backend-fusedev`
  builds on FreeBSD again — an empty shell until a FreeBSD session module
  arrives (`serving` is now gated to the OSes that have one, and the
  Linux-only `mio`/`vmm-sys-util` deps are target-gated), proven by new
  `cargo build -p fuse-backend-fusedev` rows (default and `async-io`) in
  `make check-freebsd`. 0.32 is deliberately not taken (released days
  earlier, its accept/accept4 fd-type breakage buys nothing here).
  Related cleanup: the macFUSE session's few CoreFoundation declarations
  (`CFStringCreateWithBytes`/`CFURLCreateWithFileSystemPath`/`CFRelease`)
  move out of the `core-foundation-sys` crate into local `extern "C"`
  declarations — the crate sat unused in the `fuse-t` build, where the
  macFUSE session is compiled out, and the DADisk calls next to them were
  already declared locally; the CoreFoundation framework is now linked
  directly by the fusedev build script.

### Added
- [371](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/371): `FuseSession::set_splice_write()` makes the Linux
  channels send READ replies with `splice(2)` when the file system serves the
  data from a file through `ZeroCopyWriter::write_from()`, as `PassthroughFs`
  does, so the data goes from the page cache into the FUSE request without a
  copy through the server. `FileReadWriteVolatile::raw_fd()` gives the
  transport the file descriptor. A channel falls back to copying when the
  kernel can't splice. It's off by default, because the pipes count against
  the user's `pipe-user-pages-soft`.
- [320](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/320): `VfsOptions::pseudo_dir_mode`, `pseudo_dir_uid` and `pseudo_dir_gid` set the
  permission bits, owner and group of the directories `Vfs` serves itself: its root while no file
  system is mounted at `/`, and the directories on the path to each mount point. The defaults
  keep today's root-owned `0777` ([#148](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/148)).
- [304](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/304): Give FreeBSD a verification path. The Linux wire-format ABI
  body moves out of `fuse_abi_linux.rs` into a shared `fuse_abi_wire.rs`
  (each per-OS prelude re-exports the libc names the body uses), and a new
  FreeBSD ABI arm reuses it — FreeBSD's in-kernel fusefs speaks the Linux
  wire protocol — bridging the libc spellings (`stat`/`preadv` instead of
  the glibc LFS-64 names, `u16` `mode_t`, `ENOATTR` for a missing xattr,
  a literal `UIO_MAXIOV`). `Vfs` advertises the Linux capability set there
  (the negotiation clamps it to what the kernel offered), and a Cirrus CI
  task — GitHub Actions has no FreeBSD runner — runs `make check-freebsd`,
  so `fuse-backend-core` and `fuse-backend-vfs` build and pass their unit
  tests on a real FreeBSD VM. The transport and the filesystem drivers
  stay FreeBSD-unbuildable (`nix` 0.24 does not compile there), and nothing
  here claims runtime behavior against a FreeBSD kernel yet.

- [303](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/303): Fill in the macOS twin of the passthrough driver, turning the
  PR #182 prototype (akitaSummer's macOS port) into a working mount on top of
  the cross-platform framework. Reopen-for-IO goes through a hub on the
  `O_EVTONLY` handle: `fcntl(F_GETPATH)` derives the file's current path on
  demand (the descriptor pins the vnode, so renames are tracked) and the
  reopen validates `(st_dev, st_ino)` against the inode's id, answering
  `ESTALE` on mismatch so the client re-looks-up. `getdents64()` synthesizes a
  Linux-format buffer from `fdopendir()`/`readdir()` with self-issued
  entry-index cookies (Darwin's `d_seekoff` reads zero on APFS, `telldir()`
  cookies are stream-local), resuming by rewinding and skipping. The xattr
  family maps onto the fd-based `f{set,get,remove,list}xattr()` calls with
  pass-through flags and errnos (macFUSE forwards Darwin `XATTR_*` values and
  returns daemon errnos verbatim, so `ENOATTR` reaches macOS callers
  correctly). Hard links derive the old path via `F_GETPATH` with the same
  dev/ino validation. The umbrella crate re-exports `fuse_backend_rs::
  passthrough` on macOS, and its `async-io` feature is accepted there: the
  native async path stays Linux-only (`preadv2`/`RWF_NOWAIT`, io_uring), and
  the async traits fall back to the default methods that delegate to the
  synchronous handlers. A macFUSE e2e smoke test (readdir/read/write/
  xattr/link plus handle-less chmod/touch and a stale-reopen probe through
  the mount) joins the macOS CI. Handle-less setattr
  (chmod/touch with no fh) goes through `fchmod()`/`futimens()` on the
  tracked descriptor instead of the Linux `/proc/self/fd` by-path route,
  which answered `ENOTDIR` against the macOS placeholder dirfd.
  `fallocate`,
  `copy_file_range` and the `RENAME_*` flags stay `ENOSYS` (the FUSE clients
  have fallbacks; `F_PREALLOCATE`/`fcopyfile` are future work).

- [285](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/285): Add `uring_available()`, which tells
  whether the kernel lets the process serve FUSE over io_uring: the fuse module's `enable_uring`
  parameter is on and the process may create an io_uring. Checking it before mounting saves a
  mount that would fall back to `/dev/fuse`.
- [301](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/301): Give `fuse-backend-passthrough` a cross-platform framework: the
  Linux syscall seams (statx, file handles, mount fds, credentials, directory
  walks, file operations, kernel passthrough) move behind per-OS subtrees
  (`os/linux/` with `os/macos/` twins), so the crate now also compiles on
  macOS. The macOS modules are honest stubs — types are real, unported
  operations answer `ENOSYS` — so a macOS mount fails cleanly instead of
  half-working; filling in the macOS implementations is future work. The kernel
  passthrough is gated by kernel capability instead of by OS: macOS defines
  the `FsOptions::PASSTHROUGH`/`FOPEN_PASSTHROUGH` wire values macFUSE never
  offers, and its inert twin keeps `set_backing_files()` and the public
  `BackingFiles` trait compiling. Linux behavior is unchanged
  (the seams are 1:1 delegations), and `make build-macos`/`check-macos` grow
  matching rows for the crate.
- [302](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/302): Symmetrize `fuse-backend-core`'s per-OS ABIs and un-gate the
  server code that only carried `target_os` predicates because the macOS ABI
  lacked symbols: the macOS ABI now defines the Linux protocol values
  macFUSE never sends (opcodes 44..47, `Rename2In`/`LseekIn`/`LseekOut`,
  `FUSE_EXT_GROUPS` extension types, `MAX_PAGES`, and `InitOut`'s
  `max_stack_depth`), `libc::RENAME_*` moves into the ABIs as wire
  constants, and the shared dispatch handlers, `parse_create_extensions()`
  and the INIT negotiation run without OS gates — with two deliberate
  exceptions: `INIT_EXT` stays Linux-only (macFUSE assigns its bit 30 to
  `VOL_RENAME`), and the io_uring runtime keeps its Linux-only carrier
  gates. The `overlay::Layer` contract compiles on both platforms once the
  `mode_t`/`ENOTSUP`/`ENOATTR` libc vocabulary differences are bridged, and the
  server test module now runs on macOS too, exercising the un-gated
  handlers there. `fuse-backend-vfs` gets the same treatment: the
  `no_open`/`no_opendir`/`no_writeback`/`killpriv_v2` options and their
  negotiation run on both platforms (macFUSE never offers the
  zero-message capabilities, so the negotiation keeps open/opendir
  handling enabled there), and the ABIs gain u32 `S_IF*`/`S_IRWX*` mode
  vocabulary replacing per-OS widening casts. `init()` strips
  `ATOMIC_O_TRUNC` only when `no_open` actually survives negotiation
  (the backends already negotiated this way), preserving the macFUSE
  atomic-trunc advertisement; on Linux only pre-4.20 kernels (no
  `ZERO_MESSAGE_OPEN`) see a changed reply. `VfsOptionsState` gains the
  four capability fields on macOS, so macOS persist blobs saved before
  this change cannot be restored (the Linux layout and version are
  unchanged).
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Split the library into a layered Cargo workspace and break the layers out into
  their own crates — `fuse-backend-core` (ABI, API/server, buffers),
  `fuse-backend-fusedev` and `fuse-backend-virtiofs` (transports), and
  `fuse-backend-passthrough` and `fuse-backend-overlayfs` (filesystem drivers) —
  so they can be depended on directly instead of only through the umbrella crate.
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Add standalone `passthrough` and `overlayfs` cargo features that select a
  filesystem driver on its own, without any transport.
- [252](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/252): Extract the `Vfs` union multiplexer (with its `pseudo_fs` backing store) into
  a seventh crate, `fuse-backend-vfs`, resolving RFC open question 3. It sits
  between the facade and `fuse-backend-core` and carries the `arc-swap` and
  `persist` (`versionize`/`dbs-snapshot`) stack that the multiplexer needs.
- [188](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/188): docs: document the experimental status of async-io support.
- [188](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/188): Add a unified serving layer to the fusedev transport. The `FuseServing`
  trait is implemented by `SyncFuseServing` (classic `/dev/fuse` with synchronous handlers, always
  available), `AsyncFuseServing` (`async-io` feature) and `UringFuseServing` (`fusedev-uring`
  feature): each takes ownership of a mounted `FuseSession`, spawns workers per its configuration
  and turns `Drop` into teardown (stop accepting, finish in-flight requests, unmount, join the
  workers), while `FuseServing::wait()` waits out teardown driven from outside the process.
- [188](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/188): Add `SyncFuseServing`, the serving loop every hand-rolled fusedev daemon
  duplicated, as a library type: N epoll-based worker channels — or, with
  `SyncServingConfig::blocking`, blocking channels cloned with `FUSE_DEV_IOC_CLONE` — each
  dispatching requests to a `Server<F>` until the session is torn down. On macOS the session
  exposes a single channel, so multi-worker configurations are rejected.
- [188](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/188): Add `AsyncFuseServing`/`AsyncServingConfig`, scaling the classic transport
  out to N asynchronous workers, and `UringFuseServing`/`UringConfig` for the experimental
  FUSE-over-io_uring transport (kernel 6.14+). Both join the `FuseServing` interface, so a daemon
  can pick its transport at runtime behind `Box<dyn FuseServing>` and fall back to the classic
  transport on `Error::UringNotSupported`.
- [267](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/267): `async_runtime::set_runtime_type()` selects the asynchronous runtime type in code, because
  setting `FUSE_BACKEND_RS_ASYNC_RUNTIME` from a running program isn't safe.
  `async_runtime::runtime_type()` returns the type in effect, and `RuntimeType` is now public.
- [267](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/267): `Server::init_state()` and `Server::restore_init()` let a new server take over a connection
  that another server initialized. `abi::fuse_abi::UNIQUE_RESEND` is the bit that the kernel
  sets in requests it sends again after `notify_resend()`.
- `RuntimeType::file_io_blocks()` tells whether async file IO on a runtime type blocks the
  calling thread, as it does on tokio.
- Linux kernel FUSE passthrough, from Linux 6.9 on. `FsOptions::PASSTHROUGH` and
  `OpenOptions::PASSTHROUGH` enable it, and the fusedev transport's `fuse_backing_open()` and
  `fuse_backing_close()` register and release backing files. `Server::set_max_stack_depth()` sets
  the depth sent in the INIT reply, which a backing file on overlayfs needs. In the ABI,
  `BackingMap` is the argument of the backing ioctl.
- `PassthroughFs::set_backing_files()` and the `BackingFiles` trait make `PassthroughFs` use
  kernel passthrough. `init` leaves it off when the kernel doesn't offer it. It also stays off
  with the writeback cache, `no_open`, `seal_size`, `allow_direct_io = false`, and the `Never`
  and `Metadata` cache policies. With the `async-io` feature, `PassthroughFs::into_shared()` shares a file system
  created with `new()`, so the blocking thread pool can use passthrough too.
- When `VfsOptions::out_opts` has `FsOptions::PASSTHROUGH` and the kernel offers it, `Vfs` turns
  off the writeback cache and `no_open` for all mounts, so kernel passthrough works without
  setting them by hand.
- [269](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/269): `AsyncFileSystem` methods default to calling their `FileSystem`
  counterparts, so a file system only implements the handlers it serves asynchronously.
- [269](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/269): `FuseSession::detach()` lazily unmounts a Linux session through `&self`,
  so the owner of a serving layer can start the teardown while another thread waits in
  `FuseServing::wait()`.
- `AsyncFileSystem` has `async_opendir()`, `async_readdir()`, `async_readdirplus()` and
  `async_releasedir()`, which default to the sync handlers. The async server serves OPENDIR,
  READDIR, READDIRPLUS and RELEASEDIR with them, so a file system that implements them can
  list a directory without blocking the worker. `Vfs` passes them on to the mounted file
  systems.
- [281](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/281): On Linux 7.3 and later, `UringFuseServing` gives each kernel queue a buffer pool of
  `UringConfig::bufs_per_queue` payload buffers. The kernel lends them to the queue's ring entries
  while they serve a request, so with fewer buffers than entries a mount needs less memory.
  `bufs_per_queue` defaults to 4, the default number of entries, and counts as at most
  `entries_per_queue`. 0 keeps a buffer per entry, as on older kernels. `UringConfig` has a new
  field, so struct literals need `..Default::default()`.
- [281](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/281): `abi::fuse_uring` has the commands, INIT flag and fields of protocol 7.46 for buffer pools.
  `Server::uring_bufpool_supported()` tells whether the kernel offered them at INIT, and
  `Server::uring_payload_size()` returns the size of the kernel's payload buffers.
- [282](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/282): `OpenOptions::IO_URING_ZERO_COPY` and the zero-copy flags of protocol 7.46 in
  `abi::fuse_uring` let a file system ask for FUSE-over-io_uring zero-copy on an open.
  `Reader::with_zero_copy()` attaches request data that only the transport can move, through a
  `ZeroCopySource`, and `Reader::read_to_at()` hands it over. `FileReadWriteVolatile::raw_fd()`
  gives the transport the file descriptor to move it to. Other reads get a copy through memory.
- [282](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/282): `passthrough::Config::uring_zero_copy` asks for FUSE-over-io_uring zero-copy on the files that
  `PassthroughFs` opens, except files it opens with O_DIRECT.
- [282](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/282): With `UringConfig::zero_copy` on Linux 7.3 and later, `UringFuseServing` serves the reads and
  writes of opens that ask for it with zero-copy. It moves the data between the client's pages
  and the file with io_uring fixed-buffer operations. It needs buffer pools and CAP_SYS_ADMIN,
  and serves without it otherwise. `UringConfig` has a new field.
- [313](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/313): `AsyncFileSystem` has async versions of 18 more handlers: `async_readlink()`,
  `async_symlink()`, `async_mknod()`, `async_mkdir()`, `async_unlink()`, `async_rmdir()`,
  `async_rename()`, `async_link()`, `async_statfs()`, `async_release()`, `async_setxattr()`,
  `async_getxattr()`, `async_listxattr()`, `async_removexattr()`, `async_flush()`,
  `async_access()`, `async_lseek()` and `async_copy_file_range()`. They default to the sync
  handlers, and the async server serves their requests with them. `Vfs` passes all but
  `async_lseek()` on to the mounted file systems, like its sync handlers do. The async server
  now sends only INIT, DESTROY, NOTIFY_REPLY, locks, `ioctl`, `poll`, `bmap`, forgets and DAX
  mappings to the sync handlers.
- [313](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/313): With `enable_async_thread_pool()`, `PassthroughFs` also serves those 18 handlers,
  `async_opendir()` and `async_releasedir()` on the blocking thread pool. Of its async handlers,
  only READDIR and READDIRPLUS still run on the runtime thread. A MKDIR, MKNOD, SYMLINK, LINK or
  OPENDIR that is dropped while a pool thread serves it gives back the lookup count or handle it
  took.

### Changed
- [325](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/325): The `fuse-backend-fusedev` `uring` transport uses io-uring 0.6 instead of 0.5,
  and depends on it only on Linux.
- [324](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/324): `fuse-backend-core` uses bitflags 2 instead of 1. The flag types (`FsOptions`,
  `OpenOptions`, `SetattrValid`, `IoctlFlags`, `virtio_fs::SetupmappingFlags`) keep their traits
  and methods, except that the safe `from_bits_retain()` replaces the unsafe
  `from_bits_unchecked()`. `Debug` now prints the type name, as in
  `FsOptions(ASYNC_READ | POSIX_LOCKS)`, and an empty set prints `FsOptions(0x0)`, not `(empty)`.
- [294](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/294): `PassthroughFs` negotiates
  `FsOptions::DIRECT_IO_ALLOW_MMAP` under the `Never` and `Metadata` cache policies only when the
  new `Config::allow_mmap` opts in (default off), so shared mmaps keep failing with `ENODEV` there
  by default: a negotiated flag would serve them from the client page cache, which the kernel only
  invalidates on each new mmap and on its own direct writes — weaker than the no-caching promise
  those policies make. The `Auto` and `Always` policies still negotiate the flag for the explicit
  `O_DIRECT` opens. A standalone `OverlayFs` mount under `CachePolicy::Never` gains the same
  `Config::allow_mmap` knob. Behind a `Vfs` the flag is connection-wide in `VfsOptions::out_opts`,
  where a strict deployment removes it like any other capability bit.
- [315](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/315): The async methods of `transport::Writer` are native `async fn`s instead of `async_trait`
  methods, so the `async_write*()` and `async_commit()` calls of a reply no longer box a future.
  Implementations drop their `#[async_trait(?Send)]` attribute. `Writer::async_write_from_at()`
  and `Reader::async_read_to_at()` take an unsized file type, so the server passes
  `&dyn AsyncFileReadWriteVolatile` instead of going through the `Arc` forwarding impl, which
  boxed one more future per READ and WRITE. Overrides of `async_write_from_at()` add `+ ?Sized`
  to `F`. A 4 KiB READ through `Server::async_handle_message()` takes 25-35 ns (3-5%) less.
- Without the thread pool, `PassthroughFs::async_write()` writes with `pwritev()` on tokio-uring
  too, as it does on tokio. ext4 and tmpfs don't take buffered writes that can't block, so
  io_uring handed every write to an io-wq thread. 4 KiB random writes through `/dev/fuse` with
  4 async workers went from 861k-906k to 1073k-1078k IOPS. A write that waits on dirty page
  throttling now stalls the worker, as in the sync server. Zero-copy writes over io_uring don't
  change, and still pay for the io-wq thread on ext4 and tmpfs. For this,
  `async_file::File::borrow_fd_blocking()` borrows a descriptor whose IO never uses io_uring.
- With the thread pool on the tokio runtime, `PassthroughFs::async_write()` first tries
  `pwritev2(RWF_NOWAIT)` on the runtime thread, like `async_read()` does with `preadv2()`, and
  hands only a write that would block to the pool. On XFS that saves the copy and the pool
  thread for most writes: 4 KiB random writes through `/dev/fuse` with 4 async workers went
  from 2.34M to 2.48M IOPS, and the daemon used 12% less CPU time on them and 16% less on
  1 MiB sequential writes. A handle whose file rejects non-blocking writes, on ext4 or tmpfs,
  stops trying after the first.
- `PassthroughFs::async_read()` stops trying `preadv2(RWF_NOWAIT)` on a handle once its file
  rejects the flag with `EOPNOTSUPP`, as files on tmpfs, overlayfs and FUSE do. Without the
  thread pool, it then reads them with `preadv()` on the runtime thread, also on tokio-uring,
  where io_uring handed each such read to an io-wq thread. 4 KiB random reads through
  `/dev/fuse` from tmpfs with 4 async workers went from 194k-196k to 314k IOPS. A read that
  misses the cache of overlayfs or FUSE now stalls the worker, as in the sync server.
- Bump the declared minimum supported Rust version (MSRV) from 1.80 to 1.86.
  Trait-object upcasting (stabilized in Rust 1.86) is required by the default
  `AsyncFileSystem` read/write handlers and by the passthrough O_DIRECT relay,
  so with the `async-io` feature enabled the workspace has not built on older
  toolchains for a while — the 1.80 declaration was already inaccurate. CI
  gains an MSRV job that checks the crates declaring `rust-version` with the
  declared version, so the next accidental bump is caught.
- The FUSE-over-io_uring transport answers opcodes it doesn't know with ENOSYS instead of EIO.
  Kernels that send `FUSE_STATX` only fall back to `FUSE_GETATTR` after ENOSYS, so `statx()`
  calls that ask for more than the basic fields, like the birth time `stat(1)` shows, failed.
- `AsyncFileSystem::async_open()` and `AsyncFileSystem::async_create()` return the backing id of
  kernel passthrough as the last element of their tuple, like `FileSystem::open()` and
  `FileSystem::create()`. The default methods forward the id from the sync handlers.
  Implementations that override them need to add it, and `None` keeps the old behavior.
- `InitOut` has a `max_stack_depth` field, which takes one of its `unused` words, so `unused` is
  now `[u32; 6]`.
- `PassthroughFs::init()` warns when the file system has backing files but INIT doesn't offer
  `FsOptions::PASSTHROUGH`, as on a kernel without `CONFIG_FUSE_PASSTHROUGH` or under a `Vfs`
  whose `out_opts` lacks it. It used to serve all IO in the daemon without logging anything.
- [267](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/267): With the tokio runtime, `FuseDevTask` no longer retries reads in a loop. It waits for requests
  through the IO driver of the tokio runtime that polls it, and checks its state flag every 100ms
  while idle. Polling it on a tokio runtime without IO enabled panics. `fuse-backend-fusedev`
  needs tokio 1.53.3.
- [267](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/267): The async fusedev server retries a read that fails with `ENOENT` and stops the task on read
  errors it doesn't know, like the synchronous server. It used to log them and read again.
- `async-io` builds on macOS, where it runs on tokio. `fuse-backend-core` now depends on
  `io-uring` only on Linux, like `tokio-uring`.
- If io-uring isn't available, `set_runtime_type(RuntimeType::Uring)` returns the probe's
  error, and the fallback warning includes it.
- On the tokio runtime, the vectored reads and writes of `async_file::File` make one
  `preadv()`/`pwritev()` call for all buffers instead of one call per buffer.
  `async_file::preadv()` and `pwritev()` accept more than 1024 buffers and make one call per
  1024.
- `PassthroughFs::enable_async_thread_pool(true)` also moves READ and WRITE
  requests that would block the runtime thread to the blocking thread pool.
  These are the O_DIRECT and WRITE_KILL_PRIV requests, and on the tokio
  runtime also READ cache misses and every WRITE. On a file system without
  `RWF_NOWAIT`, such as tmpfs, overlayfs or FUSE, every READ counts as a cache
  miss. Each of these requests costs one more copy and a thread handoff.
- The umbrella crate's `async-io` no longer turns on the `fusedev` and `virtiofs`
  transports. Code that uses the items they gate, such as `abi::virtio_fs`, has
  to enable them. A crate that depends on a transport crate directly must enable
  that crate's `async-io` too, or its writers fail asynchronous replies with
  `EINVAL`.
- [281](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/281): `FuseUringEntInOut::padding` is now `offset`, and `FuseUringCmdReq` has a new `bufpool` field.
- [316](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/316): `UringFuseServing` spreads the ring entries of every kernel queue over its workers, instead of
  giving each worker whole queues, and the workers register them in rounds, so that requests that
  arrive together reach different workers. With the default worker per CPU, 1 MiB reads from 8 CPUs
  got 2.5 times faster. With 8 workers, writes through the writeback cache got 18 to 27% faster,
  and reads from 8 CPUs whose queues each had a worker of their own got 11 to 17% slower.
  `UringConfig::workers` can exceed the number of queues, up to `entries_per_queue` times that,
  and an `entries_per_queue` of 0 counts as 1.
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): `fuse-backend-rs` is now a thin facade re-exporting the sub-crates. Every
  historical `fuse_backend_rs::{abi, api, buffer, common, transport, passthrough,
  overlayfs}` import path and cargo feature name (`fusedev`, `virtiofs`,
  `vhost-user-fs`, `async-io`, `persist`, `fuse-t`, `fusedev-uring`) still
  resolves to the same types, so existing dependency lines are unchanged.
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Small breaking surface from the layering fix (a 0.x release may break API):
  `transport::Writer` is a trait now instead of an enum, so code naming its
  variants must adapt; the transport-specific `Reader` constructors
  (`from_fuse_buffer`, `from_descriptor_chain`) moved onto the `FuseDevReaderExt`
  and `VirtioFsReaderExt` extension traits and need that trait in scope (the
  `Reader::from_…` spelling is otherwise unchanged); and on `transport::Error`
  the never-constructed `ConvertIndirectDescriptor` variant was removed, while
  `FindMemoryRegion` and `InvalidChain` are now gated behind the `virtiofs`
  feature. Those variants stay on the same `transport::Error` type (there is no
  separate virtiofs error type), so a `virtiofs` build matching them is
  unaffected.
- [252](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/252): Replace the `lazy_static` dependency with `std::sync::LazyLock` and declare
  an explicit MSRV of Rust 1.80 (`rust-version = "1.80"`) on every published
  crate. No API change; this drops one dependency and formalizes the minimum
  toolchain, which was previously undeclared (CI builds on `stable`).
- [252](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/252): `Vfs`, `arc-swap` and the `persist` snapshot stack
  (`versionize`/`dbs-snapshot`) move out of `fuse-backend-core` into
  `fuse-backend-vfs`, so a consumer that brings its own `FileSystem` and does
  not need the multiplexer can depend on `fuse-backend-core` directly and skip
  `arc-swap` entirely (`cargo tree -p fuse-backend-core --all-features` shows no
  `arc-swap` or `dbs-snapshot`). The umbrella crate depends on
  `fuse-backend-vfs` unconditionally and still re-exports the historical
  `api::vfs::*` and flat `api::Vfs` paths under every feature combination
  (guarded by `tests/legacy_paths.rs`), so existing imports and the
  `persist`/`async-io` feature names are unchanged, and snapshots stay
  byte-compatible.
- [#221](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/221): `FuseDevWriter` no longer derives `PartialEq`/`Eq`; comparing two
  writers for equality was never meaningful (they wrap a mutable reply buffer)
  and no code in the workspace relied on it.

### Fixed
- [NNN](link): A `FuseDevTask` that keeps finding requests lets its runtime run. On tokio,
  `AsyncFd::ready()` takes none of the task's budget, and the read of a readable fuse fd doesn't
  wait, so a task that kept finding requests never returned to its runtime. The timers, IO and
  other tasks there waited until the clients paused, and so did the `AsyncFuseServing` handlers
  that waited for a timer or for a task they spawned. After 64 requests read in a row without
  waiting, the task now waits for the new `fuse_backend_core::async_runtime::park()`, which yields
  on tokio and waits for the runtime to park on tokio-uring.
- [328](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/328): The servers answer a request that fails before it gets a reply. A malformed
  request (a short body, a name without its NUL, a size that disagrees with the body) gets
  `EINVAL`, and a failure of the server itself, such as remapping the ids, gets `EIO`. Most early
  returns in the handlers dropped such a request, and FUSE has no request timeout, so the client
  waited forever. `handle_message()` and `async_handle_message()` then return the size of the
  reply, not the error, because transports treat an error as a request without a reply: the
  io_uring worker replaced the reply with `EIO`, and a virtio-fs device may never return the
  descriptor. FORGET, BATCH_FORGET, INTERRUPT and NOTIFY_REPLY get no reply, now also when they
  are oversized.
- [329](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/329): The servers no longer reply to NOTIFY_REPLY when `FileSystem::notify_reply()`
  fails, which the default implementation does. The kernel takes no reply to NOTIFY_REPLY, and
  sends it under the unique number that the server picked for NOTIFY_RETRIEVE, so the reply
  could end another request. `handle_message()` returns the error instead.
- [NNN](link): With `allow_direct_io` off, a create with O_DIRECT no longer opens the new host
  file with O_DIRECT, which made buffered IO on it fail with EINVAL. `PassthroughFs::create()`
  now builds the host open flags with the same helper as `open_inode()`.
- [347](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/347): `Vfs` forwards COPY_FILE_RANGE to the mounted file system that holds both
  files, so a `PassthroughFs` behind a `Vfs` copies on the host. `Vfs` answered ENOSYS, on
  which the kernel stops sending COPY_FILE_RANGE on the connection and falls back to a
  splice copy. A copy between two mounts now gets EXDEV, and a backend's ENOSYS turns into
  EOPNOTSUPP. On both, Linux falls back for that call only. FreeBSD falls back only on
  ENOSYS, so there both stay ENOSYS. The pseudo fs directories answer EISDIR.
- [303](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/303): The sync server answers a SETXATTR request it received in full
  but cannot decode — no NUL separator in the attribute name, or a value size
  that disagrees with the body — with `EINVAL` instead of dropping it. FUSE
  has no request timeout, so a dropped request hung the client forever: an
  uninterruptible sleep against `/dev/fuse` on Linux, and a permanent stall
  under fuse-t's hard NFS mount. (The async server dispatches SETXATTR to the
  same shared handler, so it had the identical silent exits; fixing the sync
  handler covers both serving paths.)
- SYMLINK, RENAME and RENAME2 also answer `EINVAL` when the body lacks one of
  its two NUL-terminated names, for the same reason as SETXATTR above.
- [303](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/303): The macOS `INIT` reply keeps the 24-byte macFUSE shape for any client
  version, instead of growing to the full 64-byte Linux struct for clients
  that advertise a newer minor. macFUSE's own `fuse_init_out` never grew past
  the `FUSE_COMPAT_22` shape, and the reply size is wire-visible: fuse-t 1.2.x
  reads it to classify the daemon's client family, and a Linux-shaped reply
  made it negotiate its libfuse3 profile and parse every later reply with
  Linux field offsets, tearing the mount down right after the handshake.
  macFUSE kernels (minor 19) already received the 24-byte reply, so only such
  probed transports are answered differently.
- A shared mmap of a file opened with O_DIRECT on a `PassthroughFs` mount failed with ENODEV,
  because the open replies `DIRECT_IO`. `PassthroughFs` and the `Vfs` defaults now negotiate the
  new `FsOptions::DIRECT_IO_ALLOW_MMAP` when the kernel offers it, so the kernel maps such a file
  through the page cache. This also allows shared mmap with the `Never` and `Metadata` cache
  policies, which open every file with `DIRECT_IO`.
- Turning O_DIRECT on or off for a READ or WRITE no longer puts O_APPEND back on a host file
  that the writeback cache opened without it. `PassthroughFs` passed the client's open flags to
  `fcntl()`, so later writes on that handle went to the end of the file instead of their offset.
- [308](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/308): With `allow_direct_io` off, an O_DIRECT READ or WRITE no longer sets O_DIRECT on the
  host file with `fcntl()` under `no_open` or on a handle opened without it, which made buffered
  IO on that file fail with EINVAL.
- Reading a request from the fuse device now returns `Ok(None)` on `ECONNABORTED` too, like
  `ENODEV`. The kernel returns `ECONNABORTED` instead of `ENODEV` when the connection is aborted
  while a request is being handed over to the reader, so `FuseChannel` and
  `BlockingFuseChannel` reported a session failure for a teardown their callers should see as a
  normal end — for example a blocking channel whose `FUSE_INIT` read races the session's umount.
- GETXATTR and LISTXATTR answer ERANGE when the file system returns a value or name list
  bigger than the requested size, instead of a reply the kernel would reject with EINVAL
  (surfacing as EIO to the caller). The server now enforces the documented size contract
  on the file system's behalf: a value or name list for a zero-size probe is converted to
  the needed size the kernel expects, and a count for a nonzero size is answered with
  EINVAL instead of being copied out as the value or the list. The `getxattr`/`listxattr`
  trait docs say so.
- `Vfs` no longer runs xattr names through its path component checks. They failed a name with
  '/', which Linux allows, and the names '.' and '..' with EINVAL. The file system now gets them.
- READDIR and READDIRPLUS answer ENOMEM when the reply can't hold the reply header plus the
  requested size. The check left out the header, so a writer short by up to 16 bytes started the
  listing and failed partway.
- A `UringFuseServing` worker that fails while the connection is up ends the connection through
  its fusectl `abort` file. Its queues had no entries left, so requests from those CPUs waited
  forever, and so did requests it had taken but not answered. Now they fail, the other workers
  stop, and `FuseServing::wait()` returns.
- A `UringFuseServing` worker whose request handler panics ends the connection the same way and
  waits for the kernel to give its ring entries back before the panic goes on. Before, unwinding
  freed entries the kernel could still copy a request into.
- A `UringFuseServing` worker that stops frees its ring entries only after the kernel has given
  them all back, and leaks them if that takes more than a second. A worker that stopped on an
  error while the connection was up freed entries the kernel could still copy requests into. A
  signal that interrupts the worker's `io_uring_enter()` calls no longer stops it.
- `UringWriter::write_from_at()` fails when the data doesn't fit into the reply body. It counted
  free space in the header slot too, and could read file data past the end of the body.
- [278](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/278): Treat `EOPNOTSUPP`/`ENOTSUP` and `ENOSYS` from `getxattr` as "not opaque"
  in `Layer::is_opaque()`, so `OverlayFs::import()` no longer aborts when a layer's
  backing filesystem has no xattr support at all (tmpfs answers `EOPNOTSUPP` to
  `user.*` xattrs before Linux 6.12, and a `PassthroughFs` layer with `xattr`
  disabled answers `ENOSYS`).
- [269](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/269): For a session mounted with `set_target_mntns()`,
  `FuseSession::umount()` unmounts in that mount namespace. It no longer follows a symlink at the mountpoint.

### Removed
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Drop the vestigial `vhost` and `virtio-bindings` dependencies that the
  pre-split `vhost-user-fs` build carried but never referenced; `vhost-user-fs`
  is now an alias for the `virtiofs` build.

## [0.14.0]
### Added
- [261](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/216): feat(fusedev): add try_with_writer on FuseSession

### Fixed

### Removed
- [222](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/222): Drop virtiofs DAX support as it never made it to the spec

## [0.13.0]
### Added
- [187](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/187): Feat/support fuse resend notify
- [211](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/211): Add notify_inval_inode and extend get_rootfs to return fs_idx for umount

### Fixed
- [189](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/189): fix by_id not free when use_host_ino=true
- [191](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/191): fix request size too large when use direct io
- [205](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/205): Fix: unable to perform sync on directory
- [212](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/212): Fix fuse out header len in notify_resend

## [0.12.0]
### Added
- [156](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/156): Fuse OverlayFs implementation.
- [166](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/166): Import latest improvement for passthroughfs from virtiofsd project.
- [169](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/169): Optimize implementation of lookup() for passthroughfs.
- [170](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/170): abi: unify st_nlink.
- [172](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/172): ptfs: refine implementation of seal_size_check().
- [173](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/173): ptfs: use BorrowedFd instead of RawFd when possible.
- [174](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/174): ptfs: add support for new cache mode Metadata.
- [177](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/177): fusedev: add clone_fuse_file method to FuseSession.

### Fixed
- [125](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/125): fusedev: add fd-passthrough support.
- [178](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/178): Fix batch forget can't handle too large msg.
- [180](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/180): fix: fuse-t nobrowse.
- [181](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/181): Fix CI: xfstests: restrict xfstests version.
- [184](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/184): bugfix: read/write fd dropped unexpectedly.
- [185](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/185): fix: fuse t channel read bug in during multiple reads

## [0.11.0]
### Added
- [144](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/144): feat: implement fuse-t feature
- [149](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/149): feat: add "persist" feature
- [152](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/152): Add the ability to clean up the dentry cache can be used to clean up resources when VFS umount.
- [153](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/153): linux_session: Make allow_other mount option optional
- [159](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/159): UID/GID remapping support
- [162](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/162): abi: Disable unsupported flags and functionality on MacOS
- [163](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/163): vfs: add method to export root pseudofs's reference
- [167](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/167): CI: add xfstests for passthrough fs

### Fixed
- [154](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/154): fuse: Ensure fd has same flags as read/write
- [165](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/165): build: fix a build failure related to conditional compilation

## [0.10.5]
### Added
- [138](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/138): linuxsession: support mount in given mount namespace
- [141](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/141): linux_session: support set fusermount binary

### Fixed
- [140](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/140): fuse: Ensure readdir returns same ino as lookup

## [0.10.4]

### Added
- [135](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/135): ZeroCopyWriter pass through available bytes from inner writer

### Fixed
- [133](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/133): https://github.com/cloud-hypervisor/fuse-backend-rs/pull/133

## [0.10.3]

### Added
- [#115](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/115)
  * transport: pre-allocate VecDeque to avoid expending at runtime
  * passthroughfs: convert MultiKeyBTreeMap to InodeStore for InodeMap
  * passthroughfs: add config to specify entry and attr timeout for dir
  * passthroughfs: add config to control count mntid in altkey or not
- [#119](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/119): Support non-privileged users
- [#126 #127](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/126 https://github.com/cloud-hypervisor/fuse-backend-rs/pull/127): vfs: ensure entry attr st_ino consistency
- [#131](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/131): implement stable unique inode for passthroughfs

### Fixed
- [#120](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/120): api: forget and batch forget must not reply
- [#123](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/123): fix possible IO hang due to string convertion failure
- [#129](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/129): abi: st_nlink is u32 on aarch64

## [0.10.2]

### Fixed
- [#105](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/105): abi: fix the conflict of PERFILE_DAX flag
- [#106](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/106): bugfix: passthrough: refect CFileHandle struct

## [0.10.1]

### Fixed
- [#102](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/102): passthrough: reduce the memory footprint of file handle
- [#103](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/103): vfs: correctly set attr.st_ino for loopup()

## [0.10.0]

### Added
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): async_runtime: add probe of io_uring support
- [#88](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/88): add ability to disallow operations that could change file size

### Fixed
- [#98](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/98): vfs: fix incorrect st_ino in entry.attr
- [#93](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/93): fix BIG_WRITES doesn't work

### Removed
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): async_runtime: remove thread_local of Runtime
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): remove temporarily tokio-uring module

### Changed
- [#97](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/97): log: print some variables in hexadecimal
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): async_runtime: improved async file implement
- [#95](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/95): open file with O_APPEND cleared when writeback is enabled
- [#90](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/90): open file for reading if writeback cache is enabled

### Upgraded
- virtio-queue from 0.4 to 0.6
- vhost from 0.4 to 0.5

## [0.9.6]
- Fix no_opendir option handling

## [0.9.5]

### Changed
- Update dependency
- Fix a bug in fusedev
- Add toio-uring/tokio based async io framework

## [0.9.2]

### Added

- [#77](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/77): Implement Sync for FileVolatileSlice

## [0.9.1]

### Fixed
- [#74](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/74): Fixed some issues about EINTR and EAGIN handled incorrectly

## [v0.4.0]
### Added
- MacOS support

### Changed
- linux_abi renamed to fuse_abi
- switch from epoll to mio for cross-platform support
- VFS umount no longer evicts pseudofs inodes
- virtiofs transport Reader/Writer takes generic typed memory argument

## [v0.3.0]
### Added
- Optionally enable MAX_PAGES feature
- Allow customizing the default FUSE features before creating a new vfs structure
- Support more FUSE server APIs

### Changed
- The FUSE server has no default FUSE feature set now. The default feature set is only
  defined in VfsOptions. Non VFS users have to define the default FUSE feature set in
  the init() method.

## [v0.2.0]
### Added
- Enhance passthrough to reduce active fds by using file handle
- implement From<fusedev::Error> for std::io::Error
- Use `vhost` crate from crates.io
- Introduce readlinkat_proc_file helper
- Update vm-memory to 0.7.0
- Add @eryugey to CODEOWNERS file

### Fixed
- Validate path components
- Prevent ".." escape in do_lookup in passthroughfs
- Prevent opening of special file in passthroughfs
- Fix compile error in vfs async test
- Record real root inode's ino of file system backends in vfs

### Deprecated 

## [v0.1.2]
- support KILLPRIV_v2
- enhance vfs to support DAX window map/unmap operations

## [v0.1.1]
- Set README.md file for crate
- Add CHANGELOG.md
