# fuse-backend-fusedev

The **/dev/fuse** transport for FUSE servers: it mounts a filesystem through the
kernel FUSE device and serves requests over `FuseSession`/`FuseChannel`. It also
carries the experimental **FUSE-over-io_uring** transport (`uring`) and the
macOS **macFUSE / fuse-t** transports.

Built on [`fuse-backend-core`], which it enables with core's `fusedev` cfg. It
ships no filesystem driver of its own; the umbrella [`fuse-backend-rs`] crate
bundles it with the passthrough and overlayfs drivers.

## Cargo features

| Feature | Effect |
| --- | --- |
| `async-io` | Experimental asynchronous serving path (Linux-only). |
| `uring` | Experimental FUSE-over-io_uring transport (kernel >= 6.14, protocol 7.42); the kernel interface is still evolving. |
| `fuse-t` | On macOS, serve through [fuse-t](https://github.com/macos-fuse-t/fuse-t) instead of macFUSE. |

## Choosing a serving layer

A *serving layer* owns a mounted `FuseSession`, drives it with worker threads
and turns `Drop` into teardown: stop accepting new requests, finish the
in-flight ones, unmount the session and join the workers. Three
implementations share the `FuseServing` trait:

| Layer | Handlers | Transport | Feature |
| --- | --- | --- | --- |
| `SyncFuseServing` | `FileSystem` | classic `/dev/fuse` | always available |
| `AsyncFuseServing` | `AsyncFileSystem` | classic `/dev/fuse` | `async-io` (Linux) |
| `UringFuseServing` | `FileSystem` | FUSE-over-io_uring | `uring` (Linux) |

Three inputs drive the choice:

- **Kernel**: `UringFuseServing` needs Linux 6.14+ *and* the runtime fuse
  module parameter `enable_uring` turned on — a version check alone proves
  neither, so request the capability with `Server::set_uring(true)` before
  the INIT handshake, probe by constructing the serving layer and fall back
  on `Error::UringNotSupported`. Everywhere else, including macOS, the
  classic transport is the choice.
- **Workload**: on a uring-capable kernel, metadata-heavy workloads gain the
  most (3.7x file creation at 8 threads), while large sequential IO
  currently regresses on uring — a known upstream limitation analyzed in
  [fuse-uring-performance.md](../../docs/fuse-uring-performance.md) — so
  classic multi-worker serving stays the throughput choice there.
- **Backing storage**: with local storage, synchronous handlers
  (`FileSystem`) saturate with one worker per CPU. When every request hides
  a network round trip, asynchronous handlers (`AsyncFileSystem`) decouple
  the request concurrency from the worker count.

A daemon that picks its transport at runtime switches implementations behind
`Box<dyn FuseServing>`:

```text
// set_uring() arms the server; UringFuseServing::new() then performs the
// INIT handshake on the mounted session.
server.set_uring(true);
let serving: Box<dyn FuseServing> =
    match UringFuseServing::new(session, server.clone(), uring_cfg) {
        Ok(s) => Box::new(s),
        Err(Error::UringNotSupported) => {
            // The uring constructor tears the failed session down, so
            // remount before falling back to the classic transport.
            Box::new(SyncFuseServing::new(remount()?, server, sync_cfg)?)
        }
        Err(e) => return Err(e),
    };
// serving.wait() parks until the workers drain (e.g. an external umount);
// dropping `serving` tears the mount down.
```

The `serving` module documentation spells out the semantics every
implementation shares.

## Usage

```toml
[dependencies]
fuse-backend-fusedev = { git = "https://github.com/cloud-hypervisor/fuse-backend-rs" }
```

Not published to crates.io yet — depend on the git repository for now.

## License

Apache-2.0 AND BSD-3-Clause, the same as the umbrella crate.

[`fuse-backend-core`]: ../fuse-backend-core
[`fuse-backend-rs`]: ../../README.md
