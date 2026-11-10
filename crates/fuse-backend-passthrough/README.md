# fuse-backend-passthrough

A **passthrough** FUSE filesystem driver: it forwards FUSE requests
to the host filesystem, passing files through from the daemon to the client. It
is the sample/reference driver shipped with the library.

Built on [`fuse-backend-core`]. It is a driver only — pair it with a transport
([`fuse-backend-fusedev`] or [`fuse-backend-virtiofs`]), or use the umbrella
[`fuse-backend-rs`] crate, which bundles it with each transport.

## Platform support

Linux is fully supported. The crate also compiles on macOS, but the macOS
support is a stub for now: the unported operations answer `ENOSYS`, so a
macOS mount fails cleanly instead of half-working. Filling in the macOS
implementations is future work.

## Cargo features

| Feature | Effect |
| --- | --- |
| `async-io` | Experimental asynchronous IO path. The async handlers currently relay to their synchronous counterparts, so blocking syscalls run on the async runtime. Linux-only: it builds on `preadv2`/`RWF_NOWAIT` and io_uring. |
| `virtiofs` | Compile the DAX-window callbacks (`setupmapping`/`removemapping`) that operate on core's virtio-fs ABI types. Forwarded from the umbrella crate. |

## Usage

```toml
[dependencies]
fuse-backend-passthrough = { git = "https://github.com/cloud-hypervisor/fuse-backend-rs" }
```

Not published to crates.io yet — depend on the git repository for now.

## License

Apache-2.0 AND BSD-3-Clause, the same as the umbrella crate.

[`fuse-backend-core`]: ../fuse-backend-core
[`fuse-backend-fusedev`]: ../fuse-backend-fusedev
[`fuse-backend-virtiofs`]: ../fuse-backend-virtiofs
[`fuse-backend-rs`]: ../../README.md
