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
