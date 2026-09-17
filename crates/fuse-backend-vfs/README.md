# fuse-backend-vfs

A **union** FUSE filesystem multiplexer: it mounts several backend filesystems
under a single inode namespace, so a new backend can be mounted onto a
subdirectory at runtime instead of hot-adding another virtio-fs device. This is
convenient for managing container images at runtime.

Built on [`fuse-backend-core`]. `Vfs` implements both `FileSystem` and (with the
`async-io` feature) `AsyncFileSystem`, so it is a composite backend that pairs
with a transport ([`fuse-backend-fusedev`] or [`fuse-backend-virtiofs`]). It is
also bundled by the umbrella [`fuse-backend-rs`] crate, which always re-exports
it at the historical `fuse_backend_rs::api::{vfs, Vfs}` paths. A consumer that
brings its own `FileSystem` can depend on `fuse-backend-core` alone and skip
this crate (and its `arc-swap` dependency) entirely.

## Cargo features

| Feature | Effect |
| --- | --- |
| `async-io` | Experimental asynchronous serving path (`impl AsyncFileSystem for Vfs`). |
| `virtiofs` | DAX `setupmapping`/`removemapping` handlers for a virtio-fs device. |
| `persist` | Snapshot/restore of the mount table (`VfsState`/`PseudoFsState`). |

## Usage

```toml
[dependencies]
fuse-backend-vfs = { git = "https://github.com/cloud-hypervisor/fuse-backend-rs" }
```

Not published to crates.io yet — depend on the git repository for now.

## License

Apache-2.0 AND BSD-3-Clause, the same as the umbrella crate.

[`fuse-backend-core`]: ../fuse-backend-core
[`fuse-backend-fusedev`]: ../fuse-backend-fusedev
[`fuse-backend-virtiofs`]: ../fuse-backend-virtiofs
[`fuse-backend-rs`]: ../../README.md
