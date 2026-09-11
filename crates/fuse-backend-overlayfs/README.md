# fuse-backend-overlayfs

An **overlay** FUSE filesystem driver (Linux-only): it stacks multiple read-only
lower layers under a writable upper layer, presenting them as a single union
filesystem.

Built on [`fuse-backend-core`]. It is a driver only — pair it with a transport
([`fuse-backend-fusedev`] or [`fuse-backend-virtiofs`]), or use the umbrella
[`fuse-backend-rs`] crate, which bundles it with each transport.

## Cargo features

| Feature | Effect |
| --- | --- |
| `async-io` | Experimental asynchronous IO path. |

## Usage

```toml
[dependencies]
fuse-backend-overlayfs = { git = "https://github.com/cloud-hypervisor/fuse-backend-rs" }
```

Not published to crates.io yet — depend on the git repository for now.

## License

Apache-2.0 AND BSD-3-Clause, the same as the umbrella crate.

[`fuse-backend-core`]: ../fuse-backend-core
[`fuse-backend-fusedev`]: ../fuse-backend-fusedev
[`fuse-backend-virtiofs`]: ../fuse-backend-virtiofs
[`fuse-backend-rs`]: ../../README.md
