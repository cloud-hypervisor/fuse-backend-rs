# fuse-backend-core

The transport-neutral core of the fuse-backend-rs library: the FUSE **ABI**, the
**API/server** layer, the **VFS** multiplexer and pseudo-fs, the **buffer**
abstractions (`Reader`, `Writer`, `IoBuffers`) and the shared **common**
utilities. Every other crate in the workspace builds on this one; it contains no
transport and no filesystem driver.

Most applications want the umbrella [`fuse-backend-rs`] crate, which re-exports
this crate under the historical `fuse_backend_rs::{abi, api, buffer, common}`
paths. Depend on `fuse-backend-core` directly only when you need the core layers
without any transport or driver.

## Cargo features

| Feature | Effect |
| --- | --- |
| `async-io` | Experimental asynchronous IO path (tokio-uring / io_uring; Linux-only). |
| `persist` | Snapshot/restore of the VFS and pseudo-fs state (`versionize` + `dbs-snapshot`). |
| `fusedev`, `virtiofs`, `fusedev-uring`, `fuse-t` | Dependency-free cfg flags forwarded from the umbrella and transport crates so code historically gated on those names keeps compiling. Enable them through the transport crates, not directly. |

## Usage

```toml
[dependencies]
fuse-backend-core = { git = "https://github.com/cloud-hypervisor/fuse-backend-rs" }
```

Not published to crates.io yet — depend on the git repository for now.

## License

Apache-2.0 AND BSD-3-Clause, the same as the umbrella crate.

[`fuse-backend-rs`]: ../../README.md
