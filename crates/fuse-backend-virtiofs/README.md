# fuse-backend-virtiofs

The **virtio-fs** transport for FUSE servers: it carries FUSE requests and
replies over virtio descriptor chains, so a guest kernel can mount a filesystem
served on the host. This is the transport behind a vhost-user-fs device.

Built on [`fuse-backend-core`], which it enables with core's `virtiofs` cfg. It
ships no filesystem driver of its own; the umbrella [`fuse-backend-rs`] crate
bundles it with the passthrough and overlayfs drivers.

## Cargo features

| Feature | Effect |
| --- | --- |
| `async-io` | Experimental asynchronous serving path. |

## Usage

```toml
[dependencies]
fuse-backend-virtiofs = { git = "https://github.com/cloud-hypervisor/fuse-backend-rs" }
```

Not published to crates.io yet — depend on the git repository for now.

## License

Apache-2.0 AND BSD-3-Clause, the same as the umbrella crate.

[`fuse-backend-core`]: ../fuse-backend-core
[`fuse-backend-rs`]: ../../README.md
