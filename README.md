# Fuse-rs

## Design

The Fuse-rs crate is an rust library to implement Fuse daemons based on the
[Linux FUSE device (/dev/fuse)](https://www.kernel.org/doc/html/latest/filesystems/fuse.html)
or the [virtiofs](https://stefanha.github.io/virtio/virtio-fs.html#x1-41500011) draft specification.

Linux FUSE is an userspace filesystem framework, and the /dev/fuse device node is the interface for
userspace filesystem daemons to communicate with the in-kernel fuse driver.

And the virito-fs specification extends the FUSE framework into the virtualization world, which uses
the Virtio protocol to transfer FUSE requests and responses between the Fuse client and server.
With virtio-fs, the Fuse client runs within the guest kernel and the Fuse server runs on the host
userspace or hardware.

So the fuse-rs crate is a library to communicate with the Linux FUSE clients, which includes:
- ABI layer, which defines all data structures shared between linux Fuse framework and Fuse daemons.
- API layer, defines the interfaces for Fuse daemons to implement a userspace file system.
- Transport layer, which supports both the Linux Fuse device and virtio-fs protocol.
- VFS/pseudo_fs, an abstraction layer to support multiple file systems by a single virtio-fs device.
- A sample passthrough file system implementation, which passes through files from daemons to clients. 

## Usage

TODO: This section describes how the crate is used.

## Examples

TODO: Usage examples.

```rust
use fuse_rs;

...
```

## License
The crate reuses source code from the [Cloud Hypervisor](https://github.com/cloud-hypervisor/cloud-hypervisor) project
and [Crosvm](https://chromium.googlesource.com/chromiumos/platform/crosvm/) project.

This project is licensed under either of
- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
