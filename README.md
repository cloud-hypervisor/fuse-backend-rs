# Fuse-backend-rs

## Design

The fuse-backend-rs crate is an rust library to implement Fuse daemons based on the
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

Please refer to [dragonflyoss/image-service](https://github.com/dragonflyoss/image-service/blob/master/src/bin/nydusd/fusedev.rs)
for an example to use the fusedev framework.

## Examples

```rust
use fuse_backend_rs::api::{server::Server, Vfs, VfsOptions};
use fuse_backend_rs::transport::fusedev::{FuseSession, FuseChannel};

struct FuseServer {
    server: Arc<Server<Arc<Vfs>>>,
    ch: FuseChannel,
}

impl FuseServer {
    fn svc_loop(&self) -> Result<()> {
        let mut buf = vec![0x0u8; 1024 * 1024];

        // Given error EBADF, it means kernel has shut down this session.
        let _ebadf = std::io::Error::from_raw_os_error(libc::EBADF);
        loop {
            if let Some(reader) = self
                .ch
                .get_reader(&mut buf)
                .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?
            {
                let writer = self
                    .ch
                    .get_writer()
                    .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?;
                if let Err(e) = self.server.handle_message(reader, writer, None, None) {
                    match e {
                        fuse_backend_rs::Error::EncodeMessage(_ebadf) => {
                            break;
                        }
                        _ => {
                            error!("Handling fuse message failed");
                            continue;
                        }
                    }
                }
            } else {
                info!("fuse server exits");
                break;
            }
        }
        Ok(())
    }
}
```

## License
The crate reuses source code from the [Cloud Hypervisor](https://github.com/cloud-hypervisor/cloud-hypervisor) project
and [Crosvm](https://chromium.googlesource.com/chromiumos/platform/crosvm/) project.

This project is licensed under either of
- [Apache License](http://www.apache.org/licenses/LICENSE-2.0), Version 2.0
- [BSD-3-Clause License](https://opensource.org/licenses/BSD-3-Clause)
