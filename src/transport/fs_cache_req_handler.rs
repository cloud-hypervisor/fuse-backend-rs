// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0

#[cfg(not(feature = "virtiofs"))]
/// Fake trait to simplify implementation when vhost-user-fs is not used.
pub trait FsCacheReqHandler {}

#[cfg(feature = "virtiofs")]
pub use virtiofs::FsCacheReqHandler;

#[cfg(feature = "virtiofs")]
mod virtiofs {
    use std::io;
    use std::os::unix::io::RawFd;

    use crate::abi::virtio_fs::RemovemappingOne;

    /// Trait to support virtio-fs DAX Window operations.
    ///
    /// The virtio-fs DAX Window allows bypassing guest page cache and allows mapping host
    /// page cache directly in guest address space.
    ///
    /// When a page of file is needed, guest sends a request to map that page (in host page cache)
    /// in VMM address space. Inside guest this is a physical memory range controlled by virtiofs
    /// device. And guest directly maps this physical address range using DAX and hence getsi
    /// access to file data on host.
    ///
    /// This can speed up things considerably in many situations. Also this can result in
    /// substantial memory savings as file data does not have to be copied in guest and it is
    /// directly accessed from host page cache.
    pub trait FsCacheReqHandler: Send + Sync + 'static {
        /// Setup a dedicated mapping so that guest can access file data in DAX style.
        fn map(
            &mut self,
            foffset: u64,
            moffset: u64,
            len: u64,
            flags: u64,
            fd: RawFd,
        ) -> io::Result<()>;

        /// Remove those mappings that provide the access to file data.
        fn unmap(&mut self, requests: Vec<RemovemappingOne>) -> io::Result<()>;
    }
}
