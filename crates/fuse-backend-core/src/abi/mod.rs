// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse Application Binary Interfaces(ABI).

/// Linux Fuse Application Binary Interfaces.
#[cfg(target_os = "linux")]
#[path = "fuse_abi_linux.rs"]
pub mod fuse_abi;

/// MacOS Fuse Application Binary Interfaces.
#[cfg(target_os = "macos")]
#[path = "fuse_abi_macos.rs"]
pub mod fuse_abi;

#[cfg(feature = "virtiofs")]
pub mod virtio_fs;

/// Linux FUSE-over-io_uring ABI (experimental, kernel 6.14+, protocol 7.42).
#[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
pub mod fuse_uring;
