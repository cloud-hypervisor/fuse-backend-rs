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
