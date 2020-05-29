// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse Application Binary Interfaces(ABI).

#[cfg(target_os = "linux")]
/// Linux Fuse Application Binary Interfaces.
pub mod linux_abi;

#[cfg(feature = "virtiofs")]
pub mod virtio_fs;
