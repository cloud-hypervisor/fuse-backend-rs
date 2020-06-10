// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse Application Programming Interfaces(API).

mod pseudo_fs;
mod vfs;

pub use vfs::{BackendFileSystem, Vfs, VfsOptions, VFS_MAX_INO};
pub mod filesystem;
pub mod server;
