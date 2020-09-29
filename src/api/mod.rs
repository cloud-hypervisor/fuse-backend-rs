// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse Application Programming Interfaces(API).

#![allow(dead_code)]
mod pseudo_fs;
mod vfs;
mod vfs_persist;

pub use vfs::{BackendFileSystem, BackendFileSystemType, Vfs, VfsOptions, VFS_MAX_INO};
pub use vfs_persist::VfsState;
pub mod filesystem;
pub mod server;
