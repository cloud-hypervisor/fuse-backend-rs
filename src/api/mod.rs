// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse Application Programming Interfaces(API).
//!
//! The Fuse application programming interfaces(API) layer is an intermediate layer
//! between the transport layer and the backend file system drivers. It provides:
//! - [struct Server](server/struct.Server.html) to receive requests from/send reply to the
//!   transport layer.
//! - [trait FileSystem](filesystem/trait.FileSystem.html) for backend file system drivers to
//!   implement fs operations.
//! - [struct Vfs](vfs/struct.Vfs.html), a simple union file system to help organize multiple
//!   backend file systems.

pub use super::abi::linux_abi::CreateIn;

mod pseudo_fs;

pub mod vfs;
pub use vfs::{BackendFileSystem, Vfs, VfsOptions, VFS_MAX_INO};

pub mod filesystem;
pub mod server;
