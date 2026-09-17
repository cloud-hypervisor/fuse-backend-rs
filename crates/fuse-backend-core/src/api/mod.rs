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
//!
//! The `Vfs` union file system that used to live here is now the separate
//! `fuse-backend-vfs` crate. The umbrella `fuse-backend-rs` crate re-exports it
//! at the historical `api::vfs`/`api::Vfs` paths; a consumer that brings its own
//! `FileSystem` can depend on `fuse-backend-core` alone and skip it (and its
//! `arc-swap` dependency).

pub mod filesystem;
pub mod server;

// The multiplexer-neutral path/inode helpers and the `BackendFileSystem` mount
// contract live in `filesystem` (their definition site) and are re-exported at
// the flat `api::*` paths, so filesystem drivers can use them without pulling in
// the `fuse-backend-vfs` union multiplexer.
pub use filesystem::{
    validate_path_component, BackFileSystem, BackendFileSystem, CURRENT_DIR_CSTR, EMPTY_CSTR,
    PARENT_DIR_CSTR, PROC_SELF_FD_CSTR, SLASH_ASCII, VFS_MAX_INO,
};
