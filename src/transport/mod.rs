// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
//
// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
//
// SPDX-License-Identifier: Apache-2.0 AND BSD-3-Clause

//! FUSE/Virtiofs transport drivers to receive requests from/send reply to Fuse/Virtiofs clients.
//!
//! Originally a FUSE server communicates with the FUSE driver through the device `/dev/fuse`,
//! and the communication protocol is called as FUSE protocol. Later the FUSE protocol is extended
//! to support Virtio-fs device. So there are two transport layers supported:
//! - fusedev: communicate with the FUSE driver through `/dev/fuse`
//! - virtiofs: communicate with the virtiofsd on host side by using virtio descriptors.

// Re-export the transport-neutral buffer types so that existing
// `transport::{pagesize, Error, Reader, Result, Writer}` paths keep
// resolving.
pub use crate::buffer::{pagesize, Error, Reader, Result, Writer};

#[cfg(feature = "fusedev")]
mod fusedev;
#[cfg(feature = "virtiofs")]
mod virtiofs;

#[cfg(all(target_os = "linux", feature = "fusedev"))]
pub use self::fusedev::BlockingFuseChannel;
#[cfg(all(target_os = "linux", feature = "fusedev", feature = "async-io"))]
pub use self::fusedev::FuseDevTask;
#[cfg(feature = "fusedev")]
pub use self::fusedev::{
    FuseBuf, FuseChannel, FuseChannelExt, FuseDevReaderExt, FuseDevWriter, FuseSession,
    FuseSessionExt,
};
#[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
pub use self::fusedev::{UringConfig, UringFuseServing, UringWriter};
#[cfg(feature = "virtiofs")]
pub use self::virtiofs::{VirtioFsReaderExt, VirtioFsWriter};

// The trait lives with the `FileSystem` contract that consumes it; re-export
// so the historical `transport::FsCacheReqHandler` path keeps resolving.
pub use crate::api::filesystem::FsCacheReqHandler;
