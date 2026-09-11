// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0

#![deny(missing_docs)]
#![allow(unexpected_cfgs)]

//! A rust library for Fuse(filesystem in userspace) servers and virtio-fs devices.
//!
//! Filesystem in Userspace [`FUSE`](https://www.kernel.org/doc/html/latest/filesystems/fuse.html)
//! is a software interface for Unix and Unix-like computer operating systems that lets
//! non-privileged users create their own file systems without editing kernel code.
//! This is achieved by running file system code in user space while the FUSE module provides
//! only a "bridge" to the actual kernel interfaces.
//!
//! On Linux, the FUSE device driver is a general purpose filesystem abstraction layer, which
//! loads as a kernel module and presents a virtual device (/dev/fuse) to communicate with
//! a user (non-kernel) program via a well defined API. The user code need not run with root
//! priviledge if it does not need to access protected data or devices, and can implement
//! a virtual filesystem much more simply than a traditional device driver.
//!
//! In addition to traditional Fuse filesystems, the
//! [virtiofs](https://www.kernel.org/doc/html/latest/filesystems/virtiofs.html)
//! file system for Linux implements a driver for the paravirtualized VIRTIO “virtio-fs” device
//! for guest<->host file system sharing. It allows a guest to mount a directory that has
//! been exported on the host.
//!
//! Virtio-fs uses FUSE as the foundation. Unlike traditional FUSE where the file system daemon
//! runs in userspace, the virtio-fs daemon runs on the host. A VIRTIO device carries FUSE
//! messages and provides extensions for advanced features not available in traditional FUSE.
//! Since the virtio-fs device uses the FUSE protocol for file system requests, the virtiofs
//! file system for Linux is integrated closely with the FUSE file system client. The guest acts
//! as the FUSE client while the host acts as the FUSE server. The /dev/fuse interface between
//! the kernel and userspace is replaced with the virtio-fs device interface.
//!
//! The fuse-backend-rs crate includes several subsystems:
//! * [Fuse API](api/index.html). The Fuse API is the connection between transport layers and file
//!   system drivers. It receives Fuse requests from transport layers, parses the request
//!   according to Fuse ABI, invokes filesystem drivers to server the requests, and eventually
//!   send back the result to the transport layer.
//! * [Fuse ABI](abi/index.html). Currently only Linux Fuse ABIs since v7.27 are supported.
//! * [Transport Layer](transport/index.html). The transport layer receives Fuse requests from
//!   the clients and sends back replies. Currently there are two transport layers are supported:
//!   Linux Fuse device(/dev/fuse) and virtiofs.
//! * Filesystem Drivers. Filesystem drivers implement the concrete Fuse filesystem logic,
//!   at what ever is suitable. A default ["passthrough"](passthrough/index.html) filesystem
//!   driver is implemented as a sample.
//! * Async IO (Experimental). An optional `async-io` cargo feature adds an asynchronous IO
//!   path based on tokio-uring/io_uring, which is only available on Linux and may change
//!   in future releases.
//!
//! The transport-neutral layers (ABI, API, buffers, common utilities) are
//! implemented by the [`fuse-backend-core`] crate, the transports by the
//! [`fuse-backend-fusedev`] and [`fuse-backend-virtiofs`] crates, and the
//! filesystem drivers by the [`fuse-backend-passthrough`] and
//! [`fuse-backend-overlayfs`] crates. They are all re-exported here, so every
//! historical `fuse_backend_rs::{abi, api, buffer, common, transport,
//! passthrough, overlayfs}` path keeps resolving.
//!
//! The historical cargo feature names keep working too: `fusedev`,
//! `virtiofs`, `vhost-user-fs`, `async-io`, `persist`, `fuse-t` and
//! `fusedev-uring` are forwarded onto the sub-crates, and each transport
//! still bundles the drivers it has always shipped with. The additional
//! `passthrough` and `overlayfs` features select a driver on its own,
//! without any transport.

pub use fuse_backend_core::{abi, api, buffer, common};

pub use fuse_backend_core::{bytes_to_cstr, encode_io_error_kind, Error, Result};

pub use self::common::*;

// The drivers are Linux-only, exactly like the in-crate modules they replace.
// They are bundled with the `fusedev`/`virtiofs` transports and can also be
// selected on their own via the `passthrough`/`overlayfs` features.
#[cfg(all(
    any(feature = "fusedev", feature = "virtiofs", feature = "overlayfs"),
    target_os = "linux"
))]
pub use fuse_backend_overlayfs as overlayfs;
#[cfg(all(
    any(feature = "fusedev", feature = "virtiofs", feature = "passthrough"),
    target_os = "linux"
))]
pub use fuse_backend_passthrough as passthrough;
pub mod transport;
