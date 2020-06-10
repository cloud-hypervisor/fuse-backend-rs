// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0

#![deny(missing_docs)]

//! A library to support Fuse server and virtio-fs device based on Linux Fuse ABI.
//!
//! Filesystem in Userspace ([FUSE]) is a software interface for Unix and Unix-like computer
//! operating systems that lets non-privileged users create their own file systems without
//! editing kernel code. This is achieved by running file system code in user space while
//! the FUSE module provides only a "bridge" to the actual kernel interfaces.
//!
//! On Linux, the FUSE device driver is a general purpose filesystem abstraction layer, which
//! loads as a kernel module and presents a virtual device (/dev/fuse) to communicate with
//! a user (non-kernel) program via a well defined API. The user code need not run with root
//! priviledge if it does not need to access protected data or devices, and can implement
//! a virtual filesystem much more simply than a traditional device driver.
//!
//! In addition to traditional Fuse filesystems, the [virtiofs] file system for Linux implements
//! a driver for the paravirtualized VIRTIO “virtio-fs” device for guest<->host file system
//! sharing. It allows a guest to mount a directory that has been exported on the host.
//!
//! Virtio-fs uses FUSE as the foundation. Unlike traditional FUSE where the file system daemon
//! runs in userspace, the virtio-fs daemon runs on the host. A VIRTIO device carries FUSE
//! messages and provides extensions for advanced features not available in traditional FUSE.
//! Since the virtio-fs device uses the FUSE protocol for file system requests, the virtiofs
//! file system for Linux is integrated closely with the FUSE file system client. The guest acts
//! as the FUSE client while the host acts as the FUSE server. The /dev/fuse interface between
//! the kernel and userspace is replaced with the virtio-fs device interface.
//!
//! These crate could be devided into several subsystems:
//! * Transport Layer. The transport layer receives Fuse requests from the clients and sends back
//!   replies. Currently there are two transport layers are supported: Linux Fuse device(/dev/fuse)
//!   and virtiofs.
//! * Filesystem Driver. Filesystem drivers implement the concrete Fuse filesystem logic, at what
//!   ever is suitable. A default "passthrough" filesystem driver is implemented as a sample.
//! * Fuse ABI. Currently only Linux Fuse ABIs since v7.27 are supported.
//! * Fuse API. The Fuse API is the connection between transport layers and file system drivers.
//!   It receives Fuse requests from transport layers, parses the request according to Fuse ABI,
//!   invokes filesystem drivers to server the requests, and eventually send back the result to
//!   the transport layer.
//!
//! [FUSE](https://www.kernel.org/doc/html/latest/filesystems/fuse.html)
//! [virtiofs](https://www.kernel.org/doc/html/latest/filesystems/virtiofs.html)

extern crate bitflags;
extern crate libc;
#[macro_use]
extern crate log;
#[cfg(feature = "vhost-user-fs")]
extern crate vhost_rs;
extern crate vm_memory;
#[cfg(feature = "virtiofs")]
extern crate vm_virtio;

use std::ffi::FromBytesWithNulError;
use std::{error, fmt, io};

/// Error codes for Fuse related operations.
#[derive(Debug)]
pub enum Error {
    /// Failed to decode protocol messages.
    DecodeMessage(io::Error),
    /// Failed to encode protocol messages.
    EncodeMessage(io::Error),
    /// One or more parameters are missing.
    MissingParameter,
    /// A C string parameter is invalid.
    InvalidCString(FromBytesWithNulError),
    /// The `len` field of the header is too small.
    InvalidHeaderLength,
    /// The `size` field of the `SetxattrIn` message does not match the length
    /// of the decoded value.
    InvalidXattrSize((u32, usize)),
    /// An IO related error has happened.
    IoError(io::Error),
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            DecodeMessage(err) => write!(f, "failed to decode fuse message: {}", err),
            EncodeMessage(err) => write!(f, "failed to encode fuse message: {}", err),
            MissingParameter => write!(f, "one or more parameters are missing"),
            InvalidHeaderLength => write!(f, "the `len` field of the header is too small"),
            InvalidCString(err) => write!(f, "a c string parameter is invalid: {}", err),
            InvalidXattrSize((size, len)) => write!(
                f,
                "The `size` field of the `SetxattrIn` message does not match the length of the\
                 decoded value: size = {}, value.len() = {}",
                size, len
            ),
            IoError(err) => write!(f, "fail to handle request: {}", err),
        }
    }
}

/// Result for Fuse related operations.
pub type Result<T> = ::std::result::Result<T, Error>;

pub mod abi;
pub mod api;
pub mod passthrough;
pub mod transport;
