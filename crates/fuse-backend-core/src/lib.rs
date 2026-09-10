// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0

#![deny(missing_docs)]
#![allow(unexpected_cfgs)]

//! Core support for FUSE(filesystem in userspace) servers and virtio-fs devices.
//!
//! Filesystem in Userspace [`FUSE`](https://www.kernel.org/doc/html/latest/filesystems/fuse.html)
//! is a software interface for Unix and Unix-like computer operating systems that lets
//! non-privileged users create their own file systems without editing kernel code.
//! This is achieved by running file system code in user space while the FUSE module provides
//! only a "bridge" to the actual kernel interfaces.
//!
//! This crate hosts the transport-neutral and driver-neutral layers of a FUSE backend:
//! * the [Fuse ABI](abi/index.html) data structures shared by all transports,
//! * the [Fuse API](api/index.html) layer, which receives Fuse requests from transport
//!   layers, parses the requests according to the Fuse ABI, invokes filesystem drivers
//!   to serve the requests, and eventually sends back replies,
//! * transport-neutral request/response [buffers](buffer/index.html),
//! * [common](common/index.html) utilities, including an experimental async IO runtime
//!   abstraction behind the `async-io` feature.
//!
//! Transports (Linux `/dev/fuse`, virtio-fs) and filesystem drivers (passthrough,
//! overlayfs) live in the umbrella `fuse-backend-rs` crate, which re-exports this
//! crate so the historical `fuse_backend_rs::{abi, api, buffer, common}` paths keep
//! resolving.

#[macro_use]
extern crate log;

use std::ffi::{CStr, FromBytesWithNulError};
use std::io::ErrorKind;
use std::{error, fmt, io};

use vm_memory::bitmap::BitmapSlice;

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
    /// Invalid message that the server cannot handle properly.
    InvalidMessage(io::Error),
    /// Failed to write buffer to writer.
    FailedToWrite(io::Error),
    /// Failed to split a writer.
    FailedToSplitWriter(buffer::Error),
    /// Failed to remap uid/gid.
    FailedToRemapID((u32, u32)),
}

impl error::Error for Error {}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            DecodeMessage(err) => write!(f, "failed to decode fuse message: {err}"),
            EncodeMessage(err) => write!(f, "failed to encode fuse message: {err}"),
            MissingParameter => write!(f, "one or more parameters are missing"),
            InvalidHeaderLength => write!(f, "the `len` field of the header is too small"),
            InvalidCString(err) => write!(f, "a c string parameter is invalid: {err}"),
            InvalidXattrSize((size, len)) => write!(
                f,
                "The `size` field of the `SetxattrIn` message does not match the length of the \
                 decoded value: size = {size}, value.len() = {len}"
            ),
            InvalidMessage(err) => write!(f, "cannot process fuse message: {err}"),
            FailedToWrite(err) => write!(f, "cannot write to buffer: {err}"),
            FailedToSplitWriter(err) => write!(f, "cannot split a writer: {err}"),
            FailedToRemapID((uid, gid)) => write!(
                f,
                "failed to remap the context of user (uid={uid}, gid={gid})."
            ),
        }
    }
}

/// Result for Fuse related operations.
pub type Result<T> = ::std::result::Result<T, Error>;

pub mod abi;
pub mod api;
pub mod buffer;

pub mod common;
pub use self::common::*;

/// Convert io::ErrorKind to OS error code.
/// Reference to libstd/sys/unix/mod.rs => decode_error_kind.
pub fn encode_io_error_kind(kind: ErrorKind) -> i32 {
    match kind {
        //ErrorKind::ConnectionRefused => libc::ECONNREFUSED,
        //ErrorKind::ConnectionReset => libc::ECONNRESET,
        ErrorKind::PermissionDenied => libc::EPERM | libc::EACCES,
        //ErrorKind::BrokenPipe => libc::EPIPE,
        //ErrorKind::NotConnected => libc::ENOTCONN,
        //ErrorKind::ConnectionAborted => libc::ECONNABORTED,
        //ErrorKind::AddrNotAvailable => libc::EADDRNOTAVAIL,
        //ErrorKind::AddrInUse => libc::EADDRINUSE,
        ErrorKind::NotFound => libc::ENOENT,
        ErrorKind::Interrupted => libc::EINTR,
        //ErrorKind::InvalidInput => libc::EINVAL,
        //ErrorKind::TimedOut => libc::ETIMEDOUT,
        ErrorKind::AlreadyExists => libc::EEXIST,
        ErrorKind::WouldBlock => libc::EWOULDBLOCK,
        _ => libc::EIO,
    }
}

/// trim all trailing nul terminators.
pub fn bytes_to_cstr(buf: &[u8]) -> Result<&CStr> {
    // There might be multiple 0s at the end of buf, find & use the first one and trim other zeros.
    match buf.iter().position(|x| *x == 0) {
        // Convert to a `CStr` so that we can drop the '\0' byte at the end and make sure
        // there are no interior '\0' bytes.
        Some(pos) => CStr::from_bytes_with_nul(&buf[0..=pos]).map_err(Error::InvalidCString),
        None => {
            // Invalid input, just call CStr::from_bytes_with_nul() for suitable error code
            CStr::from_bytes_with_nul(buf).map_err(Error::InvalidCString)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_bytes_to_cstr() {
        assert_eq!(
            bytes_to_cstr(&[0x1u8, 0x2u8, 0x0]).unwrap(),
            CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap()
        );
        assert_eq!(
            bytes_to_cstr(&[0x1u8, 0x2u8, 0x0, 0x0]).unwrap(),
            CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap()
        );
        assert_eq!(
            bytes_to_cstr(&[0x1u8, 0x2u8, 0x0, 0x1]).unwrap(),
            CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap()
        );
        assert_eq!(
            bytes_to_cstr(&[0x1u8, 0x2u8, 0x0, 0x0, 0x1]).unwrap(),
            CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap()
        );
        assert_eq!(
            bytes_to_cstr(&[0x1u8, 0x2u8, 0x0, 0x1, 0x0]).unwrap(),
            CStr::from_bytes_with_nul(&[0x1u8, 0x2u8, 0x0]).unwrap()
        );

        assert_eq!(
            bytes_to_cstr(&[0x0u8, 0x2u8, 0x0]).unwrap(),
            CStr::from_bytes_with_nul(&[0x0u8]).unwrap()
        );
        assert_eq!(
            bytes_to_cstr(&[0x0u8, 0x0]).unwrap(),
            CStr::from_bytes_with_nul(&[0x0u8]).unwrap()
        );
        assert_eq!(
            bytes_to_cstr(&[0x0u8]).unwrap(),
            CStr::from_bytes_with_nul(&[0x0u8]).unwrap()
        );

        bytes_to_cstr(&[0x1u8]).unwrap_err();
        bytes_to_cstr(&[0x1u8, 0x1]).unwrap_err();
    }

    #[test]
    fn test_encode_io_error_kind() {
        assert_eq!(encode_io_error_kind(ErrorKind::NotFound), libc::ENOENT);
        assert_eq!(encode_io_error_kind(ErrorKind::Interrupted), libc::EINTR);
        assert_eq!(encode_io_error_kind(ErrorKind::AlreadyExists), libc::EEXIST);
        assert_eq!(
            encode_io_error_kind(ErrorKind::WouldBlock),
            libc::EWOULDBLOCK
        );
        assert_eq!(encode_io_error_kind(ErrorKind::TimedOut), libc::EIO);
    }
}
