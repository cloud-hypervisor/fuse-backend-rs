// Copyright (C) 2022 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Some utilities to support fuse-backend-rs.

pub mod file_buf;
pub mod file_traits;

// Temporarily include all source code tokio-uring.
// Will switch to upstream once our enhancement have been merged and new version available.
#[cfg(all(feature = "async-io", target_os = "linux"))]
pub mod tokio_uring;
#[cfg(all(feature = "async-io", target_os = "linux"))]
pub(crate) use self::tokio_uring::{buf, driver, fs, future, BufResult};
