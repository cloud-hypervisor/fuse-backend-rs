// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse lowlevel passthrough implementation.

mod fs;
mod multikey;

pub use fs::{CachePolicy, Config, PassthroughFs};
