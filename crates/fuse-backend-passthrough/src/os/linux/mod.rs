// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

// The Linux syscall seams, one module per layer: the statx/stat syscall
// layer, the mount-fd bookkeeping over /proc/self/mountinfo, and the file
// handle layer on top of it.

pub(crate) use super::os_compat;

pub(crate) mod file_handle;
pub(crate) mod mount_fd;
pub(crate) mod statx;
