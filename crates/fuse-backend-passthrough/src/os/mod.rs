// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

// The per-OS syscall seams of the passthrough driver. Each OS subtree
// (linux/, macos/) provides the same modules under the same names; the
// re-exports below keep the bare historical names (`statx`, `file_handle`,
// ...) valid at the crate root, so the rest of the crate needs no cfg.

pub(crate) mod compat;

// OS-independent shims shared by the per-OS seam modules: constants and
// types whose libc definitions differ between platforms or don't exist
// everywhere (`O_PATH`, `O_DIRECT`, the `FALLOC_FL_*` flags, ...).
pub(crate) use self::compat as os_compat;

#[cfg(target_os = "linux")]
pub(crate) mod linux;
#[cfg(target_os = "linux")]
pub(crate) use self::linux::{file_handle, mount_fd, statx};
