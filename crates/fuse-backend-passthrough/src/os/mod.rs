// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

// The per-OS syscall seams of the passthrough driver. Each OS subtree
// (linux/, macos/) provides the same modules under the same names, and
// each mod.rs carries its OS's arm of the libc vocabulary (its `compat`
// module). The re-exports below keep the bare historical names (`statx`,
// `file_handle`, `os_compat`, ...) valid at the crate root, so the rest
// of the crate needs no cfg.

use vm_memory::ByteValued;

/// The on-wire `getdents64` directory-entry header, shared by the per-OS
/// directory walks that parse the buffer the kernel filled.
#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct LinuxDirent64 {
    pub d_ino: u64,
    pub d_off: i64,
    pub d_reclen: libc::c_ushort,
    pub d_ty: libc::c_uchar,
}
unsafe impl ByteValued for LinuxDirent64 {}

#[cfg(target_os = "linux")]
pub(crate) mod linux;
#[cfg(target_os = "linux")]
pub(crate) use self::linux::compat as os_compat;
#[cfg(target_os = "linux")]
pub(crate) use self::linux::{
    credentials::{drop_cap_fsetid, set_creds, ScopedSuppGroups},
    dir, file_handle, fsops, mount_fd, statx,
};

#[cfg(target_os = "macos")]
pub(crate) mod macos;
#[cfg(target_os = "macos")]
pub(crate) use self::macos::compat as os_compat;
#[cfg(target_os = "macos")]
pub(crate) use self::macos::{
    credentials::{drop_cap_fsetid, set_creds, ScopedSuppGroups},
    dir, file_handle, fsops, mount_fd, statx,
};
