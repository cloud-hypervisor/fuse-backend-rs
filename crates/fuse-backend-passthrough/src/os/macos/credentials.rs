// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! macOS credential seams.
//!
//! macOS has neither the Linux capability model nor the supplementary-group
//! protocol behind `FUSE_EXT_GROUPS` (the macOS kernel never sends that
//! extension), so `set_creds()` is a no-op and `ScopedSuppGroups` never
//! adopts a group.

use std::io;

/// Adopt `(uid, gid)` for the duration of the caller's scope.
///
/// On Linux this temporarily switches the thread's fsuid/fsgid (and drops
/// `CAP_FSETID` when it would be silently cleared anyway), returning guards
/// that restore the original credentials on drop.  The macOS FUSE kernel
/// driver runs the daemon in the mounting user's context, so there is
/// nothing to switch: report the effective ids back and do nothing.
pub(crate) fn set_creds(
    uid: libc::uid_t,
    gid: libc::gid_t,
) -> io::Result<(libc::uid_t, libc::gid_t)> {
    let _ = (uid, gid);

    // Safe because neither call can fail and they do not modify any memory.
    Ok(unsafe { (libc::geteuid(), libc::getegid()) })
}

/// Guard replacing the thread's supplementary group list for the duration of
/// its scope.
///
/// The macOS kernel never sends the `FUSE_EXT_GROUPS` extension, so `new()`
/// never installs anything and always reports "no guard needed".
#[derive(Debug)]
pub(crate) struct ScopedSuppGroups;

impl ScopedSuppGroups {
    pub(crate) fn new(_supp_gid: Option<libc::gid_t>) -> io::Result<Option<Self>> {
        Ok(None)
    }
}

/// Guard for a dropped `CAP_FSETID`, mirroring the Linux twin's shape.
///
/// macOS has no capability model, so there is nothing to drop or restore;
/// the type only gives the shared `drop()` calls a guard with a `Drop` impl
/// to hold.
pub(crate) struct CapFsetid {}

impl Drop for CapFsetid {
    fn drop(&mut self) {
        // Nothing to restore on macOS.
    }
}

/// Drop `CAP_FSETID` while a size-changing write is in flight, so the kernel
/// does not silently clear the setuid/setgid bits.
///
/// macOS has no capability model, so there is nothing to drop.
pub(crate) fn drop_cap_fsetid() -> io::Result<Option<CapFsetid>> {
    Ok(None)
}
