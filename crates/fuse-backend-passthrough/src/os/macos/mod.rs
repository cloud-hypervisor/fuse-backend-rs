// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

// The macOS twins of the Linux syscall seams, one module per layer.
// They are honest stubs: the types are real, so the shared code
// compiles, but the operations with no macOS equivalent answer ENOSYS
// (see the individual modules); filling in real implementations is
// future work.

pub(crate) use self::compat as os_compat;

pub(crate) mod credentials;
pub(crate) mod dir;
pub(crate) mod file_handle;
pub(crate) mod fsops;
pub(crate) mod kernel_passthrough;
pub(crate) mod mount_fd;
pub(crate) mod statx;

// The macOS arm of the libc vocabulary shared by the seams and by the
// OS-neutral code: the closest macOS equivalents of the Linux-only
// constants, spelled out with their divergences. The Linux twin lives in
// os/linux/mod.rs; os/mod.rs aliases whichever arm is active as
// `os_compat`, so the shared code sees one name.
pub(crate) mod compat {
    /// Open a path for metadata purposes only, without read/write permission.
    ///
    /// macOS's closest equivalent of Linux's `O_PATH` is `O_EVTONLY` (an fd
    /// usable for stat and kqueue, but not for I/O).
    pub const O_PATH: libc::c_int = libc::O_EVTONLY;

    /// Request direct (page-cache-bypassing) I/O on an open file.
    ///
    /// macOS has no `open()` flag equivalent (the analog is the
    /// `F_NOCACHE`/`F_GLOBAL_NOCACHE` `fcntl`s), so the flag-poking code paths
    /// compile with 0 and behave as if the guest never requested direct I/O.
    pub const O_DIRECT: libc::c_int = 0;

    // `fallocate()` mode flags. These arrive in the FUSE FALLOCATE request
    // from the guest kernel, so they are wire-protocol values rather than
    // host syscalls and must parse identically on every platform. macOS has
    // no `fallocate()` to forward them to (the seam answers `ENOSYS`), but
    // the shared `seal_size_check()` logic still matches on them; the
    // values come from Linux's `<linux/falloc.h>`.
    pub const FALLOC_FL_KEEP_SIZE: libc::c_int = 0x01;
    pub const FALLOC_FL_PUNCH_HOLE: libc::c_int = 0x02;
    pub const FALLOC_FL_COLLAPSE_RANGE: libc::c_int = 0x08;
    pub const FALLOC_FL_ZERO_RANGE: libc::c_int = 0x10;
    pub const FALLOC_FL_INSERT_RANGE: libc::c_int = 0x20;
    pub const FALLOC_FL_UNSHARE_RANGE: libc::c_int = 0x40;

    // File type bits, normalized to `u32`. macOS's `mode_t` (and hence
    // libc's `S_IF*` constants) is `u16` and `st_mode` comes out of
    // `stat()` as `u16`; shared code standardizes on the wider `u32`, and
    // the seams widen where the narrow type leaks in. The types beyond
    // S_IFMT/S_IFREG/S_IFDIR are consumed by the portable `util` tests
    // only (so far), hence the test-aware allows.
    pub const S_IFMT: u32 = libc::S_IFMT as u32;
    pub const S_IFREG: u32 = libc::S_IFREG as u32;
    pub const S_IFDIR: u32 = libc::S_IFDIR as u32;
    #[cfg_attr(not(test), allow(dead_code))]
    pub const S_IFBLK: u32 = libc::S_IFBLK as u32;
    #[cfg_attr(not(test), allow(dead_code))]
    pub const S_IFCHR: u32 = libc::S_IFCHR as u32;
    #[cfg_attr(not(test), allow(dead_code))]
    pub const S_IFIFO: u32 = libc::S_IFIFO as u32;
    #[cfg_attr(not(test), allow(dead_code))]
    pub const S_IFLNK: u32 = libc::S_IFLNK as u32;
    #[cfg_attr(not(test), allow(dead_code))]
    pub const S_IFSOCK: u32 = libc::S_IFSOCK as u32;

    /// Widen an `st_mode` value to the shared `u32` representation.
    ///
    /// macOS's `mode_t` is `u16`, and `stat()` reports `st_mode` as `u16`.
    #[inline]
    pub fn st_mode_u32(mode: libc::mode_t) -> u32 {
        u32::from(mode)
    }
}
