// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by the Apache License, Version 2.0
// that can be found in the LICENSE files.

// The Linux syscall seams, one module per layer: the statx/stat syscall
// layer, the mount-fd bookkeeping over /proc/self/mountinfo, the file
// handle layer on top of it, the getdents64 directory walk, the thin
// fd-taking file-operation shims, and the credential switching.

pub(crate) use self::compat as os_compat;

pub(crate) mod credentials;
pub(crate) mod dir;
pub(crate) mod file_handle;
pub(crate) mod fsops;
pub(crate) mod kernel_passthrough;
pub(crate) mod mount_fd;
pub(crate) mod statx;

// The Linux arm of the libc vocabulary shared by the seams and by the
// OS-neutral code: re-exports of the libc spellings, plus the musl shims
// for `struct statx`, which the libc crate doesn't provide there. The
// macOS twin lives in os/macos/mod.rs; os/mod.rs aliases whichever arm
// is active as `os_compat`, so the shared code sees one name.
pub(crate) mod compat {
    /// Open a path for metadata purposes only, without read/write permission.
    pub const O_PATH: libc::c_int = libc::O_PATH;

    /// Request direct (page-cache-bypassing) I/O on an open file.
    pub const O_DIRECT: libc::c_int = libc::O_DIRECT;

    // `fallocate()` mode flags. These arrive in the FUSE FALLOCATE request
    // from the guest kernel, so they are wire-protocol values rather than
    // host syscalls and must parse identically on every platform. The Linux
    // arm just re-exports the libc spellings to keep behavior byte-identical.
    pub use libc::{
        FALLOC_FL_COLLAPSE_RANGE, FALLOC_FL_INSERT_RANGE, FALLOC_FL_KEEP_SIZE,
        FALLOC_FL_PUNCH_HOLE, FALLOC_FL_UNSHARE_RANGE, FALLOC_FL_ZERO_RANGE,
    };

    // File type bits, normalized to `u32`. The re-exports mirror the macOS
    // arm's widened constants; the types beyond S_IFMT/S_IFREG/S_IFDIR are
    // consumed by the portable `util` tests only (so far), hence the
    // test-aware allow.
    #[cfg_attr(not(test), allow(unused_imports))]
    pub use libc::{S_IFBLK, S_IFCHR, S_IFDIR, S_IFIFO, S_IFLNK, S_IFMT, S_IFREG, S_IFSOCK};

    /// Widen an `st_mode` value to the shared `u32` representation.
    ///
    /// Linux's `mode_t` is `u32` already, so this is the identity.
    #[inline]
    pub fn st_mode_u32(mode: libc::mode_t) -> u32 {
        mode
    }

    #[cfg(target_env = "gnu")]
    pub use libc::statx as statx_st;

    #[cfg(target_env = "gnu")]
    pub use libc::{STATX_BASIC_STATS, STATX_MNT_ID};

    // musl provides the 'struct statx', but without stx_mnt_id.
    // However, the libc crate does not provide libc::statx
    // if musl is used. So we add just the required struct and
    // constants to make it works.
    #[cfg(not(target_env = "gnu"))]
    #[repr(C)]
    pub struct statx_st_timestamp {
        pub tv_sec: i64,
        pub tv_nsec: u32,
        pub __statx_timestamp_pad1: [i32; 1],
    }

    #[cfg(not(target_env = "gnu"))]
    #[repr(C)]
    pub struct statx_st {
        pub stx_mask: u32,
        pub stx_blksize: u32,
        pub stx_attributes: u64,
        pub stx_nlink: u32,
        pub stx_uid: u32,
        pub stx_gid: u32,
        pub stx_mode: u16,
        __statx_pad1: [u16; 1],
        pub stx_ino: u64,
        pub stx_size: u64,
        pub stx_blocks: u64,
        pub stx_attributes_mask: u64,
        pub stx_atime: statx_st_timestamp,
        pub stx_btime: statx_st_timestamp,
        pub stx_ctime: statx_st_timestamp,
        pub stx_mtime: statx_st_timestamp,
        pub stx_rdev_major: u32,
        pub stx_rdev_minor: u32,
        pub stx_dev_major: u32,
        pub stx_dev_minor: u32,
        pub stx_mnt_id: u64,
        __statx_pad2: u64,
        __statx_pad3: [u64; 12],
    }

    #[cfg(not(target_env = "gnu"))]
    pub const STATX_BASIC_STATS: libc::c_uint = 0x07ff;

    #[cfg(not(target_env = "gnu"))]
    pub const STATX_MNT_ID: libc::c_uint = 0x1000;
}
