// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! MacOS Fuse Application Binary Interfaces, Version 7.31.

#![allow(missing_docs)]

use std::fmt::{Debug, Formatter};
use std::mem;

use bitflags::bitflags;
use vm_memory::ByteValued;

pub use libc::{
    blksize_t, dev_t, ino_t as ino64_t, mode_t, nlink_t, off_t as off64_t, pread as pread64,
    preadv as preadv64, pwrite as pwrite64, pwritev as pwritev64, stat as stat64,
    statvfs as statvfs64,
};

/// Version number of this interface.
pub const KERNEL_VERSION: u32 = 7;

/// Minor version number of this interface.
pub const KERNEL_MINOR_VERSION: u32 = 19;

/// Init reply size is FUSE_COMPAT_INIT_OUT_SIZE
pub const KERNEL_MINOR_VERSION_INIT_OUT_SIZE: u32 = 5;

/// Init reply size is FUSE_COMPAT_22_INIT_OUT_SIZE
pub const KERNEL_MINOR_VERSION_INIT_22_OUT_SIZE: u32 = 23;

/// Lookup negative dentry using inode number 0
pub const KERNEL_MINOR_VERSION_LOOKUP_NEGATIVE_ENTRY_ZERO: u32 = 4;

/// The ID of the inode corresponding to the root directory of the file system.
pub const ROOT_ID: u64 = 1;

// Bitmasks for `fuse_setattr_in.valid`.
const FATTR_MODE: u32 = 0x1;
const FATTR_UID: u32 = 0x2;
const FATTR_GID: u32 = 0x4;
const FATTR_SIZE: u32 = 0x8;
const FATTR_ATIME: u32 = 0x10;
const FATTR_MTIME: u32 = 0x20;
pub const FATTR_FH: u32 = 0x40;
const FATTR_ATIME_NOW: u32 = 0x80;
const FATTR_MTIME_NOW: u32 = 0x100;
pub const FATTR_LOCKOWNER: u32 = 0x200;
pub const FATTR_CRTIME: u32 = 1 << 28;
pub const FATTR_CHGTIME: u32 = 1 << 29;
pub const FATTR_BKUPTIME: u32 = 1 << 30;
pub const FATTR_FLAGS: u32 = 1 << 31;

bitflags! {
    pub struct SetattrValid: u32 {
        const MODE = FATTR_MODE;
        const UID = FATTR_UID;
        const GID = FATTR_GID;
        const SIZE = FATTR_SIZE;
        const ATIME = FATTR_ATIME;
        const MTIME = FATTR_MTIME;
        const ATIME_NOW = FATTR_ATIME_NOW;
        const MTIME_NOW = FATTR_MTIME_NOW;
        const CRTIME = FATTR_CRTIME;
        const CHGTIME = FATTR_CHGTIME;
        const BKUPTIME = FATTR_BKUPTIME;
        const FLAGS = FATTR_FLAGS;
    }
}

// Flags use by the OPEN request/reply.

/// Kill suid and sgid if executable
pub const FOPEN_IN_KILL_SUIDGID: u32 = 1;

/// Bypass page cache for this open file.
const FOPEN_DIRECT_IO: u32 = 1;

/// Don't invalidate the data cache on open.
const FOPEN_KEEP_CACHE: u32 = 2;

/// The file is not seekable.
const FOPEN_NONSEEKABLE: u32 = 4;

const FOPEN_PURGE_ATTR: u32 = 1 << 30;

const FOPEN_PURGE_UBC: u32 = 1 << 31;

bitflags! {
    /// Options controlling the behavior of files opened by the server in response
    /// to an open or create request.
    pub struct OpenOptions: u32 {
        /// Bypass page cache for this open file.
        const DIRECT_IO = FOPEN_DIRECT_IO;
        /// Don't invalidate the data cache on open.
        const KEEP_CACHE = FOPEN_KEEP_CACHE;
        /// The file is not seekable.
        const NONSEEKABLE = FOPEN_NONSEEKABLE;

        const PURGE_ATTR = FOPEN_PURGE_ATTR;

        const PURGE_UBC = FOPEN_PURGE_UBC;
    }
}

// INIT request/reply flags.

/// Asynchronous read requests.
const ASYNC_READ: u64 = 0x1;

/// Remote locking for POSIX file locks.
const POSIX_LOCKS: u64 = 0x2;

/// Kernel sends file handle for fstat, etc... (not yet supported).
const FILE_OPS: u64 = 0x4;

/// Handles the O_TRUNC open flag in the filesystem.
const ATOMIC_O_TRUNC: u64 = 0x8;

/// FileSystem handles lookups of "." and "..".
const EXPORT_SUPPORT: u64 = 0x10;

/// FileSystem can handle write size larger than 4kB.
const BIG_WRITES: u64 = 0x20;

/// Don't apply umask to file mode on create operations.
const DONT_MASK: u64 = 0x40;

/// Remote locking for BSD style file locks.
const FLOCK_LOCKS: u64 = 0x400;

const RENAME_SWAP: u64 = 1 << 25;
const RENAME_EXCL: u64 = 1 << 26;
const ALLOCATE: u64 = 1 << 27;
const EXCHANGE_DATA: u64 = 1 << 28;
const CASE_INSENSITIVE: u64 = 1 << 29;
const VOL_RENAME: u64 = 1 << 30;
const XTIMES: u64 = 1 << 31;

/**
 *
 * fuse_attr flags
 *
 * upstream kernel use (1 << 0) as FUSE_ATTR_SUBMOUNT,
 * so FUSE_ATTR_DAX will use (1 << 1)
 *
 */
/// This attribute indicates whether the file supports dax in per-file DAX mode
pub const FUSE_ATTR_DAX: u32 = 1 << 1;

bitflags! {
    /// A bitfield passed in as a parameter to and returned from the `init` method of the
    /// `FileSystem` trait.
    pub struct FsOptions: u64 {
        /// Indicates that the filesystem supports asynchronous read requests.
        ///
        /// If this capability is not requested/available, the kernel will ensure that there is at
        /// most one pending read request per file-handle at any time, and will attempt to order
        /// read requests by increasing offset.
        ///
        /// This feature is enabled by default when supported by the kernel.
        const ASYNC_READ = ASYNC_READ;

        /// Indicates that the filesystem supports "remote" locking.
        ///
        /// This feature is not enabled by default and should only be set if the filesystem
        /// implements the `getlk` and `setlk` methods of the `FileSystem` trait.
        const POSIX_LOCKS = POSIX_LOCKS;

        /// Kernel sends file handle for fstat, etc... (not yet supported).
        const FILE_OPS = FILE_OPS;

        /// Indicates that the filesystem supports the `O_TRUNC` open flag. If disabled, and an
        /// application specifies `O_TRUNC`, fuse first calls `setattr` to truncate the file and
        /// then calls `open` with `O_TRUNC` filtered out.
        ///
        /// This feature is enabled by default when supported by the kernel.
        const ATOMIC_O_TRUNC = ATOMIC_O_TRUNC;

        /// Indicates that the filesystem supports lookups of "." and "..".
        ///
        /// This feature is disabled by default.
        const EXPORT_SUPPORT = EXPORT_SUPPORT;

        /// FileSystem can handle write size larger than 4kB.
        const BIG_WRITES = BIG_WRITES;

        /// Indicates that the kernel should not apply the umask to the file mode on create
        /// operations.
        ///
        /// This feature is disabled by default.
        const DONT_MASK = DONT_MASK;

        /// If set, then calls to `flock` will be emulated using POSIX locks and must
        /// then be handled by the filesystem's `setlock()` handler.
        ///
        /// If not set, `flock` calls will be handled by the FUSE kernel module internally (so any
        /// access that does not go through the kernel cannot be taken into account).
        ///
        /// This feature is disabled by default.
        const FLOCK_LOCKS = FLOCK_LOCKS;

        const RENAME_SWAP = RENAME_SWAP;
        const RENAME_EXCL = RENAME_EXCL;
        const ALLOCATE = ALLOCATE;
        const EXCHANGE_DATA = EXCHANGE_DATA;
        const CASE_INSENSITIVE = CASE_INSENSITIVE;
        const VOL_RENAME = VOL_RENAME;
        const XTIMES = XTIMES;
    }
}

// Release flags.
pub const RELEASE_FLUSH: u32 = 1;
pub const RELEASE_FLOCK_UNLOCK: u32 = 2;

// Getattr flags.
pub const GETATTR_FH: u32 = 1;

// Lock flags.
pub const LK_FLOCK: u32 = 1;

// Write flags.

/// Delayed write from page cache, file handle is guessed.
pub const WRITE_CACHE: u32 = 1;

/// `lock_owner` field is valid.
pub const WRITE_LOCKOWNER: u32 = 2;

// Read flags.
pub const READ_LOCKOWNER: u32 = 2;

// Ioctl flags.

/// 32bit compat ioctl on 64bit machine
const IOCTL_COMPAT: u32 = 1;

/// Not restricted to well-formed ioctls, retry allowed
const IOCTL_UNRESTRICTED: u32 = 2;

/// Retry with new iovecs
const IOCTL_RETRY: u32 = 4;

/// 32bit ioctl
const IOCTL_32BIT: u32 = 8;

/// Is a directory
const IOCTL_DIR: u32 = 16;

/// Maximum of in_iovecs + out_iovecs
const IOCTL_MAX_IOV: u32 = 256;

bitflags! {
    pub struct IoctlFlags: u32 {
        /// 32bit compat ioctl on 64bit machine
        const IOCTL_COMPAT = IOCTL_COMPAT;

        /// Not restricted to well-formed ioctls, retry allowed
        const IOCTL_UNRESTRICTED = IOCTL_UNRESTRICTED;

        /// Retry with new iovecs
        const IOCTL_RETRY = IOCTL_RETRY;

        /// 32bit ioctl
        const IOCTL_32BIT = IOCTL_32BIT;

        /// Is a directory
        const IOCTL_DIR = IOCTL_DIR;

        /// Maximum of in_iovecs + out_iovecs
        const IOCTL_MAX_IOV = IOCTL_MAX_IOV;
    }
}

/// EntryOut flags
/// Entry is a submount root
pub const ATTR_SUBMOUNT: u32 = 1;

/// Request poll notify.
pub const POLL_SCHEDULE_NOTIFY: u32 = 1;

/// Fsync flags
///
/// Sync data only, not metadata
pub const FSYNC_FDATASYNC: u32 = 1;

/// The read buffer is required to be at least 8k, but may be much larger.
pub const FUSE_MIN_READ_BUFFER: u32 = 8192;

pub const FUSE_COMPAT_ENTRY_OUT_SIZE: usize = 120;
pub const FUSE_COMPAT_ATTR_OUT_SIZE: usize = 96;
pub const FUSE_COMPAT_MKNOD_IN_SIZE: usize = 8;
pub const FUSE_COMPAT_WRITE_IN_SIZE: usize = 24;
pub const FUSE_COMPAT_STATFS_SIZE: usize = 48;
pub const FUSE_COMPAT_INIT_OUT_SIZE: usize = 8;
pub const FUSE_COMPAT_22_INIT_OUT_SIZE: usize = 24;

// Message definitions follow.  It is safe to implement ByteValued for all of these
// because they are POD types.

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct Attr {
    pub ino: u64,
    pub size: u64,
    pub blocks: u64,
    pub atime: u64,
    pub mtime: u64,
    pub ctime: u64,
    pub crtime: u64,
    pub atimensec: u32,
    pub mtimensec: u32,
    pub ctimensec: u32,
    pub crtimensec: u32,
    pub mode: u32,
    pub nlink: u32,
    pub uid: u32,
    pub gid: u32,
    pub rdev: u32,
    pub flags: u32,
    pub blksize: u32,
    pub padding: u32,
}
unsafe impl ByteValued for Attr {}

impl From<stat64> for Attr {
    fn from(st: stat64) -> Attr {
        Attr::with_flags(st, 0)
    }
}

impl Attr {
    pub fn with_flags(st: stat64, flags: u32) -> Attr {
        Attr {
            ino: st.st_ino,
            size: st.st_size as u64,
            blocks: st.st_blocks as u64,
            atime: st.st_atime as u64,
            mtime: st.st_mtime as u64,
            ctime: st.st_ctime as u64,
            atimensec: st.st_atime_nsec as u32,
            mtimensec: st.st_mtime_nsec as u32,
            ctimensec: st.st_ctime_nsec as u32,
            mode: st.st_mode as u32,
            // In macos, st_nlink is always u16
            // ref:
            // macos: https://github.com/rust-lang/rust/blob/1.69.0/library/std/src/os/macos/raw.rs#L44
            nlink: st.st_nlink as u32,
            uid: st.st_uid,
            gid: st.st_gid,
            rdev: st.st_rdev as u32,
            blksize: st.st_blksize as u32,
            flags,
            crtime: 0,
            crtimensec: 0,
            padding: 0,
        }
    }
}

impl From<Attr> for stat64 {
    fn from(attr: Attr) -> stat64 {
        // Safe because we are zero-initializing a struct
        let mut out: stat64 = unsafe { mem::zeroed() };
        out.st_ino = attr.ino;
        out.st_size = attr.size as i64;
        out.st_blocks = attr.blocks as i64;
        out.st_atime = attr.atime as i64;
        out.st_mtime = attr.mtime as i64;
        out.st_ctime = attr.ctime as i64;
        out.st_atime_nsec = attr.atimensec as i64;
        out.st_mtime_nsec = attr.mtimensec as i64;
        out.st_ctime_nsec = attr.ctimensec as i64;
        out.st_mode = attr.mode as mode_t;
        out.st_nlink = attr.nlink as nlink_t;
        out.st_uid = attr.uid;
        out.st_gid = attr.gid;
        out.st_rdev = attr.rdev as dev_t;
        out.st_blksize = attr.blksize as blksize_t;

        out
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct Kstatfs {
    pub blocks: u64,
    pub bfree: u64,
    pub bavail: u64,
    pub files: u64,
    pub ffree: u64,
    pub bsize: u32,
    pub namelen: u32,
    pub frsize: u32,
    pub padding: u32,
    pub spare: [u32; 6],
}
unsafe impl ByteValued for Kstatfs {}

impl From<statvfs64> for Kstatfs {
    fn from(st: statvfs64) -> Self {
        Kstatfs {
            blocks: st.f_blocks as u64,
            bfree: st.f_bfree as u64,
            bavail: st.f_bavail as u64,
            files: st.f_files as u64,
            ffree: st.f_ffree as u64,
            bsize: st.f_bsize as u32,
            namelen: st.f_namemax as u32,
            frsize: st.f_frsize as u32,
            ..Default::default()
        }
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct FileLock {
    pub start: u64,
    pub end: u64,
    pub type_: u32,
    pub pid: u32, /* tgid */
}
unsafe impl ByteValued for FileLock {}

#[repr(u32)]
#[derive(Debug, Copy, Clone)]
pub enum Opcode {
    Lookup = 1,
    Forget = 2, /* No Reply */
    Getattr = 3,
    Setattr = 4,
    Readlink = 5,
    Symlink = 6,
    Mknod = 8,
    Mkdir = 9,
    Unlink = 10,
    Rmdir = 11,
    Rename = 12,
    Link = 13,
    Open = 14,
    Read = 15,
    Write = 16,
    Statfs = 17,
    Release = 18,
    Fsync = 20,
    Setxattr = 21,
    Getxattr = 22,
    Listxattr = 23,
    Removexattr = 24,
    Flush = 25,
    Init = 26,
    Opendir = 27,
    Readdir = 28,
    Releasedir = 29,
    Fsyncdir = 30,
    Getlk = 31,
    Setlk = 32,
    Setlkw = 33,
    Access = 34,
    Create = 35,
    Interrupt = 36,
    Bmap = 37,
    Destroy = 38,
    Ioctl = 39,
    Poll = 40,
    NotifyReply = 41,
    BatchForget = 42,
    Fallocate = 43,
    Setvolname = 61,
    Getxtimes = 62,
    Exchange = 63,
    MaxOpcode = 64,

    /* Reserved opcodes: helpful to detect structure endian-ness in case of e.g. virtiofs */
    CuseInitBswapReserved = 1_048_576, /* CUSE_INIT << 8 */
    InitBswapReserved = 436_207_616,   /* FUSE_INIT << 24 */
}

impl From<u32> for Opcode {
    fn from(op: u32) -> Opcode {
        if op >= Opcode::MaxOpcode as u32 {
            return Opcode::MaxOpcode;
        }
        unsafe { mem::transmute(op) }
    }
}

#[repr(u32)]
#[derive(Debug, Copy, Clone)]
pub enum NotifyOpcode {
    Poll = 1,
    InvalInode = 2,
    InvalEntry = 3,
    Store = 4,
    Retrieve = 5,
    Delete = 6,
    CodeMax = 7,
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct EntryOut {
    pub nodeid: u64,      /* Inode ID */
    pub generation: u64,  /* Inode generation: nodeid:gen must be unique for the fs's lifetime */
    pub entry_valid: u64, /* Cache timeout for the name */
    pub attr_valid: u64,  /* Cache timeout for the attributes */
    pub entry_valid_nsec: u32,
    pub attr_valid_nsec: u32,
    pub attr: Attr,
}
unsafe impl ByteValued for EntryOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct ForgetIn {
    pub nlookup: u64,
}
unsafe impl ByteValued for ForgetIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct ForgetOne {
    pub nodeid: u64,
    pub nlookup: u64,
}
unsafe impl ByteValued for ForgetOne {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct BatchForgetIn {
    pub count: u32,
    pub dummy: u32,
}
unsafe impl ByteValued for BatchForgetIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct GetattrIn {
    pub flags: u32,
    pub dummy: u32,
    pub fh: u64,
}
unsafe impl ByteValued for GetattrIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct AttrOut {
    pub attr_valid: u64, /* Cache timeout for the attributes */
    pub attr_valid_nsec: u32,
    pub dummy: u32,
    pub attr: Attr,
}
unsafe impl ByteValued for AttrOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct GetxtimesOut {
    pub bkuptime: u64,
    pub crtime: u64,
    pub bkuptimensec: u32,
    pub crtimensec: u32,
}
unsafe impl ByteValued for GetxtimesOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct MknodIn {
    pub mode: u32,
    pub rdev: u32,
    pub umask: u32,
    pub padding: u32,
}
unsafe impl ByteValued for MknodIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct MkdirIn {
    pub mode: u32,
    pub umask: u32,
}
unsafe impl ByteValued for MkdirIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct RenameIn {
    pub newdir: u64,
    pub flags: u32,
    pub padding: u32,
}
unsafe impl ByteValued for RenameIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct ExchangeIn {
    pub olddir: u64,
    pub newdir: u64,
    pub options: u64,
}
unsafe impl ByteValued for ExchangeIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct LinkIn {
    pub oldnodeid: u64,
}
unsafe impl ByteValued for LinkIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct SetattrIn {
    pub valid: u32,
    pub padding: u32,
    pub fh: u64,
    pub size: u64,
    pub lock_owner: u64,
    pub atime: u64,
    pub mtime: u64,
    pub ctime: u64,
    pub atimensec: u32,
    pub mtimensec: u32,
    pub ctimensec: u32,
    pub mode: u32,
    pub unused4: u32,
    pub uid: u32,
    pub gid: u32,
    pub unused5: u32,

    pub bkuptime: u64,
    pub chgtime: u64,
    pub crtime: u64,
    pub bkuptimensec: u32,
    pub chgtimensec: u32,
    pub crtimensec: u32,
    /// file flags; see chflags(2)
    pub flags: u32,
}
unsafe impl ByteValued for SetattrIn {}

impl From<SetattrIn> for stat64 {
    fn from(setattr: SetattrIn) -> stat64 {
        // Safe because we are zero-initializing a struct with only POD fields.
        let mut out: stat64 = unsafe { mem::zeroed() };
        out.st_mode = setattr.mode as mode_t;
        out.st_uid = setattr.uid;
        out.st_gid = setattr.gid;
        out.st_size = setattr.size as i64;
        out.st_atime = setattr.atime as i64;
        out.st_mtime = setattr.mtime as i64;
        out.st_ctime = setattr.ctime as i64;
        out.st_atime_nsec = i64::from(setattr.atimensec);
        out.st_mtime_nsec = i64::from(setattr.mtimensec);
        out.st_ctime_nsec = i64::from(setattr.ctimensec);
        out.st_flags = setattr.flags;

        out
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct OpenIn {
    pub flags: u32,
    pub fuse_flags: u32,
}
unsafe impl ByteValued for OpenIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct CreateIn {
    pub flags: u32,
    pub mode: u32,
    pub umask: u32,
    pub fuse_flags: u32,
}
unsafe impl ByteValued for CreateIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct OpenOut {
    pub fh: u64,
    pub open_flags: u32,
    pub padding: u32,
}
unsafe impl ByteValued for OpenOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct ReleaseIn {
    pub fh: u64,
    pub flags: u32,
    pub release_flags: u32,
    pub lock_owner: u64,
}
unsafe impl ByteValued for ReleaseIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct FlushIn {
    pub fh: u64,
    pub unused: u32,
    pub padding: u32,
    pub lock_owner: u64,
}
unsafe impl ByteValued for FlushIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct ReadIn {
    pub fh: u64,
    pub offset: u64,
    pub size: u32,
    pub read_flags: u32,
    pub lock_owner: u64,
    pub flags: u32,
    pub padding: u32,
}
unsafe impl ByteValued for ReadIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct WriteIn {
    pub fh: u64,
    pub offset: u64,
    pub size: u32,
    pub fuse_flags: u32,
    pub lock_owner: u64,
    pub flags: u32,
    pub padding: u32,
}
unsafe impl ByteValued for WriteIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct WriteOut {
    pub size: u32,
    pub padding: u32,
}
unsafe impl ByteValued for WriteOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct StatfsOut {
    pub st: Kstatfs,
}
unsafe impl ByteValued for StatfsOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct FsyncIn {
    pub fh: u64,
    pub fsync_flags: u32,
    pub padding: u32,
}
unsafe impl ByteValued for FsyncIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct SetxattrIn {
    pub size: u32,
    pub flags: u32,
}
unsafe impl ByteValued for SetxattrIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct GetxattrIn {
    pub size: u32,
    pub padding: u32,
    pub position: u32,
    pub padding2: u32,
}
unsafe impl ByteValued for GetxattrIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct GetxattrOut {
    pub size: u32,
    pub padding: u32,
}
unsafe impl ByteValued for GetxattrOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct LkIn {
    pub fh: u64,
    pub owner: u64,
    pub lk: FileLock,
    pub lk_flags: u32,
    pub padding: u32,
}
unsafe impl ByteValued for LkIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct LkOut {
    pub lk: FileLock,
}
unsafe impl ByteValued for LkOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct AccessIn {
    pub mask: u32,
    pub padding: u32,
}
unsafe impl ByteValued for AccessIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct InitIn {
    pub major: u32,
    pub minor: u32,
    pub max_readahead: u32,
    pub flags: u32,
}
unsafe impl ByteValued for InitIn {}

//The flag has been extended to 64 bit since fuse 7.36
#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct InitIn2 {
    pub flags2: u32,
    pub unused: [u32; 11],
}
unsafe impl ByteValued for InitIn2 {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct InitOut {
    pub major: u32,
    pub minor: u32,
    pub max_readahead: u32,
    pub flags: u32,
    pub max_background: u16,
    pub congestion_threshold: u16,
    pub max_write: u32,
    pub time_gran: u32,
    pub max_pages: u16,
    pub map_alignment: u16,
    pub flags2: u32,
    pub unused: [u32; 7],
}
unsafe impl ByteValued for InitOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct InterruptIn {
    pub unique: u64,
}
unsafe impl ByteValued for InterruptIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct BmapIn {
    pub block: u64,
    pub blocksize: u32,
    pub padding: u32,
}
unsafe impl ByteValued for BmapIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct BmapOut {
    pub block: u64,
}
unsafe impl ByteValued for BmapOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct IoctlIn {
    pub fh: u64,
    pub flags: u32,
    pub cmd: u32,
    pub arg: u64,
    pub in_size: u32,
    pub out_size: u32,
}
unsafe impl ByteValued for IoctlIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct IoctlIovec {
    pub base: u64,
    pub len: u64,
}
unsafe impl ByteValued for IoctlIovec {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct IoctlOut {
    pub result: i32,
    pub flags: u32,
    pub in_iovs: u32,
    pub out_iovs: u32,
}
unsafe impl ByteValued for IoctlOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct PollIn {
    pub fh: u64,
    pub kh: u64,
    pub flags: u32,
    pub events: u32,
}
unsafe impl ByteValued for PollIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct PollOut {
    pub revents: u32,
    pub padding: u32,
}
unsafe impl ByteValued for PollOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct NotifyPollWakeupOut {
    pub kh: u64,
}
unsafe impl ByteValued for NotifyPollWakeupOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct FallocateIn {
    pub fh: u64,
    pub offset: u64,
    pub length: u64,
    pub mode: u32,
    pub padding: u32,
}
unsafe impl ByteValued for FallocateIn {}

#[repr(C)]
#[derive(Default, Copy, Clone)]
pub struct InHeader {
    pub len: u32,
    pub opcode: u32,
    pub unique: u64,
    pub nodeid: u64,
    pub uid: u32,
    pub gid: u32,
    pub pid: u32,
    pub padding: u32,
}
unsafe impl ByteValued for InHeader {}

impl Debug for InHeader {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "InHeader {{ len: {}, opcode: {}, unique: {}, nodeid: 0x{:x}, uid: {}, gid: {}, pid: {}, padding: {} }}",
            self.len, self.opcode, self.unique, self.nodeid, self.uid, self.gid, self.pid, self.padding
        )
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct OutHeader {
    pub len: u32,
    pub error: i32,
    pub unique: u64,
}
unsafe impl ByteValued for OutHeader {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct Dirent {
    pub ino: u64,
    pub off: u64,
    pub namelen: u32,
    pub type_: u32,
    // char name[];
}
unsafe impl ByteValued for Dirent {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct Direntplus {
    pub entry_out: EntryOut,
    pub dirent: Dirent,
}
unsafe impl ByteValued for Direntplus {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct NotifyInvalInodeOut {
    pub ino: u64,
    pub off: i64,
    pub len: i64,
}
unsafe impl ByteValued for NotifyInvalInodeOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct NotifyInvalEntryOut {
    pub parent: u64,
    pub namelen: u32,
    pub padding: u32,
}
unsafe impl ByteValued for NotifyInvalEntryOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct NotifyDeleteOut {
    pub parent: u64,
    pub child: u64,
    pub namelen: u32,
    pub padding: u32,
}
unsafe impl ByteValued for NotifyDeleteOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct NotifyStoreOut {
    pub nodeid: u64,
    pub offset: u64,
    pub size: u32,
    pub padding: u32,
}
unsafe impl ByteValued for NotifyStoreOut {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct Notify_Retrieve_Out {
    pub notify_unique: u64,
    pub nodeid: u64,
    pub offset: u64,
    pub size: u32,
    pub padding: u32,
}
unsafe impl ByteValued for Notify_Retrieve_Out {}

/* Matches the size of fuse_write_in */
#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct NotifyRetrieveIn {
    pub dummy1: u64,
    pub offset: u64,
    pub size: u32,
    pub dummy2: u32,
    pub dummy3: u64,
    pub dummy4: u64,
}
unsafe impl ByteValued for NotifyRetrieveIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
// Returns WriteOut
pub struct CopyFileRangeIn {
    pub fh_in: u64,
    pub offset_in: u64,
    pub nodeid_out: u64,
    pub fh_out: u64,
    pub offset_out: u64,
    pub len: u64,
    pub flags: u64,
}
unsafe impl ByteValued for CopyFileRangeIn {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_struct_size() {
        assert_eq!(std::mem::size_of::<Attr>(), 104);
        assert_eq!(std::mem::size_of::<Kstatfs>(), 80);
        assert_eq!(std::mem::size_of::<FileLock>(), 24);
        assert_eq!(std::mem::size_of::<EntryOut>(), 144);
        assert_eq!(std::mem::size_of::<ForgetIn>(), 8);
        assert_eq!(std::mem::size_of::<ForgetOne>(), 16);
        assert_eq!(std::mem::size_of::<BatchForgetIn>(), 8);
        assert_eq!(std::mem::size_of::<GetattrIn>(), 16);
        assert_eq!(std::mem::size_of::<AttrOut>(), 120);
        assert_eq!(std::mem::size_of::<MknodIn>(), 16);
        assert_eq!(std::mem::size_of::<MkdirIn>(), 8);
        assert_eq!(std::mem::size_of::<InHeader>(), 40);
        assert_eq!(std::mem::size_of::<OutHeader>(), 16);
    }

    #[test]
    fn test_byte_valued() {
        let buf = [
            0x1u8, 0x2u8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0, 0x5u8, 0x6u8, 0x0, 0x0, 0x0, 0x0, 0x0, 0x0,
        ];
        let forget: &ForgetOne = ForgetOne::from_slice(&buf).unwrap();

        assert_eq!(forget.nodeid, 0x201u64);
        assert_eq!(forget.nlookup, 0x605u64);

        let forget = ForgetOne {
            nodeid: 0x201u64,
            nlookup: 0x605u64,
        };
        let buf = forget.as_slice();
        assert_eq!(buf[0], 0x1u8);
        assert_eq!(buf[1], 0x2u8);
        assert_eq!(buf[8], 0x5u8);
        assert_eq!(buf[9], 0x6u8);
    }
}
