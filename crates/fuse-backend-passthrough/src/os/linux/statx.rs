// Copyright 2021 Red Hat, Inc. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

use std::ffi::CStr;
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::AsRawFd;

use super::os_compat::{statx_st, STATX_BASIC_STATS, STATX_MNT_ID};
use crate::FileHandle;
use fuse_backend_core::abi::fuse_abi as fuse;
use fuse_backend_core::api::EMPTY_CSTR;

pub type MountId = u64;

pub struct StatExt {
    pub st: fuse::stat64,
    pub mnt_id: MountId,
}

/*
 * Fields in libc::statx are only valid if their respective flag in
 * .stx_mask is set.  This trait provides functions that allow safe
 * access to the libc::statx components we are interested in.
 *
 * (The implementations of these functions need to check whether the
 * associated flag is set, and then extract the respective information
 * to return it.)
 */
trait SafeStatXAccess {
    fn stat64(&self) -> Option<fuse::stat64>;
    fn mount_id(&self) -> Option<MountId>;
}

impl SafeStatXAccess for statx_st {
    fn stat64(&self) -> Option<fuse::stat64> {
        fn makedev(maj: libc::c_uint, min: libc::c_uint) -> libc::dev_t {
            libc::makedev(maj, min)
        }

        if self.stx_mask & STATX_BASIC_STATS != 0 {
            /*
             * Unfortunately, we cannot use an initializer to create the
             * stat64 object, because it may contain padding and reserved
             * fields (depending on the architecture), and it does not
             * implement the Default trait.
             * So we take a zeroed struct and set what we can.
             * (Zero in all fields is wrong, but safe.)
             */
            let mut st = unsafe { MaybeUninit::<fuse::stat64>::zeroed().assume_init() };

            st.st_dev = makedev(self.stx_dev_major, self.stx_dev_minor);
            st.st_ino = self.stx_ino;
            st.st_mode = self.stx_mode as _;
            st.st_nlink = self.stx_nlink as _;
            st.st_uid = self.stx_uid;
            st.st_gid = self.stx_gid;
            st.st_rdev = makedev(self.stx_rdev_major, self.stx_rdev_minor);
            st.st_size = self.stx_size as _;
            st.st_blksize = self.stx_blksize as _;
            st.st_blocks = self.stx_blocks as _;
            st.st_atime = self.stx_atime.tv_sec;
            st.st_atime_nsec = self.stx_atime.tv_nsec as _;
            st.st_mtime = self.stx_mtime.tv_sec;
            st.st_mtime_nsec = self.stx_mtime.tv_nsec as _;
            st.st_ctime = self.stx_ctime.tv_sec;
            st.st_ctime_nsec = self.stx_ctime.tv_nsec as _;

            Some(st)
        } else {
            None
        }
    }

    fn mount_id(&self) -> Option<MountId> {
        if self.stx_mask & STATX_MNT_ID != 0 {
            Some(self.stx_mnt_id)
        } else {
            None
        }
    }
}

fn get_mount_id(dir: &impl AsRawFd, path: &CStr) -> Option<MountId> {
    match FileHandle::from_name_at(dir, path) {
        Ok(Some(v)) => Some(v.mnt_id),
        _ => None,
    }
}

// Only works on Linux, and libc::SYS_statx is only defined for these
// environments
/// Performs a statx() syscall.  libc provides libc::statx() that does
/// the same, however, the system's libc may not have a statx() wrapper
/// (e.g. glibc before 2.28), so linking to it may fail.
/// libc::syscall() and libc::SYS_statx are always present, though, so
/// we can safely rely on them.
unsafe fn do_statx(
    dirfd: libc::c_int,
    pathname: *const libc::c_char,
    flags: libc::c_int,
    mask: libc::c_uint,
    statxbuf: *mut statx_st,
) -> libc::c_int {
    libc::syscall(libc::SYS_statx, dirfd, pathname, flags, mask, statxbuf) as libc::c_int
}

/// Execute `statx()` on `path` relative to `dir`, without following a final symlink. An empty
/// `path` means `dir` itself.
fn statx_raw(
    dir: &impl AsRawFd,
    path: &CStr,
    flags: libc::c_int,
    mask: libc::c_uint,
) -> io::Result<statx_st> {
    let mut stx = MaybeUninit::<statx_st>::zeroed();
    // Safe because the kernel will only write data in `stx` and we check the return value.
    let res = unsafe {
        do_statx(
            dir.as_raw_fd(),
            path.as_ptr(),
            flags | libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
            mask,
            stx.as_mut_ptr(),
        )
    };
    if res < 0 {
        return Err(io::Error::last_os_error());
    }
    // Safe because the struct was zeroed and the kernel filled it in.
    Ok(unsafe { stx.assume_init() })
}

/// Execute `statx()` to get extended status with mount id.
pub fn statx(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<StatExt> {
    // Safe because this is a constant value and a valid C string.
    let path = path.unwrap_or_else(|| unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) });
    let stx = statx_raw(dir, path, 0, STATX_BASIC_STATS | STATX_MNT_ID)?;

    // if `statx()` doesn't provide the mount id (before kernel 5.8),
    // let's try `name_to_handle_at()`, if everything fails just use 0
    let mnt_id = stx
        .mount_id()
        .or_else(|| get_mount_id(dir, path))
        .unwrap_or(0);
    let st = stx
        .stat64()
        .ok_or_else(|| io::Error::from_raw_os_error(libc::ENOSYS))?;

    Ok(StatExt { st, mnt_id })
}

/// Execute `statx()` on `file` for a FUSE STATX reply. It passes on the `AT_STATX_*` sync type
/// in `flags`, and asks for the basic fields plus the birth time if `mask` has it. `fuse::Statx`
/// has mask bits for no other fields.
pub fn fuse_statx(file: &impl AsRawFd, flags: u32, mask: u32) -> io::Result<fuse::Statx> {
    // Safe because this is a constant value and a valid C string.
    let path = unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) };
    let stx = statx_raw(
        file,
        path,
        flags as libc::c_int & libc::AT_STATX_SYNC_TYPE,
        STATX_BASIC_STATS | (mask & fuse::STATX_BTIME),
    )?;

    let time = |tv_sec: i64, tv_nsec: u32| fuse::SxTime {
        tv_sec,
        tv_nsec,
        reserved: 0,
    };
    Ok(fuse::Statx {
        mask: stx.stx_mask & (fuse::STATX_BASIC_STATS | fuse::STATX_BTIME),
        blksize: stx.stx_blksize,
        attributes: stx.stx_attributes,
        nlink: stx.stx_nlink,
        uid: stx.stx_uid,
        gid: stx.stx_gid,
        mode: stx.stx_mode,
        ino: stx.stx_ino,
        size: stx.stx_size,
        blocks: stx.stx_blocks,
        attributes_mask: stx.stx_attributes_mask,
        atime: time(stx.stx_atime.tv_sec, stx.stx_atime.tv_nsec),
        btime: time(stx.stx_btime.tv_sec, stx.stx_btime.tv_nsec),
        ctime: time(stx.stx_ctime.tv_sec, stx.stx_ctime.tv_nsec),
        mtime: time(stx.stx_mtime.tv_sec, stx.stx_mtime.tv_nsec),
        rdev_major: stx.stx_rdev_major,
        rdev_minor: stx.stx_rdev_minor,
        dev_major: stx.stx_dev_major,
        dev_minor: stx.stx_dev_minor,
        ..Default::default()
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;
    use std::fs::File;

    #[test]
    fn test_statx() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("Cargo.toml").unwrap();

        let st1 = statx(&dir, None).unwrap();
        let st2 = statx(&dir, Some(&filename)).unwrap();
        let mnt_id = get_mount_id(&dir, &filename).unwrap();

        assert_eq!(st1.mnt_id, st2.mnt_id);
        assert_eq!(st1.mnt_id, mnt_id);
    }
}
