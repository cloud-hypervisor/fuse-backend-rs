// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.
// Copyright (C) 2023 Alibaba Cloud. All rights reserved.

use std::collections::{btree_map, BTreeMap};
use std::ffi::{CStr, CString};
use std::fs::File;
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::{AsRawFd, FromRawFd};
use std::sync::atomic::{AtomicU64, AtomicU8, Ordering};
use std::sync::Mutex;

use super::inode_store::InodeId;
use super::MAX_HOST_INO;
use crate::abi::fuse_abi as fuse;
use crate::api::EMPTY_CSTR;

/// the 56th bit used to set the inode to 1 indicates virtual inode
const VIRTUAL_INODE_FLAG: u64 = 1 << 55;

/// Used to form a pair of dev and mntid as the key of the map
#[derive(Clone, Copy, Default, PartialOrd, Ord, PartialEq, Eq, Debug)]
struct DevMntIDPair(libc::dev_t, u64);

// Used to generate a unique inode with a maximum of 56 bits. the format is
// |1bit|8bit|47bit
// when the highest bit is equal to 0, it means the host inode format, and the lower 47 bits normally store no more than 47-bit inode
// When the highest bit is equal to 1, it indicates the virtual inode format,
// which is used to store more than 47 bits of inodes
// the middle 8bit is used to store the unique ID produced by the combination of dev+mntid
pub struct UniqueInodeGenerator {
    // Mapping (dev, mnt_id) pair to another small unique id
    dev_mntid_map: Mutex<BTreeMap<DevMntIDPair, u8>>,
    next_unique_id: AtomicU8,
    next_virtual_inode: AtomicU64,
}

impl UniqueInodeGenerator {
    pub fn new() -> Self {
        UniqueInodeGenerator {
            dev_mntid_map: Mutex::new(Default::default()),
            next_unique_id: AtomicU8::new(1),
            next_virtual_inode: AtomicU64::new(fuse::ROOT_ID + 1),
        }
    }

    pub fn get_unique_inode(&self, id: &InodeId) -> io::Result<libc::ino64_t> {
        let unique_id = {
            let id: DevMntIDPair = DevMntIDPair(id.dev, id.mnt);
            let mut id_map_guard = self.dev_mntid_map.lock().unwrap();
            match id_map_guard.entry(id) {
                btree_map::Entry::Occupied(v) => *v.get(),
                btree_map::Entry::Vacant(v) => {
                    if self.next_unique_id.load(Ordering::Relaxed) == u8::MAX {
                        return Err(io::Error::new(
                            io::ErrorKind::Other,
                            "the number of combinations of dev and mntid exceeds 255",
                        ));
                    }
                    let next_id = self.next_unique_id.fetch_add(1, Ordering::Relaxed);
                    v.insert(next_id);
                    next_id
                }
            }
        };

        let inode = if id.ino <= MAX_HOST_INO {
            id.ino
        } else {
            if self.next_virtual_inode.load(Ordering::Relaxed) > MAX_HOST_INO {
                return Err(io::Error::new(
                    io::ErrorKind::Other,
                    format!("the virtual inode excess {}", MAX_HOST_INO),
                ));
            }
            self.next_virtual_inode.fetch_add(1, Ordering::Relaxed) | VIRTUAL_INODE_FLAG
        };

        Ok((unique_id as u64) << 47 | inode)
    }

    #[cfg(test)]
    fn decode_unique_inode(&self, inode: libc::ino64_t) -> io::Result<InodeId> {
        if inode > crate::api::VFS_MAX_INO {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("the inode {} excess {}", inode, crate::api::VFS_MAX_INO),
            ));
        }

        let dev_mntid = (inode >> 47) as u8;
        if dev_mntid == u8::MAX {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!("invalid dev and mntid {} excess 255", dev_mntid),
            ));
        }

        let mut dev: libc::dev_t = 0;
        let mut mnt: u64 = 0;

        let mut found = false;
        let id_map_guard = self.dev_mntid_map.lock().unwrap();
        for (k, v) in id_map_guard.iter() {
            if *v == dev_mntid {
                found = true;
                dev = k.0;
                mnt = k.1;
                break;
            }
        }

        if !found {
            return Err(io::Error::new(
                io::ErrorKind::InvalidInput,
                format!(
                    "invalid dev and mntid {},there is no record in memory ",
                    dev_mntid
                ),
            ));
        }
        Ok(InodeId {
            ino: inode & MAX_HOST_INO,
            dev,
            mnt,
        })
    }
}

/// Safe wrapper around libc::openat().
pub fn openat(
    dir_fd: &impl AsRawFd,
    path: &CStr,
    flags: libc::c_int,
    mode: u32,
) -> io::Result<File> {
    // Safe because:
    // - CString::new() has returned success and thus guarantees `path_cstr` is a valid
    //   NUL-terminated string
    // - this does not modify any memory
    // - we check the return value
    // We do not check `flags` because if the kernel cannot handle poorly specified flags then we
    // have much bigger problems.
    let fd = if flags & libc::O_CREAT == libc::O_CREAT {
        // The mode argument is used only when O_CREAT is specified
        unsafe { libc::openat(dir_fd.as_raw_fd(), path.as_ptr(), flags, mode) }
    } else {
        unsafe { libc::openat(dir_fd.as_raw_fd(), path.as_ptr(), flags) }
    };
    if fd >= 0 {
        // Safe because we just opened this fd
        Ok(unsafe { File::from_raw_fd(fd) })
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Open `/proc/self/fd/{fd}` with the given flags to effectively duplicate the given `fd` with new
/// flags (e.g. to turn an `O_PATH` file descriptor into one that can be used for I/O).
pub fn reopen_fd_through_proc(
    fd: &impl AsRawFd,
    flags: libc::c_int,
    proc_self_fd: &impl AsRawFd,
) -> io::Result<File> {
    let name = CString::new(format!("{}", fd.as_raw_fd()).as_str())?;
    // Clear the `O_NOFOLLOW` flag if it is set since we need to follow the `/proc/self/fd` symlink
    // to get the file.
    openat(
        proc_self_fd,
        &name,
        flags & !libc::O_NOFOLLOW & !libc::O_CREAT,
        0,
    )
}

pub fn stat_fd(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<libc::stat64> {
    // Safe because this is a constant value and a valid C string.
    let pathname =
        path.unwrap_or_else(|| unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) });
    let mut st = MaybeUninit::<libc::stat64>::zeroed();

    // Safe because the kernel will only write data in `st` and we check the return value.
    let res = unsafe {
        libc::fstatat64(
            dir.as_raw_fd(),
            pathname.as_ptr(),
            st.as_mut_ptr(),
            libc::AT_EMPTY_PATH | libc::AT_SYMLINK_NOFOLLOW,
        )
    };
    if res >= 0 {
        // Safe because the kernel guarantees that the struct is now fully initialized.
        Ok(unsafe { st.assume_init() })
    } else {
        Err(io::Error::last_os_error())
    }
}

/// Returns true if it's safe to open this inode without O_PATH.
pub fn is_safe_inode(mode: u32) -> bool {
    // Only regular files and directories are considered safe to be opened from the file
    // server without O_PATH.
    matches!(mode & libc::S_IFMT, libc::S_IFREG | libc::S_IFDIR)
}

/// Returns true if the mode is for a directory.
pub fn is_dir(mode: u32) -> bool {
    (mode & libc::S_IFMT) == libc::S_IFDIR
}

pub fn ebadf() -> io::Error {
    io::Error::from_raw_os_error(libc::EBADF)
}

pub fn einval() -> io::Error {
    io::Error::from_raw_os_error(libc::EINVAL)
}

pub fn enosys() -> io::Error {
    io::Error::from_raw_os_error(libc::ENOSYS)
}

pub fn eperm() -> io::Error {
    io::Error::from_raw_os_error(libc::EPERM)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_is_safe_inode() {
        let mode = libc::S_IFREG;
        assert!(is_safe_inode(mode));

        let mode = libc::S_IFDIR;
        assert!(is_safe_inode(mode));

        let mode = libc::S_IFBLK;
        assert!(!is_safe_inode(mode));

        let mode = libc::S_IFCHR;
        assert!(!is_safe_inode(mode));

        let mode = libc::S_IFIFO;
        assert!(!is_safe_inode(mode));

        let mode = libc::S_IFLNK;
        assert!(!is_safe_inode(mode));

        let mode = libc::S_IFSOCK;
        assert!(!is_safe_inode(mode));
    }

    #[test]
    fn test_is_dir() {
        let mode = libc::S_IFREG;
        assert!(!is_dir(mode));

        let mode = libc::S_IFDIR;
        assert!(is_dir(mode));
    }

    #[test]
    fn test_generate_unique_inode() {
        // use normal inode format
        {
            let generator = UniqueInodeGenerator::new();

            let inode_alt_key = InodeId {
                ino: 1,
                dev: 0,
                mnt: 0,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 0
            // 55~48 bit = 0000 0001
            // 47~1 bit  = 1
            assert_eq!(unique_inode, 0x00800000000001);
            let expect_inode_alt_key = generator.decode_unique_inode(unique_inode).unwrap();
            assert_eq!(expect_inode_alt_key, inode_alt_key);

            let inode_alt_key = InodeId {
                ino: 1,
                dev: 0,
                mnt: 1,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 0
            // 55~48 bit = 0000 0010
            // 47~1 bit  = 1
            assert_eq!(unique_inode, 0x01000000000001);
            let expect_inode_alt_key = generator.decode_unique_inode(unique_inode).unwrap();
            assert_eq!(expect_inode_alt_key, inode_alt_key);

            let inode_alt_key = InodeId {
                ino: 2,
                dev: 0,
                mnt: 1,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 0
            // 55~48 bit = 0000 0010
            // 47~1 bit  = 2
            assert_eq!(unique_inode, 0x01000000000002);
            let expect_inode_alt_key = generator.decode_unique_inode(unique_inode).unwrap();
            assert_eq!(expect_inode_alt_key, inode_alt_key);

            let inode_alt_key = InodeId {
                ino: MAX_HOST_INO,
                dev: 0,
                mnt: 1,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 0
            // 55~48 bit = 0000 0010
            // 47~1 bit  = 0x7fffffffffff
            assert_eq!(unique_inode, 0x017fffffffffff);
            let expect_inode_alt_key = generator.decode_unique_inode(unique_inode).unwrap();
            assert_eq!(expect_inode_alt_key, inode_alt_key);
        }

        // use virtual inode format
        {
            let generator = UniqueInodeGenerator::new();
            let inode_alt_key = InodeId {
                ino: MAX_HOST_INO + 1,
                dev: u64::MAX,
                mnt: u64::MAX,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 1
            // 55~48 bit = 0000 0001
            // 47~1 bit  = 2 virtual inode start from 2~MAX_HOST_INO
            assert_eq!(unique_inode, 0x80800000000002);

            let inode_alt_key = InodeId {
                ino: MAX_HOST_INO + 2,
                dev: u64::MAX,
                mnt: u64::MAX,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 1
            // 55~48 bit = 0000 0001
            // 47~1 bit  = 3
            assert_eq!(unique_inode, 0x80800000000003);

            let inode_alt_key = InodeId {
                ino: MAX_HOST_INO + 3,
                dev: u64::MAX,
                mnt: 0,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 1
            // 55~48 bit = 0000 0010
            // 47~1 bit  = 4
            assert_eq!(unique_inode, 0x81000000000004);

            let inode_alt_key = InodeId {
                ino: u64::MAX,
                dev: u64::MAX,
                mnt: u64::MAX,
            };
            let unique_inode = generator.get_unique_inode(&inode_alt_key).unwrap();
            // 56 bit = 1
            // 55~48 bit = 0000 0001
            // 47~1 bit  = 5
            assert_eq!(unique_inode, 0x80800000000005);
        }
    }

    #[test]
    fn test_stat_fd() {
        let topdir = env!("CARGO_MANIFEST_DIR");
        let dir = File::open(topdir).unwrap();
        let filename = CString::new("build.rs").unwrap();

        let st1 = stat_fd(&dir, None).unwrap();
        let st2 = stat_fd(&dir, Some(&filename)).unwrap();

        assert_eq!(st1.st_dev, st2.st_dev);
        assert_ne!(st1.st_ino, st2.st_ino);
    }
}
