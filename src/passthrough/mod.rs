// Copyright (C) 2020 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! Fuse passthrough file system, mirroring an existing FS hierarchy.
//!
//! This file system mirrors the existing file system hierarchy of the system, starting at the
//! root file system. This is implemented by just "passing through" all requests to the
//! corresponding underlying file system.
//!
//! The code is derived from the
//! [CrosVM](https://chromium.googlesource.com/chromiumos/platform/crosvm/) project,
//! with heavy modification/enhancements from Alibaba Cloud OS team.

use std::any::Any;
use std::collections::{btree_map, BTreeMap};
use std::ffi::{CStr, CString};
use std::fs::File;
use std::io;
use std::marker::PhantomData;
use std::mem::MaybeUninit;
use std::ops::{Deref, DerefMut};
use std::os::unix::io::{AsRawFd, FromRawFd, RawFd};
use std::str::FromStr;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, RwLock, RwLockWriteGuard};
use std::time::Duration;

use vm_memory::ByteValued;

use crate::abi::linux_abi as fuse;
use crate::api::filesystem::Entry;
use crate::api::{BackendFileSystem, VFS_MAX_INO};
use crate::BitmapSlice;

#[cfg(feature = "async-io")]
mod async_io;
mod file_handle;
mod multikey;
mod sync_io;

use file_handle::{FileHandle, MountFds};
use multikey::MultikeyBTreeMap;

use crate::async_util::{AsyncDrive, AsyncDriver};

const CURRENT_DIR_CSTR: &[u8] = b".\0";
const PARENT_DIR_CSTR: &[u8] = b"..\0";
const EMPTY_CSTR: &[u8] = b"\0";
const PROC_CSTR: &[u8] = b"/proc\0";

type Inode = u64;
type Handle = u64;
type MultiKeyMap = MultikeyBTreeMap<Inode, InodeAltKey, Arc<InodeData>>;

#[derive(Clone, Copy)]
struct InodeStat {
    stat: libc::stat64,
    mnt_id: u64,
}

impl InodeStat {
    fn get_stat(&self) -> libc::stat64 {
        self.stat
    }

    fn get_mnt_id(&self) -> u64 {
        self.mnt_id
    }
}

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
enum InodeAltKey {
    Ids {
        ino: libc::ino64_t,
        dev: libc::dev_t,
        mnt: u64,
    },
    Handle(FileHandle),
}

impl InodeAltKey {
    fn ids_from_stat(ist: &InodeStat) -> Self {
        let st = ist.get_stat();
        InodeAltKey::Ids {
            ino: st.st_ino,
            dev: st.st_dev,
            mnt: ist.get_mnt_id(),
        }
    }
}

enum FileOrHandle {
    File(File),
    Handle(FileHandle),
}

impl FileOrHandle {
    fn handle(&self) -> Option<&FileHandle> {
        match self {
            FileOrHandle::File(_) => None,
            FileOrHandle::Handle(h) => Some(h),
        }
    }
}

#[derive(Debug)]
enum InodeFile<'a> {
    Owned(File),
    Ref(&'a File),
}

impl AsRawFd for InodeFile<'_> {
    /// Return a file descriptor for this file
    /// Note: This fd is only valid as long as the `InodeFile` exists.
    fn as_raw_fd(&self) -> RawFd {
        match self {
            Self::Owned(file) => file.as_raw_fd(),
            Self::Ref(file_ref) => file_ref.as_raw_fd(),
        }
    }
}

struct InodeData {
    inode: Inode,
    // Most of these aren't actually files but ¯\_(ツ)_/¯.
    file_or_handle: FileOrHandle,
    #[allow(dead_code)]
    altkey: InodeAltKey,
    refcount: AtomicU64,
}

impl<'a> InodeData {
    fn new(inode: Inode, f: FileOrHandle, refcount: u64, altkey: InodeAltKey) -> Self {
        InodeData {
            inode,
            file_or_handle: f,
            altkey,
            refcount: AtomicU64::new(refcount),
        }
    }

    fn get_file(&self, mount_fds: &MountFds) -> io::Result<InodeFile<'_>> {
        match &self.file_or_handle {
            FileOrHandle::File(f) => Ok(InodeFile::Ref(f)),
            FileOrHandle::Handle(h) => {
                let f = h.open_with_mount_fds(mount_fds, libc::O_PATH)?;
                Ok(InodeFile::Owned(f))
            }
        }
    }
}

/// Data structures to manage accessed inodes.
struct InodeMap {
    inodes: RwLock<MultiKeyMap>,
}

impl InodeMap {
    fn new() -> Self {
        InodeMap {
            inodes: RwLock::new(MultikeyBTreeMap::new()),
        }
    }

    fn clear(&self) {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.inodes.write().unwrap().clear();
    }

    fn get(&self, inode: Inode) -> io::Result<Arc<InodeData>> {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.inodes
            .read()
            .unwrap()
            .get(&inode)
            .map(Arc::clone)
            .ok_or_else(ebadf)
    }

    fn get_alt(
        &self,
        ids_altkey: &InodeAltKey,
        handle_altkey: Option<&InodeAltKey>,
    ) -> Option<Arc<InodeData>> {
        // Do not expect poisoned lock here, so safe to unwrap().
        let inodes = self.inodes.read().unwrap();

        Self::get_alt_locked(inodes.deref(), ids_altkey, handle_altkey)
    }

    fn get_alt_locked(
        inodes: &MultiKeyMap,
        ids_altkey: &InodeAltKey,
        handle_altkey: Option<&InodeAltKey>,
    ) -> Option<Arc<InodeData>> {
        handle_altkey
            .map(|altkey| inodes.get_alt(altkey))
            .flatten()
            .or_else(|| {
                inodes.get_alt(ids_altkey).filter(|data| {
                    // When we have to fall back to looking up an inode by its IDs, ensure that
                    // we hit an entry that does not have a file handle.  Entries with file
                    // handles must also have a handle alt key, so if we have not found it by
                    // that handle alt key, we must have found an entry with a mismatching
                    // handle; i.e. an entry for a different file, even though it has the same
                    // inode ID.
                    // (This can happen when we look up a new file that has reused the inode ID
                    // of some previously unlinked inode we still have in `.inodes`.)
                    handle_altkey.is_none() || data.file_or_handle.handle().is_none()
                })
            })
            .map(Arc::clone)
    }

    fn get_map_mut(&self) -> RwLockWriteGuard<MultiKeyMap> {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.inodes.write().unwrap()
    }

    fn insert(
        &self,
        inode: Inode,
        data: InodeData,
        ids_altkey: InodeAltKey,
        handle_altkey: Option<InodeAltKey>,
    ) {
        let mut inodes = self.get_map_mut();

        Self::insert_locked(inodes.deref_mut(), inode, data, ids_altkey, handle_altkey)
    }

    fn insert_locked(
        inodes: &mut MultiKeyMap,
        inode: Inode,
        data: InodeData,
        ids_altkey: InodeAltKey,
        handle_altkey: Option<InodeAltKey>,
    ) {
        inodes.insert(inode, Arc::new(data));
        inodes.insert_alt(ids_altkey, inode);
        if let Some(altkey) = handle_altkey {
            inodes.insert_alt(altkey, inode);
        }
    }
}

struct HandleData {
    inode: Inode,
    file: File,
    lock: Mutex<()>,
}

impl HandleData {
    fn new(inode: Inode, file: File) -> Self {
        HandleData {
            inode,
            file,
            lock: Mutex::new(()),
        }
    }

    fn get_file_mut(&self) -> (MutexGuard<()>, &File) {
        (self.lock.lock().unwrap(), &self.file)
    }

    // When making use of the underlying RawFd, the caller must ensure that the Arc<HandleData>
    // object is within scope. Otherwise it may cause race window to access wrong target fd.
    // By introducing this method, we could explicitly audit all callers making use of the
    // underlying RawFd.
    fn get_handle_raw_fd(&self) -> RawFd {
        self.file.as_raw_fd()
    }
}

struct HandleMap {
    handles: RwLock<BTreeMap<Handle, Arc<HandleData>>>,
}

impl HandleMap {
    fn new() -> Self {
        HandleMap {
            handles: RwLock::new(BTreeMap::new()),
        }
    }

    fn clear(&self) {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.handles.write().unwrap().clear();
    }

    fn insert(&self, handle: Handle, data: HandleData) {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.handles.write().unwrap().insert(handle, Arc::new(data));
    }

    fn release(&self, handle: Handle, inode: Inode) -> io::Result<()> {
        // Do not expect poisoned lock here, so safe to unwrap().
        let mut handles = self.handles.write().unwrap();

        if let btree_map::Entry::Occupied(e) = handles.entry(handle) {
            if e.get().inode == inode {
                // We don't need to close the file here because that will happen automatically when
                // the last `Arc` is dropped.
                e.remove();
                return Ok(());
            }
        }

        Err(ebadf())
    }

    fn get(&self, handle: Handle, inode: Inode) -> io::Result<Arc<HandleData>> {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.handles
            .read()
            .unwrap()
            .get(&handle)
            .filter(|hd| hd.inode == inode)
            .map(Arc::clone)
            .ok_or_else(ebadf)
    }
}

#[repr(C, packed)]
#[derive(Clone, Copy, Debug, Default)]
struct LinuxDirent64 {
    d_ino: libc::ino64_t,
    d_off: libc::off64_t,
    d_reclen: libc::c_ushort,
    d_ty: libc::c_uchar,
}
unsafe impl ByteValued for LinuxDirent64 {}

/// The caching policy that the file system should report to the FUSE client. By default the FUSE
/// protocol uses close-to-open consistency. This means that any cached contents of the file are
/// invalidated the next time that file is opened.
#[derive(Debug, Clone, PartialEq)]
pub enum CachePolicy {
    /// The client should never cache file data and all I/O should be directly forwarded to the
    /// server. This policy must be selected when file contents may change without the knowledge of
    /// the FUSE client (i.e., the file system does not have exclusive access to the directory).
    Never,

    /// The client is free to choose when and how to cache file data. This is the default policy and
    /// uses close-to-open consistency as described in the enum documentation.
    Auto,

    /// The client should always cache file data. This means that the FUSE client will not
    /// invalidate any cached data that was returned by the file system the last time the file was
    /// opened. This policy should only be selected when the file system has exclusive access to the
    /// directory.
    Always,
}

impl FromStr for CachePolicy {
    type Err = &'static str;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "never" | "Never" | "NEVER" | "none" | "None" | "NONE" => Ok(CachePolicy::Never),
            "auto" | "Auto" | "AUTO" => Ok(CachePolicy::Auto),
            "always" | "Always" | "ALWAYS" => Ok(CachePolicy::Always),
            _ => Err("invalid cache policy"),
        }
    }
}

impl Default for CachePolicy {
    fn default() -> Self {
        CachePolicy::Auto
    }
}

/// Options that configure the behavior of the passthrough fuse file system.
#[derive(Debug, Clone, PartialEq)]
pub struct Config {
    /// How long the FUSE client should consider directory entries to be valid. If the contents of a
    /// directory can only be modified by the FUSE client (i.e., the file system has exclusive
    /// access), then this should be a large value.
    ///
    /// The default value for this option is 5 seconds.
    pub entry_timeout: Duration,

    /// How long the FUSE client should consider file and directory attributes to be valid. If the
    /// attributes of a file or directory can only be modified by the FUSE client (i.e., the file
    /// system has exclusive access), then this should be set to a large value.
    ///
    /// The default value for this option is 5 seconds.
    pub attr_timeout: Duration,

    /// The caching policy the file system should use. See the documentation of `CachePolicy` for
    /// more details.
    pub cache_policy: CachePolicy,

    /// Whether the file system should enabled writeback caching. This can improve performance as it
    /// allows the FUSE client to cache and coalesce multiple writes before sending them to the file
    /// system. However, enabling this option can increase the risk of data corruption if the file
    /// contents can change without the knowledge of the FUSE client (i.e., the server does **NOT**
    /// have exclusive access). Additionally, the file system should have read access to all files
    /// in the directory it is serving as the FUSE client may send read requests even for files
    /// opened with `O_WRONLY`.
    ///
    /// Therefore callers should only enable this option when they can guarantee that: 1) the file
    /// system has exclusive access to the directory and 2) the file system has read permissions for
    /// all files in that directory.
    ///
    /// The default value for this option is `false`.
    pub writeback: bool,

    /// The path of the root directory.
    ///
    /// The default is `/`.
    pub root_dir: String,

    /// Whether the file system should support Extended Attributes (xattr). Enabling this feature may
    /// have a significant impact on performance, especially on write parallelism. This is the result
    /// of FUSE attempting to remove the special file privileges after each write request.
    ///
    /// The default value for this options is `false`.
    pub xattr: bool,

    /// To be compatible with Vfs and PseudoFs, PassthroughFs needs to prepare
    /// root inode before accepting INIT request.
    ///
    /// The default value for this option is `true`.
    pub do_import: bool,

    /// Control whether no_open is allowed.
    ///
    /// The default value for this option is `false`.
    pub no_open: bool,

    /// Control whether no_opendir is allowed.
    ///
    /// The default value for this option is `false`.
    pub no_opendir: bool,

    /// Control whether kill_priv_v2 is enabled.
    ///
    /// The default value for this option is `false`.
    pub killpriv_v2: bool,

    /// Whether to use file handles to reference inodes.  We need to be able to open file
    /// descriptors for arbitrary inodes, and by default that is done by storing an `O_PATH` FD in
    /// `InodeData`.  Not least because there is a maximum number of FDs a process can have open
    /// users may find it preferable to store a file handle instead, which we can use to open an FD
    /// when necessary.
    /// So this switch allows to choose between the alternatives: When set to `false`, `InodeData`
    /// will store `O_PATH` FDs.  Otherwise, we will attempt to generate and store a file handle
    /// instead.
    ///
    /// The default is `false`.
    pub inode_file_handles: bool,

    /// Control whether readdir/readdirplus requests return zero dirent to client, as if the
    /// directory is empty even if it has children.
    pub no_readdir: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            entry_timeout: Duration::from_secs(5),
            attr_timeout: Duration::from_secs(5),
            cache_policy: Default::default(),
            writeback: false,
            root_dir: String::from("/"),
            xattr: false,
            do_import: true,
            no_open: false,
            no_opendir: false,
            killpriv_v2: false,
            inode_file_handles: false,
            no_readdir: false,
        }
    }
}

/// A file system that simply "passes through" all requests it receives to the underlying file
/// system.
///
/// To keep the implementation simple it servers the contents of its root directory. Users
/// that wish to serve only a specific directory should set up the environment so that that
/// directory ends up as the root of the file system process. One way to accomplish this is via a
/// combination of mount namespaces and the pivot_root system call.
pub struct PassthroughFs<D: AsyncDrive = AsyncDriver, S: BitmapSlice + Send + Sync = ()> {
    // File descriptors for various points in the file system tree. These fds are always opened with
    // the `O_PATH` option so they cannot be used for reading or writing any data. See the
    // documentation of the `O_PATH` flag in `open(2)` for more details on what one can and cannot
    // do with an fd opened with this flag.
    inode_map: InodeMap,
    next_inode: AtomicU64,

    // File descriptors for open files and directories. Unlike the fds in `inodes`, these _can_ be
    // used for reading and writing data.
    handle_map: HandleMap,
    next_handle: AtomicU64,

    // Maps mount IDs to an open FD on the respective ID for the purpose of open_by_handle_at().
    mount_fds: MountFds,

    // File descriptor pointing to the `/proc` directory. This is used to convert an fd from
    // `inodes` into one that can go into `handles`. This is accomplished by reading the
    // `self/fd/{}` symlink. We keep an open fd here in case the file system tree that we are meant
    // to be serving doesn't have access to `/proc`.
    proc: File,

    // Whether writeback caching is enabled for this directory. This will only be true when
    // `cfg.writeback` is true and `init` was called with `FsOptions::WRITEBACK_CACHE`.
    writeback: AtomicBool,

    // Whether no_open is enabled.
    no_open: AtomicBool,

    // Whether no_opendir is enabled.
    no_opendir: AtomicBool,

    // Whether kill_priv_v2 is enabled.
    killpriv_v2: AtomicBool,

    // Whether no_readdir is enabled.
    no_readdir: AtomicBool,

    cfg: Config,

    phantom: PhantomData<D>,
    phantom2: PhantomData<S>,
}

impl<D: AsyncDrive, S: BitmapSlice + Send + Sync> PassthroughFs<D, S> {
    /// Create a Passthrough file system instance.
    pub fn new(cfg: Config) -> io::Result<PassthroughFs<D, S>> {
        // Safe because this is a constant value and a valid C string.
        let proc_cstr = unsafe { CStr::from_bytes_with_nul_unchecked(PROC_CSTR) };
        let proc = Self::open_file(
            libc::AT_FDCWD,
            proc_cstr,
            libc::O_PATH | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0,
        )?;

        Ok(PassthroughFs {
            inode_map: InodeMap::new(),
            next_inode: AtomicU64::new(fuse::ROOT_ID + 1),

            handle_map: HandleMap::new(),
            next_handle: AtomicU64::new(1),
            mount_fds: MountFds::new(),

            proc,

            writeback: AtomicBool::new(false),
            no_open: AtomicBool::new(false),
            no_opendir: AtomicBool::new(false),
            killpriv_v2: AtomicBool::new(false),
            no_readdir: AtomicBool::new(cfg.no_readdir),
            cfg,

            phantom: PhantomData,
            phantom2: PhantomData,
        })
    }

    /// Initialize the Passthrough file system.
    pub fn import(&self) -> io::Result<()> {
        let root = CString::new(self.cfg.root_dir.as_str()).expect("CString::new failed");

        let (file_or_handle, _st, ids_altkey, handle_altkey) = Self::open_file_or_handle(
            self.cfg.inode_file_handles,
            libc::AT_FDCWD,
            &root,
            &self.mount_fds,
            |fd, flags| {
                let pathname = CString::new(format!("self/fd/{}", fd))
                    .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
                Self::open_file(self.proc.as_raw_fd(), &pathname, flags, 0)
            },
        )
        .map_err(|e| {
            error!("fuse: import: failed to get file or handle: {:?}", e);
            e
        })?;

        // Safe because this doesn't modify any memory and there is no need to check the return
        // value because this system call always succeeds. We need to clear the umask here because
        // we want the client to be able to set all the bits in the mode.
        unsafe { libc::umask(0o000) };

        // Not sure why the root inode gets a refcount of 2 but that's what libfuse does.
        self.inode_map.insert(
            fuse::ROOT_ID,
            InodeData::new(fuse::ROOT_ID, file_or_handle, 2, ids_altkey),
            ids_altkey,
            handle_altkey,
        );

        Ok(())
    }

    /// Get the list of file descriptors which should be reserved across live upgrade.
    pub fn keep_fds(&self) -> Vec<RawFd> {
        vec![self.proc.as_raw_fd()]
    }

    fn stat(dir: &impl AsRawFd, path: Option<&CStr>) -> io::Result<libc::stat64> {
        Self::stat_fd(dir.as_raw_fd(), path)
    }

    fn stat_fd(dir_fd: RawFd, path: Option<&CStr>) -> io::Result<libc::stat64> {
        // Safe because this is a constant value and a valid C string.
        let pathname =
            path.unwrap_or_else(|| unsafe { CStr::from_bytes_with_nul_unchecked(EMPTY_CSTR) });
        let mut st = MaybeUninit::<libc::stat64>::zeroed();

        // Safe because the kernel will only write data in `st` and we check the return value.
        let res = unsafe {
            libc::fstatat64(
                dir_fd,
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

    fn create_file_excl(
        dfd: i32,
        pathname: &CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<Option<File>> {
        let fd = unsafe {
            libc::openat(
                dfd,
                pathname.as_ptr(),
                flags | libc::O_CREAT | libc::O_EXCL,
                mode,
            )
        };
        if fd < 0 {
            let err = io::Error::last_os_error();
            if err.kind() == io::ErrorKind::AlreadyExists {
                return Ok(None);
            }
            return Err(err);
        }
        Ok(Some(unsafe { File::from_raw_fd(fd) }))
    }

    fn open_file(dfd: i32, pathname: &CStr, flags: i32, mode: u32) -> io::Result<File> {
        let fd = if flags & libc::O_CREAT == libc::O_CREAT {
            unsafe { libc::openat(dfd, pathname.as_ptr(), flags, mode) }
        } else {
            unsafe { libc::openat(dfd, pathname.as_ptr(), flags) }
        };

        if fd < 0 {
            return Err(io::Error::last_os_error());
        }

        // Safe because we just opened this fd.
        Ok(unsafe { File::from_raw_fd(fd) })
    }

    fn open_proc_file(proc: &File, fd: RawFd, flags: i32) -> io::Result<File> {
        let pathname = CString::new(format!("self/fd/{}", fd))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        // We don't really check `flags` because if the kernel can't handle poorly specified flags
        // then we have much bigger problems. Also, clear the `O_NOFOLLOW` flag if it is set since
        // we need to follow the `/proc/self/fd` symlink to get the file.
        Self::open_file(
            proc.as_raw_fd(),
            &pathname,
            (flags | libc::O_CLOEXEC) & (!libc::O_NOFOLLOW),
            0,
        )
    }

    /// Create a File or File Handle for `name` under directory `dir_fd` to support `lookup()`.
    fn open_file_or_handle<F>(
        use_handle: bool,
        dir_fd: RawFd,
        name: &CStr,
        mount_fds: &MountFds,
        reopen_dir: F,
    ) -> io::Result<(FileOrHandle, InodeStat, InodeAltKey, Option<InodeAltKey>)>
    where
        F: FnOnce(RawFd, libc::c_int) -> io::Result<File>,
    {
        let handle = if use_handle {
            FileHandle::from_name_at_with_mount_fds(dir_fd, name, mount_fds, reopen_dir)
        } else {
            Err(io::Error::from_raw_os_error(libc::ENOTSUP))
        };

        // Ignore errors, because having a handle is optional
        let file_or_handle = if let Ok(h) = handle {
            FileOrHandle::Handle(h)
        } else {
            let f = Self::open_file(
                dir_fd,
                name,
                libc::O_PATH | libc::O_NOFOLLOW | libc::O_CLOEXEC,
                0,
            )?;

            FileOrHandle::File(f)
        };

        let inode_stat = match &file_or_handle {
            FileOrHandle::File(f) => {
                // TODO: use statx(2) to query mntid when 5.8 kernel or later are widely used.
                //
                // Some filesystems don't support file handle, for example overlayfs mounted
                // without index feature, if so just use mntid 0 in that case.
                let mnt_id = match FileHandle::from_name_at(dir_fd, name) {
                    Ok(h) => h.mnt_id,
                    Err(_) => 0,
                };
                InodeStat {
                    stat: Self::stat(f, None)?,
                    mnt_id,
                }
            }
            FileOrHandle::Handle(h) => InodeStat {
                stat: Self::stat_fd(dir_fd, Some(name))?,
                mnt_id: h.mnt_id,
            },
        };

        let ids_altkey = InodeAltKey::ids_from_stat(&inode_stat);

        // Note that this will always be `None` if `cfg.inode_file_handles` is false, but we only
        // really need this alt key when we do not have an `O_PATH` fd open for every inode.  So if
        // `cfg.inode_file_handles` is false, we do not need this key anyway.
        let handle_altkey = file_or_handle.handle().map(|h| InodeAltKey::Handle(*h));

        Ok((file_or_handle, inode_stat, ids_altkey, handle_altkey))
    }

    fn do_lookup(&self, parent: Inode, name: &CStr) -> io::Result<Entry> {
        let dir = self.inode_map.get(parent)?;
        let dir_file = dir.get_file(&self.mount_fds)?;
        let (file_or_handle, st, ids_altkey, handle_altkey) = Self::open_file_or_handle(
            self.cfg.inode_file_handles,
            dir_file.as_raw_fd(),
            name,
            &self.mount_fds,
            |fd, flags| Self::open_proc_file(&self.proc, fd, flags),
        )
        .map_err(|e| {
            error!("fuse: do_lookup: failed to get file or handle: {:?}", e);
            e
        })?;

        let mut found = None;
        'search: loop {
            match self.inode_map.get_alt(&ids_altkey, handle_altkey.as_ref()) {
                // No existing entry found
                None => break 'search,
                Some(data) => {
                    let curr = data.refcount.load(Ordering::Acquire);
                    // forgot_one() has just destroyed the entry, retry...
                    if curr == 0 {
                        continue 'search;
                    }

                    // Saturating add to avoid integer overflow, it's not realistic to saturate u64.
                    let new = curr.saturating_add(1);

                    // Synchronizes with the forgot_one()
                    if data
                        .refcount
                        .compare_exchange(curr, new, Ordering::AcqRel, Ordering::Acquire)
                        .is_ok()
                    {
                        found = Some(data.inode);
                        break;
                    }
                }
            }
        }

        let inode = if let Some(v) = found {
            v
        } else {
            // Write guard get_alt_locked() and insert_lock() to avoid race conditions.
            let mut inodes = self.inode_map.get_map_mut();

            // Lookup inode_map again after acquiring the inode_map lock, as there might be another
            // racing thread already added an inode with the same altkey while we're not holding
            // the lock. If so just use the newly added inode, otherwise the inode will be replaced
            // and results in EBADF.
            match InodeMap::get_alt_locked(inodes.deref(), &ids_altkey, handle_altkey.as_ref()) {
                Some(data) => {
                    trace!(
                        "fuse: do_lookup sees existing inode {} ids_altkey {:?}",
                        data.inode,
                        ids_altkey
                    );
                    data.refcount.fetch_add(1, Ordering::Relaxed);
                    data.inode
                }
                None => {
                    let inode = self.next_inode.fetch_add(1, Ordering::Relaxed);
                    if inode > VFS_MAX_INO {
                        error!("fuse: max inode number reached: {}", VFS_MAX_INO);
                        return Err(io::Error::new(
                            io::ErrorKind::Other,
                            format!("max inode number reached: {}", VFS_MAX_INO),
                        ));
                    }
                    trace!(
                        "fuse: do_lookup adds new inode {} ids_altkey {:?} handle_altkey {:?}",
                        inode,
                        ids_altkey,
                        handle_altkey
                    );

                    InodeMap::insert_locked(
                        inodes.deref_mut(),
                        inode,
                        InodeData::new(inode, file_or_handle, 1, ids_altkey),
                        ids_altkey,
                        handle_altkey,
                    );
                    inode
                }
            }
        };

        Ok(Entry {
            inode,
            generation: 0,
            attr: st.get_stat(),
            attr_timeout: self.cfg.attr_timeout,
            entry_timeout: self.cfg.entry_timeout,
        })
    }

    fn forget_one(inodes: &mut MultiKeyMap, inode: Inode, count: u64) {
        // ROOT_ID should not be forgotten, or we're not able to access to files any more.
        if inode == fuse::ROOT_ID {
            return;
        }

        if let Some(data) = inodes.get(&inode) {
            // Acquiring the write lock on the inode map prevents new lookups from incrementing the
            // refcount but there is the possibility that a previous lookup already acquired a
            // reference to the inode data and is in the process of updating the refcount so we need
            // to loop here until we can decrement successfully.
            loop {
                let curr = data.refcount.load(Ordering::Acquire);

                // Saturating sub because it doesn't make sense for a refcount to go below zero and
                // we don't want misbehaving clients to cause integer overflow.
                let new = curr.saturating_sub(count);

                trace!(
                    "fuse: forget inode {} refcount {}, count {}, new_count {}",
                    inode,
                    curr,
                    count,
                    new
                );

                // Synchronizes with the acquire load in `do_lookup`.
                if data
                    .refcount
                    .compare_exchange(curr, new, Ordering::AcqRel, Ordering::Acquire)
                    .is_ok()
                {
                    if new == 0 {
                        // We just removed the last refcount for this inode.
                        inodes.remove(&inode);
                    }
                    break;
                }
            }
        }
    }

    fn do_release(&self, inode: Inode, handle: Handle) -> io::Result<()> {
        self.handle_map.release(handle, inode)
    }
}

#[cfg(not(feature = "async-io"))]
impl<D: AsyncDrive, S: 'static + BitmapSlice + Send + Sync> BackendFileSystem<D, S>
    for PassthroughFs<D, S>
{
    fn mount(&self) -> io::Result<(Entry, u64)> {
        let entry = self.do_lookup(fuse::ROOT_ID, &CString::new(".").unwrap())?;
        Ok((entry, VFS_MAX_INO))
    }

    fn as_any(&self) -> &dyn Any {
        self
    }
}

macro_rules! scoped_cred {
    ($name:ident, $ty:ty, $syscall_nr:expr) => {
        #[derive(Debug)]
        pub(crate) struct $name;

        impl $name {
            // Changes the effective uid/gid of the current thread to `val`.  Changes
            // the thread's credentials back to root when the returned struct is dropped.
            fn new(val: $ty) -> io::Result<Option<$name>> {
                if val == 0 {
                    // Nothing to do since we are already uid 0.
                    return Ok(None);
                }

                // We want credential changes to be per-thread because otherwise
                // we might interfere with operations being carried out on other
                // threads with different uids/gids.  However, posix requires that
                // all threads in a process share the same credentials.  To do this
                // libc uses signals to ensure that when one thread changes its
                // credentials the other threads do the same thing.
                //
                // So instead we invoke the syscall directly in order to get around
                // this limitation.  Another option is to use the setfsuid and
                // setfsgid systems calls.   However since those calls have no way to
                // return an error, it's preferable to do this instead.

                // This call is safe because it doesn't modify any memory and we
                // check the return value.
                let res = unsafe { libc::syscall($syscall_nr, -1, val, -1) };
                if res == 0 {
                    Ok(Some($name))
                } else {
                    Err(io::Error::last_os_error())
                }
            }
        }

        impl Drop for $name {
            fn drop(&mut self) {
                let res = unsafe { libc::syscall($syscall_nr, -1, 0, -1) };
                if res < 0 {
                    error!(
                        "fuse: failed to change credentials back to root: {}",
                        io::Error::last_os_error(),
                    );
                }
            }
        }
    };
}
scoped_cred!(ScopedUid, libc::uid_t, libc::SYS_setresuid);
scoped_cred!(ScopedGid, libc::gid_t, libc::SYS_setresgid);

struct CapFsetid {}

impl Drop for CapFsetid {
    fn drop(&mut self) {
        if let Err(e) = caps::raise(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID) {
            error!("fail to restore thread cap_fsetid: {}", e);
        };
    }
}

fn drop_cap_fsetid() -> io::Result<Option<CapFsetid>> {
    if !caps::has_cap(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?
    {
        return Ok(None);
    }
    caps::drop(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID)
        .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;
    Ok(Some(CapFsetid {}))
}

fn set_creds(
    uid: libc::uid_t,
    gid: libc::gid_t,
) -> io::Result<(Option<ScopedUid>, Option<ScopedGid>)> {
    // We have to change the gid before we change the uid because if we change the uid first then we
    // lose the capability to change the gid.  However changing back can happen in any order.
    ScopedGid::new(gid).and_then(|gid| Ok((ScopedUid::new(uid)?, gid)))
}

fn ebadf() -> io::Error {
    io::Error::from_raw_os_error(libc::EBADF)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::filesystem::*;
    use crate::api::{Vfs, VfsOptions};
    use caps::{CapSet, Capability};
    use log;
    use std::ops::Deref;
    use vmm_sys_util::{tempdir::TempDir, tempfile::TempFile};

    fn passthroughfs_no_open(cfg: bool) {
        let opts = VfsOptions {
            no_open: cfg,
            ..Default::default()
        };

        let vfs = &Vfs::<AsyncDriver, ()>::new(opts);
        // Assume that fuse kernel supports no_open.
        vfs.init(FsOptions::ZERO_MESSAGE_OPEN).unwrap();

        let fs_cfg = Config {
            do_import: false,
            no_open: cfg,
            ..Default::default()
        };
        let fs = PassthroughFs::new(fs_cfg.clone()).unwrap();
        fs.import().unwrap();
        vfs.mount(Box::new(fs), "/submnt/A").unwrap();

        let p_fs = vfs.get_rootfs("/submnt/A").unwrap().unwrap();
        let any_fs = p_fs.deref().as_any();
        any_fs
            .downcast_ref::<PassthroughFs>()
            .map(|fs| {
                assert_eq!(fs.no_open.load(Ordering::Relaxed), cfg);
            })
            .unwrap();
    }

    #[test]
    fn test_passthroughfs_no_open() {
        passthroughfs_no_open(true);
        passthroughfs_no_open(false);
    }

    #[test]
    fn test_passthroughfs_inode_file_handles() {
        log::set_max_level(log::LevelFilter::Trace);

        match caps::has_cap(None, CapSet::Effective, Capability::CAP_DAC_READ_SEARCH) {
            Ok(false) | Err(_) => {
                println!("invoking open_by_handle_at needs CAP_DAC_READ_SEARCH");
                return;
            }
            Ok(true) => {}
        }

        let source = TempDir::new().expect("Cannot create temporary directory.");
        let parent_path =
            TempDir::new_in(source.as_path()).expect("Cannot create temporary directory.");
        let child_path =
            TempFile::new_in(parent_path.as_path()).expect("Cannot create temporary file.");

        let fs_cfg = Config {
            writeback: true,
            do_import: true,
            no_open: true,
            inode_file_handles: true,
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<AsyncDriver, ()>::new(fs_cfg).unwrap();
        fs.import().unwrap();

        let ctx = Context::default();

        // read a few files to inode map.
        let parent = CString::new(parent_path.as_path().to_str().expect("path to string")).unwrap();
        let p_entry = fs.lookup(&ctx, ROOT_ID, &parent).unwrap();
        let p_inode = p_entry.inode;

        let child = CString::new(child_path.as_path().to_str().expect("path to string")).unwrap();
        let c_entry = fs.lookup(&ctx, p_inode, &child).unwrap();

        // Following test depends on host fs, it's not reliable.
        //let data = fs.inode_map.get(c_entry.inode).unwrap();
        //assert_eq!(matches!(data.file_or_handle, FileOrHandle::Handle(_)), true);

        let (_, duration) = fs.getattr(&ctx, c_entry.inode, None).unwrap();
        assert_eq!(duration, fs.cfg.attr_timeout);

        fs.destroy();
    }
}
