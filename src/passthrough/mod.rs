// Copyright (C) 2020-2022 Alibaba Cloud. All rights reserved.
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
use std::ffi::{CStr, CString, OsString};
use std::fs::File;
use std::io;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::os::fd::{AsFd, BorrowedFd};
use std::os::unix::ffi::OsStringExt;
use std::os::unix::io::{AsRawFd, RawFd};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, Ordering};
use std::sync::{Arc, Mutex, MutexGuard, RwLock, RwLockWriteGuard};
use std::time::Duration;

use vm_memory::{bitmap::BitmapSlice, ByteValued};

pub use self::config::{CachePolicy, Config};
use self::file_handle::{FileHandle, OpenableFileHandle};
use self::inode_store::{InodeId, InodeStore};
use self::mount_fd::MountFds;
use self::statx::{statx, StatExt};
use self::util::{
    ebadf, einval, enosys, eperm, is_dir, is_safe_inode, openat, reopen_fd_through_proc, stat_fd,
    UniqueInodeGenerator,
};
use crate::abi::fuse_abi as fuse;
use crate::abi::fuse_abi::Opcode;
use crate::api::filesystem::Entry;
use crate::api::{
    validate_path_component, BackendFileSystem, CURRENT_DIR_CSTR, EMPTY_CSTR, PARENT_DIR_CSTR,
    PROC_SELF_FD_CSTR, SLASH_ASCII, VFS_MAX_INO,
};

#[cfg(feature = "async-io")]
mod async_io;
mod config;
mod file_handle;
mod inode_store;
mod mount_fd;
mod os_compat;
mod overlay;
mod statx;
mod sync_io;
mod util;

type Inode = u64;
type Handle = u64;

/// Maximum host inode number supported by passthroughfs
const MAX_HOST_INO: u64 = 0x7fff_ffff_ffff;

/**
 * Represents the file associated with an inode (`InodeData`).
 *
 * When obtaining such a file, it may either be a new file (the `Owned` variant), in which case the
 * object's lifetime is static, or it may reference `InodeData.file` (the `Ref` variant), in which
 * case the object's lifetime is that of the respective `InodeData` object.
 */
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

impl AsFd for InodeFile<'_> {
    fn as_fd(&self) -> BorrowedFd<'_> {
        match self {
            Self::Owned(file) => file.as_fd(),
            Self::Ref(file_ref) => file_ref.as_fd(),
        }
    }
}

#[derive(Debug)]
enum InodeHandle {
    File(File),
    Handle(Arc<OpenableFileHandle>),
}

impl InodeHandle {
    fn file_handle(&self) -> Option<&FileHandle> {
        match self {
            InodeHandle::File(_) => None,
            InodeHandle::Handle(h) => Some(h.file_handle().deref()),
        }
    }

    fn get_file(&self) -> io::Result<InodeFile<'_>> {
        match self {
            InodeHandle::File(f) => Ok(InodeFile::Ref(f)),
            InodeHandle::Handle(h) => {
                let f = h.open(libc::O_PATH)?;
                Ok(InodeFile::Owned(f))
            }
        }
    }

    fn open_file(&self, flags: libc::c_int, proc_self_fd: &File) -> io::Result<File> {
        match self {
            InodeHandle::File(f) => reopen_fd_through_proc(f, flags, proc_self_fd),
            InodeHandle::Handle(h) => h.open(flags),
        }
    }

    fn stat(&self) -> io::Result<libc::stat64> {
        match self {
            InodeHandle::File(f) => stat_fd(f, None),
            InodeHandle::Handle(_h) => {
                let file = self.get_file()?;
                stat_fd(&file, None)
            }
        }
    }
}

/// Represents an inode in `PassthroughFs`.
#[derive(Debug)]
pub struct InodeData {
    inode: Inode,
    // Most of these aren't actually files but ¯\_(ツ)_/¯.
    handle: InodeHandle,
    id: InodeId,
    refcount: AtomicU64,
    // File type and mode
    mode: u32,
}

impl InodeData {
    fn new(inode: Inode, f: InodeHandle, refcount: u64, id: InodeId, mode: u32) -> Self {
        InodeData {
            inode,
            handle: f,
            id,
            refcount: AtomicU64::new(refcount),
            mode,
        }
    }

    fn get_file(&self) -> io::Result<InodeFile<'_>> {
        self.handle.get_file()
    }

    fn open_file(&self, flags: libc::c_int, proc_self_fd: &File) -> io::Result<File> {
        self.handle.open_file(flags, proc_self_fd)
    }
}

/// Data structures to manage accessed inodes.
struct InodeMap {
    inodes: RwLock<InodeStore>,
}

impl InodeMap {
    fn new() -> Self {
        InodeMap {
            inodes: RwLock::new(Default::default()),
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
            .cloned()
            .ok_or_else(ebadf)
    }

    fn get_inode_locked(
        inodes: &InodeStore,
        id: &InodeId,
        handle: Option<&FileHandle>,
    ) -> Option<Inode> {
        match handle {
            Some(h) => inodes.inode_by_handle(h).copied(),
            None => inodes.inode_by_id(id).copied(),
        }
    }

    fn get_alt(&self, id: &InodeId, handle: Option<&FileHandle>) -> Option<Arc<InodeData>> {
        // Do not expect poisoned lock here, so safe to unwrap().
        let inodes = self.inodes.read().unwrap();

        Self::get_alt_locked(inodes.deref(), id, handle)
    }

    fn get_alt_locked(
        inodes: &InodeStore,
        id: &InodeId,
        handle: Option<&FileHandle>,
    ) -> Option<Arc<InodeData>> {
        handle
            .and_then(|h| inodes.get_by_handle(h))
            .or_else(|| {
                inodes.get_by_id(id).filter(|data| {
                    // When we have to fall back to looking up an inode by its IDs, ensure that
                    // we hit an entry that does not have a file handle.  Entries with file
                    // handles must also have a handle alt key, so if we have not found it by
                    // that handle alt key, we must have found an entry with a mismatching
                    // handle; i.e. an entry for a different file, even though it has the same
                    // inode ID.
                    // (This can happen when we look up a new file that has reused the inode ID
                    // of some previously unlinked inode we still have in `.inodes`.)
                    handle.is_none() || data.handle.file_handle().is_none()
                })
            })
            .cloned()
    }

    fn get_map_mut(&self) -> RwLockWriteGuard<InodeStore> {
        // Do not expect poisoned lock here, so safe to unwrap().
        self.inodes.write().unwrap()
    }

    fn insert(&self, data: Arc<InodeData>) {
        let mut inodes = self.get_map_mut();

        Self::insert_locked(inodes.deref_mut(), data)
    }

    fn insert_locked(inodes: &mut InodeStore, data: Arc<InodeData>) {
        inodes.insert(data);
    }
}

struct HandleData {
    inode: Inode,
    file: File,
    lock: Mutex<()>,
    open_flags: AtomicU32,
}

impl HandleData {
    fn new(inode: Inode, file: File, flags: u32) -> Self {
        HandleData {
            inode,
            file,
            lock: Mutex::new(()),
            open_flags: AtomicU32::new(flags),
        }
    }

    fn get_file(&self) -> &File {
        &self.file
    }

    fn get_file_mut(&self) -> (MutexGuard<()>, &File) {
        (self.lock.lock().unwrap(), &self.file)
    }

    fn borrow_fd(&self) -> BorrowedFd {
        self.file.as_fd()
    }

    fn get_flags(&self) -> u32 {
        self.open_flags.load(Ordering::Relaxed)
    }

    fn set_flags(&self, flags: u32) {
        self.open_flags.store(flags, Ordering::Relaxed);
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
            .cloned()
            .ok_or_else(ebadf)
    }
}

/// A file system that simply "passes through" all requests it receives to the underlying file
/// system.
///
/// To keep the implementation simple it servers the contents of its root directory. Users
/// that wish to serve only a specific directory should set up the environment so that that
/// directory ends up as the root of the file system process. One way to accomplish this is via a
/// combination of mount namespaces and the pivot_root system call.
pub struct PassthroughFs<S: BitmapSlice + Send + Sync = ()> {
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

    // Use to generate unique inode
    ino_allocator: UniqueInodeGenerator,
    // Maps mount IDs to an open FD on the respective ID for the purpose of open_by_handle_at().
    mount_fds: MountFds,

    // File descriptor pointing to the `/proc/self/fd` directory. This is used to convert an fd from
    // `inodes` into one that can go into `handles`. This is accomplished by reading the
    // `/proc/self/fd/{}` symlink. We keep an open fd here in case the file system tree that we are meant
    // to be serving doesn't have access to `/proc/self/fd`.
    proc_self_fd: File,

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

    // Whether seal_size is enabled.
    seal_size: AtomicBool,

    // Whether per-file DAX feature is enabled.
    // Init from guest kernel Init cmd of fuse fs.
    perfile_dax: AtomicBool,

    dir_entry_timeout: Duration,
    dir_attr_timeout: Duration,

    cfg: Config,

    phantom: PhantomData<S>,
}

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    /// Create a Passthrough file system instance.
    pub fn new(mut cfg: Config) -> io::Result<PassthroughFs<S>> {
        if cfg.no_open && cfg.cache_policy != CachePolicy::Always {
            warn!("passthroughfs: no_open only work with cache=always, reset to open mode");
            cfg.no_open = false;
        }
        if cfg.writeback && cfg.cache_policy == CachePolicy::Never {
            warn!(
                "passthroughfs: writeback cache conflicts with cache=none, reset to no_writeback"
            );
            cfg.writeback = false;
        }

        // Safe because this is a constant value and a valid C string.
        let proc_self_fd_cstr = unsafe { CStr::from_bytes_with_nul_unchecked(PROC_SELF_FD_CSTR) };
        let proc_self_fd = Self::open_file(
            &libc::AT_FDCWD,
            proc_self_fd_cstr,
            libc::O_PATH | libc::O_NOFOLLOW | libc::O_CLOEXEC,
            0,
        )?;

        let (dir_entry_timeout, dir_attr_timeout) =
            match (cfg.dir_entry_timeout, cfg.dir_attr_timeout) {
                (Some(e), Some(a)) => (e, a),
                (Some(e), None) => (e, cfg.attr_timeout),
                (None, Some(a)) => (cfg.entry_timeout, a),
                (None, None) => (cfg.entry_timeout, cfg.attr_timeout),
            };

        let mount_fds = MountFds::new(None)?;

        Ok(PassthroughFs {
            inode_map: InodeMap::new(),
            next_inode: AtomicU64::new(fuse::ROOT_ID + 1),
            ino_allocator: UniqueInodeGenerator::new(),

            handle_map: HandleMap::new(),
            next_handle: AtomicU64::new(1),

            mount_fds,
            proc_self_fd,

            writeback: AtomicBool::new(false),
            no_open: AtomicBool::new(false),
            no_opendir: AtomicBool::new(false),
            killpriv_v2: AtomicBool::new(false),
            no_readdir: AtomicBool::new(cfg.no_readdir),
            seal_size: AtomicBool::new(cfg.seal_size),
            perfile_dax: AtomicBool::new(false),
            dir_entry_timeout,
            dir_attr_timeout,
            cfg,

            phantom: PhantomData,
        })
    }

    /// Initialize the Passthrough file system.
    pub fn import(&self) -> io::Result<()> {
        let root = CString::new(self.cfg.root_dir.as_str()).expect("CString::new failed");

        let (path_fd, handle_opt, st) = Self::open_file_and_handle(self, &libc::AT_FDCWD, &root)
            .map_err(|e| {
                error!("fuse: import: failed to get file or handle: {:?}", e);
                e
            })?;
        let id = InodeId::from_stat(&st);
        let handle = if let Some(h) = handle_opt {
            InodeHandle::Handle(self.to_openable_handle(h)?)
        } else {
            InodeHandle::File(path_fd)
        };

        // Safe because this doesn't modify any memory and there is no need to check the return
        // value because this system call always succeeds. We need to clear the umask here because
        // we want the client to be able to set all the bits in the mode.
        unsafe { libc::umask(0o000) };

        // Not sure why the root inode gets a refcount of 2 but that's what libfuse does.
        self.inode_map.insert(Arc::new(InodeData::new(
            fuse::ROOT_ID,
            handle,
            2,
            id,
            st.st.st_mode,
        )));

        Ok(())
    }

    /// Get the list of file descriptors which should be reserved across live upgrade.
    pub fn keep_fds(&self) -> Vec<RawFd> {
        vec![self.proc_self_fd.as_raw_fd()]
    }

    fn readlinkat(dfd: i32, pathname: &CStr) -> io::Result<PathBuf> {
        let mut buf = Vec::with_capacity(libc::PATH_MAX as usize);

        // Safe because the kernel will only write data to buf and we check the return value
        let buf_read = unsafe {
            libc::readlinkat(
                dfd,
                pathname.as_ptr(),
                buf.as_mut_ptr() as *mut libc::c_char,
                buf.capacity(),
            )
        };
        if buf_read < 0 {
            error!("fuse: readlinkat error");
            return Err(io::Error::last_os_error());
        }

        // Safe because we trust the value returned by kernel.
        unsafe { buf.set_len(buf_read as usize) };
        buf.shrink_to_fit();

        // Be careful:
        // - readlink() does not append a terminating null byte to buf
        // - OsString instances are not NUL terminated
        Ok(PathBuf::from(OsString::from_vec(buf)))
    }

    /// Get the file pathname corresponding to the Inode
    /// This function is used by Nydus blobfs
    pub fn readlinkat_proc_file(&self, inode: Inode) -> io::Result<PathBuf> {
        let data = self.inode_map.get(inode)?;
        let file = data.get_file()?;
        let pathname = CString::new(format!("{}", file.as_raw_fd()))
            .map_err(|e| io::Error::new(io::ErrorKind::InvalidData, e))?;

        Self::readlinkat(self.proc_self_fd.as_raw_fd(), &pathname)
    }

    fn create_file_excl(
        dir: &impl AsRawFd,
        pathname: &CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<Option<File>> {
        match openat(dir, pathname, flags | libc::O_CREAT | libc::O_EXCL, mode) {
            Ok(file) => Ok(Some(file)),
            Err(err) => {
                // Ignore the error if the file exists and O_EXCL is not present in `flags`.
                if err.kind() == io::ErrorKind::AlreadyExists {
                    if (flags & libc::O_EXCL) != 0 {
                        return Err(err);
                    }
                    return Ok(None);
                }
                Err(err)
            }
        }
    }

    fn open_file(dfd: &impl AsRawFd, pathname: &CStr, flags: i32, mode: u32) -> io::Result<File> {
        openat(dfd, pathname, flags, mode)
    }

    fn open_file_restricted(
        &self,
        dir: &impl AsRawFd,
        pathname: &CStr,
        flags: i32,
        mode: u32,
    ) -> io::Result<File> {
        let flags = libc::O_NOFOLLOW | libc::O_CLOEXEC | flags;

        // TODO
        //if self.os_facts.has_openat2 {
        //    oslib::do_open_relative_to(dir, pathname, flags, mode)
        //} else {
        openat(dir, pathname, flags, mode)
        //}
    }

    /// Create a File or File Handle for `name` under directory `dir_fd` to support `lookup()`.
    fn open_file_and_handle(
        &self,
        dir: &impl AsRawFd,
        name: &CStr,
    ) -> io::Result<(File, Option<FileHandle>, StatExt)> {
        let path_file = self.open_file_restricted(dir, name, libc::O_PATH, 0)?;
        let st = statx(&path_file, None)?;
        let handle = if self.cfg.inode_file_handles {
            FileHandle::from_fd(&path_file)?
        } else {
            None
        };

        Ok((path_file, handle, st))
    }

    fn to_openable_handle(&self, fh: FileHandle) -> io::Result<Arc<OpenableFileHandle>> {
        fh.into_openable(&self.mount_fds, |fd, flags, _mode| {
            reopen_fd_through_proc(&fd, flags, &self.proc_self_fd)
        })
        .map(Arc::new)
        .map_err(|e| {
            if !e.silent() {
                error!("{}", e);
            }
            e.into_inner()
        })
    }

    fn allocate_inode(
        &self,
        inodes: &InodeStore,
        id: &InodeId,
        handle_opt: Option<&FileHandle>,
    ) -> io::Result<Inode> {
        if !self.cfg.use_host_ino {
            // If the inode has already been assigned before, the new inode is not reassigned,
            // ensuring that the same file is always the same inode
            Ok(InodeMap::get_inode_locked(inodes, id, handle_opt)
                .unwrap_or_else(|| self.next_inode.fetch_add(1, Ordering::Relaxed)))
        } else {
            let inode = if id.ino > MAX_HOST_INO {
                // Prefer looking for previous mappings from memory
                match InodeMap::get_inode_locked(inodes, id, handle_opt) {
                    Some(ino) => ino,
                    None => self.ino_allocator.get_unique_inode(id)?,
                }
            } else {
                self.ino_allocator.get_unique_inode(id)?
            };

            Ok(inode)
        }
    }

    fn do_lookup(&self, parent: Inode, name: &CStr) -> io::Result<Entry> {
        let name =
            if parent == fuse::ROOT_ID && name.to_bytes_with_nul().starts_with(PARENT_DIR_CSTR) {
                // Safe as this is a constant value and a valid C string.
                CStr::from_bytes_with_nul(CURRENT_DIR_CSTR).unwrap()
            } else {
                name
            };

        let dir = self.inode_map.get(parent)?;
        let dir_file = dir.get_file()?;
        let (path_fd, handle_opt, st) = Self::open_file_and_handle(self, &dir_file, name)?;
        let id = InodeId::from_stat(&st);

        let mut found = None;
        'search: loop {
            match self.inode_map.get_alt(&id, handle_opt.as_ref()) {
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
            let handle = if let Some(h) = handle_opt.clone() {
                InodeHandle::Handle(self.to_openable_handle(h)?)
            } else {
                InodeHandle::File(path_fd)
            };

            // Write guard get_alt_locked() and insert_lock() to avoid race conditions.
            let mut inodes = self.inode_map.get_map_mut();

            // Lookup inode_map again after acquiring the inode_map lock, as there might be another
            // racing thread already added an inode with the same id while we're not holding
            // the lock. If so just use the newly added inode, otherwise the inode will be replaced
            // and results in EBADF.
            match InodeMap::get_alt_locked(inodes.deref(), &id, handle_opt.as_ref()) {
                Some(data) => {
                    // An inode was added concurrently while we did not hold a lock on
                    // `self.inodes_map`, so we use that instead. `handle` will be dropped.
                    data.refcount.fetch_add(1, Ordering::Relaxed);
                    data.inode
                }
                None => {
                    let inode = self.allocate_inode(inodes.deref(), &id, handle_opt.as_ref())?;

                    if inode > VFS_MAX_INO {
                        error!("fuse: max inode number reached: {}", VFS_MAX_INO);
                        return Err(io::Error::new(
                            io::ErrorKind::Other,
                            format!("max inode number reached: {VFS_MAX_INO}"),
                        ));
                    }

                    InodeMap::insert_locked(
                        inodes.deref_mut(),
                        Arc::new(InodeData::new(inode, handle, 1, id, st.st.st_mode)),
                    );
                    inode
                }
            }
        };

        let (entry_timeout, attr_timeout) = if is_dir(st.st.st_mode) {
            (self.dir_entry_timeout, self.dir_attr_timeout)
        } else {
            (self.cfg.entry_timeout, self.cfg.attr_timeout)
        };

        // Whether to enable file DAX according to the value of dax_file_size
        let mut attr_flags: u32 = 0;
        if let Some(dax_file_size) = self.cfg.dax_file_size {
            // st.stat.st_size is i64
            if self.perfile_dax.load(Ordering::Relaxed)
                && st.st.st_size >= 0x0
                && st.st.st_size as u64 >= dax_file_size
            {
                attr_flags |= fuse::FUSE_ATTR_DAX;
            }
        }

        Ok(Entry {
            inode,
            generation: 0,
            attr: st.st,
            attr_flags,
            attr_timeout,
            entry_timeout,
        })
    }

    fn forget_one(&self, inodes: &mut InodeStore, inode: Inode, count: u64) {
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

                // Synchronizes with the acquire load in `do_lookup`.
                if data
                    .refcount
                    .compare_exchange(curr, new, Ordering::AcqRel, Ordering::Acquire)
                    .is_ok()
                {
                    if new == 0 {
                        // We just removed the last refcount for this inode.
                        // The allocated inode number should be kept in the map when use_host_ino
                        // is false or host inode(don't use the virtual 56bit inode) is bigger than MAX_HOST_INO.
                        let keep_mapping = !self.cfg.use_host_ino || data.id.ino > MAX_HOST_INO;
                        inodes.remove(&inode, keep_mapping);
                    }
                    break;
                }
            }
        }
    }

    fn do_release(&self, inode: Inode, handle: Handle) -> io::Result<()> {
        self.handle_map.release(handle, inode)
    }

    // Validate a path component, same as the one in vfs layer, but only do the validation if this
    // passthroughfs is used without vfs layer, to avoid double validation.
    fn validate_path_component(&self, name: &CStr) -> io::Result<()> {
        // !self.cfg.do_import means we're under vfs, and vfs has already done the validation
        if !self.cfg.do_import {
            return Ok(());
        }
        validate_path_component(name)
    }

    // When seal_size is set, we don't allow operations that could change file size nor allocate
    // space beyond EOF
    fn seal_size_check(
        &self,
        opcode: Opcode,
        file_size: u64,
        offset: u64,
        size: u64,
        mode: i32,
    ) -> io::Result<()> {
        if offset.checked_add(size).is_none() {
            error!(
                "fuse: {:?}: invalid `offset` + `size` ({}+{}) overflows u64::MAX",
                opcode, offset, size
            );
            return Err(einval());
        }

        match opcode {
            // write should not exceed the file size.
            Opcode::Write => {
                if size + offset > file_size {
                    return Err(eperm());
                }
            }

            Opcode::Fallocate => {
                let op = mode & !(libc::FALLOC_FL_KEEP_SIZE | libc::FALLOC_FL_UNSHARE_RANGE);
                match op {
                    // Allocate, punch and zero, must not change file size.
                    0 | libc::FALLOC_FL_PUNCH_HOLE | libc::FALLOC_FL_ZERO_RANGE => {
                        if size + offset > file_size {
                            return Err(eperm());
                        }
                    }
                    // collapse and insert will change file size, forbid.
                    libc::FALLOC_FL_COLLAPSE_RANGE | libc::FALLOC_FL_INSERT_RANGE => {
                        return Err(eperm());
                    }
                    // Invalid operation
                    _ => return Err(einval()),
                }
            }

            // setattr operation should be handled in setattr handler.
            _ => return Err(enosys()),
        }

        Ok(())
    }

    fn get_writeback_open_flags(&self, flags: i32) -> i32 {
        let mut new_flags = flags;
        let writeback = self.writeback.load(Ordering::Relaxed);

        // When writeback caching is enabled, the kernel may send read requests even if the
        // userspace program opened the file write-only. So we need to ensure that we have opened
        // the file for reading as well as writing.
        if writeback && flags & libc::O_ACCMODE == libc::O_WRONLY {
            new_flags &= !libc::O_ACCMODE;
            new_flags |= libc::O_RDWR;
        }

        // When writeback caching is enabled the kernel is responsible for handling `O_APPEND`.
        // However, this breaks atomicity as the file may have changed on disk, invalidating the
        // cached copy of the data in the kernel and the offset that the kernel thinks is the end of
        // the file. Just allow this for now as it is the user's responsibility to enable writeback
        // caching only for directories that are not shared. It also means that we need to clear the
        // `O_APPEND` flag.
        if writeback && flags & libc::O_APPEND != 0 {
            new_flags &= !libc::O_APPEND;
        }

        new_flags
    }
}

#[cfg(not(feature = "async-io"))]
impl<S: BitmapSlice + Send + Sync + 'static> BackendFileSystem for PassthroughFs<S> {
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

fn set_creds(
    uid: libc::uid_t,
    gid: libc::gid_t,
) -> io::Result<(Option<ScopedUid>, Option<ScopedGid>)> {
    // We have to change the gid before we change the uid because if we change the uid first then we
    // lose the capability to change the gid.  However changing back can happen in any order.
    ScopedGid::new(gid).and_then(|gid| Ok((ScopedUid::new(uid)?, gid)))
}

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
        .map_err(|_e| io::Error::new(io::ErrorKind::PermissionDenied, "no CAP_FSETID capability"))?
    {
        return Ok(None);
    }
    caps::drop(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID).map_err(|_e| {
        io::Error::new(
            io::ErrorKind::PermissionDenied,
            "failed to drop CAP_FSETID capability",
        )
    })?;
    Ok(Some(CapFsetid {}))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::abi::fuse_abi::CreateIn;
    use crate::api::filesystem::*;
    use crate::api::{Vfs, VfsOptions};
    use caps::{CapSet, Capability};
    use log;
    use std::io::{Read, Seek, SeekFrom, Write};
    use std::ops::Deref;
    use std::os::unix::prelude::MetadataExt;
    use vmm_sys_util::{tempdir::TempDir, tempfile::TempFile};

    fn prepare_passthroughfs() -> PassthroughFs {
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let parent_path =
            TempDir::new_in(source.as_path()).expect("Cannot create temporary directory.");
        let _child_path =
            TempFile::new_in(parent_path.as_path()).expect("Cannot create temporary file.");

        let fs_cfg = Config {
            writeback: true,
            do_import: true,
            no_open: true,
            inode_file_handles: false,
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();

        fs
    }

    fn passthroughfs_no_open(cfg: bool) {
        let opts = VfsOptions {
            no_open: cfg,
            ..Default::default()
        };

        let vfs = &Vfs::new(opts);
        // Assume that fuse kernel supports no_open.
        vfs.init(FsOptions::ZERO_MESSAGE_OPEN).unwrap();

        let fs_cfg = Config {
            do_import: false,
            no_open: cfg,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg.clone()).unwrap();
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
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();

        let ctx = Context::default();

        // read a few files to inode map.
        let parent = CString::new(
            parent_path
                .as_path()
                .file_name()
                .unwrap()
                .to_str()
                .expect("path to string"),
        )
        .unwrap();
        let p_entry = fs.lookup(&ctx, ROOT_ID, &parent).unwrap();
        let p_inode = p_entry.inode;

        let child = CString::new(
            child_path
                .as_path()
                .file_name()
                .unwrap()
                .to_str()
                .expect("path to string"),
        )
        .unwrap();
        let c_entry = fs.lookup(&ctx, p_inode, &child).unwrap();

        // Following test depends on host fs, it's not reliable.
        //let data = fs.inode_map.get(c_entry.inode).unwrap();
        //assert_eq!(matches!(data.handle, InodeHandle::Handle(_)), true);

        let (_, duration) = fs.getattr(&ctx, c_entry.inode, None).unwrap();
        assert_eq!(duration, fs.cfg.attr_timeout);

        fs.destroy();
    }

    #[test]
    fn test_lookup_escape_root() {
        let fs = prepare_passthroughfs();
        let ctx = Context::default();

        let name = CString::new("..").unwrap();
        let entry = fs.lookup(&ctx, ROOT_ID, &name).unwrap();
        assert_eq!(entry.inode, ROOT_ID);
    }

    #[test]
    fn test_get_writeback_open_flags() {
        // prepare a fs with writeback cache and open being true, so O_WRONLY should be promoted to
        // O_RDWR, as writeback may read files even if file being opened with write-only. And
        // O_APPEND should be cleared as well.
        let mut fs = prepare_passthroughfs();
        fs.writeback = AtomicBool::new(true);
        fs.no_open = AtomicBool::new(false);

        assert!(fs.writeback.load(Ordering::Relaxed));
        assert!(!fs.no_open.load(Ordering::Relaxed));

        let flags = libc::O_RDWR;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDWR);

        let flags = libc::O_RDONLY;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDONLY);

        let flags = libc::O_WRONLY;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDWR);

        let flags = libc::O_RDWR | libc::O_APPEND;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDWR);

        let flags = libc::O_RDONLY | libc::O_APPEND;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDONLY);

        let flags = libc::O_WRONLY | libc::O_APPEND;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDWR);

        // prepare a fs with writeback cache disabled, open flags should not change
        let mut fs = prepare_passthroughfs();
        fs.writeback = AtomicBool::new(false);
        fs.no_open = AtomicBool::new(false);

        assert!(!fs.writeback.load(Ordering::Relaxed));
        assert!(!fs.no_open.load(Ordering::Relaxed));

        let flags = libc::O_RDWR;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDWR);

        let flags = libc::O_RDONLY;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_RDONLY);

        let flags = libc::O_WRONLY;
        assert_eq!(fs.get_writeback_open_flags(flags), libc::O_WRONLY);

        let flags = libc::O_RDWR | libc::O_APPEND;
        assert_eq!(
            fs.get_writeback_open_flags(flags),
            libc::O_RDWR | libc::O_APPEND
        );

        let flags = libc::O_RDONLY | libc::O_APPEND;
        assert_eq!(
            fs.get_writeback_open_flags(flags),
            libc::O_RDONLY | libc::O_APPEND
        );

        let flags = libc::O_WRONLY | libc::O_APPEND;
        assert_eq!(
            fs.get_writeback_open_flags(flags),
            libc::O_WRONLY | libc::O_APPEND
        );
    }

    #[test]
    fn test_writeback_open_and_create() {
        // prepare a fs with writeback cache and open being true, so a write-only opened file
        // should have read permission as well.
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let _ = std::process::Command::new("sh")
            .arg("-c")
            .arg(format!("touch {}/existfile", source.as_path().to_str().unwrap()).as_str())
            .output()
            .unwrap();
        let fs_cfg = Config {
            writeback: true,
            do_import: true,
            no_open: false,
            inode_file_handles: false,
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            ..Default::default()
        };
        let mut fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.writeback = AtomicBool::new(true);
        fs.no_open = AtomicBool::new(false);
        fs.import().unwrap();

        assert!(fs.writeback.load(Ordering::Relaxed));
        assert!(!fs.no_open.load(Ordering::Relaxed));

        let ctx = Context::default();

        // Create a new file with O_WRONLY, and make sure we can read it as well.
        let fname = CString::new("testfile").unwrap();
        let args = CreateIn {
            flags: libc::O_WRONLY as u32,
            mode: 0644,
            umask: 0,
            fuse_flags: 0,
        };
        let (entry, handle, _, _) = fs.create(&ctx, ROOT_ID, &fname, args).unwrap();
        let handle_data = fs.handle_map.get(handle.unwrap(), entry.inode).unwrap();
        let (_guard, mut f) = handle_data.get_file_mut();
        let mut buf = [0; 4];
        // Buggy code return EBADF on read
        let n = f.read(&mut buf).unwrap();
        assert_eq!(n, 0);

        // Then Open an existing file with O_WRONLY, we should be able to read it as well.
        let fname = CString::new("existfile").unwrap();
        let entry = fs.lookup(&ctx, ROOT_ID, &fname).unwrap();
        let (handle, _, _) = fs
            .open(&ctx, entry.inode, libc::O_WRONLY as u32, 0)
            .unwrap();
        let handle_data = fs.handle_map.get(handle.unwrap(), entry.inode).unwrap();
        let (_guard, mut f) = handle_data.get_file_mut();
        let mut buf = [0; 4];
        let n = f.read(&mut buf).unwrap();
        assert_eq!(n, 0);
    }

    #[test]
    fn test_passthroughfs_dir_timeout() {
        log::set_max_level(log::LevelFilter::Trace);

        let source = TempDir::new().expect("Cannot create temporary directory.");
        let parent_path =
            TempDir::new_in(source.as_path()).expect("Cannot create temporary directory.");
        let child_path =
            TempFile::new_in(parent_path.as_path()).expect("Cannot create temporary file.");

        // passthroughfs with cache=none, but non-zero dir entry/attr timeout.
        let fs_cfg = Config {
            writeback: false,
            do_import: true,
            no_open: false,
            root_dir: source
                .as_path()
                .to_str()
                .expect("source path to string")
                .to_string(),
            cache_policy: CachePolicy::Never,
            entry_timeout: Duration::from_secs(0),
            attr_timeout: Duration::from_secs(0),
            dir_entry_timeout: Some(Duration::from_secs(1)),
            dir_attr_timeout: Some(Duration::from_secs(2)),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        fs.import().unwrap();

        let ctx = Context::default();

        // parent entry should have non-zero timeouts
        let parent = CString::new(
            parent_path
                .as_path()
                .file_name()
                .unwrap()
                .to_str()
                .expect("path to string"),
        )
        .unwrap();
        let p_entry = fs.lookup(&ctx, ROOT_ID, &parent).unwrap();
        assert_eq!(p_entry.entry_timeout, Duration::from_secs(1));
        assert_eq!(p_entry.attr_timeout, Duration::from_secs(2));

        // regular file has zero timeout value
        let child = CString::new(
            child_path
                .as_path()
                .file_name()
                .unwrap()
                .to_str()
                .expect("path to string"),
        )
        .unwrap();
        let c_entry = fs.lookup(&ctx, p_entry.inode, &child).unwrap();
        assert_eq!(c_entry.entry_timeout, Duration::from_secs(0));
        assert_eq!(c_entry.attr_timeout, Duration::from_secs(0));

        fs.destroy();
    }

    #[test]
    fn test_stable_inode() {
        use std::os::unix::fs::MetadataExt;
        let source = TempDir::new().expect("Cannot create temporary directory.");
        let child_path = TempFile::new_in(source.as_path()).expect("Cannot create temporary file.");
        let child = CString::new(
            child_path
                .as_path()
                .file_name()
                .unwrap()
                .to_str()
                .expect("path to string"),
        )
        .unwrap();
        let meta = child_path.as_file().metadata().unwrap();
        let ctx = Context::default();
        {
            let fs_cfg = Config {
                writeback: true,
                do_import: true,
                no_open: true,
                inode_file_handles: false,
                root_dir: source
                    .as_path()
                    .to_str()
                    .expect("source path to string")
                    .to_string(),
                ..Default::default()
            };
            let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
            fs.import().unwrap();
            let entry = fs.lookup(&ctx, ROOT_ID, &child).unwrap();
            assert_eq!(entry.inode, ROOT_ID + 1);
            fs.forget(&ctx, entry.inode, 1);
            let entry = fs.lookup(&ctx, ROOT_ID, &child).unwrap();
            assert_eq!(entry.inode, ROOT_ID + 1);
        }
        {
            let fs_cfg = Config {
                writeback: true,
                do_import: true,
                no_open: true,
                inode_file_handles: false,
                root_dir: source
                    .as_path()
                    .to_str()
                    .expect("source path to string")
                    .to_string(),
                use_host_ino: true,
                ..Default::default()
            };
            let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
            fs.import().unwrap();
            let entry = fs.lookup(&ctx, ROOT_ID, &child).unwrap();
            assert_eq!(entry.inode & MAX_HOST_INO, meta.ino());
            let inode_store = fs.inode_map.get_map_mut();
            let inode_data = inode_store.get(&entry.inode).unwrap();
            assert!(inode_store.inode_by_id(&inode_data.id).is_some());
            let id = inode_data.id.clone();
            drop(inode_store);

            fs.forget(&ctx, entry.inode, 1);
            let inode_store = fs.inode_map.get_map_mut();
            assert!(inode_store.get(&entry.inode).is_none());
            assert!(inode_store.inode_by_id(&id).is_none());
            drop(inode_store);

            let entry = fs.lookup(&ctx, ROOT_ID, &child).unwrap();
            assert_eq!(entry.inode & MAX_HOST_INO, meta.ino());
        }
    }

    #[test]
    fn test_allocation_inode_locked() {
        {
            let fs = prepare_passthroughfs();
            let m = InodeStore::default();
            let id = InodeId {
                ino: MAX_HOST_INO + 1,
                dev: 1,
                mnt: 1,
            };

            // Default
            let inode = fs.allocate_inode(&m, &id, None).unwrap();
            assert_eq!(inode, 2);
        }

        {
            let mut fs = prepare_passthroughfs();
            fs.cfg.use_host_ino = true;
            let m = InodeStore::default();
            let id = InodeId {
                ino: 12345,
                dev: 1,
                mnt: 1,
            };
            // direct return host inode 12345
            let inode = fs.allocate_inode(&m, &id, None).unwrap();
            assert_eq!(inode & MAX_HOST_INO, 12345)
        }

        {
            let mut fs = prepare_passthroughfs();
            fs.cfg.use_host_ino = true;
            let mut m = InodeStore::default();
            let id = InodeId {
                ino: MAX_HOST_INO + 1,
                dev: 1,
                mnt: 1,
            };
            // allocate a virtual inode
            let inode = fs.allocate_inode(&m, &id, None).unwrap();
            assert_eq!(inode & MAX_HOST_INO, 2);
            let file = TempFile::new().expect("Cannot create temporary file.");
            let mode = file.as_file().metadata().unwrap().mode();
            let inode_data =
                InodeData::new(inode, InodeHandle::File(file.into_file()), 1, id, mode);
            m.insert(Arc::new(inode_data));
            let inode = fs.allocate_inode(&m, &id, None).unwrap();
            assert_eq!(inode & MAX_HOST_INO, 2);
        }
    }

    #[test]
    fn test_validate_virtiofs_config() {
        // cache=none + writeback, writeback should be disabled
        let fs_cfg = Config {
            writeback: true,
            cache_policy: CachePolicy::Never,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        assert!(!fs.cfg.writeback);

        // cache=none + no_open, no_open should be disabled
        let fs_cfg = Config {
            no_open: true,
            cache_policy: CachePolicy::Never,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        assert!(!fs.cfg.no_open);

        // cache=auto + no_open, no_open should be disabled
        let fs_cfg = Config {
            no_open: true,
            cache_policy: CachePolicy::Auto,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        assert!(!fs.cfg.no_open);

        // cache=always + no_open, no_open should be set
        let fs_cfg = Config {
            no_open: true,
            cache_policy: CachePolicy::Always,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        assert!(fs.cfg.no_open);

        // cache=none + no_open + writeback, no_open and writeback should be disabled
        let fs_cfg = Config {
            no_open: true,
            writeback: true,
            cache_policy: CachePolicy::Never,
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg).unwrap();
        assert!(!fs.cfg.no_open);
        assert!(!fs.cfg.writeback);
    }

    #[test]
    fn test_generic_read_write_noopen() {
        let tmpdir = TempDir::new().expect("Cannot create temporary directory.");
        // Prepare passthrough fs.
        let fs_cfg = Config {
            do_import: false,
            no_open: true,
            root_dir: tmpdir.as_path().to_string_lossy().to_string(),
            ..Default::default()
        };
        let fs = PassthroughFs::<()>::new(fs_cfg.clone()).unwrap();
        fs.import().unwrap();
        fs.init(FsOptions::ZERO_MESSAGE_OPEN).unwrap();
        fs.mount().unwrap();

        // Create a new file for testing.
        let ctx = Context::default();
        let createin = CreateIn {
            flags: libc::O_CREAT as u32,
            mode: 0o644,
            umask: 0,
            fuse_flags: 0,
        };
        let file_name = CString::new("test_file").unwrap();

        let (entry, _, _, _) = fs
            .create(&ctx, ROOT_ID, file_name.as_c_str(), createin)
            .unwrap();
        let ino = entry.inode;
        assert_ne!(ino, 0);
        assert_ne!(ino, ROOT_ID);

        // Write on the inode
        let data = b"hello world";
        // Write to one intermidiate temp file.
        let buffer_file = TempFile::new().expect("Cannot create temporary file.");
        let mut buffer_file = buffer_file.into_file();
        buffer_file.write_all(data).unwrap();
        let _ = buffer_file.flush();

        // Read back and check.
        let mut newbuf = Vec::new();
        buffer_file.seek(SeekFrom::Start(0)).unwrap();
        buffer_file.read_to_end(&mut newbuf).unwrap();
        assert_eq!(newbuf, data);

        // Call fs.write to write content to the file
        buffer_file.seek(SeekFrom::Start(0)).unwrap();
        let write_sz = fs
            .write(
                &ctx,
                ino,
                0,
                &mut buffer_file,
                data.len() as u32,
                0,
                None,
                false,
                0,
                0,
            )
            .unwrap();
        assert_eq!(write_sz, data.len());

        // Create a new temp file as read buffer.
        let read_buffer_file = TempFile::new().expect("Cannot create temporary file.");
        let mut read_buffer_file = read_buffer_file.into_file();
        let read_sz = fs
            .read(
                &ctx,
                ino,
                0,
                &mut read_buffer_file,
                data.len() as u32,
                0,
                None,
                0,
            )
            .unwrap();
        assert_eq!(read_sz, data.len());

        read_buffer_file.seek(SeekFrom::Start(0)).unwrap();
        let mut newbuf = Vec::new();
        read_buffer_file.read_to_end(&mut newbuf).unwrap();
        assert_eq!(newbuf, data);
    }
}
