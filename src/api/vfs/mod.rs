// Copyright 2020 Ant Financial. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! A union file system which combines multiple backend file systems into one.
//!
//! A simple union file system with limited functionality, which
//! 1. uses pseudo fs to maintain the directory structures
//! 2. supports mounting a file system at "/" or and subdirectory
//! 3. supports mounting multiple file systems at different paths
//! 4. remounting another file system at the same path will evict the old one
//! 5. doesn't support recursive mounts. If /a is a mounted file system, you can't
//!    mount another file systems under /a.
//!
//! Its main usage is to avoid virtio-fs device hotplug. With this simple union fs,
//! a new backend file system could be mounted onto a subdirectory, instead of hot-adding
//! another virtio-fs device. This is very convenient to manage container images at runtime.

use std::any::Any;
use std::collections::HashMap;
use std::ffi::CStr;
use std::fmt;
use std::io;
use std::io::{Error, ErrorKind, Result};
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use arc_swap::ArcSwap;

use crate::abi::fuse_abi::*;
use crate::api::filesystem::*;
use crate::api::pseudo_fs::PseudoFs;

#[cfg(feature = "async-io")]
mod async_io;
mod sync_io;

/// Current directory
pub const CURRENT_DIR_CSTR: &[u8] = b".\0";
/// Parent directory
pub const PARENT_DIR_CSTR: &[u8] = b"..\0";
/// Emptry CSTR
pub const EMPTY_CSTR: &[u8] = b"\0";
/// Proc fd directory
pub const PROC_SELF_FD_CSTR: &[u8] = b"/proc/self/fd\0";
/// ASCII for slash('/')
pub const SLASH_ASCII: u8 = 47;

/// Maximum inode number supported by the VFS for backend file system
pub const VFS_MAX_INO: u64 = 0xff_ffff_ffff_ffff;

// The 64bit inode number for VFS is divided into two parts:
// 1. an 8-bit file-system index, to identify mounted backend file systems.
// 2. the left bits are reserved for backend file systems, and it's limited to VFS_MAX_INO.
const VFS_INDEX_SHIFT: u8 = 56;
const VFS_PSEUDO_FS_IDX: VfsIndex = 0;

type ArcBackFs = Arc<BackFileSystem>;
type ArcSuperBlock = ArcSwap<Vec<Option<Arc<BackFileSystem>>>>;
type VfsEitherFs<'a> = Either<&'a PseudoFs, ArcBackFs>;

type VfsHandle = u64;
/// Vfs backend file system index
pub type VfsIndex = u8;

// VfsIndex is type of 'u8', so maximum 256 entries.
const MAX_VFS_INDEX: usize = 256;

/// Data struct to store inode number for the VFS filesystem.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub struct VfsInode(u64);

/// Vfs error definition
#[derive(Debug)]
pub enum VfsError {
    /// Operation not supported
    Unsupported,
    /// Mount backend filesystem
    Mount(Error),
    /// Restore mount backend filesystem
    RestoreMount(Error),
    /// Illegal inode index is used
    InodeIndex(String),
    /// Filesystem index related. For example, an index can't be allocated.
    FsIndex(Error),
    /// Error happened when walking path
    PathWalk(Error),
    /// Entry can't be found
    NotFound(String),
    /// File system can't ba initialized
    Initialize(String),
    /// Error serializing or deserializing the vfs state
    Persist(String),
}

impl fmt::Display for VfsError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::VfsError::*;
        match self {
            Unsupported => write!(f, "Vfs operation not supported"),
            Mount(e) => write!(f, "Mount backend filesystem: {e}"),
            RestoreMount(e) => write!(f, "Restore mount backend filesystem: {e}"),
            InodeIndex(s) => write!(f, "Illegal inode index: {s}"),
            FsIndex(e) => write!(f, "Filesystem index error: {e}"),
            PathWalk(e) => write!(f, "Walking path error: {e}"),
            NotFound(s) => write!(f, "Entry can't be found: {s}"),
            Initialize(s) => write!(f, "File system can't be initialized: {s}"),
            Persist(e) => write!(f, "Error serializing: {e}"),
        }
    }
}

impl std::error::Error for VfsError {}

/// Vfs result
pub type VfsResult<T> = std::result::Result<T, VfsError>;

#[inline]
fn is_dot_or_dotdot(name: &CStr) -> bool {
    let bytes = name.to_bytes_with_nul();
    bytes.starts_with(CURRENT_DIR_CSTR) || bytes.starts_with(PARENT_DIR_CSTR)
}

// Is `path` a single path component that is not "." or ".."?
fn is_safe_path_component(name: &CStr) -> bool {
    let bytes = name.to_bytes_with_nul();

    if bytes.contains(&SLASH_ASCII) {
        return false;
    }
    !is_dot_or_dotdot(name)
}

/// Validate a path component. A well behaved FUSE client should never send dot, dotdot and path
/// components containing slash ('/'). The only exception is that LOOKUP might contain dot and
/// dotdot to support NFS export.
#[inline]
pub fn validate_path_component(name: &CStr) -> io::Result<()> {
    match is_safe_path_component(name) {
        true => Ok(()),
        false => Err(io::Error::from_raw_os_error(libc::EINVAL)),
    }
}

impl VfsInode {
    fn new(fs_idx: VfsIndex, ino: u64) -> Self {
        assert_eq!(ino & !VFS_MAX_INO, 0);
        VfsInode(((fs_idx as u64) << VFS_INDEX_SHIFT) | ino)
    }

    fn is_pseudo_fs(&self) -> bool {
        (self.0 >> VFS_INDEX_SHIFT) as VfsIndex == VFS_PSEUDO_FS_IDX
    }

    fn fs_idx(&self) -> VfsIndex {
        (self.0 >> VFS_INDEX_SHIFT) as VfsIndex
    }

    fn ino(&self) -> u64 {
        self.0 & VFS_MAX_INO
    }
}

impl From<u64> for VfsInode {
    fn from(val: u64) -> Self {
        VfsInode(val)
    }
}

impl From<VfsInode> for u64 {
    fn from(val: VfsInode) -> Self {
        val.0
    }
}

#[derive(Debug, Clone)]
enum Either<A, B> {
    /// First branch of the type
    Left(A),
    /// Second branch of the type
    Right(B),
}
use Either::*;

/// Type that implements BackendFileSystem and Sync and Send
pub type BackFileSystem = Box<dyn BackendFileSystem<Inode = u64, Handle = u64> + Sync + Send>;

#[cfg(not(feature = "async-io"))]
/// BackendFileSystem abstracts all backend file systems under vfs
pub trait BackendFileSystem: FileSystem {
    /// mount returns the backend file system root inode entry and
    /// the largest inode number it has.
    fn mount(&self) -> Result<(Entry, u64)> {
        Err(Error::from_raw_os_error(libc::ENOSYS))
    }

    /// Provides a reference to the Any trait. This is useful to let
    /// the caller have access to the underlying type behind the
    /// trait.
    fn as_any(&self) -> &dyn Any;
}

#[cfg(feature = "async-io")]
/// BackendFileSystem abstracts all backend file systems under vfs
pub trait BackendFileSystem: AsyncFileSystem {
    /// mount returns the backend file system root inode entry and
    /// the largest inode number it has.
    fn mount(&self) -> Result<(Entry, u64)> {
        Err(Error::from_raw_os_error(libc::ENOSYS))
    }

    /// Provides a reference to the Any trait. This is useful to let
    /// the caller have access to the underlying type behind the
    /// trait.
    fn as_any(&self) -> &dyn Any;
}

struct MountPointData {
    fs_idx: VfsIndex,
    ino: u64,
    root_entry: Entry,
    _path: String,
}

#[derive(Debug, Copy, Clone)]
/// vfs init options
pub struct VfsOptions {
    /// Make readdir/readdirplus request return zero dirent even if dir has children.
    pub no_readdir: bool,
    /// Reject requests which will change the file size, or allocate file
    /// blocks exceed file size.
    pub seal_size: bool,
    /// File system options passed in from client
    pub in_opts: FsOptions,
    /// File system options returned to client
    pub out_opts: FsOptions,
    /// Declaration of ID mapping, in the format (internal ID, external ID, range).
    /// For example, (0, 1, 65536) represents mapping the external UID/GID range of `1~65536`
    /// to the range of `0~65535` within the filesystem.
    pub id_mapping: (u32, u32, u32),

    /// Disable fuse open request handling. When enabled, fuse open
    /// requests are always replied with ENOSYS.
    #[cfg(target_os = "linux")]
    pub no_open: bool,
    /// Disable fuse opendir request handling. When enabled, fuse opendir
    /// requests are always replied with ENOSYS.
    #[cfg(target_os = "linux")]
    pub no_opendir: bool,
    /// Disable fuse WRITEBACK_CACHE option so that kernel will not cache
    /// buffer writes.
    #[cfg(target_os = "linux")]
    pub no_writeback: bool,
    /// Enable fuse killpriv_v2 support. When enabled, fuse file system makes sure
    /// to remove security.capability xattr and setuid/setgid bits. See details in
    /// comments for HANDLE_KILLPRIV_V2
    #[cfg(target_os = "linux")]
    pub killpriv_v2: bool,
}

impl VfsOptions {
    fn new() -> Self {
        VfsOptions::default()
    }
}

impl Default for VfsOptions {
    #[cfg(target_os = "linux")]
    fn default() -> Self {
        let out_opts = FsOptions::ASYNC_READ
            | FsOptions::PARALLEL_DIROPS
            | FsOptions::BIG_WRITES
            | FsOptions::ASYNC_DIO
            | FsOptions::AUTO_INVAL_DATA
            | FsOptions::HAS_IOCTL_DIR
            | FsOptions::WRITEBACK_CACHE
            | FsOptions::ZERO_MESSAGE_OPEN
            | FsOptions::MAX_PAGES
            | FsOptions::ATOMIC_O_TRUNC
            | FsOptions::CACHE_SYMLINKS
            | FsOptions::DO_READDIRPLUS
            | FsOptions::READDIRPLUS_AUTO
            | FsOptions::EXPLICIT_INVAL_DATA
            | FsOptions::ZERO_MESSAGE_OPENDIR
            | FsOptions::HANDLE_KILLPRIV_V2
            | FsOptions::PERFILE_DAX;
        VfsOptions {
            no_open: true,
            no_opendir: true,
            no_writeback: false,
            no_readdir: false,
            seal_size: false,
            killpriv_v2: false,
            in_opts: FsOptions::empty(),
            out_opts,
            id_mapping: (0, 0, 0),
        }
    }

    #[cfg(target_os = "macos")]
    fn default() -> Self {
        let out_opts = FsOptions::ASYNC_READ | FsOptions::BIG_WRITES | FsOptions::ATOMIC_O_TRUNC;
        VfsOptions {
            no_readdir: false,
            seal_size: false,
            in_opts: FsOptions::empty(),
            out_opts,
            id_mapping: (0, 0, 0),
        }
    }
}

/// A union fs that combines multiple backend file systems.
pub struct Vfs {
    next_super: AtomicU8,
    root: PseudoFs,
    // mountpoints maps from pseudo fs inode to mounted fs mountpoint data
    mountpoints: ArcSwap<HashMap<u64, Arc<MountPointData>>>,
    // superblocks keeps track of all mounted file systems
    superblocks: ArcSuperBlock,
    opts: ArcSwap<VfsOptions>,
    initialized: AtomicBool,
    lock: Mutex<()>,
    remove_pseudo_root: bool,
    id_mapping: Option<(u32, u32, u32)>,
}

impl Default for Vfs {
    fn default() -> Self {
        Self::new(VfsOptions::new())
    }
}

impl Vfs {
    /// Create a new vfs instance
    pub fn new(opts: VfsOptions) -> Self {
        Vfs {
            next_super: AtomicU8::new(VFS_PSEUDO_FS_IDX + 1),
            mountpoints: ArcSwap::new(Arc::new(HashMap::new())),
            superblocks: ArcSwap::new(Arc::new(vec![None; MAX_VFS_INDEX])),
            root: PseudoFs::new(),
            opts: ArcSwap::new(Arc::new(opts)),
            lock: Mutex::new(()),
            initialized: AtomicBool::new(false),
            remove_pseudo_root: false,
            id_mapping: match opts.id_mapping.2 {
                0 => None,
                _ => Some(opts.id_mapping),
            },
        }
    }

    /// mark remove pseudo root inode when umount
    pub fn set_remove_pseudo_root(&mut self) {
        self.remove_pseudo_root = true;
    }

    /// For sake of live-upgrade, only after negotiation is done, it's safe to persist
    /// state of vfs.
    pub fn initialized(&self) -> bool {
        self.initialized.load(Ordering::Acquire)
    }

    /// Get a snapshot of the current vfs options.
    pub fn options(&self) -> VfsOptions {
        *self.opts.load_full()
    }

    fn insert_mount_locked(
        &self,
        fs: BackFileSystem,
        mut entry: Entry,
        fs_idx: VfsIndex,
        path: &str,
    ) -> Result<()> {
        // The visibility of mountpoints and superblocks:
        // superblock should be committed first because it won't be accessed until
        // a lookup returns a cross mountpoint inode.
        let mut superblocks = self.superblocks.load().deref().deref().clone();
        let mut mountpoints = self.mountpoints.load().deref().deref().clone();
        let inode = self.root.mount(path)?;
        let real_root_ino = entry.inode;

        self.convert_entry(fs_idx, entry.inode, &mut entry)?;

        // Over mount would invalidate previous superblock inodes.
        if let Some(mnt) = mountpoints.get(&inode) {
            superblocks[mnt.fs_idx as usize] = None;
        }
        superblocks[fs_idx as usize] = Some(Arc::new(fs));
        self.superblocks.store(Arc::new(superblocks));
        trace!("fs_idx {} inode {}", fs_idx, inode);

        let mountpoint = Arc::new(MountPointData {
            fs_idx,
            ino: real_root_ino,
            root_entry: entry,
            _path: path.to_string(),
        });
        mountpoints.insert(inode, mountpoint);
        self.mountpoints.store(Arc::new(mountpoints));

        Ok(())
    }

    /// Mount a backend file system to path
    pub fn mount(&self, fs: BackFileSystem, path: &str) -> VfsResult<VfsIndex> {
        let (entry, ino) = fs.mount().map_err(VfsError::Mount)?;
        if ino > VFS_MAX_INO {
            fs.destroy();
            return Err(VfsError::InodeIndex(format!(
                "Unsupported max inode number, requested {ino} supported {VFS_MAX_INO}"
            )));
        }

        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        if self.initialized() {
            let opts = self.opts.load().deref().out_opts;
            fs.init(opts).map_err(|e| {
                VfsError::Initialize(format!("Can't initialize with opts {opts:?}, {e:?}"))
            })?;
        }
        let index = self.allocate_fs_idx().map_err(VfsError::FsIndex)?;
        self.insert_mount_locked(fs, entry, index, path)
            .map_err(VfsError::Mount)?;

        Ok(index)
    }

    /// Restore a backend file system to path
    #[cfg(feature = "persist")]
    pub fn restore_mount(&self, fs: BackFileSystem, fs_idx: VfsIndex, path: &str) -> Result<()> {
        let (entry, ino) = fs.mount()?;
        if ino > VFS_MAX_INO {
            return Err(Error::new(
                ErrorKind::Other,
                format!(
                    "Unsupported max inode number, requested {} supported {}",
                    ino, VFS_MAX_INO
                ),
            ));
        }

        let _guard = self.lock.lock().unwrap();
        self.insert_mount_locked(fs, entry, fs_idx, path)
    }

    /// Umount a backend file system at path
    pub fn umount(&self, path: &str) -> VfsResult<(u64, u64)> {
        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        let inode = self
            .root
            .path_walk(path)
            .map_err(VfsError::PathWalk)?
            .ok_or_else(|| VfsError::NotFound(path.to_string()))?;
        let parent = self
            .root
            .get_parent_inode(inode)
            .ok_or(VfsError::NotFound(format!(
                "{}'s parent inode does not exist",
                inode
            )))?;
        let mut mountpoints = self.mountpoints.load().deref().deref().clone();
        let fs_idx = mountpoints
            .get(&inode)
            .map(Arc::clone)
            .map(|x| {
                // Do not remove pseudofs inode. We keep all pseudofs inode so that
                // 1. they can be reused later on
                // 2. during live upgrade, it is easier reconstruct pseudofs inodes since
                //    we do not have to track pseudofs deletions
                // In order to make the hot upgrade of virtiofs easy, VFS will save pseudo
                // inodes when umount for easy recovery. However, in the fuse scenario, if
                // umount does not remove the pseudo inode, it will cause an invalid
                // directory to be seen on the host, which is not friendly to users. So add
                // this option to control this behavior.
                if self.remove_pseudo_root {
                    self.root.evict_inode(inode);
                }
                mountpoints.remove(&inode);
                self.mountpoints.store(Arc::new(mountpoints));
                x.fs_idx
            })
            .ok_or_else(|| {
                error!("{} is not a mount point.", path);
                VfsError::NotFound(path.to_string())
            })?;

        trace!("fs_idx {}", fs_idx);
        let mut superblocks = self.superblocks.load().deref().deref().clone();
        if let Some(fs) = superblocks[fs_idx as usize].take() {
            fs.destroy();
        }
        self.superblocks.store(Arc::new(superblocks));

        Ok((inode, parent))
    }

    /// Get the mounted backend file system alongside the path if there's one.
    pub fn get_rootfs(&self, path: &str) -> VfsResult<Option<Arc<BackFileSystem>>> {
        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        let inode = match self.root.path_walk(path).map_err(VfsError::PathWalk)? {
            Some(i) => i,
            None => return Ok(None),
        };

        if let Some(mnt) = self.mountpoints.load().get(&inode) {
            Ok(Some(self.get_fs_by_idx(mnt.fs_idx).map_err(|e| {
                VfsError::NotFound(format!("fs index {}, {:?}", mnt.fs_idx, e))
            })?))
        } else {
            // Pseudo fs dir inode exists, but that no backend is ever mounted
            // is a normal case.
            Ok(None)
        }
    }

    /// Get the root pseudo fs's reference in vfs
    pub fn get_root_pseudofs(&self) -> &PseudoFs {
        &self.root
    }

    // Inode converting rules:
    // 1. Pseudo fs inode is not hashed
    // 2. Index is always larger than 0 so that pseudo fs inodes are never affected
    //    and can be found directly
    // 3. Other inodes are hashed via (index << 56 | inode)
    fn convert_inode(&self, fs_idx: VfsIndex, inode: u64) -> Result<u64> {
        // Do not hash negative dentry
        if inode == 0 {
            return Ok(inode);
        }
        if inode > VFS_MAX_INO {
            return Err(Error::new(
                ErrorKind::Other,
                format!("Inode number {inode} too large, max supported {VFS_MAX_INO}"),
            ));
        }
        let ino: u64 = ((fs_idx as u64) << VFS_INDEX_SHIFT) | inode;
        trace!(
            "fuse: vfs fs_idx {} inode {} fuse ino {:#x}",
            fs_idx,
            inode,
            ino
        );
        Ok(ino)
    }

    fn convert_entry(&self, fs_idx: VfsIndex, inode: u64, entry: &mut Entry) -> Result<Entry> {
        self.convert_inode(fs_idx, inode).map(|ino| {
            entry.inode = ino;
            entry.attr.st_ino = ino;
            // If id_mapping is enabled, map the internal ID to the external ID.
            if let Some((internal_id, external_id, range)) = self.id_mapping {
                if entry.attr.st_uid >= internal_id && entry.attr.st_uid < internal_id + range {
                    entry.attr.st_uid += external_id - internal_id;
                }
                if entry.attr.st_gid >= internal_id && entry.attr.st_gid < internal_id + range {
                    entry.attr.st_gid += external_id - internal_id;
                }
            }
            *entry
        })
    }

    /// If id_mapping is enabled, remap the uid/gid in attributes.
    ///
    /// If `map_internal_to_external` is true, the IDs inside VFS will be mapped
    /// to external IDs.
    /// If `map_internal_to_external` is false, the external IDs will be mapped
    /// to VFS internal IDs.
    fn remap_attr_id(&self, map_internal_to_external: bool, attr: &mut stat64) {
        if let Some((internal_id, external_id, range)) = self.id_mapping {
            if map_internal_to_external
                && attr.st_uid >= internal_id
                && attr.st_uid < internal_id + range
            {
                attr.st_uid += external_id - internal_id;
            }
            if map_internal_to_external
                && attr.st_gid >= internal_id
                && attr.st_gid < internal_id + range
            {
                attr.st_gid += external_id - internal_id;
            }
            if !map_internal_to_external
                && attr.st_uid >= external_id
                && attr.st_uid < external_id + range
            {
                attr.st_uid += internal_id - external_id;
            }
            if !map_internal_to_external
                && attr.st_gid >= external_id
                && attr.st_gid < external_id + range
            {
                attr.st_gid += internal_id - external_id;
            }
        }
    }

    fn allocate_fs_idx(&self) -> Result<VfsIndex> {
        let superblocks = self.superblocks.load().deref().deref().clone();
        let start = self.next_super.load(Ordering::SeqCst);
        let mut found = false;

        loop {
            let index = self.next_super.fetch_add(1, Ordering::Relaxed);
            if index == start {
                if found {
                    // There's no available file system index
                    break;
                } else {
                    found = true;
                }
            }

            if index == VFS_PSEUDO_FS_IDX {
                // Skip the pseudo fs index
                continue;
            }
            if (index as usize) < superblocks.len() && superblocks[index as usize].is_some() {
                // Skip if it's allocated
                continue;
            } else {
                return Ok(index);
            }
        }

        Err(Error::new(
            ErrorKind::Other,
            "vfs maximum mountpoints reached",
        ))
    }

    fn get_fs_by_idx(&self, fs_idx: VfsIndex) -> Result<Arc<BackFileSystem>> {
        let superblocks = self.superblocks.load();

        if let Some(fs) = &superblocks[fs_idx as usize] {
            return Ok(fs.clone());
        }

        Err(Error::from_raw_os_error(libc::ENOENT))
    }

    fn get_real_rootfs(&self, inode: VfsInode) -> Result<(VfsEitherFs<'_>, VfsInode)> {
        if inode.is_pseudo_fs() {
            // ROOT_ID is special, we need to check if we have a mountpoint on the vfs root
            if inode.ino() == ROOT_ID {
                if let Some(mnt) = self.mountpoints.load().get(&inode.ino()).map(Arc::clone) {
                    let fs = self.get_fs_by_idx(mnt.fs_idx)?;
                    return Ok((Right(fs), VfsInode::new(mnt.fs_idx, mnt.ino)));
                }
            }
            Ok((Left(&self.root), inode))
        } else {
            let fs = self.get_fs_by_idx(inode.fs_idx())?;
            Ok((Right(fs), inode))
        }
    }

    fn lookup_pseudo(
        &self,
        fs: &PseudoFs,
        idata: VfsInode,
        ctx: &Context,
        name: &CStr,
    ) -> Result<Entry> {
        trace!("lookup pseudo ino {} name {:?}", idata.ino(), name);
        let mut entry = fs.lookup(ctx, idata.ino(), name)?;

        match self.mountpoints.load().get(&entry.inode) {
            Some(mnt) => {
                // cross mountpoint, return mount root entry
                entry = mnt.root_entry;
                self.convert_entry(mnt.fs_idx, mnt.ino, &mut entry)?;
                trace!(
                    "vfs lookup cross mountpoint, return new mount fs_idx {} inode 0x{:x} fuse inode 0x{:x}, attr inode 0x{:x}",
                    mnt.fs_idx,
                    mnt.ino,
                    entry.inode,
                    entry.attr.st_ino,
                );
                Ok(entry)
            }
            None => self.convert_entry(idata.fs_idx(), entry.inode, &mut entry),
        }
    }
}

/// Sava and restore Vfs state.
#[cfg(feature = "persist")]
pub mod persist {
    use std::{
        ops::Deref,
        sync::{atomic::Ordering, Arc},
    };

    use dbs_snapshot::Snapshot;
    use versionize::{VersionMap, Versionize, VersionizeResult};
    use versionize_derive::Versionize;

    use crate::api::{
        filesystem::FsOptions,
        pseudo_fs::persist::PseudoFsState,
        vfs::{VfsError, VfsResult},
        Vfs, VfsOptions,
    };

    /// VfsState stores the state of the VFS.
    #[derive(Versionize, Debug)]
    struct VfsState {
        /// Vfs options
        options: VfsOptionsState,
        /// Vfs root
        root: Vec<u8>,
        /// next super block index
        next_super: u8,
    }

    #[derive(Versionize, Debug, Default)]
    struct VfsOptionsState {
        in_opts: u64,
        out_opts: u64,
        no_readdir: bool,
        seal_size: bool,
        id_mapping_internal: u32,
        id_mapping_external: u32,
        id_mapping_range: u32,

        #[cfg(target_os = "linux")]
        no_open: bool,
        #[cfg(target_os = "linux")]
        no_opendir: bool,
        #[cfg(target_os = "linux")]
        no_writeback: bool,
        #[cfg(target_os = "linux")]
        killpriv_v2: bool,
    }

    impl VfsOptions {
        fn save(&self) -> VfsOptionsState {
            VfsOptionsState {
                in_opts: self.in_opts.bits(),
                out_opts: self.out_opts.bits(),
                no_readdir: self.no_readdir,
                seal_size: self.seal_size,
                id_mapping_internal: self.id_mapping.0,
                id_mapping_external: self.id_mapping.1,
                id_mapping_range: self.id_mapping.2,

                #[cfg(target_os = "linux")]
                no_open: self.no_open,
                #[cfg(target_os = "linux")]
                no_opendir: self.no_opendir,
                #[cfg(target_os = "linux")]
                no_writeback: self.no_writeback,
                #[cfg(target_os = "linux")]
                killpriv_v2: self.killpriv_v2,
            }
        }

        fn restore(state: &VfsOptionsState) -> VfsResult<VfsOptions> {
            Ok(VfsOptions {
                in_opts: FsOptions::from_bits(state.in_opts).ok_or(VfsError::Persist(
                    "Failed to restore VfsOptions.in_opts".to_owned(),
                ))?,
                out_opts: FsOptions::from_bits(state.out_opts).ok_or(VfsError::Persist(
                    "Failed to restore VfsOptions.out_opts".to_owned(),
                ))?,
                no_readdir: state.no_readdir,
                seal_size: state.seal_size,
                id_mapping: (
                    state.id_mapping_internal,
                    state.id_mapping_external,
                    state.id_mapping_range,
                ),

                #[cfg(target_os = "linux")]
                no_open: state.no_open,
                #[cfg(target_os = "linux")]
                no_opendir: state.no_opendir,
                #[cfg(target_os = "linux")]
                no_writeback: state.no_writeback,
                #[cfg(target_os = "linux")]
                killpriv_v2: state.killpriv_v2,
            })
        }
    }

    impl Vfs {
        fn get_version_map() -> versionize::VersionMap {
            let mut version_map = VersionMap::new();
            version_map
                .set_type_version(VfsState::type_id(), 1)
                .set_type_version(PseudoFsState::type_id(), 1)
                .set_type_version(VfsOptionsState::type_id(), 1);

            // more versions for the future

            version_map
        }

        /// Saves part of the Vfs metadata into a byte array.
        /// The upper layer caller can use this method to save
        /// and transfer metadata for the reloading in the future.
        ///
        /// Note! This function does not save the information
        /// of the Backend FileSystem mounted by VFS,
        /// which means that when the caller restores VFS,
        /// in addition to restoring the information in the byte array
        /// returned by this function,
        /// it also needs to manually remount each Backend FileSystem
        /// according to the Index obtained from the previous mount,
        /// the method `restore_mount` may be help to do this.
        ///
        /// # Example
        ///
        /// The following example shows how the function is used in conjunction with
        /// `restore_from_bytes` to implement the serialization and deserialization of VFS.
        ///
        /// ```
        /// use fuse_backend_rs::api::{Vfs, VfsIndex, VfsOptions};
        /// use fuse_backend_rs::passthrough::{Config, PassthroughFs};
        ///
        /// let new_backend_fs = || {
        ///     let fs_cfg = Config::default();
        ///     let fs = PassthroughFs::<()>::new(fs_cfg.clone()).unwrap();
        ///     fs.import().unwrap();
        ///     Box::new(fs)
        /// };
        ///
        /// // create new vfs
        /// let vfs = &Vfs::new(VfsOptions::default());
        /// let paths = vec!["/a", "/a/b", "/a/b/c", "/b", "/b/a/c", "/d"];
        /// // record the backend fs and their VfsIndexes
        /// let backend_fs_list: Vec<(&str, VfsIndex)> = paths
        ///     .iter()
        ///     .map(|path| {
        ///         let fs = new_backend_fs();
        ///         let idx = vfs.mount(fs, path).unwrap();
        ///
        ///         (path.to_owned(), idx)
        ///     })
        ///     .collect();
        ///
        /// // save the vfs state
        /// let mut buf = vfs.save_to_bytes().unwrap();
        ///
        /// // restore the vfs state
        /// let restored_vfs = &Vfs::new(VfsOptions::default());
        /// restored_vfs.restore_from_bytes(&mut buf).unwrap();
        ///
        /// // mount the backend fs
        /// backend_fs_list.into_iter().for_each(|(path, idx)| {
        ///     let fs = new_backend_fs();
        ///     vfs.restore_mount(fs, idx, path).unwrap();
        /// });
        /// ```
        pub fn save_to_bytes(&self) -> VfsResult<Vec<u8>> {
            let root_state = self
                .root
                .save_to_bytes()
                .map_err(|e| VfsError::Persist(format!("Failed to save Vfs root: {:?}", e)))?;
            let vfs_state = VfsState {
                options: self.opts.load().deref().deref().save(),
                root: root_state,
                next_super: self.next_super.load(Ordering::SeqCst),
            };

            let vm = Vfs::get_version_map();
            let target_version = vm.latest_version();
            let mut s = Snapshot::new(vm, target_version);
            let mut buf = Vec::new();
            s.save(&mut buf, &vfs_state).map_err(|e| {
                VfsError::Persist(format!("Failed to save Vfs using snapshot: {:?}", e))
            })?;

            Ok(buf)
        }

        /// Restores part of the Vfs metadata from a byte array.
        /// For more information, see the example of `save_to_bytes`.
        pub fn restore_from_bytes(&self, buf: &mut Vec<u8>) -> VfsResult<()> {
            let mut state: VfsState =
                Snapshot::load(&mut buf.as_slice(), buf.len(), Vfs::get_version_map())
                    .map_err(|e| {
                        VfsError::Persist(format!("Failed to load Vfs using snapshot: {:?}", e))
                    })?
                    .0;
            let opts = VfsOptions::restore(&state.options)?;
            self.initialized
                .store(!opts.in_opts.is_empty(), Ordering::Release);
            self.opts.store(Arc::new(opts));

            self.next_super.store(state.next_super, Ordering::SeqCst);
            self.root
                .restore_from_bytes(&mut state.root)
                .map_err(|e| VfsError::Persist(format!("Failed to restore Vfs root: {:?}", e)))?;

            Ok(())
        }
    }

    mod test {

        // This test is to make sure that VfsState can be serialized and deserialized
        #[test]
        fn test_vfs_save_restore_simple() {
            use crate::api::{Vfs, VfsOptions};

            // create new vfs
            let vfs = &Vfs::new(VfsOptions::default());

            // save the vfs state using Snapshot
            let mut buf = vfs.save_to_bytes().unwrap();

            // restore the vfs state
            let vfs = &Vfs::new(VfsOptions::default());
            vfs.restore_from_bytes(&mut buf).unwrap();
            assert_eq!(vfs.next_super.load(std::sync::atomic::Ordering::SeqCst), 1);
        }

        #[test]
        fn test_vfs_save_restore_with_backend_fs() {
            use crate::api::{Vfs, VfsIndex, VfsOptions};
            use crate::passthrough::{Config, PassthroughFs};

            let new_backend_fs = || {
                let fs_cfg = Config::default();
                let fs = PassthroughFs::<()>::new(fs_cfg.clone()).unwrap();
                fs.import().unwrap();
                Box::new(fs)
            };

            // create new vfs
            let vfs = &Vfs::new(VfsOptions::default());
            let paths = vec!["/a", "/a/b", "/a/b/c", "/b", "/b/a/c", "/d"];
            let backend_fs_list: Vec<(&str, VfsIndex)> = paths
                .iter()
                .map(|path| {
                    let fs = new_backend_fs();
                    let idx = vfs.mount(fs, path).unwrap();

                    (path.to_owned(), idx)
                })
                .collect();

            // save the vfs state using Snapshot
            let mut buf = vfs.save_to_bytes().unwrap();

            // restore the vfs state
            let restored_vfs = &Vfs::new(VfsOptions::default());
            restored_vfs.restore_from_bytes(&mut buf).unwrap();
            // restore the backend fs
            backend_fs_list.into_iter().for_each(|(path, idx)| {
                let fs = new_backend_fs();
                vfs.restore_mount(fs, idx, path).unwrap();
            });

            // check the vfs and restored_vfs
            assert_eq!(
                vfs.next_super.load(std::sync::atomic::Ordering::SeqCst),
                restored_vfs
                    .next_super
                    .load(std::sync::atomic::Ordering::SeqCst)
            );
            assert_eq!(
                vfs.initialized.load(std::sync::atomic::Ordering::SeqCst),
                restored_vfs
                    .initialized
                    .load(std::sync::atomic::Ordering::SeqCst)
            );
            for path in paths.iter() {
                let inode = vfs.root.path_walk(path).unwrap();
                let restored_inode = restored_vfs.root.path_walk(path).unwrap();
                assert_eq!(inode, restored_inode);
            }
        }

        #[test]
        fn test_vfs_save_restore_with_backend_fs_with_initialized() {
            use crate::api::filesystem::{FileSystem, FsOptions};
            use crate::api::{Vfs, VfsIndex, VfsOptions};
            use crate::passthrough::{Config, PassthroughFs};
            use std::sync::atomic::Ordering;

            let new_backend_fs = || {
                let fs_cfg = Config::default();
                let fs = PassthroughFs::<()>::new(fs_cfg.clone()).unwrap();
                fs.import().unwrap();
                Box::new(fs)
            };

            // create new vfs
            let vfs = &Vfs::new(VfsOptions::default());
            let paths = vec!["/a", "/a/b", "/a/b/c", "/b", "/b/a/c", "/d"];
            let backend_fs_list: Vec<(&str, VfsIndex)> = paths
                .iter()
                .map(|path| {
                    let fs = new_backend_fs();
                    let idx = vfs.mount(fs, path).unwrap();

                    (path.to_owned(), idx)
                })
                .collect();
            vfs.init(FsOptions::ASYNC_READ).unwrap();
            assert!(vfs.initialized.load(Ordering::Acquire));

            // save the vfs state using Snapshot
            let mut buf = vfs.save_to_bytes().unwrap();

            // restore the vfs state
            let restored_vfs = &Vfs::new(VfsOptions::default());
            restored_vfs.restore_from_bytes(&mut buf).unwrap();

            // restore the backend fs
            backend_fs_list.into_iter().for_each(|(path, idx)| {
                let fs = new_backend_fs();
                vfs.restore_mount(fs, idx, path).unwrap();
            });

            // check the vfs and restored_vfs
            assert_eq!(
                vfs.next_super.load(std::sync::atomic::Ordering::SeqCst),
                restored_vfs
                    .next_super
                    .load(std::sync::atomic::Ordering::SeqCst)
            );
            assert_eq!(
                vfs.initialized.load(std::sync::atomic::Ordering::Acquire),
                restored_vfs
                    .initialized
                    .load(std::sync::atomic::Ordering::Acquire)
            );
            for path in paths.iter() {
                let inode = vfs.root.path_walk(path).unwrap();
                let restored_inode = restored_vfs.root.path_walk(path).unwrap();
                assert_eq!(inode, restored_inode);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::Vfs;
    use std::ffi::CString;
    use std::io::{Error, ErrorKind};

    pub(crate) struct FakeFileSystemOne {}
    impl FileSystem for FakeFileSystemOne {
        type Inode = u64;
        type Handle = u64;
        fn lookup(&self, _: &Context, _: Self::Inode, _: &CStr) -> Result<Entry> {
            Ok(Entry::default())
        }
        fn getattr(
            &self,
            _ctx: &Context,
            _inode: Self::Inode,
            _handle: Option<Self::Handle>,
        ) -> Result<(stat64, Duration)> {
            let mut attr = Attr {
                ..Default::default()
            };
            attr.ino = 1;
            Ok((attr.into(), Duration::from_secs(1)))
        }
    }

    pub(crate) struct FakeFileSystemTwo {}
    impl FileSystem for FakeFileSystemTwo {
        type Inode = u64;
        type Handle = u64;
        fn lookup(&self, _: &Context, _: Self::Inode, _: &CStr) -> Result<Entry> {
            Ok(Entry {
                inode: 1,
                ..Default::default()
            })
        }
    }

    #[test]
    fn test_is_safe_path_component() {
        let name = CStr::from_bytes_with_nul(b"normal\0").unwrap();
        assert!(is_safe_path_component(name), "\"{:?}\"", name);

        let name = CStr::from_bytes_with_nul(b".a\0").unwrap();
        assert!(is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"a.a\0").unwrap();
        assert!(is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"a.a\0").unwrap();
        assert!(is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"/\0").unwrap();
        assert!(!is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"/a\0").unwrap();
        assert!(!is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b".\0").unwrap();
        assert!(!is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"..\0").unwrap();
        assert!(!is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"../.\0").unwrap();
        assert!(!is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"a/b\0").unwrap();
        assert!(!is_safe_path_component(name));

        let name = CStr::from_bytes_with_nul(b"./../a\0").unwrap();
        assert!(!is_safe_path_component(name));
    }

    #[test]
    fn test_is_dot_or_dotdot() {
        let name = CStr::from_bytes_with_nul(b"..\0").unwrap();
        assert!(is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b".\0").unwrap();
        assert!(is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b"...\0").unwrap();
        assert!(!is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b"./.\0").unwrap();
        assert!(!is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b"a\0").unwrap();
        assert!(!is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b"aa\0").unwrap();
        assert!(!is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b"/a\0").unwrap();
        assert!(!is_dot_or_dotdot(name));

        let name = CStr::from_bytes_with_nul(b"a/\0").unwrap();
        assert!(!is_dot_or_dotdot(name));
    }

    #[cfg(feature = "async-io")]
    mod async_io {
        use super::*;
        use crate::abi::fuse_abi::{OpenOptions, SetattrValid};
        use async_trait::async_trait;

        #[allow(unused_variables)]
        #[async_trait]
        impl AsyncFileSystem for FakeFileSystemOne {
            async fn async_lookup(
                &self,
                ctx: &Context,
                parent: <Self as FileSystem>::Inode,
                name: &CStr,
            ) -> Result<Entry> {
                Ok(Entry::default())
            }

            async fn async_getattr(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: Option<<Self as FileSystem>::Handle>,
            ) -> Result<(libc::stat64, Duration)> {
                unimplemented!()
            }

            async fn async_setattr(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                attr: libc::stat64,
                handle: Option<<Self as FileSystem>::Handle>,
                valid: SetattrValid,
            ) -> Result<(libc::stat64, Duration)> {
                unimplemented!()
            }

            async fn async_open(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                flags: u32,
                fuse_flags: u32,
            ) -> Result<(Option<<Self as FileSystem>::Handle>, OpenOptions)> {
                unimplemented!()
            }

            async fn async_create(
                &self,
                ctx: &Context,
                parent: <Self as FileSystem>::Inode,
                name: &CStr,
                args: CreateIn,
            ) -> Result<(Entry, Option<<Self as FileSystem>::Handle>, OpenOptions)> {
                unimplemented!()
            }

            async fn async_read(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: <Self as FileSystem>::Handle,
                w: &mut (dyn AsyncZeroCopyWriter + Send),
                size: u32,
                offset: u64,
                lock_owner: Option<u64>,
                flags: u32,
            ) -> Result<usize> {
                unimplemented!()
            }

            async fn async_write(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: <Self as FileSystem>::Handle,
                r: &mut (dyn AsyncZeroCopyReader + Send),
                size: u32,
                offset: u64,
                lock_owner: Option<u64>,
                delayed_write: bool,
                flags: u32,
                fuse_flags: u32,
            ) -> Result<usize> {
                unimplemented!()
            }

            async fn async_fsync(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                datasync: bool,
                handle: <Self as FileSystem>::Handle,
            ) -> Result<()> {
                unimplemented!()
            }

            async fn async_fallocate(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: <Self as FileSystem>::Handle,
                mode: u32,
                offset: u64,
                length: u64,
            ) -> Result<()> {
                unimplemented!()
            }

            async fn async_fsyncdir(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                datasync: bool,
                handle: <Self as FileSystem>::Handle,
            ) -> Result<()> {
                unimplemented!()
            }
        }

        impl BackendFileSystem for FakeFileSystemOne {
            fn mount(&self) -> Result<(Entry, u64)> {
                Ok((
                    Entry {
                        inode: 1,
                        ..Default::default()
                    },
                    0,
                ))
            }

            fn as_any(&self) -> &dyn Any {
                self
            }
        }

        #[allow(unused_variables)]
        #[async_trait]
        impl AsyncFileSystem for FakeFileSystemTwo {
            async fn async_lookup(
                &self,
                ctx: &Context,
                parent: <Self as FileSystem>::Inode,
                name: &CStr,
            ) -> Result<Entry> {
                Err(std::io::Error::from_raw_os_error(libc::EINVAL))
            }

            async fn async_getattr(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: Option<<Self as FileSystem>::Handle>,
            ) -> Result<(libc::stat64, Duration)> {
                unimplemented!()
            }

            async fn async_setattr(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                attr: libc::stat64,
                handle: Option<<Self as FileSystem>::Handle>,
                valid: SetattrValid,
            ) -> Result<(libc::stat64, Duration)> {
                unimplemented!()
            }

            async fn async_open(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                flags: u32,
                fuse_flags: u32,
            ) -> Result<(Option<<Self as FileSystem>::Handle>, OpenOptions)> {
                unimplemented!()
            }

            async fn async_create(
                &self,
                ctx: &Context,
                parent: <Self as FileSystem>::Inode,
                name: &CStr,
                args: CreateIn,
            ) -> Result<(Entry, Option<<Self as FileSystem>::Handle>, OpenOptions)> {
                unimplemented!()
            }

            async fn async_read(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: <Self as FileSystem>::Handle,
                w: &mut (dyn AsyncZeroCopyWriter + Send),
                size: u32,
                offset: u64,
                lock_owner: Option<u64>,
                flags: u32,
            ) -> Result<usize> {
                unimplemented!()
            }

            async fn async_write(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: <Self as FileSystem>::Handle,
                r: &mut (dyn AsyncZeroCopyReader + Send),
                size: u32,
                offset: u64,
                lock_owner: Option<u64>,
                delayed_write: bool,
                flags: u32,
                fuse_flags: u32,
            ) -> Result<usize> {
                unimplemented!()
            }

            async fn async_fsync(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                datasync: bool,
                handle: <Self as FileSystem>::Handle,
            ) -> Result<()> {
                unimplemented!()
            }

            async fn async_fallocate(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                handle: <Self as FileSystem>::Handle,
                mode: u32,
                offset: u64,
                length: u64,
            ) -> Result<()> {
                unimplemented!()
            }

            async fn async_fsyncdir(
                &self,
                ctx: &Context,
                inode: <Self as FileSystem>::Inode,
                datasync: bool,
                handle: <Self as FileSystem>::Handle,
            ) -> Result<()> {
                unimplemented!()
            }
        }

        impl BackendFileSystem for FakeFileSystemTwo {
            fn mount(&self) -> Result<(Entry, u64)> {
                Ok((
                    Entry {
                        inode: 1,
                        ..Default::default()
                    },
                    0,
                ))
            }
            fn as_any(&self) -> &dyn Any {
                self
            }
        }
    }

    #[cfg(not(feature = "async-io"))]
    impl BackendFileSystem for FakeFileSystemOne {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    ..Default::default()
                },
                0,
            ))
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    #[cfg(not(feature = "async-io"))]
    impl BackendFileSystem for FakeFileSystemTwo {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    ..Default::default()
                },
                0,
            ))
        }
        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    #[test]
    fn test_vfs_init() {
        let vfs = Vfs::default();
        assert_eq!(vfs.initialized(), false);

        let opts = vfs.opts.load();
        let out_opts = opts.out_opts;

        #[cfg(target_os = "linux")]
        {
            assert_eq!(opts.no_open, true);
            assert_eq!(opts.no_opendir, true);
            assert_eq!(opts.no_writeback, false);
            assert_eq!(opts.killpriv_v2, false);
        }
        assert_eq!(opts.no_readdir, false);
        assert_eq!(opts.seal_size, false);
        assert_eq!(opts.in_opts.is_empty(), true);

        vfs.init(FsOptions::ASYNC_READ).unwrap();
        assert_eq!(vfs.initialized(), true);

        let opts = vfs.opts.load();
        #[cfg(target_os = "linux")]
        {
            assert_eq!(opts.no_open, false);
            assert_eq!(opts.no_opendir, false);
            assert_eq!(opts.no_writeback, false);
            assert_eq!(opts.killpriv_v2, false);
        }
        assert_eq!(opts.no_readdir, false);
        assert_eq!(opts.seal_size, false);

        vfs.destroy();
        assert_eq!(vfs.initialized(), false);

        let vfs = Vfs::default();
        #[cfg(target_os = "linux")]
        let in_opts =
            FsOptions::ASYNC_READ | FsOptions::ZERO_MESSAGE_OPEN | FsOptions::ZERO_MESSAGE_OPENDIR;
        #[cfg(target_os = "macos")]
        let in_opts = FsOptions::ASYNC_READ;
        vfs.init(in_opts).unwrap();
        let opts = vfs.opts.load();
        #[cfg(target_os = "linux")]
        {
            assert_eq!(opts.no_open, true);
            assert_eq!(opts.no_opendir, true);
            assert_eq!(opts.no_writeback, false);
            assert_eq!(opts.killpriv_v2, false);
        }
        assert_eq!(opts.out_opts, out_opts & in_opts);
    }

    #[test]
    fn test_vfs_lookup() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs = FakeFileSystemOne {};
        let ctx = Context::new();

        assert!(vfs.mount(Box::new(fs), "/x/y").is_ok());

        // Lookup inode on pseudo file system.
        let entry1 = vfs
            .lookup(&ctx, ROOT_ID.into(), CString::new("x").unwrap().as_c_str())
            .unwrap();
        assert_eq!(entry1.inode, 0x2);

        // Lookup inode on mounted file system.
        let entry2 = vfs
            .lookup(
                &ctx,
                entry1.inode.into(),
                CString::new("y").unwrap().as_c_str(),
            )
            .unwrap();
        assert_eq!(entry2.inode, 0x100_0000_0000_0001);

        // lookup for negative result.
        let entry3 = vfs
            .lookup(
                &ctx,
                entry2.inode.into(),
                CString::new("z").unwrap().as_c_str(),
            )
            .unwrap();
        assert_eq!(entry3.inode, 0);

        let (stat, _) = vfs
            .getattr(&ctx, VfsInode(0x100_0000_0000_0001), None)
            .unwrap();
        assert_eq!(stat.st_ino, 0x100_0000_0000_0001);
    }

    #[test]
    fn test_mount_different_fs_types() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemTwo {};
        assert!(vfs.mount(Box::new(fs1), "/foo").is_ok());
        assert!(vfs.mount(Box::new(fs2), "/bar").is_ok());

        // Lookup inode on pseudo file system.
        let ctx = Context::new();
        let entry1 = vfs
            .lookup(
                &ctx,
                ROOT_ID.into(),
                CString::new("bar").unwrap().as_c_str(),
            )
            .unwrap();
        assert_eq!(entry1.inode, 0x200_0000_0000_0001);
        assert_eq!(entry1.attr.st_ino, 0x200_0000_0000_0001);
    }

    #[test]
    fn test_umount() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemOne {};
        assert!(vfs.mount(Box::new(fs1), "/foo").is_ok());
        assert!(vfs.umount("/foo").is_ok());

        assert!(vfs.mount(Box::new(fs2), "/x/y").is_ok());

        match vfs.umount("/x") {
            Err(VfsError::NotFound(_e)) => {}
            _ => panic!("expect VfsError::NotFound(/x)"),
        }
    }

    #[test]
    fn test_umount_overlap() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemTwo {};

        assert!(vfs.mount(Box::new(fs1), "/x/y/z").is_ok());
        assert!(vfs.mount(Box::new(fs2), "/x/y").is_ok());

        let m1 = vfs.get_rootfs("/x/y/z").unwrap().unwrap();
        assert!(m1.as_any().is::<FakeFileSystemOne>());
        let m2 = vfs.get_rootfs("/x/y").unwrap().unwrap();
        assert!(m2.as_any().is::<FakeFileSystemTwo>());

        assert!(vfs.umount("/x/y/z").is_ok());
        assert!(vfs.umount("/x/y").is_ok());

        match vfs.umount("/x/y/z") {
            Err(VfsError::NotFound(_e)) => {}
            _ => panic!("expect VfsError::NotFound(/x/y/z)"),
        }
    }

    #[test]
    fn test_umount_same() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemTwo {};

        assert!(vfs.mount(Box::new(fs1), "/x/y").is_ok());
        assert!(vfs.mount(Box::new(fs2), "/x/y").is_ok());

        let m1 = vfs.get_rootfs("/x/y").unwrap().unwrap();
        assert!(m1.as_any().is::<FakeFileSystemTwo>());

        assert!(vfs.umount("/x/y").is_ok());

        match vfs.umount("/x/y") {
            Err(VfsError::NotFound(_e)) => {}
            _ => panic!("expect VfsError::NotFound(/x/y)"),
        }
    }

    #[test]
    #[should_panic]
    fn test_invalid_inode() {
        let _ = VfsInode::new(1, VFS_MAX_INO + 1);
    }

    #[test]
    fn test_inode() {
        let inode = VfsInode::new(2, VFS_MAX_INO);

        assert_eq!(inode.fs_idx(), 2);
        assert_eq!(inode.ino(), VFS_MAX_INO);
        assert!(!inode.is_pseudo_fs());
        assert_eq!(u64::from(inode), 0x200_0000_0000_0000u64 + VFS_MAX_INO);
    }

    #[test]
    fn test_allocate_fs_idx() {
        let vfs = Vfs::new(VfsOptions::default());
        let _guard = vfs.lock.lock().unwrap();

        // Test case: allocate all available fs idx
        for _ in 0..255 {
            let fs = FakeFileSystemOne {};
            let index = vfs.allocate_fs_idx().unwrap();
            let mut superblocks = vfs.superblocks.load().deref().deref().clone();

            superblocks[index as usize] = Some(Arc::new(Box::new(fs)));
            vfs.superblocks.store(Arc::new(superblocks));
        }

        // Test case: fail to allocate more fs idx if all have been allocated
        for _ in 0..=256 {
            vfs.allocate_fs_idx().unwrap_err();
        }
    }

    #[test]
    fn test_fmt_vfs_error() {
        assert_eq!(
            format!("{}", VfsError::Unsupported),
            "Vfs operation not supported".to_string()
        );
        assert_eq!(
            format!(
                "{}",
                VfsError::Mount(Error::new(ErrorKind::Other, "mount".to_string()),)
            ),
            "Mount backend filesystem: mount".to_string()
        );
        assert_eq!(
            format!("{}", VfsError::InodeIndex("inode index".to_string())),
            "Illegal inode index: inode index".to_string()
        );
        assert_eq!(
            format!(
                "{}",
                VfsError::FsIndex(Error::new(ErrorKind::Other, "fs index".to_string()),)
            ),
            "Filesystem index error: fs index".to_string()
        );
        assert_eq!(
            format!(
                "{}",
                VfsError::PathWalk(Error::new(ErrorKind::Other, "path walk".to_string()),)
            ),
            "Walking path error: path walk".to_string()
        );
        assert_eq!(
            format!("{}", VfsError::NotFound("not found".to_string())),
            "Entry can't be found: not found".to_string()
        );
        assert_eq!(
            format!("{}", VfsError::Initialize("initialize".to_string())),
            "File system can't be initialized: initialize".to_string()
        );
    }
}
