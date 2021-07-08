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
use std::io::{Error, ErrorKind, Result};
use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use arc_swap::ArcSwap;

use super::pseudo_fs::PseudoFs;
use crate::abi::linux_abi::*;
use crate::api::filesystem::*;
use crate::async_util::{AsyncDrive, AsyncDriver};
use crate::BitmapSlice;

#[cfg(feature = "async-io")]
mod async_io;
mod sync_io;

/// Maximum inode number supported by the VFS for backend file system
pub const VFS_MAX_INO: u64 = 0xff_ffff_ffff_ffff;

// The 64bit inode number for VFS is divided into two parts:
// 1. an 8-bit file-system index, to identify mounted backend file systems.
// 2. the left bits are reserved for backend file systems, and it's limited to VFS_MAX_INO.
const VFS_INDEX_SHIFT: u8 = 56;
const VFS_PSEUDO_FS_IDX: VfsIndex = 0;

type ArcBackFs<DR, S> = Arc<BackFileSystem<DR, S>>;
type VfsEitherFs<'a, D, S> = Either<&'a PseudoFs<S>, ArcBackFs<D, S>>;

type VfsHandle = u64;
/// Vfs backend file system index
pub type VfsIndex = u8;

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
}

/// Vfs result
pub type VfsResult<T> = std::result::Result<T, VfsError>;

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
/// D refers to the type of asynchronous event driver
pub type BackFileSystem<D, S> =
    Box<dyn BackendFileSystem<D, S, Inode = u64, Handle = u64> + Sync + Send>;

#[cfg(not(feature = "async-io"))]
/// BackendFileSystem abstracts all backend file systems under vfs
pub trait BackendFileSystem<D: AsyncDrive, S: BitmapSlice = ()>: FileSystem<S> {
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
pub trait BackendFileSystem<D: AsyncDrive = AsyncDriver, S: BitmapSlice = ()>:
    AsyncFileSystem<D, S>
{
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
    /// Disable fuse open request handling. When enabled, fuse open
    /// requests are always replied with ENOSYS.
    pub no_open: bool,
    /// Disable fuse opendir request handling. When enabled, fuse opendir
    /// requests are always replied with ENOSYS.
    pub no_opendir: bool,
    /// Disable fuse WRITEBACK_CACHE option so that kernel will not cache
    /// buffer writes.
    pub no_writeback: bool,
    /// Enable fuse killpriv_v2 support. When enabled, fuse file system makes sure
    /// to remove security.capability xattr and setuid/setgid bits. See details in
    /// comments for HANDLE_KILLPRIV_V2
    pub killpriv_v2: bool,
    /// File system options passed in from client
    pub in_opts: FsOptions,
    /// File system options returned to client
    pub out_opts: FsOptions,
}

impl Default for VfsOptions {
    fn default() -> Self {
        VfsOptions {
            no_open: true,
            no_opendir: true,
            no_writeback: false,
            killpriv_v2: false,
            in_opts: FsOptions::empty(),
            out_opts: FsOptions::ASYNC_READ
                | FsOptions::PARALLEL_DIROPS
                | FsOptions::BIG_WRITES
                | FsOptions::ASYNC_DIO
                | FsOptions::HAS_IOCTL_DIR
                | FsOptions::WRITEBACK_CACHE
                | FsOptions::ZERO_MESSAGE_OPEN
                | FsOptions::ATOMIC_O_TRUNC
                | FsOptions::CACHE_SYMLINKS
                | FsOptions::DO_READDIRPLUS
                | FsOptions::READDIRPLUS_AUTO
                | FsOptions::ZERO_MESSAGE_OPENDIR
                | FsOptions::HANDLE_KILLPRIV_V2,
        }
    }
}

/// A union fs that combines multiple backend file systems.
pub struct Vfs<D: AsyncDrive = AsyncDriver, S: BitmapSlice = ()> {
    next_super: AtomicU8,
    root: PseudoFs<S>,
    // mountpoints maps from pseudo fs inode to mounted fs mountpoint data
    mountpoints: ArcSwap<HashMap<u64, Arc<MountPointData>>>,
    // superblocks keeps track of all mounted file systems
    superblocks: ArcSwap<HashMap<VfsIndex, Arc<BackFileSystem<D, S>>>>,
    opts: ArcSwap<VfsOptions>,
    initialized: AtomicBool,
    lock: Mutex<()>,
    phantom: PhantomData<D>,
    phantom2: PhantomData<S>,
}

impl<D: AsyncDrive, S: BitmapSlice> Default for Vfs<D, S> {
    fn default() -> Self {
        Self::new(VfsOptions::default())
    }
}

impl<D: AsyncDrive, S: BitmapSlice> Vfs<D, S> {
    /// Create a new vfs instance
    pub fn new(opts: VfsOptions) -> Self {
        Vfs {
            next_super: AtomicU8::new((VFS_PSEUDO_FS_IDX + 1) as u8),
            mountpoints: ArcSwap::new(Arc::new(HashMap::new())),
            superblocks: ArcSwap::new(Arc::new(HashMap::new())),
            root: PseudoFs::new(),
            opts: ArcSwap::new(Arc::new(opts)),
            lock: Mutex::new(()),
            initialized: AtomicBool::new(false),
            phantom: PhantomData,
            phantom2: PhantomData,
        }
    }

    /// For sake of live-upgrade, only after negotiation is done, it's safe to persist
    /// state of vfs.
    pub fn initialized(&self) -> bool {
        self.initialized.load(Ordering::Acquire)
    }

    fn insert_mount_locked(
        &self,
        fs: BackFileSystem<D, S>,
        mut entry: Entry,
        fs_idx: VfsIndex,
        path: &str,
    ) -> Result<()> {
        let inode = self.root.mount(path)?;
        entry.inode = self.convert_inode(fs_idx, entry.inode)?;

        // The visibility of mountpoints and superblocks:
        // superblock should be committed first because it won't be accessed until
        // a lookup returns a cross mountpoint inode.
        let mut superblocks = self.superblocks.load().deref().deref().clone();
        let mut mountpoints = self.mountpoints.load().deref().deref().clone();

        // Over mount would invalidate previous superblock inodes.
        if let Some(mnt) = mountpoints.get(&inode) {
            superblocks.remove(&mnt.fs_idx);
        }
        superblocks.insert(fs_idx, Arc::new(fs));
        self.superblocks.store(Arc::new(superblocks));
        trace!("fs_idx {} inode {}", fs_idx, inode);

        mountpoints.insert(
            inode,
            Arc::new(MountPointData {
                fs_idx,
                ino: ROOT_ID,
                root_entry: entry,
                _path: path.to_string(),
            }),
        );
        self.mountpoints.store(Arc::new(mountpoints));

        Ok(())
    }

    /// Mount a backend file system to path
    pub fn mount(&self, fs: BackFileSystem<D, S>, path: &str) -> VfsResult<VfsIndex> {
        let (entry, ino) = fs.mount().map_err(VfsError::Mount)?;
        if ino > VFS_MAX_INO {
            fs.destroy();
            return Err(VfsError::InodeIndex(format!(
                "Unsupported max inode number, requested {} supported {}",
                ino, VFS_MAX_INO
            )));
        }

        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        if self.initialized() {
            let opts = self.opts.load().deref().out_opts;
            fs.init(opts).map_err(|e| {
                VfsError::Initialize(format!("Can't initialize with opts {:?}, {:?}", opts, e))
            })?;
        }
        let index = self.allocate_fs_idx().map_err(VfsError::FsIndex)?;
        self.insert_mount_locked(fs, entry, index, path)
            .map_err(VfsError::Mount)?;

        Ok(index)
    }

    /// Umount a backend file system at path
    pub fn umount(&self, path: &str) -> VfsResult<()> {
        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        let inode = self
            .root
            .path_walk(path)
            .map_err(VfsError::PathWalk)?
            .ok_or_else(|| VfsError::NotFound(path.to_string()))?;

        let mut mountpoints = self.mountpoints.load().deref().deref().clone();
        let fs_idx = mountpoints
            .get(&inode)
            .map(Arc::clone)
            .map(|x| {
                self.root.evict_inode(inode);
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
        if let Some(fs) = superblocks.remove(&fs_idx) {
            fs.destroy();
        }
        self.superblocks.store(Arc::new(superblocks));

        Ok(())
    }

    /// Get the mounted backend file system alongside the path if there's one.
    pub fn get_rootfs(&self, path: &str) -> VfsResult<Option<Arc<BackFileSystem<D, S>>>> {
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
                format!(
                    "Inode number {} too large, max supported {}",
                    inode, VFS_MAX_INO
                ),
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
            if superblocks.contains_key(&index) {
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

    fn get_fs_by_idx(&self, fs_idx: VfsIndex) -> Result<Arc<BackFileSystem<D, S>>> {
        self.superblocks
            .load()
            .get(&fs_idx)
            .map(Arc::clone)
            .ok_or_else(|| Error::from_raw_os_error(libc::ENOENT))
    }

    fn get_real_rootfs(&self, inode: VfsInode) -> Result<(VfsEitherFs<'_, D, S>, VfsInode)> {
        // ROOT_ID is special, we need to check if we have a mountpoint on the vfs root
        if inode.is_pseudo_fs() && inode.ino() == ROOT_ID {
            if let Some(mnt) = self.mountpoints.load().get(&inode.ino()).map(Arc::clone) {
                let fs = self.get_fs_by_idx(mnt.fs_idx)?;
                return Ok((Right(fs), VfsInode::new(mnt.fs_idx, ROOT_ID)));
            }
        }

        if inode.is_pseudo_fs() {
            Ok((Left(&self.root), inode))
        } else {
            let fs = self.get_fs_by_idx(inode.fs_idx())?;
            Ok((Right(fs), inode))
        }
    }

    fn lookup_pseudo(
        &self,
        fs: &PseudoFs<S>,
        idata: VfsInode,
        ctx: Context,
        name: &CStr,
    ) -> Result<Entry> {
        trace!("lookup pseudo ino {} name {:?}", idata.ino(), name);
        let mut entry = fs.lookup(ctx, idata.ino(), name)?;

        match self.mountpoints.load().get(&entry.inode) {
            Some(mnt) => {
                // cross mountpoint, return mount root entry
                entry = mnt.root_entry;
                entry.inode = self.convert_inode(mnt.fs_idx, mnt.ino)?;
                trace!(
                    "vfs lookup cross mountpoint, return new mount fs_idx {} inode {} fuse inode {}",
                    mnt.fs_idx,
                    mnt.ino,
                    entry.inode
                );
            }
            None => entry.inode = self.convert_inode(idata.fs_idx(), entry.inode)?,
        }

        Ok(entry)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::api::Vfs;
    use crate::async_util::AsyncDriver;
    use std::ffi::CString;

    #[cfg(feature = "async-io")]
    use crate::abi::linux_abi::{OpenOptions, SetattrValid};
    #[cfg(feature = "async-io")]
    use async_trait::async_trait;

    pub(crate) struct FakeFileSystemOne {}
    impl FileSystem for FakeFileSystemOne {
        type Inode = u64;
        type Handle = u64;
        fn lookup(&self, _: Context, _: Self::Inode, _: &CStr) -> Result<Entry> {
            Ok(Entry {
                inode: 0,
                generation: 0,
                attr: Attr::default().into(),
                attr_timeout: Duration::new(0, 0),
                entry_timeout: Duration::new(0, 0),
            })
        }
    }

    #[cfg(feature = "async-io")]
    #[allow(unused_variables)]
    #[async_trait]
    impl AsyncFileSystem for FakeFileSystemOne {
        async fn async_lookup(
            &self,
            ctx: Context,
            parent: <Self as FileSystem>::Inode,
            name: &CStr,
        ) -> Result<Entry> {
            Ok(Entry {
                inode: 0,
                generation: 0,
                attr: unsafe { std::mem::zeroed() },
                attr_timeout: Default::default(),
                entry_timeout: Default::default(),
            })
        }

        async fn async_getattr(
            &self,
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            handle: Option<<Self as FileSystem>::Handle>,
        ) -> Result<(libc::stat64, Duration)> {
            unimplemented!()
        }

        async fn async_setattr(
            &self,
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            attr: libc::stat64,
            handle: Option<<Self as FileSystem>::Handle>,
            valid: SetattrValid,
        ) -> Result<(libc::stat64, Duration)> {
            unimplemented!()
        }

        async fn async_open(
            &self,
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            flags: u32,
            fuse_flags: u32,
        ) -> Result<(Option<<Self as FileSystem>::Handle>, OpenOptions)> {
            unimplemented!()
        }

        async fn async_create(
            &self,
            ctx: Context,
            parent: <Self as FileSystem>::Inode,
            name: &CStr,
            args: CreateIn,
        ) -> Result<(Entry, Option<<Self as FileSystem>::Handle>, OpenOptions)> {
            unimplemented!()
        }

        async fn async_read(
            &self,
            ctx: Context,
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
            ctx: Context,
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
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            datasync: bool,
            handle: <Self as FileSystem>::Handle,
        ) -> Result<()> {
            unimplemented!()
        }

        async fn async_fallocate(
            &self,
            ctx: Context,
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
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            datasync: bool,
            handle: <Self as FileSystem>::Handle,
        ) -> Result<()> {
            unimplemented!()
        }
    }

    #[cfg(feature = "async-io")]
    impl BackendFileSystem for FakeFileSystemOne {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    generation: 0,
                    attr: Attr::default().into(),
                    attr_timeout: Duration::new(0, 0),
                    entry_timeout: Duration::new(0, 0),
                },
                0,
            ))
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    #[cfg(not(feature = "async-io"))]
    impl BackendFileSystem<AsyncDriver, ()> for FakeFileSystemOne {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    generation: 0,
                    attr: Attr::default().into(),
                    attr_timeout: Duration::new(0, 0),
                    entry_timeout: Duration::new(0, 0),
                },
                0,
            ))
        }

        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    pub(crate) struct FakeFileSystemTwo {}
    impl FileSystem for FakeFileSystemTwo {
        type Inode = u64;
        type Handle = u64;
        fn lookup(&self, _: Context, _: Self::Inode, _: &CStr) -> Result<Entry> {
            Ok(Entry {
                inode: 1,
                generation: 0,
                attr: Attr::default().into(),
                attr_timeout: Duration::new(0, 0),
                entry_timeout: Duration::new(0, 0),
            })
        }
    }

    #[cfg(feature = "async-io")]
    #[allow(unused_variables)]
    #[async_trait]
    impl AsyncFileSystem for FakeFileSystemTwo {
        async fn async_lookup(
            &self,
            ctx: Context,
            parent: <Self as FileSystem>::Inode,
            name: &CStr,
        ) -> Result<Entry> {
            Err(std::io::Error::from_raw_os_error(libc::EINVAL))
        }

        async fn async_getattr(
            &self,
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            handle: Option<<Self as FileSystem>::Handle>,
        ) -> Result<(libc::stat64, Duration)> {
            unimplemented!()
        }

        async fn async_setattr(
            &self,
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            attr: libc::stat64,
            handle: Option<<Self as FileSystem>::Handle>,
            valid: SetattrValid,
        ) -> Result<(libc::stat64, Duration)> {
            unimplemented!()
        }

        async fn async_open(
            &self,
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            flags: u32,
            fuse_flags: u32,
        ) -> Result<(Option<<Self as FileSystem>::Handle>, OpenOptions)> {
            unimplemented!()
        }

        async fn async_create(
            &self,
            ctx: Context,
            parent: <Self as FileSystem>::Inode,
            name: &CStr,
            args: CreateIn,
        ) -> Result<(Entry, Option<<Self as FileSystem>::Handle>, OpenOptions)> {
            unimplemented!()
        }

        async fn async_read(
            &self,
            ctx: Context,
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
            ctx: Context,
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
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            datasync: bool,
            handle: <Self as FileSystem>::Handle,
        ) -> Result<()> {
            unimplemented!()
        }

        async fn async_fallocate(
            &self,
            ctx: Context,
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
            ctx: Context,
            inode: <Self as FileSystem>::Inode,
            datasync: bool,
            handle: <Self as FileSystem>::Handle,
        ) -> Result<()> {
            unimplemented!()
        }
    }

    #[cfg(feature = "async-io")]
    impl BackendFileSystem for FakeFileSystemTwo {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    generation: 0,
                    attr: Attr::default().into(),
                    attr_timeout: Duration::new(0, 0),
                    entry_timeout: Duration::new(0, 0),
                },
                0,
            ))
        }
        fn as_any(&self) -> &dyn Any {
            self
        }
    }

    #[cfg(not(feature = "async-io"))]
    impl BackendFileSystem<AsyncDriver, ()> for FakeFileSystemTwo {
        fn mount(&self) -> Result<(Entry, u64)> {
            Ok((
                Entry {
                    inode: 1,
                    generation: 0,
                    attr: Attr::default().into(),
                    attr_timeout: Duration::new(0, 0),
                    entry_timeout: Duration::new(0, 0),
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
        let vfs = Vfs::<AsyncDriver>::default();
        assert_eq!(vfs.initialized(), false);

        let out_opts = FsOptions::ASYNC_READ
            | FsOptions::PARALLEL_DIROPS
            | FsOptions::BIG_WRITES
            | FsOptions::ASYNC_DIO
            | FsOptions::HAS_IOCTL_DIR
            | FsOptions::WRITEBACK_CACHE
            | FsOptions::ZERO_MESSAGE_OPEN
            | FsOptions::ATOMIC_O_TRUNC
            | FsOptions::CACHE_SYMLINKS
            | FsOptions::DO_READDIRPLUS
            | FsOptions::READDIRPLUS_AUTO
            | FsOptions::ZERO_MESSAGE_OPENDIR
            | FsOptions::HANDLE_KILLPRIV_V2;
        let opts = vfs.opts.load();

        assert_eq!(opts.no_open, true);
        assert_eq!(opts.no_opendir, true);
        assert_eq!(opts.no_writeback, false);
        assert_eq!(opts.killpriv_v2, false);
        assert_eq!(opts.in_opts.is_empty(), true);
        assert_eq!(opts.out_opts, out_opts);

        vfs.init(FsOptions::ASYNC_READ).unwrap();
        assert_eq!(vfs.initialized(), true);

        let opts = vfs.opts.load();
        assert_eq!(opts.no_open, false);
        assert_eq!(opts.no_opendir, false);
        assert_eq!(opts.no_writeback, false);
        assert_eq!(opts.killpriv_v2, false);

        vfs.destroy();
        assert_eq!(vfs.initialized(), false);

        let vfs = Vfs::<AsyncDriver>::default();
        let in_opts =
            FsOptions::ASYNC_READ | FsOptions::ZERO_MESSAGE_OPEN | FsOptions::ZERO_MESSAGE_OPENDIR;
        vfs.init(in_opts).unwrap();
        let opts = vfs.opts.load();
        assert_eq!(opts.no_open, true);
        assert_eq!(opts.no_opendir, true);
        assert_eq!(opts.no_writeback, false);
        assert_eq!(opts.killpriv_v2, false);
        assert_eq!(opts.out_opts, out_opts & in_opts);
    }

    #[test]
    fn test_vfs_lookup() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs = FakeFileSystemOne {};
        let ctx = Context {
            uid: 0,
            gid: 0,
            pid: 0,
            #[cfg(feature = "async-io")]
            drive: 0,
        };

        assert!(vfs.mount(Box::new(fs), "/x/y").is_ok());

        // Lookup inode on pseudo file system.
        let entry1 = vfs
            .lookup(ctx, ROOT_ID.into(), CString::new("x").unwrap().as_c_str())
            .unwrap();
        assert_eq!(entry1.inode, 0x2);

        // Lookup inode on mounted file system.
        let entry2 = vfs
            .lookup(
                ctx,
                entry1.inode.into(),
                CString::new("y").unwrap().as_c_str(),
            )
            .unwrap();
        assert_eq!(entry2.inode, 0x100_0000_0000_0001);

        // lookup for negative result.
        let entry3 = vfs
            .lookup(
                ctx,
                entry2.inode.into(),
                CString::new("z").unwrap().as_c_str(),
            )
            .unwrap();
        assert_eq!(entry3.inode, 0);
    }

    #[test]
    fn test_mount_different_fs_types() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemTwo {};
        assert!(vfs.mount(Box::new(fs1), "/foo").is_ok());
        assert!(vfs.mount(Box::new(fs2), "/bar").is_ok());
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

            superblocks.insert(index, Arc::new(Box::new(fs)));
            vfs.superblocks.store(Arc::new(superblocks));
        }

        // Test case: fail to allocate more fs idx if all have been allocated
        for _ in 0..=256 {
            vfs.allocate_fs_idx().unwrap_err();
        }
    }
}
