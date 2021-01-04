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
use std::ops::Deref;
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Duration;

use arc_swap::ArcSwap;

use super::pseudo_fs::PseudoFs;
use crate::abi::linux_abi::*;
use crate::api::filesystem::*;

/// Maximum inode number supported by the VFS for backend file system
pub const VFS_MAX_INO: u64 = 0xff_ffff_ffff_ffff;

// The 64bit inode number for VFS is divided into two parts:
// 1. an 8-bit file-system index, to identify mounted backend file systems.
// 2. the left bits are reserved for backend file systems, and it's limited to VFS_MAX_INO.
const VFS_INDEX_SHIFT: u8 = 56;
const VFS_PSEUDO_FS_IDX: VfsIndex = 0;

type VfsHandle = u64;
/// Vfs backend file system index
pub type VfsIndex = u8;

/// Data struct to store inode number for the VFS filesystem.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub struct VfsInode(u64);

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

type BackFileSystem = Box<dyn BackendFileSystem<Inode = u64, Handle = u64> + Sync + Send>;

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
                | FsOptions::ZERO_MESSAGE_OPENDIR,
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
    superblocks: ArcSwap<HashMap<VfsIndex, Arc<BackFileSystem>>>,
    opts: ArcSwap<VfsOptions>,
    initialized: AtomicBool,
    lock: Mutex<()>,
}

impl Default for Vfs {
    fn default() -> Self {
        Self::new(VfsOptions::default())
    }
}

impl Vfs {
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
        }
    }

    /// For sake of live-upgrade, only after negotiation is done, it's safe to persist
    /// state of vfs.
    pub fn initialized(&self) -> bool {
        self.initialized.load(Ordering::Acquire)
    }

    fn insert_mount_locked(
        &self,
        fs: BackFileSystem,
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
        let mountpoints = self.mountpoints.load().deref().deref().clone();

        // Over mount would invalidate previous superblock inodes.
        if let Some(mnt) = mountpoints.get(&inode) {
            superblocks.remove(&mnt.fs_idx);
        }
        superblocks.insert(fs_idx, Arc::new(fs));
        self.superblocks.store(Arc::new(superblocks));
        trace!("fs_idx {} inode {}", fs_idx, inode);

        let mut mountpoints = self.mountpoints.load().deref().deref().clone();
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
    pub fn mount(&self, fs: BackFileSystem, path: &str) -> Result<VfsIndex> {
        let (entry, ino) = fs.mount()?;
        if ino > VFS_MAX_INO {
            fs.destroy();
            return Err(Error::new(
                ErrorKind::Other,
                format!(
                    "Unsupported max inode number, requested {} supported {}",
                    ino, VFS_MAX_INO
                ),
            ));
        }

        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        if self.initialized() {
            fs.init(self.opts.load().deref().out_opts)?;
        }
        let index = self.allocate_fs_idx()?;
        self.insert_mount_locked(fs, entry, index, path)?;

        Ok(index)
    }

    /// Umount a backend file system at path
    pub fn umount(&self, path: &str) -> Result<()> {
        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        let inode = self.root.path_walk(path)?;

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
                Error::from_raw_os_error(libc::EINVAL)
            })?;

        trace!("fs_idx {}", fs_idx);

        let mut superblocks = self.superblocks.load().deref().deref().clone();
        let fs = superblocks.get(&fs_idx).map(Arc::clone).unwrap();
        fs.destroy();
        superblocks.remove(&fs_idx);
        self.superblocks.store(Arc::new(superblocks));

        Ok(())
    }

    /// Get the mounted backend file system alongside the path if there's one.
    pub fn get_rootfs(&self, path: &str) -> Result<Arc<BackFileSystem>> {
        // Serialize mount operations. Do not expect poisoned lock here.
        let _guard = self.lock.lock().unwrap();
        let inode = self.root.path_walk(path)?;

        if let Some(mnt) = self.mountpoints.load().get(&inode).map(Arc::clone) {
            trace!("mnt.fs_idx {} inode {}", mnt.fs_idx, inode);
            self.get_fs_by_idx(mnt.fs_idx)
        } else {
            error!("inode {} is not found\n", inode);
            Err(Error::from_raw_os_error(libc::EINVAL))
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

    fn get_fs_by_idx(&self, fs_idx: VfsIndex) -> Result<Arc<BackFileSystem>> {
        self.superblocks
            .load()
            .get(&fs_idx)
            .map(Arc::clone)
            .ok_or_else(|| Error::from_raw_os_error(libc::ENOENT))
    }

    fn get_real_rootfs(
        &self,
        inode: VfsInode,
    ) -> Result<(Either<&PseudoFs, Arc<BackFileSystem>>, VfsInode)> {
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
}

impl FileSystem for Vfs {
    type Inode = VfsInode;
    type Handle = VfsHandle;

    fn init(&self, opts: FsOptions) -> Result<FsOptions> {
        if self.initialized() {
            error!("vfs is already initialized");
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }
        let mut n_opts = *self.opts.load().deref().deref();
        if n_opts.no_open {
            n_opts.no_open = !(opts & FsOptions::ZERO_MESSAGE_OPEN).is_empty();
        }
        n_opts.no_opendir = !(opts & FsOptions::ZERO_MESSAGE_OPENDIR).is_empty();
        if n_opts.no_writeback {
            n_opts.out_opts.remove(FsOptions::WRITEBACK_CACHE);
        }
        n_opts.in_opts = opts;

        n_opts.out_opts &= opts;
        self.opts.store(Arc::new(n_opts));

        {
            // Serialize mount operations. Do not expect poisoned lock here.
            // Ensure that every backend fs only get init()ed once.
            let _guard = self.lock.lock().unwrap();
            for (_, fs) in self.superblocks.load().iter() {
                fs.init(n_opts.out_opts)?;
            }
            self.initialized.store(true, Ordering::Release);
        }

        Ok(n_opts.out_opts)
    }

    fn destroy(&self) {
        if self.initialized() {
            self.superblocks
                .load()
                .iter()
                .for_each(|(_, f)| f.destroy());

            // Keep initialized true to avoid being attacked by guest
            // self.initialized.store(false, Ordering::Release);
        }
    }

    fn lookup(&self, ctx: Context, parent: VfsInode, name: &CStr) -> Result<Entry> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => {
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
            (Right(fs), idata) => {
                // parent is in an underlying rootfs
                let mut entry = fs.lookup(ctx, idata.ino(), name)?;
                // lookup success, hash it to a real fuse inode
                entry.inode = self.convert_inode(idata.fs_idx(), entry.inode)?;
                Ok(entry)
            }
        }
    }

    fn forget(&self, ctx: Context, inode: VfsInode, count: u64) {
        match self.get_real_rootfs(inode) {
            Ok(real_rootfs) => match real_rootfs {
                (Left(fs), idata) => fs.forget(ctx, idata.ino(), count),
                (Right(fs), idata) => fs.forget(ctx, idata.ino(), count),
            },
            Err(e) => {
                error!("vfs::forget: failed to get_real_rootfs {:?}", e);
            }
        }
    }

    fn getattr(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: Option<VfsHandle>,
    ) -> Result<(libc::stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getattr(ctx, idata.ino(), handle),
            (Right(fs), idata) => fs.getattr(ctx, idata.ino(), handle),
        }
    }

    fn setattr(
        &self,
        ctx: Context,
        inode: VfsInode,
        attr: libc::stat64,
        handle: Option<u64>,
        valid: SetattrValid,
    ) -> Result<(libc::stat64, Duration)> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setattr(ctx, idata.ino(), attr, handle, valid),
            (Right(fs), idata) => fs.setattr(ctx, idata.ino(), attr, handle, valid),
        }
    }

    fn readlink(&self, ctx: Context, inode: VfsInode) -> Result<Vec<u8>> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.readlink(ctx, idata.ino()),
            (Right(fs), idata) => fs.readlink(ctx, idata.ino()),
        }
    }

    fn symlink(
        &self,
        ctx: Context,
        linkname: &CStr,
        parent: VfsInode,
        name: &CStr,
    ) -> Result<Entry> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.symlink(ctx, linkname, idata.ino(), name),
            (Right(fs), idata) => fs.symlink(ctx, linkname, idata.ino(), name).map(|mut e| {
                e.inode = self.convert_inode(idata.fs_idx(), e.inode)?;
                Ok(e)
            })?,
        }
    }

    fn mknod(
        &self,
        ctx: Context,
        inode: VfsInode,
        name: &CStr,
        mode: u32,
        rdev: u32,
        umask: u32,
    ) -> Result<Entry> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.mknod(ctx, idata.ino(), name, mode, rdev, umask),
            (Right(fs), idata) => {
                fs.mknod(ctx, idata.ino(), name, mode, rdev, umask)
                    .map(|mut e| {
                        e.inode = self.convert_inode(idata.fs_idx(), e.inode)?;
                        Ok(e)
                    })?
            }
        }
    }

    fn mkdir(
        &self,
        ctx: Context,
        parent: VfsInode,
        name: &CStr,
        mode: u32,
        umask: u32,
    ) -> Result<Entry> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.mkdir(ctx, idata.ino(), name, mode, umask),
            (Right(fs), idata) => fs.mkdir(ctx, idata.ino(), name, mode, umask).map(|mut e| {
                e.inode = self.convert_inode(idata.fs_idx(), e.inode)?;
                Ok(e)
            })?,
        }
    }

    fn unlink(&self, ctx: Context, parent: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.unlink(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.unlink(ctx, idata.ino(), name),
        }
    }

    fn rmdir(&self, ctx: Context, parent: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.rmdir(ctx, idata.ino(), name),
        }
    }

    fn rename(
        &self,
        ctx: Context,
        olddir: VfsInode,
        oldname: &CStr,
        newdir: VfsInode,
        newname: &CStr,
        flags: u32,
    ) -> Result<()> {
        let (root, idata_old) = self.get_real_rootfs(olddir)?;
        let (_, idata_new) = self.get_real_rootfs(newdir)?;

        if idata_old.fs_idx() != idata_new.fs_idx() {
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }

        match root {
            Left(fs) => fs.rename(
                ctx,
                idata_old.ino(),
                oldname,
                idata_new.ino(),
                newname,
                flags,
            ),
            Right(fs) => fs.rename(
                ctx,
                idata_old.ino(),
                oldname,
                idata_new.ino(),
                newname,
                flags,
            ),
        }
    }

    fn link(
        &self,
        ctx: Context,
        inode: VfsInode,
        newparent: VfsInode,
        newname: &CStr,
    ) -> Result<Entry> {
        let (root, idata_old) = self.get_real_rootfs(inode)?;
        let (_, idata_new) = self.get_real_rootfs(newparent)?;

        if idata_old.fs_idx() != idata_new.fs_idx() {
            return Err(Error::from_raw_os_error(libc::EINVAL));
        }

        match root {
            Left(fs) => fs.link(ctx, idata_old.ino(), idata_new.ino(), newname),
            Right(fs) => fs
                .link(ctx, idata_old.ino(), idata_new.ino(), newname)
                .map(|mut e| {
                    e.inode = self.convert_inode(idata_new.fs_idx(), e.inode)?;
                    Ok(e)
                })?,
        }
    }

    fn open(
        &self,
        ctx: Context,
        inode: VfsInode,
        flags: u32,
    ) -> Result<(Option<u64>, OpenOptions)> {
        if self.opts.load().no_open {
            Err(Error::from_raw_os_error(libc::ENOSYS))
        } else {
            match self.get_real_rootfs(inode)? {
                (Left(fs), idata) => fs.open(ctx, idata.ino(), flags),
                (Right(fs), idata) => fs
                    .open(ctx, idata.ino(), flags)
                    .map(|(h, opt)| (h.map(Into::into), opt)),
            }
        }
    }

    fn create(
        &self,
        ctx: Context,
        parent: VfsInode,
        name: &CStr,
        mode: u32,
        flags: u32,
        umask: u32,
    ) -> Result<(Entry, Option<u64>, OpenOptions)> {
        match self.get_real_rootfs(parent)? {
            (Left(fs), idata) => fs.create(ctx, idata.ino(), name, mode, flags, umask),
            (Right(fs), idata) => {
                fs.create(ctx, idata.ino(), name, mode, flags, umask)
                    .map(|(mut a, b, c)| {
                        a.inode = self.convert_inode(idata.fs_idx(), a.inode)?;
                        Ok((a, b, c))
                    })?
            }
        }
    }

    fn read(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        w: &mut dyn ZeroCopyWriter,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> Result<usize> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                fs.read(ctx, idata.ino(), handle, w, size, offset, lock_owner, flags)
            }
            (Right(fs), idata) => {
                fs.read(ctx, idata.ino(), handle, w, size, offset, lock_owner, flags)
            }
        }
    }

    fn write(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        r: &mut dyn ZeroCopyReader,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
    ) -> Result<usize> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.write(
                ctx,
                idata.ino(),
                handle,
                r,
                size,
                offset,
                lock_owner,
                delayed_write,
                flags,
            ),
            (Right(fs), idata) => fs.write(
                ctx,
                idata.ino(),
                handle,
                r,
                size,
                offset,
                lock_owner,
                delayed_write,
                flags,
            ),
        }
    }

    fn flush(&self, ctx: Context, inode: VfsInode, handle: u64, lock_owner: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
            (Right(fs), idata) => fs.flush(ctx, idata.ino(), handle, lock_owner),
        }
    }

    fn fsync(&self, ctx: Context, inode: VfsInode, datasync: bool, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.fsync(ctx, idata.ino(), datasync, handle),
        }
    }

    fn fallocate(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fallocate(ctx, idata.ino(), handle, mode, offset, length),
            (Right(fs), idata) => fs.fallocate(ctx, idata.ino(), handle, mode, offset, length),
        }
    }

    fn release(
        &self,
        ctx: Context,
        inode: VfsInode,
        flags: u32,
        handle: u64,
        flush: bool,
        flock_release: bool,
        lock_owner: Option<u64>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.release(
                ctx,
                idata.ino(),
                flags,
                handle,
                flush,
                flock_release,
                lock_owner,
            ),
            (Right(fs), idata) => fs.release(
                ctx,
                idata.ino(),
                flags,
                handle,
                flush,
                flock_release,
                lock_owner,
            ),
        }
    }

    fn statfs(&self, ctx: Context, inode: VfsInode) -> Result<libc::statvfs64> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.statfs(ctx, idata.ino()),
            (Right(fs), idata) => fs.statfs(ctx, idata.ino()),
        }
    }

    fn setxattr(
        &self,
        ctx: Context,
        inode: VfsInode,
        name: &CStr,
        value: &[u8],
        flags: u32,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.setxattr(ctx, idata.ino(), name, value, flags),
            (Right(fs), idata) => fs.setxattr(ctx, idata.ino(), name, value, flags),
        }
    }

    fn getxattr(
        &self,
        ctx: Context,
        inode: VfsInode,
        name: &CStr,
        size: u32,
    ) -> Result<GetxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
            (Right(fs), idata) => fs.getxattr(ctx, idata.ino(), name, size),
        }
    }

    fn listxattr(&self, ctx: Context, inode: VfsInode, size: u32) -> Result<ListxattrReply> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
            (Right(fs), idata) => fs.listxattr(ctx, idata.ino(), size),
        }
    }

    fn removexattr(&self, ctx: Context, inode: VfsInode, name: &CStr) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
            (Right(fs), idata) => fs.removexattr(ctx, idata.ino(), name),
        }
    }

    fn opendir(
        &self,
        ctx: Context,
        inode: VfsInode,
        flags: u32,
    ) -> Result<(Option<VfsHandle>, OpenOptions)> {
        if self.opts.load().no_opendir {
            Err(Error::from_raw_os_error(libc::ENOSYS))
        } else {
            match self.get_real_rootfs(inode)? {
                (Left(fs), idata) => fs.opendir(ctx, idata.ino(), flags),
                (Right(fs), idata) => fs
                    .opendir(ctx, idata.ino(), flags)
                    .map(|(h, opt)| (h.map(Into::into), opt)),
            }
        }
    }

    fn readdir(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry) -> Result<usize>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => {
                fs.readdir(
                    ctx,
                    idata.ino(),
                    handle,
                    size,
                    offset,
                    &mut |mut dir_entry| {
                        match self.mountpoints.load().get(&dir_entry.ino) {
                            // cross mountpoint, return mount root entry
                            Some(mnt) => {
                                dir_entry.ino = self.convert_inode(mnt.fs_idx, mnt.ino)?;
                            }
                            None => {
                                dir_entry.ino =
                                    self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                            }
                        }
                        add_entry(dir_entry)
                    },
                )
            }

            (Right(fs), idata) => fs.readdir(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry| {
                    dir_entry.ino = self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                    add_entry(dir_entry)
                },
            ),
        }
    }

    fn readdirplus(
        &self,
        ctx: Context,
        inode: VfsInode,
        handle: u64,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, Entry) -> Result<usize>,
    ) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.readdirplus(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry, mut entry| {
                    match self.mountpoints.load().get(&dir_entry.ino) {
                        Some(mnt) => {
                            // cross mountpoint, return mount root entry
                            dir_entry.ino = self.convert_inode(mnt.fs_idx, mnt.ino)?;
                            entry = mnt.root_entry;
                        }
                        None => {
                            dir_entry.ino = self.convert_inode(idata.fs_idx(), dir_entry.ino)?;
                            entry.inode = dir_entry.ino;
                        }
                    }

                    add_entry(dir_entry, entry)
                },
            ),

            (Right(fs), idata) => fs.readdirplus(
                ctx,
                idata.ino(),
                handle,
                size,
                offset,
                &mut |mut dir_entry, mut entry| {
                    dir_entry.ino = self.convert_inode(idata.fs_idx(), entry.inode)?;
                    entry.inode = dir_entry.ino;
                    add_entry(dir_entry, entry)
                },
            ),
        }
    }

    fn fsyncdir(&self, ctx: Context, inode: VfsInode, datasync: bool, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
            (Right(fs), idata) => fs.fsyncdir(ctx, idata.ino(), datasync, handle),
        }
    }

    fn releasedir(&self, ctx: Context, inode: VfsInode, flags: u32, handle: u64) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
            (Right(fs), idata) => fs.releasedir(ctx, idata.ino(), flags, handle),
        }
    }

    fn access(&self, ctx: Context, inode: VfsInode, mask: u32) -> Result<()> {
        match self.get_real_rootfs(inode)? {
            (Left(fs), idata) => fs.access(ctx, idata.ino(), mask),
            (Right(fs), idata) => fs.access(ctx, idata.ino(), mask),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CString;

    struct FakeFileSystemOne {}
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

    struct FakeFileSystemTwo {}
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

    #[test]
    fn test_vfs_init() {
        let vfs = Vfs::default();
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
            | FsOptions::ZERO_MESSAGE_OPENDIR;
        let opts = vfs.opts.load();

        assert_eq!(opts.no_open, true);
        assert_eq!(opts.no_opendir, true);
        assert_eq!(opts.no_writeback, false);
        assert_eq!(opts.in_opts, FsOptions::empty());
        assert_eq!(opts.out_opts, out_opts);

        vfs.init(FsOptions::ASYNC_READ).unwrap();
        assert_eq!(vfs.initialized(), true);

        let opts = vfs.opts.load();
        assert_eq!(opts.no_open, false);
        assert_eq!(opts.no_opendir, false);
        assert_eq!(opts.no_writeback, false);

        vfs.destroy();
        assert!(vfs.initialized());

        let vfs = Vfs::default();
        let in_opts =
            FsOptions::ASYNC_READ | FsOptions::ZERO_MESSAGE_OPEN | FsOptions::ZERO_MESSAGE_OPENDIR;
        vfs.init(in_opts).unwrap();
        let opts = vfs.opts.load();
        assert_eq!(opts.no_open, true);
        assert_eq!(opts.no_opendir, true);
        assert_eq!(opts.no_writeback, false);
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
        assert_eq!(
            vfs.umount("/x").unwrap_err().raw_os_error().unwrap(),
            libc::EINVAL
        );
    }

    #[test]
    fn test_umount_overlap() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemTwo {};

        assert!(vfs.mount(Box::new(fs1), "/x/y/z").is_ok());
        assert!(vfs.mount(Box::new(fs2), "/x/y").is_ok());

        let m1 = vfs.get_rootfs("/x/y/z").unwrap();
        assert!(m1.as_any().is::<FakeFileSystemOne>());
        let m2 = vfs.get_rootfs("/x/y").unwrap();
        assert!(m2.as_any().is::<FakeFileSystemTwo>());

        assert!(vfs.umount("/x/y/z").is_ok());
        assert!(vfs.umount("/x/y").is_ok());
        assert_eq!(
            vfs.umount("/x/y/z").unwrap_err().raw_os_error().unwrap(),
            libc::ENOENT
        );
    }

    #[test]
    fn test_umount_same() {
        let vfs = Vfs::new(VfsOptions::default());
        let fs1 = FakeFileSystemOne {};
        let fs2 = FakeFileSystemTwo {};

        assert!(vfs.mount(Box::new(fs1), "/x/y").is_ok());
        assert!(vfs.mount(Box::new(fs2), "/x/y").is_ok());

        let m1 = vfs.get_rootfs("/x/y").unwrap();
        assert!(m1.as_any().is::<FakeFileSystemTwo>());

        assert!(vfs.umount("/x/y").is_ok());
        assert_eq!(
            vfs.umount("/x/y").unwrap_err().raw_os_error().unwrap(),
            libc::ENOENT
        );
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
