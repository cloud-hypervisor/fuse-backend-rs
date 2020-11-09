// Copyright 2020 Alibaba Cloud. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![allow(missing_docs)]

use std::io::Error as IoError;
use std::ops::Deref;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use snapshot::Persist;
use versionize::{VersionMap, Versionize, VersionizeResult};
use versionize_derive::Versionize;

use crate::api::filesystem::FsOptions;
use crate::api::vfs::BackFileSystem;
use crate::api::{Vfs, VfsOptions};

// Use version map to mange resource version during serializing/deserializing,
// here is a default implementation, returns the version map with only one version,
// If you need to add a version 2 for resource, need to do like this:
// `VersionMap::new().new_version().set_type_version(Self::type_id(), 2).clone()`
pub trait VersionMapGetter {
    fn version_map() -> VersionMap {
        VersionMap::new()
    }
}

#[derive(Versionize, PartialEq, Debug)]
pub struct VfsOptionsState {
    no_open: bool,
    no_opendir: bool,
    no_writeback: bool,
    in_opts: u32,
    out_opts: u32,
}

impl Persist<'_> for VfsOptions {
    type State = VfsOptionsState;
    type ConstructorArgs = ();
    type LiveUpgradeConstructorArgs = ();
    type Error = ();

    fn save(&self) -> Self::State {
        Self::State {
            no_open: self.no_open,
            no_opendir: self.no_opendir,
            no_writeback: self.no_writeback,
            in_opts: self.in_opts.bits(),
            out_opts: self.out_opts.bits(),
        }
    }

    fn restore(
        _constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        Ok(Self {
            no_open: state.no_open,
            no_opendir: state.no_opendir,
            no_writeback: state.no_writeback,
            in_opts: FsOptions::from_bits_truncate(state.in_opts),
            out_opts: FsOptions::from_bits_truncate(state.out_opts),
        })
    }
}

// VfsState includes all information of a vfs mountpoint except of that of each backend
// filesystem. At save(), caller should save each backend file system with a proper persist
// implementation, that can match a backend state with a specified mountpoint. At restore(),
// it only restores the vfs data structures and backend file system data structures need to
// be restored via separate calls.
#[derive(Versionize, PartialEq, Debug)]
pub struct VfsState {
    /// Vfs options
    opts: VfsOptionsState,
    /// next super block index
    next_super: u8,
    /// backend fs super index, mountpoint and whether it is unmounted
    backend_fs: Vec<VfsMountpoints>,
}

impl VersionMapGetter for VfsState {}

#[derive(Versionize, PartialEq, Debug)]
pub struct VfsMountpoints {
    index: u8,
    unmounted: bool,
    path: String,
}

impl<'a> Persist<'a> for &'a Vfs {
    type State = VfsState;
    type ConstructorArgs = &'a Vfs;
    type LiveUpgradeConstructorArgs = &'a Vfs;
    type Error = IoError;

    fn save(&self) -> Self::State {
        let mut backend_fs = Vec::new();

        for (index, path) in self.unmounted_path.lock().unwrap().iter() {
            backend_fs.push(VfsMountpoints {
                index: *index,
                unmounted: true,
                path: path.to_string(),
            });
        }

        for (_, mnt) in self.mountpoints.load().iter() {
            backend_fs.push(VfsMountpoints {
                index: mnt.super_index,
                unmounted: false,
                path: mnt.path.to_string(),
            })
        }

        // store backend fs by 'super_index' order
        backend_fs.sort_by(|a, b| a.index.cmp(&b.index));

        VfsState {
            opts: self.opts.load().deref().deref().save(),
            next_super: self.next_super.load(Ordering::SeqCst),
            backend_fs,
        }
    }

    fn restore(vfs: Self::ConstructorArgs, state: &Self::State) -> Result<Self, Self::Error> {
        let opts = VfsOptions::restore((), &state.opts).unwrap();
        vfs.initialized
            .store(!opts.in_opts.is_empty(), Ordering::Release);
        vfs.opts.store(Arc::new(opts));

        vfs.next_super.store(state.next_super, Ordering::SeqCst);

        for fs in &state.backend_fs {
            // Create all components in path as directories in the pseudo file system
            vfs.root.mount(&fs.path)?;
            if fs.unmounted {
                vfs.unmounted_path
                    .lock()
                    .unwrap()
                    .insert(fs.index, fs.path.to_string());
            }
        }
        Ok(vfs)
    }

    fn live_upgrade_save(&self) -> Self::State {
        self.save()
    }
    fn live_upgrade_restore(
        vfs: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        Self::restore(vfs, state)
    }
}

impl Vfs {
    pub fn restore_mount(
        &self,
        fs: BackFileSystem,
        path: &str,
        state: &VfsState,
    ) -> std::result::Result<(), IoError> {
        for b_fs in state.backend_fs.iter() {
            if !b_fs.unmounted && path == b_fs.path {
                self.restore_backend_fs(fs, b_fs.index, path)?;
                break;
            }
        }
        Ok(())
    }
}

impl PartialEq for VfsOptions {
    fn eq(&self, other: &VfsOptions) -> bool {
        self.no_open == other.no_open
            && self.no_opendir == other.no_opendir
            && self.no_writeback == other.no_writeback
            && self.in_opts == other.in_opts
            && self.out_opts == other.out_opts
    }
}

impl PartialEq for Vfs {
    fn eq(&self, other: &Vfs) -> bool {
        let mut old_unmounted: Vec<(u8, String)> = self
            .unmounted_path
            .lock()
            .unwrap()
            .iter()
            .map(|(k, v)| (*k, v.to_string()))
            .collect();

        let mut new_unmounted: Vec<(u8, String)> = other
            .unmounted_path
            .lock()
            .unwrap()
            .iter()
            .map(|(k, v)| (*k, v.to_string()))
            .collect();

        let mut old_root_inodes: Vec<u64> =
            self.mountpoints.load().iter().map(|(&k, _)| k).collect();
        let mut new_root_inodes: Vec<u64> =
            other.mountpoints.load().iter().map(|(&k, _)| k).collect();
        let mut old_super_indexes: Vec<u8> =
            self.superblocks.load().iter().map(|(&k, _)| k).collect();
        let mut new_super_indexes: Vec<u8> =
            other.superblocks.load().iter().map(|(&k, _)| k).collect();

        old_root_inodes.sort_unstable();
        new_root_inodes.sort_unstable();
        old_super_indexes.sort_unstable();
        new_super_indexes.sort_unstable();
        old_unmounted.sort();
        new_unmounted.sort();

        self.next_super.load(Ordering::Relaxed) == other.next_super.load(Ordering::Relaxed)
            && self.opts.load().deref().deref() == other.opts.load().deref().deref()
            && old_unmounted == new_unmounted
            && old_root_inodes == new_root_inodes
            && old_super_indexes == new_super_indexes
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use crate::api::filesystem::FileSystem;
    use crate::passthrough::{Config, PassthroughFs};

    #[test]
    fn test_persist_vfs() {
        let opts = VfsOptions {
            no_open: false,
            no_writeback: true,
            ..Default::default()
        };

        let vfs = &Vfs::new(opts);
        assert!(!vfs.initialized.load(Ordering::Acquire));

        let vfs_mount_fs = |path| {
            let fs_cfg = Config::default();
            let fs = PassthroughFs::new(fs_cfg.clone()).unwrap();
            fs.import().unwrap();
            vfs.mount(Box::new(fs), path).unwrap();
        };

        vfs_mount_fs("/submnt/mnt_a");
        vfs_mount_fs("/submnt/mnt_a");
        vfs_mount_fs("/submnt/mnt_a");
        vfs.umount("/submnt/mnt_a").unwrap();
        vfs_mount_fs("/submnt/mnt_a");
        vfs_mount_fs("/submnt/mnt_a");
        vfs_mount_fs("/submnt/mnt_b");
        vfs_mount_fs("/submnt/mnt_c");
        vfs.umount("/submnt/mnt_b").unwrap();
        vfs_mount_fs("/submnt/mnt_d");
        vfs_mount_fs("/submnt/mnt_b/c/d/e");
        vfs.umount("/submnt/mnt_d").unwrap();
        vfs_mount_fs("/submnt/mnt_e");
        vfs_mount_fs("/submnt/mnt_f");
        vfs.umount("/submnt/mnt_e").unwrap();
        vfs_mount_fs("/submnt/mnt_d");

        // snapshot
        // save the state
        let mut mem = vec![0; 4096];
        let version_map = VersionMap::new();
        vfs.save()
            .serialize(&mut mem.as_mut_slice(), &version_map, 1)
            .unwrap();

        // restore the state
        let restored_vfs = &Vfs::default();
        let restored_state = VfsState::deserialize(&mut mem.as_slice(), &version_map, 1).unwrap();
        <&Vfs>::restore(&restored_vfs, &restored_state).unwrap();
        assert!(!restored_vfs.initialized.load(Ordering::Acquire));

        for b_fs in restored_state.backend_fs.iter() {
            if b_fs.unmounted {
                continue;
            }
            let fs_cfg = Config::default();
            let fs = PassthroughFs::new(fs_cfg.clone()).unwrap();
            fs.import().unwrap();
            restored_vfs
                .restore_mount(Box::new(fs), &b_fs.path, &restored_state)
                .unwrap();
        }

        assert!(vfs == restored_vfs);

        // fake init
        vfs.init(FsOptions::ASYNC_READ).unwrap();
        assert!(vfs.initialized.load(Ordering::Acquire));

        // live upgrade
        let mut mem = vec![0; 4096];
        let version_map = VersionMap::new();
        vfs.live_upgrade_save()
            .serialize(&mut mem.as_mut_slice(), &version_map, 1)
            .unwrap();

        // restore the state
        let restored_vfs = &Vfs::default();
        let restored_state = VfsState::deserialize(&mut mem.as_slice(), &version_map, 1).unwrap();
        <&Vfs>::live_upgrade_restore(&restored_vfs, &restored_state).unwrap();
        assert!(restored_vfs.initialized.load(Ordering::Acquire));

        for b_fs in restored_state.backend_fs.iter() {
            if b_fs.unmounted {
                continue;
            }
            let fs_cfg = Config::default();
            let fs = PassthroughFs::new(fs_cfg.clone()).unwrap();
            fs.import().unwrap();
            restored_vfs
                .restore_mount(Box::new(fs), &b_fs.path, &restored_state)
                .unwrap();
        }

        assert!(vfs == restored_vfs);
    }
}
