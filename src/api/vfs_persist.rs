// Copyright 2020 Alibaba Cloud. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![allow(missing_docs)]

use std::io::Error as IoError;
use std::ops::Deref;
use std::sync::atomic::Ordering;
use std::sync::Arc;

use snapshot::Persist;
use versionize::{VersionMap, Versionize, VersionizeError, VersionizeResult};
use versionize_derive::Versionize;

use crate::api::vfs::BackFileSystem;
use crate::api::{BackendFileSystemType, Vfs, VfsOptions};
use crate::api::filesystem::FsOptions;
use crate::passthrough::{PassthroughFs, PassthroughFsState};

#[derive(Versionize, PartialEq, Debug)]
pub enum BackendFsStateInner {
    PassthroughFs(PassthroughFsState),
    // Place holder, not implemented yet
    Rafs,
}

#[derive(Versionize, PartialEq, Debug)]
pub struct BackendFsState {
    super_index: u8,
    fs_state: Option<BackendFsStateInner>,
    path: String,
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

#[derive(Versionize, PartialEq, Debug)]
pub struct VfsState {
    opts: VfsOptionsState,
    next_super: u8,
    backend_fs: Vec<BackendFsState>,
}

impl Persist<'_> for Vfs {
    type State = VfsState;
    type ConstructorArgs = ();
    type LiveUpgradeConstructorArgs = ();
    type Error = IoError;

    fn save(&self) -> Self::State {
        self.persist_save_common(|fs: Arc<BackFileSystem>| match fs.fstype() {
            BackendFileSystemType::PassthroughFs => BackendFsStateInner::PassthroughFs(
                fs.deref()
                    .as_any()
                    .downcast_ref::<PassthroughFs>()
                    .unwrap()
                    .save(),
            ),
            _ => unimplemented!(),
        })
    }

    fn restore(
        _constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        Self::persist_restore_common(state, |fs_state| match fs_state {
            BackendFsStateInner::PassthroughFs(passthrough_fs_state) => {
                let passthrough_fs = PassthroughFs::restore((), &passthrough_fs_state)?;
                passthrough_fs.import()?;
                Ok(Box::new(passthrough_fs))
            }
            _ => unimplemented!(),
        })
    }

    fn live_upgrade_save(&self) -> Self::State {
        self.persist_save_common(|fs: Arc<BackFileSystem>| match fs.fstype() {
            BackendFileSystemType::PassthroughFs => BackendFsStateInner::PassthroughFs(
                fs.deref()
                    .as_any()
                    .downcast_ref::<PassthroughFs>()
                    .unwrap()
                    .live_upgrade_save(),
            ),
            _ => unimplemented!(),
        })
    }
    fn live_upgrade_restore(
        _constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        Self::persist_restore_common(state, |fs_state| match fs_state {
            BackendFsStateInner::PassthroughFs(passthrough_fs_state) => {
                let passthrough_fs =
                    PassthroughFs::live_upgrade_restore((), &passthrough_fs_state)?;
                passthrough_fs.import()?;
                Ok(Box::new(passthrough_fs))
            }
            _ => unimplemented!(),
        })
    }
}

impl Vfs {
    fn persist_save_common<F>(&self, save_fn: F) -> VfsState
    where
        F: FnOnce(Arc<BackFileSystem>) -> BackendFsStateInner + Copy,
    {
        let mut backend_fs_vec = Vec::new();

        for (index, path) in self.unmounted_path.lock().unwrap().iter() {
            backend_fs_vec.push(BackendFsState {
                super_index: *index,
                fs_state: None,
                path: path.to_string(),
            });
        }

        for (_, val) in self.mountpoints.load().iter() {
            let super_index = val.super_index;
            let fs = self
                .superblocks
                .load()
                .get(&super_index)
                .map(Arc::clone)
                .unwrap();

            backend_fs_vec.push(BackendFsState {
                super_index: super_index,
                fs_state: Some(save_fn(fs)),
                path: val.path.clone(),
            });
        }
        // store backend fs by 'super_index' order
        backend_fs_vec.sort_by(|a, b| a.super_index.cmp(&b.super_index));

        VfsState {
            opts: self.opts.load().deref().deref().save(),
            next_super: self.next_super.load(Ordering::SeqCst),
            backend_fs: backend_fs_vec,
        }
    }

    fn persist_restore_common<F>(
        state: &VfsState,
        restore_fn: F,
    ) -> std::result::Result<Self, IoError>
    where
        F: FnOnce(&BackendFsStateInner) -> std::result::Result<BackFileSystem, IoError> + Copy,
    {
        let vfs = Vfs::default();
        vfs.opts.store(Arc::new(VfsOptions::restore((), &state.opts).unwrap()));

        for fs in state.backend_fs.iter() {
            if let Some(fs_state) = fs.fs_state.as_ref() {
                let b_fs: BackFileSystem = restore_fn(&fs_state)?;
                vfs.mount(b_fs, fs.path.as_str())?;
            } else {
                vfs.mkdir_all(fs.super_index, &fs.path)?;
            }
        }

        vfs.next_super.store(state.next_super, Ordering::SeqCst);
        Ok(vfs)
    }
}

impl PartialEq for VfsOptions {
    fn eq(&self, other: &VfsOptions) -> bool {
        self.no_open == other.no_open
            && self.no_opendir == other.no_opendir
            && self.no_writeback == other.no_writeback
            && self.in_opts == self.in_opts
            && self.out_opts == self.out_opts
    }
}

impl PartialEq for Vfs {
    fn eq(&self, other: &Vfs) -> bool {
        let old_unmounted = self.unmounted_path.lock().unwrap().clone();
        let new_unmounted = other.unmounted_path.lock().unwrap().clone();
        let mut old_root_inodes: Vec<u64> =
            self.mountpoints.load().iter().map(|(&k, _)| k).collect();
        let mut new_root_inodes: Vec<u64> =
            other.mountpoints.load().iter().map(|(&k, _)| k).collect();
        let mut old_super_indexes: Vec<u8> =
            self.superblocks.load().iter().map(|(&k, _)| k).collect();
        let mut new_super_indexes: Vec<u8> =
            self.superblocks.load().iter().map(|(&k, _)| k).collect();

        old_root_inodes.sort();
        new_root_inodes.sort();
        old_super_indexes.sort();
        new_super_indexes.sort();

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
    use crate::passthrough::{Config, PassthroughFs};

    #[test]
    fn test_persist_vfs() {
        let opts = VfsOptions {
            no_open: false,
            no_writeback: true,
            ..Default::default()
        };

        let vfs = Vfs::new(opts);

        let mount_fs = |path| {
            let fs_cfg = Config::default();
            let fs = PassthroughFs::new(fs_cfg.clone()).unwrap();
            fs.import().unwrap();
            vfs.mount(Box::new(fs), path).unwrap();
        };

        mount_fs("/submnt/mnt_a");
        mount_fs("/submnt/mnt_a");
        mount_fs("/submnt/mnt_a");
        vfs.umount("/submnt/mnt_a").unwrap();
        mount_fs("/submnt/mnt_a");
        mount_fs("/submnt/mnt_a");
        mount_fs("/submnt/mnt_b");
        mount_fs("/submnt/mnt_c");
        vfs.umount("/submnt/mnt_b").unwrap();
        mount_fs("/submnt/mnt_d");
        mount_fs("/submnt/mnt_b/c/d/e");
        vfs.umount("/submnt/mnt_d").unwrap();
        mount_fs("/submnt/mnt_e");
        mount_fs("/submnt/mnt_f");
        vfs.umount("/submnt/mnt_e").unwrap();
        mount_fs("/submnt/mnt_d");

        // snapshot
        // save the state
        let mut mem = vec![0; 4096];
        let version_map = VersionMap::new();
        vfs.save()
            .serialize(&mut mem.as_mut_slice(), &version_map, 1)
            .unwrap();

        // restore the state
        let restored_vfs = Vfs::restore(
            (),
            &VfsState::deserialize(&mut mem.as_slice(), &version_map, 1).unwrap(),
        )
        .unwrap();

        assert!(vfs == restored_vfs);

        // live upgrade
        let mut mem = vec![0; 4096];
        let version_map = VersionMap::new();
        vfs.live_upgrade_save()
            .serialize(&mut mem.as_mut_slice(), &version_map, 1)
            .unwrap();

        // restore the state
        let restored_vfs = Vfs::live_upgrade_restore(
            (),
            &VfsState::deserialize(&mut mem.as_slice(), &version_map, 1).unwrap(),
        )
        .unwrap();

        assert!(vfs == restored_vfs);
    }
}
