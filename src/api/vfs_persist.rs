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
use crate::passthrough::{Config, PassthroughFs, PassthroughFsState};

#[derive(Versionize, PartialEq, Debug)]
pub enum BackendFsStateInner {
    PassthroughFs(PassthroughFsState),
}

#[derive(Versionize, PartialEq, Debug)]
pub struct BackendFsState {
    super_index: u8,
    fs_state: BackendFsStateInner,
    path: String,
}

#[derive(Versionize, PartialEq, Debug)]
pub struct VfsState {
    opts: VfsOptions,
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
                fs_state: save_fn(fs),
                path: val.path.clone(),
            });
        }
        // store backend fs by 'super_index' order
        backend_fs_vec.sort_by(|a, b| a.super_index.cmp(&b.super_index));

        VfsState {
            opts: self.opts.load().deref().deref().clone(),
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
        vfs.opts.store(Arc::new(state.opts));

        for fs in state.backend_fs.iter() {
            let b_fs: BackFileSystem = restore_fn(&fs.fs_state)?;
            vfs.mount(b_fs, fs.path.as_str())?;
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
        self.next_super.load(Ordering::Relaxed) == other.next_super.load(Ordering::Relaxed)
            && self.opts.load().deref().deref() == other.opts.load().deref().deref()
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;

    #[test]
    fn test_persist_vfs_state() {
        let opts = VfsOptions {
            no_open: false,
            no_writeback: true,
            ..Default::default()
        };

        let vfs = Vfs::new(opts);

        // attach two fs
        let fs_cfg = Config::default();
        let fs_a = PassthroughFs::new(fs_cfg.clone()).unwrap();
        fs_a.import().unwrap();
        vfs.mount(Box::new(fs_a), "/submnt/mnt_a").unwrap();

        let fs_b = PassthroughFs::new(fs_cfg).unwrap();
        fs_b.import().unwrap();
        vfs.mount(Box::new(fs_b), "/submnt/mnt_b").unwrap();

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
    }

    #[test]
    fn test_persist_vfs_state_live_upgrade() {
        let opts = VfsOptions {
            no_open: false,
            no_writeback: true,
            ..Default::default()
        };

        let vfs = Vfs::new(opts);

        // attach two fs
        let fs_cfg = Config::default();
        let fs_a = PassthroughFs::new(fs_cfg.clone()).unwrap();
        fs_a.import().unwrap();
        vfs.mount(Box::new(fs_a), "/submnt/mnt_a").unwrap();

        let fs_b = PassthroughFs::new(fs_cfg).unwrap();
        fs_b.import().unwrap();
        vfs.mount(Box::new(fs_b), "/submnt/mnt_b").unwrap();

        // save the state
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
