// Copyright 2020 Alibaba Cloud. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

#![allow(missing_docs)]

use std::convert::TryInto;
use std::io;
use std::io::Error as IoError;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, RwLock};
use std::time::Duration;

use std::fs::File;
use std::os::unix::io::RawFd;

use snapshot::{FilePersist, Persist};
use versionize::{VersionMap, Versionize, VersionizeResult};
use versionize_derive::Versionize;

use crate::abi::linux_abi as fuse;
use crate::passthrough::fs::{stat, Handle, HandleData, Inode, InodeAltKey, InodeData};
use crate::passthrough::{CachePolicy, Config, PassthroughFs};

#[derive(Versionize, PartialEq, Debug)]
pub struct ConfigState {
    // record nanosec
    entry_timeout: u128,
    attr_timeout: u128,
    cache_policy: CachePolicy,
    writeback: bool,
    root_dir: String,
    xattr: bool,
    do_import: bool,
    no_open: bool,
}

impl Persist<'_> for Config {
    type State = ConfigState;
    type ConstructorArgs = ();
    type LiveUpgradeConstructorArgs = ();
    type Error = IoError;

    fn save(&self) -> Self::State {
        ConfigState {
            entry_timeout: self.entry_timeout.as_nanos(),
            attr_timeout: self.attr_timeout.as_nanos(),
            cache_policy: self.cache_policy.clone(),
            writeback: self.writeback,
            root_dir: self.root_dir.clone(),
            xattr: self.xattr,
            do_import: self.do_import,
            no_open: self.no_open,
        }
    }

    fn restore(
        _constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        Ok(Config {
            entry_timeout: Duration::from_nanos(state.entry_timeout.try_into().unwrap()),
            attr_timeout: Duration::from_nanos(state.attr_timeout.try_into().unwrap()),
            cache_policy: state.cache_policy.clone(),
            writeback: state.writeback,
            root_dir: state.root_dir.clone(),
            xattr: state.xattr,
            do_import: state.do_import,
            no_open: state.no_open,
        })
    }

    fn live_upgrade_save(&self) -> Self::State {
        self.save()
    }

    fn live_upgrade_restore(
        constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        Self::restore(constructor_args, state)
    }
}

#[derive(Versionize, Debug, PartialEq)]
struct InodeDataState {
    inode: Inode,
    fd: RawFd,
    refcount: u64,
}

#[derive(Versionize, Debug, PartialEq)]
struct HandleDataState {
    handle: Handle,
    inode: Inode,
    fd: RawFd,
}

#[derive(Versionize, Debug, PartialEq)]
pub struct PassthroughFsLiveUpgradeState {
    proc: RawFd,
    next_inode: u64,
    inodes: Vec<InodeDataState>,
    next_handle: u64,
    handles: Vec<HandleDataState>,
}

#[derive(Versionize, Debug, PartialEq)]
pub struct PassthroughFsState {
    writeback: bool,
    no_open: bool,
    cfg: ConfigState,

    live_upgrade_state: Option<PassthroughFsLiveUpgradeState>,
}

impl Persist<'_> for PassthroughFs {
    type State = PassthroughFsState;
    type ConstructorArgs = ();
    type LiveUpgradeConstructorArgs = ();
    type Error = IoError;

    fn save(&self) -> Self::State {
        PassthroughFsState {
            writeback: self.writeback.load(Ordering::Relaxed),
            no_open: self.no_open.load(Ordering::Relaxed),
            cfg: self.cfg.save(),
            live_upgrade_state: None,
        }
    }
    fn restore(
        _constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        let cfg = Config::restore((), &state.cfg).unwrap();
        let fs = PassthroughFs::new(cfg)?;
        fs.no_open.store(state.no_open, Ordering::Relaxed);
        fs.writeback.store(state.writeback, Ordering::Relaxed);
        Ok(fs)
    }

    fn live_upgrade_save(&self) -> Self::State {
        let mut inodes = Vec::new();
        for (key, val) in self
            .inodes
            .read()
            .unwrap()
            .iter()
            .filter(|(&key, _)| key != fuse::ROOT_ID)
        {
            inodes.push(InodeDataState {
                inode: *key,
                fd: val.1.file.save(),
                refcount: val.1.refcount.load(Ordering::Relaxed),
            });
        }

        let mut handles = Vec::new();
        for (key, val) in self.handles.read().unwrap().iter() {
            handles.push(HandleDataState {
                handle: *key,
                inode: val.inode,
                fd: val.file.read().unwrap().save(),
            });
        }

        PassthroughFsState {
            writeback: self.writeback.load(Ordering::Relaxed),
            no_open: self.no_open.load(Ordering::Relaxed),
            cfg: self.cfg.save(),
            live_upgrade_state: Some(PassthroughFsLiveUpgradeState {
                proc: self.proc.save(),
                next_inode: self.next_inode.load(Ordering::Relaxed),
                inodes: inodes,
                next_handle: self.next_handle.load(Ordering::Relaxed),
                handles: handles,
            }),
        }
    }

    fn live_upgrade_restore(
        constructor_args: Self::ConstructorArgs,
        state: &Self::State,
    ) -> Result<Self, Self::Error> {
        if state.live_upgrade_state.is_none() {
            error!("Fs::live_upgrade_restore: no PassthroughFsLiveUpgradeState found in state");
            return Err(IoError::new(
                io::ErrorKind::InvalidInput,
                "no PassthroughFsLiveUpgradeState found in PassthroughFsState.",
            ));
        }

        let mut fs = Self::restore(constructor_args, state)?;

        // Safe to unwrap as we just checked it above.
        let live_state = state.live_upgrade_state.as_ref().unwrap();
        fs.proc = File::restore(live_state.proc);
        fs.next_inode
            .store(live_state.next_inode, Ordering::Relaxed);
        for elem in live_state.inodes.iter() {
            let file = File::restore(elem.fd);
            let st = stat(&file)?;
            fs.inodes.write().unwrap().insert(
                elem.inode,
                InodeAltKey {
                    ino: st.st_ino,
                    dev: st.st_dev,
                },
                Arc::new(InodeData {
                    inode: elem.inode,
                    file,
                    refcount: AtomicU64::new(elem.refcount),
                }),
            );
        }

        fs.next_handle
            .store(live_state.next_handle, Ordering::Relaxed);
        for elem in live_state.handles.iter() {
            fs.handles.write().unwrap().insert(
                elem.handle,
                Arc::new(HandleData {
                    inode: elem.inode,
                    file: RwLock::new(File::restore(elem.fd)),
                }),
            );
        }

        Ok(fs)
    }
}

impl PartialEq for PassthroughFs {
    fn eq(&self, other: &PassthroughFs) -> bool {
        // TODO: compare more fields
        self.no_open.load(Ordering::Relaxed) == other.no_open.load(Ordering::Relaxed)
            && self.writeback.load(Ordering::Relaxed) == other.writeback.load(Ordering::Relaxed)
            && self.cfg == other.cfg
    }
}

#[cfg(test)]
pub(crate) mod tests {
    use super::*;
    use std::os::unix::io::AsRawFd;

    #[test]
    fn test_persist_passthroughfs_state() {
        let fs_cfg = Config {
            writeback: true,
            do_import: false,
            no_open: true,
            ..Default::default()
        };
        let fs = PassthroughFs::new(fs_cfg).unwrap();
        fs.import().unwrap();

        // save the state
        let mut mem = vec![0; 4096];
        let version_map = VersionMap::new();
        fs.save()
            .serialize(&mut mem.as_mut_slice(), &version_map, 1)
            .unwrap();

        // restore the state
        let restored_fs = PassthroughFs::restore(
            (),
            &PassthroughFsState::deserialize(&mut mem.as_slice(), &version_map, 1).unwrap(),
        )
        .unwrap();

        assert_eq!(restored_fs.writeback.load(Ordering::Relaxed), true);
        assert_eq!(restored_fs.no_open.load(Ordering::Relaxed), true);
        println!("fs.proc {:?} {:?}", fs.proc, restored_fs.proc);
        assert!(fs == restored_fs);
    }

    #[test]
    fn test_persist_passthroughfs_state_live_upgrade() {
        let fs_cfg = Config {
            writeback: true,
            do_import: false,
            no_open: true,
            ..Default::default()
        };
        let fs = PassthroughFs::new(fs_cfg).unwrap();
        fs.import().unwrap();
        // TODO: insert a few lookup()s to fs.

        // save the state
        let mut mem = vec![0; 4096];
        let version_map = VersionMap::new();
        fs.live_upgrade_save()
            .serialize(&mut mem.as_mut_slice(), &version_map, 1)
            .unwrap();

        // restore the state
        let restored_fs = PassthroughFs::live_upgrade_restore(
            (),
            &PassthroughFsState::deserialize(&mut mem.as_slice(), &version_map, 1).unwrap(),
        )
        .unwrap();

        assert!(fs == restored_fs);

        assert_eq!(fs.proc.as_raw_fd(), restored_fs.proc.as_raw_fd());
        assert_eq!(
            fs.next_inode.load(Ordering::Relaxed),
            restored_fs.next_inode.load(Ordering::Relaxed)
        );

        // let fs_inodes = fs.inodes.read().unwrap();
        // let fs_root_inode = fs_inodes.get(&fuse::ROOT_ID).unwrap();

        // let restored_inodes = restored_fs.inodes.read().unwrap();
        // let root_inode = restored_inodes.get(&fuse::ROOT_ID);
        // assert_eq!(root_inode.is_some(), true);

        // let root_inode = root_inode.unwrap();
        // assert_eq!(root_inode.file.as_raw_fd(), fs_root_inode.file.as_raw_fd());
    }
}
