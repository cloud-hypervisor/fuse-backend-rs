// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0

//! Trait for virtio-fs cache requests operations.

use std::io;
use std::os::unix::io::RawFd;

use vhost_rs::vhost_user::message::{
    VhostUserFSSlaveMsg, VhostUserFSSlaveMsgFlags, VHOST_USER_FS_SLAVE_ENTRIES,
};
use vhost_rs::vhost_user::{SlaveFsCacheReq, VhostUserMasterReqHandler};

use crate::abi::virtio_fs::{RemovemappingOne, SetupmappingFlags};

/// Trait for virtio-fs cache requests operations.
///
/// This is mainly used to hide vhost-user details from virtio-fs's fuse part.
pub trait FsCacheReqHandler: Send + Sync + 'static {
    /// Setup a dedicated mapping so that guest can access file data in DAX style.
    fn map(
        &mut self,
        foffset: u64,
        moffset: u64,
        len: u64,
        flags: u64,
        fd: RawFd,
    ) -> io::Result<()>;

    /// Remove those mappings that provide the access to file data.
    fn unmap(&mut self, requests: Vec<RemovemappingOne>) -> io::Result<()>;
}

impl FsCacheReqHandler for SlaveFsCacheReq {
    fn map(
        &mut self,
        foffset: u64,
        moffset: u64,
        len: u64,
        flags: u64,
        fd: RawFd,
    ) -> io::Result<()> {
        let mut msg: VhostUserFSSlaveMsg = Default::default();
        msg.fd_offset[0] = foffset;
        msg.cache_offset[0] = moffset;
        msg.len[0] = len;
        msg.flags[0] = if (flags & SetupmappingFlags::WRITE.bits()) != 0 {
            VhostUserFSSlaveMsgFlags::MAP_W | VhostUserFSSlaveMsgFlags::MAP_R
        } else {
            VhostUserFSSlaveMsgFlags::MAP_R
        };

        self.fs_slave_map(&msg, fd)?;

        Ok(())
    }

    fn unmap(&mut self, requests: Vec<RemovemappingOne>) -> io::Result<()> {
        for chunk in requests.chunks(VHOST_USER_FS_SLAVE_ENTRIES) {
            let mut msg: VhostUserFSSlaveMsg = Default::default();

            for (ind, req) in chunk.iter().enumerate() {
                msg.len[ind] = req.len;
                msg.cache_offset[ind] = req.moffset;
            }

            self.fs_slave_unmap(&msg)?;
        }

        Ok(())
    }
}
