// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use super::PassthroughFs;
use fuse_backend_core::abi::fuse_abi;
use fuse_backend_core::api::filesystem::Layer;

// Implment Layer trait for PassthroughFs.
impl Layer for PassthroughFs {
    // Return root inode of this layer.
    fn root_inode(&self) -> Self::Inode {
        fuse_abi::ROOT_ID
    }
}
