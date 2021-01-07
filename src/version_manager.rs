// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0
#![allow(missing_docs)]

use versionize::VersionManager;

use crate::api::vfs::persist::get_versions_vfs;
use crate::passthrough::get_versions_passthrough_fs;

pub fn get_version_manager() -> VersionManager {
    let mut version_manager = VersionManager::new();
    version_manager
        .add_version("0.0.0")
        .add_version("0.0.1")
        .add_version("0.0.2")
        .add_version("latest");
    version_manager
        .add_version_provider(get_versions_passthrough_fs)
        .add_version_provider(get_versions_vfs);
    version_manager
}
