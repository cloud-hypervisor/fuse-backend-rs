// Copyright (C) 2023 Ant Group. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use self::super::CachePolicy;
use std::fmt;
use std::time::Duration;

#[derive(Default, Clone, Debug)]
pub struct Config {
    pub mountpoint: String,
    pub work: String,
    pub do_import: bool,
    // Filesystem options.
    pub writeback: bool,
    pub no_open: bool,
    pub no_opendir: bool,
    pub killpriv_v2: bool,
    pub no_readdir: bool,
    pub perfile_dax: bool,
    pub cache_policy: CachePolicy,
    /// Whether shared mmaps of regular files are allowed under the `Never` cache policy, which
    /// opens them with `DIRECT_IO`. Without this option (the default) a standalone mount does
    /// not negotiate `FsOptions::DIRECT_IO_ALLOW_MMAP`, so the kernel fails such a mmap with
    /// `ENODEV`; opting in lets the kernel serve it from the client page cache, which it only
    /// invalidates on each new mmap and on its own direct writes. Behind a `Vfs` the flag is
    /// connection-wide and comes from `VfsOptions::out_opts` instead. The `Auto` and `Always`
    /// policies never open files with `DIRECT_IO`, so the option does nothing for them.
    pub allow_mmap: bool,
    pub attr_timeout: Duration,
    pub entry_timeout: Duration,
}

impl Clone for CachePolicy {
    fn clone(&self) -> Self {
        match *self {
            CachePolicy::Never => CachePolicy::Never,
            CachePolicy::Always => CachePolicy::Always,
            CachePolicy::Auto => CachePolicy::Auto,
        }
    }
}

impl fmt::Debug for CachePolicy {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let policy = match *self {
            CachePolicy::Never => "Never",
            CachePolicy::Always => "Always",
            CachePolicy::Auto => "Auto",
        };

        write!(f, "CachePolicy: {}", policy)
    }
}
