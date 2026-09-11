// Copyright (C) 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! Compile-time guards for the historical public API surface.
//!
//! The crate split (fuse-backend-core/-fusedev/-virtiofs/-passthrough/
//! -overlayfs) must be invisible to downstream users: every import path that
//! resolved against the monolithic `fuse-backend-rs` has to keep resolving
//! through the facade. Each module below imports the paths that a given
//! feature combination historically exposed, and the cfg gates mirror the
//! gates the in-crate modules used before the split. If a re-export is ever
//! dropped or re-gated, the corresponding build of this file stops compiling.
#![allow(unused_imports)]

/// Flat re-exports at the crate root, from the transport-neutral layers.
mod root_paths {
    use fuse_backend_rs::file_buf;
    use fuse_backend_rs::file_traits;
    use fuse_backend_rs::{bytes_to_cstr, common, encode_io_error_kind, Error, Result};

    #[test]
    fn root_paths_resolve() {
        assert!(bytes_to_cstr(b"legacy\0").is_ok());
        assert_eq!(
            encode_io_error_kind(std::io::ErrorKind::NotFound),
            libc::ENOENT
        );
    }
}

/// Module paths of the transport-neutral layers, from `fuse-backend-core`.
mod core_paths {
    use fuse_backend_rs::abi::fuse_abi::{Attr, Opcode};
    use fuse_backend_rs::api::filesystem::{
        Context, DirEntry, Entry, FileSystem, FsOptions, OpenOptions, SetattrValid, ZeroCopyReader,
        ZeroCopyWriter, ROOT_ID,
    };
    use fuse_backend_rs::api::server::{MetricsHook, Server, ServerVersion};
    use fuse_backend_rs::api::vfs::{
        validate_path_component, BackendFileSystem, Vfs, VfsIndex, VfsOptions, VFS_MAX_INO,
    };
    use fuse_backend_rs::buffer::{pagesize, Error, IoBuffers, Reader, Result, Writer};
    use fuse_backend_rs::common::file_buf::FileVolatileSlice;
    use fuse_backend_rs::common::file_traits::FileReadWriteVolatile;

    #[test]
    fn core_paths_resolve() {
        assert_eq!(pagesize(), fuse_backend_rs::transport::pagesize());
        assert_eq!(Opcode::Lookup as u32, 1);
        assert_eq!(ROOT_ID, 1);
        assert_eq!(VFS_MAX_INO, 0xff_ffff_ffff_ffff);

        // The flat `api::Vfs` re-export names the same type as `api::vfs::Vfs`.
        let _vfs: fuse_backend_rs::api::Vfs = Vfs::new(VfsOptions::default());
    }
}

/// Buffer and cache-handler re-exports under the historical `transport::`
/// module, which the transports used to live next to.
mod transport_paths {
    use fuse_backend_rs::transport::{pagesize, Error, FsCacheReqHandler, Reader, Result, Writer};

    #[test]
    fn transport_paths_resolve() {
        assert_eq!(pagesize(), fuse_backend_rs::buffer::pagesize());
    }
}

/// The `/dev/fuse` transport surface, historical `feature = "fusedev"`.
#[cfg(feature = "fusedev")]
mod fusedev_paths {
    use fuse_backend_rs::transport::fusedev::{
        FuseBuf, FuseChannel, FuseChannelExt, FuseDevReaderExt, FuseDevWriter, FuseSession,
        FuseSessionExt,
    };
    // The flat `transport::X` aliases prove the flat re-exports resolve too.
    use fuse_backend_rs::transport::{
        FuseBuf as FlatFuseBuf, FuseChannel as FlatFuseChannel,
        FuseChannelExt as FlatFuseChannelExt, FuseDevReaderExt as FlatFuseDevReaderExt,
        FuseDevWriter as FlatFuseDevWriter, FuseSession as FlatFuseSession,
        FuseSessionExt as FlatFuseSessionExt,
    };

    #[test]
    fn fusedev_paths_resolve() {
        // And they name the very same items.
        fn same_type<T>(_: T, _: T) {}
        same_type(FuseBuf::new(&mut []), FlatFuseBuf::new(&mut []));
    }
}

/// Linux-only items of the fusedev transport.
#[cfg(all(target_os = "linux", feature = "fusedev"))]
mod fusedev_linux {
    use fuse_backend_rs::transport::fusedev::BlockingFuseChannel;
    use fuse_backend_rs::transport::BlockingFuseChannel as FlatBlockingFuseChannel;
}

/// The async serving task of the fusedev transport.
#[cfg(all(target_os = "linux", feature = "fusedev", feature = "async-io"))]
mod fusedev_async {
    use fuse_backend_rs::transport::fusedev::FuseDevTask;
    use fuse_backend_rs::transport::FuseDevTask as FlatFuseDevTask;
}

/// The FUSE-over-io_uring transport, historical `feature = "fusedev-uring"`.
#[cfg(all(target_os = "linux", feature = "fusedev-uring"))]
mod uring_paths {
    use fuse_backend_rs::transport::fusedev::{UringConfig, UringFuseServing, UringWriter};
    use fuse_backend_rs::transport::{
        UringConfig as FlatUringConfig, UringFuseServing as FlatUringFuseServing,
        UringWriter as FlatUringWriter,
    };

    #[test]
    fn uring_paths_resolve() {
        fn same_type<T>(_: T, _: T) {}
        same_type(UringConfig::default(), FlatUringConfig::default());
    }
}

/// The virtiofs transport surface, historical `feature = "virtiofs"`.
#[cfg(feature = "virtiofs")]
mod virtiofs_paths {
    use fuse_backend_rs::abi::virtio_fs::{RemovemappingIn, RemovemappingOne, SetupmappingIn};
    use fuse_backend_rs::transport::virtiofs::{VirtioFsReaderExt, VirtioFsWriter};
    use fuse_backend_rs::transport::{
        VirtioFsReaderExt as FlatVirtioFsReaderExt, VirtioFsWriter as FlatVirtioFsWriter,
    };
}

/// The passthrough driver, Linux-only as it has always been. Historically
/// bundled with the transports, now also selectable via its own feature.
#[cfg(all(
    target_os = "linux",
    any(feature = "fusedev", feature = "virtiofs", feature = "passthrough")
))]
mod passthrough_paths {
    use fuse_backend_rs::passthrough::{CachePolicy, Config, PassthroughFs};

    #[test]
    fn passthrough_paths_resolve() {
        let _cfg = Config::default();
        let _fs: Option<PassthroughFs<()>> = None;
    }
}

/// The overlayfs driver, Linux-only as it has always been. Historically
/// bundled with the transports, now also selectable via its own feature.
#[cfg(all(
    target_os = "linux",
    any(feature = "fusedev", feature = "virtiofs", feature = "overlayfs")
))]
mod overlayfs_paths {
    use fuse_backend_rs::api::filesystem::Layer;
    use fuse_backend_rs::overlayfs::config::Config;
    use fuse_backend_rs::overlayfs::{BoxedLayer, CachePolicy, Handle, Inode, OverlayFs};

    #[test]
    fn overlayfs_paths_resolve() {
        let _cfg = Config::default();
        let _fs: Option<OverlayFs> = None;
    }
}

/// The async IO surface, historical `feature = "async-io"` (Linux-only).
#[cfg(all(target_os = "linux", feature = "async-io"))]
mod async_paths {
    use fuse_backend_rs::api::filesystem::{
        AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter,
    };
    use fuse_backend_rs::async_file::File as AsyncFile;
    use fuse_backend_rs::async_runtime::Runtime;
    use fuse_backend_rs::file_traits::AsyncFileReadWriteVolatile;
    use fuse_backend_rs::{async_file, async_runtime, mpmc};
}

/// The VFS snapshot surface, historical `feature = "persist"`.
#[cfg(feature = "persist")]
mod persist_paths {
    use fuse_backend_rs::api::{Vfs, VfsOptions};

    #[test]
    fn vfs_save_restore_roundtrip() {
        // The `api::vfs::Vfs` path names the same type as the flat `api::Vfs`.
        let vfs: fuse_backend_rs::api::vfs::Vfs = Vfs::new(VfsOptions::default());
        let mut buf = vfs.save_to_bytes().unwrap();

        let restored = Vfs::new(VfsOptions::default());
        restored.restore_from_bytes(&mut buf).unwrap();
        assert_eq!(vfs.initialized(), restored.initialized());
    }
}
