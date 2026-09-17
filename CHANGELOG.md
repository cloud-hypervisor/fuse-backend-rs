# Changelog
## [Unreleased]
### Added
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Split the library into a layered Cargo workspace and break the layers out into
  their own crates — `fuse-backend-core` (ABI, API/server, buffers),
  `fuse-backend-fusedev` and `fuse-backend-virtiofs` (transports), and
  `fuse-backend-passthrough` and `fuse-backend-overlayfs` (filesystem drivers) —
  so they can be depended on directly instead of only through the umbrella crate.
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Add standalone `passthrough` and `overlayfs` cargo features that select a
  filesystem driver on its own, without any transport.
- [252](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/252): Extract the `Vfs` union multiplexer (with its `pseudo_fs` backing store) into
  a seventh crate, `fuse-backend-vfs`, resolving RFC open question 3. It sits
  between the facade and `fuse-backend-core` and carries the `arc-swap` and
  `persist` (`versionize`/`dbs-snapshot`) stack that the multiplexer needs.
- [188](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/188): docs: document the experimental status of async-io support.

### Changed
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): `fuse-backend-rs` is now a thin facade re-exporting the sub-crates. Every
  historical `fuse_backend_rs::{abi, api, buffer, common, transport, passthrough,
  overlayfs}` import path and cargo feature name (`fusedev`, `virtiofs`,
  `vhost-user-fs`, `async-io`, `persist`, `fuse-t`, `fusedev-uring`) still
  resolves to the same types, so existing dependency lines are unchanged.
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Small breaking surface from the layering fix (a 0.x release may break API):
  `transport::Writer` is a trait now instead of an enum, so code naming its
  variants must adapt; the transport-specific `Reader` constructors
  (`from_fuse_buffer`, `from_descriptor_chain`) moved onto the `FuseDevReaderExt`
  and `VirtioFsReaderExt` extension traits and need that trait in scope (the
  `Reader::from_…` spelling is otherwise unchanged); and on `transport::Error`
  the never-constructed `ConvertIndirectDescriptor` variant was removed, while
  `FindMemoryRegion` and `InvalidChain` are now gated behind the `virtiofs`
  feature. Those variants stay on the same `transport::Error` type (there is no
  separate virtiofs error type), so a `virtiofs` build matching them is
  unaffected.
- [252](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/252): Replace the `lazy_static` dependency with `std::sync::LazyLock` and declare
  an explicit MSRV of Rust 1.80 (`rust-version = "1.80"`) on every published
  crate. No API change; this drops one dependency and formalizes the minimum
  toolchain, which was previously undeclared (CI builds on `stable`).
- [252](https://github.com/cloud-hypervisor/fuse-backend-rs/issues/252): `Vfs`, `arc-swap` and the `persist` snapshot stack
  (`versionize`/`dbs-snapshot`) move out of `fuse-backend-core` into
  `fuse-backend-vfs`, so a consumer that brings its own `FileSystem` and does
  not need the multiplexer can depend on `fuse-backend-core` directly and skip
  `arc-swap` entirely (`cargo tree -p fuse-backend-core --all-features` shows no
  `arc-swap` or `dbs-snapshot`). The umbrella crate depends on
  `fuse-backend-vfs` unconditionally and still re-exports the historical
  `api::vfs::*` and flat `api::Vfs` paths under every feature combination
  (guarded by `tests/legacy_paths.rs`), so existing imports and the
  `persist`/`async-io` feature names are unchanged, and snapshots stay
  byte-compatible.

### Removed
- [254](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/254): Drop the vestigial `vhost` and `virtio-bindings` dependencies that the
  pre-split `vhost-user-fs` build carried but never referenced; `vhost-user-fs`
  is now an alias for the `virtiofs` build.

## [0.14.0]
### Added
- [261](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/216): feat(fusedev): add try_with_writer on FuseSession

### Fixed

### Removed
- [222](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/222): Drop virtiofs DAX support as it never made it to the spec

## [0.13.0]
### Added
- [187](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/187): Feat/support fuse resend notify
- [211](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/211): Add notify_inval_inode and extend get_rootfs to return fs_idx for umount

### Fixed
- [189](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/189): fix by_id not free when use_host_ino=true
- [191](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/191): fix request size too large when use direct io
- [205](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/205): Fix: unable to perform sync on directory
- [212](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/212): Fix fuse out header len in notify_resend

## [0.12.0]
### Added
- [156](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/156): Fuse OverlayFs implementation.
- [166](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/166): Import latest improvement for passthroughfs from virtiofsd project.
- [169](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/169): Optimize implementation of lookup() for passthroughfs.
- [170](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/170): abi: unify st_nlink.
- [172](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/172): ptfs: refine implementation of seal_size_check().
- [173](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/173): ptfs: use BorrowedFd instead of RawFd when possible.
- [174](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/174): ptfs: add support for new cache mode Metadata.
- [177](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/177): fusedev: add clone_fuse_file method to FuseSession.

### Fixed
- [125](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/125): fusedev: add fd-passthrough support.
- [178](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/178): Fix batch forget can't handle too large msg.
- [180](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/180): fix: fuse-t nobrowse.
- [181](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/181): Fix CI: xfstests: restrict xfstests version.
- [184](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/184): bugfix: read/write fd dropped unexpectedly.
- [185](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/185): fix: fuse t channel read bug in during multiple reads

## [0.11.0]
### Added
- [144](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/144): feat: implement fuse-t feature
- [149](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/149): feat: add "persist" feature
- [152](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/152): Add the ability to clean up the dentry cache can be used to clean up resources when VFS umount.
- [153](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/153): linux_session: Make allow_other mount option optional
- [159](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/159): UID/GID remapping support
- [162](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/162): abi: Disable unsupported flags and functionality on MacOS
- [163](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/163): vfs: add method to export root pseudofs's reference
- [167](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/167): CI: add xfstests for passthrough fs

### Fixed
- [154](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/154): fuse: Ensure fd has same flags as read/write
- [165](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/165): build: fix a build failure related to conditional compilation

## [0.10.5]
### Added
- [138](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/138): linuxsession: support mount in given mount namespace
- [141](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/141): linux_session: support set fusermount binary

### Fixed
- [140](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/140): fuse: Ensure readdir returns same ino as lookup

## [0.10.4]

### Added
- [135](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/135): ZeroCopyWriter pass through available bytes from inner writer

### Fixed
- [133](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/133): https://github.com/cloud-hypervisor/fuse-backend-rs/pull/133

## [0.10.3]

### Added
- [#115](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/115)
  * transport: pre-allocate VecDeque to avoid expending at runtime
  * passthroughfs: convert MultiKeyBTreeMap to InodeStore for InodeMap
  * passthroughfs: add config to specify entry and attr timeout for dir
  * passthroughfs: add config to control count mntid in altkey or not
- [#119](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/119): Support non-privileged users
- [#126 #127](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/126 https://github.com/cloud-hypervisor/fuse-backend-rs/pull/127): vfs: ensure entry attr st_ino consistency
- [#131](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/131): implement stable unique inode for passthroughfs

### Fixed
- [#120](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/120): api: forget and batch forget must not reply
- [#123](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/123): fix possible IO hang due to string convertion failure
- [#129](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/129): abi: st_nlink is u32 on aarch64

## [0.10.2]

### Fixed
- [#105](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/105): abi: fix the conflict of PERFILE_DAX flag
- [#106](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/106): bugfix: passthrough: refect CFileHandle struct

## [0.10.1]

### Fixed
- [#102](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/102): passthrough: reduce the memory footprint of file handle
- [#103](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/103): vfs: correctly set attr.st_ino for loopup()

## [0.10.0]

### Added
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): async_runtime: add probe of io_uring support
- [#88](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/88): add ability to disallow operations that could change file size

### Fixed
- [#98](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/98): vfs: fix incorrect st_ino in entry.attr
- [#93](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/93): fix BIG_WRITES doesn't work

### Removed
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): async_runtime: remove thread_local of Runtime
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): remove temporarily tokio-uring module

### Changed
- [#97](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/97): log: print some variables in hexadecimal
- [#96](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/96): async_runtime: improved async file implement
- [#95](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/95): open file with O_APPEND cleared when writeback is enabled
- [#90](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/90): open file for reading if writeback cache is enabled

### Upgraded
- virtio-queue from 0.4 to 0.6
- vhost from 0.4 to 0.5

## [0.9.6]
- Fix no_opendir option handling

## [0.9.5]

### Changed
- Update dependency
- Fix a bug in fusedev
- Add toio-uring/tokio based async io framework

## [0.9.2]

### Added

- [#77](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/77): Implement Sync for FileVolatileSlice

## [0.9.1]

### Fixed
- [#74](https://github.com/cloud-hypervisor/fuse-backend-rs/pull/74): Fixed some issues about EINTR and EAGIN handled incorrectly

## [v0.4.0]
### Added
- MacOS support

### Changed
- linux_abi renamed to fuse_abi
- switch from epoll to mio for cross-platform support
- VFS umount no longer evicts pseudofs inodes
- virtiofs transport Reader/Writer takes generic typed memory argument

## [v0.3.0]
### Added
- Optionally enable MAX_PAGES feature
- Allow customizing the default FUSE features before creating a new vfs structure
- Support more FUSE server APIs

### Changed
- The FUSE server has no default FUSE feature set now. The default feature set is only
  defined in VfsOptions. Non VFS users have to define the default FUSE feature set in
  the init() method.

## [v0.2.0]
### Added
- Enhance passthrough to reduce active fds by using file handle
- implement From<fusedev::Error> for std::io::Error
- Use `vhost` crate from crates.io
- Introduce readlinkat_proc_file helper
- Update vm-memory to 0.7.0
- Add @eryugey to CODEOWNERS file

### Fixed
- Validate path components
- Prevent ".." escape in do_lookup in passthroughfs
- Prevent opening of special file in passthroughfs
- Fix compile error in vfs async test
- Record real root inode's ino of file system backends in vfs

### Deprecated 

## [v0.1.2]
- support KILLPRIV_v2
- enhance vfs to support DAX window map/unmap operations

## [v0.1.1]
- Set README.md file for crate
- Add CHANGELOG.md
