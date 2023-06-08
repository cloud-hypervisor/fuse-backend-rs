# Changelog
## [Unreleased]

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
