# Changelog
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
