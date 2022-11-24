#![allow(missing_docs)]

use std::sync::{Arc, Weak};
use std::io::{Result, Error};
use std::os::unix::io::RawFd;
use std::fs::File;
use std::path::PathBuf;
use std::cmp::Eq;
use libc;


use self::super::super::abi::fuse_abi::Dirent;
use self::super::datasource::DataSource;
use self::super::OverlayFs;
use self::super::{WHITEOUT_PREFIX, ORIGIN_XATTR, OPAQUE_XATTR, PRIVILEGED_OPAQUE_XATTR, PRIVILEGED_ORIGIN_XATTR, UNPRIVILEGED_OPAQUE_XATTR, OPAQUE_WHITEOUT};

pub const OPAQUE_XATTR_LEN: usize = 16;

// we cannot constraint Layer with Eq, as Eq requires Sized
// So we need api to get an identifier and then use identifier
// to do comparation.. Here may have better solutions..
pub trait Layer {
	fn init(&mut self) -> Result<()>;
	fn cleanup(&mut self) -> Result<()>;
	fn indentifier(&self) -> u64;
	fn is_me(&self, id: u64) -> bool;
	// file exists, returns true, not exists return false
	// otherwise, error out
	fn file_exists(&self, ppath: &str, ino: u64, name: &str) -> Result<bool>;
	fn whiteout_exists(&self, ppath: &str, ino: u64, name: &str) -> Result<bool> {
		let mut wh_name = String::from(WHITEOUT_PREFIX);
		wh_name.push_str(name);

		match self.file_exists(ppath, ino, wh_name.as_str()) {
			Ok(v) => {
				// has whiteout
				if v {
					return Ok(v);
				}

				// no .wh.<name> whiteout, fallback to device node whiteout
			},

			Err(e) => {
				if let Some(e1) = e.raw_os_error() {
					if e1 != libc::ENOENT && e1 != libc::ENOTDIR && e1 != libc::ENAMETOOLONG {
						return Err(e);
					}
					// as no .wh.<name> whiteout
				} else {
					return Err(e);
				}
			},
		}

		match self.stat64(ppath, ino, name) {
			Ok(st) => {
				let major = unsafe { libc::major(st.st_rdev) };
				let minor = unsafe { libc::minor(st.st_rdev) };

				if st.st_mode & libc::S_IFMT == libc::S_IFCHR && major == 0 && minor == 0 {
					return Ok(true);
				}

				return Ok(false);
			},
			Err(e) => {
				if let Some(e1) = e.raw_os_error() {
					if e1 == libc::ENOENT || e1 == libc::ENOTDIR || e1 == libc::ENAMETOOLONG {
						return Ok(false);
					}
				}

				return Err(e);
			},
		}
	}

	fn is_opaque_whiteout(&self, ppath: &str, parent: u64, name: &str, me: u64) -> Result<bool> {
		let st = self.stat64(ppath, parent, name)?;
		if st.st_mode & libc::S_IFMT != libc::S_IFDIR {
			return Err(Error::from_raw_os_error(libc::ENOTDIR));
		}
		// check xattr first
		match self.getxattr(ppath, parent, name, PRIVILEGED_OPAQUE_XATTR, OPAQUE_XATTR_LEN) {
			Ok(r) => {
				if r[0].to_ascii_lowercase() == b'y' {
					return Ok(true);
				} else {
					return Ok(false);
				}
			},

			Err(e) => {
				if let Some(e1) = e.raw_os_error() {
					if e1 != libc::ENODATA && e1 != libc::ENOTSUP {
						return Err(e);
					}
				} else {
					return Err(e);
				}
			},
		}

		match self.getxattr(ppath, parent, name, UNPRIVILEGED_OPAQUE_XATTR, OPAQUE_XATTR_LEN) {
			Ok(r) => {
				if r[0].to_ascii_lowercase() == b'y' {
					return Ok(true);
				} else {
					return Ok(false);
				}
			},

			Err(e) => {
				if let Some(e1) = e.raw_os_error() {
					if e1 != libc::ENODATA && e1 != libc::ENOTSUP {
						return Err(e);
					}
				} else {
					return Err(e);
				}
			},
		}

		match self.getxattr(ppath, parent, name, OPAQUE_XATTR, OPAQUE_XATTR_LEN) {
			Ok(r) => {
				if r[0].to_ascii_lowercase() == b'y' {
					return Ok(true);
				} else {
					return Ok(false);
				}
			},

			Err(e) => {
				if let Some(e1) = e.raw_os_error() {
					if e1 != libc::ENODATA && e1 != libc::ENOTSUP {
						return Err(e);
					}
				} else {
					return Err(e);
				}
			},
		}

		// check .wh..wh..opaque, hwoever, we have no parent inode number for the parent of .wh..wh..opaque
		let mut my_path = String::from(ppath);
		my_path.push_str("/");
		my_path.push_str(name);

		match self.file_exists(my_path.as_str(), me, OPAQUE_WHITEOUT) {
			Ok(v) => {
				return Ok(v);
			},

			Err(e) => {
				if let Some(e1) = e.raw_os_error() {
					if e1 == libc::ENOENT || e1 == libc::ENOTDIR {
						return Ok(false);
					}
				}
				return Err(e);
			},
		}
	}

	fn readdir(&self, path:String) -> Result<Vec<Dirent>>;
	fn stat64(&self, ppath: &str, ino: u64, name: &str) -> Result<libc::stat64>;
	fn fstat64(&self, fd: RawFd) -> Result<libc::stat64>;
	fn openat(&self, path: String, flags: i32, mode: libc::mode_t) -> Result<File>;
	fn readlinkat(&self, path: String) -> Result<PathBuf>;

	// read file content out for copy up, interface for
	// abstract files
	fn getxattr(&self, ppath: &str, ino: u64, file: &str, attr_name: &str, size: usize) -> Result<Vec<u8>>;
	fn listxattr(&self, ppath: &str, ino: u64, file: &str, size: usize) -> Result<Vec<u8>>;
	fn read(&self, fd: RawFd, len: libc::size_t) -> Result<Vec<u8>>;
	fn write(&self, fd: RawFd, buf: &[u8]) -> Result<libc::size_t>;

	fn update_data(&self, ppath: &str, parent: u64, child: &str, child_ino: u64);
}
