#![allow(missing_docs)]

use std::sync::{Arc, Weak};
use std::io::{Result, Error};
use std::os::unix::io::RawFd;
use std::fs::File;
use std::path::PathBuf;
use std::cmp::Eq;
use std::ffi::{CString, CStr};
use libc;


use self::super::super::abi::fuse_abi::Dirent;
use self::super::datasource::DataSource;
use self::super::{OverlayFs, Inode, Handle};
use self::super::{WHITEOUT_PREFIX, ORIGIN_XATTR, OPAQUE_XATTR, PRIVILEGED_OPAQUE_XATTR, PRIVILEGED_ORIGIN_XATTR, UNPRIVILEGED_OPAQUE_XATTR, OPAQUE_WHITEOUT};
use crate::api::filesystem::{FileSystem, Context, Entry, GetxattrReply};
use crate::abi::fuse_abi::{CreateIn};
use crate::api::VFS_MAX_INO;

pub const OPAQUE_XATTR_LEN: u32 = 16;

// we cannot constraint Layer with Eq, as Eq requires Sized
// So we need api to get an identifier and then use identifier
// to do comparation.. Here may have better solutions..
pub trait Layer: FileSystem {
	fn init_layer(&mut self) -> Result<()>;
	fn cleanup(&mut self) -> Result<()>;
	fn is_upper(&self) -> bool;
	// file exists, returns true, not exists return false
	// otherwise, error out
	// Ok(None) denotes no entry
	fn lookup_ignore_enoent(&self, ctx: &Context, ino: u64, name: &str) -> Result<Option<Entry>> {
		let cname = CString::new(name).expect("invalid c string");
		match self.lookup(ctx, Self::Inode::from(ino), cname.as_c_str()) {
			Ok(v) => return Ok(Some(v)),
			Err(e) => {
				if let Some(raw_error) = e.raw_os_error() {
					if raw_error == libc::ENOENT || raw_error == libc::ENAMETOOLONG {
						return Ok(None);
					}
				}

				return Err(e);
			},
		}
	}

	fn getxattr_ignore_nodata(&self, ctx: &Context, inode: u64, name: &str, size: u32) -> Result<Option<Vec<u8>>> {
		let cname = CString::new(name).expect("invalid c string");
		match self.getxattr(ctx, Self::Inode::from(inode), cname.as_c_str(), size)
		{
			Ok(v) => {
				if let GetxattrReply::Value(buf) = v {
					return Ok(Some(buf));
				} else {
					return Ok(None);
				}
			},
			Err(e) => {
				if let Some(raw_error) = e.raw_os_error() {
					if raw_error == libc::ENODATA || raw_error == libc::ENOTSUP || raw_error == libc::ENOSYS {
						return Ok(None);
					}
				}

				return Err(e);
			},
		}
	}

	fn whiteout_exists(&self, ctx: &Context, ino: u64, name: &CStr) -> Result<(bool, u64, String)> {
		let sname = name.to_string_lossy().into_owned().to_owned();

		let mut wh_name = String::from(WHITEOUT_PREFIX);
		wh_name.push_str(sname.as_str());

		// .wh.name exists
		if let Some(v) = self.lookup_ignore_enoent(ctx, ino, wh_name.as_str())? {
			return Ok((true, v.inode, wh_name));
		}

		// char node whiteout
		if let Some(st) = self.lookup_ignore_enoent(ctx, ino, sname.as_str())? {
			let major = unsafe { libc::major(st.attr.st_rdev) };
			let minor = unsafe { libc::minor(st.attr.st_rdev) };
			if st.attr.st_mode & libc::S_IFMT == libc::S_IFCHR && major == 0 && minor == 0 {
				return Ok((true, st.inode, sname));
			}
		}
		
		Ok((false, VFS_MAX_INO, String::from("")))
	}

	fn is_opaque_whiteout(&self, ctx: &Context, inode: u64) -> Result<(bool, Option<u64>)> {
		let (st, _d) = self.getattr(ctx, Self::Inode::from(inode), None)?;
		if st.st_mode & libc::S_IFMT != libc::S_IFDIR {
			return Err(Error::from_raw_os_error(libc::ENOTDIR));
		}

		// check xattr first
		if let Some(v) = self.getxattr_ignore_nodata(ctx, inode, PRIVILEGED_OPAQUE_XATTR, OPAQUE_XATTR_LEN)? {
			if v[0].to_ascii_lowercase() == b'y' {
				return Ok((true, None));
			} else {
				return Ok((false, None));
			}
		}

		if let Some(v) = self.getxattr_ignore_nodata(ctx, inode, UNPRIVILEGED_OPAQUE_XATTR, OPAQUE_XATTR_LEN)? {
			if v[0].to_ascii_lowercase() == b'y' {
				return Ok((true, None));
			} else {
				return Ok((false, None));
			}
		}

		if let Some(v) = self.getxattr_ignore_nodata(ctx, inode, OPAQUE_XATTR, OPAQUE_XATTR_LEN)? {
			if v[0].to_ascii_lowercase() == b'y' {
				return Ok((true, None));
			} else {
				return Ok((false, None));
			}
		}

		// check .wh..wh..opaque, hwoever, we have no parent inode number for the parent of .wh..wh..opaque
		if let Some(v) = self.lookup_ignore_enoent(ctx, inode, OPAQUE_WHITEOUT)? {
			return Ok((true, Some(v.inode)));
		}

		Ok((false, None))
	}

	fn delete_whiteout(&self, ctx: &Context, parent: u64, name: &str) -> Result<()> {
		if !self.is_upper() {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		let mut wh_name = String::from(WHITEOUT_PREFIX);
		wh_name.push_str(name);
		let cwh_name = CString::new(wh_name.as_str()).expect("invalid c string");
		let cname = CString::new(name).expect("invalid c string");

		// .wh.name exists
		if let Some(v) = self.lookup_ignore_enoent(ctx, parent, wh_name.as_str())? {
			self.unlink(ctx, Self::Inode::from(parent), cwh_name.as_c_str())?;
		}

		// char node whiteout
		if let Some(st) = self.lookup_ignore_enoent(ctx, parent, name)? {
			let major = unsafe { libc::major(st.attr.st_rdev) };
			let minor = unsafe { libc::minor(st.attr.st_rdev) };
			if st.attr.st_mode & libc::S_IFMT == libc::S_IFCHR && major == 0 && minor == 0 {
				self.unlink(ctx, Self::Inode::from(parent), cname.as_c_str())?;
			}
		}

		Ok(())
	}
	fn create_whiteout(&self, ctx: &Context, parent: u64, name: &str) -> Result<Entry> {
		if !self.is_upper() {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		let mut wh_name = String::from(WHITEOUT_PREFIX);
		wh_name.push_str(name);
		let cwh_name = CString::new(wh_name.as_str()).expect("invalid c string");
		let cname = CString::new(name).expect("invalid c string");

		let (exists, _inode, name) = self.whiteout_exists(ctx, parent, cname.as_c_str())?;

		if exists {
			return self.lookup(ctx, Self::Inode::from(parent), CString::new(name.as_str()).expect("invalid c string").as_c_str());
		}

		// try to creat .wh.name
		let args = CreateIn {
			flags: 0,
			mode: 0o777,
			umask: 0,
			fuse_flags: 0,
		};

		if let Ok((entry, h, o)) = self.create(ctx, Self::Inode::from(parent), cwh_name.as_c_str(), args) {
			// if let Some(handle) = h {
			// 	self.release(ctx, Self::Inode::from(entry.inode), 0, handle, true, true, None)?;
			// }

			return Ok(entry);
		}

		// try mknod
		let dev = unsafe { libc::makedev(0, 0) };
		let mode = libc::S_IFCHR | 0o777;
		self.mknod(ctx, Self::Inode::from(parent), cname.as_c_str(), mode, dev as u32, 0)
	}

	fn create_opaque_whiteout(&self, ctx: &Context, parent: u64) -> Result<Entry> {
		if !self.is_upper() {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		let cname = CString::new(OPAQUE_WHITEOUT).expect("invalid c string");

		// opaque whiteout exists
		if let Some(v) = self.lookup_ignore_enoent(ctx, parent, OPAQUE_WHITEOUT)? {
			return Ok(v);
		}

		// create
		let args = CreateIn {
			flags: 0,
			mode: 0o777,
			umask: 0,
			fuse_flags: 0,
		};

		let (entry, h, _o) = self.create(ctx, Self::Inode::from(parent), cname.as_c_str(), args)?;

		Ok(entry)
	}

}
