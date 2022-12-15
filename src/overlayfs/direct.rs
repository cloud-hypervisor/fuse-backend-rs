use std::collections::LinkedList;
use std::sync::Arc;
use std::io::{Result, Error, ErrorKind};
use std::fs;
use std::ffi::{CStr, CString};
use std::time::Duration;


use self::super::layer::Layer;
use self::super::BoxedLayer;
use self::super::{Inode, Handle};
use crate::passthrough::{PassthroughFs, Config as PassthroughConfig};
use crate::api::filesystem::{Entry, FileSystem, FsOptions, OpenOptions, GetxattrReply, ListxattrReply, DirEntry, SetattrValid, ZeroCopyReader, ZeroCopyWriter, Context};
use crate::abi::fuse_abi::CreateIn;

pub struct Direct {
	pub upper: bool,
	pub fs: PassthroughFs,
}

impl Direct {
	pub fn new(path: String, upper: bool) -> Result<LinkedList<Arc<BoxedLayer>>> {
		let dir = fs::canonicalize(path.as_str())?;
		let root_dir = dir.to_string_lossy().into_owned().to_owned();
		let mut config = PassthroughConfig::default();
		config.root_dir = root_dir;

		// enable xattr
		config.xattr = true;

		// under overlay fs, no need to negotiate
		config.do_import = false;
		let fs = PassthroughFs::new(config)?;

		let mut layer = Direct{
			upper,
			fs,
		};

		layer.init_layer()?;

		let mut list = LinkedList::new();
		list.push_back(Arc::new(Box::new(layer) as BoxedLayer));

		Ok(list)
	}
}

impl Layer for Direct {
	fn init_layer(&mut self) -> Result<()> {
		self.fs.import()
	}

	fn cleanup(&mut self) -> Result<()> {
		Ok(())
	}

	fn is_upper(&self) -> bool {
		self.upper
	}
}

impl FileSystem for Direct {
	type Inode = Inode;
	type Handle = Handle;

	fn init(&self, capable: FsOptions) -> Result<FsOptions> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn destroy(&self) {
		self.fs.destroy()
	}

	fn statfs(&self, ctx: &Context, inode: Inode) -> Result<libc::statvfs64> {
		self.fs.statfs(ctx, inode)
	}

	fn lookup(&self, ctx: &Context, parent: Inode, name: &CStr) -> Result<Entry> {
		self.fs.lookup(ctx, parent, name)
	}

	fn forget(&self, ctx: &Context, inode: Inode, count: u64) {
		self.fs.forget(ctx, inode, count)
	}

	fn batch_forget(&self, ctx: &Context, requests: Vec<(Inode, u64)>) {
		self.fs.batch_forget(ctx, requests)
	}

	fn opendir(&self, ctx: &Context, inode: Inode, flags: u32) -> Result<(Option<Handle>, OpenOptions)> {
		// should test flags to refuse write operations
		let iflags: i32 = flags as i32;
		let write = iflags & libc::O_RDWR != 0 || iflags & libc::O_WRONLY != 0 || iflags & libc::O_CREAT != 0 || iflags & libc::O_APPEND != 0 || iflags & libc::O_TRUNC != 0;
		if !self.upper && write {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.opendir(ctx, inode, flags)
	}

	fn releasedir(&self, ctx: &Context, inode: Inode, flags: u32, handle: Handle) -> Result<()> {
		self.fs.releasedir(ctx, inode, flags, handle)
	}

	fn mkdir(&self, ctx: &Context, parent: Inode, name: &CStr, mode: u32, umask: u32) -> Result<Entry> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.mkdir(ctx, parent, name, mode, umask)
	}

	fn rmdir(&self, ctx: &Context, parent: Inode, name: &CStr) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.rmdir(ctx, parent, name)
	}

	fn readdir(&self, ctx: &Context, inode: Inode, handle: Handle, size: u32, offset: u64, add_entry: &mut dyn FnMut(DirEntry) -> Result<usize>) -> Result<()> {
		self.fs.readdir(ctx, inode, handle, size, offset, add_entry)
	}

	fn readdirplus(&self, ctx: &Context, inode: Inode, handle: Handle, size: u32, offset: u64, add_entry: &mut dyn FnMut(DirEntry, Entry) -> Result<usize>) -> Result<()> {
		self.fs.readdirplus(ctx, inode, handle, size, offset, add_entry)
	}

	fn open(&self, ctx: &Context, inode: Inode, flags: u32, fuse_flags: u32) -> Result<(Option<Handle>, OpenOptions)> {
		let iflags: i32 = flags as i32;
		let write = iflags & libc::O_RDWR != 0 || iflags & libc::O_WRONLY != 0 || iflags & libc::O_CREAT != 0 || iflags & libc::O_APPEND != 0 || iflags & libc::O_TRUNC != 0;
		if !self.upper && write {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.open(ctx, inode, flags, fuse_flags)
	}

	fn release(&self, ctx: &Context, inode: Inode, flags: u32, handle: Handle, flush: bool, flock_release: bool, lock_owner: Option<u64>) -> Result<()> {
		self.fs.release(ctx, inode, flags, handle, flush, flock_release, lock_owner)
	}

	fn create(&self, ctx: &Context, parent: Inode, name: &CStr, args: CreateIn) -> Result<(Entry, Option<Handle>, OpenOptions)> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.create(ctx, parent, name, args)
	}

	fn unlink(&self, ctx: &Context, parent: Inode, name: &CStr) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.unlink(ctx, parent, name)
	}

	fn read(&self, ctx: &Context, inode: Inode, handle: Handle, w: &mut dyn ZeroCopyWriter, size: u32, offset: u64, lock_owner: Option<u64>, flags: u32) -> Result<usize> {
		self.fs.read(ctx, inode, handle, w, size, offset, lock_owner, flags)
	}

	fn write(&self, ctx: &Context, inode: Inode, handle: Handle, r: &mut dyn ZeroCopyReader, size: u32, offset: u64, lock_owner: Option<u64>, delay_write: bool, flags: u32, fuse_flags: u32) -> Result<usize> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.write(ctx, inode, handle, r, size, offset, lock_owner, delay_write, flags, fuse_flags)
	}

	fn getattr(&self, ctx: &Context, inode: Inode, handle: Option<Handle>) -> Result<(libc::stat64, Duration)> {
		self.fs.getattr(ctx, inode, handle)
	}

	fn setattr(&self, ctx: &Context, inode: Inode, attr: libc::stat64, handle: Option<Handle>, valid: SetattrValid) -> Result<(libc::stat64, Duration)> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.setattr(ctx, inode, attr, handle, valid)
	}

	fn rename(&self, ctx: &Context, olddir: Inode, oldname: &CStr, newdir: Inode, newname: &CStr, flags: u32) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.rename(ctx, olddir, oldname, newdir, newname, flags)
	}

	fn mknod(&self, ctx: &Context, parent: Inode, name: &CStr, mode: u32, rdev: u32, umask: u32) -> Result<Entry> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.mknod(ctx, parent, name, mode, rdev, umask)
	}

	fn link(&self, ctx: &Context, inode: Inode, newparent: Inode, newname: &CStr) -> Result<Entry> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.link(ctx, inode, newparent, newname)
	}

	fn symlink(&self, ctx: &Context, linkname: &CStr, parent: Inode, name: &CStr) -> Result<Entry> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.symlink(ctx, linkname, parent, name)
	}

	fn readlink(&self, ctx: &Context, inode: Inode) -> Result<Vec<u8>> {
		self.fs.readlink(ctx, inode)
	}

	fn flush(&self, ctx: &Context, inode: Inode, handle: Handle, lock_owner: u64) -> Result<()> {
		// even readonly opened file can be flushed,
		// so it does't have to be in upper layer
		// if !self.upper {
		// 	return Err(Error::from_raw_os_error(libc::EROFS));
		// }

		self.fs.flush(ctx, inode, handle, lock_owner)
	}

	fn fsync(&self, ctx: &Context, inode: Inode, datasync: bool, handle: Handle) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.fsync(ctx, inode, datasync, handle)
	}

	fn fsyncdir(&self, ctx: &Context, inode: Inode, datasync: bool, handle: Handle) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.fsyncdir(ctx, inode, datasync, handle)
	}

	fn access(&self, ctx: &Context, inode: Inode, mask: u32) -> Result<()> {
		let write = mask as i32 & libc::W_OK != 0;
		if !self.upper && write {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.access(ctx, inode, mask)
	}

	fn setxattr(&self, ctx: &Context, inode: Inode, name: &CStr, value: &[u8], flags: u32) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.setxattr(ctx, inode, name, value, flags)
	}

	fn getxattr(&self, ctx: &Context, inode: Inode, name: &CStr, size: u32) -> Result<GetxattrReply> {
		self.fs.getxattr(ctx, inode, name, size)
	}

	fn listxattr(&self, ctx: &Context, inode: Inode, size: u32) -> Result<ListxattrReply> {
		self.fs.listxattr(ctx, inode, size)
	}

	fn removexattr(&self, ctx: &Context, inode: Inode, name: &CStr) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.removexattr(ctx, inode, name)
	}

	fn fallocate(&self, ctx: &Context, inode: Inode, handle: Handle, mode: u32, offset: u64, length: u64) -> Result<()> {
		if !self.upper {
			return Err(Error::from_raw_os_error(libc::EROFS));
		}

		self.fs.fallocate(ctx, inode, handle, mode, offset, length)
	}

	fn lseek(&self, ctx: &Context, inode: Inode, handle: Handle, offset: u64, whence: u32) -> Result<u64> {
		self.fs.lseek(ctx, inode, handle, offset, whence)
	}
}
