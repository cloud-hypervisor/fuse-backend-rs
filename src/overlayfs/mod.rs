#![allow(missing_docs)]

pub mod layer;
pub mod datasource;
pub mod plugin;
pub mod config;
pub mod direct;

use std::collections::{LinkedList, HashMap};
use std::io::Result;
use std::sync::{Arc, Mutex, Weak};
use std::sync::atomic::{AtomicBool, Ordering, AtomicU64};
use std::any::Any;
use std::ffi::CStr;
use std::time::Duration;
use std::string::ToString;

use crate::api::filesystem::{Entry, FileSystem, FsOptions, OpenOptions, GetxattrReply, ListxattrReply, DirEntry, SetattrValid, ZeroCopyReader, ZeroCopyWriter, Context};
use crate::api::{BackendFileSystem, SLASH_ASCII, VFS_MAX_INO};
use crate::abi::fuse_abi::CreateIn;

use self::plugin::PluginManager;
use self::layer::Layer;
use self::config::Config;
use std::io::{Error, ErrorKind};
use libc;


type Inode = u64;
type Handle = u64;
pub const PLUGIN_PREFIX: &str = "//";
pub const WHITEOUT_PREFIX: &str = ".wh.";
pub const XATTR_PREFIX: &str = "user.fuseoverlayfs";
pub const ORIGIN_XATTR: &str = "user.fuseoverlayfs.origin";
pub const OPAQUE_XATTR: &str = "user.fuseoverlayfs.opaque";
pub const XATTR_CONTAINERS_PREFIX: &str = "user.containers";
pub const UNPRIVILEGED_XATTR_PREFIX: &str = "user.overlay";
pub const UNPRIVILEGED_OPAQUE_XATTR: &str = "user.overlay.opaque";
pub const PRIVILEGED_XATTR_PREFIX: &str = "trusted.overlay";
pub const PRIVILEGED_OPAQUE_XATTR: &str = "trusted.overlay.opaque";
pub const PRIVILEGED_ORIGIN_XATTR: &str = "trusted.overlay.origin";
pub const OPAQUE_WHITEOUT: &str = ".wh..wh..opq";

#[derive(Default)]
pub struct OverlayInode {
	pub childrens: Mutex<HashMap<String, Arc<OverlayInode>>>,
	pub parent: Mutex<Weak<OverlayInode>>,
	pub layers: Vec<Arc<Box<dyn Layer>>>,
	pub last_layer: Option<Arc<Box<dyn Layer>>>,
	pub ino: libc::ino64_t,
	pub dev: libc::dev_t,
	pub mode: libc::mode_t,
	pub path: String,
	pub name: String,

	pub hidden: AtomicBool,
	pub whiteout: AtomicBool,
	pub loaded: AtomicBool,

	// what about data source related data for each inode
	// put it into layer struct, ino -> private data hash
}

pub struct OverlayFs {
	// should be in daemon structure
	pub config: Config,
	pub layers: LinkedList<Arc<Box<dyn Layer>>>,
	pub upper_layer: Option<Arc<Box<dyn Layer>>>,
	// inode management..
	pub root: Arc<OverlayInode>,
	pub inodes: Mutex<HashMap<u64, Arc<OverlayInode>>>, 
	pub next_inode: AtomicU64,
	pub writeback: AtomicBool,
	pub no_open: AtomicBool,
	pub no_opendir: AtomicBool,
	pub killpriv_v2: AtomicBool,
	pub perfile_dax: AtomicBool,
}

fn process_lower_layer(manager: &PluginManager, opaque: &[String]) -> Result<LinkedList<Arc<Box<dyn Layer>>>> {
	let mut layers = LinkedList::new();

	for lower in opaque {
		let mut lower_layers = plugin::process_onelayer(manager, lower.into())?;
		layers.append(&mut lower_layers);
	}

	Ok(layers)
}

impl OverlayInode {
	pub fn new() -> Self {
		OverlayInode::default()
	}
}

impl OverlayFs {
	pub fn new(manager: &PluginManager, params: Config) -> Result<Self> {
		// upper dir 
		let mut layers = plugin::process_onelayer(manager, String::from(params.upper.as_str()))?;

		// lower dir
		let mut lower_layers = process_lower_layer(manager, params.lower.as_slice())?;

		layers.append(&mut lower_layers);
		// load root inode
		Ok(OverlayFs {
				config: params,
				layers,
				inodes: Mutex::new(HashMap::new()),
			})
	}

	pub fn import(&self) -> Result<()> {
		Ok(())
	}

	pub fn lookup_node(&self, parent: Inode, name: &CStr) -> Result<Arc<OverlayInode>> {
		if name.to_bytes_with_nul().contains(&SLASH_ASCII) {
			return Err(Error::from_raw_os_error(libc::EINVAL));
		}

		// lookup name
		let pnode = {
			let inodes = self.inodes.lock().unwrap();
			if let Some(v) = inodes.get(&parent) {
				Arc::clone(v)
			} else {
				// no parent inode?
				return Err(Error::from_raw_os_error(libc::EINVAL));
			}
		};

		let sname = name.to_string_lossy().into_owned().to_owned();
		if sname.is_empty() || sname.starts_with(WHITEOUT_PREFIX){
			return Err(Error::from_raw_os_error(libc::EINVAL));
		}

		// found the node
		if let Some (v) = pnode.childrens.lock().unwrap().get(sname.as_str()) {
			return Ok(Arc::clone(v));
		}

		// don't find it, lookup in layers
		let mut wh_name = String::from(WHITEOUT_PREFIX);
		wh_name.push_str(sname.as_str());

		let mut path = String::from(pnode.path);
		path.push_str("/");
		path.push_str(sname.as_str());
		let ppath = String::from(pnode.path);

		let mut node_inited: bool = false;
		let mut new = OverlayInode::new();

		// always add upper layer to layers
		if let Some(ref l) = self.upper_layer {
			new.layers.push(Arc::clone(l));
		}

		'layer_loop:
		for layer in self.layers.iter() {
			// check whiteout first
			if layer.whiteout_exists(ppath.as_str(), pnode.ino as u64, sname.as_str())? {
				if !node_inited {
					new.whiteout.store(true, Ordering::Relaxed);
					new.path = String::from(path.as_str());
					new.name = String::from(sname.as_str());
					// find an available inode number to use
					let ino = self.next_inode.fetch_add(1, Ordering::Relaxed);

					if ino > VFS_MAX_INO {
						error!("reached maximum inode number: {}", VFS_MAX_INO);
						return Err(Error::new(ErrorKind::Other, format!("maximum inode number {} reached", VFS_MAX_INO)));
					}

					new.ino = ino;
					node_inited = true;
				}

				break 'layer_loop;
			}

			let st = layer.stat64(ppath.as_str(), pnode.ino as u64, sname.as_str());

			match st {
				Ok(s) => {
					if !node_inited {
						new.path = String::from(path.as_str());
						new.name = String::from(sname.as_str());
						// find an available inode number to use
						let ino = self.next_inode.fetch_add(1, Ordering::Relaxed);

						if ino > VFS_MAX_INO {
							error!("reached maximum inode number: {}", VFS_MAX_INO);
							return Err(Error::new(ErrorKind::Other, format!("maximum inode number {} reached", VFS_MAX_INO)));
						}

						new.ino = ino;
						new.layers.push(Arc::clone(layer));
						node_inited = true;
					} else {
						//add this layer to node
						new.layers.push(Arc::clone(layer));
					}

					// update layer specific datas
					layer.update_data(ppath.as_str(), pnode.ino as u64, sname.as_str(), new.ino as u64);

					// am I file? break out if it is a file
					// directory have to be merged
					// FIXME: it is wrong..
					// what if a dir xx in layer1,  and then a file xx in layer2
					if s.st_mode & libc::S_IFDIR == 0 {
							break 'layer_loop;
					}

					// opaque whiteout?
					if layer.is_opaque_whiteout(ppath.as_str(), pnode.ino as u64, sname.as_str(), new.ino as u64)? {
						// end here
						break 'layer_loop;
					}
					// next layer..
				},

				Err(e) => {
					if let Some(raw_error) =  e.raw_os_error() {
						if raw_error == libc::ENOENT || raw_error == libc::ENOTDIR || raw_error == libc::ENAMETOOLONG {
							// not exists, try next layer
							continue 'layer_loop;
						}
					}

					// other errors, error out or return partial
					// lookup result?
					break 'layer_loop;
				},
			}
		}

		if node_inited {
			// set its parent node
			*new.parent.lock().unwrap() = Arc::downgrade(&pnode);
			// insert node into hashs
			let new_node = Arc::new(new);
			self.inodes.lock().unwrap().insert(new.ino as u64, Arc::clone(&new_node));
			pnode.childrens.lock().unwrap().insert(sname, Arc::clone(&new_node));
			return Ok(Arc::clone(&new_node));
		}

		// return specific errors?
		Err(Error::from_raw_os_error(libc::ENOENT))
	}

	pub fn get_node_from_inode(&self, inode: u64) -> Option<Arc<OverlayInode>> {
		if let Some(v) = self.inodes.lock().unwrap().get(&inode) {
			return Some(Arc::clone(v));
		}

		return None;
	}
}

impl BackendFileSystem for OverlayFs {
	fn mount(&self) -> Result<(Entry, u64)> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn as_any(&self) -> &dyn Any {
		self
	}
}

impl FileSystem for OverlayFs {
	type Inode = Inode;
	type Handle = Handle;

	fn init(&self, capable: FsOptions) -> Result<FsOptions> {
		// use vfs' negotiated capability if imported
		// other wise, do our own negotiation
		let mut opts = FsOptions::DO_READDIRPLUS | FsOptions::READDIRPLUS_AUTO;

		if self.config.do_import {
			self.import()?;
		}

		if (!self.config.do_import || self.config.writeback) && capable.contains(FsOptions::WRITEBACK_CACHE) {
			opts |= FsOptions::WRITEBACK_CACHE;
			self.writeback.store(true, Ordering::Relaxed);
		}

		if (!self.config.do_import || self.config.no_open) && capable.contains(FsOptions::ZERO_MESSAGE_OPEN) {
			opts |= FsOptions::ZERO_MESSAGE_OPEN;
			opts.remove(FsOptions::ATOMIC_O_TRUNC);
			self.no_open.store(true, Ordering::Relaxed);
		}

		if (!self.config.do_import || self.config.no_opendir) && capable.contains(FsOptions::ZERO_MESSAGE_OPENDIR) {
			opts |= FsOptions::ZERO_MESSAGE_OPENDIR;
			self.no_opendir.store(true, Ordering::Relaxed);
		}

		if (!self.config.do_import || self.config.killpriv_v2) && capable.contains(FsOptions::HANDLE_KILLPRIV_V2) {
			opts |= FsOptions::HANDLE_KILLPRIV_V2;
			self.killpriv_v2.store(true, Ordering::Relaxed);
		}

		if self.config.perfile_dax && capable.contains(FsOptions::PERFILE_DAX) {
			opts |= FsOptions::PERFILE_DAX;
			self.perfile_dax.store(true, Ordering::Relaxed);
		}

		Ok(opts)
	}

	fn destroy(&self) {
	}

	fn statfs(&self, ctx: &Context, inode: Inode) -> Result<libc::statvfs64> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn lookup(&self, ctx: &Context, parent: Inode, name: &CStr) -> Result<Entry> {
		let node = self.lookup_node(parent, name)?;

		if node.whiteout.load(Ordering::Relaxed) {
			return Err(Error::from_raw_os_error(libc::ENOENT));
		}

		let pnode = if let Some(v) = self.get_node_from_inode(parent) {
			v
		} else {
			return Err(Error::from_raw_os_error(libc::EINVAL));
		};

		let ppath = String::from(pnode.path);
		let sname = name.to_string_lossy().into_owned().to_owned();
		let st = {
			let mut found: bool = false;
			let mut stat: libc::stat64;

			'layer_loop:
			for layer in node.layers {
				if let Ok(v) = layer.stat64(ppath.as_str(), parent, sname.as_str()) {
					stat = v;
					found = true;
					break 'layer_loop;
				}
			}

			if found {
				stat
			} else {
				return Err(Error::from_raw_os_error(libc::ENOENT));
			}
		};

		// load this directory here
		if st.st_mode & libc::S_IFMT == libc::S_IFDIR {
			self.load_directory(Arc::clone(&node))?;
		}

		Ok(Entry{
			inode: node.ino as u64,
			generation: 0,
			attr: st,//libc::stat64
			attr_flags: 0,
			attr_timeout: self.config.attr_timeout,
			entry_timeout: self.config.entry_timeout,
		})
	}

	fn forget(&self, ctx: &Context, inode: Inode, count: u64) {

	}

	fn batch_forget(&self, ctx: &Context, requests: Vec<(Inode, u64)>) {
	}

	fn opendir(&self, ctx: &Context, inode: Inode, flags: u32) -> Result<(Option<Handle>, OpenOptions)> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn releasedir(&self, ctx: &Context, inode: Inode, flags: u32, handle: Handle) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn mkdir(&self, ctx: &Context, parent: Inode, name: &CStr, mode: u32, umask: u32) -> Result<Entry> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn rmdir(&self, ctx: &Context, parent: Inode, name: &CStr) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn readdir(&self, ctx: &Context, inode: Inode, handle: Handle, size: u32, offset: u64, add_entry: &mut dyn FnMut(DirEntry) -> Result<usize>) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn readdirplus(&self, ctx: &Context, inode: Inode, handle: Handle, size: u32, offset: u64, add_entry: &mut dyn FnMut(DirEntry, Entry) -> Result<usize>) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn open(&self, ctx: &Context, inode: Inode, flags: u32, fuse_flags: u32) -> Result<(Option<Handle>, OpenOptions)> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn release(&self, ctx: &Context, inode: Inode, flags: u32, handle: Handle, flush: bool, flock_release: bool, lock_owner: Option<u64>) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn create(&self, ctx: &Context, parent: Inode, name: &CStr, args: CreateIn) -> Result<(Entry, Option<Handle>, OpenOptions)> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn unlink(&self, ctx: &Context, parent: Inode, name: &CStr) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn read(&self, ctx: &Context, inode: Inode, handle: Handle, w: &mut dyn ZeroCopyWriter, size: u32, offset: u64, lock_owner: Option<u64>, flags: u32) -> Result<usize> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn write(&self, ctx: &Context, inode: Inode, handle: Handle, r: &mut dyn ZeroCopyReader, size: u32, offset: u64, lock_owner: Option<u64>, delayed_write: bool, flags: u32, fuse_flags: u32) -> Result<usize> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn getattr(&self, ctx: &Context, inode: Inode, handle: Option<Handle>) -> Result<(libc::stat64, Duration)> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn setattr(&self, ctx: &Context, inode: Inode, attr: libc::stat64, handle: Option<Handle>, valid: SetattrValid) -> Result<(libc::stat64, Duration)> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn rename(&self, ctx: &Context, olddir: Inode, odlname: &CStr, newdir: Inode, newname: &CStr, flags: u32) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn mknod(&self, ctx: &Context, parent: Inode, name: &CStr, mode: u32, rdev: u32, umask: u32) -> Result<Entry> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn link(&self, ctx: &Context, inode: Inode, newparent: Inode, name: &CStr) -> Result<Entry> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn symlink(&self, ctx: &Context, linkname: &CStr, parent: Inode, name: &CStr) -> Result<Entry> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn readlink(&self, ctx: &Context, inode: Inode) -> Result<Vec<u8>> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn flush(&self, ctx: &Context, inode: Inode, handle: Handle, lock_owner: u64) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn fsync(&self, ctx: &Context, inode: Inode, datasync: bool, handle: Handle) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn fsyncdir(&self, ctx: &Context, inode: Inode, datasync: bool, handle: Handle) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn access(&self, ctx: &Context, inode: Inode, mask: u32) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn setxattr(&self, ctx: &Context, inode: Inode, name: &CStr, value: &[u8], flags: u32) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn getxattr(&self, ctx: &Context, inode: Inode, name: &CStr, size: u32) -> Result<GetxattrReply> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn listxattr(&self, ctx: &Context, inode: Inode, size: u32) -> Result<ListxattrReply> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn removexattr(&self, ctx: &Context, inode: Inode, name: &CStr) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn fallocate(&self, ctx: &Context, inode: Inode, handle: Handle, mode: u32, offset: u64, length: u64) -> Result<()> {
		Err(Error::from(ErrorKind::Unsupported))
	}

	fn lseek(&self, ctx: &Context, inode: Inode, handle: Handle, offset: u64, whence: u32) -> Result<u64> {
		Err(Error::from(ErrorKind::Unsupported))
	}

}
