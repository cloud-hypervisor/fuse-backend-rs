extern crate fuse_backend_rs;
extern crate log;
extern crate vmm_sys_util;
extern crate libc;
extern crate simple_logger;
extern crate signal_hook;
#[macro_use]
extern crate lazy_static;

use std::io::{Result, Error};
use std::sync::{Arc, Mutex};
use std::path::Path;

use fuse_backend_rs::overlayfs::{OverlayFs};
use fuse_backend_rs::overlayfs::config::Config;
use fuse_backend_rs::overlayfs::plugin::PluginManager;
use fuse_backend_rs::api::server::Server;
use fuse_backend_rs::transport::{FuseChannel, FuseSession};
use fuse_backend_rs::api::{Vfs, VfsOptions};
use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
use std::thread;
use simple_logger::SimpleLogger;
use log::LevelFilter;

pub struct FuseServer {
	server: Arc<Server<Arc<OverlayFs>>>,
	ch: FuseChannel,
}

fn main() -> Result<()> {
	SimpleLogger::new().with_level(LevelFilter::Trace).init().unwrap();
	let upperdir = String::from("/home/boyang/sources/testoverlay/testdir/upper");
	let mut lowerdir = Vec::new();
	lowerdir.push(String::from("/home/boyang/sources/testoverlay/testdir/lower1"));
	lowerdir.push(String::from("/home/boyang/sources/testoverlay/testdir/lower2"));
	let workdir = String::from("/home/boyang/sources/testoverlay/testdir/work");
	let mountpoint = String::from("/home/boyang/sources/testoverlay/testdir/merged");

	let mut config = Config::default();
	config.upper = upperdir;
	config.lower = lowerdir;
	config.work = workdir;
	config.mountpoint = String::from(mountpoint.as_str());
	config.do_import = true;

	let manager = PluginManager::new();

	print!("new overlay fs\n");
	let mut fs = OverlayFs::new(&manager, config)?;
	print!("init root inode\n");
	fs.init_root()?;

	// let vfs = Vfs::new(VfsOptions {
	//	no_open: false,
	//	no_opendir: false,
	//	..Default::default()
	// });

	// vfs.mount(Box::new(fs), "/")?;
	print!("open fuse session\n");
	let mut se = FuseSession::new(Path::new(mountpoint.as_str()), "testoverlay", "", false).unwrap();
	print!("session opened\n");
	se.mount().unwrap();

	let mut server = FuseServer {
		server: Arc::new(Server::new(Arc::new(fs))),
		ch: se.new_channel().unwrap(),
	};

	let quit = Arc::new(Mutex::new(false));
	let quit1 = Arc::clone(&quit);

	let handle = thread::spawn(move || {
		let _ = server.svc_loop(quit1);
	});

	// main thread
	let mut signals = Signals::new(TERM_SIGNALS).unwrap();
	for _sig in signals.forever() {
		*quit.lock().unwrap() = true;
		break;
	}

	let _ = handle.join();

	se.umount().unwrap();
	se.wake().unwrap();

	Ok(())
}

impl FuseServer {
	pub fn svc_loop(&mut self, quit: Arc<Mutex<bool>>) -> Result<()>{
        let _ebadf = std::io::Error::from_raw_os_error(libc::EBADF);
		print!("entering server loop\n");
        loop {

			if *quit.lock().unwrap() {
				break;
			}

            if let Some((reader, writer)) = self
                .ch
                .get_request()
                .map_err(|_| std::io::Error::from_raw_os_error(libc::EINVAL))?
            {
                if let Err(e) = self
                    .server
                    .handle_message(reader, writer.into(), None, None)
                {
                    match e {
                        fuse_backend_rs::Error::EncodeMessage(_ebadf) => {
                            break;
                        }
                        _ => {
                            print!("Handling fuse message failed");
                            continue;
                        }
                    }
                }
            } else {
                print!("fuse server exits");
                break;
            }
        }
        Ok(())
	}
}
