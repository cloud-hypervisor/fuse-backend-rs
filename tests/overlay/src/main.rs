extern crate fuse_backend_rs;
extern crate lazy_static;
extern crate libc;
extern crate log;
extern crate signal_hook;
extern crate simple_logger;
extern crate vmm_sys_util;

use std::env;
use std::io::{Error, Result};
use std::path::Path;
use std::sync::Arc;
use std::thread;

use fuse_backend_rs::api::filesystem::Layer;
use fuse_backend_rs::api::server::Server;
use fuse_backend_rs::overlayfs::config::Config;
use fuse_backend_rs::overlayfs::OverlayFs;
use fuse_backend_rs::passthrough::{self, PassthroughFs};
use fuse_backend_rs::transport::{FuseChannel, FuseSession};
use log::LevelFilter;
use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
use simple_logger::SimpleLogger;

#[derive(Debug, Default)]
pub struct Args {
    name: String,
    mountpoint: String,
    lowerdir: Vec<String>,
    upperdir: String,
    workdir: String,
    log_level: String,
}

pub struct FuseServer {
    server: Arc<Server<Arc<OverlayFs>>>,
    ch: FuseChannel,
}

type BoxedLayer = Box<dyn Layer<Inode = u64, Handle = u64> + Send + Sync>;

fn new_passthroughfs_layer(rootdir: &str) -> Result<BoxedLayer> {
    let mut config = passthrough::Config::default();
    config.root_dir = String::from(rootdir);
    // enable xattr
    config.xattr = true;
    config.do_import = true;
    let fs = Box::new(PassthroughFs::<()>::new(config)?);
    fs.import()?;
    Ok(fs as BoxedLayer)
}

fn help() {
    println!(
        "Usage:\n   overlay -o lowerdir=<lower1>:<lower2>:<more>,upperdir=<upper>,workdir=<work> <name> <mountpoint> [-l log_level]\n"
    );
}

fn parse_args() -> Result<Args> {
    let args = env::args().collect::<Vec<String>>();
    // We expect at least 5 arguments.
    if args.len() < 5 {
        help();
        return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
    }

    let mut cmd_args = Args {
        name: "".to_string(),
        mountpoint: "".to_string(),
        ..Default::default()
    };

    let mut i = 0;
    loop {
        i += 1;
        if i >= args.len() {
            break;
        }
        if args[i].as_str() == "-h" {
            help();
            return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
        }

        if args[i].as_str() == "-o" {
            i += 1;
            // Parse options.
            let option = args[i].clone();
            option.split(",").try_for_each(|value| -> Result<()> {
                let kv = value.split("=").collect::<Vec<&str>>();
                if kv.len() != 2 {
                    println!("unknown option: {}", value);
                    return Ok(());
                }

                match kv[0] {
                    "lowerdir" => {
                        cmd_args.lowerdir = kv[1]
                            .split(":")
                            .map(|s| s.to_string())
                            .collect::<Vec<String>>();
                    }
                    "upperdir" => {
                        cmd_args.upperdir = kv[1].to_string();
                    }
                    "workdir" => {
                        cmd_args.workdir = kv[1].to_string();
                    }
                    _ => {
                        // Ignore unknown options.
                        println!("unknown option: {}", kv[0]);
                    }
                }
                Ok(())
            })?;
            continue;
        }

        if args[i].as_str() == "-l" {
            i += 1;
            cmd_args.log_level = args[i].clone();
        }

        if cmd_args.name.is_empty() {
            cmd_args.name = args[i].clone();
            continue;
        } else if cmd_args.mountpoint.is_empty() {
            cmd_args.mountpoint = args[i].clone();
            continue;
        }
    }

    // All fields should be set.
    if cmd_args.lowerdir.is_empty() || cmd_args.upperdir.is_empty() || cmd_args.workdir.is_empty() {
        println!("lowerdir, upperdir and workdir should be set");
        help();
        return Err(Error::from_raw_os_error(libc::EINVAL));
    }

    Ok(cmd_args)
}

fn set_log(args: &Args) {
    let log_level = match args.log_level.as_str() {
        "trace" => LevelFilter::Trace,
        "debug" => LevelFilter::Debug,
        "info" => LevelFilter::Info,
        "warn" => LevelFilter::Warn,
        "error" => LevelFilter::Error,
        _ => LevelFilter::Info,
    };

    SimpleLogger::new().with_level(log_level).init().unwrap();
}

fn main() -> Result<()> {
    let args = parse_args()?;
    println!("args: {:?}", args);

    set_log(&args);

    // let basedir = "/home/zhangwei/program/test-overlay/test2/";
    let upper_layer = Arc::new(new_passthroughfs_layer(&args.upperdir)?);
    let mut lower_layers = Vec::new();
    for lower in args.lowerdir {
        lower_layers.push(Arc::new(new_passthroughfs_layer(&lower)?));
    }

    let mut config = Config::default();
    config.work = args.workdir.clone();
    config.mountpoint = args.mountpoint.clone();
    config.do_import = true;

    print!("new overlay fs\n");
    let fs = OverlayFs::new(Some(upper_layer), lower_layers, config)?;
    print!("init root inode\n");
    fs.import()?;

    print!("open fuse session\n");
    let mut se = FuseSession::new(Path::new(&args.mountpoint), &args.name, "", false).unwrap();
    print!("session opened\n");
    se.mount().unwrap();

    let mut server = FuseServer {
        server: Arc::new(Server::new(Arc::new(fs))),
        ch: se.new_channel().unwrap(),
    };

    let handle = thread::spawn(move || {
        let _ = server.svc_loop();
    });

    // main thread
    let mut signals = Signals::new(TERM_SIGNALS).unwrap();
    for _sig in signals.forever() {
        break;
    }

    se.umount().unwrap();
    se.wake().unwrap();

    let _ = handle.join();

    Ok(())
}

impl FuseServer {
    pub fn svc_loop(&mut self) -> Result<()> {
        let _ebadf = std::io::Error::from_raw_os_error(libc::EBADF);
        print!("entering server loop\n");
        loop {
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
