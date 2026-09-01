//! Passthrough filesystem implementation using fuser.
//!
//! This mirrors all operations to a backing directory, providing a baseline
//! for comparing fuser performance against fuse-backend-rs.

use clap::Parser;
use fuser::{
    Filesystem, KernelConfig, MountOption, ReplyAttr, ReplyCreate, ReplyData,
    ReplyDirectory, ReplyEmpty, ReplyEntry, ReplyOpen, ReplyStatfs, ReplyWrite, ReplyXattr,
    Request,
};
use log::{error, info};
use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::os::unix::fs::{FileExt, MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::time::{Duration, SystemTime};

const TTL: Duration = Duration::from_secs(1);

#[derive(Parser)]
#[command(name = "passthrough-fuser")]
#[command(about = "Fuser-based passthrough filesystem for benchmarking")]
struct Args {
    /// Source directory to mirror
    src: String,
    /// Mount point
    dest: String,
    /// Number of worker threads (unused by fuser — single-threaded dispatch)
    #[arg(short, long, default_value = "1")]
    threads: usize,
}

/// Inode data stored per inode number
#[derive(Clone)]
struct InodeData {
    path: PathBuf,
}

/// File handle data for open files
struct FileHandle {
    file: File,
}

/// Passthrough filesystem implementation
struct PassthroughFs {
    _source: PathBuf,
    inodes: HashMap<u64, InodeData>,
    next_ino: u64,
    handles: HashMap<u64, FileHandle>,
    next_fh: u64,
}

impl PassthroughFs {
    fn new(source: PathBuf) -> Self {
        let mut inodes = HashMap::new();
        inodes.insert(
            1,
            InodeData {
                path: source.clone(),
            },
        );
        PassthroughFs {
            _source: source,
            inodes,
            next_ino: 2,
            handles: HashMap::new(),
            next_fh: 1,
        }
    }

    fn get_path(&self, ino: u64) -> Option<PathBuf> {
        self.inodes.get(&ino).map(|d| d.path.clone())
    }

    fn alloc_ino(&mut self, path: PathBuf) -> u64 {
        let ino = self.next_ino;
        self.next_ino += 1;
        self.inodes.insert(ino, InodeData { path });
        ino
    }

    fn alloc_fh(&mut self, file: File) -> u64 {
        let fh = self.next_fh;
        self.next_fh += 1;
        self.handles.insert(fh, FileHandle { file });
        fh
    }

    fn metadata_to_attr(&self, ino: u64, meta: &fs::Metadata) -> fuser::FileAttr {
        fuser::FileAttr {
            ino,
            size: meta.len(),
            blocks: meta.blocks(),
            atime: meta.accessed().unwrap_or(SystemTime::UNIX_EPOCH),
            mtime: meta.modified().unwrap_or(SystemTime::UNIX_EPOCH),
            ctime: SystemTime::UNIX_EPOCH,
            crtime: SystemTime::UNIX_EPOCH,
            kind: if meta.is_dir() {
                fuser::FileType::Directory
            } else if meta.is_symlink() {
                fuser::FileType::Symlink
            } else {
                fuser::FileType::RegularFile
            },
            perm: (meta.mode() & 0o7777) as u16,
            nlink: meta.nlink() as u32,
            uid: meta.uid(),
            gid: meta.gid(),
            rdev: meta.rdev() as u32,
            blksize: meta.blksize() as u32,
            flags: 0,
        }
    }
}

impl Filesystem for PassthroughFs {
    fn init(&mut self, _req: &Request<'_>, config: &mut KernelConfig) -> Result<(), libc::c_int> {
        // Match fuse-backend-rs INIT: 1MB max write (256 pages). Without this the
        // kernel splits large writes into 4k chunks on this host.
        let _ = config.set_max_write(1024 * 1024);
        info!("Passthrough filesystem initialized");
        Ok(())
    }

    fn destroy(&mut self) {
        info!("Passthrough filesystem destroyed");
    }

    fn lookup(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEntry) {
        let parent_path = match self.get_path(parent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        let child_path = parent_path.join(name);
        match fs::metadata(&child_path) {
            Ok(meta) => {
                let ino = self.alloc_ino(child_path);
                let attr = self.metadata_to_attr(ino, &meta);
                reply.entry(&TTL, &attr, 0);
            }
            Err(e) => {
                reply.error(e.raw_os_error().unwrap_or(libc::EIO));
            }
        }
    }

    fn getattr(&mut self, _req: &Request<'_>, ino: u64, _fh: Option<u64>, reply: ReplyAttr) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        match fs::metadata(&path) {
            Ok(meta) => {
                let attr = self.metadata_to_attr(ino, &meta);
                reply.attr(&TTL, &attr);
            }
            Err(e) => {
                reply.error(e.raw_os_error().unwrap_or(libc::EIO));
            }
        }
    }

    fn setattr(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        mode: Option<u32>,
        _uid: Option<u32>,
        _gid: Option<u32>,
        size: Option<u64>,
        _atime: Option<fuser::TimeOrNow>,
        _mtime: Option<fuser::TimeOrNow>,
        _ctime: Option<SystemTime>,
        _fh: Option<u64>,
        _crtime: Option<SystemTime>,
        _chgtime: Option<SystemTime>,
        _bkuptime: Option<SystemTime>,
        _flags: Option<u32>,
        reply: ReplyAttr,
    ) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        if let Some(size) = size {
            if let Err(e) = fs::OpenOptions::new()
                .write(true)
                .open(&path)
                .and_then(|f| f.set_len(size))
            {
                reply.error(e.raw_os_error().unwrap_or(libc::EIO));
                return;
            }
        }

        if let Some(mode) = mode {
            let _ = fs::set_permissions(&path, fs::Permissions::from_mode(mode));
        }

        match fs::metadata(&path) {
            Ok(meta) => {
                let attr = self.metadata_to_attr(ino, &meta);
                reply.attr(&TTL, &attr);
            }
            Err(e) => {
                reply.error(e.raw_os_error().unwrap_or(libc::EIO));
            }
        }
    }

    fn read(
        &mut self,
        _req: &Request<'_>,
        _ino: u64,
        fh: u64,
        offset: i64,
        size: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyData,
    ) {
        if let Some(handle) = self.handles.get_mut(&fh) {
            let mut buf = vec![0u8; size as usize];
            // pread: single syscall, no seek (matches fuse-backend-rs read_at path)
            match handle.file.read_at(&mut buf, offset as u64) {
                Ok(n) => {
                    buf.truncate(n);
                    reply.data(&buf);
                }
                Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
            }
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn write(
        &mut self,
        _req: &Request<'_>,
        _ino: u64,
        fh: u64,
        offset: i64,
        data: &[u8],
        _write_flags: u32,
        _flags: i32,
        _lock_owner: Option<u64>,
        reply: ReplyWrite,
    ) {
        if let Some(handle) = self.handles.get_mut(&fh) {
            // pwrite: single syscall, no seek (matches fuse-backend-rs write path)
            match handle.file.write_at(data, offset as u64) {
                Ok(n) => reply.written(n as u32),
                Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
            }
        } else {
            reply.error(libc::EBADF);
        }
    }

    fn open(&mut self, _req: &Request<'_>, ino: u64, flags: i32, reply: ReplyOpen) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        let mut opts = fs::OpenOptions::new();
        let access_mode = flags & libc::O_ACCMODE;
        if access_mode == libc::O_RDONLY {
            opts.read(true);
        } else if access_mode == libc::O_WRONLY {
            opts.write(true);
        } else if access_mode == libc::O_RDWR {
            opts.read(true).write(true);
        }
        if flags & libc::O_APPEND != 0 {
            opts.append(true);
        }
        if flags & libc::O_TRUNC != 0 {
            opts.truncate(true);
        }

        match opts.open(&path) {
            Ok(file) => {
                let fh = self.alloc_fh(file);
                reply.opened(fh, 0);
            }
            Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }

    fn release(
        &mut self,
        _req: &Request<'_>,
        _ino: u64,
        fh: u64,
        _flags: i32,
        _lock_owner: Option<u64>,
        _flush: bool,
        reply: ReplyEmpty,
    ) {
        self.handles.remove(&fh);
        reply.ok();
    }

    fn create(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        mode: u32,
        _umask: u32,
        flags: i32,
        reply: ReplyCreate,
    ) {
        let parent_path = match self.get_path(parent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        let child_path = parent_path.join(name);
        let mut opts = fs::OpenOptions::new();
        opts.create(true).write(true).read(true);
        if flags & libc::O_TRUNC != 0 {
            opts.truncate(true);
        }

        match opts.open(&child_path) {
            Ok(file) => {
                let _ = fs::set_permissions(&child_path, fs::Permissions::from_mode(mode));
                match fs::metadata(&child_path) {
                    Ok(meta) => {
                        let ino = self.alloc_ino(child_path);
                        let attr = self.metadata_to_attr(ino, &meta);
                        let fh = self.alloc_fh(file);
                        reply.created(&TTL, &attr, 0, fh, 0);
                    }
                    Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
                }
            }
            Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }

    fn unlink(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        let parent_path = match self.get_path(parent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let child_path = parent_path.join(name);
        match fs::remove_file(&child_path) {
            Ok(_) => reply.ok(),
            Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }

    fn rmdir(&mut self, _req: &Request<'_>, parent: u64, name: &OsStr, reply: ReplyEmpty) {
        let parent_path = match self.get_path(parent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let child_path = parent_path.join(name);
        match fs::remove_dir(&child_path) {
            Ok(_) => reply.ok(),
            Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }

    fn mkdir(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        mode: u32,
        _umask: u32,
        reply: ReplyEntry,
    ) {
        let parent_path = match self.get_path(parent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let child_path = parent_path.join(name);
        match fs::create_dir(&child_path) {
            Ok(_) => {
                let _ = fs::set_permissions(&child_path, fs::Permissions::from_mode(mode));
                match fs::metadata(&child_path) {
                    Ok(meta) => {
                        let ino = self.alloc_ino(child_path);
                        let attr = self.metadata_to_attr(ino, &meta);
                        reply.entry(&TTL, &attr, 0);
                    }
                    Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
                }
            }
            Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }

    fn readdir(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        _fh: u64,
        offset: i64,
        mut reply: ReplyDirectory,
    ) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        let entries = match fs::read_dir(&path) {
            Ok(entries) => entries,
            Err(e) => {
                reply.error(e.raw_os_error().unwrap_or(libc::EIO));
                return;
            }
        };

        let mut result: Vec<(u64, fuser::FileType, String)> = vec![
            (1, fuser::FileType::Directory, ".".to_string()),
            (1, fuser::FileType::Directory, "..".to_string()),
        ];

        for entry in entries.filter_map(|e| e.ok()) {
            let name = entry.file_name().to_string_lossy().to_string();
            let ft = match entry.file_type() {
                Ok(ft) if ft.is_dir() => fuser::FileType::Directory,
                Ok(ft) if ft.is_symlink() => fuser::FileType::Symlink,
                _ => fuser::FileType::RegularFile,
            };
            let ino = self.alloc_ino(entry.path());
            result.push((ino, ft, name));
        }

        for (i, (ino, ft, name)) in result.iter().enumerate().skip(offset as usize) {
            if reply.add(*ino, (i + 1) as i64, *ft, name) {
                break;
            }
        }
        reply.ok();
    }

    fn statfs(&mut self, _req: &Request<'_>, ino: u64, reply: ReplyStatfs) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };

        let mut stat: libc::statvfs = unsafe { std::mem::zeroed() };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let ret = unsafe { libc::statvfs(c_path.as_ptr(), &mut stat) };
        if ret == 0 {
            reply.statfs(
                stat.f_blocks as u64,
                stat.f_bfree as u64,
                stat.f_bavail as u64,
                stat.f_files as u64,
                stat.f_ffree as u64,
                stat.f_bsize as u32,
                stat.f_namemax as u32,
                stat.f_frsize as u32,
            );
        } else {
            reply.error(libc::EIO);
        }
    }

    fn flush(&mut self, _req: &Request<'_>, _ino: u64, fh: u64, _lock_owner: u64, reply: ReplyEmpty) {
        if let Some(handle) = self.handles.get(&fh) {
            let _ = handle.file.sync_all();
        }
        reply.ok();
    }

    fn fsync(&mut self, _req: &Request<'_>, _ino: u64, fh: u64, datasync: bool, reply: ReplyEmpty) {
        if let Some(handle) = self.handles.get(&fh) {
            if datasync {
                let _ = handle.file.sync_data();
            } else {
                let _ = handle.file.sync_all();
            }
        }
        reply.ok();
    }

    fn access(&mut self, _req: &Request<'_>, ino: u64, mask: i32, reply: ReplyEmpty) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let ret = unsafe { libc::access(c_path.as_ptr(), mask) };
        if ret == 0 {
            reply.ok();
        } else {
            reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
        }
    }

    fn rename(
        &mut self,
        _req: &Request<'_>,
        parent: u64,
        name: &OsStr,
        newparent: u64,
        newname: &OsStr,
        _flags: u32,
        reply: ReplyEmpty,
    ) {
        let parent_path = match self.get_path(parent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let newparent_path = match self.get_path(newparent) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        match fs::rename(parent_path.join(name), newparent_path.join(newname)) {
            Ok(_) => reply.ok(),
            Err(e) => reply.error(e.raw_os_error().unwrap_or(libc::EIO)),
        }
    }

    fn getxattr(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        name: &OsStr,
        size: u32,
        reply: ReplyXattr,
    ) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let c_name = std::ffi::CString::new(name.to_string_lossy().as_bytes()).unwrap();

        if size == 0 {
            let ret = unsafe {
                libc::getxattr(c_path.as_ptr(), c_name.as_ptr(), std::ptr::null_mut(), 0)
            };
            if ret >= 0 {
                reply.size(ret as u32);
            } else {
                reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
            }
        } else {
            let mut buf = vec![0u8; size as usize];
            let ret = unsafe {
                libc::getxattr(
                    c_path.as_ptr(),
                    c_name.as_ptr(),
                    buf.as_mut_ptr() as *mut libc::c_void,
                    size as usize,
                )
            };
            if ret >= 0 {
                buf.truncate(ret as usize);
                reply.data(&buf);
            } else {
                reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
            }
        }
    }

    fn listxattr(&mut self, _req: &Request<'_>, ino: u64, size: u32, reply: ReplyXattr) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();

        if size == 0 {
            let ret = unsafe { libc::listxattr(c_path.as_ptr(), std::ptr::null_mut(), 0) };
            if ret >= 0 {
                reply.size(ret as u32);
            } else {
                reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
            }
        } else {
            let mut buf = vec![0u8; size as usize];
            let ret = unsafe {
                libc::listxattr(
                    c_path.as_ptr(),
                    buf.as_mut_ptr() as *mut libc::c_char,
                    size as usize,
                )
            };
            if ret >= 0 {
                buf.truncate(ret as usize);
                reply.data(&buf);
            } else {
                reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
            }
        }
    }

    fn setxattr(
        &mut self,
        _req: &Request<'_>,
        ino: u64,
        name: &OsStr,
        value: &[u8],
        flags: i32,
        _position: u32,
        reply: ReplyEmpty,
    ) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let c_name = std::ffi::CString::new(name.to_string_lossy().as_bytes()).unwrap();

        let ret = unsafe {
            libc::setxattr(
                c_path.as_ptr(),
                c_name.as_ptr(),
                value.as_ptr() as *const libc::c_void,
                value.len(),
                flags,
            )
        };
        if ret == 0 {
            reply.ok();
        } else {
            reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
        }
    }

    fn removexattr(&mut self, _req: &Request<'_>, ino: u64, name: &OsStr, reply: ReplyEmpty) {
        let path = match self.get_path(ino) {
            Some(p) => p,
            None => {
                reply.error(libc::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let c_name = std::ffi::CString::new(name.to_string_lossy().as_bytes()).unwrap();

        let ret = unsafe { libc::removexattr(c_path.as_ptr(), c_name.as_ptr()) };
        if ret == 0 {
            reply.ok();
        } else {
            reply.error(std::io::Error::last_os_error().raw_os_error().unwrap_or(libc::EIO));
        }
    }
}

fn main() -> std::io::Result<()> {
    simple_logger::SimpleLogger::new()
        .with_level(log::LevelFilter::Info)
        .env()
        .init()
        .unwrap();

    let args = Args::parse();

    let src = Path::new(&args.src);
    if !src.exists() {
        fs::create_dir_all(src)?;
    }
    if !src.is_dir() {
        error!("Source {} is not a directory", args.src);
        return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
    }

    let dest = Path::new(&args.dest);
    if !dest.exists() {
        fs::create_dir_all(dest)?;
    }
    if !dest.is_dir() {
        error!("Destination {} is not a directory", args.dest);
        return Err(std::io::Error::from_raw_os_error(libc::EINVAL));
    }

    info!(
        "Starting passthrough-fuser: src={:?} mountpoint={:?} threads={}",
        src, dest, args.threads
    );

    let fs = PassthroughFs::new(src.to_path_buf());

    let options = vec![
        MountOption::FSName("passthrough-fuser".to_string()),
        MountOption::AutoUnmount,
        MountOption::AllowOther,
    ];

    // Use spawn_mount2 for background session — dropping the handle unmounts
    let bg = fuser::spawn_mount2(fs, dest, &options)?;

    // Wait for signal
    let mut signals = Signals::new(TERM_SIGNALS)?;
    for _sig in signals.forever() {
        break;
    }

    info!("Received signal, unmounting...");
    drop(bg);

    Ok(())
}
