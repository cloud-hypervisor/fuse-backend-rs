//! Passthrough filesystem implementation using fuser.
//!
//! This mirrors all operations to a backing directory, providing a baseline
//! for comparing fuser performance against fuse-backend-rs.
//!
//! Uses fuser >= 0.17 APIs: `&self` Filesystem methods (shared state behind
//! locks) and `Config::{n_threads, clone_fd}` for multi-threaded event loops
//! with per-worker FUSE_DEV_IOC_CLONE fds.

use clap::Parser;
use fuser::{
    AccessFlags, BsdFileFlags, Config, Errno, FileAttr, FileHandle, FileType, Filesystem,
    FopenFlags, Generation, INodeNo, KernelConfig, LockOwner, MountOption, OpenFlags, RenameFlags,
    ReplyAttr, ReplyCreate, ReplyData, ReplyDirectory, ReplyEmpty, ReplyEntry, ReplyOpen,
    ReplyStatfs, ReplyWrite, ReplyXattr, Request, SessionACL, TimeOrNow, WriteFlags,
};
use log::{error, info};
use signal_hook::{consts::TERM_SIGNALS, iterator::Signals};
use std::collections::HashMap;
use std::ffi::OsStr;
use std::fs::{self, File};
use std::os::unix::fs::{FileExt, MetadataExt, PermissionsExt};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, RwLock};
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
    /// Number of event loop threads (fuser >= 0.17 Config::n_threads)
    #[arg(short, long, default_value = "1")]
    threads: usize,
    /// Share one dup'ed /dev/fuse fd across event loop threads instead of
    /// giving each thread its own FUSE_DEV_IOC_CLONE fd (Config::clone_fd)
    #[arg(long, default_value_t = false)]
    no_clone_fd: bool,
}

/// Inode data stored per inode number
#[derive(Clone)]
struct InodeData {
    path: PathBuf,
}

/// Passthrough filesystem implementation.
///
/// Shared across event loop threads (`&self` methods), so all mutable state
/// lives behind locks/atomics. File handles are stored as `Arc<File>`: the
/// read/write paths clone the Arc and release the lock before doing I/O, so
/// concurrent pread/pwrite never contend on the handle map.
struct PassthroughFs {
    _source: PathBuf,
    inodes: RwLock<HashMap<u64, InodeData>>,
    next_ino: AtomicU64,
    handles: RwLock<HashMap<u64, Arc<File>>>,
    next_fh: AtomicU64,
}

/// Map a std io error to the fuser Errno reply type
fn errno_of(e: std::io::Error) -> Errno {
    Errno::from_i32(e.raw_os_error().unwrap_or(libc::EIO))
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
            inodes: RwLock::new(inodes),
            next_ino: AtomicU64::new(2),
            handles: RwLock::new(HashMap::new()),
            next_fh: AtomicU64::new(1),
        }
    }

    fn get_path(&self, ino: u64) -> Option<PathBuf> {
        self.inodes
            .read()
            .unwrap()
            .get(&ino)
            .map(|d| d.path.clone())
    }

    fn alloc_ino(&self, path: PathBuf) -> u64 {
        let ino = self.next_ino.fetch_add(1, Ordering::Relaxed);
        self.inodes.write().unwrap().insert(ino, InodeData { path });
        ino
    }

    fn alloc_fh(&self, file: File) -> u64 {
        let fh = self.next_fh.fetch_add(1, Ordering::Relaxed);
        self.handles.write().unwrap().insert(fh, Arc::new(file));
        fh
    }

    fn get_file(&self, fh: u64) -> Option<Arc<File>> {
        self.handles.read().unwrap().get(&fh).cloned()
    }

    fn metadata_to_attr(&self, ino: u64, meta: &fs::Metadata) -> FileAttr {
        FileAttr {
            ino: INodeNo(ino),
            size: meta.len(),
            blocks: meta.blocks(),
            atime: meta.accessed().unwrap_or(SystemTime::UNIX_EPOCH),
            mtime: meta.modified().unwrap_or(SystemTime::UNIX_EPOCH),
            ctime: SystemTime::UNIX_EPOCH,
            crtime: SystemTime::UNIX_EPOCH,
            kind: if meta.is_dir() {
                FileType::Directory
            } else if meta.is_symlink() {
                FileType::Symlink
            } else {
                FileType::RegularFile
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
    fn init(&mut self, _req: &Request, config: &mut KernelConfig) -> std::io::Result<()> {
        // Match fuse-backend-rs INIT: 1MB max write (256 pages). fuser >= 0.17
        // negotiates the ABI at runtime, so the old abi-7-x feature-flag trap
        // (protocol 7.8 fallback splitting writes into 4k) no longer exists,
        // but set max_write explicitly for a like-for-like comparison.
        let _ = config.set_max_write(1024 * 1024);
        info!("Passthrough filesystem initialized");
        Ok(())
    }

    fn destroy(&mut self) {
        info!("Passthrough filesystem destroyed");
    }

    fn lookup(&self, _req: &Request, parent: INodeNo, name: &OsStr, reply: ReplyEntry) {
        let parent_path = match self.get_path(u64::from(parent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };

        let child_path = parent_path.join(name);
        match fs::metadata(&child_path) {
            Ok(meta) => {
                let ino = self.alloc_ino(child_path);
                let attr = self.metadata_to_attr(ino, &meta);
                reply.entry(&TTL, &attr, Generation(0));
            }
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn getattr(&self, _req: &Request, ino: INodeNo, _fh: Option<FileHandle>, reply: ReplyAttr) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };

        match fs::metadata(&path) {
            Ok(meta) => {
                let attr = self.metadata_to_attr(u64::from(ino), &meta);
                reply.attr(&TTL, &attr);
            }
            Err(e) => reply.error(errno_of(e)),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn setattr(
        &self,
        _req: &Request,
        ino: INodeNo,
        mode: Option<u32>,
        _uid: Option<u32>,
        _gid: Option<u32>,
        size: Option<u64>,
        _atime: Option<TimeOrNow>,
        _mtime: Option<TimeOrNow>,
        _ctime: Option<SystemTime>,
        _fh: Option<FileHandle>,
        _crtime: Option<SystemTime>,
        _chgtime: Option<SystemTime>,
        _bkuptime: Option<SystemTime>,
        _flags: Option<BsdFileFlags>,
        reply: ReplyAttr,
    ) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };

        if let Some(size) = size {
            if let Err(e) = fs::OpenOptions::new()
                .write(true)
                .open(&path)
                .and_then(|f| f.set_len(size))
            {
                reply.error(errno_of(e));
                return;
            }
        }

        if let Some(mode) = mode {
            let _ = fs::set_permissions(&path, fs::Permissions::from_mode(mode));
        }

        match fs::metadata(&path) {
            Ok(meta) => {
                let attr = self.metadata_to_attr(u64::from(ino), &meta);
                reply.attr(&TTL, &attr);
            }
            Err(e) => reply.error(errno_of(e)),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn read(
        &self,
        _req: &Request,
        _ino: INodeNo,
        fh: FileHandle,
        offset: u64,
        size: u32,
        _flags: OpenFlags,
        _lock_owner: Option<LockOwner>,
        reply: ReplyData,
    ) {
        if let Some(file) = self.get_file(fh.0) {
            let mut buf = vec![0u8; size as usize];
            // pread: single syscall, no seek (matches fuse-backend-rs read_at path)
            match file.read_at(&mut buf, offset) {
                Ok(n) => {
                    buf.truncate(n);
                    reply.data(&buf);
                }
                Err(e) => reply.error(errno_of(e)),
            }
        } else {
            reply.error(Errno::EBADF);
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn write(
        &self,
        _req: &Request,
        _ino: INodeNo,
        fh: FileHandle,
        offset: u64,
        data: &[u8],
        _write_flags: WriteFlags,
        _flags: OpenFlags,
        _lock_owner: Option<LockOwner>,
        reply: ReplyWrite,
    ) {
        if let Some(file) = self.get_file(fh.0) {
            // pwrite: single syscall, no seek (matches fuse-backend-rs write path)
            match file.write_at(data, offset) {
                Ok(n) => reply.written(n as u32),
                Err(e) => reply.error(errno_of(e)),
            }
        } else {
            reply.error(Errno::EBADF);
        }
    }

    fn open(&self, _req: &Request, ino: INodeNo, flags: OpenFlags, reply: ReplyOpen) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };

        let raw = flags.0;
        let mut opts = fs::OpenOptions::new();
        let access_mode = raw & libc::O_ACCMODE;
        if access_mode == libc::O_RDONLY {
            opts.read(true);
        } else if access_mode == libc::O_WRONLY {
            opts.write(true);
        } else if access_mode == libc::O_RDWR {
            opts.read(true).write(true);
        }
        if raw & libc::O_APPEND != 0 {
            opts.append(true);
        }
        if raw & libc::O_TRUNC != 0 {
            opts.truncate(true);
        }

        match opts.open(&path) {
            Ok(file) => {
                let fh = self.alloc_fh(file);
                reply.opened(FileHandle(fh), FopenFlags::empty());
            }
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn release(
        &self,
        _req: &Request,
        _ino: INodeNo,
        fh: FileHandle,
        _flags: OpenFlags,
        _lock_owner: Option<LockOwner>,
        _flush: bool,
        reply: ReplyEmpty,
    ) {
        self.handles.write().unwrap().remove(&fh.0);
        reply.ok();
    }

    fn create(
        &self,
        _req: &Request,
        parent: INodeNo,
        name: &OsStr,
        mode: u32,
        _umask: u32,
        flags: i32,
        reply: ReplyCreate,
    ) {
        let parent_path = match self.get_path(u64::from(parent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
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
                        reply.created(
                            &TTL,
                            &attr,
                            Generation(0),
                            FileHandle(fh),
                            FopenFlags::empty(),
                        );
                    }
                    Err(e) => reply.error(errno_of(e)),
                }
            }
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn unlink(&self, _req: &Request, parent: INodeNo, name: &OsStr, reply: ReplyEmpty) {
        let parent_path = match self.get_path(u64::from(parent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        let child_path = parent_path.join(name);
        match fs::remove_file(&child_path) {
            Ok(_) => reply.ok(),
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn rmdir(&self, _req: &Request, parent: INodeNo, name: &OsStr, reply: ReplyEmpty) {
        let parent_path = match self.get_path(u64::from(parent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        let child_path = parent_path.join(name);
        match fs::remove_dir(&child_path) {
            Ok(_) => reply.ok(),
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn mkdir(
        &self,
        _req: &Request,
        parent: INodeNo,
        name: &OsStr,
        mode: u32,
        _umask: u32,
        reply: ReplyEntry,
    ) {
        let parent_path = match self.get_path(u64::from(parent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
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
                        reply.entry(&TTL, &attr, Generation(0));
                    }
                    Err(e) => reply.error(errno_of(e)),
                }
            }
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn readdir(
        &self,
        _req: &Request,
        ino: INodeNo,
        _fh: FileHandle,
        offset: u64,
        mut reply: ReplyDirectory,
    ) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };

        let entries = match fs::read_dir(&path) {
            Ok(entries) => entries,
            Err(e) => {
                reply.error(errno_of(e));
                return;
            }
        };

        let mut result: Vec<(u64, FileType, String)> = vec![
            (1, FileType::Directory, ".".to_string()),
            (1, FileType::Directory, "..".to_string()),
        ];

        for entry in entries.filter_map(|e| e.ok()) {
            let name = entry.file_name().to_string_lossy().to_string();
            let ft = match entry.file_type() {
                Ok(ft) if ft.is_dir() => FileType::Directory,
                Ok(ft) if ft.is_symlink() => FileType::Symlink,
                _ => FileType::RegularFile,
            };
            let ino = self.alloc_ino(entry.path());
            result.push((ino, ft, name));
        }

        for (i, (ino, ft, name)) in result.iter().enumerate().skip(offset as usize) {
            if reply.add(INodeNo(*ino), (i + 1) as u64, *ft, name) {
                break;
            }
        }
        reply.ok();
    }

    fn statfs(&self, _req: &Request, ino: INodeNo, reply: ReplyStatfs) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };

        let mut stat: libc::statvfs = unsafe { std::mem::zeroed() };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let ret = unsafe { libc::statvfs(c_path.as_ptr(), &mut stat) };
        if ret == 0 {
            reply.statfs(
                stat.f_blocks,
                stat.f_bfree,
                stat.f_bavail,
                stat.f_files,
                stat.f_ffree,
                stat.f_bsize as u32,
                stat.f_namemax as u32,
                stat.f_frsize as u32,
            );
        } else {
            reply.error(Errno::EIO);
        }
    }

    fn flush(
        &self,
        _req: &Request,
        _ino: INodeNo,
        fh: FileHandle,
        _lock_owner: LockOwner,
        reply: ReplyEmpty,
    ) {
        if let Some(file) = self.get_file(fh.0) {
            let _ = file.sync_all();
        }
        reply.ok();
    }

    fn fsync(
        &self,
        _req: &Request,
        _ino: INodeNo,
        fh: FileHandle,
        datasync: bool,
        reply: ReplyEmpty,
    ) {
        if let Some(file) = self.get_file(fh.0) {
            if datasync {
                let _ = file.sync_data();
            } else {
                let _ = file.sync_all();
            }
        }
        reply.ok();
    }

    fn access(&self, _req: &Request, ino: INodeNo, mask: AccessFlags, reply: ReplyEmpty) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let ret = unsafe { libc::access(c_path.as_ptr(), mask.bits()) };
        if ret == 0 {
            reply.ok();
        } else {
            reply.error(errno_of(std::io::Error::last_os_error()));
        }
    }

    fn rename(
        &self,
        _req: &Request,
        parent: INodeNo,
        name: &OsStr,
        newparent: INodeNo,
        newname: &OsStr,
        _flags: RenameFlags,
        reply: ReplyEmpty,
    ) {
        let parent_path = match self.get_path(u64::from(parent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        let newparent_path = match self.get_path(u64::from(newparent)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        match fs::rename(parent_path.join(name), newparent_path.join(newname)) {
            Ok(_) => reply.ok(),
            Err(e) => reply.error(errno_of(e)),
        }
    }

    fn getxattr(&self, _req: &Request, ino: INodeNo, name: &OsStr, size: u32, reply: ReplyXattr) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
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
                reply.error(errno_of(std::io::Error::last_os_error()));
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
                reply.error(errno_of(std::io::Error::last_os_error()));
            }
        }
    }

    fn listxattr(&self, _req: &Request, ino: INodeNo, size: u32, reply: ReplyXattr) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();

        if size == 0 {
            let ret = unsafe { libc::listxattr(c_path.as_ptr(), std::ptr::null_mut(), 0) };
            if ret >= 0 {
                reply.size(ret as u32);
            } else {
                reply.error(errno_of(std::io::Error::last_os_error()));
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
                reply.error(errno_of(std::io::Error::last_os_error()));
            }
        }
    }

    fn setxattr(
        &self,
        _req: &Request,
        ino: INodeNo,
        name: &OsStr,
        value: &[u8],
        flags: i32,
        _position: u32,
        reply: ReplyEmpty,
    ) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
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
            reply.error(errno_of(std::io::Error::last_os_error()));
        }
    }

    fn removexattr(&self, _req: &Request, ino: INodeNo, name: &OsStr, reply: ReplyEmpty) {
        let path = match self.get_path(u64::from(ino)) {
            Some(p) => p,
            None => {
                reply.error(Errno::ENOENT);
                return;
            }
        };
        let c_path = std::ffi::CString::new(path.to_string_lossy().as_bytes()).unwrap();
        let c_name = std::ffi::CString::new(name.to_string_lossy().as_bytes()).unwrap();

        let ret = unsafe { libc::removexattr(c_path.as_ptr(), c_name.as_ptr()) };
        if ret == 0 {
            reply.ok();
        } else {
            reply.error(errno_of(std::io::Error::last_os_error()));
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
        "Starting passthrough-fuser: src={:?} mountpoint={:?} threads={} clone_fd={}",
        src, dest, args.threads, !args.no_clone_fd
    );

    let fs = PassthroughFs::new(src.to_path_buf());

    // Config is #[non_exhaustive]: start from Default and assign the pub fields.
    // SessionACL::All corresponds to allow_other, which AutoUnmount requires.
    let mut config = Config::default();
    config.mount_options = vec![
        MountOption::FSName("passthrough-fuser".to_string()),
        MountOption::AutoUnmount,
    ];
    config.acl = SessionACL::All;
    config.n_threads = Some(args.threads);
    config.clone_fd = !args.no_clone_fd;

    // Background session — dropping the handle unmounts
    let bg = fuser::spawn_mount(fs, dest, &config)?;

    // Wait for signal
    let mut signals = Signals::new(TERM_SIGNALS)?;
    let _sig = signals.forever().next();

    info!("Received signal, unmounting...");
    drop(bg);

    Ok(())
}
