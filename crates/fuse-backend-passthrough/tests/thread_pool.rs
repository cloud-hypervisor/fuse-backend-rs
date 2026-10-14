// SPDX-License-Identifier: Apache-2.0

//! `PassthroughFs` serves READ and WRITE on the tokio runtime, with and without the blocking
//! thread pool. The crate fixes the runtime type once per process, so these tests run in a binary
//! of their own.

#![cfg(feature = "async-io")]

use std::ffi::CString;
use std::future::Future;
use std::io;
use std::pin::Pin;
use std::sync::mpsc::channel;
use std::sync::Arc;
use std::task::Poll;

use async_trait::async_trait;
use fuse_backend_core::abi::fuse_abi::{ROOT_ID, WRITE_KILL_PRIV};
use fuse_backend_core::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, FileSystem, FsOptions,
    ZeroCopyReader, ZeroCopyWriter,
};
use fuse_backend_core::async_runtime::{self, RuntimeType};
use fuse_backend_core::file_buf::{FileVolatileBuf, FileVolatileSlice};
use fuse_backend_core::file_traits::{AsyncFileReadWriteVolatile, FileReadWriteVolatile};
use fuse_backend_passthrough::{Config, PassthroughFs};
use vmm_sys_util::tempdir::TempDir;

/// A reply buffer. `write_from()` serves the first `inline` bytes of `source` like a page cache
/// would, and then fails with `EAGAIN` like a cache miss. `native` records whether the native
/// asynchronous path served a part.
struct ReplyBuf {
    source: Vec<u8>,
    inline: usize,
    data: Vec<u8>,
    native: bool,
}

impl ReplyBuf {
    fn new(source: &[u8], inline: usize) -> Self {
        ReplyBuf {
            source: source.to_vec(),
            inline,
            data: Vec::new(),
            native: false,
        }
    }
}

impl io::Write for ReplyBuf {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.data.extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl ZeroCopyWriter for ReplyBuf {
    fn write_from(
        &mut self,
        _f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let start = std::cmp::min(off as usize, self.source.len());
        let n = std::cmp::min(count, self.source.len() - start);
        if n > 0 && self.inline == 0 {
            return Err(io::Error::from_raw_os_error(libc::EAGAIN));
        }
        let n = std::cmp::min(n, self.inline);
        self.inline -= n;
        self.data.extend_from_slice(&self.source[start..start + n]);
        Ok(n)
    }

    fn available_bytes(&self) -> usize {
        usize::MAX
    }
}

#[async_trait(?Send)]
impl AsyncZeroCopyWriter for ReplyBuf {
    async fn async_write_from(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.native = true;
        let mut buf = vec![0u8; count];
        // Safe because `vbuf` doesn't outlive `buf`.
        let vbuf = unsafe { FileVolatileBuf::from_raw_ptr(buf.as_mut_ptr(), 0, count) };
        let (res, _) = f.async_read_at_volatile(vbuf, off).await;
        let n = res?;
        self.data.extend_from_slice(&buf[..n]);
        Ok(n)
    }
}

/// The payload of a WRITE. `native` records whether the native asynchronous path wrote it.
struct Payload {
    data: Vec<u8>,
    pos: usize,
    native: bool,
}

impl Payload {
    fn new(data: &[u8]) -> Self {
        Payload {
            data: data.to_vec(),
            pos: 0,
            native: false,
        }
    }
}

impl io::Read for Payload {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let n = std::cmp::min(buf.len(), self.data.len() - self.pos);
        buf[..n].copy_from_slice(&self.data[self.pos..self.pos + n]);
        self.pos += n;
        Ok(n)
    }
}

impl ZeroCopyReader for Payload {
    fn read_to(
        &mut self,
        f: &mut dyn FileReadWriteVolatile,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        let n = std::cmp::min(count, self.data.len() - self.pos);
        // Safe because the slice doesn't outlive `self.data`.
        let slice =
            unsafe { FileVolatileSlice::from_raw_ptr(self.data[self.pos..].as_mut_ptr(), n) };
        let n = f.write_at_volatile(slice, off)?;
        self.pos += n;
        Ok(n)
    }
}

#[async_trait(?Send)]
impl AsyncZeroCopyReader for Payload {
    async fn async_read_to(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize> {
        self.native = true;
        let n = std::cmp::min(count, self.data.len() - self.pos);
        // Safe because `vbuf` doesn't outlive `self.data`.
        let vbuf =
            unsafe { FileVolatileBuf::from_raw_ptr(self.data[self.pos..].as_mut_ptr(), n, n) };
        let (res, _) = f.async_write_at_volatile(vbuf, off).await;
        let n = res?;
        self.pos += n;
        Ok(n)
    }
}

fn context() -> Context {
    Context {
        uid: unsafe { libc::getuid() },
        gid: unsafe { libc::getgid() },
        pid: unsafe { libc::getpid() },
        ..Default::default()
    }
}

/// A shared file system over a new directory holding `file` with `content`, and a handle of the
/// file opened with `flags`.
fn setup(
    content: &[u8],
    options: FsOptions,
    flags: u32,
) -> (Arc<PassthroughFs<()>>, TempDir, u64, u64) {
    async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();
    let dir = TempDir::new().unwrap();
    std::fs::write(dir.as_path().join("file"), content).unwrap();
    let fs = PassthroughFs::<()>::new_shared(Config {
        root_dir: dir.as_path().to_str().unwrap().to_string(),
        // Negotiating HANDLE_KILLPRIV_V2 needs `do_import: false`.
        do_import: false,
        ..Default::default()
    })
    .unwrap();
    fs.import().unwrap();
    fs.init(options).unwrap();
    let ctx = context();
    let inode = fs
        .lookup(&ctx, ROOT_ID, &CString::new("file").unwrap())
        .unwrap()
        .inode;
    let handle = fs.open(&ctx, inode, flags, 0).unwrap().0.unwrap();
    (fs, dir, inode, handle)
}

fn pattern(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i % 251) as u8).collect()
}

/// Poll `future` once.
async fn poll_once<F: Future + Unpin>(future: &mut F) -> Poll<F::Output> {
    std::future::poll_fn(|cx| Poll::Ready(Pin::new(&mut *future).poll(cx))).await
}

#[test]
fn test_read_cache_misses() {
    let content = pattern(100_000);
    let flags = libc::O_RDONLY as u32;
    let (fs, _dir, inode, handle) = setup(&content, FsOptions::empty(), flags);
    let ctx = context();

    for pool in [false, true] {
        fs.enable_async_thread_pool(pool);
        // The inline attempt serves nothing, a part, or everything, and the rest continues
        // where it stopped.
        for inline in [0, 3, 70_000, 100_000] {
            let mut w = ReplyBuf::new(&content, inline);
            // The request reaches past the end of the file.
            let n = async_runtime::block_on(
                fs.async_read(&ctx, inode, handle, &mut w, 150_000, 0, None, flags),
            )
            .unwrap();
            assert_eq!(n, content.len());
            assert!(w.data == content, "pool {} inline {}", pool, inline);
            // The pool serves the misses instead of the native path.
            assert_eq!(w.native, !pool && inline < content.len());
        }

        let mut w = ReplyBuf::new(&content, 0);
        let n = async_runtime::block_on(
            fs.async_read(&ctx, inode, handle, &mut w, 4096, 99_000, None, flags),
        )
        .unwrap();
        assert_eq!(n, 1000);
        assert_eq!(w.data, &content[99_000..]);
    }
}

#[test]
fn test_writes() {
    let flags = libc::O_RDWR as u32;
    let (fs, dir, inode, handle) = setup(b"", FsOptions::empty(), flags);
    let ctx = context();
    let path = dir.as_path().join("file");

    for pool in [false, true] {
        fs.enable_async_thread_pool(pool);
        std::fs::write(&path, b"").unwrap();
        let payload = pattern(100_000);
        let mut r = Payload::new(&payload);
        let n = async_runtime::block_on(fs.async_write(
            &ctx, inode, handle, &mut r, 100_000, 10, None, false, flags, 0,
        ))
        .unwrap();
        assert_eq!(n, payload.len());
        assert_eq!(r.native, !pool);
        let written = std::fs::read(&path).unwrap();
        assert_eq!(&written[..10], &[0u8; 10]);
        assert!(written[10..] == payload[..], "pool {}", pool);
    }
}

/// A WRITE_KILL_PRIV write runs the synchronous handler, on a pool thread with the pool enabled.
#[test]
fn test_kill_priv_writes() {
    let flags = libc::O_RDWR as u32;
    let (fs, dir, inode, handle) = setup(b"", FsOptions::HANDLE_KILLPRIV_V2, flags);
    let ctx = context();

    for pool in [false, true] {
        fs.enable_async_thread_pool(pool);
        let payload = pattern(5000);
        let mut r = Payload::new(&payload);
        let n = async_runtime::block_on(fs.async_write(
            &ctx,
            inode,
            handle,
            &mut r,
            5000,
            0,
            None,
            false,
            flags,
            WRITE_KILL_PRIV,
        ))
        .unwrap();
        assert_eq!(n, payload.len());
        assert!(!r.native);
        assert_eq!(std::fs::read(dir.as_path().join("file")).unwrap(), payload);
    }
}

/// Run `test` on a runtime whose blocking thread pool has one thread, which another task holds
/// until `test` completes. So requests offloaded to the pool wait in its queue until then.
fn with_busy_pool<F: Future<Output = ()>>(test: F) {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .max_blocking_threads(1)
        .build()
        .unwrap();
    rt.block_on(async {
        let (release, wait) = channel::<()>();
        let blocker = tokio::task::spawn_blocking(move || wait.recv());
        test.await;
        release.send(()).unwrap();
        blocker.await.unwrap().unwrap();
        // The pool thread runs its queue in order, so the requests that `test` left there are
        // done once this task completes.
        tokio::task::spawn_blocking(|| ()).await.unwrap();
    });
}

/// While a READ waits for the pool, the runtime thread serves other requests. Dropping the READ
/// returns right away, and nothing writes to the reply buffer of the dropped request.
#[test]
fn test_dropped_read() {
    let content = pattern(100_000);
    let flags = libc::O_RDONLY as u32;
    let (fs, _dir, inode, handle) = setup(&content, FsOptions::empty(), flags);
    fs.enable_async_thread_pool(true);
    let ctx = context();

    let mut w = ReplyBuf::new(&content, 0);
    with_busy_pool(async {
        let mut read =
            Box::pin(fs.async_read(&ctx, inode, handle, &mut w, 100_000, 0, None, flags));
        assert!(poll_once(&mut read).await.is_pending());

        // A READ the page cache serves completes while the first one waits.
        let mut cached = ReplyBuf::new(&content, usize::MAX);
        let n = fs
            .async_read(&ctx, inode, handle, &mut cached, 10, 5, None, flags)
            .await
            .unwrap();
        assert_eq!(n, 10);
        assert_eq!(cached.data, &content[5..15]);

        drop(read);
    });
    // No pool thread had started the dropped READ, so it never ran.
    assert!(w.data.is_empty());
    assert!(!w.native);
}

/// A WRITE dropped before a pool thread starts it doesn't run. The kernel sends it again after a
/// takeover, so a late run could overwrite a newer write to the same range.
#[test]
fn test_dropped_write() {
    let flags = libc::O_RDWR as u32;
    let (fs, dir, inode, handle) = setup(b"", FsOptions::empty(), flags);
    fs.enable_async_thread_pool(true);
    let ctx = context();
    let path = dir.as_path().join("file");

    let mut r = Payload::new(b"old");
    with_busy_pool(async {
        let mut write =
            Box::pin(fs.async_write(&ctx, inode, handle, &mut r, 3, 0, None, false, flags, 0));
        assert!(poll_once(&mut write).await.is_pending());
        drop(write);
        // A newer write to the same range, like the one a new server serves after a takeover.
        std::fs::write(&path, b"new").unwrap();
    });
    assert_eq!(std::fs::read(&path).unwrap(), b"new");
}
