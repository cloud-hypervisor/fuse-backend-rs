// Copyright 2026 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0

//! A file system that forwards to the benchmark's `Vfs` and waits before
//! each LOOKUP and READ, to stand in for a backend that waits on a remote
//! store. The synchronous handlers block their thread for the delay, and
//! the asynchronous ones sleep without blocking it, so a transport that
//! keeps several requests in flight overlaps the waits.
//!
//! It forwards the requests the benchmark workloads send. The other
//! synchronous handlers keep the `ENOSYS` defaults, and the other
//! asynchronous ones call the synchronous handlers.

use std::ffi::CStr;
use std::io;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd};
use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;
use tokio::io::unix::AsyncFd;
use tokio::io::Interest;

use fuse_backend_rs::abi::fuse_abi::{
    stat64, statvfs64, CreateIn, FsOptions, OpenOptions, SetattrValid,
};
use fuse_backend_rs::api::filesystem::{
    AsyncFileSystem, AsyncZeroCopyReader, AsyncZeroCopyWriter, Context, DirEntry, Entry,
    FileSystem, ZeroCopyReader, ZeroCopyWriter,
};
use fuse_backend_rs::api::Vfs;

pub struct DelayFs {
    inner: Arc<Vfs>,
    delay: Duration,
}

impl DelayFs {
    pub fn new(inner: Arc<Vfs>, delay: Duration) -> Self {
        DelayFs { inner, delay }
    }

    fn wait(&self) {
        std::thread::sleep(self.delay);
    }

    async fn async_wait(&self) {
        if let Err(e) = timerfd_sleep(self.delay).await {
            static WARNED: std::sync::Once = std::sync::Once::new();
            WARNED.call_once(|| {
                log::warn!("timerfd delay failed, async delays round up to whole ms: {e}");
            });
            tokio::time::sleep(self.delay).await;
        }
    }
}

/// Wait `delay` on a timerfd. tokio's timer rounds a deadline up to the next
/// millisecond, so a 1 ms sleep takes about 2 ms there, while a timerfd
/// waits about as long as `std::thread::sleep()` in the sync handlers.
async fn timerfd_sleep(delay: Duration) -> io::Result<()> {
    // SAFETY: timerfd_create() takes no pointers.
    let fd = unsafe {
        libc::timerfd_create(
            libc::CLOCK_MONOTONIC,
            libc::TFD_NONBLOCK | libc::TFD_CLOEXEC,
        )
    };
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: timerfd_create() returned a new fd that nothing else owns.
    let fd = unsafe { OwnedFd::from_raw_fd(fd) };
    let spec = libc::itimerspec {
        it_interval: libc::timespec {
            tv_sec: 0,
            tv_nsec: 0,
        },
        it_value: libc::timespec {
            tv_sec: delay.as_secs() as libc::time_t,
            tv_nsec: delay.subsec_nanos() as libc::c_long,
        },
    };
    // SAFETY: `fd` is a timerfd and `spec` lives for the call.
    if unsafe { libc::timerfd_settime(fd.as_raw_fd(), 0, &spec, std::ptr::null_mut()) } < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: `fd` is dropped after `ready`, so it outlives the registration.
    let ready = unsafe { AsyncFd::register_with_interest(fd.as_raw_fd(), Interest::READABLE) }?;
    let _expired = ready.readable().await?;
    Ok(())
}

type Inode = <Vfs as FileSystem>::Inode;
type Handle = <Vfs as FileSystem>::Handle;

impl FileSystem for DelayFs {
    type Inode = Inode;
    type Handle = Handle;

    fn init(&self, capable: FsOptions) -> io::Result<FsOptions> {
        self.inner.init(capable)
    }

    fn destroy(&self) {
        self.inner.destroy()
    }

    fn lookup(&self, ctx: &Context, parent: Inode, name: &CStr) -> io::Result<Entry> {
        self.wait();
        self.inner.lookup(ctx, parent, name)
    }

    fn forget(&self, ctx: &Context, inode: Inode, count: u64) {
        self.inner.forget(ctx, inode, count)
    }

    fn batch_forget(&self, ctx: &Context, requests: Vec<(Inode, u64)>) {
        self.inner.batch_forget(ctx, requests)
    }

    fn getattr(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Option<Handle>,
    ) -> io::Result<(stat64, Duration)> {
        self.inner.getattr(ctx, inode, handle)
    }

    fn setattr(
        &self,
        ctx: &Context,
        inode: Inode,
        attr: stat64,
        handle: Option<Handle>,
        valid: SetattrValid,
    ) -> io::Result<(stat64, Duration)> {
        self.inner.setattr(ctx, inode, attr, handle, valid)
    }

    fn open(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions, Option<u32>)> {
        self.inner.open(ctx, inode, flags, fuse_flags)
    }

    #[allow(clippy::too_many_arguments)]
    fn release(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
        handle: Handle,
        flush: bool,
        flock_release: bool,
        lock_owner: Option<u64>,
    ) -> io::Result<()> {
        self.inner
            .release(ctx, inode, flags, handle, flush, flock_release, lock_owner)
    }

    fn create(
        &self,
        ctx: &Context,
        parent: Inode,
        name: &CStr,
        args: CreateIn,
    ) -> io::Result<(Entry, Option<Handle>, OpenOptions, Option<u32>)> {
        self.inner.create(ctx, parent, name, args)
    }

    #[allow(clippy::too_many_arguments)]
    fn read(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        w: &mut dyn ZeroCopyWriter,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> io::Result<usize> {
        self.wait();
        self.inner
            .read(ctx, inode, handle, w, size, offset, lock_owner, flags)
    }

    #[allow(clippy::too_many_arguments)]
    fn write(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        r: &mut dyn ZeroCopyReader,
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<usize> {
        self.inner.write(
            ctx,
            inode,
            handle,
            r,
            size,
            offset,
            lock_owner,
            delayed_write,
            flags,
            fuse_flags,
        )
    }

    fn flush(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        lock_owner: u64,
    ) -> io::Result<()> {
        self.inner.flush(ctx, inode, handle, lock_owner)
    }

    fn fsync(&self, ctx: &Context, inode: Inode, datasync: bool, handle: Handle) -> io::Result<()> {
        self.inner.fsync(ctx, inode, datasync, handle)
    }

    fn fallocate(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> io::Result<()> {
        self.inner
            .fallocate(ctx, inode, handle, mode, offset, length)
    }

    fn statfs(&self, ctx: &Context, inode: Inode) -> io::Result<statvfs64> {
        self.inner.statfs(ctx, inode)
    }

    fn unlink(&self, ctx: &Context, parent: Inode, name: &CStr) -> io::Result<()> {
        self.inner.unlink(ctx, parent, name)
    }

    fn access(&self, ctx: &Context, inode: Inode, mask: u32) -> io::Result<()> {
        self.inner.access(ctx, inode, mask)
    }

    fn opendir(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions)> {
        self.inner.opendir(ctx, inode, flags)
    }

    fn readdir(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry) -> io::Result<usize>,
    ) -> io::Result<()> {
        self.inner
            .readdir(ctx, inode, handle, size, offset, add_entry)
    }

    fn readdirplus(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, Entry) -> io::Result<usize>,
    ) -> io::Result<()> {
        self.inner
            .readdirplus(ctx, inode, handle, size, offset, add_entry)
    }

    fn releasedir(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
        handle: Handle,
    ) -> io::Result<()> {
        self.inner.releasedir(ctx, inode, flags, handle)
    }
}

#[async_trait]
impl AsyncFileSystem for DelayFs {
    async fn async_lookup(&self, ctx: &Context, parent: Inode, name: &CStr) -> io::Result<Entry> {
        self.async_wait().await;
        self.inner.async_lookup(ctx, parent, name).await
    }

    async fn async_getattr(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Option<Handle>,
    ) -> io::Result<(stat64, Duration)> {
        self.inner.async_getattr(ctx, inode, handle).await
    }

    async fn async_setattr(
        &self,
        ctx: &Context,
        inode: Inode,
        attr: stat64,
        handle: Option<Handle>,
        valid: SetattrValid,
    ) -> io::Result<(stat64, Duration)> {
        self.inner
            .async_setattr(ctx, inode, attr, handle, valid)
            .await
    }

    async fn async_open(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions, Option<u32>)> {
        self.inner.async_open(ctx, inode, flags, fuse_flags).await
    }

    async fn async_create(
        &self,
        ctx: &Context,
        parent: Inode,
        name: &CStr,
        args: CreateIn,
    ) -> io::Result<(Entry, Option<Handle>, OpenOptions, Option<u32>)> {
        self.inner.async_create(ctx, parent, name, args).await
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_read(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        w: &mut (dyn AsyncZeroCopyWriter + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> io::Result<usize> {
        self.async_wait().await;
        self.inner
            .async_read(ctx, inode, handle, w, size, offset, lock_owner, flags)
            .await
    }

    #[allow(clippy::too_many_arguments)]
    async fn async_write(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        r: &mut (dyn AsyncZeroCopyReader + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> io::Result<usize> {
        self.inner
            .async_write(
                ctx,
                inode,
                handle,
                r,
                size,
                offset,
                lock_owner,
                delayed_write,
                flags,
                fuse_flags,
            )
            .await
    }

    async fn async_fsync(
        &self,
        ctx: &Context,
        inode: Inode,
        datasync: bool,
        handle: Handle,
    ) -> io::Result<()> {
        self.inner.async_fsync(ctx, inode, datasync, handle).await
    }

    async fn async_fallocate(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> io::Result<()> {
        self.inner
            .async_fallocate(ctx, inode, handle, mode, offset, length)
            .await
    }

    async fn async_opendir(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
    ) -> io::Result<(Option<Handle>, OpenOptions)> {
        self.inner.async_opendir(ctx, inode, flags).await
    }

    async fn async_readdir(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut (dyn FnMut(DirEntry) -> io::Result<usize> + Send),
    ) -> io::Result<()> {
        self.inner
            .async_readdir(ctx, inode, handle, size, offset, add_entry)
            .await
    }

    async fn async_readdirplus(
        &self,
        ctx: &Context,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut (dyn FnMut(DirEntry, Entry) -> io::Result<usize> + Send),
    ) -> io::Result<()> {
        self.inner
            .async_readdirplus(ctx, inode, handle, size, offset, add_entry)
            .await
    }

    async fn async_releasedir(
        &self,
        ctx: &Context,
        inode: Inode,
        flags: u32,
        handle: Handle,
    ) -> io::Result<()> {
        self.inner.async_releasedir(ctx, inode, flags, handle).await
    }
}
