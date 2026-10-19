// Copyright (C) 2021-2022 Alibaba Cloud. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::ffi::CStr;
use std::future::Future;
use std::io;
use std::ops::Deref;
use std::pin::Pin;
use std::sync::Arc;
use std::time::Duration;

use async_trait::async_trait;

use super::{Context, DirEntry, Entry, FileSystem, ZeroCopyReader, ZeroCopyWriter};
use crate::abi::fuse_abi::{stat64, CreateIn, OpenOptions, SetattrValid};
use crate::file_traits::AsyncFileReadWriteVolatile;

/// A trait for directly copying data from the fuse transport into a `File` without first storing it
/// in an intermediate buffer in asynchronous mode.
#[async_trait(?Send)]
pub trait AsyncZeroCopyReader: ZeroCopyReader {
    /// Copies at most `count` bytes from `self` directly into `f` at offset `off` without storing
    /// it in any intermediate buffers. If the return value is `Ok(n)` then it must be guaranteed
    /// that `0 <= n <= count`. If `n` is `0`, then it can indicate one of 3 possibilities:
    ///
    /// 1. There is no more data left in `self`.
    /// 2. There is no more space in `f`.
    /// 3. `count` was `0`.
    ///
    /// # Errors
    ///
    /// If any error is returned then the implementation must guarantee that no bytes were copied
    /// from `self`. If the underlying write to `f` returns `0` then the implementation must return
    /// an error of the kind `io::ErrorKind::WriteZero`.
    async fn async_read_to(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize>;
}

/// A trait for directly copying data from a `RawFd` into the fuse transport without first storing
/// it in an intermediate buffer in asynchronous mode.
#[async_trait(?Send)]
pub trait AsyncZeroCopyWriter: ZeroCopyWriter {
    /// Copies at most `count` bytes from `f` at offset `off` directly into `self` without storing
    /// it in any intermediate buffers. If the return value is `Ok(n)` then it must be guaranteed
    /// that `0 <= n <= count`. If `n` is `0`, then it can indicate one of 3 possibilities:
    ///
    /// 1. There is no more data left in `f`.
    /// 2. There is no more space in `self`.
    /// 3. `count` was `0`.
    ///
    /// # Errors
    ///
    /// If any error is returned then the implementation must guarantee that no bytes were copied
    /// from `f`. If the underlying read from `f` returns `0` then the implementation must return an
    /// error of the kind `io::ErrorKind::UnexpectedEof`.
    async fn async_write_from(
        &mut self,
        f: Arc<dyn AsyncFileReadWriteVolatile>,
        count: usize,
        off: u64,
    ) -> io::Result<usize>;
}

/// The main trait that connects a file system with a transport with asynchronous IO.
///
/// Each method defaults to calling its [`FileSystem`] counterpart, which blocks the thread
/// serving the request until the handler returns. Override the methods that wait on IO, so the
/// thread can serve other requests in the meantime.
///
/// A default method calls the sync handler as soon as it is called, not when its future is
/// polled, so the handler runs even if the caller drops the future without polling it. The
/// handler runs on an async runtime thread, inside the runtime's context. Blocking on a tokio
/// runtime there, for example with `Handle::block_on()`, panics. The `async_open()` and
/// `async_create()` defaults drop the passthrough id that `open()` and `create()` return,
/// because the asynchronous replies have no field for it.
#[allow(unused_variables)]
#[async_trait]
pub trait AsyncFileSystem: FileSystem {
    /// Look up a directory entry by name and get its attributes.
    ///
    /// If this call is successful then the lookup count of the `Inode` associated with the returned
    /// `Entry` must be increased by 1.
    fn async_lookup<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        parent: Self::Inode,
        name: &'c CStr,
    ) -> Pin<Box<dyn Future<Output = io::Result<Entry>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(self.lookup(ctx, parent, name)))
    }

    /*
    /// Forget about an inode.
    ///
    /// Called when the kernel removes an inode from its internal caches. `count` indicates the
    /// amount by which the lookup count for the inode should be decreased. If reducing the lookup
    /// count by `count` causes it to go to zero, then the implementation may delete the `Inode`.
    async fn async_forget(&self, ctx: Context, inode: Self::Inode, count: u64);

    /// Forget about multiple inodes.
    ///
    /// `requests` is a vector of `(inode, count)` pairs. See the documentation for `forget` for
    /// more information.
    async fn async_batch_forget(&self, ctx: Context, requests: Vec<(Self::Inode, u64)>);
     */

    /// Get attributes for a file / directory.
    ///
    /// If `handle` is not `None`, then it contains the handle previously returned by the
    /// implementation after a call to `open` or `opendir`. However, implementations should still
    /// take care to verify the handle if they do not trust the client (e.g., virtio-fs).
    ///
    /// If writeback caching is enabled (`FsOptions::WRITEBACK_CACHE`), then the kernel module
    /// likely has a better idea of the length of the file than the file system (for
    /// example, if there was a write that extended the size of the file but has not yet been
    /// flushed). In this case, the `st_size` field of the returned struct is ignored.
    ///
    /// The returned `Duration` indicates how long the returned attributes should be considered
    /// valid by the client. If the attributes are only changed via the FUSE kernel module (i.e.,
    /// the kernel module has exclusive access), then this should be a very large value.
    fn async_getattr<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Option<Self::Handle>,
    ) -> Pin<AttrFuture<'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(self.getattr(ctx, inode, handle)))
    }

    /// Set attributes for a file / directory.
    ///
    /// If `handle` is not `None`, then it contains the handle previously returned by the
    /// implementation after a call to `open` or `opendir`. However, implementations should still
    /// take care to verify the handle if they do not trust the client (e.g., virtio-fs).
    ///
    /// The `valid` parameter indicates the fields of `attr` that may be considered valid and should
    /// be set by the file system. The content of all other fields in `attr` is undefined.
    ///
    /// If the `FsOptions::HANDLE_KILLPRIV` was set during `init`, then the implementation is
    /// expected to reset the setuid and setgid bits if the file size or owner is being changed.
    ///
    /// This method returns the new attributes after making the modifications requested by the
    /// client. The returned `Duration` indicates how long the returned attributes should be
    /// considered valid by the client. If the attributes are only changed via the FUSE kernel
    /// module (i.e., the kernel module has exclusive access), then this should be a very large
    /// value.
    fn async_setattr<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        attr: stat64,
        handle: Option<Self::Handle>,
        valid: SetattrValid,
    ) -> Pin<AttrFuture<'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.setattr(ctx, inode, attr, handle, valid),
        ))
    }

    /*
        /// Read a symbolic link.
        fn readlink(&self, ctx: Context, inode: Self::Inode) -> io::Result<Vec<u8>> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Create a symbolic link.
        ///
        /// The file system must create a symbolic link named `name` in the directory represented by
        /// `parent`, which contains the string `linkname`. Returns an `Entry` for the newly created
        /// symlink.
        ///
        /// If this call is successful then the lookup count of the `Inode` associated with the returned
        /// `Entry` must be increased by 1.
        fn symlink(
            &self,
            ctx: Context,
            linkname: &CStr,
            parent: Self::Inode,
            name: &CStr,
        ) -> io::Result<Entry> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Create a file node.
        ///
        /// Create a regular file, character device, block device, fifo, or socket node named `name` in
        /// the directory represented by `inode`. Valid values for `mode` and `rdev` are the same as
        /// those accepted by the `mknod(2)` system call. Returns an `Entry` for the newly created node.
        ///
        /// When the `FsOptions::DONT_MASK` feature is set, the file system is responsible for setting
        /// the permissions of the created node to `mode & !umask`.
        ///
        /// If this call is successful then the lookup count of the `Inode` associated with the returned
        /// `Entry` must be increased by 1.
        fn mknod(
            &self,
            ctx: Context,
            inode: Self::Inode,
            name: &CStr,
            mode: u32,
            rdev: u32,
            umask: u32,
        ) -> io::Result<Entry> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Create a directory.
        ///
        /// When the `FsOptions::DONT_MASK` feature is set, the file system is responsible for setting
        /// the permissions of the created directory to `mode & !umask`. Returns an `Entry` for the
        /// newly created directory.
        ///
        /// If this call is successful then the lookup count of the `Inode` associated with the returned
        /// `Entry` must be increased by 1.
        fn mkdir(
            &self,
            ctx: Context,
            parent: Self::Inode,
            name: &CStr,
            mode: u32,
            umask: u32,
        ) -> io::Result<Entry> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Remove a file.
        ///
        /// If the file's inode lookup count is non-zero, then the file system is expected to delay
        /// removal of the inode until the lookup count goes to zero. See the documentation of the
        /// `forget` function for more information.
        fn unlink(&self, ctx: Context, parent: Self::Inode, name: &CStr) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Remove a directory.
        ///
        /// If the directory's inode lookup count is non-zero, then the file system is expected to delay
        /// removal of the inode until the lookup count goes to zero. See the documentation of the
        /// `forget` function for more information.
        fn rmdir(&self, ctx: Context, parent: Self::Inode, name: &CStr) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Rename a file / directory.
        ///
        /// If the destination exists, it should be atomically replaced. If the destination's inode
        /// lookup count is non-zero, then the file system is expected to delay removal of the inode
        /// until the lookup count goes to zero. See the documentation of the `forget` function for more
        /// information.
        ///
        /// `flags` may be `libc::RENAME_EXCHANGE` or `libc::RENAME_NOREPLACE`. If
        /// `libc::RENAME_NOREPLACE` is specified, the implementation must not overwrite `newname` if it
        /// exists and must return an error instead. If `libc::RENAME_EXCHANGE` is specified, the
        /// implementation must atomically exchange the two files, i.e., both must exist and neither may
        /// be deleted.
        fn rename(
            &self,
            ctx: Context,
            olddir: Self::Inode,
            oldname: &CStr,
            newdir: Self::Inode,
            newname: &CStr,
            flags: u32,
        ) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Create a hard link.
        ///
        /// Create a hard link from `inode` to `newname` in the directory represented by `newparent`.
        ///
        /// If this call is successful then the lookup count of the `Inode` associated with the returned
        /// `Entry` must be increased by 1.
        fn link(
            &self,
            ctx: Context,
            inode: Self::Inode,
            newparent: Self::Inode,
            newname: &CStr,
        ) -> io::Result<Entry> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }
    */

    /// Open a file.
    ///
    /// Open the file associated with `inode` for reading / writing. All values accepted by the
    /// `open(2)` system call are valid values for `flags` and must be handled by the file system.
    /// However, there are some additional rules:
    ///
    /// * Creation flags (`libc::O_CREAT`, `libc::O_EXCL`, `libc::O_NOCTTY`) will be filtered out
    ///   and handled by the kernel.
    ///
    /// * The file system should check the access modes (`libc::O_RDONLY`, `libc::O_WRONLY`,
    ///   `libc::O_RDWR`) to determine if the operation is permitted. If the file system was mounted
    ///   with the `-o default_permissions` mount option, then this check will also be carried out
    ///   by the kernel before sending the open request.
    ///
    /// * When writeback caching is enabled (`FsOptions::WRITEBACK_CACHE`) the kernel may send read
    ///   requests even for files opened with `libc::O_WRONLY`. The file system should be prepared
    ///   to handle this.
    ///
    /// * When writeback caching is enabled, the kernel will handle the `libc::O_APPEND` flag.
    ///   However, this will not work reliably unless the kernel has exclusive access to the file.
    ///   In this case the file system may either ignore the `libc::O_APPEND` flag or return an
    ///   error to indicate that reliable `libc::O_APPEND` handling is not available.
    ///
    /// * When writeback caching is disabled, the file system is expected to properly handle
    ///   `libc::O_APPEND` and ensure that each write is appended to the end of the file.
    ///
    /// The file system may choose to return a `Handle` to refer to the newly opened file. The
    /// kernel will then use this `Handle` for all operations on the content of the file (`read`,
    /// `write`, `flush`, `release`, `fsync`). If the file system does not return a
    /// `Handle` then the kernel will use the `Inode` for the file to operate on its contents. In
    /// this case the file system may wish to enable the `FsOptions::ZERO_MESSAGE_OPEN` feature if
    /// it is supported by the kernel (see below).
    ///
    /// The returned `OpenOptions` allow the file system to change the way the opened file is
    /// handled by the kernel. See the documentation of `OpenOptions` for more information.
    ///
    /// If the `FsOptions::ZERO_MESSAGE_OPEN` feature is enabled by both the file system
    /// implementation and the kernel, then the file system may return an error of `ENOSYS`. This
    /// will be interpreted by the kernel as success and future calls to `open` and `release` will
    /// be handled by the kernel without being passed on to the file system.
    fn async_open<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> Pin<OpenFuture<'async_trait, Self::Handle>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        let result = self
            .open(ctx, inode, flags, fuse_flags)
            .map(|(handle, opts, _backing_id)| (handle.map(Into::<u64>::into), opts));
        Box::pin(async move { result.map(|(handle, opts)| (handle.map(From::from), opts)) })
    }

    /// Create and open a file.
    ///
    /// If the file does not already exist, the file system should create it with the specified
    /// `mode`. When the `FsOptions::DONT_MASK` feature is set, the file system is responsible for
    /// setting the permissions of the created file to `mode & !umask`.
    ///
    /// If the file system returns an `ENOSYS` error, then the kernel will treat this method as
    /// unimplemented and all future calls to `create` will be handled by calling the `mknod` and
    /// `open` methods instead.
    ///
    /// See the documentation for the `open` method for more information about opening the file. In
    /// addition to the optional `Handle` and the `OpenOptions`, the file system must also return an
    /// `Entry` for the file. This increases the lookup count for the `Inode` associated with the
    /// file by 1.
    fn async_create<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        parent: Self::Inode,
        name: &'c CStr,
        args: CreateIn,
    ) -> Pin<CreateFuture<'async_trait, Self::Handle>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        let result = self
            .create(ctx, parent, name, args)
            .map(|(entry, handle, opts, _backing_id)| (entry, handle.map(Into::<u64>::into), opts));
        Box::pin(async move {
            result.map(|(entry, handle, opts)| (entry, handle.map(From::from), opts))
        })
    }

    /// Read data from a file.
    ///
    /// Returns `size` bytes of data starting from offset `off` from the file associated with
    /// `inode` or `handle`.
    ///
    /// `flags` contains the flags used to open the file. Similarly, `handle` is the `Handle`
    /// returned by the file system from the `open` method, if any. If the file system
    /// implementation did not return a `Handle` from `open` then the contents of `handle` are
    /// undefined.
    ///
    /// This method should return exactly the number of bytes requested by the kernel, except in the
    /// case of error or EOF. Otherwise, the kernel will substitute the rest of the data with
    /// zeroes. An exception to this rule is if the file was opened with the "direct I/O" option
    /// (`libc::O_DIRECT`), in which case the kernel will forward the return code from this method
    /// to the userspace application that made the system call.
    #[allow(clippy::too_many_arguments)]
    fn async_read<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        w: &'c mut (dyn AsyncZeroCopyWriter + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> Pin<Box<dyn Future<Output = io::Result<usize>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.read(ctx, inode, handle, w, size, offset, lock_owner, flags),
        ))
    }

    /// Write data to a file.
    ///
    /// Writes `size` bytes of data starting from offset `off` to the file associated with `inode`
    /// or `handle`.
    ///
    /// `flags` contains the flags used to open the file. Similarly, `handle` is the `Handle`
    /// returned by the file system from the `open` method, if any. If the file system
    /// implementation did not return a `Handle` from `open` then the contents of `handle` are
    /// undefined.
    ///
    /// If the `FsOptions::HANDLE_KILLPRIV` feature is not enabled then then the file system is
    /// expected to clear the setuid and setgid bits.
    ///
    /// If `delayed_write` is true then it indicates that this is a write for buffered data.
    ///
    /// This method should return exactly the number of bytes requested by the kernel, except in the
    /// case of error. An exception to this rule is if the file was opened with the "direct I/O"
    /// option (`libc::O_DIRECT`), in which case the kernel will forward the return code from this
    /// method to the userspace application that made the system call.
    #[allow(clippy::too_many_arguments)]
    fn async_write<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        r: &'c mut (dyn AsyncZeroCopyReader + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> Pin<Box<dyn Future<Output = io::Result<usize>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(self.write(
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
        )))
    }

    /*
        /// Flush the contents of a file.
        ///
        /// This method is called on every `close()` of a file descriptor. Since it is possible to
        /// duplicate file descriptors there may be many `flush` calls for one call to `open`.
        ///
        /// File systems should not make any assumptions about when `flush` will be
        /// called or even if it will be called at all.
        ///
        /// `handle` is the `Handle` returned by the file system from the `open` method, if any. If the
        /// file system did not return a `Handle` from `open` then the contents of `handle` are
        /// undefined.
        ///
        /// Unlike `fsync`, the file system is not required to flush pending writes. One reason to flush
        /// data is if the file system wants to return write errors during close. However, this is not
        /// portable because POSIX does not require `close` to wait for delayed I/O to complete.
        ///
        /// If the `FsOptions::POSIX_LOCKS` feature is enabled, then the file system must remove all
        /// locks belonging to `lock_owner`.
        ///
        /// If this method returns an `ENOSYS` error then the kernel will treat it as success and all
        /// subsequent calls to `flush` will be handled by the kernel without being forwarded to the
        /// file system.
        fn flush(
            &self,
            ctx: Context,
            inode: Self::Inode,
            handle: Self::Handle,
            lock_owner: u64,
        ) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }
    */

    /// Synchronize file contents.
    ///
    /// File systems must ensure that the file contents have been flushed to disk before returning
    /// from this method. If `datasync` is true then only the file data (but not the metadata) needs
    /// to be flushed.
    ///
    /// `handle` is the `Handle` returned by the file system from the `open` method, if any. If the
    /// file system did not return a `Handle` from `open` then the contents of
    /// `handle` are undefined.
    ///
    /// If this method returns an `ENOSYS` error then the kernel will treat it as success and all
    /// subsequent calls to `fsync` will be handled by the kernel without being forwarded to the
    /// file system.
    fn async_fsync<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        datasync: bool,
        handle: Self::Handle,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(self.fsync(ctx, inode, datasync, handle)))
    }

    /// Allocate requested space for file data.
    ///
    /// If this function returns success, then the file sytem must guarantee that it is possible to
    /// write up to `length` bytes of data starting at `offset` without failing due to a lack of
    /// free space on the disk.
    ///
    /// `handle` is the `Handle` returned by the file system from the `open` method, if any. If the
    /// file system did not return a `Handle` from `open` then the contents of `handle` are
    /// undefined.
    ///
    /// If this method returns an `ENOSYS` error then the kernel will treat that as a permanent
    /// failure: all future calls to `fallocate` will fail with `EOPNOTSUPP` without being forwarded
    /// to the file system.
    fn async_fallocate<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.fallocate(ctx, inode, handle, mode, offset, length),
        ))
    }

    /*
        /// Release an open file.
        ///
        /// This method is called when there are no more references to an open file: all file
        /// descriptors are closed and all memory mappings are unmapped.
        ///
        /// For every `open` call there will be exactly one `release` call (unless the file system is
        /// force-unmounted).
        ///
        /// The file system may reply with an error, but error values are not returned to the `close()`
        /// or `munmap()` which triggered the release.
        ///
        /// `handle` is the `Handle` returned by the file system from the `open` method, if any. If the
        /// file system did not return a `Handle` from `open` then the contents of
        /// `handle` are undefined.
        ///
        /// If `flush` is `true` then the contents of the file should also be flushed to disk.
        #[allow(clippy::too_many_arguments)]
        fn release(
            &self,
            ctx: Context,
            inode: Self::Inode,
            flags: u32,
            handle: Self::Handle,
            flush: bool,
            flock_release: bool,
            lock_owner: Option<u64>,
        ) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Get information about the file system.
        fn statfs(&self, ctx: Context, inode: Self::Inode) -> io::Result<libc::statvfs64> {
            // Safe because we are zero-initializing a struct with only POD fields.
            let mut st: libc::statvfs64 = unsafe { mem::zeroed() };

            // This matches the behavior of libfuse as it returns these values if the
            // filesystem doesn't implement this method.
            st.f_namemax = 255;
            st.f_bsize = 512;

            Ok(st)
        }

        /// Set an extended attribute.
        ///
        /// If this method fails with an `ENOSYS` error, then the kernel will treat that as a permanent
        /// failure. The kernel will return `EOPNOTSUPP` for all future calls to `setxattr` without
        /// forwarding them to the file system.
        ///
        /// Valid values for flags are the same as those accepted by the `setxattr(2)` system call and
        /// have the same behavior.
        fn setxattr(
            &self,
            ctx: Context,
            inode: Self::Inode,
            name: &CStr,
            value: &[u8],
            flags: u32,
        ) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Get an extended attribute.
        ///
        /// If `size` is 0, then the file system should respond with `GetxattrReply::Count` and the
        /// number of bytes needed to hold the value. If `size` is large enough to hold the value, then
        /// the file system should reply with `GetxattrReply::Value` and the value of the extended
        /// attribute. If `size` is not 0 but is also not large enough to hold the value, then the file
        /// system should reply with an `ERANGE` error.
        ///
        /// If this method fails with an `ENOSYS` error, then the kernel will treat that as a permanent
        /// failure. The kernel will return `EOPNOTSUPP` for all future calls to `getxattr` without
        /// forwarding them to the file system.
        fn getxattr(
            &self,
            ctx: Context,
            inode: Self::Inode,
            name: &CStr,
            size: u32,
        ) -> io::Result<GetxattrReply> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// List extended attribute names.
        ///
        /// If `size` is 0, then the file system should respond with `ListxattrReply::Count` and the
        /// number of bytes needed to hold a `\0` byte separated list of the names of all the extended
        /// attributes. If `size` is large enough to hold the `\0` byte separated list of the attribute
        /// names, then the file system should reply with `ListxattrReply::Names` and the list. If
        /// `size` is not 0 but is also not large enough to hold the list, then the file system should
        /// reply with an `ERANGE` error.
        ///
        /// If this method fails with an `ENOSYS` error, then the kernel will treat that as a permanent
        /// failure. The kernel will return `EOPNOTSUPP` for all future calls to `listxattr` without
        /// forwarding them to the file system.
        fn listxattr(&self, ctx: Context, inode: Self::Inode, size: u32) -> io::Result<ListxattrReply> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        /// Remove an extended attribute.
        ///
        /// If this method fails with an `ENOSYS` error, then the kernel will treat that as a permanent
        /// failure. The kernel will return `EOPNOTSUPP` for all future calls to `removexattr` without
        /// forwarding them to the file system.
        fn removexattr(&self, ctx: Context, inode: Self::Inode, name: &CStr) -> io::Result<()> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }
    */

    /// Open a directory for reading.
    ///
    /// The file system may choose to return a `Handle` to refer to the newly opened directory. The
    /// kernel will then use this `Handle` for all operations on the content of the directory
    /// (`readdir`, `readdirplus`, `fsyncdir`, `releasedir`). If the file system does not return a
    /// `Handle` then the kernel will use the `Inode` for the directory to operate on its contents.
    /// In this case the file system may wish to enable the `FsOptions::ZERO_MESSAGE_OPENDIR`
    /// feature if it is supported by the kernel (see below).
    ///
    /// The returned `OpenOptions` allow the file system to change the way the opened directory is
    /// handled by the kernel. See the documentation of `OpenOptions` for more information.
    ///
    /// If the `FsOptions::ZERO_MESSAGE_OPENDIR` feature is enabled by both the file system
    /// implementation and the kernel, then the file system may return an error of `ENOSYS`. This
    /// will be interpreted by the kernel as success and future calls to `opendir` and `releasedir`
    /// will be handled by the kernel without being passed on to the file system.
    fn async_opendir<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        flags: u32,
    ) -> Pin<OpenFuture<'async_trait, Self::Handle>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        let result = self
            .opendir(ctx, inode, flags)
            .map(|(handle, opts)| (handle.map(Into::<u64>::into), opts));
        Box::pin(async move { result.map(|(handle, opts)| (handle.map(From::from), opts)) })
    }

    /// Read a directory.
    ///
    /// `handle` is the `Handle` returned by the file system from the `opendir` method, if any. If
    /// the file system did not return a `Handle` from `opendir` then the contents of `handle` are
    /// undefined.
    ///
    /// `size` indicates the maximum number of bytes that should be returned by this method,
    /// but can be ignored in practice. Instead, entries are returned by calling the
    /// `add_entry` function until it returns zero (indicating that the buffer is full).
    ///
    /// `add_entry` copies the entry into the reply buffer and returns right away, so the returned
    /// future may call it between `.await` points. It is `Send`, so a future that holds it stays
    /// `Send`. The server sends the reply once the future completes. If the future fails, the
    /// reply carries only the error and none of the entries added before.
    ///
    /// If `offset` is non-zero then it corresponds to one of the `offset` values from a `DirEntry`
    /// that was previously returned by a call to `readdir` for the same handle. In this case the
    /// file system should skip over the entries before the position defined by the `offset` value.
    /// If entries were added or removed while the `Handle` is open then the file system may still
    /// include removed entries or skip newly created entries. However, adding or removing entries
    /// should never cause the file system to skip over unrelated entries or include an entry more
    /// than once. This means that `offset` cannot be a simple index and must include sufficient
    /// information to uniquely determine the next entry in the list even when the set of entries is
    /// being changed.
    ///
    /// The file system may return entries for the current directory (".") and parent directory
    /// ("..") but is not required to do so. The Linux kernel doesn't add them, so a listing shows
    /// them only if the file system returns them.
    ///
    /// The lookup count for `Inode`s associated with the returned directory entries is **NOT**
    /// affected by this method.
    fn async_readdir<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        size: u32,
        offset: u64,
        add_entry: &'c mut (dyn FnMut(DirEntry) -> io::Result<usize> + Send),
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.readdir(ctx, inode, handle, size, offset, add_entry),
        ))
    }

    /// Read a directory with entry attributes.
    ///
    /// Like `async_readdir` but also includes the attributes for each directory entry.
    ///
    /// `handle` is the `Handle` returned by the file system from the `opendir` method, if any. If
    /// the file system did not return a `Handle` from `opendir` then the contents of `handle` are
    /// undefined.
    ///
    /// `size` indicates the maximum number of bytes that should be returned by this method,
    /// but can be ignored in practice. Instead, entries are returned by calling the
    /// `add_entry` function until it returns zero (indicating that the buffer is full).
    /// `add_entry` works as it does for `async_readdir`.
    ///
    /// Unlike `async_readdir`, the lookup count for `Inode`s associated with the returned
    /// directory entries **IS** affected by this method (since it returns an `Entry` for each
    /// `DirEntry`). The count for each `Inode` should be increased by 1. If the future fails after
    /// `add_entry` accepted entries, the kernel never sees them and sends no FORGET for them. So
    /// drop the lookup counts taken for them before failing, or succeed with the entries added so
    /// far and report the error on the next call.
    ///
    /// File systems that implement this method should enable the `FsOptions::DO_READDIRPLUS`
    /// feature when supported by the kernel. The kernel will not call this method unless that
    /// feature is enabled.
    ///
    /// Additionally, file systems that implement both `readdir` and `readdirplus` should enable the
    /// `FsOptions::READDIRPLUS_AUTO` feature to allow the kernel to issue both `readdir` and
    /// `readdirplus` requests, depending on how much information is expected to be required.
    fn async_readdirplus<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        size: u32,
        offset: u64,
        add_entry: &'c mut (dyn FnMut(DirEntry, Entry) -> io::Result<usize> + Send),
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.readdirplus(ctx, inode, handle, size, offset, add_entry),
        ))
    }

    /// Synchronize the contents of a directory.
    ///
    /// File systems must ensure that the directory contents have been flushed to disk before
    /// returning from this method. If `datasync` is true then only the directory data (but not the
    /// metadata) needs to be flushed.
    ///
    /// `handle` is the `Handle` returned by the file system from the `opendir` method, if any. If
    /// the file system did not return a `Handle` from `opendir` then the contents of
    /// `handle` are undefined.
    ///
    /// If this method returns an `ENOSYS` error then the kernel will treat it as success and all
    /// subsequent calls to `fsyncdir` will be handled by the kernel without being forwarded to the
    /// file system.
    fn async_fsyncdir<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        datasync: bool,
        handle: Self::Handle,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.fsyncdir(ctx, inode, datasync, handle),
        ))
    }

    /// Release an open directory.
    ///
    /// For every `opendir` call there will be exactly one `releasedir` call (unless the file system
    /// is force-unmounted).
    ///
    /// `handle` is the `Handle` returned by the file system from the `opendir` method, if any. If
    /// the file system did not return a `Handle` from `opendir` then the contents of `handle` are
    /// undefined.
    ///
    /// `flags` contains used the flags used to open the directory in `opendir`.
    fn async_releasedir<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        flags: u32,
        handle: Self::Handle,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        Box::pin(std::future::ready(
            self.releasedir(ctx, inode, flags, handle),
        ))
    }

    /*
    #[cfg(feature = "virtiofs")]
    /// Setup a mapping so that guest can access files in DAX style.
    ///
    /// The virtio-fs DAX Window allows bypassing guest page cache and allows mapping host
    /// page cache directly in guest address space.
    ///
    /// When a page of file is needed, guest sends a request to map that page (in host page cache)
    /// in VMM address space. Inside guest this is a physical memory range controlled by virtiofs
    /// device. And guest directly maps this physical address range using DAX and hence gets
    /// access to file data on host.
    ///
    /// This can speed up things considerably in many situations. Also this can result in
    /// substantial memory savings as file data does not have to be copied in guest and it is
    /// directly accessed from host page cache.
    #[allow(clippy::too_many_arguments)]
    fn setupmapping(
        &self,
        _ctx: Context,
        inode: Self::Inode,
        handle: Self::Handle,
        foffset: u64,
        len: u64,
        flags: u64,
        moffset: u64,
        vu_req: &mut dyn FsCacheReqHandler,
    ) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    #[cfg(feature = "virtiofs")]
    /// Teardown a mapping which was setup for guest DAX style access.
    fn removemapping(
        &self,
        _ctx: Context,
        _inode: Self::Inode,
        requests: Vec<RemovemappingOne>,
        vu_req: &mut dyn FsCacheReqHandler,
    ) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// Check file access permissions.
    ///
    /// This method is called when a userspace process in the client makes an `access()` or
    /// `chdir()` system call. If the file system was mounted with the `-o default_permissions`
    /// mount option, then the kernel will perform these checks itself and this method will not be
    /// called.
    ///
    /// If this method returns an `ENOSYS` error, then the kernel will treat it as a permanent
    /// success: all future calls to `access` will return success without being forwarded to the
    /// file system.
    fn access(&self, ctx: Context, inode: Self::Inode, mask: u32) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// Reposition read/write file offset.
    fn lseek(
        &self,
        ctx: Context,
        inode: Self::Inode,
        handle: Self::Handle,
        offset: u64,
        whence: u32,
    ) -> io::Result<u64> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// Copy data from one file to another.
    ///
    /// The `inode_in`/`fh_in` pair identifies the source file and the `inode_out`/`fh_out` pair
    /// the destination file. `offset_in` and `offset_out` are the starting offsets. `len` is the
    /// maximum number of bytes to copy and the return value is the number of bytes actually
    /// copied, which may be smaller than `len`, for example when the end of the source file is
    /// reached. `flags` is currently unused by the kernel and must be zero.
    #[allow(clippy::too_many_arguments)]
    fn copy_file_range(
        &self,
        ctx: Context,
        inode_in: Self::Inode,
        fh_in: Self::Handle,
        offset_in: u64,
        inode_out: Self::Inode,
        fh_out: Self::Handle,
        offset_out: u64,
        len: u64,
        flags: u64,
    ) -> io::Result<u32> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn getlk(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn setlk(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn setlkw(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn ioctl(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn bmap(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn poll(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }

    /// TODO: support this
    fn notify_reply(&self) -> io::Result<()> {
        Err(io::Error::from_raw_os_error(libc::ENOSYS))
    }
    */
}

type AttrFuture<'async_trait> =
    Box<dyn Future<Output = io::Result<(stat64, Duration)>> + Send + 'async_trait>;
type OpenFuture<'async_trait, H> =
    Box<dyn Future<Output = io::Result<(Option<H>, OpenOptions)>> + Send + 'async_trait>;
type CreateFuture<'async_trait, H> =
    Box<dyn Future<Output = io::Result<(Entry, Option<H>, OpenOptions)>> + Send + 'async_trait>;

impl<FS: AsyncFileSystem> AsyncFileSystem for Arc<FS> {
    fn async_lookup<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        parent: Self::Inode,
        name: &'c CStr,
    ) -> Pin<Box<dyn Future<Output = io::Result<Entry>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_lookup(ctx, parent, name)
    }

    fn async_getattr<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Option<Self::Handle>,
    ) -> Pin<AttrFuture<'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_getattr(ctx, inode, handle)
    }

    fn async_setattr<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        attr: stat64,
        handle: Option<Self::Handle>,
        valid: SetattrValid,
    ) -> Pin<AttrFuture<'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_setattr(ctx, inode, attr, handle, valid)
    }

    fn async_open<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        flags: u32,
        fuse_flags: u32,
    ) -> Pin<OpenFuture<'async_trait, Self::Handle>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_open(ctx, inode, flags, fuse_flags)
    }

    fn async_create<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        parent: Self::Inode,
        name: &'c CStr,
        args: CreateIn,
    ) -> Pin<CreateFuture<'async_trait, Self::Handle>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_create(ctx, parent, name, args)
    }

    fn async_read<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        w: &'c mut (dyn AsyncZeroCopyWriter + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        flags: u32,
    ) -> Pin<Box<dyn Future<Output = io::Result<usize>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        self.deref()
            .async_read(ctx, inode, handle, w, size, offset, lock_owner, flags)
    }

    fn async_write<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        r: &'c mut (dyn AsyncZeroCopyReader + Send),
        size: u32,
        offset: u64,
        lock_owner: Option<u64>,
        delayed_write: bool,
        flags: u32,
        fuse_flags: u32,
    ) -> Pin<Box<dyn Future<Output = io::Result<usize>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_write(
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

    fn async_fsync<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        datasync: bool,
        handle: Self::Handle,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_fsync(ctx, inode, datasync, handle)
    }

    fn async_fallocate<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        mode: u32,
        offset: u64,
        length: u64,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref()
            .async_fallocate(ctx, inode, handle, mode, offset, length)
    }

    fn async_opendir<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        flags: u32,
    ) -> Pin<OpenFuture<'async_trait, Self::Handle>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_opendir(ctx, inode, flags)
    }

    fn async_readdir<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        size: u32,
        offset: u64,
        add_entry: &'c mut (dyn FnMut(DirEntry) -> io::Result<usize> + Send),
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        self.deref()
            .async_readdir(ctx, inode, handle, size, offset, add_entry)
    }

    fn async_readdirplus<'a, 'b, 'c, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        handle: Self::Handle,
        size: u32,
        offset: u64,
        add_entry: &'c mut (dyn FnMut(DirEntry, Entry) -> io::Result<usize> + Send),
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        'c: 'async_trait,
        Self: 'async_trait,
    {
        self.deref()
            .async_readdirplus(ctx, inode, handle, size, offset, add_entry)
    }

    fn async_fsyncdir<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        datasync: bool,
        handle: Self::Handle,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_fsyncdir(ctx, inode, datasync, handle)
    }

    fn async_releasedir<'a, 'b, 'async_trait>(
        &'a self,
        ctx: &'b Context,
        inode: Self::Inode,
        flags: u32,
        handle: Self::Handle,
    ) -> Pin<Box<dyn Future<Output = io::Result<()>> + Send + 'async_trait>>
    where
        'a: 'async_trait,
        'b: 'async_trait,
        Self: 'async_trait,
    {
        self.deref().async_releasedir(ctx, inode, flags, handle)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file_traits::FileReadWriteVolatile;

    /// Implements only the sync handlers.
    struct SyncFs;

    impl FileSystem for SyncFs {
        type Inode = u64;
        type Handle = u64;

        fn lookup(&self, _ctx: &Context, parent: u64, _name: &CStr) -> io::Result<Entry> {
            Ok(Entry {
                inode: parent + 1,
                ..Default::default()
            })
        }

        fn open(
            &self,
            _ctx: &Context,
            inode: u64,
            _flags: u32,
            _fuse_flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions, Option<u32>)> {
            Ok((Some(inode * 10), OpenOptions::KEEP_CACHE, None))
        }

        fn read(
            &self,
            _ctx: &Context,
            _inode: u64,
            _handle: u64,
            w: &mut dyn ZeroCopyWriter,
            size: u32,
            _offset: u64,
            _lock_owner: Option<u64>,
            _flags: u32,
        ) -> io::Result<usize> {
            w.write(&b"served by read()"[..size as usize])
        }

        fn opendir(
            &self,
            _ctx: &Context,
            inode: u64,
            _flags: u32,
        ) -> io::Result<(Option<u64>, OpenOptions)> {
            Ok((Some(inode * 10), OpenOptions::DIRECT_IO))
        }

        fn readdir(
            &self,
            _ctx: &Context,
            _inode: u64,
            _handle: u64,
            _size: u32,
            offset: u64,
            add_entry: &mut dyn FnMut(DirEntry) -> io::Result<usize>,
        ) -> io::Result<()> {
            let names: [&[u8]; 2] = [b"a", b"b"];
            for (i, name) in names.iter().enumerate().skip(offset as usize) {
                let entry = DirEntry {
                    ino: i as u64 + 2,
                    offset: i as u64 + 1,
                    type_: libc::DT_REG as u32,
                    name,
                };
                if add_entry(entry)? == 0 {
                    break;
                }
            }
            Ok(())
        }

        fn readdirplus(
            &self,
            ctx: &Context,
            inode: u64,
            handle: u64,
            size: u32,
            offset: u64,
            add_entry: &mut dyn FnMut(DirEntry, Entry) -> io::Result<usize>,
        ) -> io::Result<()> {
            self.readdir(ctx, inode, handle, size, offset, &mut |dir_entry| {
                let entry = Entry {
                    inode: dir_entry.ino,
                    ..Default::default()
                };
                add_entry(dir_entry, entry)
            })
        }

        fn releasedir(
            &self,
            _ctx: &Context,
            inode: u64,
            _flags: u32,
            handle: u64,
        ) -> io::Result<()> {
            if handle == inode * 10 {
                Ok(())
            } else {
                Err(io::Error::from_raw_os_error(libc::EBADF))
            }
        }
    }

    impl AsyncFileSystem for SyncFs {}

    struct VecWriter(Vec<u8>);

    impl io::Write for VecWriter {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
            self.0.write(buf)
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    impl ZeroCopyWriter for VecWriter {
        fn write_from(
            &mut self,
            _f: &mut dyn FileReadWriteVolatile,
            _count: usize,
            _off: u64,
        ) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }

        fn available_bytes(&self) -> usize {
            usize::MAX
        }
    }

    #[async_trait(?Send)]
    impl AsyncZeroCopyWriter for VecWriter {
        async fn async_write_from(
            &mut self,
            _f: Arc<dyn AsyncFileReadWriteVolatile>,
            _count: usize,
            _off: u64,
        ) -> io::Result<usize> {
            Err(io::Error::from_raw_os_error(libc::ENOSYS))
        }
    }

    #[tokio::test]
    async fn test_defaults_call_sync_handlers() {
        let fs = SyncFs;
        let ctx = Context::default();

        let name = CStr::from_bytes_with_nul(b"file\0").unwrap();
        let entry = fs.async_lookup(&ctx, 1, name).await.unwrap();
        assert_eq!(entry.inode, 2);

        let (handle, opts) = fs.async_open(&ctx, 2, 0, 0).await.unwrap();
        assert_eq!((handle, opts), (Some(20), OpenOptions::KEEP_CACHE));

        let mut w = VecWriter(Vec::new());
        let n = fs
            .async_read(&ctx, 2, 20, &mut w, 9, 0, None, 0)
            .await
            .unwrap();
        assert_eq!(&w.0[..n], b"served by");

        // Without a sync handler, the default still returns ENOSYS.
        let err = fs.async_getattr(&ctx, 2, None).await.unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::ENOSYS));
    }

    #[tokio::test]
    async fn test_dir_defaults_call_sync_handlers() {
        let fs = SyncFs;
        let ctx = Context::default();

        let (handle, opts) = fs.async_opendir(&ctx, 1, 0).await.unwrap();
        assert_eq!((handle, opts), (Some(10), OpenOptions::DIRECT_IO));

        // The entries come from readdir(), which starts at the offset and
        // stops once add_entry() returns 0.
        let mut names = Vec::new();
        fs.async_readdir(&ctx, 1, 10, 4096, 0, &mut |dir_entry| {
            names.push(dir_entry.name.to_vec());
            Ok(0)
        })
        .await
        .unwrap();
        assert_eq!(names, [b"a"]);

        let mut inodes = Vec::new();
        fs.async_readdirplus(&ctx, 1, 10, 4096, 1, &mut |dir_entry, entry| {
            inodes.push((dir_entry.ino, entry.inode));
            Ok(1)
        })
        .await
        .unwrap();
        assert_eq!(inodes, [(3, 3)]);

        fs.async_releasedir(&ctx, 1, 0, 10).await.unwrap();
        let err = fs.async_releasedir(&ctx, 1, 0, 11).await.unwrap_err();
        assert_eq!(err.raw_os_error(), Some(libc::EBADF));
    }
}
