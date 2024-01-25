use std::{
    io,
    mem::{self, size_of},
    os::fd::{AsRawFd, RawFd},
};
use vm_memory::{bitmap::BitmapSlice, ByteValued};

use crate::{
    api::{filesystem::DirEntry, CURRENT_DIR_CSTR, PARENT_DIR_CSTR},
    bytes_to_cstr,
    passthrough::{os_compat::LinuxDirent64, util::einval},
};

use super::{Handle, Inode, OffT, PassthroughFs};

impl<S: BitmapSlice + Send + Sync> PassthroughFs<S> {
    pub fn do_readdir(
        &self,
        inode: Inode,
        handle: Handle,
        size: u32,
        offset: u64,
        add_entry: &mut dyn FnMut(DirEntry, RawFd) -> io::Result<usize>,
    ) -> io::Result<()> {
        if size == 0 {
            return Ok(());
        }

        let mut buf = Vec::<u8>::with_capacity(size as usize);
        let data = self.get_dirdata(handle, inode, libc::O_RDONLY)?;

        {
            // Since we are going to work with the kernel offset, we have to acquire the file lock
            // for both the `lseek64` and `getdents64` syscalls to ensure that no other thread
            // changes the kernel offset while we are using it.
            let (guard, dir) = data.get_file_mut();

            // Safe because this doesn't modify any memory and we check the return value.
            let res = unsafe { libc::lseek64(dir.as_raw_fd(), offset as OffT, libc::SEEK_SET) };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }

            // Safe because the kernel guarantees that it will only write to `buf` and we check the
            // return value.
            let res = unsafe {
                libc::syscall(
                    libc::SYS_getdents64,
                    dir.as_raw_fd(),
                    buf.as_mut_ptr() as *mut LinuxDirent64,
                    size as libc::c_int,
                )
            };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }

            // Safe because we trust the value returned by kernel.
            unsafe { buf.set_len(res as usize) };

            // Explicitly drop the lock so that it's not held while we fill in the fuse buffer.
            mem::drop(guard);
        }

        let mut rem = &buf[..];
        let orig_rem_len = rem.len();

        while !rem.is_empty() {
            // We only use debug asserts here because these values are coming from the kernel and we
            // trust them implicitly.
            debug_assert!(
                rem.len() >= size_of::<LinuxDirent64>(),
                "fuse: not enough space left in `rem`"
            );

            let (front, back) = rem.split_at(size_of::<LinuxDirent64>());

            let dirent64 = LinuxDirent64::from_slice(front)
                .expect("fuse: unable to get LinuxDirent64 from slice");

            let namelen = dirent64.d_reclen as usize - size_of::<LinuxDirent64>();
            debug_assert!(
                namelen <= back.len(),
                "fuse: back is smaller than `namelen`"
            );

            let name = &back[..namelen];
            let res = if name.starts_with(CURRENT_DIR_CSTR) || name.starts_with(PARENT_DIR_CSTR) {
                // We don't want to report the "." and ".." entries. However, returning `Ok(0)` will
                // break the loop so return `Ok` with a non-zero value instead.
                Ok(1)
            } else {
                // The Sys_getdents64 in kernel will pad the name with '\0'
                // bytes up to 8-byte alignment, so @name may contain a few null
                // terminators.  This causes an extra lookup from fuse when
                // called by readdirplus, because kernel path walking only takes
                // name without null terminators, the dentry with more than 1
                // null terminators added by readdirplus doesn't satisfy the
                // path walking.
                let name = bytes_to_cstr(name)
                    .map_err(|e| {
                        error!("fuse: do_readdir: {:?}", e);
                        einval()
                    })?
                    .to_bytes();

                add_entry(
                    DirEntry {
                        ino: dirent64.d_ino,
                        offset: dirent64.d_off as u64,
                        type_: u32::from(dirent64.d_ty),
                        name,
                    },
                    data.borrow_fd().as_raw_fd(),
                )
            };

            debug_assert!(
                rem.len() >= dirent64.d_reclen as usize,
                "fuse: rem is smaller than `d_reclen`"
            );

            match res {
                Ok(0) => break,
                Ok(_) => rem = &rem[dirent64.d_reclen as usize..],
                // If there's an error, we can only signal it if we haven't
                // stored any entries yet - otherwise we'd end up with wrong
                // lookup counts for the entries that are already in the
                // buffer. So we return what we've collected until that point.
                Err(e) if rem.len() == orig_rem_len => return Err(e),
                Err(_) => return Ok(()),
            }
        }

        Ok(())
    }
}
