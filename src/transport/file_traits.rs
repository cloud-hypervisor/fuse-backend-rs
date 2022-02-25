// Copyright 2018 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! File extension traits to transfer data between File objects and [VolatileSlice][2] buffers.
//!
//! Fuse filesystem servers use normal memory buffers to transfer data from/to File objects.
//! For virtio-fs file servers, they need to transfer data between File objects and guest memory.
//! The guest memory could be accessed through [GuestMemory][1] or [VolatileSlice][2] objects.
//! And the [VolatileSlice][2] trait could also be used to access normal memory buffers too.
//! So several [VolatileSlice][2] based File extension traits are introduced to deal with both
//! guest memory and normal memory buffers.
//!
//! [1]: https://docs.rs/vm-memory/0.2.0/vm_memory/guest_memory/trait.GuestMemory.html
//! [2]: https://docs.rs/vm-memory/0.2.0/vm_memory/volatile_memory/struct.VolatileSlice.html

use std::fs::File;
use std::io::{Error, ErrorKind, Result};
use std::os::unix::io::AsRawFd;

use libc::{c_int, c_void, read, readv, size_t, write, writev};

use crate::abi::fuse_abi::{off64_t, pread64, preadv64, pwrite64, pwritev64};
use crate::transport::FileVolatileSlice;

/// A trait for setting the size of a file.
/// This is equivalent to File's `set_len` method, but wrapped in a trait so that it can be
/// implemented for other types.
pub trait FileSetLen {
    /// Set the size of this file.
    ///
    /// This is the moral equivalent of `ftruncate()`.
    fn set_len(&self, _len: u64) -> Result<()>;
}

impl FileSetLen for File {
    fn set_len(&self, len: u64) -> Result<()> {
        File::set_len(self, len)
    }
}

/// A trait similar to `Read` and `Write`, but uses volatile memory as buffers.
pub trait FileReadWriteVolatile {
    /// Read bytes from this file into the given slice, returning the number of bytes read on
    /// success.
    fn read_volatile(&mut self, slice: FileVolatileSlice) -> Result<usize>;

    /// Like `read_volatile`, except it reads to a slice of buffers. Data is copied to fill each
    /// buffer in order, with the final buffer written to possibly being only partially filled. This
    /// method must behave as a single call to `read_volatile` with the buffers concatenated would.
    /// The default implementation calls `read_volatile` with either the first nonempty buffer
    /// provided, or returns `Ok(0)` if none exists.
    fn read_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> Result<usize> {
        bufs.iter()
            .find(|b| !b.is_empty())
            .map(|b| self.read_volatile(*b))
            .unwrap_or(Ok(0))
    }

    /// Reads bytes from this into the given slice until all bytes in the slice are written, or an
    /// error is returned.
    fn read_exact_volatile(&mut self, mut slice: FileVolatileSlice) -> Result<()> {
        while !slice.is_empty() {
            let bytes_read = self.read_volatile(slice)?;
            if bytes_read == 0 {
                return Err(Error::from(ErrorKind::UnexpectedEof));
            }
            // Will panic if read_volatile read more bytes than we gave it, which would be worthy of
            // a panic.
            slice = slice.offset(bytes_read).unwrap();
        }
        Ok(())
    }

    /// Write bytes from the slice to the given file, returning the number of bytes written on
    /// success.
    fn write_volatile(&mut self, slice: FileVolatileSlice) -> Result<usize>;

    /// Like `write_volatile`, except that it writes from a slice of buffers. Data is copied from
    /// each buffer in order, with the final buffer read from possibly being only partially
    /// consumed. This method must behave as a call to `write_volatile` with the buffers
    /// concatenated would. The default implementation calls `write_volatile` with either the first
    /// nonempty buffer provided, or returns `Ok(0)` if none exists.
    fn write_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> Result<usize> {
        bufs.iter()
            .find(|b| !b.is_empty())
            .map(|b| self.write_volatile(*b))
            .unwrap_or(Ok(0))
    }

    /// Write bytes from the slice to the given file until all the bytes from the slice have been
    /// written, or an error is returned.
    fn write_all_volatile(&mut self, mut slice: FileVolatileSlice) -> Result<()> {
        while !slice.is_empty() {
            let bytes_written = self.write_volatile(slice)?;
            if bytes_written == 0 {
                return Err(Error::from(ErrorKind::WriteZero));
            }
            // Will panic if write_volatile read more bytes than we gave it, which would be worthy
            // of a panic.
            slice = slice.offset(bytes_written).unwrap();
        }
        Ok(())
    }

    /// Reads bytes from this file at `offset` into the given slice, returning the number of bytes
    /// read on success.
    fn read_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<usize>;

    /// Like `read_at_volatile`, except it reads to a slice of buffers. Data is copied to fill each
    /// buffer in order, with the final buffer written to possibly being only partially filled. This
    /// method must behave as a single call to `read_at_volatile` with the buffers concatenated
    /// would. The default implementation calls `read_at_volatile` with either the first nonempty
    /// buffer provided, or returns `Ok(0)` if none exists.
    fn read_vectored_at_volatile(
        &mut self,
        bufs: &[FileVolatileSlice],
        offset: u64,
    ) -> Result<usize> {
        if let Some(slice) = bufs.first() {
            self.read_at_volatile(*slice, offset)
        } else {
            Ok(0)
        }
    }

    /// Reads bytes from this file at `offset` into the given slice until all bytes in the slice are
    /// read, or an error is returned.
    fn read_exact_at_volatile(
        &mut self,
        mut slice: FileVolatileSlice,
        mut offset: u64,
    ) -> Result<()> {
        while !slice.is_empty() {
            match self.read_at_volatile(slice, offset) {
                Ok(0) => return Err(Error::from(ErrorKind::UnexpectedEof)),
                Ok(n) => {
                    // Will panic if read_at_volatile read more bytes than we gave it, which would
                    // be worthy of a panic.
                    slice = slice.offset(n).unwrap();
                    offset = offset.checked_add(n as u64).unwrap();
                }
                Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }

    /// Writes bytes from this file at `offset` into the given slice, returning the number of bytes
    /// written on success.
    fn write_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<usize>;

    /// Like `write_at_at_volatile`, except that it writes from a slice of buffers. Data is copied
    /// from each buffer in order, with the final buffer read from possibly being only partially
    /// consumed. This method must behave as a call to `write_at_volatile` with the buffers
    /// concatenated would. The default implementation calls `write_at_volatile` with either the
    /// first nonempty buffer provided, or returns `Ok(0)` if none exists.
    fn write_vectored_at_volatile(
        &mut self,
        bufs: &[FileVolatileSlice],
        offset: u64,
    ) -> Result<usize> {
        if let Some(slice) = bufs.first() {
            self.write_at_volatile(*slice, offset)
        } else {
            Ok(0)
        }
    }

    /// Writes bytes from this file at `offset` into the given slice until all bytes in the slice
    /// are written, or an error is returned.
    fn write_all_at_volatile(
        &mut self,
        mut slice: FileVolatileSlice,
        mut offset: u64,
    ) -> Result<()> {
        while !slice.is_empty() {
            match self.write_at_volatile(slice, offset) {
                Ok(0) => return Err(Error::from(ErrorKind::WriteZero)),
                Ok(n) => {
                    // Will panic if write_at_volatile read more bytes than we gave it, which would
                    // be worthy of a panic.
                    slice = slice.offset(n).unwrap();
                    offset = offset.checked_add(n as u64).unwrap();
                }
                Err(ref e) if e.kind() == ErrorKind::Interrupted => {}
                Err(e) => return Err(e),
            }
        }
        Ok(())
    }
}

impl<T: FileReadWriteVolatile + ?Sized> FileReadWriteVolatile for &mut T {
    fn read_volatile(&mut self, slice: FileVolatileSlice) -> Result<usize> {
        (**self).read_volatile(slice)
    }

    fn read_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> Result<usize> {
        (**self).read_vectored_volatile(bufs)
    }

    fn read_exact_volatile(&mut self, slice: FileVolatileSlice) -> Result<()> {
        (**self).read_exact_volatile(slice)
    }

    fn write_volatile(&mut self, slice: FileVolatileSlice) -> Result<usize> {
        (**self).write_volatile(slice)
    }

    fn write_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> Result<usize> {
        (**self).write_vectored_volatile(bufs)
    }

    fn write_all_volatile(&mut self, slice: FileVolatileSlice) -> Result<()> {
        (**self).write_all_volatile(slice)
    }

    fn read_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<usize> {
        (**self).read_at_volatile(slice, offset)
    }

    fn read_vectored_at_volatile(
        &mut self,
        bufs: &[FileVolatileSlice],
        offset: u64,
    ) -> Result<usize> {
        (**self).read_vectored_at_volatile(bufs, offset)
    }

    fn read_exact_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<()> {
        (**self).read_exact_at_volatile(slice, offset)
    }

    fn write_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<usize> {
        (**self).write_at_volatile(slice, offset)
    }

    fn write_vectored_at_volatile(
        &mut self,
        bufs: &[FileVolatileSlice],
        offset: u64,
    ) -> Result<usize> {
        (**self).write_vectored_at_volatile(bufs, offset)
    }

    fn write_all_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<()> {
        (**self).write_all_at_volatile(slice, offset)
    }
}

macro_rules! volatile_impl {
    ($ty:ty) => {
        impl FileReadWriteVolatile for $ty {
            fn read_volatile(&mut self, slice: FileVolatileSlice) -> Result<usize> {
                // Safe because only bytes inside the slice are accessed and the kernel is expected
                // to handle arbitrary memory for I/O.
                let ret =
                    unsafe { read(self.as_raw_fd(), slice.as_ptr() as *mut c_void, slice.len()) };

                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn read_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> Result<usize> {
                let iovecs: Vec<libc::iovec> = bufs
                    .iter()
                    .map(|s| libc::iovec {
                        iov_base: s.as_ptr() as *mut c_void,
                        iov_len: s.len() as size_t,
                    })
                    .collect();

                if iovecs.is_empty() {
                    return Ok(0);
                }

                // Safe because only bytes inside the buffers are accessed and the kernel is
                // expected to handle arbitrary memory for I/O.
                let ret = unsafe { readv(self.as_raw_fd(), &iovecs[0], iovecs.len() as c_int) };

                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn write_volatile(&mut self, slice: FileVolatileSlice) -> Result<usize> {
                // Safe because only bytes inside the slice are accessed and the kernel is expected
                // to handle arbitrary memory for I/O.
                let ret = unsafe {
                    write(
                        self.as_raw_fd(),
                        slice.as_ptr() as *const c_void,
                        slice.len(),
                    )
                };
                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn write_vectored_volatile(&mut self, bufs: &[FileVolatileSlice]) -> Result<usize> {
                let iovecs: Vec<libc::iovec> = bufs
                    .iter()
                    .map(|s| libc::iovec {
                        iov_base: s.as_ptr() as *mut c_void,
                        iov_len: s.len() as size_t,
                    })
                    .collect();

                if iovecs.is_empty() {
                    return Ok(0);
                }

                // Safe because only bytes inside the buffers are accessed and the kernel is
                // expected to handle arbitrary memory for I/O.
                let ret = unsafe { writev(self.as_raw_fd(), &iovecs[0], iovecs.len() as c_int) };
                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn read_at_volatile(&mut self, slice: FileVolatileSlice, offset: u64) -> Result<usize> {
                // Safe because only bytes inside the slice are accessed and the kernel is expected
                // to handle arbitrary memory for I/O.
                let ret = unsafe {
                    pread64(
                        self.as_raw_fd(),
                        slice.as_ptr() as *mut c_void,
                        slice.len(),
                        offset as off64_t,
                    )
                };

                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn read_vectored_at_volatile(
                &mut self,
                bufs: &[FileVolatileSlice],
                offset: u64,
            ) -> Result<usize> {
                let iovecs: Vec<libc::iovec> = bufs
                    .iter()
                    .map(|s| libc::iovec {
                        iov_base: s.as_ptr() as *mut c_void,
                        iov_len: s.len() as size_t,
                    })
                    .collect();

                if iovecs.is_empty() {
                    return Ok(0);
                }

                // Safe because only bytes inside the buffers are accessed and the kernel is
                // expected to handle arbitrary memory for I/O.
                let ret = unsafe {
                    preadv64(
                        self.as_raw_fd(),
                        &iovecs[0],
                        iovecs.len() as c_int,
                        offset as off64_t,
                    )
                };

                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn write_at_volatile(
                &mut self,
                slice: FileVolatileSlice,
                offset: u64,
            ) -> Result<usize> {
                // Safe because only bytes inside the slice are accessed and the kernel is expected
                // to handle arbitrary memory for I/O.
                let ret = unsafe {
                    pwrite64(
                        self.as_raw_fd(),
                        slice.as_ptr() as *const c_void,
                        slice.len(),
                        offset as off64_t,
                    )
                };

                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }

            fn write_vectored_at_volatile(
                &mut self,
                bufs: &[FileVolatileSlice],
                offset: u64,
            ) -> Result<usize> {
                let iovecs: Vec<libc::iovec> = bufs
                    .iter()
                    .map(|s| libc::iovec {
                        iov_base: s.as_ptr() as *mut c_void,
                        iov_len: s.len() as size_t,
                    })
                    .collect();

                if iovecs.is_empty() {
                    return Ok(0);
                }

                // Safe because only bytes inside the buffers are accessed and the kernel is
                // expected to handle arbitrary memory for I/O.
                let ret = unsafe {
                    pwritev64(
                        self.as_raw_fd(),
                        &iovecs[0],
                        iovecs.len() as c_int,
                        offset as off64_t,
                    )
                };
                if ret >= 0 {
                    Ok(ret as usize)
                } else {
                    Err(Error::last_os_error())
                }
            }
        }
    };
}

volatile_impl!(File);

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::{Seek, SeekFrom, Write};
    use vmm_sys_util::tempfile::TempFile;

    #[test]
    fn test_read_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let buf = [0xfu8; 32];
        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        assert_eq!(file.read_volatile(slice).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_volatile(slice).unwrap(), 0);
    }

    #[test]
    fn test_read_vectored_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let buf = [0xfu8; 32];
        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slices = unsafe {
            [
                FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, 16),
                FileVolatileSlice::new((buf2.as_mut_ptr() as *mut u8).add(16), 16),
            ]
        };
        assert_eq!(file.read_vectored_volatile(&slices).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_vectored_volatile(&slices).unwrap(), 0);
    }

    #[test]
    fn test_read_exact_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let buf = [0xfu8; 32];
        file.write_all(&buf).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 31];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        file.read_exact_volatile(slice).unwrap();
        assert_eq!(buf[..31], buf2);

        file.read_exact_volatile(slice).unwrap_err();
    }

    #[test]
    fn test_read_at_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let buf = [0xfu8; 32];
        file.write_all(&buf).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        assert_eq!(file.read_at_volatile(slice, 0).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_at_volatile(slice, 30).unwrap(), 2);
        assert_eq!(file.read_at_volatile(slice, 32).unwrap(), 0);
    }

    #[test]
    fn test_read_vectored_at_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let buf = [0xfu8; 32];
        file.write_all(&buf).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slices = unsafe {
            [
                FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, 16),
                FileVolatileSlice::new((buf2.as_mut_ptr() as *mut u8).add(16), 16),
            ]
        };
        assert_eq!(file.read_vectored_at_volatile(&slices, 0).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_vectored_at_volatile(&slices, 30).unwrap(), 2);
        assert_eq!(file.read_vectored_at_volatile(&slices, 32).unwrap(), 0);
    }

    #[test]
    fn test_read_exact_at_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let buf = [0xfu8; 32];
        file.write_all(&buf).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        file.read_exact_at_volatile(slice, 0).unwrap();
        assert_eq!(buf, buf2);

        file.read_exact_at_volatile(slice, 30).unwrap_err();
        file.read_exact_at_volatile(slice, 32).unwrap_err();
    }

    #[test]
    fn test_write_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let mut buf = [0xfu8; 32];
        let slice1 = unsafe { FileVolatileSlice::new(buf.as_mut_ptr() as *mut u8, buf.len()) };
        file.write_volatile(slice1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        assert_eq!(file.read_volatile(slice).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_volatile(slice).unwrap(), 0);
    }

    #[test]
    fn test_write_vectored_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let mut buf = [0xfu8; 32];
        let slices1 = unsafe {
            [
                FileVolatileSlice::new(buf.as_mut_ptr() as *mut u8, 16),
                FileVolatileSlice::new((buf.as_mut_ptr() as *mut u8).add(16), 16),
            ]
        };
        file.write_vectored_volatile(&slices1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slices = unsafe {
            [
                FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, 16),
                FileVolatileSlice::new((buf2.as_mut_ptr() as *mut u8).add(16), 16),
            ]
        };
        assert_eq!(file.read_vectored_volatile(&slices).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_vectored_volatile(&slices).unwrap(), 0);
    }

    #[test]
    fn test_write_exact_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let mut buf = [0xfu8; 32];
        let slice1 = unsafe { FileVolatileSlice::new(buf.as_mut_ptr() as *mut u8, buf.len()) };
        file.write_all_volatile(slice1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        file.read_exact_volatile(slice).unwrap();
        assert_eq!(buf, buf2);

        file.read_exact_volatile(slice).unwrap_err();
    }

    #[test]
    fn test_write_at_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let mut buf = [0xfu8; 32];
        let slice1 = unsafe { FileVolatileSlice::new(buf.as_mut_ptr() as *mut u8, buf.len()) };
        file.write_volatile(slice1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        assert_eq!(file.read_at_volatile(slice, 0).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_at_volatile(slice, 30).unwrap(), 2);
        assert_eq!(file.read_at_volatile(slice, 32).unwrap(), 0);
    }

    #[test]
    fn test_write_vectored_at_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let mut buf = [0xfu8; 32];
        let slices1 = unsafe {
            [
                FileVolatileSlice::new(buf.as_mut_ptr() as *mut u8, 16),
                FileVolatileSlice::new((buf.as_mut_ptr() as *mut u8).add(16), 16),
            ]
        };
        file.write_vectored_volatile(&slices1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slices = unsafe {
            [
                FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, 16),
                FileVolatileSlice::new((buf2.as_mut_ptr() as *mut u8).add(16), 16),
            ]
        };
        assert_eq!(file.read_vectored_at_volatile(&slices, 0).unwrap(), 32);
        assert_eq!(buf, buf2);

        assert_eq!(file.read_vectored_at_volatile(&slices, 30).unwrap(), 2);
        assert_eq!(file.read_vectored_at_volatile(&slices, 32).unwrap(), 0);
    }

    #[test]
    fn test_write_exact_at_volatile() {
        let mut file = TempFile::new().unwrap().into_file();

        let mut buf = [0xfu8; 32];
        let slice1 = unsafe { FileVolatileSlice::new(buf.as_mut_ptr() as *mut u8, buf.len()) };
        file.write_all_volatile(slice1).unwrap();
        file.seek(SeekFrom::Start(0)).unwrap();

        let mut buf2 = [0x0u8; 32];
        let slice = unsafe { FileVolatileSlice::new(buf2.as_mut_ptr() as *mut u8, buf2.len()) };
        file.read_exact_at_volatile(slice, 0).unwrap();
        assert_eq!(buf, buf2);

        file.read_exact_at_volatile(slice, 30).unwrap_err();
        file.read_exact_at_volatile(slice, 32).unwrap_err();
    }
}
