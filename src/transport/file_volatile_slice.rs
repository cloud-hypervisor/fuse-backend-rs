// Copyright (C) 2021 Alibaba Cloud. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause

//! vm-memory 0.6.0 added Bitmap support, which caused some interfaces
//! to not compile with the extra BitmapSlice generic parameter. So added
//! a FileVolatileSlice which is used for volatile access. And mask out
//! BitmapSlice so that FileSystem interfaces don't have to pass BitmapSlice
//! generic parameters.
//! Dirty page tracking is handled in IoBuffers.
use std::io::{Read, Write};
use std::marker::PhantomData;
use std::sync::atomic::Ordering;
use std::{error, fmt, result};

use vm_memory::{
    bitmap::BitmapSlice, volatile_memory::Error as VError, AtomicAccess, Bytes, VolatileSlice,
};

/// `FileVolatileSlice` related errors.
#[allow(missing_docs)]
#[derive(Debug)]
pub enum Error {
    /// `addr` is out of bounds of the volatile memory slice.
    OutOfBounds { addr: usize },
    /// Taking a slice at `base` with `offset` would overflow `usize`.
    Overflow { base: usize, offset: usize },
    /// The error of VolatileSlice.
    VolatileSliceError(VError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::OutOfBounds { addr } => write!(f, "address 0x{:x} is out of bounds", addr),
            Error::Overflow { base, offset } => write!(
                f,
                "address 0x{:x} offset by 0x{:x} would overflow",
                base, offset
            ),
            Error::VolatileSliceError(e) => write!(f, "{}", e),
        }
    }
}

impl error::Error for Error {}

/// Result of volatile memory operations.
pub type Result<T> = result::Result<T, Error>;

/// A adapter in order to mask the BitmapSlice generic parameter.
#[derive(Clone, Copy, Debug)]
pub struct FileVolatileSlice<'a> {
    addr: *mut u8,
    size: usize,
    phantom: PhantomData<&'a u8>,
}

unsafe impl<'a> Sync for FileVolatileSlice<'a> {}

impl<'a> FileVolatileSlice<'a> {
    /// Create a new instance
    ///
    /// # Safety
    /// This function is the same as VolatileSlice::new.
    pub unsafe fn new(addr: *mut u8, size: usize) -> Self {
        Self {
            addr,
            size,
            phantom: PhantomData,
        }
    }

    /// Create a new FileVolatileSlice from VolatileSlice, but don't have bitmap.
    /// The caller needs to ensure that dirty pages are marked.
    pub fn new_from_volatile_slice<S: BitmapSlice>(s: &VolatileSlice<'a, S>) -> Self {
        unsafe { Self::new(s.as_ptr(), s.len()) }
    }

    /// Create a new VolatileSlice
    pub fn as_volatile_slice(&self) -> VolatileSlice<'_, ()> {
        unsafe { VolatileSlice::new(self.as_ptr(), self.len()) }
    }

    /// Returns a pointer to the beginning of the slice.
    pub fn as_ptr(&self) -> *mut u8 {
        self.addr
    }

    /// Gets the size of this slice.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Checks if the slice is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns a subslice of this FileVolatileSlice starting at `offset`.
    pub fn offset(&self, count: usize) -> Result<Self> {
        let new_addr = (self.addr as usize)
            .checked_add(count)
            .ok_or(Error::Overflow {
                base: self.addr as usize,
                offset: count,
            })?;
        let new_size = self
            .size
            .checked_sub(count)
            .ok_or(Error::OutOfBounds { addr: new_addr })?;
        unsafe { Ok(Self::new(new_addr as *mut u8, new_size)) }
    }
}

impl<'a> Bytes<usize> for FileVolatileSlice<'a> {
    type E = VError;

    fn write(&self, buf: &[u8], addr: usize) -> result::Result<usize, Self::E> {
        VolatileSlice::write(&self.as_volatile_slice(), buf, addr)
    }

    fn read(&self, buf: &mut [u8], addr: usize) -> result::Result<usize, Self::E> {
        VolatileSlice::read(&self.as_volatile_slice(), buf, addr)
    }

    fn write_slice(&self, buf: &[u8], addr: usize) -> result::Result<(), Self::E> {
        VolatileSlice::write_slice(&self.as_volatile_slice(), buf, addr)
    }

    fn read_slice(&self, buf: &mut [u8], addr: usize) -> result::Result<(), Self::E> {
        VolatileSlice::write_slice(&self.as_volatile_slice(), buf, addr)
    }

    fn read_from<F>(&self, addr: usize, src: &mut F, count: usize) -> result::Result<usize, Self::E>
    where
        F: Read,
    {
        VolatileSlice::read_from(&self.as_volatile_slice(), addr, src, count)
    }

    fn read_exact_from<F>(
        &self,
        addr: usize,
        src: &mut F,
        count: usize,
    ) -> result::Result<(), Self::E>
    where
        F: Read,
    {
        VolatileSlice::read_exact_from(&self.as_volatile_slice(), addr, src, count)
    }

    fn write_to<F>(&self, addr: usize, dst: &mut F, count: usize) -> result::Result<usize, Self::E>
    where
        F: Write,
    {
        VolatileSlice::write_to(&self.as_volatile_slice(), addr, dst, count)
    }

    fn write_all_to<F>(&self, addr: usize, dst: &mut F, count: usize) -> result::Result<(), Self::E>
    where
        F: Write,
    {
        VolatileSlice::write_all_to(&self.as_volatile_slice(), addr, dst, count)
    }

    fn store<T: AtomicAccess>(
        &self,
        val: T,
        addr: usize,
        order: Ordering,
    ) -> result::Result<(), Self::E> {
        VolatileSlice::store(&self.as_volatile_slice(), val, addr, order)
    }

    fn load<T: AtomicAccess>(&self, addr: usize, order: Ordering) -> result::Result<T, Self::E> {
        VolatileSlice::load(&self.as_volatile_slice(), addr, order)
    }
}
