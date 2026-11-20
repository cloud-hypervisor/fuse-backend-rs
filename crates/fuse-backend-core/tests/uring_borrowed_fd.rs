// SPDX-License-Identifier: Apache-2.0

//! The crate fixes the runtime type once per process, and the allocator below counts the
//! allocations of the whole process, so this test runs in a binary of its own.

#![cfg(all(feature = "async-io", target_os = "linux"))]

use std::alloc::{GlobalAlloc, Layout, System};
use std::os::unix::io::AsRawFd;
use std::sync::atomic::{AtomicIsize, Ordering};
use std::sync::Arc;

use fuse_backend_core::async_file::File;
use fuse_backend_core::async_runtime::{self, RuntimeType};
use fuse_backend_core::file_buf::FileVolatileBuf;

/// Counts the bytes the process has allocated and not freed yet.
struct LiveBytes;

static LIVE: AtomicIsize = AtomicIsize::new(0);

unsafe impl GlobalAlloc for LiveBytes {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        LIVE.fetch_add(layout.size() as isize, Ordering::Relaxed);
        System.alloc(layout)
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        LIVE.fetch_sub(layout.size() as isize, Ordering::Relaxed);
        System.dealloc(ptr, layout)
    }
}

#[global_allocator]
static ALLOCATOR: LiveBytes = LiveBytes;

#[test]
fn test_borrowed_fd_uring_io_frees_its_memory() {
    if let Err(e) = async_runtime::set_runtime_type(RuntimeType::Uring) {
        eprintln!("io_uring isn't available ({}), skipping", e);
        return;
    }
    let owner = tempfile::tempfile().unwrap();
    let file = File::borrow_fd(owner.as_raw_fd(), Arc::new(()));
    let mut mem = [0u8; 8];

    async_runtime::block_on(async {
        // Let the runtime grow its tables first.
        for _ in 0..100 {
            read_and_write(&file, &mut mem).await;
        }
        let before = LIVE.load(Ordering::Relaxed);
        for _ in 0..1000 {
            read_and_write(&file, &mut mem).await;
        }
        let grown = LIVE.load(Ordering::Relaxed) - before;
        // Each of these 4000 IOs used to leak an `Rc` of 56 bytes.
        assert!(grown < 4096, "4000 IOs left {} bytes allocated", grown);
    });
}

/// Write `mem` to `file` and read it back, plainly and vectored.
async fn read_and_write(file: &File, mem: &mut [u8; 8]) {
    let buf = unsafe { FileVolatileBuf::new_with_data(mem, 8) };
    assert_eq!(file.async_write_at(buf, 0).await.0.unwrap(), 8);
    let buf = unsafe { FileVolatileBuf::new(mem) };
    assert_eq!(file.async_read_at(buf, 0).await.0.unwrap(), 8);
    let bufs = vec![unsafe { FileVolatileBuf::new_with_data(mem, 8) }];
    assert_eq!(file.async_writev_at(bufs, 0).await.0.unwrap(), 8);
    let bufs = vec![unsafe { FileVolatileBuf::new(mem) }];
    assert_eq!(file.async_readv_at(bufs, 0).await.0.unwrap(), 8);
}
