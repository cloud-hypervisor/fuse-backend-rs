// SPDX-License-Identifier: Apache-2.0

//! Checks that `set_runtime_type()` says why io-uring isn't available. A seccomp filter makes
//! `io_uring_setup()` fail with `EPERM` on the test's thread. The crate fixes the runtime type
//! once per process, so this test runs in a binary of its own.

#[cfg(all(target_os = "linux", feature = "async-io"))]
#[test]
fn test_set_runtime_type_reports_probe_error() {
    use fuse_backend_core::async_runtime::{self, RuntimeType};

    // Return EPERM from io_uring_setup() and allow every other syscall.
    let mut filter = [
        libc::sock_filter {
            code: (libc::BPF_LD | libc::BPF_W | libc::BPF_ABS) as u16,
            jt: 0,
            jf: 0,
            k: 0, // offsetof(struct seccomp_data, nr)
        },
        libc::sock_filter {
            code: (libc::BPF_JMP | libc::BPF_JEQ | libc::BPF_K) as u16,
            jt: 0,
            jf: 1,
            k: libc::SYS_io_uring_setup as u32,
        },
        libc::sock_filter {
            code: (libc::BPF_RET | libc::BPF_K) as u16,
            jt: 0,
            jf: 0,
            k: libc::SECCOMP_RET_ERRNO | libc::EPERM as u32,
        },
        libc::sock_filter {
            code: (libc::BPF_RET | libc::BPF_K) as u16,
            jt: 0,
            jf: 0,
            k: libc::SECCOMP_RET_ALLOW,
        },
    ];
    let prog = libc::sock_fprog {
        len: filter.len() as u16,
        filter: filter.as_mut_ptr(),
    };
    // SAFETY: `prog` points to a valid filter that outlives the calls, and the filter only
    // affects this thread.
    let filtered = unsafe {
        assert_eq!(libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0), 0);
        libc::prctl(
            libc::PR_SET_SECCOMP,
            libc::SECCOMP_MODE_FILTER,
            &prog as *const libc::sock_fprog,
        ) == 0
    };
    // QEMU's user mode emulation and kernels without seccomp filters refuse the filter.
    if !filtered {
        eprintln!(
            "can't install a seccomp filter ({}), skipping",
            std::io::Error::last_os_error()
        );
        return;
    }

    let err = async_runtime::set_runtime_type(RuntimeType::Uring).unwrap_err();
    assert_eq!(err.kind(), std::io::ErrorKind::PermissionDenied);
    assert!(
        err.to_string().starts_with("io-uring isn't available: "),
        "{}",
        err
    );
    assert_eq!(async_runtime::runtime_type(), RuntimeType::Tokio);
}
