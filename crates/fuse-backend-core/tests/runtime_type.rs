// SPDX-License-Identifier: Apache-2.0

//! The crate fixes the runtime type once per process, so this test runs in a binary of its own.

#[cfg(feature = "async-io")]
#[test]
fn test_set_runtime_type() {
    use fuse_backend_core::async_file::File;
    use fuse_backend_core::async_runtime::{self, Runtime, RuntimeType};

    async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();
    assert_eq!(async_runtime::runtime_type(), RuntimeType::Tokio);
    // Asking for the type in effect again succeeds.
    async_runtime::set_runtime_type(RuntimeType::Tokio).unwrap();
    // The type can't change once it is fixed.
    #[cfg(target_os = "linux")]
    assert!(async_runtime::set_runtime_type(RuntimeType::Uring).is_err());

    assert!(matches!(Runtime::new(), Runtime::Tokio(..)));
    let file = File::from_std_file(std::fs::File::open("/dev/null").unwrap());
    assert!(matches!(file, File::Tokio(_)));
}
