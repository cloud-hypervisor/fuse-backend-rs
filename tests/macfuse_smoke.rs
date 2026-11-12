// Copyright 2020-2022 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

#[cfg(all(feature = "fusedev", feature = "fuse-t", target_os = "macos"))]
#[macro_use]
extern crate log;

mod example;

#[cfg(all(feature = "fusedev", feature = "fuse-t", target_os = "macos"))]
mod macfuse_tests {
    use std::io::Result;
    use std::os::unix::fs::MetadataExt;
    use std::process::Command;

    use vmm_sys_util::tempdir::TempDir;

    use crate::example::macfuse;
    use crate::example::passthroughfs;

    fn validate_hello_file(dest: &str) -> bool {
        let files = exec(format!("cd {}; ls -la .;cd - > /dev/null", dest).as_str()).unwrap();
        if files.find("hello").is_none() {
            error!("files {}:\n not include hello \n", files);
            return false;
        }
        println!("files: {}", files);

        let content = exec(format!("cat {}/hello;", dest).as_str()).unwrap();
        if !content.eq("hello, fuse") {
            error!("content {}:\n is not right\n", content);
            return false;
        }

        true
    }

    fn exec(cmd: &str) -> Result<String> {
        debug!("exec: {}", cmd);
        let output = Command::new("sh")
            .arg("-c")
            .arg(cmd)
            .env("RUST_BACKTRACE", "1")
            .output()?;

        if !output.status.success() || !output.stderr.is_empty() {
            let msg = std::str::from_utf8(&output.stderr).unwrap();
            panic!("exec failed: {}: {}", cmd, msg);
        }
        let stdout = std::str::from_utf8(&output.stdout).unwrap();

        Ok(stdout.to_string())
    }

    #[test]
    #[cfg(feature = "fuse-t")]
    fn integration_test_macfuse_hello() -> Result<()> {
        // test the fuse-rs repository
        let tmp_dir = TempDir::new().unwrap();
        let mnt_dir = tmp_dir.as_path().to_str().unwrap();
        info!("test macfuse mountpoint {}", mnt_dir);

        let mut daemon = macfuse::Daemon::new(mnt_dir, 2).unwrap();
        daemon.mount().unwrap();
        assert!(validate_hello_file(mnt_dir));
        daemon.umount().unwrap();
        Ok(())
    }

    #[test]
    #[cfg(feature = "fuse-t")]
    fn integration_test_macfuse_passthrough() -> Result<()> {
        let src_dir = TempDir::new().unwrap();
        let mnt_dir = TempDir::new().unwrap();
        let src = src_dir.as_path().to_str().unwrap();
        let mnt = mnt_dir.as_path().to_str().unwrap();
        info!("test passthroughfs src {} mountpoint {}", src, mnt);

        // Backing files to look for through the mount.
        std::fs::write(format!("{}/hello", src), "hello, fuse").unwrap();
        std::fs::create_dir(format!("{}/dir", src)).unwrap();

        let mut daemon = passthroughfs::Daemon::new(src, mnt, 2).unwrap();
        daemon.mount().unwrap();

        // readdir: the mount exposes the backing directory.
        let files = exec(format!("ls {}", mnt).as_str()).unwrap();
        assert!(files.find("hello").is_some(), "files: {}", files);
        assert!(files.find("dir").is_some(), "files: {}", files);

        // read (through the F_GETPATH reopen hub): the content matches.
        let content = exec(format!("cat {}/hello", mnt).as_str()).unwrap();
        assert!(content.eq("hello, fuse"), "content: {}", content);

        // write and create through the mount.
        exec(format!("echo written > {}/new.txt", mnt).as_str()).unwrap();
        let content = std::fs::read_to_string(format!("{}/new.txt", src)).unwrap();
        assert_eq!(content.trim(), "written");

        // xattr: set, list, and read through the mount land on the backing
        // file (ENOATTR for a missing attribute round-trips too).
        exec(format!("xattr -w user.e2e v {}/hello", mnt).as_str()).unwrap();
        let xattrs = exec(format!("xattr -l {}/hello", mnt).as_str()).unwrap();
        assert!(xattrs.find("user.e2e").is_some(), "xattrs: {}", xattrs);
        let value = exec(format!("xattr -p user.e2e {}/hello", mnt).as_str()).unwrap();
        assert!(value.trim().eq("v"), "value: {}", value);

        // link-by-fd: a hard link through the mount shares the backing inode.
        exec(format!("ln {}/hello {}/hello.lnk", mnt, mnt).as_str()).unwrap();
        let md = std::fs::metadata(format!("{}/hello", src)).unwrap();
        let md_lnk = std::fs::metadata(format!("{}/hello.lnk", src)).unwrap();
        assert_eq!(md.ino(), md_lnk.ino());
        assert_eq!(md_lnk.nlink(), 2);

        daemon.umount().unwrap();
        Ok(())
    }
}
