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
    use std::os::unix::fs::{MetadataExt, PermissionsExt};
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

    /// Like `exec`, but a failure is an `Err` instead of a panic — for steps
    /// whose acceptable outcome depends on kernel-side behavior. Unlike
    /// `exec`, stderr on success is not treated as a failure.
    fn try_exec(cmd: &str) -> Result<String> {
        debug!("exec: {}", cmd);
        let output = Command::new("sh")
            .arg("-c")
            .arg(cmd)
            .env("RUST_BACKTRACE", "1")
            .output()?;

        if !output.status.success() {
            let msg = String::from_utf8_lossy(&output.stderr);
            return Err(std::io::Error::other(format!("{}: {}", cmd, msg)));
        }
        Ok(String::from_utf8_lossy(&output.stdout).to_string())
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
        // file. fuse-t 1.2.9 doesn't send xattrs to the daemon. macOS keeps
        // them in an AppleDouble `._hello` file instead and reports any
        // failure there as EPERM, so on fuse-t these steps test macOS, not
        // PassthroughFs. They stay for a macFUSE build of this test, though
        // the test builds only with fuse-t today.
        if cfg!(feature = "fuse-t") {
            println!("xattr: skipped, fuse-t doesn't send xattrs to the daemon");
        } else {
            exec(format!("xattr -w user.e2e v {}/hello", mnt).as_str()).unwrap();
            let xattrs = exec(format!("xattr -l {}/hello", mnt).as_str()).unwrap();
            assert!(xattrs.find("user.e2e").is_some(), "xattrs: {}", xattrs);
            let value = exec(format!("xattr -p user.e2e {}/hello", mnt).as_str()).unwrap();
            assert!(value.trim().eq("v"), "value: {}", value);
            // Reading a missing attribute through the mount must fail. The
            // only success path would be serving data for an attribute the
            // daemon answered ENOATTR for. The error text also records which
            // errno the transport forwarded, the one part the shim tests
            // cannot observe.
            let e = try_exec(format!("xattr -p user.e2e.missing {}/hello", mnt).as_str())
                .expect_err("missing-attribute read through the mount must fail");
            println!("enoattr through mount: {}", e);
        }

        // link-by-fd: a hard link through the mount shares the backing inode.
        exec(format!("ln {}/hello {}/hello.lnk", mnt, mnt).as_str()).unwrap();
        let md = std::fs::metadata(format!("{}/hello", src)).unwrap();
        let md_lnk = std::fs::metadata(format!("{}/hello.lnk", src)).unwrap();
        assert_eq!(md.ino(), md_lnk.ino());
        assert_eq!(md_lnk.nlink(), 2);

        // Handle-less setattr (the kernel passes no fh for chmod/touch): both
        // must land on the backing file through the pinned descriptor. Pin a
        // known mode first — under a 0xx umask `fs::write` creates the file
        // already 0600, and a no-op setattr would then pass the assert.
        std::fs::set_permissions(
            format!("{}/hello", src),
            std::fs::Permissions::from_mode(0o644),
        )
        .unwrap();
        exec(format!("chmod 0600 {}/hello", mnt).as_str()).unwrap();
        let mode = std::fs::metadata(format!("{}/hello", src))
            .unwrap()
            .permissions()
            .mode();
        assert_eq!(mode & 0o777, 0o600, "mode: {:o}", mode);
        // `touch -t` interprets its argument in local time, so only assert a
        // coarse pre-2001 bound that holds in every timezone on Earth.
        exec(format!("touch -t 200001010000 {}/new.txt", mnt).as_str()).unwrap();
        let mtime = std::fs::metadata(format!("{}/new.txt", src))
            .unwrap()
            .mtime();
        assert!(mtime < 1_000_000_000, "mtime: {}", mtime);

        // Stale reopen: with the inode pinned by the mount, replace the
        // backing file behind its back. The next open through the mount must
        // either fail (ESTALE) or see the new file — never the old content.
        exec(format!("echo stale > {}/stale.txt", mnt).as_str()).unwrap();
        let content = exec(format!("cat {}/stale.txt", mnt).as_str()).unwrap();
        assert_eq!(content.trim(), "stale");
        std::fs::remove_file(format!("{}/stale.txt", src)).unwrap();
        std::fs::write(format!("{}/stale.txt", src), "replaced").unwrap();
        match try_exec(format!("cat {}/stale.txt", mnt).as_str()) {
            Ok(content) => {
                assert_eq!(content.trim(), "replaced", "served stale content");
                println!("stale-reopen: healed (transport re-looked-up the name)");
            }
            // `println!`, not `info!`: no logger is initialized in this
            // binary, and which way the transport goes — self-healing or a
            // caller-visible error — is behavior the test deliberately does
            // not assert.
            Err(e) => println!("stale-reopen: rejected (error surfaced to caller: {})", e),
        }

        daemon.umount().unwrap();
        Ok(())
    }
}
