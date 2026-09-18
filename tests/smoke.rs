// Copyright 2020-2022 Ant Group. All rights reserved.
//
// SPDX-License-Identifier: Apache-2.0
//

#[cfg(all(feature = "fusedev", target_os = "linux"))]
#[macro_use]
extern crate log;

mod example;

#[cfg(all(feature = "fusedev", target_os = "linux"))]
mod fusedev_tests {
    use std::ffi::CString;
    use std::io::Result;
    use std::os::unix::ffi::OsStrExt;
    use std::os::unix::fs::MetadataExt;
    use std::os::unix::fs::PermissionsExt;
    use std::os::unix::process::CommandExt;
    use std::path::Path;
    use std::process::Command;

    use nix::mount::MsFlags;
    use vmm_sys_util::tempdir::TempDir;

    use crate::example::passthroughfs;

    fn validate_two_git_directory(src: &str, dest: &str) -> bool {
        let str = format!(
            "cd {}; git config --global --add safe.directory {}; git ls-files; cd - > /dev/null",
            src, src
        );
        let src_files = exec(str.as_str()).unwrap();
        let str = format!(
            "cd {}; git config --global --add safe.directory {}; git ls-files; cd - > /dev/null",
            dest, dest
        );
        let dest_files = exec(str.as_str()).unwrap();
        if src_files != dest_files {
            error!(
                "src {}:\n{}\ndest {}:\n{}",
                src, src_files, dest, dest_files
            );
            return false;
        }

        let src_md5 = exec(
            format!(
                "cd {}; git ls-files --recurse-submodules | grep --invert-match rust-vmm-ci | xargs md5sum; cd - > /dev/null",
                src
            )
            .as_str(),
        )
        .unwrap();
        let dest_md5 = exec(
            format!(
                "cd {}; git ls-files --recurse-submodules | grep --invert-match rust-vmm-ci | xargs md5sum; cd - > /dev/null",
                dest
            )
            .as_str(),
        )
        .unwrap();
        if src_md5 != dest_md5 {
            error!("src {}:\n{}\ndest {}:\n{}", src, src_md5, dest, dest_md5,);
            return false;
        }

        return true;
    }

    fn exec(cmd: &str) -> Result<String> {
        debug!("exec: {}", cmd);
        let output = Command::new("sh")
            .arg("-c")
            .arg(cmd)
            .env("RUST_BACKTRACE", "1")
            .output()?;

        if !output.status.success() || output.stderr.len() > 0 {
            let msg = std::str::from_utf8(&output.stderr).unwrap();
            panic!("exec failed: {}: {}", cmd, msg);
        }
        let stdout = std::str::from_utf8(&output.stdout).unwrap();

        return Ok(stdout.to_string());
    }

    /// Validates that the mounted filesystem has the expected mount flags
    fn validate_mount_flags(mountpoint: &str, expected_flags: MsFlags) -> bool {
        // Use findmnt to get the mount flags
        let cmd = format!("findmnt -no OPTIONS {}", mountpoint);
        let output = match exec(&cmd) {
            Ok(out) => out,
            Err(_) => return false,
        };

        // Convert the expected flags to a string representation
        let expected_flags_str = msflags_to_string_set(expected_flags);

        // Check if all expected flags are present in the output
        for flag in expected_flags_str {
            if !output.contains(&flag) {
                error!(
                    "Expected flag '{}' not found in mount options: {}",
                    flag, output
                );
                return false;
            }
        }

        true
    }

    /// Converts MsFlags to a set of string representations
    fn msflags_to_string_set(flags: MsFlags) -> Vec<String> {
        let mut result = Vec::new();

        if flags.contains(MsFlags::MS_RDONLY) {
            result.push("ro".to_string());
        }
        if flags.contains(MsFlags::MS_NOSUID) {
            result.push("nosuid".to_string());
        }
        if flags.contains(MsFlags::MS_NODEV) {
            result.push("nodev".to_string());
        }
        if flags.contains(MsFlags::MS_NOEXEC) {
            result.push("noexec".to_string());
        }
        if flags.contains(MsFlags::MS_SYNCHRONOUS) {
            result.push("sync".to_string());
        }
        if flags.contains(MsFlags::MS_NOATIME) {
            result.push("noatime".to_string());
        }

        result
    }

    fn running_as_root() -> bool {
        unsafe { libc::geteuid() == 0 }
    }

    fn kernel_release() -> String {
        std::fs::read_to_string("/proc/sys/kernel/osrelease")
            .map(|release| release.trim().to_string())
            .unwrap_or_else(|_| "unknown".to_string())
    }

    fn kernel_at_least(major: u32, minor: u32) -> bool {
        let release = kernel_release();
        let mut fields = release.split('.');
        match (
            fields.next().and_then(|f| f.parse::<u32>().ok()),
            fields.next().and_then(|f| f.parse::<u32>().ok()),
        ) {
            (Some(kmaj), Some(kmin)) => (kmaj, kmin) >= (major, minor),
            _ => false,
        }
    }

    #[test]
    #[ignore] // it depends on privileged mode to pass through /dev/fuse
    fn integration_test_tree_gitrepo() -> Result<()> {
        // test the fuse-rs repository
        let src = Path::new(".").canonicalize().unwrap();
        let src_dir = src.to_str().unwrap();
        let tmp_dir = TempDir::new().unwrap();
        let mnt_dir = tmp_dir.as_path().to_str().unwrap();
        info!(
            "test passthroughfs src {:?} mountpoint {}",
            src_dir, mnt_dir
        );

        let mut daemon = passthroughfs::Daemon::new(src_dir, mnt_dir, 2).unwrap();
        daemon.mount().unwrap();
        std::thread::sleep(std::time::Duration::from_secs(1));
        assert!(validate_two_git_directory(src_dir, mnt_dir));
        daemon.umount().unwrap();
        Ok(())
    }

    #[test]
    #[ignore]
    fn integration_test_mount_flags() -> Result<()> {
        // Test custom mount flags
        let src = Path::new(".").canonicalize().unwrap();
        let src_dir = src.to_str().unwrap();
        let tmp_dir = TempDir::new().unwrap();
        let mnt_dir = tmp_dir.as_path().to_str().unwrap();
        info!("test mount flags src {:?} mountpoint {}", src_dir, mnt_dir);

        // Create a set of custom mount flags
        let custom_flags = MsFlags::MS_NODEV | MsFlags::MS_NOSUID | MsFlags::MS_NOEXEC;

        let mut daemon = passthroughfs::Daemon::new(src_dir, mnt_dir, 2).unwrap();

        // Set the custom mount flags
        daemon.set_mount_flags(custom_flags);

        // Mount the filesystem
        daemon.mount().unwrap();

        // Wait for the mount to complete
        std::thread::sleep(std::time::Duration::from_millis(100));

        // Validate that the mounted filesystem has the expected flags
        assert!(validate_mount_flags(mnt_dir, custom_flags));

        // Unmount the filesystem
        daemon.umount().unwrap();

        Ok(())
    }

    #[test]
    #[ignore] // it depends on privileged mode to pass through /dev/fuse
    fn integration_test_create_supp_group() -> Result<()> {
        // End-to-end test for FUSE_CREATE_SUPP_GROUP: an unprivileged
        // process creates a file through the FUSE mount inside a setgid
        // directory whose group is only in the creator's supplementary
        // groups.  The kernel (>= 6.3) sends that group in a
        // FUSE_EXT_GROUPS extension, and the server must temporarily
        // adopt it, so that the create succeeds and the new file inherits
        // the group of the setgid directory.  Without the extension the
        // server-side create fails with EACCES, since the server adopts
        // the creator's credentials, which lack the directory's group.
        //
        // It needs root (CAP_SETGID/CAP_CHOWN) and a kernel >= 6.3, both
        // of which the GitHub CI runners provide.
        if !running_as_root() {
            eprintln!("skipping integration_test_create_supp_group: not running as root");
            return Ok(());
        }
        if !kernel_at_least(6, 3) {
            eprintln!(
                "skipping integration_test_create_supp_group: kernel {} does not support FUSE_CREATE_SUPP_GROUP (needs >= 6.3)",
                kernel_release()
            );
            return Ok(());
        }

        // Group of the setgid directory, used as a supplementary group of
        // the unprivileged creator.  It must not be a group of the daemon
        // itself, otherwise the create would succeed without the extension.
        let gid: libc::gid_t = 12345;
        // An unprivileged uid whose primary group differs from `gid`.
        let uid: libc::uid_t = 65534;

        let src_dir = TempDir::new().unwrap();
        let mnt_dir = TempDir::new().unwrap();
        let src = src_dir.as_path().to_str().unwrap().to_string();
        let mnt = mnt_dir.as_path().to_str().unwrap().to_string();

        // Setgid directory owned by root:`gid` with mode 2770: only group
        // members may create entries in it.
        let setgid_dir = src_dir.as_path().join("setgid-dir");
        std::fs::create_dir(&setgid_dir).unwrap();
        let setgid_dir_c = CString::new(setgid_dir.as_os_str().as_bytes()).unwrap();
        assert_eq!(
            unsafe { libc::chown(setgid_dir_c.as_ptr(), 0, gid) },
            0,
            "failed to chown the setgid directory"
        );
        std::fs::set_permissions(&setgid_dir, std::fs::Permissions::from_mode(0o2770)).unwrap();
        // Let the unprivileged creator traverse the mount root.
        std::fs::set_permissions(src_dir.as_path(), std::fs::Permissions::from_mode(0o755))
            .unwrap();

        let mut daemon = passthroughfs::Daemon::new(&src, &mnt, 1).unwrap();
        daemon.mount().unwrap();

        // The creator has `gid` as its only supplementary group and nobody's
        // uid and primary gid, and creates a file in the setgid directory
        // through the FUSE mount.
        let mut cmd = Command::new("touch");
        cmd.arg(format!("{}/setgid-dir/file", mnt));
        unsafe {
            cmd.pre_exec(move || {
                // Add `gid` to the supplementary groups while the process
                // still has CAP_SETGID, then drop all privileges.
                let groups = [gid];
                if libc::setgroups(1, groups.as_ptr()) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                if libc::setresgid(uid, uid, uid) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                if libc::setresuid(uid, uid, uid) < 0 {
                    return Err(std::io::Error::last_os_error());
                }
                Ok(())
            });
        }
        let status = cmd.status().unwrap();
        assert!(
            status.success(),
            "create through the FUSE mount failed: {}",
            status
        );

        // The file must have been created on the source side with the group
        // of the setgid directory.
        let md = std::fs::metadata(src_dir.as_path().join("setgid-dir/file")).unwrap();
        assert_eq!(md.gid(), gid);

        daemon.umount().unwrap();
        Ok(())
    }
}
