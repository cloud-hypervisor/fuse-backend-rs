// Copyright (C) 2025 Alibaba Cloud. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Linux credentials helpers for the passthrough file system: thread-scoped
//! uid/gid switching, supplementary groups and the killpriv capability drop.

use std::io;

use log::error;

macro_rules! scoped_cred {
    ($name:ident, $ty:ty, $syscall_nr:expr) => {
        #[derive(Debug)]
        pub(crate) struct $name;

        impl $name {
            // Changes the effective uid/gid of the current thread to `val`.  Changes
            // the thread's credentials back to root when the returned struct is dropped.
            fn new(val: $ty) -> io::Result<Option<$name>> {
                if val == 0 {
                    // Nothing to do since we are already uid 0.
                    return Ok(None);
                }

                // We want credential changes to be per-thread because otherwise
                // we might interfere with operations being carried out on other
                // threads with different uids/gids.  However, posix requires that
                // all threads in a process share the same credentials.  To do this
                // libc uses signals to ensure that when one thread changes its
                // credentials the other threads do the same thing.
                //
                // So instead we invoke the syscall directly in order to get around
                // this limitation.  Another option is to use the setfsuid and
                // setfsgid systems calls.   However since those calls have no way to
                // return an error, it's preferable to do this instead.

                // This call is safe because it doesn't modify any memory and we
                // check the return value.
                let res = unsafe { libc::syscall($syscall_nr, -1, val, -1) };
                if res == 0 {
                    Ok(Some($name))
                } else {
                    Err(io::Error::last_os_error())
                }
            }
        }

        impl Drop for $name {
            fn drop(&mut self) {
                let res = unsafe { libc::syscall($syscall_nr, -1, 0, -1) };
                if res < 0 {
                    error!(
                        "fuse: failed to change credentials back to root: {}",
                        io::Error::last_os_error(),
                    );
                }
            }
        }
    };
}
scoped_cred!(ScopedUid, libc::uid_t, libc::SYS_setresuid);
scoped_cred!(ScopedGid, libc::gid_t, libc::SYS_setresgid);

pub(crate) fn set_creds(
    uid: libc::uid_t,
    gid: libc::gid_t,
) -> io::Result<(Option<ScopedUid>, Option<ScopedGid>)> {
    // We have to change the gid before we change the uid because if we change the uid first then we
    // lose the capability to change the gid.  However changing back can happen in any order.
    ScopedGid::new(gid).and_then(|gid| Ok((ScopedUid::new(uid)?, gid)))
}

/// RAII guard that temporarily adds a supplementary group to the current
/// thread's group list.
///
/// The FUSE_CREATE_SUPP_GROUP extension tells the server which supplementary
/// group of the caller matches the parent directory's group, so that objects
/// created in setgid directories get the correct group ownership.
#[derive(Debug)]
pub(crate) struct ScopedSuppGroups {
    old_groups: Vec<libc::gid_t>,
}

impl ScopedSuppGroups {
    /// Add `supp_gid` to the supplementary group list of the current thread.
    /// Does nothing and returns `None` if `supp_gid` is `None`.  The original
    /// group list is restored when the returned guard is dropped.
    pub(crate) fn new(supp_gid: Option<libc::gid_t>) -> io::Result<Option<Self>> {
        let gid = match supp_gid {
            Some(gid) => gid,
            None => return Ok(None),
        };

        // Save the current supplementary group list.
        let count = unsafe { libc::getgroups(0, std::ptr::null_mut()) };
        if count < 0 {
            return Err(io::Error::last_os_error());
        }
        let mut old_groups = vec![0 as libc::gid_t; count as usize];
        if count > 0 {
            let res = unsafe { libc::getgroups(count, old_groups.as_mut_ptr()) };
            if res < 0 {
                return Err(io::Error::last_os_error());
            }
            old_groups.truncate(res as usize);
        }

        // Like scoped_cred!, invoke the syscall directly so that only the
        // calling thread's credentials are changed.  And setgroups() needs
        // CAP_SETGID, so this must run before set_creds() drops privileges.
        let res = unsafe { libc::syscall(libc::SYS_setgroups, 1, [gid].as_ptr()) };
        if res < 0 {
            return Err(io::Error::last_os_error());
        }

        Ok(Some(ScopedSuppGroups { old_groups }))
    }
}

impl Drop for ScopedSuppGroups {
    fn drop(&mut self) {
        let res = unsafe {
            libc::syscall(
                libc::SYS_setgroups,
                self.old_groups.len(),
                self.old_groups.as_ptr(),
            )
        };
        if res < 0 {
            error!(
                "fuse: failed to restore supplementary groups: {}",
                io::Error::last_os_error(),
            );
        }
    }
}

pub(crate) struct CapFsetid {}

impl Drop for CapFsetid {
    fn drop(&mut self) {
        if let Err(e) = caps::raise(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID) {
            error!("fail to restore thread cap_fsetid: {}", e);
        };
    }
}

pub(crate) fn drop_cap_fsetid() -> io::Result<Option<CapFsetid>> {
    if !caps::has_cap(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID)
        .map_err(|_e| io::Error::new(io::ErrorKind::PermissionDenied, "no CAP_FSETID capability"))?
    {
        return Ok(None);
    }
    caps::drop(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID).map_err(|_e| {
        io::Error::new(
            io::ErrorKind::PermissionDenied,
            "failed to drop CAP_FSETID capability",
        )
    })?;
    Ok(Some(CapFsetid {}))
}
