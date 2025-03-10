// SPDX-License-Identifier: BSD-3-Clause

use std::io;

use super::util::{dropsupgroups, seteffgid, seteffuid, setsupgroup};

pub struct UnixCredentials {
    uid: libc::uid_t,
    gid: libc::gid_t,
    sup_gid: Option<u32>,
    keep_capability: bool,
}

impl UnixCredentials {
    pub fn new(uid: libc::uid_t, gid: libc::gid_t) -> Self {
        UnixCredentials {
            uid,
            gid,
            sup_gid: None,
            keep_capability: false,
        }
    }

    /// Set a supplementary group. Set `supported_extension` to `false` to signal that a
    /// supplementary group maybe required, but the guest was not able to tell us which,
    /// so we have to rely on keeping the DAC_OVERRIDE capability.
    #[allow(dead_code)]
    pub fn supplementary_gid(self, supported_extension: bool, sup_gid: Option<u32>) -> Self {
        UnixCredentials {
            uid: self.uid,
            gid: self.gid,
            sup_gid,
            keep_capability: !supported_extension,
        }
    }

    /// Changes the effective uid/gid of the current thread to `val`.
    ///
    /// Changes the thread's credentials back to root when the returned struct is dropped.
    pub fn set(self) -> io::Result<Option<UnixCredentialsGuard>> {
        let change_uid = self.uid != 0;
        let change_gid = self.gid != 0;

        // We have to change the gid before we change the uid because if we
        // change the uid first then we lose the capability to change the gid.
        // However changing back can happen in any order.
        if let Some(sup_gid) = self.sup_gid {
            setsupgroup(sup_gid)?;
        }

        if change_gid {
            seteffgid(self.gid)?;
        }

        if change_uid {
            seteffuid(self.uid)?;
        }

        if change_uid && self.keep_capability {
            // Before kernel 6.3, we don't have access to process supplementary groups.
            // To work around this we can set the `DAC_OVERRIDE` in the effective set.
            // We are allowed to set the capability because we only change the effective
            // user ID, so we still have the 'DAC_OVERRIDE' in the permitted set.
            // After switching back to root the permitted set is copied to the effective set,
            // so no additional steps are required.
            if let Err(e) = add_cap_to_eff(caps::Capability::CAP_DAC_OVERRIDE) {
                warn!("failed to add 'DAC_OVERRIDE' to the effective set of capabilities: {e}");
            }
        }

        if !change_uid && !change_gid {
            return Ok(None);
        }

        Ok(Some(UnixCredentialsGuard {
            reset_uid: change_uid,
            reset_gid: change_gid,
            drop_sup_gid: self.sup_gid.is_some(),
        }))
    }
}

pub struct UnixCredentialsGuard {
    reset_uid: bool,
    reset_gid: bool,
    drop_sup_gid: bool,
}

impl Drop for UnixCredentialsGuard {
    fn drop(&mut self) {
        if self.reset_uid {
            seteffuid(0).unwrap_or_else(|e| {
                error!("failed to change uid back to root: {e}");
            });
        }

        if self.reset_gid {
            seteffgid(0).unwrap_or_else(|e| {
                error!("failed to change gid back to root: {e}");
            });
        }

        if self.drop_sup_gid {
            dropsupgroups().unwrap_or_else(|e| {
                error!("failed to drop supplementary groups: {e}");
            });
        }
    }
}

pub struct ScopedCaps {
    capability: caps::Capability,
}

impl Drop for ScopedCaps {
    fn drop(&mut self) {
        if let Err(e) = caps::raise(None, caps::CapSet::Effective, self.capability) {
            error!("fail to restore thread cap_fsetid: {}", e);
        };
    }
}

pub fn scoped_drop_capability(capability: caps::Capability) -> io::Result<Option<ScopedCaps>> {
    if !caps::has_cap(None, caps::CapSet::Effective, capability)
        .map_err(|_e| io::Error::new(io::ErrorKind::PermissionDenied, "no capability"))?
    {
        return Ok(None);
    }
    caps::drop(None, caps::CapSet::Effective, capability).map_err(|_e| {
        io::Error::new(io::ErrorKind::PermissionDenied, "failed to drop capability")
    })?;
    Ok(Some(ScopedCaps { capability }))
}

pub fn drop_cap_fssetid() -> io::Result<Option<ScopedCaps>> {
    scoped_drop_capability(caps::Capability::CAP_FSETID)
}

/// Add a capability to the effective set
///
/// # Errors
/// An error variant will be returned:
/// - if the input string does not match the name, without the 'CAP_' prefix,
/// of any of the capability defined in `linux/capabiliy.h`.
/// - if `capng::get_caps_process()` cannot get the capabilities and bounding set of the process.
/// - if `capng::update()` fails to update the internal posix capabilities settings.
/// - if `capng::apply()` fails to transfer the specified internal posix capabilities
///   settings to the kernel.
pub fn add_cap_to_eff(capability: caps::Capability) -> io::Result<()> {
    caps::raise(None, caps::CapSet::Effective, capability).map_err(|_e| {
        io::Error::new(
            io::ErrorKind::PermissionDenied,
            "failed to raise capability",
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use nix::unistd::getuid;

    #[test]
    fn test_unix_credentials_set() {
        if getuid().is_root() {
            let cred = UnixCredentials::new(0, 0).set().unwrap();
            assert!(cred.is_none());
            drop(cred);

            let cred = UnixCredentials::new(1, 1);
            let cred = cred.supplementary_gid(false, Some(2));
            let guard = cred.set().unwrap();
            assert!(guard.is_some());
            drop(guard);
        }
    }

    #[test]
    fn test_drop_cap_fssetid() {
        let cap = drop_cap_fssetid().unwrap();
        let has_cap =
            caps::has_cap(None, caps::CapSet::Effective, caps::Capability::CAP_FSETID).unwrap();
        assert_eq!(has_cap, false);
        drop(cap);
    }

    #[test]
    fn test_add_cap_to_eff() {
        if getuid().is_root() {
            add_cap_to_eff(caps::Capability::CAP_DAC_OVERRIDE).unwrap();
        }
    }
}
