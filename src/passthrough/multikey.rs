// Copyright 2019 The Chromium OS Authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

//! Struct MultikeyBTreeMap implementation used by passthrough.

use std::collections::BTreeMap;
use std::ops::DerefMut;
use std::sync::{Arc, Mutex};

use super::{Inode, InodeAltKey, InodeData};

/// A BTreeMap that supports 2 types of keys per value. All the usual restrictions and warnings for
/// `std::collections::BTreeMap` also apply to this struct. Additionally, there is a 1:n
/// relationship between the 2 key types: For each `K1` in the map, any number of `K2` may exist;
/// but each `K2` only has exactly one `K1` associated with it.
#[derive(Default)]
pub struct MultikeyBTreeMap {
    // We need to keep a copy of the second keys in the main map so that we can remove entries using
    // just the main key. Otherwise we would require the caller to provide all keys when calling
    // `remove`.
    main: BTreeMap<Inode, Arc<InodeData>>,
    alt: BTreeMap<Arc<InodeAltKey>, Inode>,
}

impl MultikeyBTreeMap {
    /// Create a new empty MultikeyBTreeMap.
    pub fn new() -> Self {
        MultikeyBTreeMap {
            main: BTreeMap::default(),
            alt: BTreeMap::default(),
        }
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of `K1``, but the ordering on the borrowed form must match
    /// the ordering on `K1`.
    pub(super) fn get(&self, key: Inode) -> Option<&Arc<InodeData>> {
        self.main.get(&key)
    }

    /// Returns a reference to the value corresponding to an alternate key.
    ///
    /// The key may be any borrowed form of the `K2``, but the ordering on the borrowed form must
    /// match the ordering on `K2`.
    ///
    /// Note that this method performs 2 lookups: one to get the main key and another to get the
    /// value associated with that key. For best performance callers should prefer the `get` method
    /// over this method whenever possible as `get` only needs to perform one lookup.
    pub(super) fn get_alt(&self, key: &Arc<InodeAltKey>) -> Option<&Arc<InodeData>> {
        if let Some(k) = self.alt.get(key) {
            self.get(*k)
        } else {
            None
        }
    }

    /// Inserts a new entry into the map with the given main key and value.
    ///
    /// If there already was an entry present with the given key, then the value is updated,
    /// all alternate keys pointing to the main key are removed, and the old value is returned.
    /// Otherwise, returns `None`.
    pub(super) fn insert(&mut self, k1: Inode, v: Arc<InodeData>) -> Option<Arc<InodeData>> {
        self.main.insert(k1, v).map(|old_v| {
            self.remove_alt_keys(&old_v);
            old_v
        })
    }

    /// Adds an alternate key for an existing main key.
    ///
    /// If the given alternate key was present already, then the main key it points to is updated,
    /// and that previous main key is returned.
    /// Otherwise, returns `None`.
    pub(super) fn insert_alt(&mut self, k2: Arc<InodeAltKey>, k1: Inode) -> Option<Inode> {
        let old_inode = self.alt.insert(k2.clone(), k1).map(|k| {
            if let Some(old_v) = self.main.get(&k) {
                old_v.multi_key_state.remove_alt_key(&k2);
            }
            k
        });

        // `k1` must exist, so we can .unwrap()
        self.main
            .get(&k1)
            .unwrap()
            .multi_key_state
            .insert_alt_key(k2);

        old_inode
    }

    /// Remove a key from the map, returning the value associated with that key if it was previously
    /// in the map.
    ///
    /// The key may be any borrowed form of `K1``, but the ordering on the borrowed form must match
    /// the ordering on `K1`.
    pub(super) fn remove(&mut self, key: Inode) -> Option<Arc<InodeData>> {
        self.main.remove(&key).map(|v| {
            self.remove_alt_keys(&v);
            v
        })
    }

    fn remove_alt_keys(&mut self, v: &Arc<InodeData>) {
        let mut guard = v.multi_key_state.alt_keys.lock().unwrap();
        for k2 in guard.deref_mut() {
            if k2.is_valid() {
                self.alt.remove(k2);
                *k2 = Arc::new(InodeAltKey::default());
            }
        }
    }

    /// Clears the map, removing all values.
    pub(super) fn clear(&mut self) {
        self.alt.clear();
        self.main.clear()
    }
}

pub struct MultiKeyState {
    alt_keys: Mutex<[Arc<InodeAltKey>; 2]>,
}

impl MultiKeyState {
    pub(super) fn new() -> Self {
        let key = Arc::new(InodeAltKey::default());

        Self {
            alt_keys: Mutex::new([key.clone(), key]),
        }
    }

    fn insert_alt_key(&self, key: Arc<InodeAltKey>) {
        let mut guard = self.alt_keys.lock().unwrap();
        for idx in 0..2 {
            if !guard[idx].is_valid() {
                guard[idx] = key;
                return;
            }
        }
        panic!("too many alt keys");
    }

    fn remove_alt_key(&self, key: &Arc<InodeAltKey>) {
        let mut guard = self.alt_keys.lock().unwrap();
        for idx in 0..2 {
            if &guard[idx] == key {
                guard[idx] = Arc::new(InodeAltKey::default());
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::passthrough::file_handle::CFileHandle;
    use crate::passthrough::{FileHandle, FileOrHandle};

    #[test]
    fn get() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));

        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let data = m.get(k1).expect("failed to look up main key");
        assert_eq!(data.inode, val.inode);
        let data = m.get_alt(&k2).expect("failed to look up alt key");
        assert_eq!(data.inode, val.inode);
    }

    #[test]
    fn get_multi_alt() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2a = Arc::new(InodeAltKey::Handle(handle.clone()));
        let k2b = Arc::new(InodeAltKey::Ids {
            ino: 5,
            dev: 1,
            mnt: 5,
        });
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));

        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2a.clone(), k1).is_none());
        assert!(m.insert_alt(k2b.clone(), k1).is_none());

        let data = m.get_alt(&k2a).expect("failed to look up alt key A");
        assert_eq!(data.inode, val.inode);
        let data = m.get_alt(&k2b).expect("failed to look up alt key A");
        assert_eq!(data.inode, val.inode);
    }

    #[test]
    fn update_main_key() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let new_k1 = 0x3add_f8f8_c7c5_df5e;
        let val2 = Arc::new(InodeData::new(
            100,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(new_k1, val2.clone()).is_none());
        let old_key = m
            .insert_alt(k2.clone(), new_k1)
            .expect("failed to update main key to which alt key points");
        assert_eq!(old_key, k1);
        let data = m.remove(k1).expect("failed to remove old main key");
        assert!(m.get(k1).is_none());
        assert_eq!(data.inode, val.inode);
        for entry in data.multi_key_state.alt_keys.lock().unwrap().iter() {
            assert!(!entry.is_valid());
        }

        let data = m.get(new_k1).expect("failed to look up main key");
        assert_eq!(data.inode, val2.inode);
        let data = m.get_alt(&k2).expect("failed to look up alt key");
        assert_eq!(data.inode, val2.inode);
    }

    #[test]
    fn update_alt_key() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let new_k2 = Arc::new(InodeAltKey::Ids {
            ino: 5,
            dev: 1,
            mnt: 5,
        });
        let val2 = Arc::new(InodeData::new(
            100,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        let data = m.insert(k1, val2.clone()).expect("failed to update value");
        assert_eq!(data.inode, val.inode);
        assert!(m.insert_alt(new_k2.clone(), k1).is_none());

        // Updating a main key invalidates all its alt keys
        assert!(m.get_alt(&k2).is_none());
        let data = m.get(k1).expect("failed to look up main key");
        assert_eq!(data.inode, val2.inode);
        let data = m.get_alt(&new_k2).expect("failed to look up alt key");
        assert_eq!(data.inode, val2.inode);
    }

    #[test]
    fn update_value() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let val2 = Arc::new(InodeData::new(
            100,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        let data = m
            .insert(k1, val2.clone())
            .expect("failed to update alt key");
        assert_eq!(data.inode, val.inode);
        // Updating a main key invalidates all its alt keys
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let data = m.get(k1).expect("failed to look up main key");
        assert_eq!(data.inode, val2.inode);
        let data = m.get_alt(&k2).expect("failed to look up alt key");
        assert_eq!(data.inode, val2.inode);
    }

    #[test]
    fn update_both_keys_main() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let new_k1 = 0xc980_587a_24b3_ae30;
        let new_k2 = Arc::new(InodeAltKey::Ids {
            ino: 5,
            dev: 1,
            mnt: 5,
        });
        let val2 = Arc::new(InodeData::new(
            100,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(new_k1, val2.clone()).is_none());
        assert!(m.insert_alt(new_k2.clone(), new_k1).is_none());

        let val3 = Arc::new(InodeData::new(
            200,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        let data = m
            .insert(k1, val3.clone())
            .expect("failed to update main key");
        assert_eq!(data.inode, val.inode);
        let data = m
            .insert_alt(new_k2.clone(), k1)
            .expect("failed to update alt key");
        assert_eq!(data, new_k1);

        // We did not touch new_k1, so it should still be there
        let data = m.get(new_k1).expect("failed to look up main key");
        assert_eq!(data.inode, val2.inode);

        // However, we did update k1, which removed its associated alt keys
        assert!(m.get_alt(&k2).is_none());

        let data = m.get(k1).expect("failed to look up main key");
        assert_eq!(data.inode, val3.inode);
        let data = m.get_alt(&new_k2).expect("failed to look up alt key");
        assert_eq!(data.inode, val3.inode);
    }

    #[test]
    fn update_both_keys_alt() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let new_k1 = 0xc980_587a_24b3_ae30;
        let new_k2 = Arc::new(InodeAltKey::Ids {
            ino: 5,
            dev: 1,
            mnt: 5,
        });
        let val2 = Arc::new(InodeData::new(
            100,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(new_k1, val2.clone()).is_none());
        assert!(m.insert_alt(new_k2.clone(), new_k1).is_none());

        let val3 = Arc::new(InodeData::new(
            200,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        let data = m
            .insert(new_k1, val3.clone())
            .expect("failed to update main key");
        assert_eq!(data.inode, val2.inode);
        let data = m
            .insert_alt(k2.clone(), new_k1)
            .expect("failed to update alt key");
        assert_eq!(data, k1);

        // We did not touch k1, so it should still be there
        let data = m.get(k1).expect("failed to look up first main key");
        assert_eq!(data.inode, val.inode);

        // However, we did update new_k1, which removed its associated alt keys
        assert!(m.get_alt(&new_k2).is_none());

        let data = m.get(new_k1).expect("failed to look up main key");
        assert_eq!(data.inode, val3.inode);
        let data = m.get_alt(&k2).expect("failed to look up alt key");
        assert_eq!(data.inode, val3.inode);
    }

    #[test]
    fn remove() {
        let mut m = MultikeyBTreeMap::new();
        let k1 = 0xc6c8_f5e0_b13e_ed40;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2 = Arc::new(InodeAltKey::Handle(handle.clone()));
        let val = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        assert!(m.insert(k1, val.clone()).is_none());
        assert!(m.insert_alt(k2.clone(), k1).is_none());

        let data = m.remove(k1).expect("failed to remove entry");
        assert_eq!(data.inode, val.inode);
        assert!(m.get(k1).is_none());
        assert!(m.get_alt(&k2).is_none());
    }

    #[test]
    fn remove_multi() {
        let mut m = MultikeyBTreeMap::new();
        let k1a = 0xc6c8_f5e0_b13e_ed40;
        let k1b = 0x3add_f8f8_c7c5_df5e;
        let handle = Arc::new(FileHandle {
            mnt_id: 1,
            handle: CFileHandle::new(128),
        });
        let k2a = Arc::new(InodeAltKey::Handle(handle.clone()));
        let k2b = Arc::new(InodeAltKey::Ids {
            ino: 5,
            dev: 1,
            mnt: 5,
        });
        let val_a = Arc::new(InodeData::new(
            5,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));
        let val_b = Arc::new(InodeData::new(
            100,
            FileOrHandle::Handle(handle.clone()),
            1,
            libc::S_IFREG,
        ));

        assert!(m.insert(k1a, val_a.clone()).is_none());
        assert!(m.insert_alt(k2a.clone(), k1a).is_none());
        assert!(m.insert_alt(k2b.clone(), k1a).is_none());
        assert!(m.insert(k1b, val_b.clone()).is_none());

        let data = m
            .insert_alt(k2b.clone(), k1b)
            .expect("failed to make second alt key point to second main key");
        assert_eq!(data, k1a);

        let data = m.remove(k1a).expect("failed to remove first main key");
        assert_eq!(data.inode, val_a.inode);
        assert!(m.get(k1a).is_none());
        assert!(m.get_alt(&k2a).is_none());

        let data = m.get(k1b).expect("failed to get second main key");
        assert_eq!(data.inode, val_b.inode);
        let data = m.get_alt(&k2b).expect("failed to get second alt key");
        assert_eq!(data.inode, val_b.inode);
    }
}
