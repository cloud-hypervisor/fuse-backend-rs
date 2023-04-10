// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE-BSD-3-Clause file.

use std::collections::BTreeMap;
use std::sync::Arc;

use super::file_handle::FileHandle;
use super::{FileOrHandle, Inode, InodeAltKey, InodeData};

#[derive(Default)]
pub struct InodeStore {
    data: BTreeMap<Inode, Arc<InodeData>>,
    by_ids: BTreeMap<InodeAltKey, Inode>,
    by_handle: BTreeMap<Arc<FileHandle>, Inode>,
}

impl InodeStore {
    pub fn insert(&mut self, data: Arc<InodeData>) {
        self.by_ids.insert(data.altkey, data.inode);
        if let FileOrHandle::Handle(handle) = &data.file_or_handle {
            self.by_handle.insert(handle.clone(), data.inode);
        }
        self.data.insert(data.inode, data);
    }

    pub fn remove(&mut self, inode: &Inode) -> Option<Arc<InodeData>> {
        let data = self.data.remove(inode);
        if let Some(data) = data.as_ref() {
            if let FileOrHandle::Handle(handle) = &data.file_or_handle {
                self.by_handle.remove(handle);
            }
            self.by_ids.remove(&data.altkey);
        }
        data
    }

    pub fn clear(&mut self) {
        self.data.clear();
        self.by_handle.clear();
        self.by_ids.clear();
    }

    pub fn get(&self, inode: &Inode) -> Option<&Arc<InodeData>> {
        self.data.get(inode)
    }

    pub fn get_by_ids(&self, ids: &InodeAltKey) -> Option<&Arc<InodeData>> {
        // safe to unwrap, inode must be in data map if found by ids, otherwise unwrap on
        // corruption.
        self.inode_by_ids(ids).map(|inode| self.get(inode).unwrap())
    }

    pub fn get_by_handle(&self, handle: &FileHandle) -> Option<&Arc<InodeData>> {
        // safe to unwrap, inode must be in data map if found by ids, otherwise unwrap on
        // corruption.
        self.inode_by_handle(handle)
            .map(|inode| self.get(inode).unwrap())
    }

    pub fn inode_by_ids(&self, ids: &InodeAltKey) -> Option<&Inode> {
        self.by_ids.get(ids)
    }

    pub fn inode_by_handle(&self, handle: &FileHandle) -> Option<&Inode> {
        self.by_handle.get(handle)
    }
}
