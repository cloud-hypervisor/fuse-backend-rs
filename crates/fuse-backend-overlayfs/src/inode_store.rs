// Copyright (C) 2023 Ant Group. All rights reserved.
// SPDX-License-Identifier: Apache-2.0

use std::io::{Error, Result};
use std::{
    collections::HashMap,
    sync::{atomic::Ordering, Arc, Weak},
};

use super::{Inode, OverlayInode, VFS_MAX_INO};

use radix_trie::Trie;

// One directory entry of a multi-linked inode: (parent, name, path).
pub(crate) type HardLink = (Weak<OverlayInode>, String, String);

pub struct InodeStore {
    // Active inodes.
    inodes: HashMap<Inode, Arc<OverlayInode>>,
    // Deleted inodes which were unlinked but have non zero lookup count.
    deleted: HashMap<Inode, Arc<OverlayInode>>,
    // Path to inode mapping, used to reserve inode number for same path.
    path_mapping: Trie<String, Inode>,
    // Backend identity (layer, real inode) to overlay inode mapping. Only
    // files with multiple hard links are recorded here, so that all links
    // of such a file resolve to the same overlay inode number.
    real_index: HashMap<(usize, u64), Inode>,
    // Extra hard links of multi-linked inodes. Only files with multiple
    // directory entries show up here, so single-link inodes (the common
    // case) don't pay any memory overhead.
    extra_links: HashMap<Inode, Vec<HardLink>>,
    next_inode: u64,
}

impl InodeStore {
    pub(crate) fn new() -> Self {
        Self {
            inodes: HashMap::new(),
            deleted: HashMap::new(),
            path_mapping: Trie::new(),
            real_index: HashMap::new(),
            extra_links: HashMap::new(),
            next_inode: 1,
        }
    }

    pub(crate) fn alloc_unique_inode(&mut self) -> Result<Inode> {
        // Iter VFS_MAX_INO times to find a free inode number.
        let mut ino = self.next_inode;
        for _ in 0..VFS_MAX_INO {
            if ino > VFS_MAX_INO {
                ino = 1;
            }
            if !self.inodes.contains_key(&ino) && !self.deleted.contains_key(&ino) {
                self.next_inode = ino + 1;
                return Ok(ino);
            }
            ino += 1;
        }
        error!("reached maximum inode number: {}", VFS_MAX_INO);
        Err(Error::other(format!(
            "maximum inode number {} reached",
            VFS_MAX_INO
        )))
    }

    pub(crate) fn alloc_inode(&mut self, path: &String) -> Result<Inode> {
        match self.path_mapping.get(path) {
            // If the path is already in the mapping, return the reserved inode number.
            Some(v) => {
                // Unless the number still belongs to a deferred inode:
                // the kernel keeps references to it with FORGETs still
                // pending, and handing the number to a new node, e.g. the
                // whiteout placeholder do_rm() installs for the removed
                // name, would let those forgets tear the new node down.
                // A number owned by a live inode is still returned:
                // reloading a hard link relies on it to find the inode
                // shared with its other links.
                if self.deleted.contains_key(v) {
                    self.alloc_unique_inode()
                } else {
                    Ok(*v)
                }
            }
            // Or allocate a new inode number.
            None => self.alloc_unique_inode(),
        }
    }

    pub(crate) fn insert_inode(&mut self, inode: Inode, node: Arc<OverlayInode>) {
        self.path_mapping.insert(node.path.clone(), inode);
        self.inodes.insert(inode, node);
    }

    // Record a path to inode mapping without touching the inode table,
    // e.g. an extra hard link path of an existing inode.
    pub(crate) fn insert_path(&mut self, path: &str, inode: Inode) {
        self.path_mapping.insert(path.to_string(), inode);
    }

    // Drop a path to inode mapping, e.g. when one hard link of a
    // multi-linked inode is removed.
    pub(crate) fn remove_path(&mut self, path: &str) {
        self.path_mapping.remove(path);
    }

    // Register an extra hard link for an inode. Re-registering an
    // existing path (e.g. the parent directory was evicted and reloaded)
    // replaces the stale entry instead of accumulating duplicates, and
    // refreshes the parent reference to the live directory.
    pub(crate) fn add_link(&mut self, inode: Inode, link: HardLink) {
        let links = self.extra_links.entry(inode).or_default();
        if let Some(pos) = links.iter().position(|(_, _, p)| *p == link.2) {
            links[pos] = link;
        } else {
            links.push(link);
        }
    }

    // Query the extra hard links of an inode.
    pub(crate) fn get_links(&self, inode: Inode) -> Option<&Vec<HardLink>> {
        self.extra_links.get(&inode)
    }

    // Detach and return all extra hard links of an inode.
    pub(crate) fn take_links(&mut self, inode: Inode) -> Vec<HardLink> {
        self.extra_links.remove(&inode).unwrap_or_default()
    }

    // Remove the directory entry (parent, name) from an inode's link set
    // and return the number of remaining links, or None if no such link
    // exists. The primary link of the node is counted too, unless it has
    // been unlinked from its parent directory already.
    pub(crate) fn remove_link(
        &mut self,
        node: &Arc<OverlayInode>,
        parent: &Arc<OverlayInode>,
        name: &str,
    ) -> Option<usize> {
        let parent_ptr = Arc::as_ptr(parent);
        let node_ptr = Arc::as_ptr(node);

        // The primary link is (node.parent, node.name). It counts as a
        // remaining link while its parent directory still lists it,
        // unless it is the directory entry being removed.
        let primary = node.parent.lock().unwrap().upgrade();
        let removing_primary = primary
            .as_ref()
            .map(|p| Arc::as_ptr(p) == parent_ptr)
            .unwrap_or(false)
            && node.name == name;
        let primary_live = !removing_primary
            && primary
                .as_ref()
                .map(|p| {
                    p.child(&node.name)
                        .map(|c| Arc::as_ptr(&c) == node_ptr)
                        .unwrap_or(false)
                })
                .unwrap_or(false);

        let mut removed = false;
        let mut remaining = usize::from(primary_live);
        if let Some(links) = self.extra_links.get_mut(&node.inode) {
            if let Some(pos) = links.iter().position(|(p, n, _)| {
                n == name
                    && p.upgrade()
                        .map(|p| Arc::as_ptr(&p) == parent_ptr)
                        .unwrap_or(false)
            }) {
                links.remove(pos);
                removed = true;
            }
            // Links whose parent directory is gone are stale: their
            // entries died with the parent, so they don't keep the inode
            // alive.
            remaining += links
                .iter()
                .filter(|(p, _, _)| p.upgrade().is_some())
                .count();
            if links.is_empty() {
                self.extra_links.remove(&node.inode);
            }
        }

        if removed || removing_primary {
            Some(remaining)
        } else {
            None
        }
    }

    // Query the overlay inode associated with a backend inode identity,
    // registered when the file got its first extra hard link.
    pub(crate) fn get_real_inode(&self, key: &(usize, u64)) -> Option<Inode> {
        self.real_index.get(key).copied()
    }

    pub(crate) fn insert_real_inode(&mut self, key: (usize, u64), inode: Inode) {
        self.real_index.insert(key, inode);
    }

    pub(crate) fn get_inode(&self, inode: Inode) -> Option<Arc<OverlayInode>> {
        self.inodes.get(&inode).cloned()
    }

    pub(crate) fn get_deleted_inode(&self, inode: Inode) -> Option<Arc<OverlayInode>> {
        self.deleted.get(&inode).cloned()
    }

    // Return the inode only if it's permanently deleted from both self.inodes and self.deleted_inodes.
    pub(crate) fn remove_inode(
        &mut self,
        inode: Inode,
        path_removed: Option<String>,
    ) -> Option<Arc<OverlayInode>> {
        let removed = match self.inodes.remove(&inode) {
            Some(v) => {
                // Refcount is not 0, we have to delay the removal.
                if v.lookups.load(Ordering::Relaxed) > 0 {
                    // A deleted inode has no live directory entries, so
                    // it can never be a hard link share target again.
                    // Drop the bookkeeping now: a stale backend identity
                    // entry would otherwise alias whatever inode number
                    // gets allocated for this one's paths, e.g. the
                    // whiteout of the removed name.
                    self.real_index.retain(|_, ino| *ino != inode);
                    self.extra_links.remove(&inode);
                    self.deleted.insert(inode, v.clone());
                    return None;
                }
                Some(v)
            }
            None => {
                // If the inode is not in hash, it must be in deleted_inodes.
                match self.deleted.get(&inode) {
                    Some(v) => {
                        // Refcount is 0, the inode can be removed now.
                        if v.lookups.load(Ordering::Relaxed) == 0 {
                            self.deleted.remove(&inode)
                        } else {
                            // Refcount is not 0, the inode will be removed later.
                            None
                        }
                    }
                    None => None,
                }
            }
        };

        if let Some(path) = path_removed {
            self.path_mapping.remove(&path);
        }

        // Drop hard link bookkeeping once the inode is permanently gone.
        if removed.is_some() {
            self.real_index.retain(|_, ino| *ino != inode);
            self.extra_links.remove(&inode);
        }

        removed
    }

    // As a debug function, print all inode numbers in hash table.
    // This function consumes quite lots of memory, so it's disabled by default.
    #[allow(dead_code)]
    pub(crate) fn debug_print_all_inodes(&self) {
        // Convert the HashMap to Vector<(inode, pathname)>
        let mut all_inodes = self
            .inodes
            .iter()
            .map(|(inode, ovi)| (inode, ovi.path.clone(), ovi.lookups.load(Ordering::Relaxed)))
            .collect::<Vec<_>>();
        all_inodes.sort_by(|a, b| a.0.cmp(b.0));
        trace!("all active inodes: {:?}", all_inodes);

        let mut to_delete = self
            .deleted
            .iter()
            .map(|(inode, ovi)| (inode, ovi.path.clone(), ovi.lookups.load(Ordering::Relaxed)))
            .collect::<Vec<_>>();
        to_delete.sort_by(|a, b| a.0.cmp(b.0));
        trace!("all deleted inodes: {:?}", to_delete);
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use std::sync::Mutex;

    #[test]
    fn test_alloc_unique() {
        let mut store = InodeStore::new();
        let empty_node = Arc::new(OverlayInode::new());
        store.insert_inode(1, empty_node.clone());
        store.insert_inode(2, empty_node.clone());
        store.insert_inode(VFS_MAX_INO - 1, empty_node.clone());

        let inode = store.alloc_unique_inode().unwrap();
        assert_eq!(inode, 3);
        assert_eq!(store.next_inode, 4);

        store.next_inode = VFS_MAX_INO - 1;
        let inode = store.alloc_unique_inode().unwrap();
        assert_eq!(inode, VFS_MAX_INO);

        let inode = store.alloc_unique_inode().unwrap();
        assert_eq!(inode, 3);
    }

    #[test]
    fn test_alloc_existing_path() {
        let mut store = InodeStore::new();
        let mut node_a = OverlayInode::new();
        node_a.path = "/a".to_string();
        store.insert_inode(1, Arc::new(node_a));
        let mut node_b = OverlayInode::new();
        node_b.path = "/b".to_string();
        store.insert_inode(2, Arc::new(node_b));
        let mut node_c = OverlayInode::new();
        node_c.path = "/c".to_string();
        store.insert_inode(VFS_MAX_INO - 1, Arc::new(node_c));

        let inode = store.alloc_inode(&"/a".to_string()).unwrap();
        assert_eq!(inode, 1);

        let inode = store.alloc_inode(&"/b".to_string()).unwrap();
        assert_eq!(inode, 2);

        let inode = store.alloc_inode(&"/c".to_string()).unwrap();
        assert_eq!(inode, VFS_MAX_INO - 1);

        let inode = store.alloc_inode(&"/notexist".to_string()).unwrap();
        assert_eq!(inode, 3);
    }

    #[test]
    fn test_remove_inode() {
        let mut store = InodeStore::new();
        let mut node_a = OverlayInode::new();
        node_a.lookups.fetch_add(1, Ordering::Relaxed);
        node_a.path = "/a".to_string();
        store.insert_inode(1, Arc::new(node_a));

        let mut node_b = OverlayInode::new();
        node_b.path = "/b".to_string();
        store.insert_inode(2, Arc::new(node_b));

        let mut node_c = OverlayInode::new();
        node_c.lookups.fetch_add(1, Ordering::Relaxed);
        node_c.path = "/c".to_string();
        store.insert_inode(VFS_MAX_INO - 1, Arc::new(node_c));

        let inode = store.alloc_inode(&"/new".to_string()).unwrap();
        assert_eq!(inode, 3);

        // Not existing.
        let inode = store.remove_inode(4, None);
        assert!(inode.is_none());

        // Existing but with non-zero refcount.
        let inode = store.remove_inode(1, None);
        assert!(inode.is_none());
        assert!(store.get_deleted_inode(1).is_some());
        assert!(store.path_mapping.get(&"/a".to_string()).is_some());

        // Remove again with file path.
        let inode = store.remove_inode(1, Some("/a".to_string()));
        assert!(inode.is_none());
        assert!(store.get_deleted_inode(1).is_some());
        assert!(store.path_mapping.get(&"/a".to_string()).is_none());

        // Node b has refcount 0, removing will be permanent.
        let inode = store.remove_inode(2, Some("/b".to_string()));
        assert!(inode.is_some());
        assert!(store.get_deleted_inode(2).is_none());
        assert!(store.path_mapping.get(&"/b".to_string()).is_none());

        // Allocate new inode, it should reuse inode 2 since inode 1 is still in deleted list.
        store.next_inode = 1;
        let inode = store.alloc_inode(&"/b".to_string()).unwrap();
        assert_eq!(inode, 2);

        // Allocate inode with path "/c" will reuse its inode number.
        let inode = store.alloc_inode(&"/c".to_string()).unwrap();
        assert_eq!(inode, VFS_MAX_INO - 1);
    }

    #[test]
    fn test_real_index() {
        let mut store = InodeStore::new();
        let mut node_a = OverlayInode::new();
        node_a.path = "/a".to_string();
        store.insert_inode(1, Arc::new(node_a));

        // Nothing is registered for unknown backend identities.
        assert_eq!(store.get_real_inode(&(0x1000usize, 42)), None);

        // Register and query a backend inode identity.
        store.insert_real_inode((0x1000, 42), 1);
        assert_eq!(store.get_real_inode(&(0x1000, 42)), Some(1));

        // Extra hard link paths only record path mapping.
        store.add_link(1, (Weak::new(), "b".to_string(), "/b".to_string()));
        store.insert_path("/b", 1);
        assert_eq!(store.alloc_inode(&"/b".to_string()).unwrap(), 1);

        // Permanent removal of the inode purges its real index entries
        // and its hard link bookkeeping.
        let inode = store.remove_inode(1, Some("/a".to_string()));
        assert!(inode.is_some());
        assert_eq!(store.get_real_inode(&(0x1000, 42)), None);
        assert!(store.get_links(1).is_none());

        // Path mapping of extra links is kept independently of the inode.
        assert_eq!(store.alloc_inode(&"/b".to_string()).unwrap(), 1);
        store.remove_path("/b");
        store.next_inode = 2;
        assert_eq!(store.alloc_inode(&"/b".to_string()).unwrap(), 2);
    }

    #[test]
    fn test_link_bookkeeping() {
        let mut store = InodeStore::new();
        let parent1 = Arc::new(OverlayInode::new());
        let parent2 = Arc::new(OverlayInode::new());

        let mut n = OverlayInode::new();
        n.inode = 1;
        n.name = "a".to_string();
        n.path = "/a".to_string();
        n.parent = Mutex::new(Arc::downgrade(&parent1));
        let node = Arc::new(n);
        parent1.insert_child("a", node.clone());
        store.insert_inode(1, node.clone());

        // Unknown links aren't reported.
        assert_eq!(store.remove_link(&node, &parent2, "x"), None);
        assert!(store.get_links(1).is_none());

        // Register an extra hard link.
        store.add_link(
            1,
            (Arc::downgrade(&parent2), "b".to_string(), "/b".to_string()),
        );
        parent2.insert_child("b", node.clone());
        assert_eq!(store.get_links(1).map(|l| l.len()), Some(1));

        // Re-registering the same path (e.g. the parent directory was
        // evicted and reloaded) replaces the stale entry instead of
        // accumulating duplicates, and refreshes the parent reference.
        let parent2b = Arc::new(OverlayInode::new());
        parent2b.insert_child("b", node.clone());
        store.add_link(
            1,
            (Arc::downgrade(&parent2b), "b".to_string(), "/b".to_string()),
        );
        assert_eq!(store.get_links(1).map(|l| l.len()), Some(1));
        assert!(Arc::ptr_eq(
            &store.get_links(1).unwrap()[0].0.upgrade().unwrap(),
            &parent2b
        ));

        // The stale parent no longer matches the re-registered entry;
        // removing it through the live parent keeps the primary link alive.
        assert_eq!(store.remove_link(&node, &parent2, "b"), None);
        assert_eq!(store.remove_link(&node, &parent2b, "b"), Some(1));
        assert!(store.get_links(1).is_none());

        // Register the extra link again, then remove the primary one.
        store.add_link(
            1,
            (Arc::downgrade(&parent2), "b".to_string(), "/b".to_string()),
        );
        assert_eq!(store.remove_link(&node, &parent1, "a"), Some(1));
        parent1.remove_child("a");

        // The last remaining link reports zero remaining links.
        assert_eq!(store.remove_link(&node, &parent2, "b"), Some(0));
        assert!(store.get_links(1).is_none());

        // All bookkeeping is dropped once the inode is removed.
        store.add_link(
            1,
            (Arc::downgrade(&parent2), "b".to_string(), "/b".to_string()),
        );
        assert_eq!(store.take_links(1).len(), 1);
        assert_eq!(store.take_links(1).len(), 0);

        // Three live links -- the primary and two extra links -- count
        // down 2 -> 1 -> 0 as they are unlinked one by one.
        parent1.insert_child("a", node.clone());
        store.add_link(
            1,
            (Arc::downgrade(&parent2), "b".to_string(), "/b".to_string()),
        );
        let parent3 = Arc::new(OverlayInode::new());
        parent3.insert_child("c", node.clone());
        store.add_link(
            1,
            (Arc::downgrade(&parent3), "c".to_string(), "/c".to_string()),
        );
        assert_eq!(store.get_links(1).map(|l| l.len()), Some(2));
        assert_eq!(store.remove_link(&node, &parent3, "c"), Some(2));
        assert_eq!(store.remove_link(&node, &parent2, "b"), Some(1));
        assert_eq!(store.remove_link(&node, &parent1, "a"), Some(0));
        assert!(store.get_links(1).is_none());
    }

    #[test]
    fn test_remove_inode_defer_purges_bookkeeping() {
        let mut store = InodeStore::new();
        let mut node_a = OverlayInode::new();
        node_a.inode = 1;
        node_a.path = "/a".to_string();
        node_a.lookups.fetch_add(1, Ordering::Relaxed);
        store.insert_inode(1, Arc::new(node_a));
        store.insert_real_inode((0x1000, 42), 1);
        store.add_link(1, (Weak::new(), "b".to_string(), "/b".to_string()));

        // A non-zero refcount delays the removal, but the hard link
        // bookkeeping is dropped immediately: a deleted inode has no
        // live directory entries and can never be a share target again,
        // so a stale backend identity entry would only alias whatever
        // inode number gets allocated for this one's paths, e.g. the
        // whiteout of the removed name.
        assert!(store.remove_inode(1, None).is_none());
        assert!(store.get_deleted_inode(1).is_some());
        assert_eq!(store.get_real_inode(&(0x1000, 42)), None);
        assert!(store.get_links(1).is_none());
    }

    #[test]
    fn test_alloc_deferred_path() {
        let mut store = InodeStore::new();
        let mut node_a = OverlayInode::new();
        node_a.inode = 1;
        node_a.path = "/a".to_string();
        node_a.lookups.fetch_add(1, Ordering::Relaxed);
        store.insert_inode(1, Arc::new(node_a));

        // The inode is deferred with pending kernel references, but the
        // path reservation survives the deferral.
        assert!(store.remove_inode(1, None).is_none());
        assert!(store.get_deleted_inode(1).is_some());
        assert!(store.path_mapping.get(&"/a".to_string()).is_some());

        // A new node for the same path, e.g. the whiteout placeholder
        // do_rm() installs for the removed name, must not reuse the
        // deferred number: the pending FORGETs would tear it down.
        let inode = store.alloc_inode(&"/a".to_string()).unwrap();
        assert_eq!(inode, 2);

        // A number owned by a live inode is still handed out, so
        // reloading a hard link finds the inode shared with its other
        // links.
        let mut node_b = OverlayInode::new();
        node_b.path = "/b".to_string();
        store.insert_inode(3, Arc::new(node_b));
        store.insert_path("/b2", 3);
        assert_eq!(store.alloc_inode(&"/b2".to_string()).unwrap(), 3);

        // Once the deferred inode's references settled and it is freed,
        // the reservation may hand its number out again.
        let deferred = store.get_deleted_inode(1).unwrap();
        deferred.lookups.fetch_sub(1, Ordering::Relaxed);
        assert!(store.remove_inode(1, None).is_some());
        assert_eq!(store.alloc_inode(&"/a".to_string()).unwrap(), 1);
    }

    #[test]
    fn test_remove_link_stale_parent() {
        let mut store = InodeStore::new();
        let parent1 = Arc::new(OverlayInode::new());

        let mut n = OverlayInode::new();
        n.inode = 1;
        n.name = "a".to_string();
        n.path = "/a".to_string();
        n.parent = Mutex::new(Arc::downgrade(&parent1));
        let node = Arc::new(n);
        parent1.insert_child("a", node.clone());
        store.insert_inode(1, node.clone());

        // An extra link whose parent directory goes away entirely: the
        // link dies with the parent, e.g. after rmdir of the parent.
        let parent2 = Arc::new(OverlayInode::new());
        store.add_link(
            1,
            (Arc::downgrade(&parent2), "b".to_string(), "/b".to_string()),
        );
        parent2.insert_child("b", node.clone());
        drop(parent2);

        // The stale link doesn't keep the inode alive when the primary
        // link is removed.
        assert_eq!(store.remove_link(&node, &parent1, "a"), Some(0));
        // The stale entry itself is still recorded until the inode is
        // permanently removed from the store.
        assert_eq!(store.get_links(1).map(|l| l.len()), Some(1));
    }
}
