// Copyright © 2019 Intel Corporation
//
// SPDX-License-Identifier: Apache-2.0

//! Data structs to support virtiofs based on vhost-user protocol.

#![allow(missing_docs)]

use bitflags::bitflags;
use vm_memory::ByteValued;

bitflags! {
    pub struct SetupmappingFlags: u64 {
        const WRITE = 0x1;
        const READ = 0x2;
    }
}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct SetupmappingIn {
    pub fh: u64,
    pub foffset: u64,
    pub len: u64,
    pub flags: u64,
    pub moffset: u64,
}

unsafe impl ByteValued for SetupmappingIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct RemovemappingIn {
    pub count: u32,
}

unsafe impl ByteValued for RemovemappingIn {}

#[repr(C)]
#[derive(Debug, Default, Copy, Clone)]
pub struct RemovemappingOne {
    pub moffset: u64,
    pub len: u64,
}

unsafe impl ByteValued for RemovemappingOne {}
