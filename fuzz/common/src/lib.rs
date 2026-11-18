// SPDX-License-Identifier: Apache-2.0

//! The harness behind the fuzz targets, in a crate of its own so that its tests can replay
//! fuzz inputs on a stable toolchain.

pub mod server;
