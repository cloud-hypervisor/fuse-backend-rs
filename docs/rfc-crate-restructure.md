# RFC: Restructuring fuse-backend-rs into a layered crate workspace

- **Status:** Draft for community discussion
- **Scope:** crate/feature reorganization + reduction of the core dependency footprint
- **Non-normative:** names, crate counts, and staging are proposals open to feedback

## 1. Summary

`fuse-backend-rs` is a single crate that bundles the FUSE ABI, the VFS/server
core, four transports (fusedev, fusedev-uring, virtiofs, vhost-user-fs) and two
filesystem drivers (passthrough, overlayfs), all selected by Cargo features.

The feature gates already work: a fusedev-only build does **not** pull `vhost`,
`virtio-queue`, or `virtio-bindings`. But three structural problems remain:

1. **Layering inversion** — the transport-neutral `api` layer depends on
   `transport` for its buffer types (`Reader`/`Writer`/`FuseBuf`/`pagesize`).
2. **Driver-only dependency leaks** — every build pulls deps used by a single
   driver (e.g. `radix_trie`, used only by overlayfs).
3. **rust-vmm coupling in the shared core** — `vm-memory` and `vmm-sys-util` are
   reachable from the core that every transport and driver shares.

This RFC proposes splitting the crate into a **layered workspace behind a
compatibility facade**, and reducing core's rust-vmm footprint to **zero
`vmm-sys-util`** and a **minimal `vm-memory`** surface.

## 2. Motivation

### 2.1 What is already fine (correcting a common assumption)

A frequent concern is that "using fusedev drags in vhost and the virtio crates."
`cargo tree` shows this is **not** the case today — those deps are optional and
correctly gated behind `virtiofs` / `vhost-user-fs`:

```
$ cargo tree --no-default-features --features fusedev -e normal --depth 1
fuse-backend-rs v0.14.0
├── arc-swap        ├── bitflags      ├── caps (linux)
├── lazy_static     ├── libc          ├── log
├── mio             ├── nix           ├── radix_trie
├── vm-memory       └── vmm-sys-util
```

So the "dependency explosion" is narrower than feared. The real, fixable issues
are the three in §1 — above all the rust-vmm coupling and the driver-only leaks.

### 2.2 Competitive context: fuser 0.18.0

[`fuser`](https://crates.io/crates/fuser) is the main alternative Rust FUSE
library. Its 0.18.0 default dependency footprint (11 direct deps, +1 build) has
**zero rust-vmm crates**:

```
bitflags  libc  log  memchr  num_enum  page_size  parking_lot
ref-cast  smallvec  zerocopy  nix        (+ pkg-config, build-only)
```

fuser uses **`zerocopy`** for safe ABI transmutation (our `vm-memory::ByteValued`
role) and **`nix`** for syscalls; `tokio`/`async-trait`/`serde` are optional and
off by default. This is the bar a fusedev-only build of this crate should meet:
a handful of small, widely-used crates with no virtualization-stack coupling.

## 3. Goals / Non-goals

**Goals**

- **G1** — Layer the project into `core` → `transports` → `drivers`, behind a
  facade crate that preserves today's `fuse_backend_rs::…` import paths and
  Cargo feature names.
- **G2** — Fix the layering inversion: `api` no longer depends on `transport`.
- **G3** — A fusedev-only build pulls no driver-only deps (`radix_trie`) and no
  virtio/vhost deps (structurally guaranteed, not just feature-gated).
- **G4** — `core` has **zero** `vmm-sys-util` dependency (production or dev).
- **G5** — `core` has a **minimal** `vm-memory` surface; all guest-memory/dirty-
  bitmap machinery lives only in `virtiofs`.
- **G6** — Land the change in independently shippable, testable stages.

**Non-goals**

- **N1** — Removing `vm-memory` from the *project*. virtiofs fundamentally needs
  it (`GuestMemory`, `Address`, dirty-page bitmaps). The goal is to evict it from
  **core**, not from the repo.
- **N2** — Changing the FUSE ABI or on-wire protocol.
- **N3** — Rewriting transports/drivers' internals; this is a reorganization.

## 4. Current-state audit

### 4.1 Module inventory → target crate

| Current module | Role | Target crate |
|---|---|---|
| `abi/` | FUSE ABI structs (`ByteValued`) | `core` |
| `api/` (filesystem, server, vfs) | FS trait, request dispatcher, multiplexer | `core` |
| `common/` (file_traits, file_buf, mpmc, async_runtime) | buffer/file/runtime helpers | `core` |
| `transport/` `Reader`/`Writer`/`FuseBuf`/`pagesize`/`Error` | transport-neutral buffers | `core` (**moved**) |
| `transport/fusedev/` | `/dev/fuse` channels + sessions | `fuse-backend-fusedev` |
| `transport/fusedev/uring_session.rs` | FUSE-over-io_uring | `fuse-backend-fusedev` (`uring` feature) |
| `transport/virtiofs/` | virtio descriptor transport | `fuse-backend-virtiofs` |
| `transport/fs_cache_req_handler.rs` | DAX cache req handler **trait** (referenced by `api`) | trait → `core`; vhost-backed impl → `fuse-backend-virtiofs` |
| `passthrough/` | passthrough filesystem driver | `fuse-backend-passthrough` |
| `overlayfs/` | overlay filesystem driver | `fuse-backend-overlayfs` |
| (new) | re-export facade | `fuse-backend-rs` |

### 4.2 Dependency allocation

| Dep | Used by | Target |
|---|---|---|
| `vm-memory` | abi `ByteValued`; core `Reader`/`Writer` (`VolatileSlice`, `BitmapSlice`); virtiofs guest memory | `core` (**minimal**) + `virtiofs` (full) |
| `vmm-sys-util` | core: **tests only**; fusedev fd-passing; passthrough `fam` | drop from `core`; keep in `fusedev`+`passthrough` |
| `arc-swap` | `api/server`, `api/vfs`, `api/pseudo_fs` | `core` |
| `lazy_static` | `transport` pagesize, `common/async_runtime` | `core` (or replace with `OnceLock`) |
| `versionize`, `versionize_derive`, `dbs-snapshot` | `api/vfs` + `api/pseudo_fs` (`persist`) | `core` (behind `persist`; see §7.4) |
| `radix_trie` | **`overlayfs` only** | `fuse-backend-overlayfs` |
| `mio`, `caps` | fusedev epoll/mount | `fuse-backend-fusedev` |
| `nix`, `libc`, `log`, `bitflags` | shared | `core` and/or transports |
| `virtio-queue`, `virtio-bindings`, `vhost` | virtiofs (incl. its `vhost-user-fs` feature) | `fuse-backend-virtiofs` only |

### 4.3 Layering inversion

`api` (transport-neutral) imports `transport`:

- [api/server/mod.rs:30](../src/api/server/mod.rs) `use crate::transport::{Reader, Writer};`
- [api/server/sync_io.rs:24](../src/api/server/sync_io.rs) `use crate::transport::{pagesize, FsCacheReqHandler, Reader, Writer};`

The fix is to relocate the transport-neutral buffer types (`Reader`, `Writer`,
`FuseBuf`, `pagesize`) and the buffer `Error` into `core`, then `pub use` them
back from `transport` so existing paths keep resolving (§7.1).

### 4.4 rust-vmm coupling in core

**`vm-memory`** is the buffer/ABI model, not an incidental utility:

- `ByteValued` — implemented by ~30 ABI structs ([abi/fuse_abi_linux.rs:13](../src/abi/fuse_abi_linux.rs)) and used by `Reader::read_obj<T: ByteValued>`.
- `VolatileSlice<'a, S>` — the element type of `IoBuffers` ([transport/mod.rs:135](../src/transport/mod.rs)).
- `BitmapSlice` — the generic bound on the **public** `Reader<'a, S = ()>` / `Writer<'a, S: BitmapSlice = ()>` / `FuseDevWriter` / `UringWriter` / `VirtioFsWriter`.

**`vmm-sys-util`** in core is **test-only** (`TempFile`/`TempDir`):
`api/server/{sync_io,async_io}.rs`, `api/vfs/async_io.rs`,
`common/{file_traits,async_file}.rs`. Its only production users are transports/
drivers: fusedev `ScmSocket::recv_with_fd`
([linux_session.rs:750](../src/transport/fusedev/linux_session.rs)) and
passthrough `fam` ([file_handle.rs:15](../src/passthrough/file_handle.rs)).

## 5. Proposed crate layout

### 5.1 Crate graph

```
                 fuse-backend-rs  (facade, re-exports only)
                    │   │   │   │
     ┌──────────────┘   │   │   └───────────────┐
     ▼                  ▼   ▼                   ▼
fuse-backend-fusedev  fuse-backend-virtiofs  fuse-backend-passthrough  fuse-backend-overlayfs
     │                  │  (+ vm-memory full,
     │                  │   virtio-queue, vhost)
     └────────┬─────────┘
              ▼
        fuse-backend-core   (abi + api + common + buffer; minimal vm-memory; zero vmm-sys-util)
```

Six crates, facade included (option **B**): the two drivers are their own crates,
and `vhost-user-fs` is a **feature of `fuse-backend-virtiofs`**, not a separate
crate. Dependency direction is fixed by the code: transports/drivers need core's
types, so they sit **above** core; the facade sits above all and only re-exports.

### 5.2 The facade is forced, not cosmetic

Suppose we let `fuse-backend-rs` *be* the core but still want
`fuse_backend_rs::transport::FuseChannel` to resolve. That requires core to
re-export its transports:

```
fuse-backend-rs (=core) ─▶ fuse-backend-fusedev ─▶ fuse-backend-rs   ✗ CYCLE
```

Cargo forbids cyclic crate dependencies (even optional ones). So the only way to
preserve today's paths is for `fuse-backend-rs` to sit **above** every sub-crate
and re-export downward — the umbrella/facade pattern.

### 5.3 Facade mechanics

```toml
# fuse-backend-rs (facade)
[features]
default      = ["fusedev"]
fusedev      = ["dep:fuse-backend-fusedev"]
virtiofs     = ["dep:fuse-backend-virtiofs"]
vhost-user-fs = ["fuse-backend-virtiofs/vhost-user-fs"]  # a virtiofs feature, not a crate
passthrough   = ["dep:fuse-backend-passthrough"]
overlayfs     = ["dep:fuse-backend-overlayfs"]
persist       = ["fuse-backend-core/persist"]            # snapshots live in core
async-io      = ["fuse-backend-core/async-io", "fuse-backend-fusedev/async-io"]
```

```rust
// facade lib.rs — re-export only, no logic
pub use fuse_backend_core::{abi, api, common};
pub mod transport {
    pub use fuse_backend_core::buffer::*;              // Reader/Writer/FuseBuf/pagesize
    #[cfg(feature = "fusedev")]  pub use fuse_backend_fusedev::*;
    #[cfg(feature = "virtiofs")] pub use fuse_backend_virtiofs::*;
}
#[cfg(feature = "passthrough")] pub use fuse_backend_passthrough as passthrough;
#[cfg(feature = "overlayfs")]   pub use fuse_backend_overlayfs as overlayfs;
```

`fuse_backend_rs::transport::Reader`, `…::FuseChannel`, `…::api::Server`,
`…::passthrough::PassthroughFs` all keep resolving. Re-exports preserve *type
identity*, so generic bounds, impls, and turbofish are unaffected.

## 6. Reducing core's rust-vmm footprint

### 6.1 `vmm-sys-util` → zero in core (G4)

Free. Core's only uses are `#[cfg(test)]` `TempFile`/`TempDir`; migrate them to
the `tempfile` crate (which fuser also uses). Core's manifest then lists **no**
`vmm-sys-util` at all — not even a dev-dependency. fusedev keeps it for
`recv_with_fd` (or drops it too — see 6.4), passthrough keeps it for `fam`.

### 6.2 `vm-memory` → minimal in core (G5)

**Minimal surface core retains:** `ByteValued`, `VolatileSlice`, and the
`BitmapSlice` trait bound. Everything else moves out.

**Why not zero (the crux):** virtiofs builds the *same* core `Reader`/`Writer`
over guest memory with a real dirty-page bitmap:

```rust
// transport/virtiofs/mod.rs
impl<'a> Reader<'a> {
    fn from_desc_chain<M>(desc_chain: DescriptorChain<M>)
        -> Result<Reader<'a, MS<'a, M::Target>>>   // MS = a real BitmapSlice, not ()
    where M::Target: GuestMemory + Sized { … }
}
```

Because `VolatileSlice<'a, S>` requires `S: vm_memory::bitmap::BitmapSlice`, and
core's buffers must stay generic to serve virtiofs, core must keep *that* bound
(and hence `VolatileSlice`). fusedev simply instantiates the default `S = ()`.

**What moves out of core → `virtiofs`:** `GuestMemory`, `GuestMemoryRegion`,
`Address`, `MemoryRegionAddress`, `MS`, `Bytes`, `Le16/32/64`, and the
virtio-specific `Error` variants (`DescriptorChainOverflow`, `FindMemoryRegion`,
`InvalidChain`, and the `GuestMemoryError` wrapper). Core's `Error` keeps only
the transport-neutral variants (`IoError`, `InvalidParameter`, `SplitOutOfBounds`,
`VolatileMemoryError`).

### 6.3 `Writer` is a closed enum spanning transports

Today `Writer` is an enum over `FuseDev`/`Uring`/`VirtioFs`/`Noop` variants
([transport/mod.rs:540](../src/transport/mod.rs)). A closed enum in core cannot
reference a type that lives in the virtiofs crate. Two options:

- **(a) Trait-ify** — core defines a `Writer` trait; each transport implements
  it. Cleanest layering, but touches every `Writer` match site in `api/server`.
- **(b) Generic-over-backend** — core keeps a `Writer<B>` generic; transports
  supply `B`. Less churn at call sites, more generics noise.

Recommendation: **(a)**, done in Stage 0 while still one crate, so the enum→trait
migration is testable before the split.

### 6.4 Optional stretch — Tier 2 (zero `vm-memory` in core)

To reach fuser's zero-rust-vmm core, replace the minimal surface:

- `ByteValued` → adopt **`zerocopy`** (as fuser does) for ABI structs, or vendor
  a tiny core-local marker trait.
- `VolatileSlice` + `BitmapSlice` → vendor a minimal volatile-buffer + bitmap
  trait into core, with a `vm-memory`-backed adapter living in `virtiofs`.

**Cost:** new `unsafe` (volatile access + transmutation) in core that must match
vm-memory's safety guarantees, plus ongoing maintenance. **Benefit:** a truly
standalone core with zero rust-vmm. This is a genuine trade-off and is left as an
**open question** (§9) rather than pre-decided — the minimal path (6.2) already
removes the guest-memory coupling and is far cheaper.

## 7. Backward compatibility

### 7.1 Preserved (free)

- **Import paths** — relocation + `pub use` re-export keeps
  `fuse_backend_rs::transport::Reader`, `…::FuseChannel`, `…::api::Server`,
  `…::passthrough::PassthroughFs` resolving to the *same* types.
- **Manifest line** — the facade maps today's feature names onto sub-crate deps,
  so `fuse-backend-rs = { version = "…", features = ["fusedev"] }` is unchanged.

### 7.2 Breaking surface (small, with the minimal path)

- **`transport::Error` variant relocation** — the virtio-specific variants move
  to a virtiofs error type. Only code matching those variants is affected (they
  are unreachable in a fusedev-only build anyway).
- **`Writer` enum → trait** (6.3a) — downstream code that names the `Writer`
  enum variants directly must adapt; `api/server` is updated in-tree.
- **`Reader` constructors → extension traits** — the transport-specific
  constructors (`from_fuse_buffer`, `from_descriptor_chain`, …) move from
  inherent impls to the `FuseDevReaderExt`/`VirtioFsReaderExt` traits in
  the transport crates (core owns `Reader`; inherent impls are confined
  to the defining crate). The `Reader::from_…` call spelling is unchanged
  once the facade-re-exported trait is imported.
- **Crate identity** — a downstream `impl` of a core trait still works via the
  facade re-export (same type), but anyone depending on the *crate name*
  `fuse-backend-rs` for internals should move to the sub-crate.

Keeping `vm-memory` minimal (6.2) rather than removing it (6.4) means the public
`Reader<'a, S>`/`Writer<'a, S>` signatures are **unchanged** — no generic-signature
break.

### 7.3 MSRV / edition

fuser is edition 2024 / rust-version 1.85. This crate is edition 2018. Replacing
`lazy_static` with `std::sync::OnceLock` (and any `zerocopy` adoption in Tier 2)
would raise MSRV; propose deciding MSRV explicitly in §9.

### 7.4 Snapshot / persistence compatibility (`persist`)

The `persist` feature (`dbs-snapshot` + `versionize`) serializes **core-only**
state: `api/vfs::persist` (`VfsState`, `VfsOptionsState`, `IdMappingState`) and
`api/pseudo_fs::persist` (`PseudoFsState`). The Vfs snapshot deliberately
**excludes** mounted backend filesystems (callers re-mount via `restore_mount`),
so **no driver carries versionize state** — the passthrough/overlayfs crates are
irrelevant to persistence.

**Relocation is byte-compatible.** versionize keys struct versions on
`std::any::TypeId` (`fn type_id() -> TypeId`), used only as an **in-memory,
per-binary** map key that `get_version_map()` rebuilds on every save *and*
restore; the `TypeId` is **never written into the snapshot bytes**. The format
depends solely on field order/types, the `#[version(start = N)]` attributes, and
the app-version header — none of which change when the types move into
`fuse-backend-core`. Old v0.14 snapshots stay loadable; the v1→v2 path is intact.

**Requirements:** move the `persist` feature + `versionize`/`dbs-snapshot` deps
to core (facade forwards `persist = ["fuse-backend-core/persist"]`), and relocate
the two `persist` modules **verbatim** — no field reordering, no version
renumbering, no edits to `get_version_map()`'s history.

## 8. Migration plan (each stage shippable)

- **Stage 0 — re-layer in place (single crate).** Move `Reader`/`Writer`/
  `FuseBuf`/`pagesize` + buffer `Error` into a new `src/buffer/`; `pub use` them
  back from `transport`. Convert `Writer` enum → trait. Split virtio-specific
  `Error` variants behind `cfg(feature = "virtiofs")`. Migrate core tests from
  `vmm-sys-util` to `tempfile`. *Result: `api` no longer imports `transport`;
  mostly non-breaking.*
- **Stage 1 — extract `fuse-backend-core`.** abi + api + common + buffer. Deps:
  minimal `vm-memory`, `arc-swap`, `libc`, `log`, `bitflags` (+`lazy_static`
  until replaced). **Zero `vmm-sys-util`.** Carries the `persist` feature
  (Vfs/PseudoFs snapshots, byte-compatible per §7.4) + `versionize`/`dbs-snapshot`
  deps, and the `FsCacheReqHandler` **trait** (its vhost-backed impl stays in
  virtiofs, so `api`/drivers never depend on the virtiofs crate).
- **Stage 2 — extract transports & drivers.** `fuse-backend-fusedev`
  (+`uring` feature), `fuse-backend-virtiofs` (full `vm-memory`, `virtio-queue`,
  `vhost`; **`vhost-user-fs` is a feature of this crate, not a separate crate**),
  `fuse-backend-passthrough` (`vmm-sys-util` fam, `caps`), and
  `fuse-backend-overlayfs` (`radix_trie`).
- **Stage 3 — facade.** Turn `fuse-backend-rs` into the re-export umbrella; map
  feature names; verify all legacy paths + the workspace tests still build.
- **Stage 4 (optional) — Tier 2.** Vendor `ByteValued`+volatile-slice (or adopt
  `zerocopy`) to reach zero `vm-memory` in core, per the §9 decision.

Each stage is gated by the existing verification matrix: `cargo fmt --check`,
macOS build (default + `fuse-t`), Linux build `--all-targets` (+ `fusedev-uring`,
`virtiofs`, `vhost-user-fs`), and `cargo test --lib`.

## 9. Open questions for the community

1. **Tier 2 or not?** Is a zero-`vm-memory` core worth vendoring `unsafe`
   buffer/transmute code (or adopting `zerocopy`), given `vm-memory` is small and
   well-maintained? The minimal path (6.2) already decouples guest memory.
2. **`Writer` enum → trait** (6.3a) vs generic-over-backend (6.3b)?
3. **Should `Vfs`/`arc-swap` be optional** for users who bring their own
   `FileSystem` and don't need the multiplexer?
4. **Crate naming & publishing** — `fuse-backend-core` / `-fusedev` / `-virtiofs`
   / … under the cloud-hypervisor org? Versioning cadence across the workspace?
5. **MSRV / edition** — bump to enable `OnceLock` (drop `lazy_static`) and
   possibly `zerocopy`?

## Appendix A — dependency comparison

Direct dependencies of a **fusedev-only** build (Linux), vs **fuser 0.18.0**:

| | today | after split | +core−vmm-sys-util, fd→nix | +drop lazy_static | +Tier 2 | fuser 0.18.0 |
|---|---|---|---|---|---|---|
| count | 11 | 10 | 9 | 8 | **7** | 11 (+1 build) |
| rust-vmm | vm-memory, vmm-sys-util | 2 | vm-memory | vm-memory | **none** | **none** |
| driver-only leak | radix_trie | — | — | — | — | — |

- **Today (fusedev):** arc-swap, bitflags, caps, lazy_static, libc, log, mio, nix, radix_trie, vm-memory, vmm-sys-util. *(macOS swaps `caps` → `core-foundation-sys`.)*
- **Tier-2 target:** arc-swap, bitflags, caps, libc, log, mio, nix — zero rust-vmm.
- **fuser 0.18.0:** bitflags, libc, log, memchr, num_enum, page_size, parking_lot, ref-cast, smallvec, zerocopy, nix (+ pkg-config build).

The sets differ (fuser has no VFS multiplexer → no `arc-swap`; we have no
`smallvec`/`memchr`/`zerocopy`), but the **weight class is the same**: a handful
of small, mainstream crates plus `libc`/`nix`. The refactor's concrete wins are
removing the driver-only `radix_trie` leak, evicting `vmm-sys-util` from core,
shrinking `vm-memory` to a minimal buffer surface — and making all of it
structural so it cannot regress.
