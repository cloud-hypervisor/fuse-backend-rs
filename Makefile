current_dir := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
CARGO ?= $(shell which cargo)

ifdef RUST_TARGET
	TARGET = --target ${RUST_TARGET}
endif

# Core's own `--all-features` is target-independent now that `persist`/
# `dbs-snapshot` moved out to the `fuse-backend-vfs` crate, so it is built
# unconditionally below. But `dbs-snapshot` still only defines its snapshot
# magic id for x86_64, aarch64, powerpc64 and riscv64; it fails to compile for
# s390x and powerpc64le, both of which the CI matrix cross-builds. So gate the
# vfs `persist` cross-build to the supported targets (an empty RUST_TARGET is a
# native dev/macOS build, always supported); elsewhere it stays covered by the
# amd64 native `test` rows and the macOS rows.
VFS_PERSIST_TARGETS := x86_64-unknown-linux-musl aarch64-unknown-linux-musl powerpc64-unknown-linux-gnu riscv64gc-unknown-linux-gnu
ifeq ($(strip $(RUST_TARGET)),)
BUILD_VFS_PERSIST := yes
else ifneq ($(filter $(RUST_TARGET),$(VFS_PERSIST_TARGETS)),)
BUILD_VFS_PERSIST := yes
else
BUILD_VFS_PERSIST :=
endif

build:
	${CARGO} build ${TARGET} --features="fusedev"
	${CARGO} build ${TARGET} --features="virtiofs"
	${CARGO} build ${TARGET} --features="vhost-user-fs"
	${CARGO} build ${TARGET} --features="fusedev,async-io"
	${CARGO} build ${TARGET} --features="virtiofs,async-io"
	${CARGO} build ${TARGET} --features="vhost-user-fs,async-io"
	${CARGO} build ${TARGET} -p fuse-backend-core --all-features
ifdef BUILD_VFS_PERSIST
	${CARGO} build ${TARGET} -p fuse-backend-vfs --features="fuse-backend-vfs/persist"
endif

check: build
	${CARGO} fmt --all -- --check
	${CARGO} clippy ${TARGET} --features="fusedev" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="fusedev,fusedev-uring" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="virtiofs" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="vhost-user-fs" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="fusedev,virtiofs" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="fusedev,async-io" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="virtiofs,async-io" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="vhost-user-fs,async-io" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="fusedev,virtiofs,async-io" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} -p fuse-backend-core --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} -p fuse-backend-core --no-default-features --features="async-io" -- -Dwarnings
	${CARGO} clippy ${TARGET} -p fuse-backend-core --no-default-features --features="fusedev-uring" -- -Dwarnings
	# `Vfs` used to be clippy'd as part of core (the rows above); now that it is
	# its own crate, restore the same no-default + async-io lib coverage.
	# `persist` is deliberately excluded here: dbs-snapshot does not cross-compile
	# for every CI target, so it stays covered natively by `test` and the macOS
	# rows below.
	${CARGO} clippy ${TARGET} -p fuse-backend-vfs --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} -p fuse-backend-vfs --no-default-features --features="fuse-backend-vfs/async-io" -- -Dwarnings

test:
	${CARGO} test ${TARGET} --features="fusedev" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="virtiofs" --no-default-features  -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="vhost-user-fs" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="fusedev,virtiofs" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="fusedev,async-io" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="virtiofs,async-io" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="vhost-user-fs,async-io" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="fusedev,virtiofs,async-io" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --features="fusedev,persist" --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} --all-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-core --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-core --no-default-features --features="async-io" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-core --no-default-features --features="fusedev-uring" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-core --all-features -- --nocapture --skip integration
	# `cargo test --features=X` only builds the test targets of the selected
	# package, so the umbrella rows above never reach the unit tests living in
	# the other workspace members. Each member owning tests needs its own rows.
	# Their features are spelled `pkg/feature` because with `-p` a bare
	# `--features=X` is validated against the workspace root package as well,
	# which does not define the sub-crate-only names (`uring`).
	${CARGO} test ${TARGET} -p fuse-backend-vfs --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-vfs --features="fuse-backend-vfs/async-io" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-vfs --features="fuse-backend-vfs/virtiofs" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-vfs --features="fuse-backend-vfs/persist" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-vfs --all-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-fusedev --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-fusedev --features="fuse-backend-fusedev/async-io" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-fusedev --features="fuse-backend-fusedev/uring" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-fusedev --all-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-virtiofs --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-virtiofs --all-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-passthrough --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-passthrough --features="fuse-backend-passthrough/async-io" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-passthrough --features="fuse-backend-passthrough/virtiofs" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-passthrough --all-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-overlayfs --no-default-features -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-overlayfs --all-features -- --nocapture --skip integration

smoke:
	${CARGO} test ${TARGET} --features="fusedev,persist" -- --nocapture

smoke-all: smoke
	${CARGO} test ${TARGET} --features="fusedev,persist" -- --nocapture --ignored
	${CARGO} test ${TARGET} --features="fusedev,async-io" --no-default-features -- --nocapture --ignored

build-macos:
	${CARGO} build --features="fusedev"
	${CARGO} build --features="fusedev,fuse-t"
	${CARGO} build -p fuse-backend-core --no-default-features
	${CARGO} build -p fuse-backend-vfs --no-default-features
	${CARGO} build -p fuse-backend-vfs --no-default-features --features="fuse-backend-vfs/persist"

check-macos: build-macos
	${CARGO} fmt --all -- --check
	${CARGO} clippy --features="fusedev" -- -Dwarnings
	${CARGO} test --features="fusedev" -- --nocapture --skip integration
	${CARGO} clippy --features="fusedev,fuse-t" -- -Dwarnings
	${CARGO} test --features="fusedev,fuse-t" -- --nocapture --skip integration
	${CARGO} clippy -p fuse-backend-core --no-default-features -- -Dwarnings
	${CARGO} test -p fuse-backend-core --no-default-features -- --nocapture --skip integration
	${CARGO} clippy -p fuse-backend-vfs --no-default-features -- -Dwarnings
	${CARGO} test -p fuse-backend-vfs --no-default-features -- --nocapture --skip integration
	${CARGO} test -p fuse-backend-vfs --no-default-features --features="fuse-backend-vfs/persist" -- --nocapture --skip integration
	# The fusedev crate owns the macOS session tests; the umbrella rows above
	# only build it as a dependency and never run its test target. virtiofs,
	# passthrough and overlayfs are deliberately absent: virtiofs cannot build
	# on macOS (core's Opcode::SetupMapping/RemoveMapping are Linux-only) and
	# the two filesystem drivers are Linux-only crates.
	${CARGO} test -p fuse-backend-fusedev --no-default-features -- --nocapture --skip integration
	${CARGO} test -p fuse-backend-fusedev --features="fuse-backend-fusedev/fuse-t" -- --nocapture --skip integration

smoke-macos: check-macos
	${CARGO} test --features="fusedev,fuse-t" -- --nocapture

docker-smoke:
	docker run --env RUST_BACKTRACE=1 --rm --privileged --volume ${current_dir}:/fuse-rs rust:1.68 sh -c "rustup component add clippy rustfmt; cd /fuse-rs; make smoke-all"

testoverlay:
	${CARGO} build -p overlay

# Setup xfstests env and run.
xfstests:
	./tests/scripts/xfstests.sh
