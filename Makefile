current_dir := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
CARGO ?= $(shell which cargo)

ifdef RUST_TARGET
	TARGET = --target ${RUST_TARGET}
endif

# dbs-snapshot (pulled in by core's `persist` feature, and therefore by core's
# --all-features) only defines its snapshot magic id for x86_64, aarch64,
# powerpc64 and riscv64; it fails to compile for s390x and powerpc64le, both of
# which the CI matrix cross-builds. Enable core's full feature set only where
# the dependency supports the target; elsewhere build core without `persist`,
# which stays covered on the amd64 native test path. An empty RUST_TARGET is a
# native build (dev box / macOS), treated as supported.
PERSIST_TARGETS := x86_64-unknown-linux-musl aarch64-unknown-linux-musl powerpc64-unknown-linux-gnu riscv64gc-unknown-linux-gnu
ifeq ($(strip $(RUST_TARGET)),)
CORE_FEATURES := --all-features
else ifneq ($(filter $(RUST_TARGET),$(PERSIST_TARGETS)),)
CORE_FEATURES := --all-features
else
CORE_FEATURES := --no-default-features --features=async-io
endif

build:
	${CARGO} build ${TARGET} --features="fusedev"
	${CARGO} build ${TARGET} --features="virtiofs"
	${CARGO} build ${TARGET} --features="vhost-user-fs"
	${CARGO} build ${TARGET} --features="fusedev,async-io"
	${CARGO} build ${TARGET} --features="virtiofs,async-io"
	${CARGO} build ${TARGET} --features="vhost-user-fs,async-io"
	${CARGO} build ${TARGET} -p fuse-backend-core ${CORE_FEATURES}

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
	${CARGO} test ${TARGET} -p fuse-backend-core --no-default-features --features="persist" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-core --no-default-features --features="fusedev-uring" -- --nocapture --skip integration
	${CARGO} test ${TARGET} -p fuse-backend-core --all-features -- --nocapture --skip integration

smoke:
	${CARGO} test ${TARGET} --features="fusedev,persist" -- --nocapture

smoke-all: smoke
	${CARGO} test ${TARGET} --features="fusedev,persist" -- --nocapture --ignored
	${CARGO} test ${TARGET} --features="fusedev,async-io" --no-default-features -- --nocapture --ignored

build-macos:
	${CARGO} build --features="fusedev"
	${CARGO} build --features="fusedev,fuse-t"
	${CARGO} build -p fuse-backend-core --no-default-features
	${CARGO} build -p fuse-backend-core --no-default-features --features="persist"

check-macos: build-macos
	${CARGO} fmt --all -- --check
	${CARGO} clippy --features="fusedev" -- -Dwarnings
	${CARGO} test --features="fusedev" -- --nocapture --skip integration
	${CARGO} clippy --features="fusedev,fuse-t" -- -Dwarnings
	${CARGO} test --features="fusedev,fuse-t" -- --nocapture --skip integration
	${CARGO} clippy -p fuse-backend-core --no-default-features -- -Dwarnings
	${CARGO} test -p fuse-backend-core --no-default-features -- --nocapture --skip integration
	${CARGO} test -p fuse-backend-core --no-default-features --features="persist" -- --nocapture --skip integration

smoke-macos: check-macos
	${CARGO} test --features="fusedev,fuse-t" -- --nocapture

docker-smoke:
	docker run --env RUST_BACKTRACE=1 --rm --privileged --volume ${current_dir}:/fuse-rs rust:1.68 sh -c "rustup component add clippy rustfmt; cd /fuse-rs; make smoke-all"

testoverlay:
	cd tests/testoverlay && ${CARGO} build

# Setup xfstests env and run.
xfstests:
	./tests/scripts/xfstests.sh
