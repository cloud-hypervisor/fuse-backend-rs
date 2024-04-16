current_dir := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))
CARGO ?= $(shell which cargo)

ifdef RUST_TARGET
	TARGET = --target ${RUST_TARGET}
endif

build:
	${CARGO} build ${TARGET} --features="fusedev"
	${CARGO} build ${TARGET} --features="virtiofs"
	${CARGO} build ${TARGET} --features="vhost-user-fs"
	${CARGO} build ${TARGET} --features="fusedev,async-io"
	${CARGO} build ${TARGET} --features="virtiofs,async-io"
	${CARGO} build ${TARGET} --features="vhost-user-fs,async-io"

check: build
	${CARGO} fmt -- --check
	${CARGO} clippy ${TARGET} --features="fusedev" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="virtiofs" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="vhost-user-fs" --no-default-features -- -Dwarnings
	${CARGO} clippy ${TARGET} --features="fusedev,virtiofs" --no-default-features -- -Dwarnings

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

smoke:
	${CARGO} test ${TARGET} --features="fusedev,persist" -- --nocapture

smoke-all: smoke
	${CARGO} test ${TARGET} --features="fusedev,persist" -- --nocapture --ignored

build-macos:
	${CARGO} build --features="fusedev"
	${CARGO} build --features="fusedev,fuse-t"

check-macos: build-macos
	${CARGO} fmt -- --check
	${CARGO} clippy --features="fusedev" -- -Dwarnings
	${CARGO} test --features="fusedev" -- --nocapture --skip integration
	${CARGO} clippy --features="fusedev,fuse-t" -- -Dwarnings
	${CARGO} test --features="fusedev,fuse-t" -- --nocapture --skip integration

smoke-macos: check-macos
	${CARGO} test --features="fusedev,fuse-t" -- --nocapture

docker-smoke:
	docker run --env RUST_BACKTRACE=1 --rm --privileged --volume ${current_dir}:/fuse-rs rust:1.68 sh -c "rustup component add clippy rustfmt; cd /fuse-rs; make smoke-all"

testoverlay:
	cd tests/testoverlay && ${CARGO} build

# Setup xfstests env and run.
xfstests:
	./tests/scripts/xfstests.sh