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
	cargo test ${TARGET} --features="fusedev" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="virtiofs" --no-default-features  -- --nocapture --skip integration
	cargo test ${TARGET} --features="vhost-user-fs" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="fusedev,virtiofs" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="fusedev,async-io" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="virtiofs,async-io" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="vhost-user-fs,async-io" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="fusedev,virtiofs,async-io" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --features="fusedev,persist" --no-default-features -- --nocapture --skip integration
	cargo test ${TARGET} --all-features -- --nocapture --skip integration

smoke:
	cargo test ${TARGET} --features="fusedev,persist" -- --nocapture

smoke-all: smoke
	cargo test ${TARGET} --features="fusedev,persist" -- --nocapture --ignored

build-macos:
	cargo build --features="fusedev"
	cargo build --features="fusedev,fuse-t"

check-macos: build-macos
	cargo fmt -- --check
	cargo clippy --features="fusedev" -- -Dwarnings
	cargo test --features="fusedev" -- --nocapture --skip integration
	cargo clippy --features="fusedev,fuse-t" -- -Dwarnings
	cargo test --features="fusedev,fuse-t" -- --nocapture --skip integration

smoke-macos: check-macos
	cargo test --features="fusedev,fuse-t" -- --nocapture

docker-smoke:
	docker run --env RUST_BACKTRACE=1 --rm --privileged --volume ${current_dir}:/fuse-rs rust:1.68 sh -c "rustup component add clippy rustfmt; cd /fuse-rs; make smoke-all"
