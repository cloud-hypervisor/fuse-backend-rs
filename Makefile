current_dir := $(shell dirname $(realpath $(firstword $(MAKEFILE_LIST))))

build:
	cargo build --features="fusedev"

check: build
	cargo fmt -- --check
	cargo clippy --features="fusedev" -- -Dclippy::all
	cargo test --features="fusedev" -- --nocapture --skip integration

smoke: check
	cargo test --features="fusedev" -- --nocapture

docker-smoke:
	docker run --rm --privileged -v ${current_dir}:/fuse-rs rust:1.47.0 sh -c "rustup component add clippy rustfmt; cd /fuse-rs; make smoke"
