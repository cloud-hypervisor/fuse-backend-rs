build:
	cargo build --features="fusedev"
	cargo build --features="virtiofs"
	cargo build --features="vhost-user-fs"

check: build
	cargo fmt -- --check
	cargo clippy --all-features -- -Dclippy::all
	cargo test --all-features -- --nocapture
