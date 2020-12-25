build:
	cargo build --features="fusedev"
	cargo build --features="virtiofs,with-serde"
	cargo build --features="vhost-user-fs,with-serde"

check: build
	cargo fmt -- --check
	cargo clippy --all-features -- -Dclippy::all
	cargo test --all-features -- --nocapture
