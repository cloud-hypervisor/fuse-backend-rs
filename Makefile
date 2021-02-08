build:
	cargo build --features="fusedev"
	cargo build --features="virtiofs"
	cargo build --features="vhost-user-fs"

check: build
	cargo fmt -- --check
	cargo clippy --features="fusedev" -- -Dclippy::all
	cargo clippy --features="virtiofs" -- -Dclippy::all
	cargo test --features="fusedev" -- --nocapture
	cargo test --features="virtiofs" -- --nocapture
