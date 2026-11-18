# Fuzzing

The `fuzz` crate fuzzes the request server of `fuse-backend-core` with
[libFuzzer](https://llvm.org/docs/LibFuzzer.html) through
[cargo-fuzz](https://github.com/rust-fuzz/cargo-fuzz). It is a workspace of its
own, so the main workspace keeps building on a stable toolchain.

- `server` feeds the input to `Server::handle_message()`.
- `async_server` feeds it to `Server::async_handle_message()`.

The harness lives in `common/src/server.rs`, whose module documentation
describes the input format and what the harness checks.

## Running

The tests of the `common` crate run on a stable toolchain. They check the
seeds, write them to `corpus/<target>`, replay the inputs in `regressions`, and
run a short mutation loop:

```bash
cd fuzz
cargo test -p common
```

The fuzz targets need a nightly toolchain and `cargo install cargo-fuzz`:

```bash
cd fuzz
cargo +nightly fuzz run server -- -max_total_time=900 -timeout=60
cargo +nightly fuzz run async_server -- -max_total_time=900 -timeout=60
```

Add `-jobs=N -workers=N` to run N processes in parallel. A failure leaves its
input in `artifacts/<target>`. Once the bug is fixed, copy the input to
`regressions/` so that the stable tests replay it.
