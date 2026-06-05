# Format code
fmt:
    cargo fmt --all

# Check if code is formatted
fmtcheck:
    cargo fmt --all -- --check

# Run code linter
lint:
    cargo clippy --all-targets --workspace -- --deny warnings

# Build code with all feature combinations
build_features:
    cargo hack check --feature-powerset --no-dev-deps

# Run unit tests
test:
    cargo test --workspace --all-features

# Check code (CI)
check:
    cargo --version
    rustc --version
    just fmtcheck
    just lint
    just build_features
    just test

# Run fuzz test for 30 seconds
fuzz target:
    cargo +nightly fuzz run {{target}} -- -max_total_time=30 -max_len=50

# Check fuzz targets (CI; requires nightly)
check_fuzz:
    just fuzz compile_parse_tree
    just fuzz compile_text
    just fuzz display_parse_tree
    just fuzz parse_value_rtt
    just fuzz parse_witness_json_rtt
    just fuzz reconstruct_value

# Build fuzz tests
build_fuzz:
    cargo +nightly fuzz check

# Check the standalone fuzz crate compiles
check_fuzz_crate:
    cargo rbmt --lock-file existing run --toolchain nightly -- check --manifest-path fuzz/Cargo.toml

# Run fuzz target unit tests
check_fuzz_bins:
    cargo rbmt --lock-file existing run --toolchain nightly -- test --manifest-path fuzz/Cargo.toml --bins

# Run CI-equivalent checks plus strict non-mutating RBMT checks
check_all:
    cargo rbmt toolchains
    cargo rbmt --lock-file existing test --toolchain stable
    cargo rbmt --lock-file existing test --toolchain nightly
    cargo rbmt --lock-file existing test --toolchain msrv
    cargo test
    cargo rbmt --lock-file existing lint
    cargo rbmt --lock-file existing docs
    cargo rbmt --lock-file existing docsrs
    cargo rbmt fmt --check
    rustup target add wasm32-unknown-unknown
    just build_wasm
    cargo rbmt tools cargo-fuzz
    just check_fuzz_crate
    just check_fuzz_bins
    cargo rbmt --lock-file existing integration
    cargo rbmt --lock-file existing bench
    cargo rbmt --lock-file existing api --baseline master
    cargo rbmt --lock-file existing prerelease --baseline master
    just build_integration

# Build integration tests
build_integration:
    cargo test --locked --no-run --manifest-path ./bitcoind-tests/Cargo.toml

# Run integration tests (requires custom elementsd)
check_integration:
    cargo test --locked --manifest-path ./bitcoind-tests/Cargo.toml

# Build code for the WASM target
build_wasm:
    cargo check --target wasm32-unknown-unknown

# Remove all temporary files
clean:
    rm -rf target
    rm -rf fuzz/target
