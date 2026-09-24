# Daemon integration tests

Run from the repository root using the shared workspace lockfile. Compile without a daemon:

```sh
cargo test --locked -p bitcoind-tests --test spend_utxo --no-run
```

To run, set `ELEMENTSD_EXE` to a Simplicity-enabled Elements daemon or enter `nix develop .#elements` ([daemon pin](elementsd-simplicity.nix)):

```sh
just check_integration
```

The daemon target is opt-in (`--test spend_utxo`), even with `--all-features`. CI only compiles it on Linux, macOS and Windows. Explicit runs use isolated regtest.
