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

## Experimental Bitcoin test

`bitcoin_spend_utxo` locks coins to [`examples/bitcoin_p2pk.simf`](../examples/bitcoin_p2pk.simf) on regtest and spends them back. It needs the `unstable-bitcoin` feature and `BITCOIND_EXE` set to Bitcoin Inquisition [`v29.2-inq-simplicity`](https://github.com/delta1/bitcoin/releases/tag/v29.2-inq-simplicity), which uses Simplicity leaf version `0xbe`:

```sh
BITCOIND_EXE=/path/to/bitcoind just check_bitcoin_integration
```
