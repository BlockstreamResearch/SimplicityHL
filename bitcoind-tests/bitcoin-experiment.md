# Experimental Bitcoin integration test

The daemon-backed Bitcoin test is `tests/bitcoin_spend_utxo.rs`. It uses
[Bitcoin Inquisition v29.2-inq-simplicity](https://github.com/delta1/bitcoin/releases/tag/v29.2-inq-simplicity),
commit `32f5911cab012703b1e80c7e19a9f52253e2b377`, and the adjacent modified
`rust-simplicity` checkout selected by the local Cargo patches.

From the repository root:

```sh
BITCOIND_EXE=/absolute/path/to/compatible/bitcoind \
  cargo test --locked --manifest-path bitcoind-tests/Cargo.toml \
  --features unstable-bitcoin --test bitcoin_spend_utxo -- --nocapture
```

The test starts a fresh temporary regtest node with P2P disabled, creates a new
wallet and random script key, activates Simplicity, compiles
`examples/bitcoin_p2pk.simf`, and confirms both the lock and spend back to that
wallet. The node stops and temporary files are removed when the test finishes.
A missing or incompatible daemon fails the test. This command needs no faucet,
external network or files from the evidence directory.

The source declares `target bitcoin;`. SimplicityHL's `unstable-bitcoin` feature
and `-Z bitcoin` compiler gate enable that target; Rust's backend Cargo feature
is named `bitcoin`. Node configuration stays in the integration test.

Shared offline transaction construction lives in `tests/common/bitcoin.rs`.

The earlier custom-Signet experiment and its confirmations remain recorded in
`contexts/bitcoind-tests/evidence/2026-10-06-bitcoin-target/`. Its private wallets,
RPC cookies and signing keys remain local and are not test fixtures.
