# Unstable features

Unstable features are experimental compiler capabilities. They may change
or be removed before stabilization.

## Viewing available unstable features

Run `simc --help`; the features are listed under the `-Z` flag.

## Enabling an unstable feature

Pass `-Z <feature-name>` to `simc`.

## `raw_hash`

`raw_hash::<T>(tuple)` hashes a tuple of unsigned integers with SHA-256:

```rust
let digest: u256 = raw_hash::<(u8, u256)>((0x02, public_key));
```

This is the same as:

```rust
let ctx: Ctx8 = jet::sha_256_ctx_8_init();
let ctx: Ctx8 = jet::sha_256_ctx_8_add_1(ctx, 0x02);
let ctx: Ctx8 = jet::sha_256_ctx_8_add_32(ctx, public_key);
let digest: u256 = jet::sha_256_ctx_8_finalize(ctx);
```

In particular, the type parameter selects which `add_N` jets run; the digest does not
commit to it. `raw_hash::<(u8, u8)>((0x01, 0x02))` and `raw_hash::<(u16,)>((0x0102,))`
produce the same digest, as does any other type with the same bytes, such as an alias
of `u32` versus a plain `u32`. If your protocol needs the digest to be unambiguous,
commit to the type yourself, for example by hashing a domain-separation tag first.

## `bitcoin`

A `target` header selects the chain whose jets the program uses. Enable it with
`-Z bitcoin`:

```rust
target bitcoin;

fn main() {
    jet::bip_0340_verify((param::ALICE_PUBLIC_KEY, jet::sig_all_hash()), witness::ALICE_SIGNATURE)
}
```

The chain is `elements` or `bitcoin`; without a header, programs use Elements jets.
The header may only open the entry file, after the `simc` directive if there is one.

`target bitcoin;` also needs the `unstable-bitcoin` Cargo feature, which currently pins
unreleased rust-simplicity changes:

```sh
cargo run --features unstable-bitcoin -- -Z bitcoin examples/bitcoin_p2pk.simf --args examples/p2pk.args
```

Use `CompiledProgram::satisfy_with_bitcoin_env` to satisfy and
prune a Bitcoin program in its transaction environment. Bitcoin programs only run
on a Simplicity-enabled test node, not on Bitcoin mainnet; see
`bitcoind-tests/README.md`.

## Adding or stabilizing a feature

See the rustdoc on `UnstableFeature` in `src/unstable.rs`; the procedures
live next to the code they mutate, so they cannot drift.
