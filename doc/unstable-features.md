# Unstable features

Unstable features are experimental compiler capabilities. They may change
or be removed before stabilization.

## Viewing available unstable features

Run `simc --help`; the features are listed under the `-Z` flag.

## Enabling an unstable feature

Pass `-Z <feature-name>` to `simc`.

## Feature notes

`--help` names each feature; these have semantics that do not fit on that line.

### `chain`

`chain!(ctx = seed(), step(ctx), ..., last(ctx))` threads one value through a
sequence of steps under a named hole.

* The first step is the seed: it binds the hole with `=` and cannot read it.
* Later steps see the previous step's value, shadowing as a repeated `let` does.
* The last step is the chain's value, so it takes its type from the chain's
  surroundings rather than from the hole. A `Ctx8` chain can end in a `u256`.
* A step's type is read off its callee. A step typed by its context instead
  (`unwrap`, `dbg!`, a cast) must be written `ctx: Ctx8 = <expr>`.

A chain compiles to the `let` chain written in its place. Rewriting *nested*
calls into a chain does not preserve the CMR, because binding a value
materializes it in the environment; spelling the nesting out as `let`s changes
it the same way.

See `examples/chain.simf` and `examples/chain_sighash_modes.simf`.

### `imports`

See `doc/architecture.md` for how imports and flattening affect the CMR.

## Adding or stabilizing a feature

See the rustdoc on `UnstableFeature` in `src/unstable.rs`; the procedures
live next to the code they mutate, so they cannot drift.
