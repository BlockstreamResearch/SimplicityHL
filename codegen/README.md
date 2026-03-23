# Code and documentation generation

## Generate Rust code

Generate Rust modules, like in this [repository](https://github.com/BlockstreamResearch/SimplicityHL-as-rust):

```bash
cargo run --bin codegen -- modules --out-dir modules/
```

## Generate Jet documentation in a JSON file

Generate JSON file containing jet information:

```bash
cargo run --bin codegen -- docs elements.json
```

This JSON file contains an array of jets, each of which includes the following information:
- "haskell_name" -- The name of the jet used in the Haskell and Rust code.
- "simplicityhl_name" -- The name of the jet as it is used in SimplicityHL.
- "section" -- The category to which the jet belongs.
- "input_type" -- The input types represented as a vector of `AliasedType`s in SimplicityHL, separated by comma.
- "output_type" -- The output type represented as an `AliasedType` in SimplicityHL.
- "description" -- A description of the jet's functionality.
- "deprecated" (optional) -- Indicates if jet is deprecated.

> [!NOTE]
> Structure of generated JSON similar to file in [`simplicity-lang-org`](https://github.com/BlockstreamResearch/simplicity-lang-org/blob/28c67437c6cef3b111339443293a672d237d72a3/jets.json) repo, but it contains only array, without an object `elements` above.

## Installation

Install `simplicityhl` via `cargo` with `docs` feature -- `simplicityhl-codegen` would be installed alongside `simc`:

```bash
cargo install simplicityhl --features docs
```

Or install from local repository:

```bash
cargo install --path ./ --features docs
```
