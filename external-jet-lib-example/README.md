# External Jet Loading

SimplicityHL supports loading custom jet sets at runtime from a shared library (`.so` / `.dylib` / `.dll`). This crate is an end-to-end example of how to build such a library and consume it.

## How It Works

### 1. Enable the feature flag

The external jet machinery lives behind the `external-jets` Cargo feature in the main `simplicityhl` crate. Both the library and its consumer must opt in:

```toml
[dependencies]
simplicityhl = { path = "..", features = ["external-jets"] }
```

### 2. Build a `cdylib` that exports the required symbols

See [src/lib.rs](src/lib.rs) and [src/jet.rs](src/jet.rs) for a minimal implementation with a single `verify` jet.

### 3. Initialize the library at program startup

Before compiling any Simplicity programs, call `init_external_jet_lib` with the path to the compiled `.so` / `.dylib` / `.dll`:

```rust
unsafe {
    simplicityhl::jet::external::init_external_jet_lib("/path/to/libexternal_jet_lib_example.dylib")
        .expect("failed to load external jet lib");
}
```

### 4. Pass `ExternalJetHinter` to the compiler

`ExternalJetHinter` implements `JetHinter` and delegates `parse_jet` / `construct_verify` to the loaded library. Pass it when constructing a `TemplateProgram`:

```rust
use simplicityhl::{jet::external::ExternalJetHinter, TemplateProgram};

let program = TemplateProgram::new(simf_code, Box::new(ExternalJetHinter::new()))
    .expect("compilation failed");
```

The compiler will call `parse_jet` whenever it encounters an unknown jet name, forwarding the lookup to your shared library.

## Building the Example

```sh
# Build the shared library
cargo build -p external-jet-lib-example

# Run the consumer binary, pointing it at the compiled dylib
cargo run -p external-jet-lib-example --bin external-lib-consumer -- \
    target/debug/libexternal_jet_lib_example.dylib
```

## Security Notes

Loading a shared library executes arbitrary native code in the current process. Only load libraries from trusted, verified sources.
