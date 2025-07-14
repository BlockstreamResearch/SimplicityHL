SimplicityHL is a high-level language for writing Bitcoin smart contracts.

SimplicityHL looks and feels like [Rust](https://www.rust-lang.org). Just how Rust compiles down to assembly language, SimplicityHL compiles down to [Simplicity](https://github.com/BlockstreamResearch/simplicity) bytecode. Developers write Simfony, full nodes execute Simplicity.

**SimplicityHL is a work in progress and is not yet ready for production use.**

```rust
let a: u32 = 10;
let b = {
    let c: u32 = 2;
    let d: u32 = 3;
    assert!(jet::eq_32(a, 10)); // Use variables from outer scopes
    let a: u32 = 7; // Shadow variables from outer scopes
    jet::max_32(jet::max_32(c, d), a) // Missing ; because the block returns a value
};
assert!(jet::eq_32(b, 7));
```

Take a look at the [example programs](https://github.com/BlockstreamResearch/simfony/tree/master/examples).

## MSRV

This crate should compile with any feature combination on **Rust 1.78.0** or higher.

## Simplicity's need for a high-level language

Simplicity introduces a groundbreaking low-level programming language and machine model meticulously crafted for blockchain-based smart contracts. The primary goal is to provide a streamlined and comprehensible foundation that facilitates static analysis and encourages reasoning through formal methods. While the elegance of the language itself is distilled into something as succinct as fitting onto a T-shirt, it's important to note that the simplicity of the language doesn't directly equate to simplicity in the development process. Simfony revolves around demystifying and simplifying the complexities involved in this ecosystem.

The distinguishing aspects that set Simplicity apart from conventional programming languages are:

- **Distinct Programming Paradigm**: Simplicity's programming model requires a paradigm shift from conventional programming. It hinges on reasoning about programs in a functional sense with a focus on combinators. This intricacy surpasses even popular functional languages like Haskell, with its own unique challenges.
- **Exceptional Low-Level Nature**: Unlike high-level languages such as JavaScript or Python, Simplicity operates at an extremely low level, resembling assembly languages. This design choice enables easier reasoning about the formal semantics of programs, but is really work on directly.

## SimplicityHL

SimplicityHL is a high-level language that compiles to Simplicity. It maps programming concepts from Simplicity onto programming concepts that developers are more familar with. In particular, Rust is a popular language whose functional aspects fit Simplicity well. SimplicityHL aims to closely resemble Rust.

Just how Rust is compiled to assembly language, SimplicityHL is compiled to Simplicity. Just how writing Rust doesn't necessarily produce the most efficient assembly, writing SimplicityHL doesn't necessarily produce the most efficient Simplicity code. The compilers try to optimize the target code they produce, but manually written target code can be more efficient. On the other hand, a compiled language is much easier to read, write and reason about. Assembly is meant to be consumed by machines while Rust is meant to be consumed by humans. Simplicity is meant to be consumed by Bitcoin full nodes while SimplicityHL is meant to be consumed by Bitcoin developers.

## Installation

Clone the repo and build the SimplicityHL compiler using cargo.

```bash
git clone https://github.com/BlockstreamResearch/SimplicityHL.git
cd SimplicityHL
cargo build
```

Optionally, install the SimplicityHL compiler using cargo.

```bash
cargo install --path .
```

## Usage

The SimplicityHL compiler takes two arguments:

1. A path to a SimplicityHL program file (`.simf`)
1. A path to a SimplicityHL witness file (`.wit`, optional)

The compiler produces a base64-encoded Simplicity program. Witness data will be included if a witness file is provided.

```bash
./target/debug/simc examples/test.simf examples/test.wit
```

### VSCode extension

See the installation [instructions](./vscode/README.md).
