# Match Expression

A match expression conditionally executes code branches.
Which branch is executed depends on the input to the match expression.

```rust
let result: u32 = match f(42) {
    Left(x: u32) => x,
    Right(x: u16) => jet::left_pad_low_16_32(x),
};
```

In the above example, the output of the function call `f(42)` is matched.
`f` returns an output of type `Either<u32, u16>`.
If `f(42)` returns a value that matches the pattern `Left(x: u32)`, then the first match arm is executed.
This arm simply returns the value `x`.
Alternatively, if `f(42)` returns a value that matches the pattern `Right(x: u16)`, then the second match arm is executed.
This arm extends the 16-bit number `x` to a 32-bit number by padding its left with zeroes.
Because of type constraints, the output of `f` must match one of these two patterns.
The whole match expression returns a value of type `u32`, from one of the two arms.

## Explicit typing

In SimplicityHL, the type of variables inside match arms must **always** be written.
This is different from Rust, which has better type inference.

## Pattern matching

There is limited support for pattern matching inside match expressions.

Boolean values can be matched.
The Boolean match expression is the replacement for an "if-then-else" in SimplicityHL.

```rust
let bit_flip: bool = match false {
    false => true,
    true => false,
};
```

Optional values can be matched.
The `Some` arm introduces a variable which must be explicitly typed.

```rust
let unwrap_or_default: u32 = match Some(42) {
    None => 0,
    Some(x: u32) => x,
};
```

Finally, `Either` values can be matched.
Again, variables that are introduced in match arms must be explicitly typed.

```rust
let map_either: u32 = match Left(1337) {
    Left(x: u32) => f(x),
    Right(y: u32) => f(y),
};
```

Match expressions don't support further pattern matching, in contrast to Rust.

```rust
let unwrap_or_default: u32 = match Some((4, 2)) {
    None => 0,
    // this doesn't compile
    Some((y, z): (u16, u16)) => <(u16, u16)>::into((y, z)),
};
```

However, the match arm can contain code that performs the deconstruction.
For example, the tuple `x` of type `(u16, u16)` can be deconstructed into two integers `y` and `z` of type `u16`.

```rust
let unwrap_or_default: u32 = match Some((4, 2)) {
    None => 0,
    Some(x: (u16, u16)) => {
        let (y, z): (u16, u16) = x;
        <(u16, u16)>::into((y, z))
    }
};
```

The match arm can also contain match expressions for further deconstruction.
For example, the sum value `x` of type `Either<u32, u32>` can be matched as either `Left(y: u32)` or `Right(z: u32)`.

```rust
let unwrap_or_default: u32 = match Some(Left(42)) {
    None => 0,
    Some(x: Either<u32, u32>) => match x {
        Left(y: u32) => y,
        Right(z: u32) => z,
    },
};
```
