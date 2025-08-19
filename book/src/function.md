# Functions

Functions are defined and called [just like in Rust](https://doc.rust-lang.org/std/keyword.fn.html).

```rust
fn add(x: u32, y: u32) -> u32 {
    let (carry, sum): (bool, u32) = jet::add_32(x, y);
    match carry {
        true => panic!(), // overflow
        false => {}, // ok
    };
    sum
}
```

The above example defines a function called `add` that takes two parameters: variable `x` of type `u32` and variable `y` of type `u32`. The function returns a value of type `u32`.

The body of the function is a block expression `{ ... }` that is executed from top to bottom.
The function returns on the final line _(note the missing semicolon `;`)_.
In the above example, `x` and `y` are added via the `add_32` jet.
The function then checks if the carry is true, signaling an overflow, in which case it panics.
On the last line, the value of `sum` is returned.

The above function is called by writing its name `add` followed by a list of arguments `(40, 2)`.
Each parameter needs an argument, so the list of arguments is as long as the list of parameters.
Here, `x` is assigned the value `40` and `y` is assigned the value `2`.

```rust
let z: u32 = add(40, 2);
```

## No early returns

SimplicityHL has no support for an early return via a "return" keyword.
The only branching that is available is via [match expressions](./match_expression.md).

## No recursion

SimplicityHL has no support for recursive function calls.
A function can be called inside a function body if it has been defined before.
This means that a function cannot call itself.
Loops, where `f` calls `g` and `g` calls `f`, are also impossible.

What _is_ possible are stratified function definitions, where level-0 functions depend on nothing, level-1 functions depend on level-0 functions, and so on.

```rust
fn level_0() -> u32 {
    0
}

fn level_1() -> u32 {
    let (_, next) = jet::increment_32(level_0());
    next
}

fn level_2() -> u32 {
    let (_, next) = jet::increment_32(level_1());
    next
}
```

## Order matters

If function `g` calls function `f`, then `f` **must** be defined before `g`.

```rust
fn f() -> u32 {
    42
}

fn g() -> u32 {
    f()
}
```

## Main function

The `main` function is the entry point of each SimplicityHL program.
Running a program means running its `main` function.
Other functions are called from the `main` function.

```rust
fn main() {
    // ...
}
```

The `main` function is a reserved name and must exist in every program.
SimplicityHL programs are always "binaries".
There is no support for "libraries".

## Jets

Jets are predefined and optimized functions for common use cases.

```rust
jet::add_32(40, 2)
```

Jets live inside the namespace `jet`, which is why they are prefixed with `jet::`.
They can be called without defining them manually.

It is usually more efficient to call a jet than to manually compute a value.

[The jet documentation](https://docs.rs/simfony-as-rust/latest/simfony_as_rust/jet/index.html) lists each jet and explains what it does.
