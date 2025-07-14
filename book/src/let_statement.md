# Let Statement

Variables are defined in let statements, [just like in Rust](https://doc.rust-lang.org/std/keyword.let.html).

```rust
let x: u32 = 1;
```

The above let statement defines a variable called `x`.
The variable is of type `u32` and it is assigned the value `1`.

```rust
let x: u32 = f(1337);
```

Variables can be assigned to the output value of any expression, such as function calls.

## Explicit typing

In SimplicityHL, the type of a defined variable **always** has to be written.
This is different from Rust, which has better type inference.

## Immutability

SimplicityHL variables are **always** immutable.
There are no mutable variables.

## Redefinition and scoping

The same variable can be defined twice in the same scope.
The later definition overrides the earlier definition.

```rust
let x: u32 = 1;
let x: u32 = 2;
assert!(jet::eq_32(x, 2)); // x == 2
```

Normal scoping rules apply:
Variables from outer scopes are available inside inner scopes.
A variable defined in an inner scope shadows a variable of the same name from an outer scope.

```rust
let x: u32 = 1;
let y: u32 = 2;
let z: u32 = {
    let x: u32 = 3;
    assert!(jet::eq_32(y, 2)); // y == 2
    x
};
assert!(jet::eq_32(x, 3)); // z == 3
```

## Pattern matching

There is limited pattern matching support inside let statements.

```rust
let (x, y, _): (u8, u16, u32) = (1, 2, 3);
let [x, _, z]: [u32; 3] = [1, 2, 3];
```

In the first line, the tuple `(1, 2, 3)` is deconstructed into the values `1`, `2` and `3`.
These values are assigned to the variable names `x`, `y` and `_`.
The variable name `_` is a special name that ignores its value.
In the end, two variables are created: `x: u32 = 1` and `y: u16 = 2`.

Similarly, arrays can be deconstructed element by element and assigned to a variable each.
