# Casting

A SimplicityHL type can be cast into another SimplicityHL type if both types share the same structure.
The structure of a type has to do with how the type is implemented on the Simplicity "processor".
I will spare you the boring details.

Below is a table of types that can be cast into each other.

| Type           | Casts To (And Back)                |
|----------------|------------------------------------|
| `bool`         | `Either<(), ()>`                   |
| `Option<A>`    | `Either<(), A>`                    |
| `u1`           | `bool`                             |
| `u2`           | `(u1, u1)`                         |
| `u4`           | `(u2, u2)`                         |
| `u8`           | `(u4, u4)`                         |
| `u16`          | `(u8, u8)`                         |
| `u32`          | `(u16, u16)`                       |
| `u64`          | `(u32, u32)`                       |
| `u128`         | `(u64, u64)`                       |
| `u256`         | `(u128, u128)`                     |
| `(A)`          | `A`                                |
| `(A, B, C)`    | `(A, (B, C))`                      |
| `(A, B, C, D)` | `((A, B), (C, D))`                 |
| …              | …                                  |
| `[A; 0]`       | `()`                               |
| `[A; 1]`       | `A`                                |
| `[A; 2]`       | `(A, A)`                           |
| `[A; 3]`       | `(A, (A, A))`                      |
| `[A; 4]`       | `((A, A), (A, A))`                 |
| …              | …                                  |
| `List<A, 2>`   | `Option<A>`                        |
| `List<A, 4>`   | `(Option<[A; 2]>, List<A, 2>)`     |
| `List<A, 8>`   | `(Option<[A; 4]>, List<A, 4>)`     |
| `List<A, 16>`  | `(Option<[A; 8]>, List<A, 8>)`     |
| `List<A, 32>`  | `(Option<[A; 16]>, List<A, 16>)`   |
| `List<A, 64>`  | `(Option<[A; 32]>, List<A, 32>)`   |
| `List<A, 128>` | `(Option<[A; 64]>, List<A, 64>)`   |
| `List<A, 256>` | `(Option<[A; 128]>, List<A, 128>)` |
| `List<A, 512>` | `(Option<[A; 256]>, List<A, 256>)` |
| …              | …                                  |

## Casting Rules

Type `A` can be cast into itself (reflexivity).

If type `A` can be cast into type `B`, then type `B` can be cast into type `A` (symmetry).

If type `A` can be cast into type `B` and type `B` can be cast into type `C`, then type `A` can be cast into type `C` (transitivity).

## Casting Expression

All casting in SimplicityHL happens explicitly through a casting expression.

```rust
<Input>::into(input)
```

The above expression casts the value `input` of type `Input` into some output type.
The input type of the cast is explicit while the output type is implicit.

In SimplicityHL, the output type of every expression is known.

```rust
let x: u32 = 1;
```

In the above example, the meaning of the expression `1` is clear because of the type `u32` of variable `x`.
Here, `1` means a string of 31 zeroes and 1 one.
_In other contexts, `1` could mean something different, like a string of 255 zeroes and 1 one._

The SimplicityHL compiler knows the type of the outermost expression, and it tries to infer the types of inner expressions based on that.
When it comes to casting expressions, the compiler has no idea about the input type of the cast.
The programmer needs to supply this information by annotating the cast with its input type.

```rust
let x: u32 = <(u16, u16)>::into((0, 1));
```

In the above example, we cast the tuple `(0, 1)` of type `(u16, u16)` into type `u32`.
Feel free to consult the table above to verify that this is a valid cast.
