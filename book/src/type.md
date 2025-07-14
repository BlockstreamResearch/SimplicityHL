# Types and Values

SimplicityHL mostly uses a subset of Rust's types.
It extends Rust in some ways to make it work better with Simplicity and with the blockchain.

## Boolean Type

| Type   | Description     | Values          |
|--------|-----------------|-----------------|
| `bool` | Boolean         | `false`, `true` |

Values of type `bool` are truth values, which are either `true` or `false`.

## Integer Types

| Type   | Description     | Values                                                 |
|--------|-----------------|--------------------------------------------------------|
| `u1`   | 1-bit integer   | `0`, `1`                                               |
| `u2`   | 2-bit integer   | `0`, `1`, `2`, `3`                                     |
| `u4`   | 4-bit integer   | `0`, `1`, …, `15`                                      |
| `u8`   | 8-bit integer   | `0`, `1`, …, `255`                                     |
| `u16`  | 16-bit integer  | `0`, `1`, …, `65535`                                   |
| `u32`  | 32-bit integer  | `0`, `1`, …, `4294967295`                              |
| `u64`  | 64-bit integer  | `0`, `1`, …, `18446744073709551615`                    |
| `u128` | 128-bit integer | `0`, `1`, …, `340282366920938463463374607431768211455` |
| `u256` | 256-bit integer | `0`, `1`, …, 2<sup>256</sup> - 1[^u256max]             |

Unsigned integers range from 1 bit to 256 bits.
[`u8`](https://doc.rust-lang.org/std/primitive.u8.html) to [`u128`](https://doc.rust-lang.org/std/primitive.u128.html) are also supported in Rust.
`u1`, `u2`, `u4` and `u256` are new to SimplicityHL.
Integer values can be written in decimal notation `123456`, binary notation[^bin] `0b10101010` or hexadecimal notation[^hex] `0xdeadbeef`.
There are no signed integers.

[^u256max]: The maximal value of type `u256` is `115792089237316195423570985008687907853269984665640564039457584007913129639935`.
[^bin]: The number of bits must be equal to the bit width of the type.
[^hex]: The number of hex digits must correspond to the bit width of the type.

## Tuple Types

| Type         | Description | Values                                            |
|--------------|-------------|---------------------------------------------------|
| `()`         | 0-tuple     | `()`                                              |
| `(A)`        | 1-tuple     | `(a0,)`, `(a1,)`, …                               |
| `(A, B)`     | 2-tuple     | `(a0, b0)`, `(a1, b1)`, `(a2, b2)`, `(a3, b3)`, … |
| …            | …           | …                                                 |
| `(A, B, …)`  | n-tuple     | `(a0, b0, …)`, …                                  |

[Tuples work just like in Rust](https://doc.rust-lang.org/std/primitive.tuple.html).

The empty tuple `()` contains no information.
It is also called the "unit".
It is mostly used as the return type of functions that don't return anything.

Singletons `(a0,)` must be written with an extra comma `,` to differentiate them from function calls.

Bigger tuples `(a0, b0, …)` work like in pretty much any other programming language.
Each tuple type `(A1, A2, …, AN)` defines a sequence `A1`, `A2`, …, `AN` of types.
Values of that type must mirror the sequence of types:
A tuple value `(a1, a2, …, aN)` consists of a sequence `a1`, `a2`, …, `aN` of values, where `a1` is of type `A1`, `a2` is of type `A2`, and so on.
Tuples are always finite in length.

> Tuples are different from arrays:
> Each element of a tuple can have a different type.
> Each element of an array must have the same type.

## Array Types

| Type     | Description | Values                                            |
|----------|-------------|---------------------------------------------------|
| `[A; 0]` | 0-array     | `[]`                                              |
| `[A; 1]` | 1-array     | `[a0]`, `[a1]`, …                                 |
| `[A; 2]` | 2-array     | `[a0, a1]`, `[a2, a3]`, `[a4, a5]`, `[a6, a7]`, … |
| …        | …           | …                                                 |
| `[A; N]` | n-array     | `[a0, …, aN]`, …                                  |

[Arrays work just like in Rust](https://doc.rust-lang.org/std/primitive.array.html).

The empty array `[]` is basically useless, but I included it for completeness.

Arrays `[a0, …, aN]` work like in pretty much any other programming language.
Each array type `[A; N]` defines an element type `A` and a length `N`.
An array value `[a0, …, aN]` of that type consists of `N` many elements `a0`, …, `aN` that are each of type `A`.
Arrays are always of finite length.

> Arrays are different from tuples:
> Each element of an array must have the same type.
> Each element of a tuple can have a different type.

## List Types

| Type                      | Description         | Values                                               |
|---------------------------|---------------------|------------------------------------------------------|
| `List<A, 2>`              | <2-list             | `list![]`, `list![a1]`                               |
| `List<A, 4>`              | <4-list             | `list![]`, …, `list![a1, a2, a3]`                    |
| `List<A, 8>`              | <8-list             | `list![]`, …, `list![a1, …, a7]`                     |
| `List<A, 16>`             | <16-list            | `list![]`, …, `list![a1, …, a15]`                    |
| `List<A, 32>`             | <32-list            | `list![]`, …, `list![a1, …, a31]`                    |
| `List<A, 64>`             | <64-list            | `list![]`, …, `list![a1, …, a62]`                    |
| `List<A, 128>`            | <128-list           | `list![]`, …, `list![a1, …, a127]`                   |
| `List<A, 256>`            | <256-list           | `list![]`, …, `list![a1, …, a255]`                   |
| `List<A, 512>`            | <512-list           | `list![]`, …, `list![a1, …, a511]`                   |
| …                         | …                   | …                                                    |
| `List<A,`2<sup>N</sup>`>` | <2<sup>N</sup>-list | `list![]`, …, `list![a1, …, a`(2<sup>N</sup> - 1)`]` |

Lists hold a variable number of elements of the same type.
This is similar to [Rust vectors](https://doc.rust-lang.org/std/vec/struct.Vec.html), but SimplicityHL doesn't have a heap.
In SimplicityHL, lists exists on the stack, which is why the maximum list length is bounded.

<2-lists hold fewer than 2 elements, so zero or one element.
<4-lists hold fewer than 4 elements, so zero to three elements.
<8-lists hold fewer than 8 elements, so zero to seven elements.
And so on.
For technical reasons, the list bound is always a power of two.
The bound 1 is not supported, because it would only allow empty lists, which is useless.

> Lists are different from arrays:
> List values hold a variable number of elements.
> Array values hold a fixed number of elements.

On the blockchain, you pay for every byte that you use.
If you use an array, then you pay for every single element.
For example, values of type `[u8; 512]` cost roughly as much as 512 many `u8` values.
However, if you use a list, then you only pay for the elements that you actually use.
For example, the type `List<u8, 512>` allows for up to 511 elements.
If you only use three elements `list![1, 2, 3]`, then you pay for exactly three elements.
You **don't** pay for the remaining 508 unused elements.

## Option Types

| Type        | Values                            |
|-------------|-----------------------------------|
| `Option<A>` | `None`, `Some(a0)`, `Some(a1)`, … |

Options represent values that might not be present. [They work just like in Rust](https://doc.rust-lang.org/std/option/index.html).

An option type is generic over a type `A`.
The value `None` is empty.
The value `Some(a)` contains an inner value `a` of type `A`.

In Rust, we implement options as follows.

```rust
enum Option<A> {
    None,
    Some(A),
}
```

## Either Types

| Type           | Values                                                 |
|----------------|--------------------------------------------------------|
| `Either<A, B>` | `Left(a0)`, `Left(a1)`, …, `Right(b0)`, `Right(b1)`, … |

Sum types represent values that are of some "left" type in some cases and that are of another "right" type in other cases.
[They work just like in the either crate](https://docs.rs/either/latest/either/enum.Either.html).
[The Result type from Rust is very similar, too](https://doc.rust-lang.org/std/result/index.html).

A sum type type is generic over two types, `A` and `B`.
The value `Left(a)` contains an inner value `a` of type `A`.
The value `Right(b)` contains an inner value `b` of type `B`.

In Rust, we implement sum types as follows.

```rust
enum Either<A, B> {
    Left(A),
    Right(B),
}
```
