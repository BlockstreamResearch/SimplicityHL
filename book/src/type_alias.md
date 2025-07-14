# Type Aliases

SimplicityHL currently doesn't support Rust-like `struct`s for organizing data.

```rust
struct User {
  active: bool,
  id: u256,
  sign_in_count: u64,
}
```

SimplicityHL programmers have to handle long tuples of unlabeled data, which can get messy.

```rust
(bool, u256, u64)
```

To help with the situation, programmers can define custom type aliases.
Aliases define a new name for an existing type.
In contrast, `struct`s define an entirely new type, so aliases are different from `struct`s.
However, aliases still help us to make the code more readable.

```rust
type User = (bool, u256, u64);
```

There is also a list of builtin type aliases.
These aliases can be used without defining them.

| Builtin Alias    | Definition                    |
|------------------|-------------------------------|
| `Amount1`        | `Either<(u1, u256), u64>`     |
| `Asset1`         | `Either<(u1, u256), u256>`    |
| `Confidential1`  | `(u1, u256)`                  |
| `Ctx8`           | `(List<u8, 64>, (u64, u256))` |
| `Distance`       | `u16`                         |
| `Duration`       | `u16`                         |
| `ExplicitAmount` | `u256`                        |
| `ExplicitAsset`  | `u256`                        |
| `ExplicitNonce`  | `u256`                        |
| `Fe`             | `u256`                        |
| `Ge`             | `(u256, u256)`                |
| `Gej`            | `((u256, u256), u256)`        |
| `Height`         | `u32`                         |
| `Lock`           | `u32`                         |
| `Message`        | `u256`                        |
| `Message64`      | `[u8; 64]`                    |
| `Nonce`          | `Either<(u1, u256), u256>`    |
| `Outpoint`       | `(u256, u32)`                 |
| `Point`          | `(u1, u256)`                  |
| `Pubkey`         | `u256`                        |
| `Scalar`         | `u256`                        |
| `Signature`      | `[u8; 64]`                    |
| `Time`           | `u32`                         |
| `TokenAmount1`   | `Either<(u1, u256), u64>`     |
