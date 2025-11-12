use std::num::NonZero;

use simplicityhl::{
    num::NonZeroPow2Usize,
    parse::CallName,
    str::{AliasName, FunctionName},
    types::AliasedType,
};

use crate::completion::types::FunctionTemplate;

/// Get completion of builtin functions. They are all defined in [`simplicityhl::parse::CallName`]
pub fn get_builtin_functions() -> Vec<FunctionTemplate> {
    let ty = AliasedType::from(AliasName::from_str_unchecked("T"));
    let function_name = FunctionName::from_str_unchecked("fn");
    let Some(some) = NonZero::new(1) else {
        return vec![];
    };

    let functions = vec![
        CallName::UnwrapLeft(ty.clone()),
        CallName::UnwrapRight(ty.clone()),
        CallName::Unwrap,
        CallName::IsNone(ty.clone()),
        CallName::Assert,
        CallName::Debug,
        CallName::Panic,
        CallName::Fold(function_name.clone(), NonZeroPow2Usize::TWO),
        CallName::ArrayFold(function_name.clone(), some),
        CallName::ForWhile(function_name.clone()),
        CallName::TypeCast(ty.clone()),
    ];

    functions.iter().filter_map(match_callname).collect()
}

/// Match [`simplicityhl::parse::CallName`] and return [`FunctionTemplate`]
pub fn match_callname(call: &CallName) -> Option<FunctionTemplate> {
    let doc = builtin_documentation(call);
    match call {
        CallName::UnwrapLeft(aliased_type) => {
            let ty = aliased_type.to_string();
            Some(FunctionTemplate::new(
                "unwrap_left",
                vec![format!("{ty}")],
                vec![format!("Either<{ty}, U>")],
                ty,
                doc,
            ))
        }
        CallName::UnwrapRight(aliased_type) => {
            let ty = aliased_type.to_string();
            Some(FunctionTemplate::new(
                "unwrap_right",
                vec![format!("{ty}")],
                vec![format!("Either<T, {ty}>")],
                ty,
                doc,
            ))
        }
        CallName::Unwrap => Some(FunctionTemplate::simple(
            "unwrap",
            vec!["Option<T>".to_string()],
            "T",
            doc,
        )),
        CallName::IsNone(aliased_type) => {
            let ty = aliased_type.to_string();
            Some(FunctionTemplate::new(
                "is_none".to_string(),
                vec![format!("{ty}")],
                vec![format!("Option<{ty}>")],
                "bool",
                doc,
            ))
        }
        CallName::Assert => Some(FunctionTemplate::simple(
            "assert!",
            vec!["condition: bool".to_string()],
            "()",
            doc,
        )),
        CallName::Panic => Some(FunctionTemplate::simple("panic!", vec![], "()", doc)),
        CallName::Debug => Some(FunctionTemplate::simple(
            "dbg!",
            vec!["T".to_string()],
            "T",
            doc,
        )),
        CallName::Fold(_, _) => Some(FunctionTemplate::new(
            "fold",
            vec!["f".to_string(), "N".to_string()],
            vec![
                "list: List<E,N>".to_string(),
                "initial_accumulator: A".to_string(),
            ],
            "A",
            doc,
        )),
        CallName::ArrayFold(_, _) => Some(FunctionTemplate::new(
            "array_fold",
            vec!["f".to_string(), "N".to_string()],
            vec![
                "array: [E; N]".to_string(),
                "initial_accumulator: A".to_string(),
            ],
            "A",
            doc,
        )),
        CallName::ForWhile(_) => Some(FunctionTemplate::new(
            "for_while",
            vec!["f".to_string()],
            vec!["accumulator: A".to_string(), "context: C".to_string()],
            "Either<B, A>",
            doc,
        )),

        // The `into` function has a different structure compared to the other built-ins,
        // so we defined a different snippet for it.
        CallName::TypeCast(_) => Some(FunctionTemplate {
            display_name: "into".into(),
            generics: vec!["Input".to_string()],
            args: vec!["input".to_string()],
            return_type: "Output".into(),
            description: doc,
            snippet: "<${1:Input}>::into".into(),
        }),
        CallName::Jet(_) | CallName::Custom(_) => None,
    }
}

/// Return documentation for builtin function.
fn builtin_documentation(call: &CallName) -> String {
    String::from(match call {
        CallName::UnwrapLeft(_) =>
    "Extracts the left variant of an `Either` value.\n
Returns the left-side value if it exists, otherwise panics.\n
```simplicityhl
let x: Either<u8, u8> = Left(42);
let y: u8 = unwrap_left::<u8>(x); // 42
```",
        CallName::UnwrapRight(_) =>
    "Extracts the right variant of an `Either` value.\n
Returns the right-side value if it exists, otherwise panics.\n
```simplicityhl
let x: Either<u8, u8> = Right(128);
let y: u8 = unwrap_right::<u8>(x); // 128
```",
        CallName::Unwrap =>
    "Unwraps an `Option` value, panicking if it is `None`.\n
```simplicityhl
let x: Option<u8> = Some(5);
let y: u8 = unwrap(x); // 5
```",
        CallName::IsNone(_) =>
    "Checks if an `Option` is `None`.\n
Returns `true` if the value is `None`, otherwise `false`.
",
        CallName::Assert => "Panics when `condition` is false.",
        CallName::Panic => "Unconditionally terminates program execution.",
        CallName::Debug =>
    "Prints a value if debugging symbols is enabled and returns it unchanged. \n
```simplicityhl
let x: u32 = dbg!(42); // prints 42, returns 42
```",
        CallName::Fold(_, _) =>
    "Fold a list of bounded length by repeatedly applying a function.\n
- Signature: `fold::<f, N>(list: List<E, N>, initial_accumulator: A) -> A`
- Fold step: `fn f(element: E, acc: A) -> A`
- Note: `N` is a power of two; lists hold fewer than `N` elements.\n
Example: sum a list of 32-bit integers.\n
```simplicityhl
fn sum(elt: u32, acc: u32) -> u32 {
    let (_, acc): (bool, u32) = jet::add_32(elt, acc);
    acc
}

fn main() {
    let xs: List<u32, 8> = list![1, 2, 3];
    let s: u32 = fold::<sum, 8>(xs, 0);
    assert!(jet::eq_32(s, 6));
}
```",
        CallName::ArrayFold(_, _) =>
    "Fold a fixed-size array by repeatedly applying a function.\n
- Signature: `array_fold::<f, N>(array: [E; N], initial_accumulator: A) -> A`
- Fold step: `fn f(element: E, acc: A) -> A`\n
Example: sum an array of 7 elements.\n
```simplicityhl
fn sum(elt: u32, acc: u32) -> u32 {
    let (_, acc): (bool, u32) = jet::add_32(elt, acc);
    acc
}

fn main() {
    let arr: [u32; 7] = [1, 2, 3, 4, 5, 6, 7];
    let sum: u32 = array_fold::<sum, 7>(arr, 0);
    assert!(jet::eq_32(sum, 28));
}
```",
        CallName::ForWhile(_) =>
    "Run a function `f` repeatedly with a bounded counter. The loop stops early when the function returns a successful value.\n
- Signature: `for_while::<f>(initial_accumulator: A, readonly_context: C) -> Either<B, A>`
- Loop body: `fn f(acc: A, ctx: C, counter: uN) -> Either<B, A>` where `N ∈ {1, 2, 4, 8, 16}`\n
Example: stop when `counter == 10`.\n
```simplicityhl
fn stop_at_10(acc: (), _: (), i: u8) -> Either<u8, ()> {
    match jet::eq_8(i, 10) {
        true => Left(i),   // success → exit loop
        false => Right(acc), // continue with same accumulator
    }
}

fn main() {
    let out: Either<u8, ()> = for_while::<stop_at_10>((), ());
    assert!(jet::eq_8(10, unwrap_left::<()>(out)));
}
```",
        CallName::TypeCast(_) => type_casting_documentation(),
        CallName::Jet(_) | CallName::Custom(_) => "",
    })
}

/// Return documentation for `into` casting.
fn type_casting_documentation() -> &'static str {
    "A SimplicityHL type can be cast into another SimplicityHL type if both types share the same structure.

## Casting Rules

- Type `A` can be cast into itself (reflexivity).

- If type `A` can be cast into type `B`, then type `B` can be cast into type `A` (symmetry).

- If type `A` can be cast into type `B` and type `B` can be cast into type `C`, then type `A` can be cast into type `C` (transitivity).

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
| ...            | ...                                |
| `[A; 0]`       | `()`                               |
| `[A; 1]`       | `A`                                |
| `[A; 2]`       | `(A, A)`                           |
| `[A; 3]`       | `(A, (A, A))`                      |
| `[A; 4]`       | `((A, A), (A, A))`                 |
| ...            | ...                                |
| `List<A, 2>`   | `Option<A>`                        |
| `List<A, 4>`   | `(Option<[A; 2]>, List<A, 2>)`     |
| `List<A, 8>`   | `(Option<[A; 4]>, List<A, 4>)`     |
| `List<A, 16>`  | `(Option<[A; 8]>, List<A, 8>)`     |
| `List<A, 32>`  | `(Option<[A; 16]>, List<A, 16>)`   |
| `List<A, 64>`  | `(Option<[A; 32]>, List<A, 32>)`   |
| `List<A, 128>` | `(Option<[A; 64]>, List<A, 64>)`   |
| `List<A, 256>` | `(Option<[A; 128]>, List<A, 128>)` |
| `List<A, 512>` | `(Option<[A; 256]>, List<A, 256>)` |
| ...            | ...                                |

## Casting Expression

All casting in SimplicityHL happens explicitly through a casting expression.

```simplicityhl
<Input>::into(input)
```

The above expression casts the value `input` of type `Input` into some output type.
The input type of the cast is explicit while the output type is implicit.
"
}
