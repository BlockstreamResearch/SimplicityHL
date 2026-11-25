# Syntax / language features

## SYN-1: Infix operators (easy)

Owner: Seth Schoen

Status: In progress

Comparison, bitwise and logical operators on booleans and unsigned
integers. This reimplements those operators from PR #232 on current
`master`. Arithmetic operators are SYN-2, because the type system rework
(TYPE-1, TYPE-3) will change how integer results are typed.

An implementation of this design is in progress and hasn't been submitted
yet. The files, functions and tests named below are those of that
implementation.

### 1. Scope

| Operators | Operand types | Result |
| --- | --- | --- |
| `==` `!=` | `bool` and `u1`..`u256` | `bool` |
| `<` `<=` `>` `>=` | `u1`..`u256` | `bool` |
| `&` `\|` `^` | `bool` and `u1`..`u256` | the operand type |
| prefix `!` | `bool` and `u1`..`u256` | the operand type |
| `&&` `\|\|` | `bool` | `bool` |

Both operands must have the same type. There is no implicit widening.
Type aliases work, because operands are checked as `ResolvedType`, in which
aliases are already expanded. Compound types (tuples, arrays, `Option`,
`Either`, `List`, enums) and ordering on `bool` are out of scope by design,
and give `Error::OperatorUnsupportedType`.

Everything is behind `-Z infix_operators`
(`UnstableFeature::InfixOperators`).

### 2. Lexer (`src/lexer.rs`)

New tokens: `EqEq`, `BangEq`, `LtEq`, `AmpAmp`, `PipePipe`, `Amp`, `Pipe`,
`Caret`, `Bang`. `<` and `>` reuse `LAngle` and `RAngle`.

- There is no `>=` token, because `let x: Option<u8>= None;` is valid. The
  lexer emits `>` and `=`, and the expression parser joins them into `>=`
  when their spans are adjacent, as Rust does after generics. `<=` is one
  token, since `<` is never followed by `=` in a type.
- Within each `choice`, a symbol comes before any shorter symbol that is its
  prefix.
- A macro token (`assert!`, `panic!`, `dbg!`, `list!`) must not be followed
  by `=`, so `list!=x` is the variable `list` compared with `x`.

### 3. Parser (`src/parse/`)

#### Parse tree

`parse::SingleExpressionInner` gains `BinaryOp(BinaryOp)`, with
`{ op: InfixOp, lhs, rhs, span }`, and `Not(Not)`, with
`{ operand, span }`. Operator spans run from the start of the left operand to
the end of the right one, and the span of `!a` includes the `!`. `ExprTree`,
`Display` and the `arbitrary` impls cover both. Generated operands are
always parenthesized, so that displaying a generated tree and parsing it
again gives the same tree.

#### Precedence

As in Rust, from the tightest binding to the loosest:

1. prefix `!`
2. `&`
3. `^`
4. `|`
5. `==` `!=` `<` `<=` `>` `>=`, which don't associate: `a < b < c` and
   `a == b != c` are errors that suggest parentheses or `&&`
6. `&&`
7. `||`

So `a & b == c` is `(a & b) == c`, unlike in C.

`SingleExpression::parser` names the `choice` of atoms `atom`, then
builds one boxed level per row of the table: a `foldr` of `!` tokens, then
`binary_level(operand, op)`, a left fold, for each binary level. The
comparison level collects every `op operand` pair and reports an error when
there is more than one. Each level is boxed, because it refers to the level
below twice, which would otherwise double the parser's type at every level.
chumsky's `pratt` module isn't used: it needs the `unstable` feature, which
is outside chumsky's semver guarantees.

`>=` is `RAngle` followed by `Eq`. When the spans aren't adjacent, the
parser reports "Expected `>=`, found `> =`" with help to remove the space.

#### `<` and `>` elsewhere

- Casts `<T>::into(x)` and generic arguments `name::<…>` start only in prefix
  position, so a `<` after an operand doesn't conflict with them.
- In `fold::<f, 4>`, `4` is a literal token rather than an expression, so the
  `>` that follows it is safe.
- Error recovery (`nested_delimiters` in `grammar/mod.rs` and in the block
  parser in `grammar/expression.rs`) doesn't treat `<` and `>` as a bracket
  pair, because a comparison `<` has no matching `>`. The type parser passes
  them as the main delimiters, which `nested_delimiters` always nests.

### 4. Analysis: desugaring to existing constructs

There isn't any operator node in the abstract syntax tree.
`src/ast/analyze/infix.rs` rewrites each operator into an equivalent
parse-tree expression made of jet calls, `<T>::into` casts, blocks with a
`let`, and `match` on a boolean, and checks that with the existing checker.
The builders for these nodes are `pub(crate)` methods on
`parse::SingleExpression`: `boolean`, `decimal`, `variable`, `tuple`,
`type_cast`, `jet_call`, `bool_match`, `assignment`, `block`,
`into_expression` and `from_expression`.

This means:

- `src/compile/`, debug symbols, the call tracker and witness handling don't
  change;
- type errors in operands come from the existing checks, at the operands'
  own spans;
- jets are found by name through the jet hinter, and every jet used is a
  core jet, available for Elements and Bitcoin;
- the type system rework has fewer places to break (section 6).

Synthesized nodes carry the operator expression's span. As a result, all
jet calls written for one operator share one debug symbol, which shows the
operator expression.

#### Lowerings

`N` is the operand width.

| Source | Rewritten to |
| --- | --- |
| `a == b`, `uN` with an `eq_N` jet (1, 8–64, 256) | `jet::eq_N(a, b)` |
| `a == b`, `u128` | `jet::eq_256` on the operands zero-extended to `u256` |
| `a < b`, `a <= b`, `u8`–`u64` | `jet::lt_N(a, b)`, `jet::le_N(a, b)` |
| `a < b`, `a <= b`, `u1` | `!a & b`, `!a \| b`, with `complement_1`, `and_1`, `or_1` |
| `a < b`, `a <= b`, `u128`, `u256` | a borrow chain (below) |
| `a > b`, `a >= b` | `b < a`, `b <= a` |
| `a != b` | `!(a == b)` |
| `!a`, `u1`, `u8`–`u64` | `jet::complement_N(a)` |
| `!a`, `bool` | `<u1>::into(jet::complement_1(<bool>::into(a)))` |
| `a & b`, `u1`, `u8`–`u64` | `jet::and_N(a, b)`, and likewise `or`, `xor` |
| `a & b`, `u128`, `u256` | the jet on each 64-bit limb, in a block (below) |
| `==` and bitwise operators on `bool` | the `u1` form on `<bool>::into(a)` and `<bool>::into(b)`, cast back with `<u1>::into` for bitwise results |
| any operator on `u2`, `u4` | the `u8` form on zero-extended operands; bitwise results cut back with `jet::rightmost_8_N` |
| `a && b` | `match a { false => false, true => b }` |
| `a \|\| b` | `match a { false => b, true => true }` |

**Zero extension.** `extend_to_u8` doubles the width one step at a time with
`<(uN, uN)>::into((0, x))`, the `u2N` whose high half is zero and whose low
half is `x`. `u128` extends to `u256` in one step.

**Limbs.** `split_into_limbs` writes the statement that splits the one or
two operands into 64-bit limbs, bound to names of its own:

```text
let ((lhs_1, lhs_0), (rhs_1, rhs_0)): ((u64, u64), (u64, u64)) =
    <(u128, u128)>::into((a, b));
let (operand_1, operand_0): (u64, u64) = <u128>::into(a);
```

For `u256` the pattern is `((lhs_3, lhs_2), (lhs_1, lhs_0))`. Splitting once
into limbs costs much less than splitting recursively into halves, because
each split copies the operands.

- A bitwise operator applies the `_64` jet to the limbs at each position
  (one operand for `!`, two for the others) and joins the results with
  `<((u64, u64), (u64, u64))>::into(…)`.
- `a < b` is a borrow chain: `jet::subtract_64` on the least significant
  limbs, then `jet::full_subtract_64` on each next pair, passing on the
  borrow, which is bound to `borrow`. `a < b` exactly when `a - b` borrows.
  `a <= b` exactly when `b - a` doesn't, so it subtracts the other way and
  ends in the complement of `borrow`.

**Hygiene.** The operands are evaluated inside the splitting `let`, before
any name is bound, and the rest of the block refers only to names the block
binds. So the names can't capture a variable of the program.

**Evaluation order.** `&&` and `||` short-circuit. Every other operator
evaluates both operands, which is why ordering on `u1` uses jets rather
than a cheaper `match` that would skip `b`. `>` and `>=` evaluate the right
operand first, because they swap the operands. The only effects of
evaluation are failure and `dbg!` output, so the swap changes which failure
is reported when both operands fail, and the order of `dbg!` output. The
user documentation states the `dbg!` difference. Keeping source order would
need a compile-side node to swap a pair, which section 4's approach avoids.

**Cost.** Casts are free: `Call::compile` returns the argument unchanged.
Each executed node costs 100 milliweight, about as much as a comparison
jet, and copying a value costs its bit width. So a `match` often costs more
than a jet, and a `let` that splits wide operands is the most expensive part
of a wide operation.

The lowerings above were chosen by measuring alternatives with
`operator_costs`, in milliweight above a baseline function:

| Operation | Chosen | Cost | Rejected | Cost |
| --- | --- | ---: | --- | ---: |
| `u32` `!=` | `complement_1` of `eq_32` | 895 | `match` on `eq_32` | 1445 |
| `u1` `<` | `!a & b` with jets | 762 | zero extension to `u8`; `match` with both operands bound | 2938; 1518 |
| `u128` `==` | `eq_256` on zero-extended operands | 2448 | `eq_64` on each half | 6060 |
| `u128` `<` | borrow chain | 8259 | comparison of halves | 9293 |
| `u256` `<` | borrow chain | 22319 | recursive comparison of halves | 47082 |
| `u256` `&` | `and_64` on four limbs | 9288 | recursive halves | 16008 |
| `bool` `==` | `eq_1` | 477 | `match` | 606 |
| `bool` `&` | `and_1` | 582 | `match` with both operands bound | 1618 |

Operators on `u2` and `u4` keep the zero extension to `u8`, which costs
about 400 milliweight per `u4` operand and 800 per `u2` operand, for the zero
constants and pairs. There isn't a jet that pads 2 or 4 bits. Packing both
operands into one `u8` would avoid the constants, but it evaluates each
operand twice or needs a `let`, which costs more.

#### Operand types

The checker works top down: `analyze(from, expected_ty, scope)`.

- `&&` and `||` have `bool` operands.
- Bitwise operators and `!` take their operand type from the expected
  type. `!` is the bitwise complement, which on `bool` is logical negation,
  as in Rust.
- Comparisons have result type `bool`, which doesn't tell the operand type.
  `operand_type(expression, scope)` finds it from `lhs`, and failing that from
  `rhs`, for variables, boolean literals, boolean-valued operators,
  parenthesized expressions, `!` and bitwise expressions (from their own
  operands), and jet and custom-function calls (from their signatures).
  Integer literals, witnesses, parameters, casts and blocks give `None`. When
  both operands give `None`, the error is `OperatorOperandTypeUnknown`.

`expect_boolean` runs before operand typing, so `let x: u8 = a == b`
reports the result type, at the operator.

#### Errors

| Variant | Message |
| --- | --- |
| `OperatorUnsupportedType { op, ty }` | Operator `` `{op}` `` cannot be applied to values of type `` `{ty}` `` |
| `OperatorOperandTypeUnknown { op }` | Cannot determine the type of the operands of `` `{op}` ``; assign one operand to a variable with a declared type first |

A result type mismatch uses the existing `ExpressionTypeMismatch`.

### 5. Feature gating

`BinaryOp` and `Not` require `UnstableFeature::InfixOperators` through
`impl_require_feature!`, which also recurses into their operands.

### 6. Dependencies on the current type and module systems

| Coupling point | Rating | Under a reworked checker |
| --- | --- | --- |
| `operand_type` | isolated | Becomes "infer both operands, unify", and `OperatorOperandTypeUnknown` goes away or changes. |
| Expected type flowing top down to bitwise operators, `!` and logical operators | contained | Unchanged in check mode. In synthesis mode, bitwise operators and `!` take their type from their operands, as `operand_type` already does. |
| Structural casts between `bool` and `u1`, `(uN, uN)` and `u2N`, and pairs of pairs | contained: `bool_to_u1`, `u1_to_bool`, `extend_to_u8`, `comparison_jets`, `split_into_limbs`, `limbs_tuple` | If casts become nominal, these helpers stop type-checking and must be rewritten with jets, which cost more. |
| Re-analysis of `let`, `match` on `bool`, blocks, casts and jet calls | contained | Depends on these constructs keeping their typing rules, which any rework keeps. |
| `ResolvedType`, `AliasedType`, `UIntType` helpers | contained | The rework has to keep "is `bool`", "as unsigned integer" and tuple construction. |
| Jets by name (`jet_call`, the jet hinter in `operand_type`) | contained | Changes if jets move into a module namespace. |
| Function lookup in `operand_type` | isolated | Changes with qualified paths. |
| Synthesized names in `split_into_limbs` and `borrow_chain` | isolated | Can use fresh names if the rework adds them. |

The feature gate lets upstream change operator typing during the rework
without breaking compatibility.

### 7. Open questions

For the type system and module rework (TYPE-1, MOD-1):

- Will structural casts between `bool` and `u1`, and between `(uN, uN)` and
  `u2N`, survive the type rework? Every lowering for `bool`, `u2`, `u4`,
  `u128` and `u256` depends on them.
- Will jets stay addressable as `jet::name` from any module?
- If the rework brings constraint-based inference, should operators become
  ordinary overloaded functions in a prelude rather than desugarings in the
  compiler?
