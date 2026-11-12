# Module system

Rust-2018-style modules, external crates, and content-based identity.

| ID    | Name              | Owner   | Status       |
|-------|-------------------|---------|--------------|
| MOD-1 | Internal modules  | @KyrylR | Proposed     |
| MOD-2 | External crates   | TBD     | Needs design |
| MOD-3 | External crates 2 | TBD     | Needs design |

## MOD-1: Internal modules

`mod x;` loads `x.simf`.
`use` only brings names into scope.

### Design

#### Syntax

- `mod x;` declares module `x` and loads its items from a file.
- `mod x { ... }` declares it inline.
- Both may be `pub`.
- `mod x;` means exactly `mod x { <items of the file> }` at the same place. Flattening does that replacement and nothing
  else.

#### File layout

There is one layout rule.
Every module owns a directory for the files of its child modules:

- the crate root file `main.simf` owns the directory it is in;
- the module file `D/x.simf` owns `D/x/`;
- the inline module `mod y { ... }` inside a module that owns `D` owns `D/y/`.

So `mod math;` in `main.simf` loads `math.simf`, `mod ops;` in `math.simf` loads `math/ops.simf`, and `mod z;` inside an
inline `mod n { }` of the root loads `n/z.simf`.

There is no `x/mod.simf` form for the time being.
In scope of MOD-1 the focus is minimal working internal module system to support the dependant roadmap items.
The `x/mod.simf` form can be added later within the MOD-N roadmap item.

Every component of the path below the crate root's directory must match its module name exactly.
Each directory and the file name, checked against the listing of the parent directory.
So `mod Utils;` does not load `utils.simf`, on a case-insensitive file system either.
A directory is checked only when a file in it is loaded, so an inline module without file children needs none.

Module names are identifiers, so the character set is already restricted and there is no `-`/`_` conversion.

Each file is loaded at most once.
This rejects `mod main;` in `main.simf` and two declarations that reach one file through links.

`use` never reads a file of the crate.
`use` only looks names up in the module tree that `mod` declarations built.
A `use` through a `--dep` alias still loads dependency files until MOD-2.

A file is part of the crate only if a `mod` declares it.
An undeclared `x.simf` next to `main.simf` is never opened.
If a `use crate::x::...` fails, the compiler only checks whether `x.simf` or `x/` exists, to suggest the `mod x;` to
add.

#### The crate directory and `--project-root`

The crate root in MOD-1 is defined by passing the file that is passed to `simc` for the compilation. `simc foo.simf`
makes `foo.simf` the root of the crate, whatever it's named.
In other words, the directory of the crate root file plays the role of that project root.
It anchors the module tree, and module files must stay inside it.

A manifest that names the crate root is a question for MOD-2 or a build tool, because only crates with several roots
need one.

So `--project-root` no longer changes where module files are found.
A module's file must not depend on a command-line flag.
The flag stays the default context of `--dep`, and the entry file must still be inside it.

#### Paths

`crate::a::b` starts at the crate root.

`self::a` starts at the current module.

`super::a` starts at the parent module.
`super::super::a` goes up twice.
`super` cannot go above the crate root.

Any other first segment names a `--dep` dependency.
With `--dep math=<dir>`, a `use` path that starts with `math::` goes to that dependency.
For example, `use math::arith::func;` (`func()` is called within the code), with `--dep math=libs/math` flag loads
`libs/math/arith.simf`.

`self` and `super` are reserved keywords. There are no glob imports and no qualified paths in expressions.

#### Visibility

Items and modules are private unless marked `pub`.

A private item or module is visible in the module that declares it and in every module below it, as in Rust.

A `use` may keep or narrow the visibility of what it imports, never widen it.
`pub use` of a private item or module is rejected at the `use`, as in Rust (E0364, E0365).
Otherwise a descendant could publish its ancestor's private items to the whole crate.

A public item of a private module may be re-exported with `pub use` (the facade pattern).

Privacy is checked against the module that holds a binding, by identity, so it does not matter through which alias a
module is reached.
In

```rust
mod a {
    fn secret() {}

    mod child {
        use crate::a as p;
        use self::p::secret;
    }
}
```

`child` sees `secret`.

#### Order and cycles

A `mod`, a `use` or any other item is position independent.
The position does not impact what an import resolves to, what a function body or a type sees, whether the program
compiles, and its CMR.

Cyclic `use` is allowed.
Modules may import from each other in both directions, which is handled by the multi-pass resolver.
Imports that can only be resolved through each other are reject, same as in Rust.

See import cycles examples in the table below

| Program                                                                                    | Result                                                                                                       |
|--------------------------------------------------------------------------------------------|--------------------------------------------------------------------------------------------------------------|
| `mod a { use crate::b::g; pub fn f() … } mod b { use crate::a::f; pub fn g() … }`          | Compiles. The two modules import from each other, but every name's chain ends at a `fn`.                     |
| `mod a { pub use crate::b::f; } mod b { pub use crate::a::f; }`                            | `ImportCycle`: `crate::b::f -> crate::a::f -> crate::b::f`                                                   |
| The same with three modules, a → b → c → a                                                 | `ImportCycle`                                                                                                |
| `mod a { pub use crate::b::f; } mod b { pub fn f() … }`, then `use crate::a::f;`           | Compiles. The chain reaches a real definition, so there's no cycle.                                          |
| `use crate::q as p; use crate::p as q;` (module aliases)                                   | `ImportCycle`: `crate::q -> crate::p -> crate::q`                                                            |
| `mod a { pub use crate::b::m; } mod b { pub use crate::a::m; }` plus `use crate::a::m::f;` | `ImportCycle`, reported once. The path through `m` isn't reported again.                                     |
| `use crate::f;` at the crate root, with no `f`                                             | "Item `f` could not be found". Strictly, this is a cycle of length 1, but "not found" is the useful message. |

Names are resolved in three passes:

1. Collect

Every module gets an identity, and every function, type alias and enum a definition.
The names that items declare are bound in their module, one binding per name in each of the three namespaces (types,
functions, modules).

2. Resolve imports

Each `use` looks its names up by module identity, in the complete set of names of the module it names, including what
that module imports itself.
While a name it needs is not bound yet, it waits for it.
This runs until no import binds anything new, so it computes the least fixed point, which does not depend on the order
of the steps.
A name gets its binding in a namespace once, and a step runs again only when a name it waits for gets bound, at most
three times per name, so the pass takes time linear in the number of imports and path segments.

3. Order and analyze the definitions

For each function, type alias, enum and `main`, collect the names it uses, in its signature, its body or its type, and
look them up in the tables.
Order the definitions so that each comes after the ones it uses.
The strongly connected components of this graph, found by an iterative search that visits the definitions in source
order.
So analysis never stops inside one definition to analyze another, and deep chains does not need a deep recursion.
A program whose definitions all come before their uses keeps its source order.
A component that uses itself is a recursion, reported where a definition uses one that is not analyzed yet, which
happens once for a simple cycle.

A module is referred to by its identity.

A module binds a name at most once in each namespace, whether by items or imports, and there is no shadowing between
them.
So programs like below, will compile.

```rust
mod m {}
type m = u8;
fn m() {}
```

The second binding in source order is reported, with the error of its kind, see the table below.

| Second binding in source order              | Error                                                                 | Should be the same on master?          |
|---------------------------------------------|-----------------------------------------------------------------------|----------------------------------------|
| `fn f() {}` after `fn f() {}`               | `FunctionRedefined` ("Function `f` was defined multiple times")       | yes                                    |
| `type T = u16;` after `type T = u8;`        | `RedefinedAlias`                                                      | yes                                    |
| `fn f() {}` after `use crate::a::f;`        | `FunctionRedefined`, at the `fn`                                      | yes                                    |
| `use crate::a::f;` after `fn f() {}`        | `RedefinedItem` ("Item `f` was defined multiple times"), at the `use` | yes                                    |
| `use crate::b::f;` after `use crate::a::f;` | `RedefinedItem`, at the second `use`                                  | yes                                    |
| `mod x {}` after `mod x {}`                 | `ModuleRedefined`                                                     | no (such behaviour is more consistent) |

A local item never hides an import of the same name, and an import never hides a local item.
Both are errors.
Rust does the same for explicit imports (E0255). This applies to names at module level only.

Everywhere else, MOD-1 makes item order irrelevant.
During error reporting it still needs a fixed rule for which duplicate to report, and it reports the second one in
source order.
For functions, type aliases and imports, that's the same place master reports.

For modules it isn't.
Master reports `ModuleRedefined` at the **first** `mod x {}` (snippet below, line 1), while the branch reports it at the
second (snippet below, line 2).

```rust
mod x {}
mod x {}
```

On master an item sees only the definitions above it, so every program that master compiles has its definitions before
their uses.
Such a program keeps its source order in pass 3, so it compiles to the same program, debug symbols included.

Existing programs see two changes:

- programs rejected only because of the order of their items now compile;
- a function that calls itself is reported as `RecursiveFunction` instead of as an undefined function.

Item order does not reach the CMR (see `doc/architecture.md`).
With `--debug`, debug symbols are numbered in the order in which analysis reaches the calls, so a reordered program can
get a different debug CMR, as moving a function already could on master.
A flattened program keeps the source order, so it gets the same debug CMR as the multi-file one.

In summary, we have the following:

| Program                                                                                                                  | MOD-1                           |
|--------------------------------------------------------------------------------------------------------------------------|---------------------------------|
| Any order of `mod`, `use` and other items, with an acyclic module graph                                                  | accepted, same CMR in any order |
| A function above the `use` it needs, or above the function it calls                                                      | accepted                        |
| A `use` through an alias that a later `use` makes, also when other imports bind the same name in other namespaces        | accepted in every order         |
| Two modules import from each other (`mod a { use crate::b::g; pub fn f() {} } mod b { use crate::a::f; pub fn g() {} }`) | accepted                        |
| Re-exports that only resolve through each other (`mod a { pub use crate::b::f; } mod b { pub use crate::a::f; }`)        | rejected, `ImportCycle`         |
| Functions of two modules that call each other                                                                            | rejected, `RecursiveFunction`   |

Resolving by identity needs no order of modules, so MOD-1 does not sort them. Crate blocks are MOD-2.

#### Diagnostics

All of the above are collected without stopping at the first one.
A module whose file fails to load stays in the tree without items, so paths into it are not reported again.

Each import cycle is reported once, as one strongly connected component of the imports that stayed unresolved.
An import that could only import itself, such as `use crate::typo;` at the crate root, is reported as not found.

Analysis goes on after a failed import or a broken item, and reports the errors of the items that do not depend on them.

Examples of error for common situations:

| Situation                                                                       | Error                                                                  | Reported at                        |
|---------------------------------------------------------------------------------|------------------------------------------------------------------------|------------------------------------|
| `mod x;` and no `x.simf`                                                        | `ModuleFileNotFound`: names the expected path                          | the `mod x;` declaration           |
| A name bound twice in one namespace of a module, by items or imports in any mix | `FunctionRedefined`/`RedefinedAlias`/`ModuleRedefined`/`RedefinedItem` | the second binding in source order |
| A file reached twice, including `mod main;`                                     | `ModuleFileLoadedTwice`                                                | the second declaration             |
| A module file that resolves outside the crate directory                         | `ModuleFileOutsideCrate`                                               | the declaration                    |
| Imports that can only be resolved through each other                            | `ImportCycle`                                                          | a `use` in the cycle               |
| A function that calls itself, directly or through others                        | `RecursiveFunction`, once for a simple cycle                           | the call that closes the cycle     |
| A type alias or enum defined in terms of itself                                 | `RecursiveAlias`, once for a simple cycle                              | the type that closes the cycle     |
| `pub use` of a private item or module                                           | `PrivateItemReexported`                                                | the `use`                          |
| `super` above the crate root                                                    | `SuperAboveCrateRoot`                                                  | the `use`                          |
| A `--dep` alias named `self` or `super`                                         | `DependencyAliasIsPathRoot`: rename the dependency                     | the command line                   |
| `mod x;` in a `--dep` dependency file                                           | `ModuleDeclInDependency`                                               | the declaration                    |
| A path of the entry crate into a generated `unit_N` module                      | `ModuleNotFound` or `UnresolvedItem`                                   | the `use`                          |
| `mod x;` compiled from a single string (`TemplateProgram::new`)                 | `ModuleFileNotLoaded`: suggests `mod x { ... }`                        | the declaration                    |
| An enum in a module file                                                        | `Grammar`: enums only at the top level of the root file                | the enum                           |

Note regarding `unit_N`: with `--dep`, each dependency file is wrapped as `mod unit_N { ... }` at the top level, where N
is the file's source id.
It is a responsibility of MOD-2 to get rid of `unit_N`.

Note regarding enums: it is responsibility of MOD-2 and TYPE-2 to make enums "work".

#### Dependencies (`--dep`)

MOD-1 does not need crate identity, and it changes `--dep` only where noted below.
Dependencies keep the file-based form until MOD-2 gives them crate roots and a `CrateId`.
So that is MOD-2's constraint entirely.

Inside a dependency, each file is a module, and `use alias::dir::file::item` loads `dir/file.simf`.

Within a dependency, `use crate::dir::file::item` loads from that dependency's own root, as before.
So under one flag, `use crate::b::x;` loads `b.simf` in a dependency file and must name a declared module in the entry
crate.

`self::` works inside a dependency file. `super` cannot leave the file.

A dependency file cannot declare `mod x;`.
Making it a module tree needs a crate root, which is MOD-2's question of library and entry roles.

A dependency cannot import a file of the entry crate.
The entry crate is loaded only through `mod`.

A dependency path in a module file of the entry crate is resolved from that file, so it gets the `--dep` contexts of the
file's location.

When flattened, each dependency file still becomes `mod unit_N { ... }`, placed before the entry crate's items.
If the entry crate binds that name at its top level, the generated name gets `_` appended until it is free.

For example, this fixture on the current master:

```rust
use lib::module::add;

mod unit_1 {}

fn main() {}
```

Compiles because the entry file is wrapped in `mod unit_0`, so its `unit_1` is really `unit_0::unit_1` and never meets
the dependency's `unit_1`. (this is how it works on the current master)

With MOD-1, it would change to appending `_` until the name is free.
This is stab for compatibility purposes and expected to be removed in MOD-2.

The entry crate cannot name a generated module.
A dependency is reached only through its `--dep` alias, and naming `unit_N` would skip the `--dep` context of a
dependency's own dependencies.
The names stay valid in the flattened program, which has no `--dep`.

`N` is a source id.
The entry crate's module files are loaded before any dependency file, and a dependency module's name `unit_N` uses that
number.
So adding a `mod x;` gives every dependency file a higher id, and every `unit_N` shifts.

That is more instability for dependency paths, which are not canonical until MOD-2 anyway.

#### Flattening

The entry crate's items stay at the top level of the flattened program, with each `mod x;` replaced by `mod x { ... }`.
Name resolution does not change the flattened program, which keeps the source order.
So `fn main` stays at the root, and enums of the root file survive flattening (issue #380).

Flattening a program without dependencies is idempotent: `flatten(flatten(p)) == flatten(p)`.

The flattened program compiles to the same CMR as the multi-file one.

### Scope

In scope:
`mod x;`, the file layout, `crate::`/`self::`/`super::`, the visibility rule, position-independent name resolution with
cyclic `use`, cycle, recursion and file diagnostics, recovery from broken and private imports, flattening, and keeping
`--dep` working.

Out of scope:
crates and `CrateId` (MOD-2), compatibility (MOD-3), enums outside the root file and nominal type identity (TYPE-2),
glob imports, qualified paths in expressions, `pub(crate)`.
