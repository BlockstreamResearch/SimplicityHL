# Architecture Notes

## The effect of imports and flattening on the CMR

Imports and the flattening phase have **no impact** on the CMR. The underlying order of calculation is strictly determined by the `main` function.

For example, consider the following code:

```rust
fn a() -> u32 { 5 }
fn b() -> u32 { 6 }

fn main() {
    let a: u32 = a();
    let b: u32 = b();
    let (_, c): (bool, u32) = jet::add_32(a, b);
    assert!(jet::eq_32(c, 11));
}
```

It does not matter whether `fn a()` or `fn b()` is declared first; the driver can reorder these declarations as it sees fit without affecting the CMR.

The flattening phase behaves in the exact same way. While it wraps the file's contents into a `mod unit_N { ... }` block, it does not alter the execution order inside `main`. The CMR will change if and only if we explicitly modify the execution order (e.g., swapping the evaluation of `let a` and `let b`) within the `main` function itself.

Below are three scenarios where resolution errors corrupt the CMR:

1. Incorrect Aliasing or Function Substitution
If the resolution phase maps an alias to the wrong function, the compiler silently substitutes one implementation for another. Since the program logic has changed, the resulting CMR will be entirely different.

2. Entry Point Fallback (main hijacking)
The CMR is rooted at the main function of the entry file. If the compiler does not enforce this, it may traverse the dependency graph and pick up a main from a dependency instead. This completely changes the execution graph.

3. Resolution Cache Poisoning (use path collisions)
When different package roots share structurally identical import paths (e.g., both a binary and a library declare `use crate::A::foo`), an improperly isolated resolution cache may link one context's import to the other's physical file. (See `functional_tests::identical_crate_uses_in_different_package_roots_do_not_poison_resolution_cache`.)

*Note: The scenarios listed above reflect bugs discovered during current testing. The list is ***not exhaustive*** and may be expanded as further testing uncovers additional edge cases.*

## Crate and Module Paths

The `crate` keyword is used to construct absolute paths where the path root is the current package's root directory. This provides an explicit and readable way to distinguish local imports from external library imports.

```rust
// Import the `add` function from the local `math.simf` file
use crate::math::add;
```

The compiler driver (`simc`) automatically maps the `crate` keyword to the directory containing the entry-point file. For external libraries linked via `--dep`, the driver also maps `crate` to the library's root, ensuring that `use crate::...` statements inside the library resolve correctly within that library's scope.

### Strict Local Imports

To enforce clear project boundaries, the compiler requires that any file belonging to the local workspace *must* be imported using a `crate::` prefixed path. Attempting to create an external dependency alias that points to a local file will result in a `LocalFileImportedAsExternal` error.

### Omitted Keywords

The `super` keyword for relative parent-module imports has not yet been implemented. All local imports should use absolute paths starting from the `crate` root.

## Namespace Separation in SimplicityHL

SimplicityHL uses distinct namespaces for types and values. This allows the same identifier to refer to different things depending on where it appears in the code — the compiler determines the correct interpretation from syntactic context, with no risk of collision.

``` Rust
fn foo() -> bool { false }
type foo = bool;

fn main() {
    let x: foo = false; // type namespace  - type alias
    assert!(foo());     // value namespace - function
}
```

## The "main" identifier in aliases

In SimplicityHL, the string "main" is reserved exclusively for the program's entry point function.
While a `TypeAlias` is technically allowed to use this name, we explicitly forbid aliasing imports
to "main" using the `as` keyword. This avoids complicating the compiler's resolution logic and
prevents accidental shadowing of the entry point.

## Dependency Managing

Currently, the module system requires explicit dependency remapping for each library context.
In the following example, we load the `math` library using two different Dependency Root Path (DRP) names.  
To achieve this, we must configure the remappings for the root `multiple_deps/` directory to map `base_math` and merkle to their respective paths. Additionally, for the `multiple_deps/merkle` subdirectory, we must define its own specific mapping to the `math` library.

Example:

``` Rust
// multiple_deps/math/simple_op.simf
pub fn hash(x: u32, y: u32) -> u32 {
    jet::xor_32(x, y)
}

// multiple_deps/merkle/build_root.simf
use math::simple_op::hash as temp_hash;

pub fn get_root(tx1: u32, tx2: u32) -> u32 {
    temp_hash(tx1, tx2)
}

pub fn hash(tx1: u32, tx2: u32) -> u32 {
    jet::and_32(tx1, tx2)
}

// multiple_deps/main.simf
use merkle::build_root::{get_root, hash as and_hash};
use base_math::simple_op::hash as or_hash;

pub fn get_block_value_hash(prev_hash: u32, tx1: u32, tx2: u32) -> u32 {
    let root: u32 = get_root(tx1, tx2);
    or_hash(prev_hash, root)
}

fn main() {
    let block_val_hash: u32 = get_block_value_hash(5, 10, 20);
    assert!(jet::eq_32(block_val_hash, 27));
    
    let first_value: u32 = 15;
    let second_value: u32 = 22;
    assert!(jet::eq_32(and_hash(first_value, second_value), 6));
}
```

> NOTE: For more details, see the `multiple_deps` test inside the `src/lib.rs` file.
