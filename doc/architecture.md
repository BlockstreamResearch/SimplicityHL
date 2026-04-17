# Architecture Note: Omitted Keywords
The `crate` and `super` keywords were not added to the compiler because they
are unnecessary at this stage. Typically, they are used to resolve relative
paths during import parsing. However, in our architecture, the prefix before
the first `::` in a `use` statement is always an dependency root path. Since all
dependency root paths are unique and strictly bound to specific paths, the resolver
can always unambiguously resolve the path without needing relative pointers.

# Architecture Note: Namespace Separation in SimplicityHL

SimplicityHL uses distinct namespaces for types and values. This allows the same identifier to refer to different things depending on where it appears in the code — the compiler determines the correct interpretation from syntactic context, with no risk of collision.

``` Rust
fn foo() -> bool { false }
type foo = bool;

fn main() {
    let x: foo = false; // type namespace  - type alias
    assert!(foo());     // value namespace - function
}
```
