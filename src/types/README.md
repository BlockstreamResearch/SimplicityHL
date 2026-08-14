# Types in SimplicityHL

There are three type structures in SimplicityHL:

* `StructuralType` is essentially a copy of `simplicity::types::Final`; there are three structural
  types: unit, sum and product, and these correspond to the types in the compiled Simplicity code.

* `ResolvedType` is a SimplicityHL type; this extends `StructuralType` by adding lists, tuples,
  enums, and some other stuff.

  Each `ResolvedType` can be "lowered" via `From` to a `StructuralType`. In general, an expression
  of the form A -> B, where A and B are `ResolvedType`s, will compile to a Simplicity expression
  whose source and target types are the lowerings of A and B, respectively. In the compiler we
  explicitly call `unify` on the Simplicity type inference engine to enforce this.

* `AliasedType` is a copy of `ResolvedType` where everything is a (re)name. Essentially they are
  "AST types". They feature primarily in parse.rs and ast.rs. Before these can be used, we call
  `aliased_type.resolve()` to get a `ResolvedType`.

SimplicityHL does *not* currently support any form of nominal typing. All structurally equal types
are considered interchangeable.

