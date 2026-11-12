# SimplicityHL Roadmap

This table has a list of all the features we'd like. Each top-level item links to a markdown file
which has a detailed description of the feature and its sub-feature.

Before working on a nontrivial feature, please make sure that it has a document in this tree. It
is probably best to start with a [Simplicity Community](https://community.simplicity-lang.org/)
post to get feedback and do some design iteration.

## Taking Work

While working on a feature, try to keep the `Status` and `PRs` column in this table up to date:

* When a feature is first suggested, throw it in the table with status `Needs design`.
* Once it has a design document, change this to `Proposed`.
* Once it is in progress, change it to `In progress` and then `Completed`.

To take on a feature, first make sure that it has an entry in the table and appears in a
linked design document. Each design document should have an owner listed. (If there is no
owner, please volunteer or ask somebody to take this on.) **The owner's responsibility is
to respond to complaints when things are stalled or blocked.** The owner doesn't necessarily
need write or review code (unless this is blocking progress) or even maintain the design
document; they are just the central point-of-contact for the feature.

Once the feature has a document, go ahead and just open PRs against the repo as you normally
would. (If there are controversial high-level design considerations in your PR, you may need
to first PR to update the design document, but ideally this won't happen too much because
we don't want process friction when implementing stuff we've agreed to do.)

## Current Priorities

This section gives an idea of what we are working on. We should endeavor to update at least once
per quarter.

Our highest priorities right now (Q4 2026) are:

* the module system `MOD-1` and `MOD-2` (blocking nominal typing, which is blocking "working enums")
* Bitcoin support `CFG-2`
* Compiler diagnostics `DIAG` (needs splitting into sub-features with dependencies)
* The object file format `IR-3`

# All Features

Feel free to add any feature to this list, no matter how futuristic or low-priority. Its purpose
is to define the DAG of dependencies so that we can understand what is blocking the high-priority
items.

| ID     | Name                                  | Description                                                        | Dependencies  | Status       | PRs |
|--------|---------------------------------------|--------------------------------------------------------------------|---------------|--------------|-----|
| MOD    | [Module system](MOD.md)               | Rust-2018-style mod1les, external crates, content-based identity   | —             | -            | -   |
| MOD-1  | Internal modules                      | `mod x;` loads `x.simf`; `use` only brings names into scope        | —             | Proposed     | -   |
| MOD-2  | External crates                       | Dependency crates identified by Merkle-style `CrateId` hash        | MOD-1,  IR-2  | Needs design | -   |
| MOD-3  | External crates 2                     | Some notion of crate "compatibility", semver rules, etc            | MOD-2         | Needs design | -   |
| TYPE   | [Type system](TYPE.md)                | Stronger notions of type identity and inference                    | —             | -            | -   |
| TYPE-1 | Better type theory                    | `more-tt`-based type theory; type inference                        | -             | Needs design | —   |
| TYPE-2 | Nominal typing                        | Named types distinct from structurally equal types                 | MOD-2, TYPE-1 | Needs design | —   |
| TYPE-3 | Integer types                         | `u1`, `u2`, etc; integer promotion; signed integers                | TYPE-1        | Needs design | —   |
| TYPE-4 | Object hashes                         | Standard hashes of SimplictiyHL objects that cannot be collided    | TYPE-2        | Needs design | —   |
| IR     | [Intermediate representations](IR.md) | Compiler output, object format, etc                                | —             | -            | -   |
| IR-1   | Parameters and Witnesses              | Coherent design for parameters, witnesses, and constants           | MOD-1         | Needs design | -   |
| IR-2   | Canonical CMR                         | Simplicity expression that computes the CMR for other expressions  | IR-1          | Needs design | -   |
| IR-3   | "Object file" format                  | Format for "templated Simplicity", metadata, "compiled crates"     | IR-2          | Needs design | -   |
| DIAG   | [Compiler diganostics](DIAG.md)       | Better error messages, continuing after initial errors, etc        | -             | -            | -   |
| OPT    | [Optimizations](OPT.md)               | Compiler optimizations                                             | —             | -            | -   |
| OPT-1  | "Post-hoc optimizer"                  | Optimizer that takes an object file, improves code, outputs proofs | IR-3          | -            | -   |
| OPT-2  | Static analyzer                       | Static analysis of Simplicity code                                 | IR-3          | -            | -   |
| TX     | [Transaction Introspection](TX.md)    | Covenants, transaction introspection, multi-tx state management    | —             | -            | -   | 
| TX-1   | Covenant Convention                   | "Covenant convention" as code convention, then as HL built-in      | —             | Needs design | —   |
| TX-2   | Contract self-reference               | Ability to reference own code, maybe with parameters changed       | IR-2, TYPE-4  | Needs design | —   |
| SYN    | [Syntax / language features](SYN.md)  | Language syntax and features                                       | —             | -            | —   |
| SYN-1  | Infix operators (easy)                | `==`, `!=`, bitwise operators, inequalities, etc                   | —             | Needs design | —   |
| SYN-2  | Infix operators (integers)            | addition, subtraction, etc; needs integer promotion rules          | TYPE-3        | Needs design | —   |
| SYN-3  | `if` expressions                      | syntax sugar for matching on booleans                              | —             | Needs design | —   |
| SYN-4  | `return` expressions                  | syntax sugar for "early returns"                                   | —             | Needs design | —   |
| SYN-5  | Better loops                          | More conventional-looking, still statically bounded loops          | -             | Needs design | —   |
| SYN-6  | Unbounded loops                       | Recursion, unbounded loops, general `disconnect` support?          | -             | Needs design | —   |
| SYN-7  | Universal sighash                     | Better sighashing, language support for "universal sighash"        | -             | Needs design | —   |
| CFG    | [Conditional compilation](CFG.md)     | Compilation based on target blockchain etc                         | —             | -            | —   |
| CFG-1  | Compilation for separate targets      | Compilation where the end user choses their blockchain target      | —             | Done(?)      | —   |
| CFG-2  | Bitcoin support                       | Adding a "Bitcoin" blockchain target                               | CFG-1         | Needs design | —   |
| CFG-3  | `cfg` flags                           | Code which is condintionally compiled per target                   | CFG-1         | Needs design | —   |
| TEST   | [Unit testing](TEST.md)               | In-language testing support                                        | —             | -            | —   |
