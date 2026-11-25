# Compiler diagnostics

Better error messages, continuing after initial errors, etc.

| ID     | Name                            | Owner       | Status       |
|--------|---------------------------------|-------------|--------------|
| DIAG-1 | Structured error types          | @LesterEvSe | Proposed     |

## Done

Tracked in #362.

| Change                                                         | PR   |
|----------------------------------------------------------------|------|
| The parser recovers and reports several syntax errors per file | #185 |
| Every span carries its `file_id`                               | #363 |
| Errors are collected as values instead of `String`s            | #369 |
| `Diagnostic`, rendering with `ariadne`                         | #370 |
| The `!` type                                                   | #417 |
| Analysis reports through `DiagnosticManager`                   | #418 |
| Every error inside an expression is reported                   | #420 |
| Analysis continues after a broken function body                | #424 |
| Analysis continues after an undefined type                     | #430 |
| Analysis continues after a failed statement                    | #448 |

On master, analysis still stops in two cases:

- A failed item other than `main`, such as a broken `use` or a redefined alias, stops the analysis of the remaining items.
- A syntax error in any file stops the compilation before analysis.

## DIAG-1: Structured error types

One error type per phase.
No `String` errors in the public API.

### Design

#### Error types

Each phase gets its own error enum, built with `thiserror` and defined next to the code that creates it:

| Enum              | Covers                                                  |
|-------------------|---------------------------------------------------------|
| `VersionError`    | the `simc` version directive                            |
| `ResolutionError` | dependencies, file loading and the order of modules     |
| `LexError`        | characters the lexer can't turn into tokens             |
| `ParseError`      | syntax, and checks such as unstable features            |
| `ScopeError`      | names: items, modules, imports and their visibility     |
| `AnalysisError`   | types, calls, patterns and `main`                       |
| `ValueError`      | literal values that don't fit their type                |
| `WitnessError`    | witness and argument values, and satisfying the program |

`ValueError` is shared: analysis checks literals with it, and witness and argument files are parsed by the same code,
so `AnalysisError` and `WitnessError` both wrap it.

`error::Error` keeps one variant per phase, so `Diagnostic` and `DiagnosticManager` stay as they are.

```rust
#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    Parse(#[from] ParseError),
    #[error(transparent)]
    Scope(#[from] ScopeError),
    // ...
}
```

A few errors stay `String`, because no caller needs to tell them apart:

- `Internal { msg }` for broken invariants and compile failures.
- The debug tracker in `src/tracker.rs`, the `--target` parsing in `src/main.rs`, and the error coverage check in
  `src/error_cases.rs`.

The new types follow apoelstra's guidelines from #324:

- No `String` errors, unless the wrapped error is already a `String`.
- No messages like `cannot parse: {0}`.
  The wrapped error is available through `source()`, and the renderer prints the `source()` chain.
- Named fields like `FileNotFound { path: PathBuf }`, instead of `FileNotFound(String)`.
- No `From` impl that only wraps another error if the call site could add more context.

#### Testing

Tests match on error variants instead of rendered messages.
`analysis_errors` in `src/test_utils.rs` returns the errors themselves instead of their `to_string()` output:

```rust
#[test]
fn tuple_elements() {
    let errors = analysis_errors("fn main() { let pair: (u32, u32) = (x, y); }");
    assert!(matches!(
        errors.as_slice(),
        [
            Error::Analysis(AnalysisError::UndefinedVariable { .. }),
            Error::Analysis(AnalysisError::UndefinedVariable { .. }),
        ]
    ));

    // Today:
    // assert_errors(src, &["Variable `x` is not defined", "Variable `y` is not defined"]);
}
```
