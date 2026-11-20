# Compiler diagnostics

Better error messages, continuing after initial errors, etc.

| ID     | Name                            | Owner       | Status       |
|--------|---------------------------------|-------------|--------------|
| DIAG-1 | Structured error types          | @LesterEvSe | Needs design |

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
