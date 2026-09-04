# Unreleased

## Changed

* Deduplicate identical compiler diagnostics and present multi-file diagnostics in deterministic dependency and source order. [#413](https://github.com/BlockstreamResearch/SimplicityHL/pull/413)

# 0.7.2 - 2026-08-25

## Added

* Add `simc --project-root <path>` to anchor `crate::` imports and unscoped `--dep` aliases at an explicit project root while allowing the entry file to live in a nested directory. [#392](https://github.com/BlockstreamResearch/SimplicityHL/pull/392)
  * The entry file must be contained within the selected root. Omitting the option preserves the existing entry-directory behavior. 
* Add a security policy with instructions for privately reporting vulnerabilities. [#393](https://github.com/BlockstreamResearch/SimplicityHL/pull/393)

## Changed

* Relicense SimplicityHL from CC0-1.0 to the user's choice of MIT or Apache-2.0. [#389](https://github.com/BlockstreamResearch/SimplicityHL/pull/389)

# 0.7.1 - 2026-08-06

## Added

* Add the `fmt` cargo feature: a lossless lexer producing `FmtTokens` with comments, newlines, and whitespace (via `FmtToken` and `TriviaKind`, both `#[non_exhaustive]`) for formatter tooling. Preserves underscored digit spellings for round-tripping, attaches spans to more AST nodes. Regular lexing/parsing is unchanged and discards trivia. [#372](https://github.com/BlockstreamResearch/SimplicityHL/pull/372)

## Changed

* Lex whitespace in contiguous chunks rather than character-by-character. [#372](https://github.com/BlockstreamResearch/SimplicityHL/pull/372)

# 0.7.0 - 2026-07-27

## Breaking Changes

* Reserve the `simc` keyword for the compiler version directive: identifiers named `simc` no longer lex. [#263](https://github.com/BlockstreamResearch/SimplicityHL/pull/263)
* Rework the diagnostics API: `RichError` -> `Diagnostic`, `ErrorCollector` -> `DiagnosticManager` (now owns `SourceMap`), `WithContent`/`WithSource` removed, `file_id` moved into `Span`, `TemplateProgram::source_map()` now returns `Option<&SourceMap>`, `SourceMap` accessor methods renamed, and `lexer::lex` gained `file_id` and `start` parameters. [#263](https://github.com/BlockstreamResearch/SimplicityHL/pull/263), [#363](https://github.com/BlockstreamResearch/SimplicityHL/pull/363), [#368](https://github.com/BlockstreamResearch/SimplicityHL/pull/368), [#369](https://github.com/BlockstreamResearch/SimplicityHL/pull/369), [#370](https://github.com/BlockstreamResearch/SimplicityHL/pull/370)
* Nominative enum types with `EnumName::Variant` and match arms, gated behind `simc -Z enums` (or `UnstableFeature::Enums`). Not allowed across module dependencies. [#376](https://github.com/BlockstreamResearch/SimplicityHL/pull/376)
* Multi-error reporting with deterministic ordering in `Arguments::is_consistent` and `WitnessValues::is_consistent`. [#378](https://github.com/BlockstreamResearch/SimplicityHL/pull/378), [#381](https://github.com/BlockstreamResearch/SimplicityHL/pull/381)

## Added

* Add the optional `simc "<range>";` compiler version directive: a fail-fast SemVer compatibility check run on the raw source before lexing, covering the entry file and every reachable dependency. A missing directive produces a CLI warning; tooling can read the declared range without compiling via `version::SimcDirective::requirement_of`. See `doc/versioning.md`. [#263](https://github.com/BlockstreamResearch/SimplicityHL/pull/263)
* Add `compiler_version` to `simc` output (JSON field and text printout) and `compiler_version()` accessors on `TemplateProgram` and `CompiledProgram`, identifying the exact compiler that produced a program. [#263](https://github.com/BlockstreamResearch/SimplicityHL/pull/263)
* Expose `array::btree_split_index` as a public helper for splitting a sequence at its natural balanced-binary-tree boundary. [#376](https://github.com/BlockstreamResearch/SimplicityHL/pull/376)

## Changed

* Render errors via `ariadne`: source-annotated diagnostics with colored output when the terminal supports it. `SourceMap` owns file contents; internal `Result<_, String>` replaced by `DiagnosticManager`. [#363](https://github.com/BlockstreamResearch/SimplicityHL/pull/363), [#368](https://github.com/BlockstreamResearch/SimplicityHL/pull/368), [#369](https://github.com/BlockstreamResearch/SimplicityHL/pull/369), [#370](https://github.com/BlockstreamResearch/SimplicityHL/pull/370)
* `simc` writes diagnostics to `stderr`, with color enabled when the target is a TTY. [#378](https://github.com/BlockstreamResearch/SimplicityHL/pull/378)
* Resolve witness and argument values against the program's declared types, so `.wit`/`.args` files no longer need type annotations. Adds `simplicityhl::UnresolvedValues` (re-exported under the `serde` feature) and `CompiledProgram::witness_types()`. [#371](https://github.com/BlockstreamResearch/SimplicityHL/pull/371)

## Fixed

* Prevent malformed input from panicking during parser recovery when constructing an empty span. [#376](https://github.com/BlockstreamResearch/SimplicityHL/pull/376)

# 0.6.0 - 2026-06-26

## Breaking Changes

* Remove `ModuleProgram` and the parsing of arguments and witnesses from the core compiler. [#323](https://github.com/BlockstreamResearch/SimplicityHL/pull/323)
* Replace the deprecated `WithFile` trait with `WithContent` and `WithSource` to cleanly separate single-file execution from multi-file environments. Replace `RichError::file()` with `source()`. [#266](https://github.com/BlockstreamResearch/SimplicityHL/pull/266)
* Rename the lock-distance/duration jets: `jet::check_lock_distance`, `jet::check_lock_duration`, `jet::tx_lock_distance`, and `jet::tx_lock_duration` are now `jet::broken_do_not_use_check_lock_distance`, `jet::broken_do_not_use_check_lock_duration`, `jet::broken_do_not_use_tx_lock_distance`, and `jet::broken_do_not_use_tx_lock_duration`. Existing `.simf` programs using these jets must be updated. [#314](https://github.com/BlockstreamResearch/SimplicityHL/pull/314)
* Public API changes around `CanonSourceFile`, `DependencyMapBuilder`, `UnstableFeatures`, `JetHinter`, and several constructor signatures. [#315](https://github.com/BlockstreamResearch/SimplicityHL/pull/315), [#330](https://github.com/BlockstreamResearch/SimplicityHL/pull/330), [#356](https://github.com/BlockstreamResearch/SimplicityHL/pull/356), [#361](https://github.com/BlockstreamResearch/SimplicityHL/pull/361)

## Added

* Add unstable-features gating via `simc -Z <feature>`, backed by an `UnstableFeature` enum and a `RequireFeature` trait implemented exhaustively on every AST node, with parse-time checks and docs in `doc/unstable-features.md`. [#354](https://github.com/BlockstreamResearch/SimplicityHL/pull/354)
* Add imports, modules, and dependency resolution: `pub`/`use` syntax, `mod` blocks with nesting, re-exports, aliases, transitive dependencies, collision diagnostics, and `simc --dep` for compiling multi-file programs. The driver flattens multi-file programs by wrapping each file in `mod unit_N { ... }` (no effect on CMR). Currently gated behind `simc -Z imports`. [#264](https://github.com/BlockstreamResearch/SimplicityHL/pull/264), [#337](https://github.com/BlockstreamResearch/SimplicityHL/pull/337)
* Add `crate::` paths for local dependencies and tighten dependency validation. [#303](https://github.com/BlockstreamResearch/SimplicityHL/pull/303), [#312](https://github.com/BlockstreamResearch/SimplicityHL/pull/312)
* Add jet extensibility: introduce `JetHL` and `CoreJetHinter`, expose an external-jets feature/API with an example, and bump `simplicity-lang` to 0.8.0. [#322](https://github.com/BlockstreamResearch/SimplicityHL/pull/322), [#334](https://github.com/BlockstreamResearch/SimplicityHL/pull/334), [#340](https://github.com/BlockstreamResearch/SimplicityHL/pull/340), [#344](https://github.com/BlockstreamResearch/SimplicityHL/pull/344), [#357](https://github.com/BlockstreamResearch/SimplicityHL/pull/357)

## Changed

* Move the VS Code extension and LSP to a separate repository. [#326](https://github.com/BlockstreamResearch/SimplicityHL/pull/326)
* Clean up whitespace in the generated jet documentation. [#276](https://github.com/BlockstreamResearch/SimplicityHL/pull/276)
* Reshape public error and diagnostic types. [#325](https://github.com/BlockstreamResearch/SimplicityHL/pull/325), [#328](https://github.com/BlockstreamResearch/SimplicityHL/pull/328)

## Deprecated

* Deprecate `DefaultTracker::new`. [#355](https://github.com/BlockstreamResearch/SimplicityHL/pull/355)

# 0.5.0 - 2026-04-17

* Migrate from the `pest` parser to a new `chumsky`-based parser, improving parser recovery and enabling multiple parse errors to be reported in one pass [#185](https://github.com/BlockstreamResearch/SimplicityHL/pull/185)
* `simc` now accepts `--args <file>` for parameterized contracts, witness input is supplied explicitly via `--wit <file>`, and JSON output now includes the program Commitment Merkle Root (CMR) [#200](https://github.com/BlockstreamResearch/SimplicityHL/pull/200), [#231](https://github.com/BlockstreamResearch/SimplicityHL/pull/231)
* Expose contract ABI metadata for tooling via `simc --abi`, and add library accessors for parameter and witness types [#201](https://github.com/BlockstreamResearch/SimplicityHL/pull/201), [#219](https://github.com/BlockstreamResearch/SimplicityHL/pull/219)
* Improve pattern matching in `match` statements, including more complex destructuring forms [#242](https://github.com/BlockstreamResearch/SimplicityHL/pull/242)
* Improve parser and type diagnostics by rejecting duplicate type-alias definitions and built-in alias redefinitions, and by fixing lexer/parser handling around `::` and angle-bracket-delimited syntax [#221](https://github.com/BlockstreamResearch/SimplicityHL/pull/221), [#222](https://github.com/BlockstreamResearch/SimplicityHL/pull/222), [#243](https://github.com/BlockstreamResearch/SimplicityHL/pull/243), [#247](https://github.com/BlockstreamResearch/SimplicityHL/pull/247)
* Improve compiler diagnostics rendering for UTF-16 text in both single-line and multiline spans [#255](https://github.com/BlockstreamResearch/SimplicityHL/pull/255), [#257](https://github.com/BlockstreamResearch/SimplicityHL/pull/257)
* Move jet documentation into the compiler, add the `simplicityhl-codegen` binary behind the `docs` feature, and correct docs for `build_tapleaf_simplicity`, `unwrap_left`, and `unwrap_right` [#229](https://github.com/BlockstreamResearch/SimplicityHL/pull/229), [#230](https://github.com/BlockstreamResearch/SimplicityHL/pull/230), [#251](https://github.com/BlockstreamResearch/SimplicityHL/pull/251)
* Update the LSP to use the new `chumsky` parser [#223](https://github.com/BlockstreamResearch/SimplicityHL/pull/223)
* Correct `FullMultiply` signatures and tracker argument decoding [#274](https://github.com/BlockstreamResearch/SimplicityHL/pull/274)

# 0.4.1 - 2026-01-22

* VSCode and LSP developer experience improvements -- [#199](https://github.com/BlockstreamResearch/SimplicityHL/pull/199), [#214](https://github.com/BlockstreamResearch/SimplicityHL/pull/214)
* Adjust jet trace debug-wrapper removal heuristic [#198](https://github.com/BlockstreamResearch/SimplicityHL/pull/198) — not an ideal solution, but adopted as a temporary approach per the discussion in [#197](https://github.com/BlockstreamResearch/SimplicityHL/issues/197).
* `analyze_named_module`: make missing modules equivalent to empty ones [#187](https://github.com/BlockstreamResearch/SimplicityHL/pull/187)

# 0.4.0 - 2025-12-18

* Add `DefaultTracker` [#184](https://github.com/BlockstreamResearch/SimplicityHL/pull/184)
* feature(simc): flag for json output [#180](https://github.com/BlockstreamResearch/SimplicityHL/pull/180)

# 0.3.0 - 2025-11-04

* Add `array_fold` builtin function [#145](https://github.com/BlockstreamResearch/SimplicityHL/pull/145)
* Add getters for `Span` and improve error handling [#146](https://github.com/BlockstreamResearch/SimplicityHL/pull/146)
* Add VSCode extension with LSP support
  [#148](https://github.com/BlockstreamResearch/SimplicityHL/pull/148)
  [#149](https://github.com/BlockstreamResearch/SimplicityHL/pull/149)
* Switch NUMS key to BIP-0341 suggested key [#143](https://github.com/BlockstreamResearch/SimplicityHL/pull/143)
* Fix `array_fold` powers-of-two bug; fix simc CLI when serde is disabled; enable serde by default [#159](https://github.com/BlockstreamResearch/SimplicityHL/pull/159)
* Update rust-simplicity to 0.6
  [#143](https://github.com/BlockstreamResearch/SimplicityHL/pull/143)
  [#160](https://github.com/BlockstreamResearch/SimplicityHL/pull/160)

# 0.2.0 - 2025-07-29

* Renamed from [Simfony](https://crates.io/crates/simfony)
* Initial release. Not recommended for production use.
