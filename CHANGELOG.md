# 0.6.0-rc.0 - 2026-04-24

* Add imports and dependency resolution, including `pub`/`use` syntax, re-exports, aliases, transitive dependencies, collision diagnostics, functional tests, examples, and `simc --dep` for compiling multi-file programs. [#264](https://github.com/BlockstreamResearch/SimplicityHL/pull/264)
* Replaced the deprecated `WithFile` trait with `WithContent` and `WithSource` to cleanly separate single-file execution from multi-file environments. Additionally, replaced the `file()` method on `RichError` with `source()`. [#266](https://github.com/BlockstreamResearch/SimplicityHL/pull/266)
* Clean up whitespace in the generated jet documentation. [#276](https://github.com/BlockstreamResearch/SimplicityHL/pull/276)

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
