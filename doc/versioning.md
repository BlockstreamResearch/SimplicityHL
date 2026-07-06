# Compiler versioning

Every `.simf` file may begin with a compiler version directive:

```text
simc ">=0.6.0";
```

It is an optional fail-fast check: if the running compiler does not satisfy the
declared [SemVer](https://semver.org) range, compilation stops with a clear message
before lexing — even when the rest of the file is written for a newer language
version. Without a directive the file still compiles and `simc` prints a warning.
The directive must be the first non-comment item, at most once per file; `simc` is
a reserved keyword. In multi-file projects the entry file and every reachable
dependency are checked.

Range versions are plain `x.y.z` numbers: pre-release tags are not allowed in a
directive, and a pre-release compiler (e.g. `0.6.0-rc.2`) counts as its base
version.

## Reproducibility

A range does not pin the output: different compiler versions can satisfy it and
produce different Commitment Merkle Roots (CMRs), hence different addresses. Pin an
exact version (`=x.y.z`) for anything you deploy. Selecting, pinning, and fetching
compilers is the job of higher-level tooling, not `simc`.

## Details

See the rustdoc of `src/version.rs`: the checking flow, the frozen directive
syntax, pre-release handling, and the tooling entry point
(`SimcDirective::requirement_of`) are documented next to the code, so they cannot
drift.
