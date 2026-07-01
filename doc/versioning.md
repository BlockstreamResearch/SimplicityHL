# Compiler versioning

A `.simf` file may begin with a compiler version directive:

```text
simc ">=0.6.0";
```

It is a **fail-fast compatibility check**: if the running compiler does not satisfy the range, compilation stops with a clear message instead of a confusing parser error. The directive is **optional** — a file without one still compiles, and `simc` prints a warning suggesting you add it. When present it must be the first non-comment item, at most once per file.

A version *range* does not pin the output: several compiler versions can satisfy it and produce different Commitment Merkle Roots (CMRs), hence different addresses. See [Reproducibility](#reproducibility).

## Version ranges

Standard [SemVer](https://semver.org) operators apply:

- `^0.6.0` / `0.6.0` — compatible updates (`0.6.1` yes, `0.7.0` no)
- `~0.6` — patch updates only
- `=0.6.0` — that exact version
- `>=0.6.0` — inequalities
- `0.x.x` — wildcards
- `>=0.6.0, <1.0.0` — comma-separated bounds

A pre-release compiler (e.g. `0.6.0-rc.0`) matches only ranges that request that base version.

## Multi-file projects

The entry file and every reachable dependency are checked; if any is incompatible, compilation halts. A stable library cannot be silently built with an incompatible compiler.

## Reproducibility

A deployed contract's address is its CMR, so pin an **exact** version (`=x.y.z`) for anything you deploy and verify the CMR that `simc` prints — a range alone is not reproducible. Selecting, pinning, and fetching compilers is the job of higher-level tooling, not `simc`.

## Tooling

The declared range is machine-readable without compiling the program. See the rustdoc on `version::requirement_of`.

## Flattened output

A flattened multi-file project carries no `simc` directive; since directives are optional it still recompiles. Threading the merged range through flattening is future work.
