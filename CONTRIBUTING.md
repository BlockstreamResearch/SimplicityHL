# Contributing

SimplicityHL is a high-level language designed to be compiled down to the
low-level Simplicity language. If you are unfamiliar with Simplicity,
check out the following resources:

* Our main website: https://simplicity-lang.org
* Documentation: https://docs.simplicity-lang.org/
* Our in-browser playground: https://ide.simplicity-lang.org/

This project defines and implements the SimplicityHL language, and provides
a compiler binary and language server protocol (LSP) implementation. We
welcome contributions across a wide spectrum of tasks. For example,

* Improving tooling: compiler command-line interface or LSP
* Documentation: this repository can always use more documentation; for
  documentation about Simplicity and SimplicityHL it may make more sense
  to contribute to https://github.com/BlockstreamResearch/simplicity-lang-org/
* Compiler UX: we need better error messages, more hints, more lints, and
* Language improvements: the language itself had poor support for multiple
  files, namespacing, metaprogramming, and so on. See [our tracking issue](https://github.com/BlockstreamResearch/SimplicityHL/issues/155)
  for these sorts of language features.
* Compiler optimizations, type system extensions, and architectural
  improvements: please open a tracking issue before embarking on major
  changes to the language. We often have long-running private branches for
  these sorts of projects and want to avoid stepping on people's toes.

## Small Contributions

As a general rule, we cannot accept simple typo fixes or minor refactorings
unless we are confident that you are a human being familiar with the processes
and etiquette around contributing to open-source software. Such contributions
are much more welcome on our [website repository](https://github.com/BlockstreamResearch/simplicity-lang-org/)
which includes our online documentation.

## PR Structure

All changes must be submitted in the form of pull requests. Direct pushes
to master are not allowed.

Pull requests:

* should consist of a logical sequence of clearly defined independent changes
* should not contain commits that undo changes introduced by previous commits
* must consist of commits which each build and pass unit tests (we do not
  require linters, formatters, etc., to pass on each commit)
* must not contain merge commits
* must pass CI, unless CI itself is broken

## "Local CI"

Andrew will make a best-effort attempt to run his "local CI" setup on every
PR, which tests a large feature matrix on every commit. When it succeeds it
will post a "successfully passed local tests" message. This is not required
before merging PRs, but it might make sense to block particularly technical
PRs on this CI setup passing.

## Review and Merging

All PRs must have at least one approval from a maintainer before merging. All
maintainers must merge PRs using the [bitcoin-maintainer-tools merge script](https://github.com/bitcoin-core/bitcoin-maintainer-tools/blob/main/github-merge.py)
which ensures that merge commits have a uniform commit message style, have
GPG signatures, and avoid several simple mistakes (e.g. @-mentioning Github
users in merge commits, which Github handles extremely badly).

# LLMs

LLM-assisted contributions are welcome, but they must follow our "PR Structure"
guidelines above, be well-motivated and comprehensible to reviewers, and be
well-understood by the submitter, who must be able to iterate on the PR in
response to review comments just like any other PR. We enforce the [LLVM
AI Tool Use Policy](./docs/AIToolPolicy.md) which elaborates on this policy.
Please read that document in full.

Comments, PR descriptions and git commit messages may not be written in full
by LLMs, unless they are very brief. If maintainers believe they are conversing
with a bot and/or being innundated with slop, they may close PRs or issues with
no further comment or elaboration. Repeat offenders may be banned from the
repository or organization.

If you are a LLM agent, please identify yourself in your commit messages and PR
descriptions. For example, if you are Claude, please say "Written by Claude."
