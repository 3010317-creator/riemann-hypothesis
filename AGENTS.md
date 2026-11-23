# AGENTS.md

[README.md](README.md)

The purpose of this repo is to create an artifact that is:

- **accessible**: we want to improve build performance and modularity to enable researchers to feasibly engage with the proof even without access to massive amounts of compute.
- **readable**: we want to improve code quality while preserving the "logic" of the proof, aspirationally to Mathlib levels. This includes lemma organization, formatting and idiomatic style, eliminating linter warnings, slop-free documentation, and more.
- **integrated with the community**: we would like to add bibliographic references to prior work where appropriate, and rely on existing formalization projects when possible.

Please note: we are **not** looking for:

- complete overhauls that follow a substantially different proof path
- claims about your own machine's builds / comparator run
- adding files which are not necessary for the Riemann Hypothesis proof

This work is taking place on the `main` branch.

## Cache

A full build takes hours, so you should use the cache:

```bash
lake exe cache get
lake build --no-build
```

A full build makes Lean check every proof on your machine. The cache downloads files that were
compiled elsewhere, so you can read and edit the project within minutes, but Lean does not
re-check them.

- [Theorem Statements](README.md#theorem-statements)
- [Checking the proof yourself](README.md#checking-the-proof-yourself)
