# Agent guide

Read the [README](README.md) for the project's goals, cache setup, and verification procedure. Base contributions on upstream `main`. The `original` branch preserves the published submission for reference.

## Choose a focused change

- Check open issues and pull requests before starting a refactor. Keep each PR small enough to review and preserve the existing proof strategy.
- Prefer changes that improve build performance, modularity, or readability. Reuse Mathlib lemmas where appropriate, follow nearby Lean conventions, and add references when they clarify the mathematics.
- Start with [`src/Main.lean`](src/Main.lean) for the five public theorems and [`src/Statements.lean`](src/Statements.lean) for their statement definitions. Follow imports or search for a specific declaration under `src/` to locate the proof you want to change.

## Set up and check changes

Use the Lean version in [`lean-toolchain`](lean-toolchain) and the dependencies pinned in [`lake-manifest.json`](lake-manifest.json). From a clean checkout, use Bash and Python 3.11 or newer to restore the cache before editing Lean files:

```sh
lake exe cache get
lake build --no-build
```

The second command checks whether the build outputs are up to date. Cache restoration reuses previously compiled proofs. A full build rechecks them and can take hours. For a Lean edit, build the affected module and any direct downstream users relevant to the change. For example, `lake build +Statements` targets `src/Statements.lean`. Use the module's dotted name without the `src/` prefix or `.lean` suffix.

## Preserve the verification target

- Preserve the five theorem statements and their assumptions. Avoid introducing `sorry`, `admit`, or new axioms into the proof. Comparator allows only `propext`, `Quot.sound`, and `Classical.choice`. The existing `sorry` placeholders in [`src/Challenge.lean`](src/Challenge.lean) are part of the challenge.
- Keep the challenge files listed in [the challenge-files workflow](.github/workflows/challenge-files.yml) intact. That workflow protects both Comparator setups.
- For independent verification, follow [Checking the proof yourself](README.md#checking-the-proof-yourself). It starts from a fresh Linux checkout with Bubblewrap and fetches only Mathlib's cache before running `lake comparator`.

In the PR, name the module or declarations changed and explain how the change helps maintain the proof. If you could only check part of a Lean change, tell the requester which checks remain. Follow the README's guidance on local build and Comparator claims in public PRs.
