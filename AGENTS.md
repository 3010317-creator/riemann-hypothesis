# AGENTS.md

Read [README.md](README.md) first. It says what this repository is for, which changes are
welcome and how the proof is checked. Base your work on `main`; the `original` branch only
preserves the first published version of the proof. The rules below are the ones an agent is
most likely to break.

## Building

A full build takes hours, so fetch the cache before anything else:

```bash
lake exe cache get
lake build --no-build
```

The cached files were compiled elsewhere, so Lean does not re-check them. To check the proof
itself, follow [Checking the proof yourself](README.md#checking-the-proof-yourself).

## Do not

- change the Comparator challenge files: `src/Challenge.lean`, `comparator.json`,
  `export-targets.txt`, `comparator/FormalConjecturesChallenge.lean`,
  `comparator/formal-conjectures.json` and `comparator/formal-conjectures-export-targets.txt`.
  CI rejects any pull request that does.
- add axioms or `sorry`. `src/Main.lean` may use only `propext`, `Quot.sound` and
  `Classical.choice`.
- rewrite the proof along a substantially different path, or add files the proof does not need.
- report the results of your own builds or Comparator runs in a pull request.
