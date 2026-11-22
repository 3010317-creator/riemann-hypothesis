# riemann-hypothesis

[![checks](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/leanprover-community/riemann-hypothesis/actions/workflows/checks.yml)

A [Comparator](https://github.com/leanprover/comparator) setup and community build cache for the Lean formalization that
claims a proof of the Riemann Hypothesis, and of GRH for Dirichlet L-functions, announced on
2026-11-20 at <https://alpo.ge/remark.pdf>.

The first commit, `40e56bab`, is the Lean source exactly as it was published. It has been
changed since. Pull requests have deleted files the proof doesn't use, shortened proofs, and
ported it from Lean 4.33.1, which it was written for, to newer releases. The five theorem
statements are still word for word the published ones, and
`git diff --stat 40e56bab HEAD -- src` lists everything else. If you want the untouched
original, check out `40e56bab` or use
[riemann-hypothesis-original](https://github.com/homeowmorphism/riemann-hypothesis-original).

## What is claimed

`src/Main.lean` proves five theorems:

| Theorem | Statement |
|---|---|
| `riemannHypothesis` | Mathlib's `RiemannHypothesis` |
| `riemannZeta_eq_zero_re` | the same, written out |
| `LFunction_ne_zero_of_half_lt_re` | L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every Dirichlet character, except the trivial character at s = 1 |
| `LFunction_eq_zero_re` | every zero of L(χ, s) with 0 < Re s < 1 has Re s = 1/2 |
| `LFunction_eq_zero_re_of_isPrimitive` | the same, for primitive characters |

[`src/Challenge.lean`](src/Challenge.lean) states the same five with `sorry` in place of the
proofs, in a file that imports only Mathlib. Comparator checks that `Main.lean` proves exactly
those statements, that it uses no axioms other than `propext`, `Quot.sound` and
`Classical.choice`, and that Lean's kernel and nanoda both accept the proof.

## Getting a build

Compiling the project takes hours on a large machine, so there is a cache of compiled files:

```bash
lake exe cache get
lake build --no-build
```

The first command needs Python 3.11 or newer. It downloads Mathlib's cache and then ours. Ours
has to match your checkout exactly. It looks for a successful CI build of the same source
(commits that only change documentation share one) and, failing that, for the baseline build
pinned in [`scripts/cache-baselines.json`](scripts/cache-baselines.json). If nothing matches,
it says so and you are left with `lake build`. The second command confirms that there is
nothing left to compile.

Don't treat the cache as a check of the proof. It contains files built from unreviewed pull
requests on volunteers' machines, and all the download verifies is that you received what was
uploaded. If you need to trust the result, build it yourself as described below.
[CACHE.md](verification/CACHE.md) explains how the cache is made.

## Checking the proof

```bash
export LEAN_ABORT_ON_PANIC=1        # stop on an internal error, as Comparator does
export LAKE_ARTIFACT_CACHE=false    # really rebuild, even if cache-env.sh was sourced earlier
export MATHLIB_CACHE_GET_URL=https://cache.mathlib.org/mathlib4

# 1. Export the challenge, in a clean clone at $CLEAN.
cd "$CLEAN"
lake exe mathlib/cache get
lake build Challenge
lake env leanexport Challenge -- $(cat export-targets.txt) > challenge.export

# 2. Build the solution, in a second clone, inside a sandbox with no network. Takes hours.
lake exe mathlib/cache get      # before entering the sandbox
lake build Main                 # inside the sandbox

# 3. Export the solution, still inside the sandbox.
lake env leanexport Main -- $(cat "$CLEAN/export-targets.txt") > solution.export

# 4. Judge, from an empty directory, with the same Lean release.
lake comparator --config "$CLEAN/comparator.json" \
  --challenge-from-export "$CLEAN/challenge.export" --solution-from-export solution.export
```

Compiling the submission runs its code. That is why the challenge is exported first, in a clone
where none of the submission has been compiled, and why the build and the second export happen
in a sandbox that only `solution.export` leaves.

Steps 1 and 2 use `lake exe mathlib/cache get` on purpose. Plain `lake exe cache get` would also
download our prebuilt copy of the submission, and `lake build Main` would then compile nothing.

All four steps use the Lean release in `lean-toolchain`, which comes with both `leanexport` and
`lake comparator`. The published source was written for Lean 4.33.1, which has neither, so
checking `40e56bab` itself takes two toolchains.
[An older version of this README](https://github.com/leanprover-community/riemann-hypothesis/blob/7cce738ba719a32964ca3822d0994f4c6952c7ae/README.md#checking-it)
has those steps.

We worked these steps out on the published source and don't have a complete run on the current
source yet. On the published source the build took hours on a large machine and about 100 GB of
disk, and judging needs a lot of memory. [NOTES.md](verification/NOTES.md) says where the source
came from, how the tools and sandboxes are set up and what a passing run does and doesn't show,
but it still describes the Lean 4.33.1 setup.

## CI

Every push and pull request gets a quick check that `Challenge.lean` compiles against Mathlib
alone. A full build is too big for GitHub's runners, so pull requests are built on machines
lent by volunteers, and successful builds go into the cache. If you have a Linux machine with
plenty of memory and disk to spare, [CI-RUNNERS.md](verification/CI-RUNNERS.md) explains how to
lend it. The scripts behind all this are in [`scripts/`](scripts/) and
[`tools/ci_native/`](tools/ci_native/README.md).

## License

The submission belongs to its author and was published without a license. It is mirrored here
so that it can be checked. Commit `40e56bab` is the unmodified copy.
