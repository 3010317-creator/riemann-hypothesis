# Formatting `src/` with the Lean auto-formatter

The **Format tree** workflow (`.github/workflows/format-tree.yml`) runs the formatter of
https://github.com/leanprover/lean4/pull/15218 over every module under `src/`, checks each
reformatted file, and proposes the files that pass as a draft pull request from the branch
`format/<base>`. It runs on GitHub-hosted runners and never on the build pool.

Start it from the Actions tab with **Run workflow**. The inputs are the branch to format, an
optional sample size for a quick trial, and whether to open the pull request.

The result is layout only, and **nothing is compiled**. The pull request is pushed with the
workflow token, which does not start other workflows, so close and reopen it to run the checks.

## What the jobs do

1. **Build Lean with the formatter.** The formatter is not in a Lean release, so Lean is built
   from the pinned commit and cached. It has to be an ordinary source build: official toolchains
   refuse `.olean` files from another build, and no Mathlib has been built with the formatter's
   Lean.
2. **Format.** `setup-formatter-mathlib.sh` downloads the Mathlib that
   `leanprover/downstream-lean4` built with the Lean nightly the formatter is based on.
   `run-workers.py` then runs `BatchFmt.lean` over the files. The driver does not elaborate the
   project. It parses each file command by command, elaborates only the commands that change how
   later text parses, and hands each command to the formatter.
3. **Verify.** Two independent checks on every file the formatter changed:
   - `ParseCompare.lean` parses the original and the formatted file on the project's own toolchain
     and Mathlib and requires the same syntax tree: the same node kinds, atoms and identifiers in
     the same order. Only `;` and the `,` between structure-instance fields may disappear.
   - `split-check.py` compares the two files as text, without Lean. Only whitespace may differ,
     apart from a removed `;` or `,`. No whitespace may land inside a token and no two tokens may
     run together, judged against every token of both Mathlib versions and of the project.

   `select-files.py` takes a file only if both checks pass.
4. **Propose.** Applies the files that passed, commits, force-pushes `format/<base>` and opens or
   updates the draft pull request. Only this job can write to the repository.

A pull request that touches the workflow or this directory runs jobs 1 to 3 on a sample of 2,000
files as a self-test.

## What has to be kept up by hand

- **`ProjectSyntax.lean`** declares the notation and tactic syntax that the project uses in a
  different file from the one that declares it. The driver does not elaborate imports, so it only
  knows such syntax from this file. If one is missing, Lean reads its token as something else
  (`*ᵥ` becomes `*` followed by `ᵥ`) and the formatter prints it that way. Both checks catch
  that, so the affected files are left alone, not broken, but they stay unformatted until the
  declaration is added here.
- **`KEEP_UNTOUCHED`** in the workflow lists the files that are never reformatted. It holds
  `Challenge.lean` and `Statements.lean`.
- **The pins** at the top of the workflow:
  - `FORMATTER_LEAN_COMMIT`, the formatter's commit. Changing it rebuilds Lean, which takes a
    while on a hosted runner.
  - `FORMATTER_MATHLIB_REF` and `FORMATTER_MATHLIB_COMMIT`, the `green-nightly-…` branch of
    `leanprover/downstream-lean4` for the nightly that commit is based on.
  - `patch-import-graph.py` removes one definition that ImportGraph and the formatter both
    declare. It stops with a message when the file no longer looks as expected.

Once the formatter ships in a Lean release that the project uses, jobs 1 and 2 reduce to running
the formatter's own command, and the Mathlib download, the patch and `ProjectSyntax.lean` go away.
The two checks are worth keeping for as long as the formatter is new.

## Running the pieces by hand

Each script documents its arguments at the top. The order is the one in the workflow:
`list-files.py`, `run-workers.py`, `DumpTokens.lean` and `project-tokens.py`, `split-check.py`,
`run-compare.py`, `select-files.py`, `apply-formatted.py`.
