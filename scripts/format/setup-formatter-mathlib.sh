#!/usr/bin/env bash
# Fetch a Mathlib that the formatter's Lean can import, and print the LEAN_PATH for it.
#
#   setup-formatter-mathlib.sh FORMATTER_LEAN WORK_DIR DOWNSTREAM_REF DOWNSTREAM_COMMIT
#
# FORMATTER_LEAN is a Lean built from the formatter's commit, with `bin/` and `lib/` inside.
# The formatter is based on a Lean nightly, and leanprover/downstream-lean4 publishes a Mathlib
# built with exactly that nightly. This script downloads that build with the nightly's own `lake`
# and then replaces the one module that clashes with the formatter (see patch-import-graph.py),
# rebuilt with the formatter's `lake`.
#
# The formatter's Lean must be an ordinary source build. Official toolchains are configured with
# CHECK_OLEAN_VERSION=ON and refuse `.olean` files that another build produced.
#
# Writes WORK_DIR/lean-path.txt. `lake` on PATH must be elan's, so that the downstream checkout
# selects the nightly through its `lean-toolchain` file.
set -euo pipefail

if [[ "$#" != 4 ]]; then
  echo "usage: setup-formatter-mathlib.sh FORMATTER_LEAN WORK_DIR DOWNSTREAM_REF DOWNSTREAM_COMMIT" >&2
  exit 2
fi
formatter_lean="$(cd -- "$1" && pwd)"
mkdir -p "$2"
work="$(cd -- "$2" && pwd)"
ref="$3"
commit="$4"
here="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

# Mathlib and the packages it depends on, as they are named in downstream-lean4.
packages=(mathlib4 batteries aesop quote4 ProofWidgets4 plausible LeanSearchClient import-graph lean4-cli)

cd "$work"
if [[ ! -d downstream/.git ]]; then
  git clone --quiet --depth 1 --filter=blob:none --sparse --branch "$ref" \
    https://github.com/leanprover/downstream-lean4.git downstream
fi
cd downstream
found="$(git rev-parse HEAD)"
if [[ "$found" != "$commit" ]]; then
  echo "downstream-lean4 $ref is at $found, expected $commit: update the pin deliberately" >&2
  exit 1
fi
patterns=('/*' '!/*/' '/.meta/')
for p in "${packages[@]}"; do patterns+=("/$p/"); done
git sparse-checkout set --no-cone "${patterns[@]}"

toolchain="$(cat lean-toolchain)"
export LAKE_CONFIG="$work/downstream/.meta/lake-config.toml" LAKE_CACHE_DIR="$work/lake-cache"
mkdir -p "$LAKE_CACHE_DIR"
# Dependencies first, Mathlib last.
for repo in lean4-cli batteries quote4 aesop plausible LeanSearchClient import-graph ProofWidgets4 mathlib4; do
  echo "== lake cache get: $repo"
  (cd "$repo" && lake cache get --scope "$toolchain/$repo")
done
echo "== restoring the Mathlib build from the cache"
(cd mathlib4 && LAKE_ARTIFACT_CACHE=1 LAKE_RESTORE_ARTIFACTS=1 lake build Mathlib)
unset LAKE_CONFIG LAKE_CACHE_DIR

echo "== rebuilding ImportGraph.Lean.Syntax without the clashing definition"
patched="$work/downstream-patched"
rm -rf "$patched"
mkdir -p "$patched"
cp -R import-graph lean4-cli "$patched/"
cp lean-toolchain "$patched/lean-toolchain"
rm -rf "$patched/import-graph/.lake/build" "$patched/import-graph/.lake/config" \
       "$patched/lean4-cli/.lake/build" "$patched/lean4-cli/.lake/config"
python3 "$here/patch-import-graph.py" "$patched/import-graph/ImportGraph/Lean/Syntax.lean"
(cd "$patched/import-graph" &&
  env -u ELAN_TOOLCHAIN -u LAKE_ARTIFACT_CACHE -u LAKE_RESTORE_ARTIFACTS \
    "$formatter_lean/bin/lake" build ImportGraph.Lean.Syntax)
built="$patched/import-graph/.lake/build/lib/lean/ImportGraph/Lean"
target="$work/downstream/import-graph/.lake/build/lib/lean/ImportGraph/Lean"
for ext in olean olean.server olean.private ilean ir ir.sig; do
  [[ -f "$target/Syntax.$ext" ]] || { echo "expected $target/Syntax.$ext from the cache" >&2; exit 1; }
  cp -f "$built/Syntax.$ext" "$target/Syntax.$ext"
done

lean_path=""
for p in "${packages[@]}"; do
  lean_path+="${lean_path:+:}$work/downstream/$p/.lake/build/lib/lean"
done
printf '%s\n' "$lean_path" > "$work/lean-path.txt"

echo "== checking that the formatter's Lean imports Mathlib"
probe="$work/probe"
mkdir -p "$probe"
printf 'import Mathlib\nimport Lean.Fmt\n' > "$probe/Probe.lean"
(cd "$probe" && env -u ELAN_TOOLCHAIN LEAN_PATH="$lean_path" "$formatter_lean/bin/lean" Probe.lean)
echo "ok: $work/lean-path.txt"
