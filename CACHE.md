# Build cache for this branch

This branch is commit 72fead1 of https://github.com/lsernau/grh-lean (the branch `grh-lean`) plus
configuration and scripts for a shared build cache. No file under `grh/src` or `grh-compact/src`,
and no `Challenge.lean`, `comparator.json` or `Statements.lean`, is changed. The additions are
`CACHE.md`, the marked lines in each `lakefile.toml`, and `Cache.lean`, `lake-cache-get.sh`,
`ci-cache-get.py` and `fetch-artifacts.py` in each project's `scripts` directory. The scripts are
copied or adapted from `scripts/` on the `main` branch of
https://github.com/leanprover-community/riemann-hypothesis.

**The cached files were built from an unverified third-party proof, and the cache does not verify
anything.** The checks in the scripts only establish that you have the bytes which were published
for your exact build inputs. To check the proof, build it from source yourself, without this cache.

## Use

In either project directory, `grh-compact` or `grh`:

    lake exe cache get
    lake build

This needs Python 3.11 or newer and curl 7.71 or newer, and no credential. It fetches Mathlib's
cache, then this project's, and unpacks it. It ends with `lake build --no-build`, which must report
that nothing needs compiling. `lake exe mathlib/cache get` fetches Mathlib alone.

A change to the sources, `lakefile.toml`, `lake-manifest.json` or `lean-toolchain` gives different
build inputs; `lake exe cache get` then says that no cache matches.

## Keys

Each project has its own keys in the bucket behind https://rh-cache.taucetiproject.org :

- `artifacts/leanprover-community/riemann-hypothesis/grh-lean/<project>/<hash>.art`: Lake's `.ltar`
  files, named by Lake's content hash;
- `grh-lean/<project>/inputs/<fingerprint>.json`: the record for one set of build inputs (Git tree of
  `src`, `lakefile.toml`, `lake-manifest.json` and toolchain);
- `grh-lean/<project>/maps/<sha256>.jsonl` and `grh-lean/<project>/module-manifests/<sha256>.jsonl.gz`:
  Lake's map and the list of modules, with the SHA-256 of every artifact.

Nothing here reads or writes the keys of the main project's cache.
