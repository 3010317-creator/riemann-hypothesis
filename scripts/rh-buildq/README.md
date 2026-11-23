# Fragment builds against the shared cache

The `fragment` mode of `.github/workflows/build-pr.yml` builds a list of Lake targets of one
commit on a chosen self-hosted runner of the RiemannHypothesisBuild group. Some of these
runners belong to donors, and the commit may be an untrusted pull request, so the build runs
sandboxed and the runner never holds cache credentials (see "Security model" below). The
newly built modules are uploaded as a GitHub Actions artifact, and the `fragment_publish` job
on a GitHub-hosted runner verifies them and publishes them to the R2 cache when the build job
ends. Chunks of an `rh-shard` plan can be built on several machines; each picks up what the
others have already published when it starts or is rerun. Dispatch it from `main`:

    gh workflow run build-pr.yml --ref main -f mode=fragment -f pr_number=0 \
      -f fragment_commit=<sha> -f fragment_targets='Mod.A Mod.B' -f fragment_runner=<label>

- `fragment_commit` is a SHA on GitHub, or `SHA BASE HEAD DATE PR` for the deterministic
  merge commit that `rh-buildq start <PR>` builds. The job recreates that merge and checks
  that it gets SHA.
- `fragment_targets` is a list of module names, `gz:<base64 of a gzipped list>`, an
  `https://` URL, or `git:<ref>:<path>` in this repository. For a URL or `git:` spec that
  points at an `rh-shard-plan/1` plan, append `#<chunk id>`. The job then builds that chunk's
  `targets`.
- `fragment_jobs` sets `LEAN_NUM_THREADS` (default: all cores).

Each job runs these steps:

0. `fragment.py probe` starts the sandbox and checks from inside that $HOME, the runner's
   files and the network are out of reach. If bubblewrap cannot create the namespaces, the job
   fails here; there is no unsandboxed fallback.
1. `fragment.py restore` keeps one tree per run, in `$RH_FRAGMENT_ROOT/<sha>-<run id>/`
   (default `~/rh-fragments`). Rerunning the job reuses it. The tree of a successful run is
   deleted at the end. Each job also deletes the trees of other runs that have completed
   (with any conclusion); it keeps those of queued or running runs. When it cannot read a
   run's status, it deletes the tree only after a week untouched. The first
   time, it clones the repository and picks the nearest first-parent ancestor that has a
   published CI record. It installs the commit's toolchain with the host's elan, after
   checking that `lean-toolchain` names an official `leanprover/lean4` release. On every
   run, `pool-restore.py` then fetches Mathlib's cache and builds
   one merged map: the CI map of a successful build with that ancestor's inputs (checked like
   `scripts/ci-cache-get.py` does, and SHA-256 checked per artifact on download), the
   `rh-buildq/pool` union, this commit's `rh-buildq/maps` entry and the stock revision maps.
   It registers the mappings Lake does not know yet with `lake cache add` (in parallel shards)
   while curl downloads the missing artifacts (`fetch-artifacts.py`, 500 at a time). Nothing is
   unpacked here: Lake 4.37 compiles a mapped module whose artifact is not local and does not
   download it, but it unpacks a local one during `lake build`.
2. `fragment.py build` runs `lake build -v -o .lake/rh-fragment-outputs-<run>.jsonl <targets>`
   with `LAKE_RESTORE_ARTIFACTS=true` in the offline sandbox. With `-v`, Lake logs every module
   as Built or Replayed, not only those with messages. The job log shows compiled modules,
   failures and one progress line a minute; the full log is in the result artifact.
3. `fragment.py stage` runs even when the build failed or the job was cancelled. It copies
   every module of the root package that Lake finished and that the restored maps do not
   already have (its `.ltar`, input hash and SHA-256) into a stage directory, which the job
   uploads as the artifact `fragment-cache-<run>`. After an interruption, it skips files from
   the last minute.
4. `fragment.py result` writes `result.json`: the built, replayed and failed modules, the
   number of staged modules, the outputs neither cached nor staged, and the timings. The job
   uploads it as the artifact `fragment-result-<run>-<attempt>`, together with the gzipped
   build log.
5. The `fragment_publish` job (`publish-fragment.py`) runs after the build job, also when it
   failed or was cancelled. It verifies the stage, then uploads the artifacts as
   content-addressed `artifacts/...` objects and records them in the
   `rh-buildq/maps/<sha>.jsonl` and `rh-buildq/pool/<toolchain>.jsonl` maps, which it updates
   by compare-and-swap.

Rerunning a job resumes the work: Lake replays everything already built in the tree, and the
stage skips what the restore found in the cache.

## Security model

The fragment job runs on self-hosted runners, some owned by donors, and builds commits that
may come from untrusted pull requests. Building a commit means running its code: Lake
evaluates the lakefiles of the project and its dependencies, runs Mathlib's cache tool and
Lean's elaborator, all at revisions the commit chooses. The job therefore splits its work:

- Trusted host code (the scripts in this directory, from the workflow's own commit): Git
  clone, fetch and checkout of the target, the toolchain installation with elan (official
  `leanprover` toolchains only), fetching and merging the public cache maps, staging. None of
  it evaluates the target's lakefile or runs anything from the target.
- The sandbox (`sandbox.py`) for everything that does: `lake exe mathlib/cache get` and
  `lake cache add` in the restore, and `lake build`. It is bubblewrap with `--unshare-all`
  (user, PID, IPC, UTS, cgroup and network namespaces, plus `--disable-userns` where
  bubblewrap supports it), `--die-with-parent`, `--new-session` and `--clearenv` with an
  explicit environment. The sandbox sees the system directories (`/usr`, `/bin`, `/lib*`,
  `/sbin`, `/nix/store`) read-only, single files of `/etc` (CA bundle, resolv.conf, hosts,
  nsswitch.conf, passwd, group, localtime, ld.so.cache) read-only, the toolchain read-only at
  `/opt/lean`, and the run's work tree `<queue>/project` read-write with its `.git`
  read-only. `/tmp` is a private tmpfs and `$HOME` is `/tmp/home`; the rest of its root is
  read-only. It does not see the donor's home directory (`~/.ssh`, `~/.elan` beyond the one
  toolchain, other runs' trees), the runner's work directory or its job token.
- Network: `lake build` and `lake cache add` run offline. Lake cloning the dependencies and
  Mathlib's cache tool need the network, so `lake exe mathlib/cache get` runs in a variant
  with `--share-net` and the same filesystem view. The artifact downloads
  (`fetch-artifacts.py`) are trusted code but write into the work tree, so they run in that
  variant too. Code in the network variant can reach whatever the host can reach on the
  network (including its LAN); donors who want to rule that out can firewall the runner's
  user account, allowing HTTPS to github.com, cache.mathlib.org and
  rh-cache.taucetiproject.org.
- The sandbox can leave anything in the work tree, including links to host files and FIFOs.
  After the first checkout, host code does not write into it, runs Git only against its
  `.git` (read-only in the sandbox), and reads it only through `sandbox.read_file`/`open_dir`
  (`O_NOFOLLOW` on every component, regular files only, bounded sizes). The stage directory
  and all other host-side state live outside the work tree.
- No R2 credentials reach the build host. The `fragment` job has no environment and reads no
  secret. Only `fragment_publish`, a fresh `ubuntu-latest` job in the `ci-cache-publish`
  environment (deployable from `main` only), derives R2 keys from `R2_ACCOUNT_TOKEN`, and
  only after `publish-fragment.py verify` has accepted the stage. Like
  `scripts/publish-ci-cache.py`, it runs nothing from the built commit and reads it only as
  Git objects. It recomputes the target (for `SHA BASE HEAD DATE PR`, the merge commit),
  requires every staged module to be a source file of that commit, every input hash to be
  valid and unique, every artifact's size and SHA-256 to match, and names each object by its
  stock Lake content hash, which it recomputes with the official toolchain. Maps only gain
  entries: an existing mapping is never replaced.
- What the publisher cannot check without rebuilding is that a module's input hash really
  yields its artifact. As for every CI cache (`verification/CACHE.md`), that is trusted to the
  build host; consumers who need certainty rebuild.

Since publication happens at the end of the build job, other fragments see a fragment's
modules only once it has finished (or been cancelled), not while it builds. Every run
downloads Mathlib's cache into its own tree instead of sharing `~/.cache/mathlib`, so that one
run's sandbox cannot alter what another run restores.

`scripts/quick-check.py` (the `quick-check` mode on small runners) already runs candidate
code only in the sandbox of `scripts/ci-build.py`: offline, `--unshare-all`, `--clearenv`,
`--die-with-parent`, `--new-session`, the project read-only except `.lake`, the toolchain at
`/opt/lean`, dependency copies without Git metadata, and no `$HOME`. It refuses candidates
whose lakefile, manifest or toolchain differ from `main`, prepares dependencies from `main`'s
own lakefile outside the sandbox, publishes nothing and holds no cache credentials.

`python3 scripts/rh-buildq/test_sandbox.py` checks the sandbox with a hostile lakefile that
tries to write into `$HOME`, read `~/.ssh`, read the runner's files and connect to the
network: all fail in the offline sandbox, all but the network in the network variant, and a
normal build of the same project succeeds. It also checks that the stage does not follow
links planted in the work tree.

These files started as copies of the rh-buildq host scripts. The additions are retries on
CDN errors, the toolchain read from the project, no EC2 Spot probing off EC2, `--settle` and
`--before` options for the publisher, the sandbox, and the split between staging on the
build host and publishing from `publish-fragment.py`. Hosts that hold their own publishing
credentials (our AWS rh-buildq hosts) keep running `publish.py` directly.
