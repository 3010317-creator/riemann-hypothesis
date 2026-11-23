# Persistent stock-Lake worker for Lean 4.37

This deployment-owned worker consumes explicitly leased, dependency-ready project modules in an immutable Git snapshot. It retains one stock Lake workspace and BuildStore across requests. The mathematical source, package pins, compiler options, plugins, dynamic libraries, stock compiler, and publication/staging tools are unchanged.

Build with the pinned official toolchain:

```sh
lake build proof-worker
```

Run the executable from the project root with `LEAN_SYSROOT` and `LAKE_HOME` pointing to that same official installation. The deployment supplies `.snapshot.json`, installs the three `support/` files into the project's `scripts/sharding/` directory, and verifies pinned dependency packages and incoming native artifacts before publishing each `request-N.json`. The worker writes the original result, artifact manifest, and response into the supplied request directory.

```sh
RH_MINIMAL_SETUP=1 /path/to/proof-worker /private/request-directory SNAPSHOT_FINGERPRINT loop
```

Without the environment flag, requested targets use the existing stock target builder. With the flag, the worker first walks current project imports using stock source-header facets. A request containing duplicate targets, non-project targets, or an ancestor and its descendant falls back as a whole to the unchanged stock builder. An antichain request constructs `ModuleSetup` directly with an empty `importArts`; it retains current stock presetup, options, plugins, dynamic libraries, build action, trace, output invalidation, compiler invocation and artifact computation. Imported native modules still resolve through the admitted Lean search path.

This adopts the applicable minimal-setup idea from [Vasily's rh-lc](https://github.com/Vilin97/rh-lc/tree/0b0432c47355481a888cfb0bbb43883d1fa0b4c3). It does not adopt its mtime/compiler stamp or archive reuse. Stock `clearOutputArtifacts` removes stale LTAR outputs before compiling. Existing producer identities and original receipts remain separate from new validation and deployment records.

Matched current-source tests compare all seven compiler output parts and stock input/output hashes. Independent gates exercise fresh stock LTAR packing, target-cold restoration, ordinary stock rehash/no-build and imports. A 150-module comparison previously reduced setup JSON from 439 MB to 46 KB but did not improve total wall time; no fourfold project speed claim is made. Bypassing recursive registration is a separately gated next step.
