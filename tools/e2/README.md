# tools/e2 — the package split and the sweep harness (2026-08-28/29)

* `moddag.py` — module/import DAG of `src/Equiv/*.dfy` (the per-file package plan); `gen_pkgs.py [--apply]` —
  one lem package per file (`lem init` scaffolds + generated `[dependencies]`), the E1 split.
* `e2ts.py FILE.dfy` — tree-sitter-dafny analysis of one module: exact declaration spans (doc comments and
  `ghost`/`opaque` modifiers attached), same-module references (member accesses excluded), SCCs. Needs
  `pip install tree-sitter ~/code/tree-sitter-dafny` (a venv is fine). Writes `FILE.dfy.ts.json`.
* `e2split.py FILE.dfy OUTDIR [--apply]` — levels = longest path over the SCC condensation; bands = contiguous
  level ranges (edit `BANDS`); asserts no upward reference; emits one module file per band. `e2pkgs.py` writes the
  band packages' manifests; `e2api.py` repoints `ApiMatch`'s `LSIM` imports to the band modules.
* `patchdeps.py`, `wfrun.sh`, `fullrun.sh` — the interim scripted sweeps (Boogie `/proc` filters through
  manifest-patched `.doo` copies); superseded by `LEM_BUILD_TIMEOUT=0 lem pack` at the workspace root.

Paths inside the scripts point at this checkout and a session scratchpad; adjust `S`/`R` before reuse.
