# linden-verify: the whole verification suite in one container

This image rebuilds every Linden package from source in a clean container and
then checks that nothing is assumed. It uses the toolchain the
registry.lemmata.sh worker uses: stock Dafny 4.11.0 with the z3 4.12.1 it
bundles. The image:

* installs `lem` from apt.lemmata.sh;
* installs the hash-pinned Dafny 4.11.0 release with `lem toolchain install`;
* clones `hath995/Linden-Dafny` at `LINDEN_REF`;
* runs `run-suite` (`run-suite.sh`) as its entrypoint.

## Build and run

```sh
docker build -t linden-verify docker/verify                         # main
docker build -t linden-verify --build-arg LINDEN_REF=<sha|branch> docker/verify
mkdir -p out
docker run --rm --memory=48g -v "$PWD/out:/out" linden-verify
```

To check a commit that is not pushed yet, mount the checkout. The suite clones
its committed `HEAD` (or `-e LINDEN_REF=...`), so uncommitted files, `deps/` and
pack caches never enter the run:

```sh
docker run --rm --memory=48g -v "$PWD:/linden-src:ro" -v "$PWD/out:/out" linden-verify
```

Podman works the same way (`podman build`, `podman run`).

For a published image, build with `LINDEN_REF` set to a full commit SHA. The
image then carries that exact source, and its `org.opencontainers.image.revision`
label names it. Reviewers only need to run it:

```sh
docker run --rm --memory=48g -v "$PWD/out:/out" <image>
```

`out/summary.txt` names the commit, the lem and Dafny versions, and the verdict.

## What it checks

1. **`lem pack` at the workspace root.** It rebuilds all members from source in
   dependency order with `dafny build -t:lib`, the same build the registry
   worker runs. Each member is checked against its siblings' freshly built
   `.doo`s, so no published artifact is trusted. Any verification error, any
   warning, or any member over `LEM_BUILD_TIMEOUT` fails the run.
2. **`dafny audit` on every member.** Every finding outside Dafny's own standard
   library fails the run: `assume`, `{:axiom}`, bodyless lemmas or functions,
   `{:extern}`, `{:verify false}`, and so on. The standard library's own axioms
   are excluded; Linden imports only `Std.Wrappers`, which has none.
3. **`lem audit` on `linden-equiv`.** lem's trust surface for the top package's
   whole closure must report 0 declared-unproven obligations.

The run exits 0 only when all three pass. `/out` receives `summary.txt`,
`pack.log`, `audit/<member>.txt`, `audit-findings.txt` and `lem-audit.txt`.

## Cost and knobs

A full pack takes about 1 h 45 min at 4 cores (pack runs S35 and S36 on
2026-11-19: 1 h 45 min 54 s and 1 h 44 min 40 s), plus about 20 min for the
audits. Those runs used 4 cores under a 48 GB cap, so give the container 48 GB.
At 16 cores under 48 GB, one nest-stamp z3 reached 15.9 GB and was OOM-killed.

| env | default | meaning |
|---|---|---|
| `DAFNY_MAX_CORES` | 4 | z3 workers per Dafny build. One batch can take 10-16 GB under z3 4.12.1, so raise this only with the memory to match (8 needs about 48 GB). |
| `LEM_JOBS` | 1 | members built at once (`lem pack --jobs`) |
| `LEM_BUILD_TIMEOUT` | 30m | wall clock per member; a build past 30 min has failed |
| `AUDIT_JOBS` | 4 | parallel `dafny audit` runs |
| `LINDEN_REF` | (none) | with `/linden-src` mounted: the ref to check out |

Build args: `LEM_VERSION` (empty means the latest apt release), `DAFNY_VERSION`
(4.11.0), `LINDEN_REPO`, `LINDEN_REF` (main).

`dafny-capped` is the only shim. lem runs it through `LEM_DAFNY`. It pins
`--cores` for `build` and `verify`, keeping a member's own lower `cores`
setting, and passes everything else to the pinned toolchain unchanged.
