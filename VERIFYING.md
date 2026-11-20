# Verifying Linden-Dafny

These instructions re-check the whole Linden-Dafny proof from source on your
own machine. There are two ways to do it:

* **A. Docker:** one command, nothing to install but Docker.
* **B. lem directly:** install the `lem` package manager, clone the
  repository, and run the same checks yourself.

Both check the same commit:

```
9c7d8cae6e9ce81e4197b792deaa479cbb7cfa08
```

## What is being checked

The headline result is `LindenRegexApi.MatchCorrect`
(`linden-equiv/src/Equiv/ApiMatch.dfy`, line 71):

```dafny
lemma MatchCorrect(pattern: R.raw_regex, str: string)
  requires Supported(pattern)
  ensures LES.MatcherSpec(pattern, str, Match(pattern, str))
```

For every supported pattern and every input, the RegElk engine's full-match
result (`Match`, the JavaScript-style capture array) is exactly the answer the
Linden backtracking-tree semantics of ECMAScript regexes prescribes.
`MatchCorrect` wraps `MainTheoremL5Cin`
(`linden-equiv-main-cin-lk/src/MainCinG4b2.dfy`). `Supported` is defined in the
same file. `linden-equiv/SUPPORTED_FRAGMENT.md` explains what the fragment
admits and why each gap exists.

The proof is split into 79 Dafny packages, built as one lem workspace
(`lem-workspace.toml`). A full check does three things:

1. **Rebuilds every package from source** in dependency order with
   `dafny build -t:lib`, using stock Dafny 4.11.0 and the z3 4.12.1 it bundles.
   Each package is checked against its dependencies' freshly built `.doo`
   files. Nothing published on the registry is trusted. Any verification
   error, timeout or warning fails the run.
2. **Audits every package for unproven assumptions** with `dafny audit`: any
   `assume`, `{:axiom}`, bodyless lemma or function, `{:extern}`,
   `{:verify false}` or similar fails the run. Findings inside Dafny's own
   standard library are excluded. Linden imports only `Std.Wrappers`
   (`Option`/`Result`) from it, and that module has none.
3. **Runs `lem audit`** on the top package. lem's trust surface over the whole
   dependency closure must report 0 declared-unproven obligations.

## Requirements

* x86-64 Linux, or Docker on an x86-64 host. That is the tested setup;
  see the notes below for other platforms.
* **48 GB of RAM** for the default 4 parallel solver workers. Under z3 4.12.1
  a single proof batch can use up to 16 GB, so we do not recommend less.
* 4 cores. A full run takes about 2 hours. Our test run of the image took
  1 h 45 min for the build and 17 min for the audits.
* Network access: Docker Hub (option A, about 800 MB), apt.lemmata.sh and
  GitHub (option B), and registry.lemmata.sh. lem reads the registry's package
  index to resolve the workspace, but builds every package locally.
* A few GB of disk.

---

## A. Verify with Docker

### A1. Use the published image

```sh
docker pull <dockerhub-user>/linden-verify:9c7d8ca
mkdir -p out
docker run --rm --memory=48g --memory-swap=48g -v "$PWD/out:/out" \
  <dockerhub-user>/linden-verify:9c7d8ca
```

### A2. Or build the image yourself

The Dockerfile is in the repository at `docker/verify/`. Building it yourself
means you need not trust a prebuilt image:

```sh
git clone https://github.com/hath995/Linden-Dafny.git
cd Linden-Dafny
git checkout 9c7d8cae6e9ce81e4197b792deaa479cbb7cfa08
docker build -t linden-verify \
  --build-arg LINDEN_REF=9c7d8cae6e9ce81e4197b792deaa479cbb7cfa08 docker/verify
mkdir -p out
docker run --rm --memory=48g --memory-swap=48g -v "$PWD/out:/out" linden-verify
```

The image is Ubuntu 24.04. It installs `lem` from the signed apt repository
apt.lemmata.sh, then installs Dafny 4.11.0 with `lem toolchain install`. lem
downloads the official Dafny release from GitHub and checks its SHA-256
against a hash pinned in the lem binary. The image then clones this
repository at `LINDEN_REF`.

Podman works the same way: replace `docker` with `podman`.

### Reading the result

The container exits 0 on success and writes these files to `out/`:

| file | contents |
|---|---|
| `summary.txt` | commit, tool versions, the result of each step, `PASS` or `FAIL` |
| `pack.log` | the full build log, one `packed linden.<name> (N obligations, time)` line per package |
| `audit/<package>.txt` | the raw `dafny audit` output per package |
| `audit-findings.txt` | audit findings outside the standard library (should be empty) |
| `lem-audit.txt` | lem's trust surface for the top package |

A successful `summary.txt` contains these lines:

```
pack:      exit 0, 79 members packed, ...
workspace packed: 79 members, 6997 obligations verified, in ...
audit:     79 members, 0 findings outside the standard library
lem audit: exit 0, 0 declared-unproven obligations
== PASS
```

---

## B. Verify with lem directly

### B1. Install lem

lem is self-contained, so you need neither .NET nor Dafny installed. It was tested with **lem 0.1.27**; check yours with `lem version`.

**Debian / Ubuntu (amd64):**

```sh
curl -fsSL https://apt.lemmata.sh/lemmata-release.pub \
  | sudo gpg --dearmor -o /usr/share/keyrings/lemmata-archive-keyring.gpg
echo "deb [signed-by=/usr/share/keyrings/lemmata-archive-keyring.gpg] https://apt.lemmata.sh stable main" \
  | sudo tee /etc/apt/sources.list.d/lemmata.list
sudo apt update && sudo apt install lem
```

**macOS (Homebrew):** `brew tap hath995/lemmata && brew install lem`

**Windows:** use WSL2 with Ubuntu and follow the Debian/Ubuntu steps, or use
Docker (option A). lem itself installs with Scoop
(`scoop bucket add lemmata https://github.com/hath995/scoop-lemmata`, then
`scoop install lem`), but the helper scripts below are POSIX shell.

**Other Linux:** download an archive from
<https://github.com/hath995/lemmata-releases/releases> and check its `.sha256`.
Keep `lem` next to the `dafny/` directory it ships with and put that directory
on your `PATH`.

Then install the pinned Dafny 4.11.0 and check the setup:

```sh
lem toolchain install 4.11.0
lem toolchain list     # shows the 4.11.0 path
lem doctor
```

### B2. Clone the repository

```sh
cd ~
git clone https://github.com/hath995/Linden-Dafny.git
cd Linden-Dafny
git checkout 9c7d8cae6e9ce81e4197b792deaa479cbb7cfa08
```

### B3. Cap the solver workers

By default Dafny starts one z3 worker for every two logical cores. On a large
machine that can exhaust memory: at 16 workers, one package needed more than
48 GB. The repository ships a small shim,
`docker/verify/dafny-capped`, that pins `--cores` and otherwise runs Dafny
unchanged. lem uses it through `LEM_DAFNY`:

```sh
export DAFNY_REAL=$(lem toolchain list | awk '$1 == "4.11.0" {print $4}')
export LEM_DAFNY=$PWD/docker/verify/dafny-capped
export DAFNY_MAX_CORES=4         # z3 workers per package build
export LEM_JOBS=1                # packages built at once
export LEM_BUILD_TIMEOUT=30m     # wall clock per package
"$DAFNY_REAL" --version          # should print 4.11.0+...
```

### B4. Run the checks

**All three steps with the suite script.** It is the same script the Docker
image runs. It needs Linux (or macOS with bash ≥ 4.3) and the clone at
`~/Linden-Dafny`:

```sh
mkdir -p ~/linden-out
OUT=~/linden-out bash docker/verify/run-suite.sh
```

It writes the same files as option A, to `~/linden-out`.

**Or step by step:**

```sh
# 1. Rebuild and verify every package from source (about 1 h 45 min at 4 cores).
lem pack --jobs 1
#    The last line reads "workspace packed: 79 members, 6997 obligations verified, in ...".
#    `lem verify` checks the same packages through `dafny verify` instead of
#    `dafny build`. The registry worker runs `dafny build`, as `lem pack` does.

# 2. Audit each package's shipped sources (src/**/*.dfy) for assumptions
#    (about a minute per package). Every finding should be in
#    DafnyStandardLibraries*.dfy, so these lines print nothing on success.
for m in regex-engine linden-*/; do
  m=${m%/}; [ -f "$m/lemmata.toml" ] || continue
  out=$( cd "$m"
    libs=$(grep -o '"deps/[^"]*\.doo"' dfyconfig.toml | tr -d '"' | sed 's/^/--library /')
    "$DAFNY_REAL" audit $(find src -name '*.dfy' | sort) $libs --standard-libraries:true 2>&1 )
  echo "$out" | grep -q 'Dafny auditor completed' || echo "$m: AUDIT DID NOT COMPLETE"
  echo "$out" | grep 'Warning:' | grep -v '^DafnyStandardLibraries' | sed "s|^|$m/|"
done

# 3. lem's trust surface of the top package's closure.
( cd linden-equiv && lem audit | head -3 )
#    Expect "... 0 declared-unproven obligation(s)".
```

Step 2 needs the `deps/` directories that step 1 creates.

---

## Notes

* **Why the exact toolchain matters.** Dafny's verdicts depend on the solver
  version. Every package here was made to verify under the stock Dafny 4.11.0
  release and its bundled z3 4.12.1, which is also what the Lemmata registry's
  verification worker runs. Every package's `.doo` records the solver version
  it was built with.
* **Apple Silicon.** The Docker image is `linux/amd64`. On an ARM Mac it runs
  under emulation, which is far slower and may exceed the 30-minute
  per-package limit. Use option B natively instead: lem pins Dafny 4.11.0 for
  `osx-arm64` too. That platform has not been part of our testing.
* **Less memory.** `DAFNY_MAX_CORES=2` lowers peak memory and lengthens the
  run. We have not measured how far it can safely go below 48 GB.
* **The published packages.** The same 79 packages are published at version
  1.0.0 on registry.lemmata.sh under the `linden` namespace. There, the
  registry's own worker re-verified each one from source. `lem status
  linden.equiv` shows that record. These instructions do not rely on it.
