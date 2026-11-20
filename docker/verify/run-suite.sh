#!/bin/bash
# The Linden verification suite. Exits 0 only when all three steps pass.
#  1. `lem pack` at the workspace root rebuilds every member from source, in
#     dependency order, with `dafny build -t:lib`. That is the build the registry
#     worker runs. Each member is checked against its siblings' just-built .doos;
#     no registry .doo is trusted.
#  2. `dafny audit` on every member. Any finding outside Dafny's own standard
#     library fails the suite: an assume, an {:axiom}, a bodyless lemma or
#     function, an {:extern}, a {:verify false}, and so on.
#  3. `lem audit` on the top package: lem's trust surface must report 0
#     declared-unproven obligations across the closure.
# Logs go to /out (mount a host directory there to keep them).
set -uo pipefail
OUT=${OUT:-/out}
mkdir -p "$OUT"
SUMMARY=$OUT/summary.txt
: > "$SUMMARY"
say() { echo "$*" | tee -a "$SUMMARY"; }

# Test for .git, not the directory: baking from a mounted repo with
# `podman build -v` leaves an empty /linden-src mount point in the image.
if [ -e /linden-src/.git ]; then
  WS=$HOME/work/Linden-Dafny
  rm -rf "$WS"
  git -c safe.directory='*' clone -q /linden-src "$WS" || exit 2
  [ -n "${LINDEN_REF:-}" ] && { git -C "$WS" checkout -q --detach "$LINDEN_REF" || exit 2; }
  SRC="mounted /linden-src"
else
  WS=$HOME/Linden-Dafny
  SRC="baked clone"
fi
cd "$WS" || exit 2

say "== Linden verification suite"
say "source:    $SRC, $(git log -1 --format='%H (%cd)')"
say "lem:       $(lem version 2>&1 | head -1)"
say "dafny:     $("$DAFNY_REAL" --version 2>&1 | head -1) (z3 bundled with the toolchain)"
say "limits:    DAFNY_MAX_CORES=$DAFNY_MAX_CORES LEM_JOBS=$LEM_JOBS LEM_BUILD_TIMEOUT=$LEM_BUILD_TIMEOUT"
say "machine:   $(nproc) cores, $(awk '/MemTotal/{printf "%.0f GiB", $2/1048576}' /proc/meminfo) RAM"

# ---- 1. full workspace pack from source -------------------------------------
say "== step 1: lem pack (all members, from source)"
t0=$(date +%s)
lem pack --jobs "$LEM_JOBS" 2>&1 | tee "$OUT/pack.log"
pack_rc=${PIPESTATUS[0]}
t1=$(date +%s)
packed=$(grep -c '^packed ' "$OUT/pack.log" || true)
say "pack:      exit $pack_rc, $packed members packed, $(( (t1 - t0) / 60 ))m"
grep -E '^workspace packed:|^error' "$OUT/pack.log" | tee -a "$SUMMARY"

# ---- 2. trust audit --------------------------------------------------------
# dafny audit only resolves (no solver), but each run loads the member's whole
# closure (about a minute and a few GB each), so AUDIT_JOBS of them run at once.
say "== step 2: dafny audit (every member, standard library excluded)"
AUDIT_JOBS=${AUDIT_JOBS:-4}
mkdir -p "$OUT/audit"
members=$(for d in regex-engine linden-*/; do d=${d%/}; [ -f "$d/lemmata.toml" ] && echo "$d"; done)
# Audits the shipped fileset (every manifest has to_export = src/**/*.dfy)
# against the member's restored closure from dfyconfig.toml. That dfyconfig
# globs **/*.dfy, which would pull in tests/ and their test-only dependencies.
audit_one() {
  local m=$1 log=$OUT/audit/$1.txt
  (
    cd "$m" || exit 1
    args=()
    for l in $(grep -o '"deps/[^"]*\.doo"' dfyconfig.toml | tr -d '"'); do args+=(--library "$l"); done
    grep -q '^standard-libraries *= *true' dfyconfig.toml && args+=(--standard-libraries:true)
    mapfile -t srcs < <(find src -name '*.dfy' | sort)
    "$DAFNY_REAL" audit "${srcs[@]}" "${args[@]}"
  ) > "$log" 2>&1
  if grep -q 'Dafny auditor completed' "$log"; then echo ok > "$OUT/audit/$m.status"
  else echo incomplete > "$OUT/audit/$m.status"; fi
}
n=0
for m in $members; do
  n=$((n + 1))
  while [ "$(jobs -rp | wc -l)" -ge "$AUDIT_JOBS" ]; do wait -n; done
  audit_one "$m" &
done
wait
audit_rc=0
: > "$OUT/audit-findings.txt"
for m in $members; do
  if [ "$(cat "$OUT/audit/$m.status" 2>/dev/null)" != ok ]; then
    say "audit:     $m did not complete (see audit/$m.txt)"; audit_rc=1; continue
  fi
  grep 'Warning:' "$OUT/audit/$m.txt" | grep -v '^DafnyStandardLibraries' | sed "s|^|$m/|" >> "$OUT/audit-findings.txt"
done
own=$(wc -l < "$OUT/audit-findings.txt")
say "audit:     $n members, $own findings outside the standard library"
[ "$own" -eq 0 ] || { audit_rc=1; head -20 "$OUT/audit-findings.txt" | tee -a "$SUMMARY"; }

# ---- 3. lem's trust surface of the top package -----------------------------
# Counts obligations any package in the closure declares unproven.
say "== step 3: lem audit (linden-equiv closure)"
(cd linden-equiv && lem audit > "$OUT/lem-audit.txt" 2>&1)
lem_audit_rc=$?
unproven=$(sed -n 's/.* \([0-9][0-9]*\) declared-unproven obligation.*/\1/p' "$OUT/lem-audit.txt" | head -1)
say "lem audit: exit $lem_audit_rc, ${unproven:-?} declared-unproven obligations"
[ "$lem_audit_rc" -eq 0 ] && [ "${unproven:-x}" = 0 ] || audit_rc=1

if [ "$pack_rc" -eq 0 ] && [ "$audit_rc" -eq 0 ]; then
  say "== PASS"; exit 0
fi
say "== FAIL (pack exit $pack_rc, audit $([ $audit_rc -eq 0 ] && echo clean || echo 'not clean'))"
exit 1
