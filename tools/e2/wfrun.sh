#!/usr/bin/env bash
# wfrun.sh OUTDIR File.dfy [File2.dfy ...]  — well-formedness-only sweep (Boogie /proc:CheckWellformed*) of whole files,
# against the manifest-patched deps in $S/deps-wf. Env: PAR (default 2), CORES (default 8), TL (default 300).
set -u
OUT=${1:?OUTDIR}; shift
S=/tmp/claude-1000/-home-aaron-code-Linden-Dafny/4b2a334e-25cd-4ec4-91cd-749084e887a7/scratchpad
ROOT=$HOME/code/Linden-Dafny/linden-equiv
PROC=${PROC:-CheckWellformed*}; PAR=${PAR:-2}; CORES=${CORES:-8}; TL=${TL:-300}
mkdir -p "$OUT"; OUT=$(readlink -f "$OUT"); cd "$ROOT" || exit 2
one() {
  f=$1; short=$(basename "$f" .dfy); log="$OUT/$short.wf.log"; start=$(date +%s)
  dafny verify --library=$S/deps-wf/DafnyStandardLibraries.doo --library=$S/deps-wf/DafnyStandardLibraries-cs.doo \
    --library=$S/deps-wf/linden-engine.doo --library=$S/deps-wf/linden-engine-model.doo --library=$S/deps-wf/linden-reasoning.doo \
    --library=$S/deps-wf/linden-semantics-core.doo --library=$S/deps-wf/linden-warblre.doo --library=$S/deps-wf/regex-engine.doo \
    --allow-warnings --cores="$CORES" --verification-time-limit="$TL" --error-limit 0 \
    --boogie "/proc:$PROC" "$f" > "$log" 2>&1
  rc=$?; el=$(( $(date +%s) - start ))
  res=$(grep -o 'finished with [0-9]* verified, [0-9]* error[s]*' "$log" | tail -1)
  [ -n "$res" ] || res="NO SUMMARY (rc=$rc) $(grep -m1 -E 'Error|error' "$log" | cut -c1-160)"
  printf '%s  %-22s %s  [%ds]\n' "$(date +%H:%M:%S)" "$short" "$res" "$el" >> "$OUT/summary.txt"
}
export -f one; export OUT S TL CORES PROC
printf '%s  START %s (PAR=%s CORES=%s TL=%s)\n' "$(date +%H:%M:%S)" "$*" "$PAR" "$CORES" "$TL" >> "$OUT/summary.txt"
printf '%s\n' "$@" | xargs -P "$PAR" -I{} bash -c 'one "$@"' _ {}
printf '%s  DONE\n' "$(date +%H:%M:%S)" >> "$OUT/summary.txt"
