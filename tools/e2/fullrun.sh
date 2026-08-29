#!/usr/bin/env bash
# fullrun.sh OUTDIR File.dfy [...] — FULL-FILE dafny verify (every symbol, no filter) with the real deps.
# Env: PAR (2), CORES (4), TL (600); BOOGIE="<args>" switches to the manifest-patched deps in $DEPS (default
# $S/deps-wf) and passes --boogie "$BOOGIE" (e.g. BOOGIE='/noProc:DeepFindRec*' to skip giants — patch the
# deps first with patchdeps.py so the manifests carry the same value).
set -u
OUT=${1:?OUTDIR}; shift
S=/tmp/claude-1000/-home-aaron-code-Linden-Dafny/4b2a334e-25cd-4ec4-91cd-749084e887a7/scratchpad
ROOT=$HOME/code/Linden-Dafny/linden-equiv
PAR=${PAR:-2}; CORES=${CORES:-4}; TL=${TL:-600}; BOOGIE=${BOOGIE:-}; DEPS=${DEPS:-$S/deps-wf}
mkdir -p "$OUT"; OUT=$(readlink -f "$OUT"); cd "$ROOT" || exit 2
one() {
  f=$1; short=$(basename "$f" .dfy); log="$OUT/$short.full.log"; start=$(date +%s)
  if [ -n "$BOOGIE" ]; then
    LIBS="--library=$DEPS/DafnyStandardLibraries.doo --library=$DEPS/DafnyStandardLibraries-cs.doo"
    for d in linden-engine linden-engine-model linden-reasoning linden-semantics-core linden-warblre regex-engine; do LIBS="$LIBS --library=$DEPS/$d.doo"; done
    EXTRA=(); for b in $BOOGIE; do EXTRA+=(--boogie "$b"); done
  else
    LIBS="--standard-libraries"
    for d in linden-engine linden-engine-model linden-reasoning linden-semantics-core linden-warblre regex-engine; do LIBS="$LIBS --library=deps/$d.doo"; done
    EXTRA=()
  fi
  dafny verify $LIBS --allow-warnings --cores="$CORES" --verification-time-limit="$TL" --error-limit 0 \
    "${EXTRA[@]}" "$f" > "$log" 2>&1
  rc=$?; el=$(( $(date +%s) - start ))
  res=$(grep -o 'finished with [0-9]* verified, [0-9]* error[s]*' "$log" | tail -1)
  [ -n "$res" ] || res="NO SUMMARY (rc=$rc) $(grep -m1 -E 'Error|error' "$log" | cut -c1-160)"
  printf '%s  %-22s %s  [%ds]\n' "$(date +%H:%M:%S)" "$short" "$res" "$el" >> "$OUT/summary.txt"
}
export -f one; export OUT S TL CORES BOOGIE DEPS
printf '%s  START %s (PAR=%s CORES=%s TL=%s BOOGIE=%s)\n' "$(date +%H:%M:%S)" "$*" "$PAR" "$CORES" "$TL" "$BOOGIE" >> "$OUT/summary.txt"
printf '%s\n' "$@" | xargs -P "$PAR" -I{} bash -c 'one "$@"' _ {}
printf '%s  DONE\n' "$(date +%H:%M:%S)" >> "$OUT/summary.txt"
