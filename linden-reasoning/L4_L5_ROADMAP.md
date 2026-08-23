
### (B) addendum — the inner-capture correspondence is SUBTLE (verify empirically)

Deeper dig into (B) this session surfaced an UNRESOLVED subtlety that the confident "surface groups +
recon_inner" plan above glosses over. Ground truth confirmed: engine `reverse_regex`
(regex-engine/src/Engine/Regex.dfy:246) is NO-FLIP and recurses into look bodies; `DefGroups` recurses
into looks (inner gids ARE in `S`); `TreeResPreservesGid` (CaptureContent.dfy:501) already exists and
is nesting-aware. The OPEN question: does `SwapGm(spec-backward-tr inner) == spec-forward-RevL(tr)
inner` hold for a nested lookbehind's inner captures? Two armchair analyses CONTRADICT:

- **char-level position trace → NO.** With no-flip, a nested `(?<=r1)` stays a lookbehind on both
  sides (LkDir=Backward both). Backward-walk-`r1`-at-`p` reads original chars `p-1,p-2,…` (before p);
  backward-walk-`RevL(r1)`-over-swapped-at-`n-p` reads original chars `p,p+1,…` (after p) — different
  characters, so the two re-walks capture unrelated spans. This says full-`MirrorGm` `BackBodyGmTie`
  is FALSE on inner gids.
- **mirrored-oracle argument → YES.** The ENGINE never re-walks a nested look inline; it consults a
  precomputed oracle whose mirror (`MirrorView`) reflects the bit/captures by position. So the engine's
  RevRE-side inner captures are `SwapGm` of the true inner captures by construction.

These can't both be right about the same object. The resolution hinges on WHAT the keystone's RHS
`GmOfLive(body, MirrorRegs(rfF…))` actually equals — the engine's oracle-based inner captures, or a
spec-forward re-walk. If the L4-forward-nested tie equates engine-forward to the spec FORWARD TREE
(re-walk semantics), the keystone reduces to the char-trace-FALSE claim and must be RESTATED (route
inner gids through the oracle mirror, not `BackBodyGmTie`). **Do NOT commit a value-side lemma until a
minimal concrete instance is run through Dafny to adjudicate this.** The span side (A) is unaffected
and stands green.
