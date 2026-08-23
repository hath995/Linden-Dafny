
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

### (B) deepest finding — WHY the mirror is a dead-end for nested looks (not just captures)

Traced the nested-look semantics under no-flip reversal rigorously (3x, consistent):
- `spec-backward-tr` at nested `(?<=r1)` (interior pos p) checks r1 backward from p = chars BEFORE p
  (correct original semantics).
- `spec-forward-RevL(tr)` at the mirrored `(?<=RevL(r1))` (pos n-p in Reverse(str)) checks RevL(r1)
  backward from n-p = `Reverse(str)[..n-p]` = reverse of `str[p..]` = r1 FORWARD from p = chars AFTER p.

So the no-flip mirror evaluates the WRONG condition for a nested lookbehind — not just wrong captures,
wrong GATE too. To read the same text the mirror would have to FLIP lookbehind->lookahead, but the
engine `reverse_regex` (regex-engine/src/Engine/Regex.dfy:246) is NO-FLIP (confirmed from source).
This is corroborated three ways: (a) `MatchesLReverse` (SpanDuality:373, the span mirror) requires
`GroupOkL` — look-free — and its own doc-comment says "the ORACLE (a boolean) can be characterized
this way while captures could not"; (b) L4 already excludes inner-look gids from the mirror tie via
`GmAgreeOutside(.., LkBodyGroups)`; (c) the engine keeps nested looks as looks precisely to consult a
position-indexed ORACLE rather than re-execute a mirrored body.

**Therefore: do NOT widen `ComputeTreeReverse` / `BackBodyGmTie` / `MatchesLReverse` to nested looks —
they are fundamentally blocked (mirror-wants-flip vs engine-no-flip).** The mirror handles ONLY the
surface (look-free skeleton). Nested looks — BOTH their zero-width gate AND their inner captures — are
supplied by the direction-generic backward oracle (the equiv-side machinery that "runs nested
lookbehinds backward today"), on both engine and spec sides, at original (un-mirrored) positions. The
span-side (A) `Bwd*`/`MatchesL` widening is the DIRECT-backward tool this needs (it characterizes the
backward walk WITHOUT any mirror) — so (A) is foundational for the direct-backward keystone, not
wasted. T2b(i)'s no-flip `RevL`-into-looks is harmless (never used for nested looks, since the mirror
is not the vehicle there) — conservative for the look-free surface, which is all it serves.

Net: L5's nested keystone `LkReplayMatchesSpecLBNested` is NOT a widening of the L3b mirror keystone;
it is a DIRECT engine-backward <-> spec-backward tie (surface groups reconciled by the mirror as
before; inner-look groups by the backward oracle). Sizeable, but the dead-ends are now fenced off.
