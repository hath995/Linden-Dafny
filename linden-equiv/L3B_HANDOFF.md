# L3b Handoff — captures inside positive LOOKBEHINDS (updated 2026-08-13)

## ⛔ REMAINING WORK: backward tree-closedness (the ONE gap left) — full recipe below

The full-file sweep (2026-08-13) proved the prior "COMPLETE" was masked across THREE layers.
Value-lift + oracle: DONE (d066355, green). Fragment/confinement/tree-rep: DONE (ae3a7b4,
green — PikeLkRegex/LkBodiesInS/guards widened for positive-BACKWARD captures). **The ONE
remaining gap:** `LookBodyLeafOpenSub` (MainTheorem.dfy) backward branch needs `ClosedGm` of a
capturing lookbehind body's first leaf, but the spec-side closedness machinery
(`FirstLeafClosedNoLk`/`BoolTreeLk`) is FORWARD-only.

**DO NOT duplicate the ~200-line `BoolTreeLk` machinery.** Use the spec-tree MIRROR (all lemmas
exist in linden-reasoning; imports `TM=LindenTreeMirror`, `TRM=LindenTreeResMirror`,
`CDE=LindenCloseDisc` ALREADY ADDED to MainTheorem, plus the verified bridge
`NoLkBrGroupOkL: EL.NoLkBrL(r) ==> SD.GroupOkL(r)`). RECIPE for `LookBodyLeafOpenSub`'s `else`
(backward) branch — goal: `ClosedGm(subR[0].1)`, then mirror the forward branch's 1140-1146
`OpenOf(sub[0].1) <= OpenOf(gm)` reasoning:
  1. `n := |inp.pref| + |inp.next|`.  `r1` is `NoLkBrL` ⇒ `NoLkBrGroupOkL(r1)` ⇒ `SD.GroupOkL(r1)`.
  2. `CDE.CloseDiscBody(rer, r1, inp, gmR, WP.Backward)` ⇒ `CDE.CloseDisc(tlk, {})`
     (needs `GroupOkL(r1)` + `CDE.NoDupG(L.DefGroups(r1))` — see threading below).
  3. `tm := FU.ComputeTr(rer, SD.RevActs([LS.Areg(r1)]), SD.SwapInput(inp), TRM.MirrorGm(gmR,n), Forward)`;
     `SD.RevActs([Areg(r1)]) == [Areg(SD.RevL(r1))]`.  `TM.ComputeTrReverse(rer,[Areg(r1)],inp,gmR,MirrorGm(gmR,n))`
     ⇒ `TM.TreeMirrorRel(tlk, tm)` (needs `SD.GroupOkActs([Areg(r1)])` from GroupOkL(r1)).
  4. Forward closedness on `tm`: `RevL(r1)` is `GroupOkL` (`SD.RevLGroupOk`) ⇒ `NoLkBrL` (bridge back);
     replicate the forward branch's ComputeTree→`EL.ComputeBoolTreeLk`→`FirstLeafClosedNoLk` setup
     for `[Areg(RevL(r1))]` over `SwapInput(inp)` from `MirrorGm(gmR,n)` ⇒ `ClosedGm(rf.value.1)`
     where `rf := LT.TreeRes(tm, MirrorGm(gmR,n), SwapInput(inp), Forward)`.
  5. `TRM.TreeResMirror(tlk, tm, gmR, inp, n, {})` ⇒ `rf.value.1 == TRM.MirrorGm(rb.value.1, n)`,
     `rb := LT.TreeRes(tlk, gmR, inp, Backward)` (== `subR[0]`, since `|subR|>0`).
  6. `TRM.MirrorRange` maps closed→closed, so `ClosedGm(MirrorGm(rb.value.1,n)) ⇒ ClosedGm(rb.value.1)`
     = `ClosedGm(subR[0].1)`. (May need a tiny `MirrorGm`-preserves-`ClosedGm` helper.)
**THREADING (the cost):** `TreeResMirror` needs `TRM.GmInBounds(gmR, n)`; `gmR ⊆ gm` so add
`requires TRM.GmInBounds(gm, |inp.pref|+|inp.next|)` to `LookBodyLeafOpenSub` AND thread it up
through `FirstLeafClosed`/`FirstLeafValueConfined` (both `least lemma`s) to their callers. Also
add `requires CDE.NoDupG(L.DefGroups(r1))` (from the regex's `CapUnique`, already threaded for L3a
elsewhere). Both new requires discharge at the two call sites (MainTheorem:~1597, ~1942). Then
REMOVE the forward-only `requires L.DefGroups(r1) != [] ==> L.LkDir(lk) == WP.Forward` (the L3a
"only lookaheads capture" assumption). Re-verify MainTheorem (2941 VCs) + LiftSim full-file.

Progress this session: imports + `NoLkBrGroupOkL` bridge added & verified; `FirstLeafClosed`/
`FirstLeafValueConfined` asserts already widened (vestigial `dir==Forward` conjunct retired).

---

## (was) L3b GENUINELY COMPLETE (branch `l3b-gate-swapgm`, commit d066355) — after closing TWO hidden holes

**Correction to the earlier "COMPLETE at af4f063" banner below.** That status came from
filter-verifying `MainTheoremL3` — which does NOT check the *bodies* of the lemmas it calls
(Dafny exports a lemma's postcondition to callers even when its own body is red). A full-file
regression sweep of every L3b-touched file (2026-08-13) exposed **two load-bearing lemmas
whose bodies never verified**. Both are now discharged with real proofs (no axioms/assumes),
commit **d066355**:

1. **`FreshBodyMatchCapWf`** (LiftSim). `FreshBodyMatch` is direction-generic
   (`capture_regex(looktype,body)` in `capture_direction(looktype)`), but the body only proved
   the forward/lookahead case → with `looktype` opaque, `CapRegWf` was undischarged. Fixed by a
   case-split: `FreshMatchWf` (lookahead) / `FreshMatchWfLB` (lookbehind), `MatchedPosLA` giving
   positivity; the backward context fact is definitional. (LiftSim full-file 9522/4 → **9537/0**)
2. **The lookbehind oracle-characterization layer** — leftover red from `dcb7cc8 "WIP L3b
   fragment flip (PACKAGE RED by design)"`. `OracleColumnSpec` → `OracleColumnCharacterized`
   → `FBuildOracleCorrectAt` + `LookTablesLidBuildOk` all required `CaptureFreeRE(body)`, false
   for a capturing lookbehind. Fixed by reasoning over `remove_capture(body)` (what `oracle_regex`
   is literally built over — `lazy_prefix(remove_capture(body))`), then bridging to the capturing
   body at the `OracleColumnSpec` top via capture-blind `MatchesRemoveCapture` +
   `TranslateLookFreeGroupOk(body)`. Mirrors the L3a `OracleColumnSpecLookahead` upgrade. Added
   NR `remove_capture` preservation lemmas (LookFree/Nullable/PlusFragment); loosened
   `OracleRegexPlusFragment`. `OracleEntry` needed no source change. (OracleBuild 45/5 → **46/0**,
   OracleEntry 23/5 → **24/0**, NfaRepRE 1328/0, OracleDecomp 72/0, OracleSpec 30/0)

**Full-file green confirmed** for all edited files + MainTheorem (2941/0) + PikeInvRE (251/0);
whole workspace re-packed in dependency order (`lem pack`: engine-model 72, engine 117,
reasoning 382, … all 0 errors). `deps/*.doo` refreshed. **Lesson: never trust filter-verified
`MainTheoremL3` alone — full-file verify every touched file.**

---

## (superseded — premature) L3b COMPLETE (commit af4f063) — captures inside positive lookbehinds, ZERO axioms

`MainTheoremL3`: **1857 verified, 0 errors.** The whole lookbehind gate path has NO
`{:axiom}` / `assume`. Task #8 (the backward capturing-lookbehind gate step) is DONE:
- `ThreadRepLkStepCheckOracleLB` (LiftSim ~6266): a real `lemma` — GateStepValueLB (inside
  tie) + WalkPairLkAtCheckOracle + GmtTieOutsideAfterGate.
- `GateStepValueLB` (337/0): Case A value = `SwapRange(gmbK[g])` from `LBK.BackFreshBodyGmTie`.
- `BackFreshBodyGmTie` (585/0): the crux — `SwapGm(LkResult.value)` ≈ `GmOfLive(body, raB.*)`
  via keystone + `BackwardReplayMirror` + `MirrorRegsInvol`/`BackCapsInRange` (only the caps
  bank is positionally read — `GmOfLiveClkCong`; the backward caps≤n bound comes from the
  FORWARD bound on `rfF` + `CapRegWf` clock-coupling, NO backward caps-LE lemma).
- gate-pass call site + coverage: derived static package (`StaticOkRE`⟹CapUnique/QuantUnique,
  `LookCheckIdsRE`, `NI.LookBodyOfFragment`, `OS.TranslateLookFreeGroupOk`,
  `TranslateDefGroupsNoDup`); coverage = the keystone key-set (SwapGm preserves keys).
- `|ov|==|str|+1`: `MIR.FAdvanceEpsilonViewLenD`/`FFindMatchViewLen` + `OB.FBuildLidsLen`/
  `FBuildOracleViewLen`, threaded through the sim chain to the gate.

Next: `lem pack` to propagate, then merge `l3b-gate-swapgm`.

---

## (superseded) ENDPOINT COMPLETE — only the gate axiom (task #8) remains

**The entire L3b proof now verifies GREEN except ONE clearly-marked axiom.** The
reversed-lookbehind-span endpoint reconciliation — the hard discovery of this run — is
fully proven:
- `MainTheoremL3` (TOP THEOREM): **1856 verified, 0 errors.**
- `L3aEndpointAssembly`: **2356 verified, 0 errors.**
- `MainExtraction`, `L3aValueBridge`, `NormRangeFromSwap`, `PIV.GmOfCapArrayBridgeNorm`
  + the `NormRange`/`NormGm` family: all green.
- `GmtTieInside` SwapGm threading: dormant-green (task #7).

**THE ONLY REMAINING WORK — task #8** (IN PROGRESS): fill `ThreadRepLkStepCheckOracleLB`
(LiftSim ~6074, `{:axiom}`) + discharge the coverage `assume {:axiom}` (LiftSim ~4566).

DONE so far: `MIR.MirrorRegsInvol` (Mirror.dfy) — `MirrorRegs(MirrorRegs(r,n),n)==r` for
banks with `a_cp` in `[-1,n]` (2/0, committed).

DETAILED ROADMAP (with the key simplifications found):
1. **`BackFreshBodyGmTie`** (put in LookBehindKeystone.dfy) — the crux value helper:
   `SwapGm(LkResult(TrLookaround(la),tlk,gmMain,inp).value)` agrees with
   `GmOfLive(body, raB.caps, raB.looks, raB.quants)` on `Sbody`, where `raB` is the backward
   FFindMatch (init regs, `cdns=crv.f_look_cdns[l]`). Proof:
   - `LBK.LkReplayMatchesSpecLB(...init...)` → agrees with `GmOfLive(body,MirrorRegs(rfF.caps),
     MirrorRegs(rfF.looks),MirrorRegs(rfF.quants))`.
   - `BV.BackwardReplayMirror(...init...)` → `rfF==MirrorThread(raB)`, so `rfF.X==MirrorRegs(raB.X)`.
     (Needs `MirrorRegs(init_regs)==init_regs` — see `MirrorRegsAgreeInit` at LBK ~191.)
   - **KEY SIMPLIFICATION**: `GmOfLive` reads ONLY `caps.a_cp` + the three `a_clk` banks
     (filter_reset ignores look/quant `a_cp` — see `GmOfLiveInit` destructuring `(_,lc)`,`(_,qc)`).
     So only the CAPS need the involution; looks are init (look-free body) and quant `a_cp`
     is unread. So: `GmOfLive(body,MirrorRegs(rfF.caps),·,·)==GmOfLive(body,raB.caps,·,·)`
     via `MirrorRegsInvol(raB.caps,n)`. (Clocks already match — MirrorRegs keeps `a_clk`.)
   - **THE ONE NEW INFRA PIECE**: `MirrorRegsInvol` needs `raB.caps.a_cp[k] in [-1,n]`.
     `CapRegWf` gives `>=-1`; the `<=n` bound is `CM.RegsValsLE(raB.caps,n)` but
     `FFindMatchCapsLE` (LBK ~100) is Forward-HARDCODED ("VmCapsLE is a forward invariant").
     Build a BACKWARD twin (`FAdvanceEpsilonCapsLE`/`FConsumeCapsLE` are already dir-generic;
     the FFindMatch recursion decreases `s.cp` for Backward) — OR a GmOfLive congruence over
     `RegsAgreeInside` on `CaptureRegs(body)` that avoids the full-bank bound.
2. **`GateStepValueLB`** (LiftSim, after GateStepValue ~2482): mirror GateStepValue's
   131-line body with `la.Lookbehind?`, `LkDir==Backward`, and the extra keystone requires
   (PlusFragmentRE, QuantUnique, GroupOkL, NoDupG). Case A uses `BackFreshBodyGmTie` +
   `FreshBodyMatch(l,th2)==raB` (definitional: `capture_regex(Lookbehind,body)==reverse_regex(body)`,
   `capture_direction(Lookbehind)==Backward`, `get_cp(th2.look_regs,l)==cp`); the ensures'
   `if looktype.Lookbehind? then SwapRange(gmb) else gmb` picks SwapRange, matching
   `gmt2[g]==SwapRange(gmbK[g])`. Case B (frame) is IDENTICAL to GateStepValue.
3. **`ThreadRepLkStepCheckOracleLB` body**: mirror `ThreadRepLkStepCheckOracle` (~6155) —
   (1) GateStepValueLB for the inside tie, (2) `WalkPairLkAtCheckOracle` (direction-generic),
   (3) `GmtTieOutsideAfterGate` ("works for backward gates too"). Add the keystone static
   package to its requires.
4. **Call site** (LiftPreserveGatePassLk `else` at ~4413): supply the static package (the
   `:|` at ~4312 already has LookEntryOk + fragment facts).
5. **Coverage `assume {:axiom}`** (~4566): `g in gm2` from SwapGm preserving keys (BackFreshBodyGmTie
   key-set) — or fold into GateStepValueLB.

---

## (superseded) LATEST — GmtTieInside threads SwapGm; gate DORMANT-GREEN; endpoint is the last red

**The deep step-6/7 crux is RESOLVED structurally and committed.** `GmtTieInside`
(LiftSim ~190) now compares the ordered spec value `gmt[g]` to the REVERSED engine
read `gmb[g]` via `if looktype.Lookbehind? then LBV.SwapRange(gmb[g]) else gmb[g]`.
The SAME if-form was threaded through all **11 manual restatements** (a script:
`scratchpad/thread_swap*.py`) so the Swap cancels SYMBOLICALLY for lookaheads —
DORMANT for every existing case. **Verified GREEN**: GateStepValue, LiftPreserveSetRegLk,
ThreadRepLkStepCheckOracle, LiftPreserveConsumeAddLk, LiftPreserveForkLk,
LiftPreserveGatePassLk, InsidePresentResBridge.

**WIP {:axiom} surface (2, both dischargeable by `LBK.LkReplayMatchesSpecLB`):**
- `ThreadRepLkStepCheckOracleLB` (LiftSim ~6074): backward-gate value step, body
  pending. Chain: `FreshBodyMatch(LB)=raB` → `BV.BackwardReplayMirror` (rfF=MirrorThread(raB))
  → keystone gives `SwapRange(gm2[g]) == GmOfLive(body, raB.caps)[g]`. Its call site
  (gate-pass `else` at ~4413) + the coverage `assume {:axiom}` (~4566) are wired.
- Task #8 = fill this body.

**ENDPOINT (task #9) — IN PROGRESS, most pieces GREEN:**
- `PIV.GmOfCapArrayBridgeNorm` + `NormRange`/`NormGm`/`NormRangeClosed`/`NormRangeOrdered`
  (PikeInvRE): committed, 2/0.
- `MainExtraction` (MainTheorem 5362): reworked to `leaf.1 == NormGm(GmOfLive)` +
  `GmOfCapArrayBridgeNorm`. **2/0 GREEN.** (Closedness derived from NormGm BEFORE the
  clock-order forall; `GmOfLiveEqGmOf` stays AFTER it — it needs the clock order.)
- `L3aValueBridge` (LiftSim): `requires OrderedGm(leafgm)`, inside-present is now
  `NormRange`, ensures `leafgm == NormGm(GmOfLive)`. **2/0 GREEN.**
- `NormRangeFromSwap` (LiftSim): converts InsidePresentResBridge's look-type swap to
  positional NormRange via leaf-orderedness. **2/0 GREEN.**
- `L3aEndpointAssembly`: reworked (forward-forall→NormRange via NormRangeFromSwap,
  ensures→NormGm, requires OrderedGm; removed a stale `assert la.Lookahead?`; fixed the
  post-L3aValueBridge assert to NormGm). **2330 verified, 0 ERRORS**, 2 perf timeouts at
  11720 (heavy `:|`+MatchedPosLA — slow-but-finite; 400→500s dropped 5→2). Re-running at
  800s / may extract the per-g body to a helper if needed.
- `MainTheoremL3`: FirstLeafOrdered supplies OrderedGm(leaf.1); the three `leaf.1==GmOfLive`
  asserts → NormGm. Verifying (trusts L3aEndpointAssembly's ensures regardless of its
  internal perf timeouts).

**Original design (for reference):**
`L3aEndpointAssembly` (LiftSim 11231) forward-forall (~11520) still claims the plain
equality `leaf.1[g] == GmOfLive(re,res0)[g]`; for capturing LB the engine registers
`res0` hold the REVERSED span, so `leaf.1[g] == SwapRange(GmOfLive(re,res0)[g])`.
`MainExtraction` (MainTheorem 5362, block 5439-5454) currently proves `f` has NO
reversed pairs (making NormalizeArr a no-op) — FALSE for LB. The clean fix (4 steps):

1. **`NormRange(r)`** = `if r reversed (start>end) then SwapRange(r) else r`;
   **`NormGm(gm)`** = per-group `NormRange`. (positional — no look-type needed.)
2. **NEW `PIV.GmOfCapArrayBridgeNorm`** (sibling of `GmOfCapArrayBridge`, PikeInvRE):
   DROP the no-reversed-pairs precondition; conclude
   `NormalizeArr(f) == CapArrayOfLeaf((inp, NormGm(GmOf(ast,caps))))`. This is the
   POSITIONAL heart of item-0 — NormalizeArr's per-pair swap == NormRange's swap.
   *Self-contained, highest-value to de-risk first.*
3. **Endpoint** (L3aEndpointAssembly + L3aValueBridge ensures): conclude
   `leaf.1 == NormGm(GmOf(re,res0))` instead of `leaf.1 == GmOf`. Per-group proof:
   `leaf.1[g] == NormRange(GmOf[g])` from InsidePresentResBridge's look-type swap +
   **FirstLeafOrdered (leaf ordered)** — the KEY: for LB, `leaf.1[g]==Swap(gmb)` ordered
   ⟹ `gmb` reversed ⟹ `NormRange(gmb)==Swap(gmb)==leaf.1[g]`; for LA, `leaf.1[g]==gmb`
   ordered ⟹ `NormRange(gmb)==gmb`. So NO separate "LB⟺reversed" lemma is needed — it
   falls out of leaf-orderedness. (`InsidePresentResBridge` already delivers the swap-
   aware per-g tie; its ensures is GREEN.)
4. **MainExtraction**: replace the 5439-5454 no-reversed-pairs block with
   `NormalizeArr(f) == CapArrayOfLeaf((inp,NormGm(GmOf))) == CapArrayOfLeaf(leaf)`
   [via `leaf.1 == NormGm(GmOf)` from step 3 + the new bridge from step 2].

---

> **IN PROGRESS — the fragment flip + its ENTIRE MECHANICAL TIER are DONE and
> VALIDATED (uncommitted WIP, package RED only on the value-machinery stubs).**
> Working-tree changes (NfaRepRE.dfy, OracleEntry.dfy, MainTheorem.dfy, LiftSim.dfy),
> NOT committed (the flip cannot reach package-green until the value-machinery stubs
> are filled — the top-level theorem is unprovable for a capturing lookbehind whose
> captures aren't yet reconstructed). DONE + verified GREEN in isolation:
> - **Fragment flipped** (`NfaRepRE.dfy`): `LookBehindFragmentRE`/`…Raw` clauses
>   (`(la.Lookahead? || …)` → `+ la.Lookbehind?`) + `AnnotateLookBehindFragment` stub
>   regated (`!look.Lookahead?` → `look.NegLookahead? || look.NegLookbehind?`).
>   **Full file 1325/0.**
> - **All 4 ENSURES roots weakened + verified 2/0**: `OE.LmOfInv` (disjunction
>   `+ la.Lookbehind?`), `LmOfInvL3a`, `LookRowsFromTablesL3a`, `LmOfBodiesDisjoint`
>   (MainTheorem), `GateStaticsSweepRE` (LiftSim).
> - **All ~26 consumer ANTECEDENT drops applied** (`(la.Lookbehind? || la.NegLookbehind?
>   || la.NegLookahead?) ==> CaptureFreeRE` → drop `la.Lookbehind?`): 19 in
>   MainTheorem.dfy (la/la2 variants), 7 in LiftSim.dfy. (`replace_all` on the exact
>   pattern; safe — positive lookbehinds may now capture.)
>
> **RESIDUAL RED = ONLY the value-machinery stubs** (build-order steps 1–4 below):
> `FLookLoopValueLift` LB branch (MainTheorem:~3848), `FLookLoopQuantValueLift` LB
> branch, `FLookLoopCaptureFrame`/`FLookLoopQuantFrame` LB branches (they used
> `ReplayFrames`' capture-IDENTITY, now unavailable), `LiftPreserveGatePassLk` LB arm
> (LiftSim:~4522), `L3aEndpointAssembly` LB arm (LiftSim:~11589), the `MainExtraction`
> rework (step 7), and the helper-precondition call sites (`OracleColumnSpec` etc.,
> step 8). To close them: build steps 1–4 (backward capture frames + `ReplayLidCapAgreeFreshLB`
> + `MatchedPosLA` widen/`FreshBodyMatch` dispatch + the LB value/quant branches),
> then steps 6–8. **Next: build the value machinery (green standalone), then these
> stubs + the whole flip land green together.**
>
> **STEPS 1 & 2 DONE — all backward frame/bisimulation lemmas verify 2/0** (MainTheorem.dfy):
> - Step 1: `ReplayCaptureFrameLB` (backward capture-write frame), `ReplayPlusFrameLB`
>   (wraps it with look/quant frames + `FNulledPlusIdentity` Backward), widened
>   `FFindMatchPlusOvStableLB` (dropped `CaptureFreeRE` → `CapUnique` + `ReverseCapUnique`;
>   oracle stability is capture-independent). Engine cores (`CM.CaptureBytecodeClassified`,
>   `FFindMatchCapWriteFrame`, `FFindMatchLookEq`, `FFindMatchQuantFinalAny`,
>   `FNulledPlusIdentity`) all dir-generic; reversed-body statics via
>   `PIV.ReversePlusFragment`/`ReverseLookFree`/`ReverseCapUnique`/`ReverseQuantUnique`/
>   `ReverseCapIds` + `NR.PlusIsLookBehindFragmentRE`.
> - Step 2: `ReplayCapAgreeFreshLB` (backward register-value-blind bisimulation, twin of
>   `ReplayCapAgreeFresh` — `CM.FFindMatchCapRel` is dir-generic, NO fragment/uniqueness
>   hypotheses) + `ReplayLidCapAgreeFreshLB` (the per-lid backward replay↔fresh capture
>   agreement, `RegsAgreeInside(result.caps, freshBackward.caps, CaptureRegs(body))`).
>
> **STEPS 3 & 4 DONE — the whole `FLookLoop` value machinery handles capturing
> lookbehinds, all GREEN:** `MatchedPosLA` widened (`+ .Lookbehind?`) and `FreshBodyMatch`
> dispatched on `capture_direction` (backward + `reverse_regex(body)` for LB;
> VALUE-IDENTICAL for lookaheads so no LA regression). LB branches rewritten:
> `FLookLoopValueLift` (**1236/0**), `FLookLoopQuantValueLift` (**1503/0**),
> `FLookLoopCaptureFrame` (1/0), `FLookLoopQuantFrame` (1/0). New helpers (all 2/0):
> `ReplayThreadWfLB`, `ReplayLidQuantAgreeFreshLB`, `ReplayQuantFrameLB`, `FreshMatchWfLB`.
> The LB branches MIRROR the lookahead branches with the step-1/2 lemmas; the
> suffix/IH/frame/assemble tails are direction-independent (copied verbatim).
>
> **THE DEEP CRUX (step 6/7), pinpointed:** `ThreadRepLk` (LiftSim:236 — the core pike
> simulation invariant) has a conjunct **`GmtTieInside`** (LiftSim) requiring, for each
> inside-look group `g in gmt`: `gmt[g] == GmOfLive(VBody(l), FreshBodyMatch(l).caps)[g]`.
> Since `FreshBodyMatch` now dispatches BACKWARD for lookbehinds, that engine read is
> REVERSED, while `gmt = gm2 = LkResult(lk, tlk, gm, inp).value` is spec-ORDERED — they
> differ by `SwapRange`. So `GmtTieInside(gm2)` is FALSE for a capturing lookbehind, and
> the gate cannot establish `ThreadRepLk` as-is. **FIX:** thread `SwapGm` through
> `GmtTieInside` — for a lookbehind lid, require `gmt[g] == SwapRange(gmb[g])` (lookahead
> unchanged). This is DORMANT/value-identical for every existing case (lookahead lids
> unchanged; capture-free lookbehinds have no groups `g`, so the branch is vacuous — like
> the `FreshBodyMatch` change), so the existing pike-simulation proofs should re-verify
> unchanged; only the NEW capturing-LB gate exercises the `SwapRange`. The keystone
> `LkReplayMatchesSpecLB` provides EXACTLY that form: `GmAgreeOn(SwapGm(LkResult),
> GmOfLive(body, MirrorRegs(rfF)))` ⟹ `gm2[g] == SwapRange(GmOfLive(fresh)[g])`. STEPS to
> land step 6/7: (1) add `SwapRange` to `GmtTieInside` (dormant); re-verify the ThreadRepLk
> consumers (LiftInv + step/preservation lemmas — most transparent). (2) build
> `ThreadRepLkStepCheckOracleLB` (the LB twin of `ThreadRepLkStepCheckOracle` LiftSim:6038,
> establishing `GmtTieInside`'s `SwapRange` form via the keystone at `cap=init`; needs the
> keystone accessible in LiftSim — add `include "LookBehindKeystone.dfy"`). (3) wire both
> LB stubs of `LiftPreserveGatePassLk` (LiftSim:4333–4370 the `gm2==gm` stub → real merged
> gm2; 4520–4533 the coverage). (4) the endpoint `L3aEndpointAssembly` LB arm. (5) the
> top reconciliation (step 7): with `GmtTieInside` SwapGm-threaded, the final leaf `gmt`
> satisfies `leaf.1[g] == SwapRange(GmOfLive(mainCaps)[g])` on LB groups, so
> `MainExtraction`/`MainTheoremL3` relate `NormalizeArr(f)` [item-0 swap] to
> `CapArrayOfLeaf(leaf)` via that per-group swap. This is a large, coupled, deep effort on
> the CORE invariant — a focused multi-session unit, but the crux and the shape are now nailed.
>
> **EMPIRICAL RESIDUAL (probed after steps 1–4):** `MainExtraction` verifies in
> ISOLATION (2/0) — its proof is self-consistent given `leaf.1 == GmOfLive`; the break
> is at its CALLER `MainTheoremL3`, where for a capturing lookbehind `GmOfLive(re,
> mainCaps)` is REVERSED on LB groups so `leaf.1 == GmOfLive` is FALSE. The gate pass
> `LiftPreserveGatePassLk` breaks at **LiftSim:4336/4521** — the LB arm is a
> value-carrying gate: it currently proves `gm2 == gm` (capture-free lookbehind adds
> no groups), but a CAPTURING lookbehind's `gm2` = the folded `LkResult` WITH the
> reconstructed (reversed) captures. So the LB arm needs a `ThreadRepLkStepCheckOracle`
> twin (the value-carrying gate step) + the keystone `LkReplayMatchesSpecLB`. **KEY
> STRUCTURAL FACT:** the keystone lives in `LookBehindKeystone.dfy` which `LiftSim`
> does NOT include (LiftSim includes MainTheorem + PikeTreeLk). To wire it, either add
> `include "LookBehindKeystone.dfy"` + `import LBK = LindenLookBehindKeystone` to
> LiftSim (transitively pulls in LookBehindValue/BackValue — no cycle; slower), or move
> the keystone (+ deps) into a file LiftSim already sees. GATE COVERAGE argument
> (worked out): apply the keystone at `cap = init_regs` — then its `raB` IS the fresh
> backward match `rfx = FreshBodyMatch`, and `BackwardReplayMirror` at `cap=init` gives
> `rfx.caps == MirrorRegs(rfF.caps)` (because `MirrorRegs(init_regs) == init_regs`), so
> `GmOfLive(body, rfx.caps)` is EXACTLY the keystone's `GmOfLive(body, MirrorRegs(rfF))`
> term; membership is swap-invariant so `g in GmOfLive(body, rfx) ==> g in gm2` follows.
> The DEEP piece (step 7): `MainTheorem`/`MainExtraction` must relate the reversed engine
> `GmOfLive` to the ordered spec `leaf.1` via the per-LB-group `SwapGm`, threaded from
> the gate/endpoint to the top — coupled with step 6, and where item-0's `NormalizeArr`
> swap finally ACTIVATES (a NEW LB-aware `GmOfCapArrayBridge` beside the forward one).
> Step 8 (oracle-column) is NOT purely mechanical: `OracleColumnSpec` requires
> `CaptureFreeRE(body)` on the ORIGINAL body; widening needs "matching is capture-
> independent" (`SuccActs(Translate(body)) == SuccActs(Translate(remove_capture(body)))`).
>
> **RESIDUAL RED now = steps 6–8 only:** the gate pass `LiftPreserveGatePassLk` LB arm
> (LiftSim:~4522) + endpoint `L3aEndpointAssembly` LB arm (LiftSim:~11589) — wire the
> keystone `LkReplayMatchesSpecLB`'s `GmAgreeOn(SwapGm(LkResult), GmOfLive(body,…))`
> (membership is swap-INVARIANT, so gate COVERAGE needs no swap); the `MainExtraction`
> reversed-span rework (step 7, `leaf.1 == GmOfLive` is forward-only — relate
> `NormalizeArr(f)` [item-0 swap] to `CapArrayOfLeaf(specLeaf)` for LB groups); and the
> oracle-column widening (step 8, `OracleColumnSpec`/`OracleColumnCharacterized`
> `CaptureFreeRE` → `CapUnique`, matching is capture-independent). Also audit any other
> `MatchedPosLA`/`FreshBodyMatch` consumer + residual `ReplayFrames`-at-LB call sites.
>
> **These WIP code changes are on a clearly-marked checkpoint commit (package RED by
> design — the value-machinery stubs are stubbed out). Do NOT treat it as green;
> the next green commit is when steps 1–8 complete.** Files: NfaRepRE.dfy,
> OracleEntry.dfy, MainTheorem.dfy, LiftSim.dfy.

> **Session 13 (2026-08-12) — ITEM 0 (the `NormalizeArr` reversed-span swap) is
> COMPLETE (dormant).** Commit `5a94f24`, three files, top-level `MainTheoremL3`
> re-verifies **1854/0**.
> - `NormalizeArr` (linden-reasoning/`Spec.dfy`) widened: a reversed pair (both
>   `>= 0`, start slot `>` end slot) is swapped back to `(start,end)`. NO-OP for
>   forward/unset groups, so L1/L2/L3a are undisturbed. Needs a `lem pack` rebuild
>   (done) to propagate the new `.doo` into linden-equiv.
> - Exactly ONE proof unfolds `NormalizeArr` element-wise — `PIV.GmOfCapArrayBridge`;
>   it gained a "no reversed pairs" precondition (`f[2g] <= f[2g+1]` for forward
>   groups), discharged at its sole caller `MainTheorem.MainExtraction` via the new
>   **`FirstLeafOrdered`** (+ `OrderedGm`/`GMUpdateOrdered`/`TreeResOrdered`) — a
>   clean structural induction: ordering is a LOCAL per-range property preserved by
>   every `TreeRes` step incl. the `LK`-node merge, needing none of `FirstLeafClosed`'s
>   pending-close bookkeeping (`GMClose` always orders min/max; `GMOpen` opens; `GMReset`
>   removes). `leaf.1 == GmOfLive` ties the ordered spec leaf to the register array.
> - The swap is **dormant** until item 1 admits capturing lookbehinds and their
>   reversed spans reach `NormalizeArr`. It is the spec-side dual of the keystone's
>   `SwapGm`, reconciling the engine's raw reversed readout with the ordered spec
>   answer at `MainExtraction`.
>
> **ITEM 1 (fragment flip) is NOT a standalone green commit — it is the integration
> trigger.** Flipping `LookBehindFragmentRE`'s `Re_lookaround` clause
> (`NfaRepRE.dfy:541`, `(la.Lookahead? || CaptureFreeRE(r1))` → add `|| la.Lookbehind?`)
> and its raw twin (`:566`) WEAKENS the fragment, so everything that derives "a
> lookbehind body is capture-free" breaks. Blast-radius map (do these together as
> the integration, wiring in `LkReplayMatchesSpecLB`):
> - **4 ENSURES roots break** (they PRODUCE the capture-free fact): `OE.LmOfInv`
>   (`OracleEntry.dfy:117`), `LmOfInvL3a` (`MainTheorem.dfy:4551`),
>   `LookRowsFromTablesL3a` (`MainTheorem.dfy:4724`), `GateStaticsSweepRE`/`GateStaticAt`
>   (`LiftSim.dfy:4170`/`4081`).
> - **~6 capture-free STUBS go live** (branches assuming "nothing to do"): the
>   lookbehind arms of `FLookLoopCaptureFrame` (`MainTheorem.dfy:2670`),
>   `FLookLoopQuantFrame` (`:2750`), `FLookLoopValueLift` (`:3648` — item #5),
>   `FLookLoopQuantValueLift` (`:3970`); `LiftPreserveGatePassLk` (`LiftSim.dfy:4522`
>   — item #6); `L3aEndpointAssembly` (`LiftSim.dfy:11589`).
> - **~10 helper preconditions become unmeetable** at capturing-lookbehind sites:
>   `ReplayFrames` (`:2792`), `FFindMatchPlusOvStableLB` (`:3036`), `OracleColumnSpec`
>   (`OracleSpec.dfy:353`), `OracleColumnCharacterized` (`OracleDecomp.dfy:1477`),
>   `CaptureCodeClassified`, `NoCaptureInstrRE` family — plus the raw-side stub
>   `AnnotateLookBehindFragment` (`NfaRepRE.dfy:667`) and `OracleRegexPlusFragment`
>   (`:703`). **Real coverage gap:** `OracleColumnSpec`/`OracleColumnCharacterized`
>   only SPECIFY capture-free lookbehind gates — capturing lookbehind gates need
>   new oracle-column coverage (part of item #3/#6).
> The keystone `LkReplayMatchesSpecLB` (item 4, `LookBehindKeystone.dfy`) supplies
> the value the STUBS need; the flip + these repairs are the remaining #1/#2/#3/#5/#6.
>
> **INTEGRATION BUILD ORDER (the remaining capstone; sub-lemma map).** Groundwork
> landed: `ReverseCapIds`/`ReverseCapUnique` (`PikeInvRE.dfy`, commit `8ceb5be`) —
> `reverse_regex` preserves cap ids + uniqueness (the engine compiles the LB capture
> pass over `compile_to_bytecode(reverse_regex(body))`, so every backward frame needs
> `CapUnique(reverse_regex(body))`). Remaining, in dependency order:
> 1. **Backward capture frames** (mirror the forward ones; the engine cores are
>    already direction-generic — `CM.FFindMatchCapWriteFrame` ClockMono:1058,
>    `FFindMatchRegsWf` MainTheorem:2093 — so the twins are mechanical):
>    - `ReplayCaptureFrameLB` / `ReplayPlusFrameLB` (twin of `ReplayCaptureFrame`/
>      `ReplayPlusFrame` MainTheorem:3025) over `bytecode==compile_to_bytecode(
>      reverse_regex(body))`, `dir==Backward`, framing on `CaptureRegs(reverse_regex
>      (body))==CaptureRegs(body)` (via `ReverseCapIds`). `FNulledPlusIdentity` and
>      `NoLookWriteBody` are dir-generic / need a `reverse_regex` look-free twin.
>    - WIDEN `FFindMatchPlusOvStableLB` (MainTheorem:3119): its `CaptureFreeRE(body)`
>      is NOT load-bearing (used only to get `CapUnique(reverse_regex(body))`) — swap
>      in `CapUnique(body)`+`ReverseCapUnique`. `ReplayThreadWfLA` needs NO twin (WF
>      comes inline from dir-generic `FFindMatchRegsWf`, as the current LB stub does).
> 2. **`ReplayLidCapAgreeFreshLB`** — the per-lid replay↔fresh cap agreement. NOT a
>    reuse of `ReplayLidCapAgreeFresh` (3214, Forward-hardcoded via `ReplayCapAgreeFresh`
>    4407): its LB analogue IS the keystone. But note the keystone's fresh reference
>    is `rfF` = a FORWARD run of `compile_to_bytecode(SD.RevRE(body))` on `Reverse(str)`
>    at `Mirror(cp,n)`, carrying the value as `GmOfLive(body, MirrorRegs(rfF...))` —
>    NOT `FreshBodyMatch` (which is forward-over-`body`, wrong for LB). So this lemma
>    dispatches into `LkReplayMatchesSpecLB`/`LBEngineLeaf`.
> 3. **`MatchedPosLA` widening** (MainTheorem:3159, currently `.Lookahead?`-only) →
>    `.Lookahead? || .Lookbehind?`. RIPPLES to ~10 `LiftSim.dfy` call sites (190,
>    2422, 3609, 10042, 11439, …) + the value/quant lifts' skip logic — the big-bang
>    trigger. Also make **`FreshBodyMatch`** (MainTheorem:3171) dispatch on
>    `capture_direction` (backward + `reverse_regex(body)` for LB), OR restate
>    `FLookLoopValueOk`/`FLookLoopQuantValueOk` (3184/3907) for LB against the reversed
>    fresh form `GmOfLive(RevRE(body), MirrorRegs(rfF))`.
> 4. **Value/quant lift LB branches** (`FLookLoopValueLift` else at MainTheorem:3848;
>    `FLookLoopQuantValueLift` LB branch 4204 — the QUANT branch ALREADY runs the
>    backward replay + WF + IH threading, a proven structural TEMPLATE, it just skips
>    the value): replace the capture-free stub with the backward frames (#1) +
>    `ReplayLidCapAgreeFreshLB` (#2) to establish the per-lid LB value.
> 5. **Fragment flip + the 4 ensures roots** (`LookBehindFragmentRE:541`/`Raw:566`;
>    `OE.LmOfInv`, `LmOfInvL3a`, `LookRowsFromTablesL3a`, `GateStaticsSweepRE`): drop
>    the `(la.Lookbehind? ==> CaptureFreeRE(body))` conjunct from their ensures.
> 6. **Gate pass + endpoint** (`LiftPreserveGatePassLk` LiftSim:4522, `L3aEndpointAssembly`
>    LiftSim:11589): replace the capture-free arm with a value-carrying `Lookbehind?`
>    arm wiring `LkReplayMatchesSpecLB`'s `GmAgreeOn(SwapGm(LkResult), GmOfLive(body,…))`.
>    Membership is swap-invariant, so gate coverage (`g in … ==> g in gm2`) needs no swap.
> 7. **`MainExtraction` rework** (MainTheorem:4843): its precondition `leaf.1 == GmOfLive`
>    is FORWARD-ONLY (for a LB group, spec leaf is ordered but `GmOfLive` is reversed —
>    they DIFFER by `SwapGm`). Change it to relate `NormalizeArr(f)` [item-0 swap active]
>    directly to `CapArrayOfLeaf(specLeaf)` through the per-group swap; the item-0
>    `GmOfCapArrayBridge` stays the forward bridge, a NEW lookbehind-aware bridge sits
>    beside it. `FirstLeafOrdered` (item 0) still gives the spec leaf's ordering.
> 8. **Oracle-column coverage gap**: `OracleColumnSpec` (OracleSpec:353) /
>    `OracleColumnCharacterized` (OracleDecomp:1477) only SPECIFY capture-free LB gates.
>    A capturing LB gate matches identically to its capture-free skeleton (matching is
>    capture-independent), so widen their `CaptureFreeRE` to `CapUnique` — but AUDIT
>    whether their proofs use capture-freeness beyond `CapUnique(reverse_regex(body))`.
>
> Verify each new frame standalone (`--filter-symbol=…`) before the #3 big-bang, which
> re-verifies `FLookLoopValueLift`/`QuantValueLift` (heavy — use `{:isolate_assertions}`)
> + the `LiftSim` `MatchedPosLA` consumers. No `.doo` rebuild needed unless a
> linden-reasoning file changes.

> **Session 12 (2026-08-11) — ITEM 4 (the backward value crux) is COMPLETE.**
> New verified file `linden-equiv/src/Equiv/LookBehindKeystone.dfy` (**769/0**),
> the sibling of the L3a keystone `LindenElkMain.LkReplayMatchesSpec`:
> - **`LkReplayMatchesSpecLB`** (module `LindenLookBehindKeystone`) — for a
>   positive LOOKBEHIND with a look-free plus-fragment body, the engine's BACKWARD
>   capture replay `raB` (over `compile_to_bytecode(reverse_regex(body))`) matches
>   the spec `LkResult` on the body's groups. **Ensures:** `raB.None? <==>
>   LkResult(TrLookaround(la), tlk, gmMain, inp).None?`, and on a match
>   `GmAgreeOn(SwapGm(LkResult(...).value), GmOfLive(body, MirrorRegs(rfF.caps,n),
>   MirrorRegs(rfF.looks,n), MirrorRegs(rfF.quants,n)), S)` where `rfF` is the
>   FRESH forward run of `compile_to_bytecode(RevRE(body))` over `Reverse(str)` at
>   `n-cp` (mirror of the backward replay via `BackwardReplayMirror`), `S =
>   DefGroups(Translate(body))`. The value tie is through the reversed-span mirror
>   `SwapGm` (item-0 `NormalizeArr` reconciles at `MainExtraction`); note membership
>   is swap-INVARIANT, so the gate-pass coverage (`g in ... ==> g in gm2`) needs no
>   swap. **Preconditions** (consumer discharges): body facts (`TransWf`,
>   `LookFreeRE`, `PlusFragmentRE`, `CapUnique`, `QuantUnique`), `GroupOkL(Translate
>   (body))`, `NoDupG(DefGroups(Translate(body)))`, `SizesOkRE(body,...)`, the
>   fresh-caps `RegsAgreeInside(cap, init_regs(ncap), CaptureRegs(body))`, `tlk ==
>   ComputeTr([Areg(Translate(body))], InpOfCp(str,cp), gmMain, Backward)`, and
>   `GmAgreeOn(gmMain, Empty, S)`. Consumer template: `LiftSim.dfy:4479` lookbehind
>   arm (currently the capture-free stub) — items #5/#6.
> - **Split for the solver:** `LBEngineLeaf` (engine half) + `LkReplayMatchesSpecLB`
>   (spec/value half), both `{:isolate_assertions}` — a monolithic version TIMED
>   OUT at 10min; isolating each VC + splitting the two fact-worlds made each
>   tractable (~90s/task). Supporting: `FConsumeCapsLE`/`FFindMatchCapsLE` (the
>   `VmCapsLE` forward invariant => `caps <= |str|`, feeds `GmOfLiveMirror`);
>   `RevREStaticOk` (the whole `StaticOkRE(qm', RevRE(body), ...)` with `looks:=
>   map[]` — `OracleOkSuffix` VACUOUS; `qm'.quants := M.QmOfRE(RevRE(body))` via
>   `QmOfREEntries`+`QmapOkFromEntries`, `LmapOk` via `AR.PlusFragmentLmapOk`);
>   `MirrorRegsAgreeInit`/`SwapGmAgree`/`CaptureRegsRevRE` bridges.
> - **Ensures well-formedness gotcha:** state the RevRE forward tree in the ensures
>   as `ComputeTr([Areg(RevL(Translate(body)))], SwapInput(InpOfCp(str,cp)), ...)`
>   NOT `Translate(RevRE(body))` — the latter needs `TransWf(RevRE(body))` which is
>   only a LEMMA (not derivable in ensures WF from the requires). Bridge in the
>   proof via `TranslateRevRE`+`InpOfCpSwap`.
> - **`.doo` note:** LookBehindKeystone.dfy is a linden-equiv file including
>   MainTheorem.dfy + LookBehindValue.dfy; no cross-package `.doo` rebuild needed
>   (the reasoning `.doo` bridge from session 11 is already in place). Verify with
>   the linden-equiv recipe + `--allow-warnings` (a pre-existing NestInv.dfy trigger
>   warning) + `--filter-symbol=LindenLookBehindKeystone`.
>
> **Remaining (items #1, #2, #3, #5, #6):** the fragment flip + the FLookLoop
> value-lift / gate-pass consumers that WIRE `LkReplayMatchesSpecLB` — see §3 below.
> They consume its `ensures`; the proof is done.

> **Session 11 (2026-08-11) — item 4 step 1 (the spec-side leaf-value crux) is
> DONE, hypothesis included.** Two new verified files in `linden-reasoning`:
> - `src/Equiv/TreeResMirror.dfy` (**19/0**) — `TreeResMirror`: folding the
>   backward body tree at `gm1` and the forward mirror tree at `MirrorGm(gm1,n)`
>   gives corresponding results (None-iff-None + on a match the winning leaf's
>   input is `SwapInput`-related and captures are `MirrorGm`-related, i.e. the
>   §2 decided range mirror). Plus `GMOpen/GMClose/GMResetMirror` (GMClose's own
>   min/max normalization IS `MirrorRange`) and the `MirrorGm`/`GmInBounds`/
>   `CloseDisc`/`OpenSubset` machinery.
> - `src/Equiv/CloseDiscEstablish.dfy` (**29/0**) — discharges `TreeResMirror`'s
>   `CloseDisc` hypothesis: `CloseDiscBody(rer, r, inp, gm, dir)` proves
>   `CloseDisc(ComputeTr(rer,[Areg(r)],inp,gm,dir), {})` for group-OK, unique-id
>   `r`. **The quantifier-stable invariant** (the campaign's old wall): relate
>   each `Areg` head's `DefGroups` to the pending CLOSES below it
>   (`HeadsFreshOfCloses`), never to other defs — a quantifier unfold pushes
>   `Areg`s (never `Aclose`s), so the close-set doesn't grow and the invariant
>   survives; it supplies exactly the freshness each `ComputeTree` case needs.
> - **Key simplification found:** `TreeRes` None-ness is group-map/input/dir-
>   independent (`Tree.ResGroupMapIndep`), so the None-iff-None half needs no
>   mirror; only the value tie (winning path) uses `MirrorGm`+`CloseDisc`.
>
> **Step 2 (engine-side GmOfLive commutation) also DONE.** New verified file:
> - `linden-equiv/src/Equiv/BackGmMirror.dfy` (**18/0**) — `GmOfLiveMirror`:
>   `GmOfLive(body, MirrorRegs(cap,n), look, quant) == RawMirrorGm(GmOfLive(body,
>   cap, look, quant), n)`, where `RawMirrorGm` is the RAW (reversed-span) range
>   mirror `Range(s,Some e) |-> Range(n-s, Some(n-e))` — `LiveRange`/`RangeFromArr`
>   read `start_reg`/`end_reg` positionally, so a closed lookbehind group reads
>   out reversed (the item-0 quirk). Built on `FilterCaptureMirror`/
>   `FilterResetMirror` (filter commutes with the mirror — it branches only on
>   clocks, which `MirrorRegs` keeps, and writes only `-1`). The ORDERED spec
>   mirror is `MirrorRange` = `Range(n-e, Some(n-s))`; the two differ by a
>   start/end swap for closed lookbehind-owned groups — reconciled by the widened
>   `NormalizeArr` (item 0) at `MainExtraction`.
>
> **RevRE bridge DONE** (item 4f, `GmOfLiveRevRE` in `BackGmMirror.dfy`, whole
> file **31/0**): `GmOfLive(RevRE(body),X)==GmOfLive(body,X)`. Proved via the
> SET characterization — `filter(r,a) == ApplyZero(ZeroSet(r), a)` (the filter
> only zeroes a clock-determined, value-INDEPENDENT set), and set union commutes,
> so `RevRE`'s `Re_con` reorder is a no-op (`ZeroSetCapRevRE`). (An earlier 2-array
> parametricity attempt TIMED OUT on disjunctive per-index quantifiers — use
> sets, not arrays, for "value-independent zero-set" facts.)
>
> **STEPS 1 AND 2 COMPLETE; STEP 3's VALUE CORE PROVED (item 4g).** The `.doo`
> bridge was rebuilt with `lem pack` (reasoning 382/0), so linden-equiv now sees
> the reasoning lemmas. New verified file `linden-equiv/src/Equiv/LookBehindValue.dfy`
> (**8/0**): `BackBodyGmTie` (tree+value core — `ComputeTrReverse` + `TreeResMirror`
> + `CloseDiscBody`), `RawMirrorMirrorSwap` (`RawMirrorGm(MirrorGm(X,n),n)==SwapGm(X)`,
> n cancels), `GmOfLiveClockIndep`, and **`BackBodyEngineTie`** which composes
> ALL proved pieces ⟹ `GmOfLive(body, MirrorRegs(rf.caps,n), MirrorRegs(rf.looks,n),
> MirrorRegs(rf.quants,n)) == SwapGm(spec backward leaf)`, taking
> `BackwardReplayMirror`'s mirror-regs relation and `ReplayCapIsBodyLeaf`@RevRE's
> value equality as HYPOTHESES.
>
> **ALL self-contained statics DONE (item 4i, LookBehindValue 16/0).** RevRE
> preservation lemmas for `StaticOkRE`: `CapUniqueRevRE`/`QuantUniqueRevRE` (via
> `CapIdsRevRE`/`QuantIdsRevRE`), `MaxGroupRevRE`/`MaxQuantRevRE` (⟹ `SizesOkRE`),
> `InpOfCpSwap`; plus pre-existing `OS.RevRELookFree`, `OS.RevREPlusFragment`,
> `SD.RevRETransWf`, `SD.TranslateRevRE`.
>
> **THE ORACLE-DISSOLVING BREAKTHROUGH:** `OracleOkSuffix` (LookLeaves:1204)
> quantifies over `qm.looks`. A look-free body has none, so use a **body-specific
> `qm'` with empty `looks`** (and `qm'.ov := MirrorView(ov)`) — then
> `OracleOkSuffix(rer, qm', ...)` is **VACUOUSLY TRUE**. The deep oracle transport
> disappears. (The engine's actual lookbehind uses the main `qm`, but the forward
> RevRE run needs `qm'.ov==MirrorView(ov)` anyway, so a fresh `qm'` is required
> regardless — and empty looks come free.)
>
> **Remaining keystone = (in a `MainTheorem.dfy`-including file, slow to iterate):**
> 1. Construct `qm'` for `RevRE(body)`: `quants` = `RevRE(body)`'s quant map,
>    `looks := map[]`, `ov := MirrorView(ov)`. Prove `QmapOk(RevRE(body),qm')` &
>    `LmapOk(RevRE(body),qm')` (look at `AR.QmapOk`/`LmapOk` + how the compiler
>    builds a QMap — `M.QmOfRE`/`OE.LmOf` may give a canonical constructor).
> 2. `StaticOkRE(qm', RevRE(body), compile(RevRE(body)), endl')`: fragment/uniques
>    from the item-4i lemmas; `NfaRepRE(RevRE(body),compile(RevRE(body)),0,endl')`
>    + `GetPcRE(code,endl')==Accept` + `|code|==endl'+1` + `StutterTameRE` from the
>    compiler-correctness family `NR.CompileNfaRepRE`(NfaRepRE:1438).
> 3. `OracleOkSuffix(rer,qm',InpOfCp(Reverse(str),n-cp))` — VACUOUS (empty looks).
> 4. Wire: `ReplayCapIsBodyLeaf`(MainTheorem:4363)@`(RevRE(body),Reverse(str),n-cp,
>    MirrorView(ov),SwapAnchorsCdns(cdns))` ⟹ `GmOfLive(RevRE(body),rf)==FirstLeaf(t_F)`;
>    `BackwardReplayMirror`(BackValue:117)@fresh-init ⟹ `capB=MirrorRegs(rf)`;
>    `InpOfCpSwap` for the input; `BackBodyEngineTie` ⟹ the value tie
>    `GmOfLive(body,capB)==SwapGm(spec leaf)`; then None-iff-None + `LkResult(
>    Lookbehind,LkDir=Backward)` fold (mirror `LkReplayMatchesSpec`'s final lines).
>    The existing call template is `LiftSim.dfy:4495` (lookahead); `T.Translate`
>    needs `TransWf(body)`.
>
> **`LkReplayMatchesSpecLB` signature** (mirror `LkReplayMatchesSpec`,
> MainTheorem.dfy:4479, `la.Lookahead?`→`la.Lookbehind?`): the engine replay is
> BACKWARD over `compile_to_bytecode(reverse_regex(body))`; `tlk` is the BACKWARD
> body tree `ComputeTr([Areg(Translate(body))], inp, gmMain, WP.Backward)`;
> `LkResult` uses `LkDir(Lookbehind)==Backward`. The value tie is stated through
> the RAW (reversed-span) mirror: `GmAgreeOn(LkResult(...).value,
> RawMirrorGm(GmOfLive(body, rf.caps, ...), n), S)` — because the engine's raw
> readout is reversed-span vs the ordered spec leaf; the `NormalizeArr` swap
> (item 0) reconciles at `MainExtraction`. **Proof deps to transport for the
> `ReplayCapIsBodyLeaf`@`(RevRE(body),Reverse(str),n-cp)` instantiation:** RevRE
> preserves `LookFreeRE`/sizes/`TransWf` (`RevRETransWf` exists; audit
> `LookFreeRE(RevRE)`), `StaticOkRE(qm', RevRE(body), compile(RevRE(body)),
> endl')`, `OracleOkSuffix` for `Reverse(str)` at `n-cp`, and the
> `InpOfCp(str,cp)`↔`SwapInput` alignment (`SD.InputAtSwap`; `PIV.InpOfCp` at
> :5544). **The `.doo` bridge (handoff §0) MUST be rebuilt before step-3 code in
> linden-equiv can see `TreeResMirror`/`CloseDiscBody`** — `deps/` is generated,
> not git-tracked.
>
> **The full step-3 value chain (traced this session):** engine backward caps
> `capB = MirrorRegs(rf_F,n)` (`BackwardReplayMirror`); `ReplayCapIsBodyLeaf`@RevRE
> ⟹ `GmOfLive(RevRE(body),rf_F) == FirstLeaf(t_F)` where `t_F` = forward tree of
> `Translate(RevRE(body))==RevL(Translate(body))`; `ComputeTrReverse` ⟹ `t_F`
> `TreeMirrorRel` `t_B` (backward tree of `Translate(body)`); `TreeResMirror` ⟹
> `FirstLeaf(t_F) == MirrorGm(TreeRes(t_B,Empty,inp_B,Backward), n)`. So the spec
> leaf `TreeRes(t_B,..,Backward) == MirrorGm(GmOfLive(RevRE(body),rf_F))` [ordered].
> Engine answer `GmOfLive(body, capB) = RawMirrorGm(GmOfLive(body,rf_F))
> = RawMirrorGm(GmOfLive(RevRE(body),rf_F))` [GmOfLiveMirror + RevRE bridge]
> = reversed-span of the ordered spec leaf ⟹ `NormalizeArr` swap closes it.
>
> Verify recipe (both files, linden-reasoning deps):
> `--filter-symbol=LindenTreeResMirror` / `--filter-symbol=LindenCloseDisc`.
> `CloseDiscEstablish.dfy` includes `TreeResMirror.dfy` includes `TreeMirror.dfy`.

**Goal:** extend `MainTheoremL3`/`ApiMatch.Supported` (L3a: capturing positive
lookaheads, DONE — see `L3_PROOF_MAP.md`) to also admit **captures inside
positive lookbehinds** — `(?<=(a))`, `(?<=(ab))c`, etc. — closing the last
capturing-lookaround gap before L4 (nesting).

**Branch:** `l3b-backward-value`, off `l3a-liftsim-scaffold`. Two commits so
far, both self-contained proof files, no existing file edited yet:

```
c01f9bf L3b item 4b: TreeMirror.dfy — the PRIORITY-AWARE tree-level reversal PROVEN
d2b2cb2 L3b item 4a: BackValue.dfy — the backward capture replay transported to a forward run
```

This is a monorepo (`Linden-Dafny`) — `linden-equiv/` and `linden-reasoning/`
share one git history/branch; `git log` from either subdirectory shows both
commits.

**Source doc:** `LOOKAROUND_CAMPAIGN.md` §4.5.1 lists the six work items in
dependency order. This handoff supersedes that outline where the two now
differ (item 4 turned out to split into an engine half and a spec half, and a
**new item 0** was discovered — see §2 below). The running narrative log (the
"why", session by session) is in the `linden-l3-campaign` memory
(`~/.claude/projects/-home-aaron-code/memory/linden-l3-campaign.md`,
**session 10** is the L3b entry — read that section first if you want the
blow-by-blow instead of this summary).

**Task list:** this session tracked the six §4.5.1 items as tasks #1–#6 (task
tool). #4 (the backward value crux) is `in_progress` — its engine half and
spec half are both proved; what remains is the assembly (§3 below). #1, #2,
#3, #5, #6 are still `pending` and untouched.

---

## 0. Verify recipes

**`linden-equiv/` files** (BackValue.dfy lives here):
```
cd linden-equiv
"$DAFNY" verify src/Equiv/<File>.dfy --standard-libraries \
  --library=deps/linden-engine-model.doo --library=deps/linden-engine.doo \
  --library=deps/linden-reasoning.doo --library=deps/linden-semantics-core.doo \
  --library=deps/linden-warblre.doo --library=deps/regex-engine.doo \
  --verification-time-limit=900 --filter-symbol=<Name>
```

**`linden-reasoning/` files** (TreeMirror.dfy lives here — smaller dep set):
```
cd linden-reasoning
"$DAFNY" verify src/Equiv/<File>.dfy --standard-libraries \
  --library=deps/linden-semantics-core.doo --library=deps/linden-warblre.doo \
  --library=deps/regex-engine.doo \
  --verification-time-limit=600 --filter-symbol=<Name>
```

`$DAFNY` = `~/.local/share/lemmata/toolchains/4.11.0/dafny/dafny` (4.11.0;
the PATH `dafny` is 4.10 and cannot load these `.doo`s).

**IMPORTANT — the dependency bridge.** `linden-equiv/deps/linden-reasoning.doo`
is a SNAPSHOT. If a `linden-reasoning` file changes (as it did here —
`TreeMirror.dfy` is new) and a `linden-equiv` proof needs to see it, rebuild
and copy:
```
cd linden-reasoning
"$DAFNY" build -t:lib dfyconfig.toml --no-verify
cp linden-reasoning-*.doo ../linden-equiv/deps/linden-reasoning.doo   # check the actual output name
```
`lem restore` reverts this — don't run it until the bridge is no longer
needed, or re-copy afterward. (Not yet done this session — `BackValue.dfy`
didn't need `TreeMirror.dfy` yet; the assembly lemma in §3 will.)

---

## 1. What's proved

### `linden-equiv/src/Equiv/BackValue.dfy` (5 verified, 0 errors)

The **engine** half: transports a lookbehind's backward capture replay to a
forward run, via `Mirror.dfy`'s existing state isomorphism.

| Lemma | Role |
|---|---|
| `SwapRevIsRevRE(r)` | For look-free `r`: `OBu.SwapAnchorsRegex(R.reverse_regex(r)) == SD.RevRE(r)` — the engine's own anchor-swap-of-reversal IS SpanDuality's `RevRE` (engine reversal + anchor swap combined). |
| `CompileToBytecodeSwap(r)` | `MIR.SwapAnchorsCode(CP.compile_to_bytecode(r)) == CP.compile_to_bytecode(OBu.SwapAnchorsRegex(r))` — `CompileSwap` capped at `[Accept]` instead of `[WriteOracle(lid)]` (the L2 form). |
| `FInitStateMirrorAt(c, str, cp, ...)` | The mirrored FInitState at an **arbitrary** `cp` (not just `init_cp`) — the capture replay anchors at the recorded gate position, unlike an oracle build which starts at position 0/`\|str\|`. |
| **`BackwardReplayMirror(body, str, cp, cap, lk, qt, ov, cdn, n)`** | **THE PAYOFF.** `FFindMatch(compile_to_bytecode(reverse_regex(body)), str, @cp, Backward)` mirrors `FFindMatch(compile_to_bytecode(SD.RevRE(body)), Reverse(str), @(n-cp), Forward)` — same match/no-match, winning thread's registers correspond **value-for-value** under `v |-> n-v` (`MirrorThread`/`MirrorRegs`). Works for ANY start registers (not just fresh/init), which item 3/4's assembly will need. |

**Key discovery:** `Mirror.dfy`'s `FFindMatchMirror` (already proved, L2 era)
ALREADY carries full register values through the isomorphism — its `ensures`
clause states `MirrorThread`/`MirrorRegs` equalities, not just match/no-match.
§4.5.4's flagged worry ("`Mirror` may need to STRENGTHEN its ensures with the
capture-register value correspondence") was unfounded. **Nothing in
`Mirror.dfy` changed or needs to.**

### `linden-reasoning/src/Equiv/TreeMirror.dfy` (6 verified, 0 errors)

The **spec** half — "the genuinely new proof" `LOOKAROUND_CAMPAIGN.md`
flagged as having no existing scaffolding.

| Lemma | Role |
|---|---|
| `GroupActionMirror(ga, gam)` | `Open`/`Close` equal; `Reset` payloads equal **as sets** (`RevL` permutes `DefGroups`, doesn't preserve seq order). |
| `TreeMirrorRel(t, tm)` | Backward tree `t` and forward tree `tm` correspond: same shape, same `Choice` order (**priority**), same `Read` chars, `AnchorPass` payloads related by `SwapAnchorL`, `GroupActionT` payloads by `GroupActionMirror`. No `LK`/`LKFail`/`ReadBackRef` cases (the fragment excludes them). |
| **`ComputeTreeReverse`/`ComputeTrReverse`** | **THE THEOREM.** For a `GroupOkActs` stack (Groups allowed, no lookarounds/backrefs — exactly an L3b lookbehind body after `Translate`): the backward `ComputeTree`/`ComputeTr` and the forward one over `RevActs(acts)`/`SwapInput(inp)` run out of fuel together and, when they complete, produce `TreeMirrorRel` trees — **at any pair of group maps**, including totally unrelated ones. |

**Why group maps can be unrelated:** a `GroupOkActs` tree never *reads* the
map to decide its shape (only `Backreference`, excluded by `GroupOkL`, would
do that) — this is the same fact `SpanDuality.TreeResSomeGmIndep`/
`ComputeTreeGroupOkGmIndep` already use. So `ComputeTreeReverse` needs no map
correspondence to *build* the two trees; the map correspondence is a
downstream question about *folding* leaves (§3, step 1).

**Proof shape:** fuel-parallel structural induction, case-for-case with
`SD.RevActs`. `SD.SeqListReverse` is the load-bearing alignment ("the spec
ALREADY reverses concatenation order when scanning backward" — exactly what
`RevL` does structurally). Every swap-layer primitive `TreeMirrorRel`
consumes was already banked in `SpanDuality.dfy` (`ReadCharSwap`,
`IsStrictSuffixSwap`, `AnchorSatisfiedSwap`, `RevLDefGroupsSet`,
`ActionsFuelReverse`) — this file assembles them at the tree level, which is
exactly what `SpanDuality.dfy`'s own "(4) CONCATENATION ORDER" status note
(written before L3 existed) predicted was "tractable" and left as the one
open assembly.

**Solver notes for anyone continuing this file:** `SD.RevActs` of a 2- or
3-element literal seq needs an explicit `assert SD.RevActs([...]) == [...]`
— Dafny won't unfold the sequence comprehension through the recursive calls
otherwise. The `GreedyChoice`/forced-copy cases need the reset-wrapped
`TreeMirrorRel` fact asserted by name (`GroupActionT(Reset(...), ...)`) right
after the two recursive calls, not left implicit — see the `Quantified` case
for the pattern.

---

## 2. THE FINDING THAT CHANGES THE PLAN — lookbehind capture spans are stored reversed, by design

Ran the engine's functional model directly (no proof, just execution — see
`/tmp/.../scratchpad/lbtest/lbtest.dfy` if you want to reproduce, or just
trust the corpus below):

```
(?<=(a))b     on "ab"   =>  [1, 2, 1, 0]     -- group 1 = (1, 0)
(?<=(ab))c    on "abc"  =>  [2, 3, 2, 0]     -- group 1 = (2, 0)
a(?=(b))      on "ab"   =>  [0, 1, 1, 2]     -- group 1 = (1, 2)  (forward, in order)
```

A capturing lookbehind's raw register bank holds the group's **end position
in the start slot and start position in the end slot** — the backward replay
writes `start_reg` first (bytecode order is fixed; only the scan direction
and `cp` reverse), so the register that's *conventionally* "start" ends up
holding the *numerically later* position.

This is not a bug and not new — `regex-engine/tests/engine/
OCamlBugRegressions.dfy`'s header says the expected arrays are the "RAW
outputs of the ORIGINAL OCaml RegElk engine ... INCLUDING register quirks
(**reversed lookbehind capture spans**, stale end registers)". It's
documented, pinned by cross-engine regression tests, and has always been
true — L1/L2 never noticed because neither admits capturing lookbehinds.

**Consequence for `MainTheoremL3b`.** The spec side normalizes: `GMClose`
(`Groups.dfy`) always produces `Range(startIdx, Some(endIdx))` with
`startIdx <= endIdx`, swapping if needed. `CapArrayOfLeaf` (`linden-reasoning/
Spec.dfy`) reads a `Range` in that already-ordered form. So:

- `PIV.GmOfLive`'s `RangeFromArr`/`LiveRange` (`PikeInvRE.dfy`), which read
  `CP.start_reg(gid)`/`CP.end_reg(gid)` **positionally, with no ordering
  fixup**, will — for a lookbehind-owned group — construct a `Range` with
  `startIdx > endIdx.value`. That is **not** what `GMClose` ever produces on
  the spec side.
- The **existing** `Normalize`/`NormalizeArr` (`linden-reasoning/Spec.dfy`)
  only absorbs the *stale-end-register* quirk (`arr[j-1] < 0 ==> -1` at odd
  indices) — nothing in it swaps a reversed pair back into order.
- So `MatcherSpec(raw, str, Normalize(FFullMatch(raw, str)))` — the exact
  statement `MainTheoremL3` (and hence `L3b`'s goal) proves — is **currently
  false** for any pattern with a capturing lookbehind, under today's
  `Normalize`.

**This is architecturally sanctioned, not a wrong turn.** `NormalizeArr` is
*declared* to be the quirk-absorption layer between the engine's raw output
convention and the spec's clean one; it already has one clause for exactly
this kind of purpose. It needs a second clause.

**The fix — new item 0, ahead of everything else in §4.5.1's numbered list:**
widen `NormalizeArr` with a per-group reversed-pair swap for lookbehind-owned
groups (`if arr[start] > arr[start+1] (and both >= 0) then swap`, gated
correctly against the existing stale-end-register clause — check the
interaction order). This is a no-op for every group NOT owned by a
lookbehind (forward pairs are already ordered), so it doesn't disturb
`MainTheorem`'s existing (L1/L2/L3a) proofs — but the equality lemma at
`MainExtraction` that currently reads `NormalizeArr`'s single clause will
need the new disjunct threaded through, and every internal value tie for a
lookbehind-owned group (the whole §3 chain below) must be stated
**orientation-aware**: the engine bank holds `(e, s)`, the spec leaf holds
`Range(s, Some(e))` — pick ONE canonical orientation for the intermediate
lemmas (recommend: state everything in spec orientation, i.e. carry the
"decided range mirror" below into `BackwardReplayMirror`'s consumers rather
than into `BackValue.dfy` itself, which is direction-agnostic and shouldn't
know about group semantics).

**The decided range mirror** (for the leaf-fold lemma in §3 step 1): under
the register mirror `v |-> n - v` (`Mirror.dfy`'s `MirrorRegs`, `n = |str|`),
an OPEN range `Range(s, None) |-> Range(n-s, None)`; a CLOSED range
`Range(s, Some(e)) |-> Range(n-e, Some(n-s))`. This is an involution. It
lines up with `GMClose` on both sides of the reversal **provided every
`Close` fires on a currently-OPEN-or-ABSENT group** (a closed-and-present
group breaks it — `GMClose` reads only `startIdx`, ignoring a prior `endIdx`,
so re-closing an already-closed group silently overwrites rather than
extending). Open-or-absent holds under unique group ids (an enclosing gid is
never in an inner quantifier's `DefGroups`, so no `Reset` can leave it
half-closed then re-close it), but the `TreeRes` induction that proves the
leaf-fold lemma needs this **threaded as an invariant**, not assumed — see
§3 step 1's `CloseDisc` sketch.

---

## 3. The remaining chain for item 4 (the backward value crux) — in order

This is what stands between "two transport lemmas proved" and item 4 (task
#4) being `completed`. Items 1–3, 5, 6 (tasks #1, #2, #3, #5, #6) are
essentially unblocked by this and can proceed in parallel once item 4's
final lemma (`LkReplayMatchesSpecLB`, step 3 below) has a stated signature —
they mostly consume its `ensures`, not its proof.

1. **`TreeResMirror`** — ✅ **DONE 2026-08-11** (`TreeResMirror.dfy` 19/0 +
   `CloseDiscEstablish.dfy` 29/0). Over `TreeMirrorRel`-related trees plus the
   `CloseDisc` invariant (`CloseDisc(t, O)`: `Close(g)` requires `g in O`,
   `Open(g)` adds, `Reset(gs)` removes; established for `ComputeTr` by
   `CloseDiscBody` via the quantifier-stable `HeadsFreshOfCloses` invariant —
   a linden-reasoning-local `NoDupG(DefGroups(·))` requires, discharged at the
   call site from `CapUnique`/`TA_NoDup`), proves: `TreeRes` mirror — `None` iff
   `None` (this half is gm-free by `ResGroupMapIndep`); `Some` implies the
   endpoint inputs `SwapInput`-related and the leaf group maps `MirrorGm`-related
   (the **decided range mirror** from §2), pointwise per group. The signature:
   `TreeResMirror(t, tm, gm1, inp, n, O)` with forward side at `MirrorGm(gm1,n)`
   over `SwapInput(inp)`. **NOTE for step 3:** `CloseDiscBody` is stated for a
   single-`Areg` fresh stack (`[Areg(r)]`, empty pending closes) — the body
   replay's shape; if the assembly folds a different stack shape, generalize via
   the already-proved `CloseDiscComputeTr`(any `StackInv` stack).

2. **`GmOfLive` commutation** (linden-equiv, likely `PikeInvRE.dfy` or a new
   small file): `PIV.GmOfLive(body, MirrorRegs(cap, n), ...)` vs
   `PIV.GmOfLive(SD.RevRE(body)-as-engine-regex, cap, ...)` — `filter_reset`
   only reads **clocks** (`a_clk`) to decide presence/reset, and `MirrorRegs`
   only remaps `a_cp` (see `Mirror.dfy:513`, `MirrorRegs` leaves clocks
   alone) — so the filter's *shape* (which gids survive) should transport for
   free per-gid; what needs an actual argument is that `RangeFromArr`'s
   readout after filtering matches the decided range mirror once you unfold
   `start_reg`/`end_reg` swap under `Mirror`. This is the piece that
   reconciles the ENGINE-side value with the register mirror from
   `BackValue.dfy`, so the assembly in step 3 can hand it to
   `TreeResMirror`'s (spec-side) range mirror and get equality, not just
   correspondence-up-to-swap.

3. **`LkReplayMatchesSpecLB`** (linden-equiv `MainTheorem.dfy`, sibling to
   the L3a keystone `LkReplayMatchesSpec` at :4479) — the assembly:
   - `BackValue.BackwardReplayMirror` (engine registers/match, done) at
     `(body, str, cp, cap, lk, qt, ov, cdns, n=|str|)`;
   - `MainTheorem.ReplayCapIsBodyLeaf` (L3a, already proved, direction-
     generic per its own doc) instantiated at `(SD.RevRE(body), Reverse(str),
     n-cp)` — needs the **statics** to transport: `RevRETransWf`
     (linden-reasoning, exists), `NR.Reverse*` family (`ReversePlusFragmentRE`
     etc., `NfaRepRE.dfy`, exist for L1's `reverse_regex` — audit whether they
     also hold for `SD.RevRE`/`OBu.SwapAnchorsRegex(reverse_regex(·))`, since
     `SwapRevIsRevRE` only proves the two ARE equal for look-free bodies, it
     doesn't reprove the fragment facts under the new name);
   - `SD.TranslateRevRE` (linden-reasoning, exists) to move `T.Translate` of
     the reversed/swapped body to `RevL(T.Translate(body))` on the spec side;
   - steps 1–2 above to fold `TreeResMirror`'s leaf correspondence back
     through `Empty -> gmMain` (the L3a keystone's `ComputeTrGmIndepLk`-style
     transfer is direction-generic already per its own comment — confirm,
     don't re-derive) and the `LkResult(Backward)` fold (`LS.LkResult` at
     `LkDir(lk) == Backward`, mirroring the L3a keystone's final `assert
     L.Positivity(...) && L.LkDir(...) == WP.Forward` line but for
     `Lookbehind`).
   - **Ensures shape to aim for** (mirror `LkReplayMatchesSpec`'s signature,
     `la.Lookbehind?` instead of `la.Lookahead?`, and note the value tie is
     stated through the §2 range mirror rather than raw equality on
     `CaptureRegs(body)`):
     ```
     (ra.None? <==> LS.LkResult(T.TrLookaround(la), tlk, gmMain, inp).None?)
     && (ra.Some? ==> ... GmAgreeOn(..., <range-mirrored version of
          PIV.GmOfLive(body, ra.value.capture_regs, ...)>, S))
     ```

Once `LkReplayMatchesSpecLB` exists with that shape, task #4 is `completed`
and the remaining tasks are:

- **#1** (fragment flip): `NfaRepRE.LookBehindFragmentRE`'s `Re_lookaround`
  clause (`:532`, currently `(la.Lookahead? || CaptureFreeRE(r1)) &&
  LookFreeRE(r1) && PlusFragmentRE(r1)`) becomes `(la.Lookahead? ||
  la.Lookbehind? || CaptureFreeRE(r1)) && ...` — plus the `Raw` counterpart
  (`:563`) and the item-0 `NormalizeArr` widening from §2, which is really
  part of this item's "flip" since it's a fragment-predicate-adjacent
  spec change.
- **#2** (`FreshBodyMatch`/`MatchedPosLA` direction dispatch,
  `MainTheorem.dfy:3076–3096`): `MatchedPosLA` already tests
  `AI.capture_type(...)` — only its extra `.Lookahead?` conjunct
  (`:3079`) needs to drop (or become `.Lookahead? || .Lookbehind?`).
  `FreshBodyMatch` hard-codes `LAnc.Forward` (`:3095`) and needs a
  `capture_direction`-dispatched twin using `LkReplayMatchesSpecLB`'s
  bytecode/cp convention.
- **#3** (backward bisim wrappers): `CM.FFindMatchCapRel`/`ThreadRel` are
  already direction-generic per the campaign doc — audit which
  `ReplayLidCapAgreeFresh`-style wrapper (`MainTheorem.dfy` — the ones
  called at `:3665` in the existing Lookahead branch) needs a literal
  Backward-instantiated twin vs. just widening its `dir` parameter.
- **#5** (value lifts): `MainTheorem.dfy:3765–3816` is the CURRENT
  capture-free-identity lookbehind branch inside `FLookLoopValueLift` —
  replace with the real value case using #2–#4, following the `Lookahead?`
  branch immediately above (`:3648–3764`) as the induction skeleton (same
  shape: replay, frame, IH-at-suffix, assemble). `FLookLoopQuantValueLift`
  (session 8b, `MainTheorem.dfy`) needs the mirror treatment for the quant
  bank.
- **#6** (gate + endpoint): `LiftSim.dfy`'s `LiftPreserveGatePassLk`
  (`:4200`) lookbehind half currently routes through
  `LkResultAgreeOutside` over the empty set (capture-free assumption,
  `L3_PROOF_MAP.md` §"GATEPASS DESIGN FINDING" case (b)) — becomes
  value-carrying via #4's keystone, following case (a)'s (Lookahead)
  wiring (`ThreadRepLkStepCheckOracle`) as the template. The endpoint's
  per-g owner dispatch (`InsidePresentResBridge`/`L3aValueBridge`,
  `LiftSim.dfy:10353`/`3956`) gains a `Lookbehind?` arm parallel to the
  existing `Lookahead?` one.

---

## 4. Quick-reference: what NOT to re-derive

- Mirror.dfy's state isomorphism (register values, priority, view/oracle
  mirror) — proved, direction-agnostic, unchanged this session.
- `SpanDuality.dfy`'s swap-layer primitives (`ReadCharSwap`,
  `IsStrictSuffixSwap`, `AnchorSatisfiedSwap`, `SeqListReverse`,
  `RevLDefGroupsSet`, `ActionsFuelReverse`, `RevRE`/`TranslateRevRE`,
  `GroupOkL`/`GroupOkActs`) — all exist, all consumed by `TreeMirror.dfy`
  as-is, none needed strengthening.
- L3a's `ReplayCapIsBodyLeaf`, `ComputeTrGmIndepLk`,
  `CM.FFindMatchCapRel`/`ThreadRel` — direction-generic per their own
  documentation; the job is instantiating/dispatching them, not reproving.
- The oracle side of lookbehinds (L1) is untouched by any of this — L3b is
  purely about the CAPTURE-RECONSTRUCTION pass, which runs after the
  (already-correct) oracle build.
