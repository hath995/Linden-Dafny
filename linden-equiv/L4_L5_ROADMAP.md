# L4 / L5 Roadmap (2026-08-03; L4 VALIDATED 2026-08-13)

## 2026-08-13 — L4 investigation: roadmap validated against post-L3b code (2 agents + recon)

**Status update: "L5" in this doc (capturing lookbehinds) IS DONE — it's the L3b now merged
to main (whole package green).** So L4 (nesting) is next, and it starts from a STRONGER base than
this doc assumed: the keystone is already direction-parametric (`LkReplayMatchesSpec` +
`LkReplayMatchesSpecLB`), so W4 generalizes an already-2-param keystone once.

Findings (file:line evidence in the agent transcripts):

- **W1 backbone — SOLID & provable.** `annotate_regex` (regex-engine `Regex.dfy:219-221`) gives
  the enclosing look lid `l` and annotates its body starting at `l+1`, so **inner lids are
  STRICTLY GREATER than their enclosing lid** (pre-order DFS). Build sweeps high→low
  (`FBuildLids`, inner-first), FLookLoop ascends 0→maxlook (outer-first reconstruct). The engine
  ordering is exactly right for nesting. [DOC BUG to fix: `FBuildLids`'s comment
  `Interpreter.dfy:521-524` says nested looks "get lower ids" — WRONG, they get HIGHER ids; the
  high→low build order is what's correct. Don't trust that comment.]
- **W2 flat→forest — CONFIRMED needed.** `LookBodiesCapsDisjoint` (NestInv:4028; distinct lids ⇒
  disjoint CapIds) is genuinely FALSE under nesting (inner CapIds ⊂ outer). Becomes a containment
  forest; owner = innermost lid; `GmtTieInside` owner existential → innermost. `CapIdsInLooks`
  (PikeInvRE:4016) already collects nested captures. Wide but mechanical — [M].
- **W4 keystone replay-entry — MECHANICAL, NOT A RISK (de-risked from L).** The register-value-
  BLIND bisimulation `FAdvanceEpsilonRel` (ClockMono.dfy:526) ALREADY proves the
  `CheckOracle`/`NegCheckOracle`/`WriteOracle` cases over ARBITRARY bytecode with NO look-free
  precondition; `ThreadRel` leaves look banks unconstrained (engine never reads registers for
  control; dedup keys on `(pc, exit_bool)`). `ReplayCapAgreeFresh` has no look-free requirement —
  only the SPEC-side `ReplayCapIsBodyLeaf`/`BodyTreeAtCp` does. So W4's real work is the SPEC-half
  depth induction ("keystone at depth k IS a lift at depth k-1"), reusing `LiftFindMatch`
  depth-indexed — the engine half is free.
- **W3 oracle build correctness — THE CRUX, confirmed campaign-sized (L, up from M).** The
  oracle-build layer is ARCHITECTURALLY oracle-blind: `LidBuildOk` (OracleBuild:158) REQUIRES
  `NoOracleReads` (no gate in the build); the reachability model `ReachF`/`ReachesWrite`/`EpsEdge`
  (OracleReach:51-91) has NO oracle-view arg and models a gate as a DEAD END; the completeness
  backbone `AdvanceOvIndep` (OracleSweep:241) proves each column is a function of `(bytecode,str)`
  ALONE — the exact column-independence nesting destroys. `remove_capture` KEEPS inner lookaround
  nodes (Regex.dfy:275), so the inner gate genuinely reaches the build bytecode. To fix: (1)
  re-parameterize `ReachF`/`EpsEdge`/`ReachesWrite` on a PARTIAL oracle view + real gate edges
  (semantics at Interpreter.dfy:315-325); (2) make `LidReaches`/`FBuildLidsCharacterized`
  inductive over the high→low order (column k = reachable writes against already-built columns >k)
  + a new "reads only columns >k, stable" frame; (3) weaken `AdvanceOvIndep`/`FindMatchOvIndep`
  from independence to "agrees on columns >k"; (4) add a gate rule to `LidBuildOk` (every
  `CheckOracle(j)` in column k has j>k) + generalize `CompileToWriteClassified`/`NoOracleInstrRE`
  from `LookFreeRE` to `LookIds(body) ⊆ {j>lid}`. **This is the single biggest L4 piece.**

**Prerequisites status:** #1 L3 green — DONE (merged). #2 decompose `ActionsTreeRepFRE` — NOT done
(still a ~650-line `{:isolate_assertions}` monolith, ActionsTreeRepRE.dfy:177, the bulk of that
file's 5276 VCs; the affordability gate). #3 `lem pack` 10-min wall — NOT fixed (hit it 2026-08-13).

**Net L4 sizing: L (full campaign), unchanged.** But the risk profile sharpened: W4 is FREE
(bisimulation already generic + L3b keystone already 2-param), and W3 (the oracle sweep) is the
confirmed crux — a model rebuild, not a hypothesis relaxation. Recommended first move: the W3
oracle-view re-parameterization scouting (build the partial-view reachability model + gate edges
standalone), in parallel with the ActionsTreeRepFRE decomposition (engineering gate). W1/W2 are
cheap groundwork that can start immediately.

## 2026-08-13 — L4 EXECUTION STARTED (branch `l4-nesting`)

**W1 DONE (commits 13a732e, 0449a40, 0a4fa75) — the depth vocabulary + lid-order backbone,
all purely additive, verified green.**
- `LookTables.dfy`: `LidsWellNested` (in every lookaround node the body's lids are STRICTLY
  GREATER than the enclosing lid — the induction backbone) + `AnnotateLidsWellNested` +
  `SpecRegexLidsWellNested`. Strengthens the flat `AnnotateLookUnique` range fact. LookTables 15/0.
- `NfaRepRE.dfy`: `NestDepth` (W4's decreases measure); `NestedFragmentRE`/`NestedFragmentRaw`
  (the L4 fragment = LookBehindFragment with the lookaround case's `LookFreeRE(body)` replaced by
  a recursive `NestedFragmentRE(body)`); backward-compat embeddings `LookBehindFragmentIsNestedRE`/
  `…Raw` + helpers (every currently-`Supported` input stays supported at L4); annotate bridge
  `AnnotateNestedFragment`/`SpecRegexNestedFragment`. NfaRepRE 1337/0.
- The eventual gate relaxation site is `LookBehindFragmentRE` at `NfaRepRE:543` (drop
  `LookFreeRE(r1)`) — deferred to W6 (wire nested end-to-end + whole-package sweep).

### W3 implementation sketch (scouted 2026-08-13; the CRUX blueprint)

Current anchors re-verified (slight line drift from the earlier snapshot):
`EpsEdge`=OracleReach.dfy:51, `ReachF`(least)=:76, `ReachesWrite`=:88, `SweepCharacterization`=:1042;
`AdvanceOvIndep`=OracleSweep.dfy:241, `FindMatchOvIndep`=:327, `WritesOnlyLid`=:62,
`NoOracleReads`=:49; `LidBuildOk`=OracleBuild.dfy:158, `LidReaches`(opaque)=:179,
`FBuildLidsCharacterized`=:388, `FBuildOracleCorrect`=:530; `CompileToWriteClassified`=NfaRepRE:2372,
`NoOracleInstrRE`=NfaRepRE:1995; interpreter gate semantics = Interpreter.dfy:315-325.

- **Gate = dead end CONFIRMED.** `EpsEdge` matches only Jmp/Fork/SetRegisterToCP/SetQuantToClock/
  BeginLoop/EndLoop/AnchorAssertion; `CheckOracle`/`NegCheckOracle`/`WriteOracle`/`CheckNullable`/
  `Consume` all fall to `case _ => false` — a config on a gate has ZERO outgoing edges. Nesting
  breaks this: the real interpreter advances past `CheckOracle(l)` to pc+1 WHEN
  `view_get_oracle(ov,cp,l)`, so the blind model undercounts reachable configs in nested build code.
- **`LidBuildOk` is stronger than "NoOracleReads" alone:** body is
  `bc==[] || (NoOracleReads(bc) && NoCheckNullable(bc) && WritesOnlyLid(bc,i) && NoAccept(bc))`.
  L4 form: DROP `NoOracleReads(bc)`, replace with `AllGatesAbove(bc,i)` (every `CheckOracle(l)`/
  `NegCheckOracle(l)` in `bc` has `l>i`), keep the other three.
- **`AdvanceOvIndep`/`FindMatchOvIndep` HAVE NO EXTERNAL CALLERS** (the big de-risker). They are a
  self-contained, un-wired pair; the §6.2 theorem routes column-independence through
  `FindMatchOracleFrame` + `SweepCharacterization` instead. So weakening them from whole-view
  `SameShape(ov1,ov2)` to `SameShape ∧ AgreeAbove(ov1,ov2,k)` (agree on columns >k;
  `AgreeAbove(a,b,k):=∀cp,l:: l>k ==> CellAgree(a,b,cp,l)`) has near-zero downstream churn — the
  work is to NEWLY WIRE the weakened form into `FBuildLidsCharacterized`. Under the weakening the
  two `assert false` gate cases (OracleSweep.dfy:285-290,308-310) become real recursive cases that
  thread `AgreeAbove`; `LidsWellNested` (W1) is what guarantees every gate reads some `l>k`.
- **MIGRATION STRATEGY (keeps existing chain untouched):** add partial-view variants
  `EpsEdgeV(c,str,ov,cp,pc,eb,pc2,eb2)` (= `EpsEdge` plus two gate cases:
  `CheckOracle(l) => view_get_oracle(ov,cp,l) && pc2==pc+1 && eb2==eb`, `NegCheckOracle(l) =>
  !view_get_oracle(ov,cp,l) && …`), `ReachFV`, `ReachesWriteV`. Prove the ERASURE EQUIVALENCE
  `NoOracleReads(c) ==> (ReachFV(c,str,ov,…) <==> ReachF(c,str,…))` for all `ov` (the gate cases are
  vacuous when gate-free) — then the entire existing OracleReach/OracleBridge/OracleDecomp chain is
  the ov-erased specialization, and ONLY nested-gate code paths need the new argument. This is a
  clean ADDITIVE first W3 brick (new defs + one equivalence lemma; touches no existing proof).
- **Blast radius if `ReachF`→`ReachFV` migrates (118 refs):** OracleBridge.dfy 61 (heaviest —
  `ReachFEpsIntro`:234/`ReachFConsumeIntro`:244 are the highest-fanout primitives), OracleDecomp.dfy 7,
  Mirror.dfy 1; plus OracleReach's own soundness (`AdvanceReachSound`:125/`FindMatchReachSound`:248)
  and completeness (`ClosureInv`:314/`AdvanceReachComplete`:543/`FindMatchReachComplete`:909) chains.
  `LidBuildOk` has 10 uses, ALL in OracleBuild.dfy (`LookTablesLidBuildOk`:235, `AllLidsBuildOk`:302,
  `FBuildLidsCharacterized`:389, `FBuildOracleCorrect`:559). The erasure-equivalence strategy means
  most of these stay on the ov-erased `ReachF` and never see `ov`.

**W2 classification DONE additively (commits bc28b5c, 04422bb) — the containment forest.**
`NestInv.dfy` now has, all requiring only `CapUnique && LookUnique` (fragment-INDEPENDENT, so no
existing consumer touched): `LookBodiesCapsDisjointOrNested` (distinct lids ⇒ body-caps DISJOINT or
one NESTED-⊆-other — the trichotomy `LookBodiesCapsDisjoint` couldn't state, since it forced
look-free bodies via `assert false`); `InnermostLookOwnerExists` (every nested capture g has an
innermost owner whose body holds g DIRECTLY); `LookBodyCompose` (LookBodyOfRE composes through
nesting); `InnermostOwnerMinimal` (that owner is subset-minimal). Together: "owner-of-g = innermost
lid whose body contains g" is now well-defined + subset-minimal. NestInv 149/0. The consumer
rewiring — `GmtTieInside`'s flat owner existential → innermost, and `LmOfBodiesDisjoint`
(MainTheorem:5461) → the forest — is W6 (changes existing lemmas, wants the widened fragment live).

**W3 bricks 1–3 DONE (commits d8d993d, 011f60c, 76fa0c2) — all purely additive.**
- Brick 1 (OracleReach 43/0): `EpsEdgeV`/`ReachFV`/`ReachesWriteV` (blind model + `ov` + real gate
  edges) and the erasure `EpsEdgeVErasure`/`ReachFVErasureFwd`/`Bwd`/`ReachesWriteVErasure` (on
  `NoOracleReads` code the V-model collapses to the blind model for every view; paired least-lemma
  inductions).
- Brick 2 (OracleSweep 25/0): `AllGatesAbove(c,k)` (generalizes `NoOracleReads`: gates read >k),
  `AgreeAbove(a,b,k)`, `AgreeAboveMonotone`, and the crux `GateReadAgrees` (AllGatesAbove +
  AgreeAbove ⇒ both views answer a gate identically), plus `NoOracleReadsAllGatesAbove`.
- Brick 3 (OracleSweep 29/0): `AdvanceOvIndepAbove`/`FindMatchOvIndepAbove` — the register-blind
  independence step now HANDLES GATES. `NoOracleReads` swapped for `AllGatesAbove(c,k) &&
  WritesOnlyLid(c,k)` + an `AgreeAbove(ov1,ov2,k)` premise; the CheckOracle/NegCheckOracle cases
  (formerly `assert false`) are real via `GateReadAgrees` (both runs branch in lockstep); the
  WriteOracle case preserves `AgreeAbove(k)` (writes hit column k, not above). `ensures
  AgreeAbove(ov1',ov2',k)` self-threads. Originals untouched.

**NEXT: W3 brick 4 (the assembly) — wire `AdvanceOvIndepAbove`/`FindMatchOvIndepAbove` into the
build-correctness proof.** (a) generalize `CompileToWriteClassified`/`NoOracleInstrRE` (NfaRepRE)
from `LookFreeRE` to `LidsWellNested`-backed `AllGatesAbove(bc, lid)`; (b) drop `NoOracleReads` from
`LidBuildOk` (OracleBuild:158), replace with `AllGatesAbove(bc, i)`; (c) rework
`FBuildLidsCharacterized` (OracleBuild:388) as a high→low induction — column k built against
already-correct columns >k, feeding `AdvanceOvIndepAbove` with `AgreeAbove(_, _, k)`. This DOES
iterate against OracleBuild/NfaRepRE compile lemmas; it is the remaining crux assembly.

**W3 brick 4 OUTCOME (commits 0785d73, 7136d47): 4a+4b DONE, 4c groundwork done, 4c-full BLOCKED
on TWO walls.** 4a = `GatesAboveInstrRE`/`GatesAboveClassified` (compile gate-classification). 4b =
`LidBuildOkAbove` (AllGatesAbove replaces NoOracleReads) + `AllLidsBuildOkAbove` establisher. 4c
groundwork = the V-model reconciliation layer + the nested-correctness THEOREM SHAPES
(`LidReachesV`, `LidReachesVErasure`, `FBuildLidsCharacterizedV`, `FBuildOracleCorrectV`) all verified
on the depth-1 fragment (OracleBuild 54/0). The full gated high→low induction is BLOCKED on:
(1) a missing `SweepCharacterizationV` — a GATE-FUL V-model sweep characterization (for
`AllGatesAbove` code, `FFindMatch` writes exactly the `ReachesWriteV` cells). `FindMatchOvIndepAbove`
proves view-INDEPENDENCE, not WHERE writes land; `SweepCharacterization` is `NoOracleReads`-only. This
is genuine heavy new work: re-derive OracleReach soundness (`FindMatchReachSound`) + completeness
(`ClosureInv`/`AdvanceReachComplete`) over `ReachFV`/`EpsEdgeV` with the two real gate edges.
(2) the SAME depth-1 wall as the keystone — the compile→`NfaRepRE` correspondence
(`CompileNfaRepRE`/`FreshCorrectRE`/`CompileToWriteRep`) still requires `LookBehindFragmentRE`, so no
nested regex flows through `FFullCompilation` with a structural proof yet.

**⚠ CORRECTION to the re-pricing below:** the oracle-build side is NOT fully "unaffected". Its MODEL
layer (ReachFV, AdvanceOvIndepAbove, gate-classification, the V-model theorem shapes) generalizes
cleanly and is DONE — but its compile-CORRESPONDENCE (`CompileNfaRepRE`) hits the SAME depth-1
`LookBehindFragmentRE` wall as the keystone's `StaticOkRE`. So the wall is the ONE central blocker for
BOTH halves of depth-k: generalize the `LookBehindFragmentRE`-gated static/correspondence stack to
`NestedFragmentRE`, PLUS build `SweepCharacterizationV`. (Pricing scout in flight.)

**W4 ENGINE HALF VALIDATED — CONFIRMED FREE (scout 2026-08-13, read-only).** The register-blind
bisimulation is genuinely gate-agnostic; every look-free hypothesis in the keystone chain lives on
the SPEC side. Evidence: `FAdvanceEpsilonRel` (ClockMono.dfy:526) requires only a processed-size
cond + `VmRel` over ARBITRARY `c: RB.code`, and PROVES the CheckOracle/NegCheckOracle/WriteOracle
cases by branching on the oracle + recursing (ClockMono.dfy:590–607, no `assert false`); `ThreadRel`
(ClockMono.dfy:502–506) keys on `pc + exit_allowed` and never mentions `look_regs`;
`ReplayCapAgreeFresh` (MainTheorem.dfy:5134) has no look-free/nesting precondition; the arbitrary-
code lift half exists as `LiftFindMatchC` (LiftSim.dfy:11147, no `LookFreeRE` — already handles gates
via LiftInv/GateStaticsOk/LookTables). [Naming: roadmap's `LiftFindMatch` is superseded by
`LiftFindMatchC`; the bisimulation family `FAdvanceEpsilonRel`/`FConsumeRel`/`FFindMatchCapRel`/
`VmRel`/`ThreadRel` is clean, though ClockMono ALSO has two capture-classification helpers
`CaptureBytecodeClassified{,Outside}` (1094/1118) that DO require `LookBehindFragmentRE` — not part
of the bisimulation.]

**W4 SPEC-HALF TO-DO (the real work — generalize these `LookFreeRE`/depth-1 preconditions to
`NestedFragmentRE`/depth-k, decreasing on `NestDepth`):**
1. `BodyTreeAtCp` (MainTheorem.dfy:2888, `requires LookFreeRE(body)` @2899) — THE crux: builds the
   checked tree as `LkConfinedTree(t, {})` (empty inside-look set) via `TranslateNoLkBr`+
   `ComputeTrLkConfined(...,{})`; at depth k the body tree has real `LK` nodes, so the `{}`-
   confinement must be replaced by the depth-(k−1) keystone. (Its engine callee `FindMatchBodyAtCp`
   @2834 is already look-free-free.)
2. `ReplayCapIsBodyLeaf` (MainTheorem.dfy:5210 @5220) — inherits from BodyTreeAtCp.
3. `LkReplayMatchesSpec` (forward keystone, MainTheorem.dfy:5326 @5337).
4. `LkReplayMatchesSpecLB` (backward keystone, LookBehindKeystone.dfy:395 @400,
   `LookFreeRE && PlusFragmentRE`).
5. `ReplayLidCapQuantAgreeFresh` (quant companion, MainTheorem.dfy:5088 @5091).

**W4 SHARPENED RISK:** the spec half is NOT merely "re-parametrize the keystone." The hard obstacle
is `TreeResGmFrame` (MainTheorem.dfy:5287, `requires EL.NoLKTree(t)` @5289): the group-map-
independence argument for own-group captures currently holds ONLY for look-FREE trees. At depth>0
`tlk` contains `LK` nodes, which DO read `gm`, so this gm-frame must be RE-DERIVED (not re-
parametrized) for trees with lookaround nodes. This is genuine spec-side proof work the "engine is
free" headline understates. Scaffolding ready: `NestedFragmentRE`/`NestDepth` + the embeddings
(NfaRepRE) from W1.

**W4 spec-half BRICK 1 DONE (commit 6ad4742) — the sharpened risk RESOLVED.** `TreeResGmFrameLk`
(MainTheorem.dfy, after TreeResGmFrame) is the gm-frame GENERALIZED to LK-node trees, under
`CE.LkConfinedTree(t, S)` instead of `NoLKTree(t)`. The move that cracks it: a confined look body is
`GmConfinedTree(_, S)` ⇒ LK-FREE (`GmConfinedNoLK`), so the ORIGINAL `TreeResGmFrame` discharges each
look body and only the CONTINUATIONS recurse — the depth-1 gm-frame lifts through exactly ONE layer
of gates, which is one step of the keystone's depth induction. Filter-verified 2/0 (full-file
MainTheorem sweep deferred — additive, no existing symbol touched). NEXT W4 spec-half bricks (the
keystone depth induction proper, now UNBLOCKED — they can consume `TreeResGmFrameLk` where they used
`TreeResGmFrame`): generalize `BodyTreeAtCp` (2888, the `{}`-confinement → depth-(k−1) keystone),
then `ReplayCapIsBodyLeaf`, `LkReplayMatchesSpec`(/`LB`), `ReplayLidCapQuantAgreeFresh`, inducting on
`NestDepth`.

**W4 spec-half BRICKS 2-3 DONE + a CAMPAIGN RE-PRICING (commit ebfab62).** Additive: `TreeResGmFrameRec`
(the gm-frame for LK trees generalized to ARBITRARY depth — drops `LkConfinedTree` entirely, since
`TreeRes` control flow never branches on `gm`, so each LK body recurses on a strict subterm;
SUPERSEDES `TreeResGmFrameLk`), `BodyTreeAtCpLk`/`ReplayCapIsBodyLeafLk` (`BodyTreeAtCp`/
`ReplayCapIsBodyLeaf` minus `LookFreeRE`, admitting CAPTURING depth-1 looks, confined via
`S = LL.LkBodyGroups(Translate(body))`, conclusion `GmAgreeOutside(_,_,S)`), `LookBehindFragmentDepth1`.

**⚠ THE RE-PRICING — "engine half is FREE" was HALF-RIGHT.** The scout validated the runtime
BISIMULATION (`FAdvanceEpsilonRel`) is gate-agnostic — TRUE. But the STATIC compilation/well-formedness
stack is DEPTH-1-CAPPED, and the keystone RETAINS it: `BodyTreeAtCp`'s (undroppable) `PSM.StaticOkRE`
DEFINITIONALLY embeds `NR.LookBehindFragmentRE(body)` (PikeSimRE.dfy:99) ⇒ `NestDepth(body) <= 1`
(machine-checked: `LookBehindFragmentDepth1`). Same cap in `CE.GmConfinedTree` (bans LK nodes),
`EL.PikeLkRegex`/`PikeLkActions`, `LL.ComputeTrLkConfined`, `ATR.ActionsTreeRepRE`, and `PikeInvFullRE`.
So the depth-k VALUE/keystone side is blocked NOT on the spec gm-frame (that's now done, arbitrary
depth) but on generalizing this whole ENGINE-STATIC stack `LookBehindFragmentRE → NestedFragmentRE` —
a large sub-campaign the original roadmap under-priced as "proof-mirrors-design, zero engine changes".
The `*Lk` bricks are correctly scoped to the depth-1 capturing fragment the static stack supports
today; they are additive scaffolding shaped for the eventual depth-k lift, not the lift itself.
**Net: L4's VALUE side is re-priced from L to L+ (adds the engine-static-stack generalization as a
prerequisite front). The ORACLE-BUILD side (W1–W3) is unaffected — it generalizes independently.**

### L5+ ladder pricing (validated 2026-08-13; corrects §3's one-paragraph sketch)

The `Supported` boundary today: `Supported(p) == NR.LookBehindFragmentRaw(p) && T.Latin1Wf(p)`
(ApiMatch.dfy:54-56). Beyond nesting (L4), it excludes: captures in NEGATIVE looks, nullable-bodied
`+`/`{n,}`, non-Latin-1, backreferences (by TYPE), and the flags (pinned off via `TheRer` =
`RER(false,false,false,…)`, Spec.dfy:94-96). Pricing the closing ladder against current code:

- **`ignoreCase` / `multiline` — the roadmap's "M each" is WRONG; each is ~L (engine change), and
  they need a DESIGN DECISION first.** The engine is flag-OBLIVIOUS: `regex-engine/src` has ZERO
  references to `Canonicalize`/`ignoreCase`/`multiline` — char matching is a raw compare
  (`Charclasses.dfy:174`), anchors are input-boundary only (`Anchors.dfy:44`). So it's NOT
  "thread the `!rer` hypothesis + prove flag-on cases" (there are 63 `!rer.ignoreCase` / 62
  `!rer.multiline` requires, but relaxing them is necessary-not-sufficient) — you must first CHANGE
  the engine (compiler emits canonicalizing char-expectations; anchors go line-aware) and re-prove.
  **Design conflict:** `LOOKAROUND_CAMPAIGN.md:373` declares RegElk flagless BY DESIGN ("`TheRer`'s
  fixed record IS the spec"). So decide whether RegElk gains flags at all before this is a rung. If
  yes: **multiline < ignoreCase** (multiline touches only the anchor matcher; ignoreCase touches
  every char/class compare + the `Canonicalize` law throughout Translate/CaptureContent/OracleSpec).
- **Backreferences — XL confirmed, a SEPARATE PROJECT.** Not a predicate exclusion but a TYPE wall:
  `raw_regex`/`regex` have no backref constructor (Regex.dfy:70-79,119-128), the parser can't emit
  one, so it's unrepresentable in the engine pipeline. Pike/NFA structurally cannot do backrefs
  (linear NFA vs NP-hard). `ReadBackRef` is a dead end in every machine (PikeTree/PikeSubset/
  PikeTreeLk/TreeRep). Needs a whole new stack (constructor+parser+instruction+interpreter+
  correspondence). Out of the pike world entirely.
- **`LookBehindFragment{Raw,RE}` → `Supported`/`LookFragment` rename — S, cosmetic but WIDE.** The
  predicate is already semantically general (admits all shapes); only the NAME lags (ApiMatch.dfy:52).
  247 occurrences across 18 files, pure rename, zero logic change, zero user payoff. **Do it
  opportunistically BEFORE L4** so L4 generalizes cleanly-named predicates.

**Recommendation:** L4 (nesting) remains the next real campaign. Fold in the rename as free
housekeeping first. Flags are NOT rungs until a "does RegElk get flags?" design call is made — and
if made, they're L-sized engine work (multiline the smaller), not M. Backreferences stay a separate
XL project. All of these are INDEPENDENT of L4's oracle-sweep machinery (can proceed in parallel).

---

## L4 / L5 Roadmap (original, 2026-08-03)

Replaces the one-line L4 entry in `LOOKAROUND_CAMPAIGN.md` §4 ("mostly
assembly once L1/L2 exist" — the same optimism that priced L3 at one session
when it took a multi-session campaign and two design pivots). This document
prices the next rungs against what L3 **actually** cost, and fixes the
architecture for each so the next campaign starts building, not discovering.

Prerequisite for everything here: **L3 closed** — `LiftSim.dfy` filled and the
else branch rewritten (see `L3A_FINAL_ASSEMBLY_HANDOFF.md` §2-NEW). Do not
start L4/L5 on top of a scaffold.

---

## 0. L3 retrospective — the calibration

What L3 taught, as pricing rules:

| lesson | rule for L4/L5 |
|---|---|
| The blocker was never the stated theorem (position) but the *invariant vocabulary* (no sim state contained an LK node) | Before pricing a rung, ask: **can the needed fact even be phrased on the states the proof holds?** If not, the cost is a new machine/relation, not a lemma. |
| Parallel frames (ClockMono trio shape) went **first-try, five times** | Work phrased as a parallel induction over `FAdvanceEpsilon`/`FConsume`/`FFindMatch` is cheap and predictable (~150-250 lines each). |
| Machine mirrors went first-try (`PikeTreeLk`: ~700 lines, 29/0, one missing match case) | Mirroring a proven invariant layer with new node shapes is mechanical **if** the new shape matches an existing case template (LK ≅ GroupActionT). |
| Augmenting load-bearing monoliths (`PikeInvFullRE`, `ActionsTreeRepFRE`) was correctly avoided every time | Never mutate the proven sim or the 615-line walk. Build parallel, compose at endpoints. |
| Local inversions beat re-walks (`GateNodeAtInp` etc. — hours, not days) | Check for an inversion before designing an induction. |
| The monolith tax is real: `MainTheorem` 15-20 min/verify, `ActionsTreeRepFRE` ~98% of package time | Decompose **before** a campaign that iterates against these files, not after. |
| Engineering blockers gate shipping independent of proofs | `lem pack`'s 10-min wall (Lemmata `Native.cs:3040`) must be fixed before any rung can ship a `.doo`. |

Sizes below: **S** = one focused session, frame/inversion-shaped. **M** = 2-3
sessions, new definitions + frame family. **L** = a campaign (L3a-scale):
multiple sessions, ≥1 design risk. **XL** = L plus a known-unsolved core.

---

## 1. L4 — nesting (lookarounds inside lookaround bodies)

### 1.0 The headline: the ENGINE is already designed for nesting

Three facts, verified in `regex-engine/src/Engine/Interpreter.dfy` (do not
re-derive; cite):

1. **Build order** (`FBuildLids`, :525): sweeps `maxlook` DOWN to 1; annotate
   numbers outer lookarounds LOWER, bodies at `l+1` — so inner lids build
   FIRST and an outer build regex's `CheckOracle(inner)` reads finished
   columns.
2. **Reconstruction order** (`FLookLoop`, :560): ascends lid 0→maxlook —
   OUTER bodies replay first.
3. **Register threading** (`FLookLoop`, :580): the `Some(t)` branch threads
   the replay's FULL triple — `(t.capture_regs, t.look_regs, t.quant_regs)` —
   into later iterations. An outer body's replay crosses `CheckOracle(inner)`
   and *records the inner gate's `a_cp` into the threaded `lk`*; the inner
   lid's own replay then fires at exactly that position. The
   `get_cp(lk, lid)` guard is `Some` for an inner lid iff some outer replay
   crossed it — which is exactly the semantics (inner captures exist iff the
   outer body's matching path crossed the inner gate).

So L4 is a **proof-mirrors-design** campaign: the proof must follow the
lid-order/threading discipline the engine already implements. Zero engine
changes (the L3 principle holds).

### 1.1 Architecture: the depth-parametric lift

The keystone insight. In L3, `LkReplayMatchesSpec` (body replay ≈ body spec
tree) was provable directly because bodies were `LookFreeRE`. At L4 a depth-k
body contains gates, so *the keystone at depth k IS a lift instance at depth
k-1*: the body's replay run relates to the body's spec tree — which contains
LK nodes — via exactly the machinery `LiftSim.dfy` builds for the main run.

Therefore: **generalize the lift, don't duplicate it.** `LiftFindMatch` is
already stated over an arbitrary `(code, ...)` start; the L4 work is making
its fragment hypotheses depth-indexed and reusing it as the keystone's engine
half, inducting on nesting depth.

What survives L4 UNTOUCHED (this is why the L3 pivot pays off twice):

- **`PikeTreeLk` — already nesting-ready.** `TreeRes`/`LkResult` recurse
  through nested LK nodes; `PikeSubtreeLk` leaves the body `tlk`
  unconstrained; the machine's correctness never looks inside a gate. No
  edits.
- **`GateAheadClear` — modular by construction.** Inner gates do not appear
  in the main code (only in body bytecode), so the main walk's pending-gate
  scan (`RegexTopGate` stops at `Quantified` and never enters `LookaroundR`
  bodies) is already correct at L4; each recursive lift level polices its own
  gates.

### 1.2 Work items

- **W1 [S] — depth vocabulary.** `NestDepth(re)`, `NestedFragmentRE(k)`
  (k=0 ≡ today's `LookBehindFragmentRE` modulo the rename), annotation/
  lazy_prefix preservation, the lid-order fact as a lemma: *inner lids are
  strictly greater than their enclosing lid* (from annotate's numbering; this
  is the induction's backbone).
- **W2 [M] — classification: flat split → containment forest.**
  `CapIdsInLooks`/`CapIdsOutsideLooks`/`CapIdsSplit`/`CapIdsLooksDisjoint`
  and `LmOfBodiesDisjoint` all assume look-free bodies ("bodies never
  nest"). Replace flat disjointness with the forest: distinct lids' CapIds
  are disjoint OR nested (inner ⊂ outer body), owner-of-g = the INNERMOST
  lid containing g. `GmtTieInside`'s owner existential switches to innermost.
  Mechanical but wide — this is the L4 analogue of L3's §4a groundwork.
- **W3 [M] — oracle correctness, "correct above lid" induction.**
  `OracleOkAt` per-column, by descending-lid induction: column `lid` built
  against columns `> lid` already correct. The campaign notes say the
  sweep-frame lemmas (a build for lid only reads higher columns, writes its
  own) already exist — VERIFY that claim early; if the frames are L1-shaped
  (look-free build regexes) the build-side rep lemmas need the gate rule
  added, which is where W3 grows from M toward L.
- **W4 [L] — the depth-inductive keystone.** Restate `LkReplayMatchesSpec`
  with `NestedFragmentRE(k)` bodies, proved by: lift-at-depth-(k-1) for the
  body run (engine half) + `PikeTreeLkComputesFirstLeaf` on the body tree
  (spec half). Induction on k, base = today's proven keystone. The delicate
  part: the replay enters with the MAIN pass's threaded registers
  (`FFindMatchPlus` from `cap, lk, qt`), so the L3 relational bisimulation
  (`ReplayCapAgreeFresh` family) needs its register-blindness argument
  restated for code that READS `look_regs`... it does not: `CheckOracle`
  branches on the ORACLE, not on register values, and writes `a_cp`
  unconditionally on the taken branch — re-verify `FAdvanceEpsilonRel`'s
  cases cover this (they should; the dedup is by (pc, flag)).
- **W5 [M] — the FLookLoop value induction, outer-first.** Strengthen
  `FLookLoopValueLift`'s per-lid induction with the threading invariant:
  after processing lids `≤ i`, for every gate the processed replays crossed,
  the threaded `lk`'s `a_cp` is oracle-true and position-correct (the L3
  oracle-truth frame `FFindMatchLookOracleTrue` re-run on REPLAY code — same
  parallel frame, S-sized on its own). The loop's ascending order + W1's
  lid-order fact make "outer before inner" the induction order.
- **W6 [S] — endpoint + else branch.** `L3aValueBridge` generalizes: inner
  groups' values reconstructed at the a_cp recorded by their OUTER replay —
  statement unchanged in shape, owner resolution via W2.

**Total: L.** A full campaign — comparable to L3a, but with no unknown of the
position-gate kind: every W-item names its template. The two places a
discovery could still lurk: W3 (if the sweep frames don't cover gate-bearing
build regexes) and W4's replay-entry conditions.

### 1.3 Prerequisites (hard gates)

1. L3 filled and green, else branch rewritten.
2. **Decompose `ActionsTreeRepFRE`** (per its own comment: per-shape
   standalone lemmas). W3/W4 iterate against walk lemmas; at ~4300 batches /
   ~3800 cpu-s per verify, L4 is unaffordable without this. Budget one
   session; it is pure refactoring of a green proof.
3. Fix the `lem pack` wall (Lemmata `Native.cs:3040`/`:610`) so rungs ship.

---

## 2. L5 — capturing LOOKBEHINDS (defining the rung)

The ladder never defined L5; this document does. L3 delivers captures in
positive lookAHEADS only — the fragment still requires capture-free
lookbehind bodies, and `FLookLoopValueLift` steps a matched capture-free
lookbehind as the IDENTITY. The engine, again, is already ahead of the proof:
`FLookLoop` replays every `capture_type` look in `capture_direction(looktype)`
— **Backward** for lookbehinds — through the same `FFindMatchPlus`. Code path
exists, unproven.

### 2.1 Work items

- **V1 [S] — direction-parametric statements.** `FreshBodyMatch`, the
  keystone, and `GmtTieInside` take the look's `capture_direction` instead of
  hardcoding Forward. (`LkResult`/`TreeRes` are already direction-correct via
  `LkDir`.) `PikeTreeLk` needs NOTHING — the machine consumes `LkResult`
  whole.
- **V2 [L] — the backward value keystone.** The Backward mirror of
  `BodyTreeAtCp`/`FindMatchBodyAtCp`: body replay running Backward over
  `compile(reverse_regex(body))` ≈ the body tree walked in `LkDir =
  Backward`. The groundwork EXISTS and was built for exactly this: L3-0
  widened the SpanDuality `Bwd*`/`Fwd*` value duality to `GroupOkL`
  (capturing bodies) — 122 verified in `linden-reasoning`. What remains is
  lifting the duality from `MatchesL`-level to first-leaf VALUE level for the
  reversed run, plus the backward analogues of the L3 parallel frames
  (mechanical; the frames are direction-generic except for the cp arithmetic
  — `FFindMatchRegsWf` is already direction-generic, cited in the L3a
  handoff §1b).
- **V3 [S] — value lift + endpoint.** Replace the lookbehind-identity arm of
  `FLookLoopValueLift` with the real backward arm; extend `L3aValueBridge`'s
  owner cases. `MainMatchLookClkSet`/`LookCpsOracleTrue` are
  direction-agnostic on the MAIN pass (unchanged).

**Total: M-to-L**, dominated by V2. No new machine, no new sim — the lift and
machine B are direction-blind at the state level.

### 2.2 Explicit non-items at L5

- **Negative-lookaround captures: a NON-ITEM.** Spec: a negative look
  contributes no group map (`LkResult` returns `Some(gm)` unchanged on
  failure-to-match). Engine: `capture_type` excludes negative flavours, so
  `FLookLoop` never replays them. Nothing to prove beyond what L1/L2 already
  cover. Do not let this creep in as work.

---

## 3. Sequencing recommendation

```
L3 fill (LiftSim bodies) ──► else-branch rewrite ──► package green
        │
        ├─► ENGINEERING GATE: ActionsTreeRepFRE decomposition + lem pack wall
        │
        ├─► L5 (capturing lookbehinds)      [M-L; independent of L4]
        │
        └─► L4 (nesting)                    [L; wants the gate paid first]
```

**L5 before L4.** Reasons: (a) L5 is the smaller rung and ships a
user-visible fragment extension (capturing `(?<=...)`) on its own; (b) V1's
direction-parametrization touches the same keystone statements W4 will make
depth-parametric — doing direction first means L4 generalizes an
already-2-parameter keystone once, instead of L4-then-L5 re-touching W4's
output; (c) L4's W3 risk (oracle sweep frames) is the roadmap's biggest
unknown — buying information there can proceed in parallel with L5 as a
scouting task (verify the sweep-frame claim against gate-bearing build
regexes; half a session).

After L5+L4, the remaining ladder to "ECMAScript minus flags" is:
backreferences (XL — outside the pike fragment entirely; `ReadBackRef` is
dead in every machine), `ignoreCase`/`multiline` (M each — `rer` hypotheses
threaded everywhere), and the `LookBehindFragmentRaw`→`Supported` rename
housekeeping. None are rungs until priced by their own document.
