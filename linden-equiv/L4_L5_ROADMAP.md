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

### L4 depth-k DEFINITIVE PRICING (scout 2026-08-14; the bottleneck hypothesis was FALSIFIED)

The architectural key: **a lookaround compiles to a SINGLE `CheckOracle`/`NegCheckOracle` LEAF**
(NfaRepRE.dfy:1193-1199 — the body lives in the per-lookaround tables), so the proven Pike sim's code
contains NO look-body structure. Therefore the "never-mutate-the-proven-sim" monolith `PikeInvFullRE`
(PikeSimRE.dfy:831-850) has **NO structural depth-1 assumption** — it is an S-shaped parameter-swap,
NOT the bottleneck. A repo note already states this boundary (MainTheorem.dfy:5586-5595).

Per-component (LookBehindFragmentRE → NestedFragmentRE):
- **StaticOkRE** (PikeSimRE:99): the fragment is ONE conjunct of 9 → **SWAP** [M], sound via the
  already-proven `LookBehindFragmentIsNestedRE`. `SizesOkRE` has no depth dep (free). ~50 `StaticOkRE`
  consumers (18 PikeSimRE + 26 LiftSim scaffold + 6 MainTheorem).
- **PikeInvFullRE** (PikeSimRE:831): parameter-swap [S], LOW — its only look-conjunct `LooksCapUnset`
  is depth-invariant (looks emit no `SetRegisterToCP`). NOT the bottleneck.
- **GmConfinedTree/LkConfinedTree** (CheckErase:1081-1108): `LK=>false` is a structural cap →
  **recursive REWRITE** [L], ~100 consumer sites (incl. the whole preservation family) — mechanical
  but wide.
- **PikeLkRegex/PikeLkActions/NoLkBrL** (EntryLk:214-567): `NoLkBrL` bans looks → recursive rewrite
  [L]; ~412 sites but nearly all are HYPOTHESES a weaker predicate satisfies — only the destructors
  (`TranslateNoLkBr`/`ComputeTrGmIndepLk`/`ComputeTrNoLK`) need real re-derivation.
- **ComputeTrLkConfined/ActionsTreeRepRE**: already S-threaded, accept `LkConfinedTree(t,S)` LK-trees
  → **mostly free** once the above land [M].
- **#6 THE BOTTLENECK — `BodyTreeAtCp`/`LkReplayMatchesSpec`** (MainTheorem:2888/5620): a genuinely
  NEW recursive theorem inducting on `NestDepth` [XL, HIGH], resting on the oracle-build passes
  (OracleEntry/OracleBuild/OracleDecomp, all `requires LookBehindFragmentRE`) building SUB-ORACLES for
  nested bodies. Cannot be unrolled. This is where the cost lives.

**Additive vs mutate:** the SIM half is fully ADDITIVE (thread `NestedFragmentRE`, or a parallel
`StaticOkNestedRE` derived via `LookBehindFragmentIsNestedRE` — all ~18 sim preservation lemmas stay
green, monolith untouched). The VALUE half is genuinely new recursive scaffolding but STILL additive
to the sim (no `PikeInvFullRE` edit). Plus the independent `SweepCharacterizationV` (W3 brick-4c gap).

**SCOPING OPTIONS (value-per-cost):**
1. **Full depth-k capturing** — L–XL, dominated by #6 + recursive #3/#4 + `SweepCharacterizationV`.
2. **Non-capturing nested looks (CHEAPER PARTIAL WIN, ~40–50% cost)** — restrict nested bodies to
   capture-free; SHEDS the entire capture-reconstruction lift (the 26 bodiless `LiftSim` scaffold
   lemmas + the `LkReplayMatchesSpec` capture-agreement obligations). Keeps only the recursive
   match-VERDICT half + recursive #3/#4. Delivers real nesting value (`(?=a(?=b)c)` — nested looks
   that gate matching without capturing).
3. **Bank the foundation** — spec side is ALREADY depth-generic (`TreeResGmFrameRec` +
   `NestedFragmentRE`/`NestDepth`); the engine↔spec bridge (#6) is the only gap. Stop with the verified
   model/spec/theorem-shape foundation and price full depth-k as its own campaign.
- Depth-2-only is NOT worth it (the recursive step is already required at depth 2).

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

> **SUPERSEDED (2026-08-23).** This section prices the *depth-1* capturing lookbehind, which
> shipped as **L3b** (done). With L4 (nested capturing lookahead) now complete, the current
> **L5 = NESTED capturing lookbehind**. See the section **"L5 (nested capturing lookbehind) —
> SCOPE + T0 SCOUTING"** at the end of this file for the up-to-date scope.

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

## 2026-08-15 — recon_inner sub-campaign (=W5 remainder) EXECUTION

The seam `LkReplayMatchesSpecNestedFull` (MainTheorem, commit 7610cdb) reduced the full-`DefGroups`
value keystone to two premises over a reconstructed bank `(reccap,reclk,recqt)`: `recon_outer`
(reconstruction preserves outer groups) and `recon_inner` (on inner-look groups it matches the spec
`LkResult`). This sub-campaign discharges them by instantiating the bank as the engine's `FLookLoop`
output and recursing on `NestDepth`.

**KEY SIMPLIFICATION (de-risk):** every nested capture `g` bottoms out at its INNERMOST OWNER lid,
where `g` is an OUTER (direct) group of that lid's body — so `g`'s value is dischargeable by the
ALREADY-PROVEN `LkReplayMatchesSpecNested` (outer-groups agreement). No deep seam recursion is
needed; the depth recursion collapses into (i) innermost-owner resolution (structural, R1),
(ii) recorded-position correctness (already proven at match level via `BodyTreeAtCpNested`), and
(iii) `TreeRes` LK-composition (spec, R3b). The `FLookLoop` reconstruction is one FLAT loop; its
only subtlety is that inner `a_cp` is written mid-loop by ancestor iterations, so the value-lift
invariant must be keyed on the FINAL look bank `res.1`, not the input `lk`.

Bricks (all ADDITIVE):
- **R1 DONE (commit 4cb73aa):** innermost-owner classification. `NestInv`: `InnermostOwnerDirect`
  (g resolves to an owner lid holding it DIRECTLY: `g in CapIds(body) && g !in CapIdsInLooks(body)`),
  `NestDepthLookBodyDrops` (`NestDepth(LookBodyOfRE(r,l)) < NestDepth(r)`), `NestedGWriteFrame`
  (only the owner directly holds `g`; any other lid holding `g` is a proper ancestor). `MainTheorem`:
  `VBodyEqLookBody` (`LookTablesOk ==> VBody(crv,l)==LookBodyOfRE(re,l)`).
- **R2 DONE (commit e3375dd):** FLookLoop frame + outer-caps value-lift for NESTED bodies.
  `FLookLoopCaptureFrameNested` (writes only inside `S`; look bank grows only by inner-look a_cp:
  `RegsAgreeOutside(res.1, lk, Slook)` — NOT `res.1==lk`, which is false at depth>=2) and
  `FLookLoopValueLiftOuter`/`FLookLoopValueOkOuter` (on each matched look body's OUTER caps
  `CaptureRegsSet(CapIdsOutsideLooks(body))`, `res.0` carries the fresh body match), per-lid
  existential relaxed `LookFreeRE -> NegLooksLookFreeRE`, per-lid engine bridge
  `ReplayLidCapAgreeFreshNested`. Verified in-tree 191/0 and 630/0. Scope: capturing looks are
  Lookahead-only (matches the nested keystone).
- **R3 IN FLIGHT:** `FLookLoopValueOkFull`/`FLookLoopValueLiftFull` — whole-loop lift re-keyed on the
  FINAL bank `res.1`, retaining inner-owner coverage (R2's Outer version drops it). Induction reuses
  R2's per-lid bridge + frame + R1 disjointness; a_cp[lid]-stability (no later replay writes look
  index `lid`, by well-nestedness) bridges input-lk to final-res.1 keying. Stretch: DefGroups-coverage
  corollary routing each `g in CapIdsInLooks(re)` through its innermost owner.
- **R3b / W6-start (NEXT):** spec-side discharge — `LkReplayMatchesSpecNested` at each owner +
  `TreeRes` LK-composition (owner LkResult[g] == outer LkResult[g]) + position via `BodyTreeAtCpNested`;
  then instantiate the seam per look inside a nested `L3aEndpointAssembly`.

**PROCESS NOTE (deps-symlink hazard):** worktree agents symlink `linden-equiv/deps` to the primary
checkout; `git add -A` staged that symlink and a cherry-pick then overwrote the real `deps/` dir with
a self-referential link (recovered by rebuilding from the versioned `*.doo` in each dep project dir).
Fixes: `.gitignore` now ignores a `deps` SYMLINK (commit adca767); integrate agent commits by
extracting the `.dfy`-only diff (`git show <c> -- <path> | git apply`), never cherry-pick whole
commits; tell agents to `git add <file>` not `git add -A`.

### 2026-08-15 (cont.) — recon_inner: BOTH novel halves PROVEN; remaining = seam-closing GLUE

- **R3 DONE (commit 2580012):** `FLookLoopValueLiftFull` + `FLookLoopFullCoversInLooks` — the whole-loop
  FLookLoop capture reconstruction re-keyed on the FINAL look bank; `res.0` provably carries EVERY
  `g in CapIdsInLooks(re)` at its innermost owner's fresh-body-match value, arbitrary depth. Adds
  well-nested-lids hyp (h) + a_cp-stability helper `FLookLoopLidCpStable`. Verified in-tree 636/0, 2/0.
  **This is the ENGINE-side recon_inner — the reconstruction is proven correct.**
- **R3b DONE (commit eb75141):** the SPEC-side value composition toolkit —
  `TreeResGValueFramed` (TreeRes leaf value at a single group `g` depends on incoming gm only through
  `gm[g]`; NO confinement needed — control flow is gm-blind, group values evolve only from own writes),
  `TreeResGIndepWhenWritten` (maps differing only at `g`: if `g` is written on the winning path the
  leaf values AGREE at `g`, independent of the differing `gm[g]` — the owning look pins it),
  `TreeResLkNodeGValue` (a matched look node's leaf value at `g` == that look's sub-tree `TreeRes`
  value at `g`), + `AgreeOffG`/`GDefBeforeClose`/`GNotWritten` toolkit. Verified in-tree 4/0,2/0,2/0,2/0.
  **This is the SPEC-side content of "inner capture value is determined by the owning look, not the
  surrounding gm."**

**Both mathematically novel obstacles of recon_inner are now cleared and verified.** What remains to
DISCHARGE the seam `LkReplayMatchesSpecNestedFull` is structural GLUE (= W6 endpoint territory):
1. **Regex↔spec-tree owner-node correspondence (the named blocker):** a new structural-induction lemma
   over `ComputeTr`/`Translate` showing `tlk = ComputeTr(Translate(body))` has, on its winning path,
   an `LK` node whose sub-tree `== ComputeTr(Translate(LookBodyOfRE(body, owner)))` and which is the
   innermost owner of `g` (with `GDefBeforeClose`/continuation-`GNotWritten`). This is what lets
   R3b's `TreeResLkNodeGValue` connect `owner-standalone-LkResult[g]` (from `LkReplayMatchesSpecNested`
   at the owner) to `outer-LkResult[g]`. Ties to the winning-path/position via `BodyTreeAtCpNested`.
2. **FLookLoop bank instantiation:** discharge hypotheses (a)-(h) of `FLookLoopFullCoversInLooks`/
   `FLookLoopCaptureFrameNested` for the reconstruction range (a nested analogue of `LookRowsFromTablesL3a`),
   supplying `recon_outer` and the engine side of `recon_inner`.
3. **Assembly:** instantiate the seam per look; then W6 proper wires it into the whole-regex value
   bridge (nested `GmtTieInside`/`L3aValueBridge`/`L3aEndpointAssembly`/`MainTheoremL3`) + widens the
   `Supported` gate `LookBehindFragmentRaw -> NestedFragmentRaw`.

Net recon_inner status: engine reconstruction + spec composition = DONE & verified (5 commits,
~20 new lemmas, 0 red). Seam closure = a bounded multi-brick GLUE sub-campaign (items 1-3), which is
the W6 endpoint. Cleanly checkpointed here.

---

## L5 (nested capturing lookbehind) — SCOPE + T0 SCOUTING (2026-08-23, after L4 complete)

**Context.** L4 (nested capturing *lookahead*) is complete: `MainTheoremL4` single-shot green
(4722/0/0, commit `117b6aa`), `ApiMatch.MatchCorrect` green over `Supported = SupportedL3 || SupportedL4`.
The old §2 "L5" (depth-1 capturing lookbehind) shipped as **L3b** (`LkReplayMatchesSpecLB`
`LookBehindKeystone.dfy:395`, re-verified 404/0 on `l4-nesting`). The **current L5 = NESTED capturing
lookbehind**: lift L4's nesting to lookbehinds by removing `NoPosLookbehind`.

### Headline — L5 is a PURE PROOF LIFT (no engine or table work)

The engine and compile-tables are already fully direction-generic and run nested lookbehinds backward
*today*:
- `AI.FLookLoop` dispatches direction per-look via `capture_direction` (`Lookbehind → Backward`);
  `AI.FFindMatchPlus` takes `dir` first-class.
- `oracle_regex`/`capture_regex` already reverse lookbehind bodies; `LookEntryOk`
  (`LookTables.dfy:209`) / `LookTablesOk` (`:221`) recurse through `Re_lookaround(_, Lookbehind, body)`
  at any depth.
- `NR.NestedFragmentRaw` (`NfaRepRE.dfy:1153`) **already admits** capturing positive lookbehind;
  `NR.NoPosLookbehindRaw` (`:624`) is the single conjunct that subtracts it.

The Forward-only restriction lives entirely in the PROOF layer, concentrated at **one dead branch**:
`LiftSim.dfy:22441`, BRICK D5's `else { assert false }` for the lookbehind arm of the nested
lookaround step. It is dead only because the nested value keystone `LkReplayMatchesSpecNested`
(`MainTheorem.dfy:9642`) is `requires la.Lookahead?`.

**The single missing lemma:** a lookbehind analog of `LkReplayMatchesSpecNested` — i.e. generalize the
depth-1 lookbehind keystone `LkReplayMatchesSpecLB` from `requires LookFreeRE(body)` to
`requires NestedFragmentRE(body)`.

### T0 SCOUTING RESULT (2026-08-23) — route the value tie through `MatchesVMirror`/`XRev`, NOT recursive `RevRE`

The feared blocker was that the depth-1 lookbehind value tie reverses the SPEC regex via
`SD.RevRE`, whose lookaround case is **identity** (`SpanDuality.dfy:2086`, does not recurse) — so
lifting that path looked like it needed a recursive `RevRE` + re-derivation of the whole SpanDuality
`Bwd*/Fwd*` value duality. **Scouting says that is avoidable.** Verdict: **VIABLE, RevRE-recursion
retired.** Findings:

1. **Span level — DONE, nested-ready.** `XRev(re) := SwapAnchorsRegex(reverse_regex(re))`
   (`OracleMirrorV.dfy:44`) IS nested-recursive (recurses into look bodies), preserves the fragment
   (`ensures NestedFragmentRE(XRev(re))`, `:189`), and is involutive (`XRev(XRev(re))==re`, `:210`).
   `MatchesVMirror` (`:306`) gives `MatchesV(re,str,ov,i,j) <==> MatchesV(XRev(re),Reverse(str),
   MirrorView(ov),|str|-j,|str|-i)` at any depth. **RevRE stays untouched** (depth-1 L3b keeps using
   it); L5 uses `XRev` in parallel.
2. **Engine value level — DONE, structure-generic.** `FFindMatchMirror` (`Mirror.dfy:963`) has NO
   `LookFree`/`NestedFragment` requirement — its backward-run ↔ forward-run-on-reversed value
   isomorphism (`MirrorState`/`MirrorRegs`) works for nested-look bytecode as-is.
3. **Groupmap register-mirror — DONE, depth-generic.** `GmOfLiveMirror` (`BackGmMirror.dfy:260`):
   `GmOfLive(body, MirrorRegs(cap,n), look, quant) == RawMirrorGm(GmOfLive(body, cap, look, quant), n)`
   — structure-agnostic, reusable verbatim. Mirror/`SwapGm` involutions likewise.
4. **THE ONE NEW VALUE-LEVEL PIECE.** The value tie needs the reversal bridge
   `GmOfLive(XRev(body), X) == GmOfLive(body, X)` (to let the FORWARD nested keystone
   `LkReplayMatchesSpecNested`, applied to `XRev(body)` which is `NestedFragmentRE`, read the reversed
   forward run's value). Today this bridge exists only for `RevRE` (`BackGmMirror.dfy:311`,
   "RevRE bridge"). Its proof reason is structural and reversal-generic: the capture filter only ZEROES
   a **clock-determined** register set that is independent of positions, and reversal only reorders
   `Re_con` children (set union commutes). Generalizing it to `XRev` adds the **lookaround-recursion
   case** (reversing a look body preserves its `DefGroups` set). **Bounded structural induction — S-to-M,
   not the feared duality re-derivation.**

**Net effect on pricing:** the old T1 ("recursive spec reversal" — M, risky) collapses to reusing the
already-built `XRev` + one bounded `GmOfLive`-under-`XRev` bridge. The campaign's dominant risk is
retired before it starts.

### Work items (revised post-T0)

| # | Item | Size | Anchors |
|---|---|---|---|
| **T1** | `GmOfLive(XRev(body),X)==GmOfLive(body,X)` bridge (extend the `RevRE`-bridge argument with the lookaround-recursion case) | **S–M** | `BackGmMirror.dfy:311` |
| **T2** | `LkReplayMatchesSpecLBNested` — the nested backward value keystone: fuse `LkReplayMatchesSpecNested`'s depth-k induction with `FFindMatchMirror` + `MatchesVMirror`(`XRev`) + T1 + `GmOfLiveMirror` + `SwapGm` | **L** (dominant) | mirror of `MainTheorem.dfy:9642` and `LookBehindKeystone.dfy:395` |
| **T3** | Wire in: replace `assert false` (`LiftSim.dfy:22441`) with T2; restore the dropped value package in `ThreadRepLkStepCheckOracleLBNested` (`LiftSim.dfy:9818`, `// (1) INSIDE tie DROPPED`); admit lookbehind bodies in `GateStaticAtNested` (`LiftSim.dfy:5592`) | S–M | |
| **T4** | Drop `NoPosLookbehind*` from `L4Scope` (`LiftSim.dfy:26517`), `LookRowsFromTablesNested` (`MainTheorem.dfy:17015`), `SupportedL4` (`ApiMatch.dfy:71`); **re-run the opaque-at-source perf pass** on the nested tower now covering lookbehind (toolkit from §18 of `FULL_DEPTH_K_HANDOFF.md` is ready: `FreshWfO`/`FreshWfAtG` pattern + `ThreadRegsWf`-into-scope + opaque `MatchCorrect` requires) | **M** | |
| **T5** | Generalize `Supported`/`MatchCorrect`; fix the stale `SupportedL3` "capture-free lookbehind" doc comment (`ApiMatch.dfy`) | S | |

**Order:** T1 → T2 → T3 → T4 → T5. **Overall:** a medium multi-phase campaign dominated by T2,
smaller than L4 itself (no new machine; the nested span-mirror and depth-1 value keystone both exist;
the boolean gate already handles nested lookbehind). Payoff: user-visible nested capturing `(?<=…)`.

### Reusable inventory (green today)
`XRev`/`MatchesVMirror`/`MatchesVMirrorFwd` (`OracleMirrorV.dfy`), `FFindMatchMirror`/`MirrorRegs`/
`MirrorRegsInvol`/`SwapAnchorsCode` (`Mirror.dfy`), `GmOfLiveMirror`/`RawMirrorGm`/the RevRE bridge
(`BackGmMirror.dfy`), `SwapGm`/`SwapRange` involutions (`LookBehindValue.dfy`),
`BackwardReplayMirror`/`SwapRevIsRevRE` (`BackValue.dfy`, depth-1 template),
`LkReplayMatchesSpecLB`/`BackFreshBodyGmTie`/`LBEngineLeaf` (`LookBehindKeystone.dfy`, depth-1 keystone
to lift), `LkReplayMatchesSpecNested` (`MainTheorem.dfy:9642`, the forward nested keystone whose shape
T2 mirrors), and the `dir`-parameterized frame family (`ReplayPlus*Nested`, `FFindMatchRegsWf`).

### Non-items (do not let creep in)
Negative-lookaround captures (spec contributes no groupmap; `capture_type` excludes negatives).
Flags (`ignoreCase`/`multiline`), non-Latin-1, backreferences — all orthogonal, priced separately
in the "L5+ ladder pricing" section above; none are L5.

### L5 progress (2026-08-23, session cont.) — T1 + T2a GREEN; T2b precisely located

**T1 GREEN (`183e465`).** `GmOfLiveXRev` + chain (`BackGmMirror.dfy`, whole file 36/0):
`GmOfLive(XRev(body),·)==GmOfLive(body,·)` at any depth. Risk gate retired on first try.

**T2a GREEN (`<this commit>` BackValue.dfy).** `BackwardReplayMirrorNested` (2/0): the backward
body replay of `compile(reverse_regex(body))` = mirror of the forward run of `compile(XRev(body))`
over `Reverse(str)`, for ANY body (no `LookFreeRE`). The depth-1 `BackwardReplayMirror` used
`LookFree` only via `SwapRevIsRevRE`; `CompileToBytecodeSwap` alone gives
`SwapAnchorsCode(bc)==compile(XRev(body))`. So the ENGINE half of T2 is done and generic.

**T2b — the dominant remaining work — is in the linden-reasoning DEPENDENCY.** The spec-side
nested tree mirror. Depth-1 `LkReplayMatchesSpecLB` routes the value tie through
`LBV.BackBodyGmTie`/`BackBodyEngineTie`, which stand on:
- **`SD.RevL`** (SpanDuality.dfy:338, linden-reasoning) — `case LookaroundR(lk, r1) => r` is IDENTITY
  on lookarounds (the L-spec twin of RevRE's blocker). Needs a recursive lookaround case.
  **SEMANTIC DECISION REQUIRED:** under string reversal a lookBEHIND faces forward — does the
  recursive `RevL` FLIP the look kind (Lookbehind↔Lookahead) or keep it? NB the engine
  `reverse_regex` keeps `la` UNCHANGED (`XRev(Re_lookaround(lid,la,r1))==Re_lookaround(lid,la,XRev(r1))`,
  OracleMirrorV.dfy:280), so `RevL` must match whatever makes `Translate(XRev(body))==RevL(Translate(body))`
  hold — resolve this equivalence FIRST (it pins the flip question).
- **`TM.ComputeTrReverse` / `TreeMirrorRel`** (TreeMirror.dfy, linden-reasoning) — gated by
  `SD.GroupOkActs` = NO lookarounds (header lines 7-13 explicitly: "no lookarounds ... the L3b
  lookbehind-body fragment"). Needs generalization to look-bearing stacks.
- `SD.TranslateRevRE` (`Translate(RevRE)==RevL(Translate)`) → an `XRev`/nested analog.
- `TRM.TreeResMirror` (tree-level, takes `TreeMirrorRel`) likely extends once its `TreeMirrorRel`
  input is nested-aware; check its `CloseDisc`/`OpenSubset` handling of look sub-trees.

**Scope correction:** T2b is a cross-project sub-campaign in linden-reasoning (edit source → rebuild
`deps/linden-reasoning.doo` → consume), NOT a single linden-equiv brick. It is the true bulk of L5
("T2 [L] dominant"). Recommended entry: resolve `Translate(XRev(body))==RevL_nested(Translate(body))`
(pins the look-kind flip), then generalize `RevL` + `ComputeTrReverse`, then assemble
`LkReplayMatchesSpecLBNested` (T2c) in linden-equiv reusing T2a + `GmOfLiveXRev` (T1).

**Remaining after T2b:** T2c (assemble `LkReplayMatchesSpecLBNested`), T3 (wire in / drop the
`assert false`), T4 (drop `NoPosLookbehind` + re-run the §18 perf pass), T5 (API/`MatchCorrect`).

### L5 T2b(i) GREEN — RevL/RevRE nested + dependency pipeline validated (2026-08-23, `9e785cc`)

First linden-reasoning brick landed. `SD.RevL` and `SD.RevRE` now recurse into lookarounds
(`LookaroundR(lk,r1) => LookaroundR(lk, RevL(r1))`; no look-KIND flip — pinned by
`Translate(XRev(body))==RevL(Translate(body))` since `Translate` keeps `TrLookaround(la)` and
`XRev`/`reverse_regex` keep `la`). Because `RevRE` reverses AND swaps anchors, recursive
`RevRE == XRev` at any depth (extends `SwapRevIsRevRE` off look-free).
Conservative for all existing (look-free) consumers; companion proofs updated
(`RevLInvolution`, `RevRETransWf`, `TranslateRevRE`).

**Dependency-update pipeline VALIDATED end-to-end:** edit linden-reasoning src → SpanDuality 122/0
→ `lem build` 382/0 → `lem pack` → copy `linden-reasoning-1.0.1.doo` to `linden-equiv/deps/` →
L3b keystone `LkReplayMatchesSpecLB` re-verifies 404/0 (no regression). `deps/*.doo` gitignored
(rebuildable), so only the `.dfy` source is committed. Rebuild recipe:
`cd linden-reasoning && lem build && lem pack && cp linden-reasoning-*.doo ../linden-equiv/deps/linden-reasoning.doo`.

**NEXT T2b brick — `TM.ComputeTrReverse` / `TreeMirrorRel` widening (the authors' noted blocker).**
`TreeMirror.dfy` gates on `SD.GroupOkActs` (= no lookarounds). The SpanDuality notes (~lines 1112-1140)
lay out the plan: the `LookaroundR` arm is zero-width (succeeds iff the body sub-walk from the SAME
position does — the `MatchesL` clause; `ComputeTreeGroupOkGmIndep` already has a real `LookaroundR`
case and admits nesting), but a ONE-SHOT widening of the `Bwd*` family from `GroupFreeL`/`GroupOkActs`
to look-bearing is **blocked on the quantifier proofs** (`BwdCompleteQuant`/`BwdCompleteFree`/...).
That is the substantial remaining reasoning-layer work. After it: `SD.TranslateRevRE` already gives
`Translate(RevRE)==RevL` at any depth now (so `Translate(XRev(body))==RevL(Translate(body))` is FREE
via `RevRE==XRev`), then the nested `BackBodyGmTie`/`BackBodyEngineTie` analogs → T2c assembly.

### L5 T2b(ii) — the CRUX identified: flip-vs-gate for the nested-look tree mirror (2026-08-23)

Pushed into `TM.ComputeTreeReverse` (TreeMirror.dfy:123) widening and hit the central semantic
decision. `ComputeTreeReverse` relates a BACKWARD walk to a FORWARD walk of `RevActs` over
`SwapInput`. `TreeMirrorRel` (TreeMirror.dfy:72) has NO `LK` case. The spec walks a look body in its
INTRINSIC `L.LkDir(lk)` (SpanDuality.dfy:1072, CaptureContent.dfy:527) — a lookbehind body is ALWAYS
walked Backward. So in the mirror:

- **No-flip `RevL`** (what T2b(i) committed): the mirrored look keeps `lk`, so its body sub-walk is
  STILL Backward — but `ComputeTreeReverse` relates Backward↔Forward, so it CANNOT relate the two
  look sub-trees. `TranslateRevRE` (no-flip) is a true theorem but is NOT obviously the reversal the
  tree mirror wants.
- **Flip `RevL`** (lookbehind↔lookahead): the mirrored look's `LkDir` flips to Forward, so
  `ComputeTreeReverse` relates the sub-walks cleanly — BUT then `Translate(XRev(body)) != RevL(...)`
  because the engine `XRev` keeps `la` (oracle-based, `MatchesVMirror` at OracleMirrorV.dfy:279-283
  proves the nested span mirror with `la` UNCHANGED, relating oracle bits via `MirrorView`, NO flip).

**Resolution direction (gate-based, consistent with no-flip + the L4 architecture):** treat a nested
look in the tree mirror as a zero-width GATE, not a re-walk. `TreeMirrorRel`'s new `LK` case should
require the two look nodes to AGREE ON PASS/FAIL (both `LK` or both `LKFail`), characterized by the
ORACLE (`MatchesVMirror`-style, no flip) — NOT that their sub-trees fully mirror. The look's INNER
captures are NOT carried by the tree mirror; they come from `recon_inner` (the L4 `FLookLoop`
per-inner-lid reconstruction, `LkReplayMatchesSpecNestedFull`). This matches the authors' note
(SpanDuality ~1112: "a nested lookBEHIND is zero-width, succeeds exactly when the sub-walk of its
body from the SAME position does — the MatchesL clause"). It keeps T2b(i)'s no-flip `RevL`/`RevRE`.

**Remaining T2b(ii) work (next session, design-first):** (1) define `TreeMirrorRel`'s `LK`/`LKFail`
cases as oracle-gated pass/fail agreement (sub-tree captures excluded); (2) prove `ComputeTreeReverse`'s
`LookaroundR` case using the oracle mirror for the gate (reusing `MatchesVMirror` reasoning), body
captures deferred to recon_inner; (3) thread this through `TreeResMirror` (its `LK` case, TreeResMirror.dfy:330,
currently `false`) so look-node leaf VALUES read from the reconstructed bank; (4) widen the `Bwd*`
family (`BwdComplete*`) off `GroupFreeL` — the authors' quantifier-proof blocker — only where the
gate characterization needs it. This is a DESIGN decision point; committing a look case before the
gate-vs-flip choice is settled would risk a wrong lemma. Everything green + committed at this checkpoint.

---

## L5 — T2b SPAN/SUCCESS SIDE COMPLETE + architecture correction (HEAD `3d55dc8`)

The `53e6021` crux above was RIGHT that `ComputeTreeReverse` can't mirror a nested look's body
sub-trees — but WRONG to locate the whole nested-look problem there. The keystone actually rests on
TWO INDEPENDENT mirror facts, and they must be handled in different places:

### (A) Span/success duality — "does the zero-width gate PASS?" — **DONE, green**

This lives ENTIRELY in the `Bwd*`/`MatchesL`/`SpanDuality*` family (linden-reasoning
`SpanDuality.dfy`) and NEVER touches `ComputeTreeReverse`. Delivered this session:

- **`GroupOkLB`** (new predicate) = `GroupOkL` + nested lookBEHINDs (`LookaroundR(lk,r1) =>
  (lk.LookBehind? || lk.NegLookBehind?) && GroupOkLB(r1)`). Lookaheads stay excluded — `MatchesL`'s
  look clause only characterises the zero-width lookbehind. Companions `GroupOkIsGroupOkLB`,
  `GroupOkLBIsNoBackref` (`NoBackrefL` already admitted looks, so the map-independence infra —
  `SuccActsGmIndep` etc. — carried over free).
- **`BwdComplete`/`BwdSound` `LookaroundR` arm:** the gate `LkResult` passes iff the body's backward
  walk succeeds iff `∃m: MatchesL(r1,str,m,i)` — established by the body's OWN `BwdComplete`/`BwdSound`
  (MUTUAL recursion on the strictly-smaller body `r1`, `decreases r`). Then `Positivity(lk) <==>
  bodySucc` fixes the gate; the continuation's map shift (`gm`→`gmlk`) is discharged by
  `SuccActsGmIndep`. `TreeRes(LK)` re-evaluates the gate on `gm` and threads `gmlk` to the
  continuation — consistent with `ComputeTr`'s `LkResult`. `BwdCompleteQuant`/`BwdCompleteFree`/
  `BwdSoundQuant` widened to `GroupOkLB(r1)` in lockstep.
- **Public API unchanged:** `SpanDualityComplete`/`SpanDualitySound` keep their `GroupOkL(r)` requires
  (equiv-side consumers in `OracleSpec.dfy`/`LiftSim.dfy` untouched) and bridge via
  `GroupOkIsGroupOkLB` to new `SpanDualityCompleteLB`/`SpanDualitySoundLB` (`GroupOkLB(r)`).

**NOTE the earlier roadmap claim "widen `Bwd*` from `GroupFreeL` to `GroupOkL`, blocked by the
quantifier proofs" was STALE:** the Group case had already been widened to `GroupOkL`; only the look
arm was missing, and it needed no quantifier surgery — just the mutual body recursion above.

Green ledger: `SpanDuality.dfy` full-file 129/0 → `lem build` 389/0 → pack/copy `.doo` → L3b keystone
`LkReplayMatchesSpecLB` 404/0 (no regression). Committed `3d55dc8`.

### (B) Value/capture mirror — "WHAT does it capture?" — **the remaining hard piece (T2c-value)**

`BackBodyGmTie` (LookBehindValue.dfy:108) proves the backward body tree's leaf group-map is the
ordered mirror of the forward `RevL(tr)` tree's first leaf, via `TM.ComputeTrReverse` +
`TRM.TreeResMirror` + `CD.CloseDiscBody` — all gated `GroupOkL(tr)` (no looks). **This is where the
`53e6021` flip-vs-gate crux ACTUALLY lives.** A nested lookbehind is zero-width but captures its
INNER groups; those inner captures come from the L4 `recon_inner`/`LkReplayMatchesSpecNestedFull`
oracle reconstruction, NOT the tree mirror. So the value-side work is exactly the `53e6021`
resolution, now correctly scoped to value only:

1. define `TreeMirrorRel`'s `LK`/`LKFail` case = continuations mirror + look-kind agree, body
   sub-trees EXCLUDED (proven unmirrorable: a nested lookahead is walked Forward on both outer sides,
   but `ComputeTreeReverse` only ever relates Forward-of-`RevL` to BACKWARD-of-body);
2. prove `ComputeTreeReverse`'s `LookaroundR` arm with that gate;
3. thread `TreeResMirror`'s `LK` case (TreeResMirror.dfy:330, currently `false`) so the look node's
   leaf VALUE reads inner captures from the reconstructed bank (recon_inner);
4. widen `BackBodyGmTie` off `GroupOkL`.

**Don't commit a value-side look case before settling how recon_inner supplies the inner-leaf
group-map correspondence.** Then T2d assembles `LkReplayMatchesSpecLBNested` (reuse T2a `BackwardReplayMirrorNested`
+ T1 `GmOfLiveXRev` + (A) + (B)), T3 wires (drop `assert false` LiftSim:22441), T4 drops
`NoPosLookbehind` + §18 opaque-at-source perf pass, T5 API/doc.

### (B) RESOLVED — inner captures split off via `GmAgreeOutside(.., LkBodyGroups)` (L4 pattern)

The contradiction above is resolved, and NOT by armchair reasoning — by reading how L4 already handles
it. `ReplayCapIsBodyLeaf` (look-free, MainTheorem.dfy:6462) binds the engine value to the spec-forward
tree leaf FULLY (`bestT == FirstLeaf(t)`). Its nested sibling `ReplayCapIsBodyLeafNested`
(MainTheorem.dfy:6557, from L4) deliberately WEAKENS that to
`GmAgreeOutside(bestT.value.1, FirstLeaf(t).value.1, LkBodyGroups(Translate(body)))` — the tie holds
only on gids OUTSIDE `LkBodyGroups` (surface gids); inner-look captures come from the confined nested
machinery (`BodyTreeAtCpNested`, MainTheorem.dfy:3836 / the oracle), never the re-walk.

So the char-level trace was RIGHT: full `MirrorGm` fails on inner-look gids (backward-`r1`-at-p reads
chars before p; backward-`RevL(r1)`-over-swap reads chars after p). The mirrored-oracle intuition was
right that the engine gets inner captures correctly, but wrong that this makes the TREE mirror hold on
them. Reconciliation = SPLIT: surface via mirror, inner via the nested oracle machinery.

**Sharp de-risked (B):**
1. widen `BackBodyGmTie`/`TreeResMirror`/`TreeMirrorRel`/`ComputeTreeReverse` to nested with a
   SURFACE-only value claim: `GmAgreeOutside(MirrorGm(rb.leaf), rf.leaf, LkBodyGroups(tr))` instead of
   full `MirrorGm` equality. `TreeMirrorRel` LK case = continuations mirror + look-kind agree, body
   sub-trees EXCLUDED. Surface-preservation across an LK node is `TreeResPreservesGid`
   (CaptureContent.dfy:501, already nesting-aware).
2. inner-look gids: a BACKWARD nested replay tied to the spec-backward `LkResult` inner captures — the
   backward analogue of `ReplayCapIsBodyLeafNested`/`BodyTreeAtCpNested`. The forward-mirror (RevRE)
   side gives RevL(tr)'s inner captures ("after p", wrong for the original), so inner captures MUST be
   read from the ORIGINAL backward run's oracle, not the mirror. This is where "engine tables run
   nested lookbehinds backward today" is the payoff.
3. keystone `LkReplayMatchesSpecLBNested` = surface(1) + inner(2) assembled into
   `GmAgreeOn(.., S=DefGroups(tr))`.

### (B) STARTED — the direct-backward value-side campaign scoped + first stone green

L5's value side = mirror the L4 forward nested-capture apparatus to BACKWARD (the outer lookbehind
body walked backward directly; no `reverse_regex`/mirror, which is a proven dead-end for nested looks).
Scouting the L4 machinery (`BodyTreeAtCpNested` MainTheorem.dfy:3836 is the forward template) splits it
cleanly by direction:

**Direction-generic — REUSE AS-IS at `WP.Backward` (verified):**
- `ComputeTrLkConfinedK(.., dir, S)` (LookLeaves.dfy:1588) — takes `dir`.
- `FirstLeafAgreeOutside`, `LeavesAgreeAtOutside`, `LkBodyGroupsConfines`, `LkActsInS*` — pure-tree /
  structural, no direction.
- `GmAgreeOutside` / `LkBodyGroups` (the surface-vs-inner split) — the whole L4 confinement layer.
- The span side (A): `Bwd*`/`MatchesL`/`SpanDuality*LB` — the DIRECT-backward span tool.

**Forward-tied — NEED BACKWARD ANALOGUES:**
- `BooleanCorrectLkRec` / `EncodeEqualLkRec` (EntryLk.dfy:1483/1463) — model the FORWARD VM boolean
  tree encoding (`BoolTreeLk`, `IsTree(.., WP.Forward)`); genuinely direction-tied.
- `FindMatchBodyAtCpNested` (MainTheorem.dfy:3620) — the engine simulation, `LAnc.Forward`. THE deep
  piece; "engine tables run nested lookbehinds backward today" is where the backward version is fed.
- the `ClosedBelow`/`ClosedBelowAll` closedness ladder (MainTheorem.dfy:~2190, `WP.Forward`,
  `FwdPosActsL`-gated) — first-leaf closedness for the nested fragment; L3b's backward closedness went
  via the MIRROR (`BackBodyLeafClosed`) which is dead for nested, so this needs a DIRECT backward
  redo, stratified on `NestDepthL` like `ClosedBelow`.
- `BodyTreeAtCpNested` itself (the assembly of all the above).

The current forward gate is `NoPosLookbehindRaw` (NfaRepRE.dfy:615) / `FwdPosLooksL`
(MainTheorem.dfy:2178) = "positive looks are forward-only"; L5 lifts it to allow positive lookbehinds.

**First stone (green, `4468878`):** `BackwardBodyConfinedTree` (LookLeaves.dfy) — the backward spec
tree of a nested body is `LkConfinedTreeK(_, LkBodyGroups)`, via the direction-generic confinement at
`WP.Backward`. Confirms the surface/inner split composes backward with no mirror. Next stones: the
backward boolean-tree correctness (analogue of `BooleanCorrectLkRec`), then the backward engine sim
(`FindMatchBodyAtCpNested` backward), then backward `ClosedBelow`, then assemble
`BodyTreeAtCpNestedBackward` → `LkReplayMatchesSpecLBNested`.

### (B) the wall is the backward SIMULATION stack (checked/oracle-gated tree), not the raw tree

Robust conclusion after scouting the backward tie end to end:
- There is NO existing direct-backward simulation tie. The L3b lookbehind work characterizes the
  engine backward run ONLY via the mirror (Mirror.dfy) — `BackwardReplayMirror`: bcB(backward) <->
  bcF(forward RevRE). For nested bodies the ENGINE mirror still holds (oracle-consistent, T2a done),
  but the pure-spec mirror `BackBodyGmTie` (spec-backward-tr <-> spec-forward-RevL(tr)) breaks even on
  SURFACE groups: the two spec trees RE-WALK the nested look and disagree on its gate ("before p" vs
  "after p"), which flips a surface continuation's None/Some.
- THE KEY: the RAW spec tree (`ComputeTr`, which re-walks nested looks) cannot mirror; the CHECKED
  tree can. `BoolTreeLk`'s `LookaroundR` case pins the gate via `LkGateOk` (the ORACLE), not a
  re-walk. Oracle gates are position-indexed and mirror-consistent, so a checked tree mirrors on
  surface and its nested captures come from the oracle (confined to `LkBodyGroups`). So L5 must route
  the value tie through the ORACLE-GATED checked tree, exactly as the L4 forward keystone does — but
  backward.

So the next major sub-brick is a BACKWARD simulation stack: `BoolTreeLk` (least predicate, Character
case hardcodes `WP.Forward`) + `ComputeBoolTreeLk` (~200-line least lemma) + `EncodeEqualLkRec` +
`ActionsTreeRepRENested`/`TreeRepRE` + `FindMatchBodyAtCpNested`, each needing a `WP.Backward`/
`LAnc.Backward` twin. `BoolTreeLk` alone has ~378 consumer sites, so this is a large, invasive,
multi-session campaign (either parameterize `BoolTreeLk` by `dir` — big ripple — or add `*Back`
twins). It is deliberately NOT started in a session tail; it needs a focused run. The direction-
generic confinement layer (first stone `BackwardBodyConfinedTree`) and the span side (A) are the parts
that WERE free; the simulation is the wall.

### (GATE side) BREAKTHROUGH — MatchesVTransfer: the gate half sidesteps the wall (green)

The backward-simulation "wall" is only for the CAPTURES (value tie). The GATE side (does the nested
lookbehind PASS? = oracle correctness) is tractable via a DIRECT-backward oracle route, no mirror, no
simulation — and my (A) `SpanDuality*LB` work unblocked it.

`MatchesV` (OracleBridgeV, from the L4 oracle-entry V-work) is the nesting-aware span predicate: it
treats a nested look as a zero-width ORACLE GATE (`view_get_oracle(ov, i, lid)`), direction-generically.
`MatchesVTransfer` (OracleEntry.dfy, NEW, full-file 39/0) proves `MatchesV(re) <==>
MatchesL(Translate(re))` for a nested-lookbehind body (`GroupOkLB` after `Translate`). The look case:
- `MatchesV(look)` = the oracle bit;
- `OracleOkAt` (direction-generic, `LkDir(lk)`) equates the bit to the body's BACKWARD walk succeeding
  (new helper `OracleOkAtGet` instantiates its per-lid forall; `LookLeaves.dfy`);
- `SpanDuality{Complete,Sound}LB` (my (A) work) equates the backward walk to a body span;
- which is exactly `MatchesL`'s lookbehind clause.

Proof notes: `MatchesVTransfer`/`IterVTransfer` mirror `MatchesTransfer`/`IterTransfer` structurally;
the look case is isolated in `MatchesVLookCase`; the gate chain is `LookGateSpec`, written
WITNESS-BASED (construct/destruct the span witness, never assert existential-equivalence) to sidestep
trigger friction that made the bulk `oracle <==> ∃m` assert flaky full-file.

**This unblocks widening `OracleColumnSpec` (OracleSpec.dfy:353, oracle bit <==> backward walk) from
`LookFreeRE` to nested bodies** — the capstone that `OracleOk`/`StaticOkRE` consume. The remaining
gates there: `MatchesTransfer` (look-free, but the nested route uses `MatchesVTransfer` instead),
`OracleColumnCharacterized` (oracle-build side, "nesting-agnostic" per authors), `TranslateGroupFree`
-> a `GroupOkLB` variant. NEXT: assemble a nested `OracleColumnSpec` from `MatchesVTransfer` +
`SpanDuality*LB`. The CAPTURES/value tie (the backward-simulation wall) stays a separate campaign.

### (GATE side) COMPLETE — OracleColumnSpecNested green (oracle bit <==> backward walk, nested)

The whole GATE half of L5 is now green — the direct-backward oracle route, no mirror, no
simulation. `OracleColumnSpecNested` (OracleEntry.dfy) proves: for a nested-lookbehind body, the
oracle bit at (cp, lid) holds EXACTLY when `Translate(body)`'s BACKWARD walk from cp succeeds. It
is the direct-backward analogue of the look-free `OS.OracleColumnSpec`, and it is what §6.5's
`OracleOk`/`StaticOkRE` consumes for a nested column.

Green chain (all this session, OracleEntry.dfy full-file 43/0):
- `MatchesVTransfer` (MatchesV <==> MatchesL, `74ecdc1`) — the gate transfer, via OracleOkAt + (A).
- `RecorderHitVBackWalk` (RecorderHitV <==> backward walk, `bf21340`) — the value bridge.
- `FBuildOracleCorrectAtNested` (oracle bit <==> ReachesWriteV, `846d6fa`) — nested oracle-build
  correctness, off `FBuildOracleCorrectAboveNested` + `LidReachesVFinal`; + `LookTablesLidDirForwardNested`.
- `OracleColumnSpecNested` (oracle bit <==> backward walk, `a8a06f1`) — the capstone, composing the
  above with the L4 V-work bridges (`ReachesWriteVToMatchesV`/`MatchesVToReachesWriteV`,
  `MatchesVRemoveCapture`).

**What remains for L5:**
1. WIRE `OracleColumnSpecNested` into the actual `OracleOk`/`StaticOkRE` establishment for nested
   lookbehind columns (the L1/§6.5 chain — the look-free path uses `OracleColumnSpec`; point the
   nested path at `OracleColumnSpecNested`). Mechanical-ish.
2. The CAPTURES / value tie (the backward-simulation WALL) — the keystone
   `LkReplayMatchesSpecLBNested` reconstructs the body's actual captures (surface via mirror-of-
   skeleton, inner-look gids via the backward oracle). This is the remaining hard campaign; the gate
   side does NOT need it.
3. Drop `NoPosLookbehindRaw`/`FwdPosLooksL`, wire the `assert false` (LiftSim), §18 perf pass, API.

### (CAPTURES side) the wall, sharpened — the checked-tree mirror is the key

Confirmed from several angles that the captures/value tie needs new tree machinery; the analysis
sharpened WHICH and pointed at the tractable approach:

- The captures for a nested positive lookbehind reduce to CLOSEDNESS of the backward body leaf
  (`FwdPosActsL` gates the L4 capture machinery `BodyTreeAtCpNested` ONLY through the closedness ladder
  `ClosedBelow`/`FirstLeafClosed`; the span/gate side needed no such gate, which is why it went green).
- `FirstLeafClosed`/`FirstLeafClosedNoLk` are `least lemma`s over the FORWARD `BoolTreeLk` (MainTheorem
  has 9 such least-lemmas; ~18 `WP.Forward` sites in the ClosedBelow region). Closedness is
  direction-SYMMETRIC in principle (group open/close balance), but the machinery is forward-tied.
- KEY DISTINCTION (the crux, now correctly placed): the RE-WALK tree (`ComputeTr`) does NOT mirror for
  nested looks (proven — before-p vs after-p). But the CHECKED tree (`BoolTreeLk`, whose look nodes are
  ORACLE gates via `LkGateOk`, not re-walks) SHOULD mirror, because oracle bits are position-consistent
  across `MirrorView`. So the previous "gate in `TreeMirrorRel`" resolution was right — for the CHECKED
  tree, not the re-walk tree.

**Approach for the captures campaign (next):** build the CHECKED-tree mirror — give `TreeMirrorRel`
(TreeMirror.dfy, linden-reasoning) an `LK`/`LKFail` case = oracle-gate agreement (via `MirrorView`) +
continuation mirror, body sub-trees EXCLUDED; extend `ComputeTreeReverse` for oracle-gated trees. Then
the backward closedness/captures for a nested positive lookbehind body reuse the FORWARD closedness via
this mirror (the oracle gates make it valid where the re-walk mirror fails), instead of building a
~200-line backward `ComputeBoolTreeLk` twin from scratch. Then widen `BodyTreeAtCpNested` off
`FwdPosLooksL` (only the closedness gate needs it), assemble `LkReplayMatchesSpecLBNested`, and finally
lift `NoPosLookbehindRE` through `OracleColumnNested`/`OracleOkRowsNested`/`MainTheorem` (wiring in both
the gate atoms already green AND the captures). This is the endgame; it needs a fresh focused session.

### (CAPTURES campaign) STARTED — independent re-derivation confirms the oracle-gated mirror

Re-scouted the whole value tie from scratch this session and INDEPENDENTLY confirmed the
architecture (was worried the earlier note conflated `LkGateOk` with the oracle):

- **Gate agreement is ORACLE-based, NOT span-based.** Tried `MatchesLReverse` (SpanDuality:372,
  the span-side mirror) as the inner-look gate-agreement source: it DIES for nested looks by the
  SAME direction-flip. `RevL(LookBehind(r1)) = LookBehind(RevL(r1))` (no flip), so on `Reverse(str)`
  a mirrored lookbehind reads span `[m', n-i)` = chars AFTER i in the original, while the original
  lookbehind read chars BEFORE i. The span mirror `MatchesLReverse` requires `GroupOkL` (look-free)
  precisely because of this — it CANNOT widen to nested lookbehinds. So the inner-gate agreement must
  come from the ORACLE: `MirrorView(ov,n)[n-i] == ov[i]` (position-consistent, NO flip), and
  `OracleOkAt` (direction-generic, `LkDir`) ties each side's bit to the body's LkDir-walk. This
  settles the LOCATION: the nested tree mirror lives in linden-EQUIV (needs the oracle), not
  reasoning.

- **The LK fold is confinement-safe.** `TreeRes(LK(lk,tlk,tc), gm, inp, dir)` for positive `lk`
  threads the inner body's first-leaf gm `pair.1` into the continuation `tc`. Since the inner body
  writes only `LkBodyGroups` (=Sin), `pair.1` agrees with `gm` OUTSIDE Sin — so the SURFACE part of
  the fold is independent of inner captures (`LkConfinedTreeK`, direction-generic). Gate re-eval at
  the fold gm matches the node type (LK vs LKFail) by `ComputeTrGmIndepLkRec` (nested gm-independence,
  already used by `LkReplayMatchesSpecNested`).

**BRICK PLAN (new file `src/Equiv/TreeMirrorLk.dfy`, module `LindenElkTreeMirrorLk`):**
1. `TreeMirrorRelLk(t, tm, Sin)` — `TreeMirrorRel` + LK/LKFail cases (same `lk`, continuation mirror,
   inner subtrees EXCLUDED); `(LK,LKFail)` mixed = false (encodes gate agreement structurally).
2. `TreeResMirrorLk` — the surface leaf fold: outside Sin, `TreeRes(t,Backward)` ~ `TreeRes(tm,Forward)`
   under `MirrorGm`, given confinement + `CloseDiscLk`.
3. `ComputeTrReverseLk` — the tree BUILDER: `ComputeTr(nested tr, Backward)` ~TreeMirrorRelLk~
   `ComputeTr(RevL(tr), Forward)`, discharging each inner-look gate agreement via the oracle
   (`OracleOkAt` + `MirrorView`). THE hard brick.
4. `BackBodyGmTieNested` — compose 2+3 → surface leaf mirror (analogue of `BackBodyGmTie`).
5. `LkReplayMatchesSpecLBNested` — surface via 4 + inner via the backward oracle reconstruction.
6. Wire into MainTheorem; lift `NoPosLookbehindRE`.

### (CAPTURES campaign) SESSION PROGRESS — foundation + crux GREEN (5 commits)

New file `src/Equiv/TreeMirrorLk.dfy` (module `LindenElkTreeMirrorLk`), full-file 19/0:
- **B1 `TreeMirrorRelLk(t,tm,Sin)`** — the LK-extended mirror relation (LK/LKFail cases: same
  look-kind + continuation mirror, inner sub-trees EXCLUDED; mixed LK/LKFail disallowed ⇒ gate
  agreement is STRUCTURAL). `TreeMirrorRelLkFromRel` lifts the look-free `TM.TreeMirrorRel`.
- **B2 `TreeResMirrorLk`** — the SURFACE leaf fold. Two `TreeMirrorRelLk`-related trees fold to
  leaves that mirror OUTSIDE `Sin`: None-iff, input swap, `GmAgreeOutside(rf.1, MirrorGm(rb.1,n),
  Sin)`. Carries the WEAKER `GmAgreeOutside(gm2, MirrorGm(gm1,n), Sin)` invariant uniformly (not
  exact `gm2==MirrorGm(gm1)`), since inner captures don't mirror. Helpers: `GMUpdateInBounds`,
  `TreeResGmInBounds` (leaf bounds, direction-generic), `ConfinedNoGid`/`ConfinedLeafAgree`
  (confined leaf agrees with input gm outside Sin, via `CC.TreeResPreservesGid`),
  `MirrorGmAgreeOutside`. Aux predicates `CloseDiscLk`, `GActsOutsideSin`, `GateStableLk`.
- **B3a `InnerGateAgree` — THE CRUX, GREEN.** A nested inner look's BACKWARD gate at cp (original)
  == its RevL forward-of-mirror gate at n-cp (reversed). Proof = `OracleOkAtGet(qm)` +
  `OracleOkAtGet(qm', RevL body)` + `MIR.MirrorViewGet` (MirrorView[n-cp]==ov[cp], NO direction
  flip). This is the fact the span/tree walk-mirror provably CANNOT give (confirmed a 3rd way:
  `MatchesLReverse` requires GroupOkL; nested lookbehind reads opposite sides). It de-risks the
  whole builder.
- **B3b-base `ComputeTrReverseLkLookFree`** — depth-0 base: look-free body ⇒ `TM.ComputeTrReverse`
  lifted through `TreeMirrorRelLkFromRel`.

**KEY STRUCTURAL FINDING (unblocks the builder): `SD.RevActs` KEEPS LIST ORDER** (maps each action
pointwise Areg(r)->Areg(RevL(r)); only `Sequence` reorders internally via `SeqList`). So a look
`Areg(LookaroundR(lk,r1))` at list position i has `racts[i]=Areg(LookaroundR(lk,RevL(r1)))` at the
SAME position, evaluated (zero-width) at the SAME starting input on both sides (inp backward,
SwapInput(inp) forward). Therefore the two LK nodes ALIGN, and the gate agreement needed is EXACTLY
`InnerGateAgree`'s conclusion. The builder's LK case is LOCALIZED.

**REMAINING (brick 3b-main + 4 + 5 + 6):**
1. **B3b-main `ComputeTreeReverseLk`** — the fuel recursion. MECHANICAL COPY of reasoning's
   `ComputeTreeReverse` (TreeMirror.dfy:123-270, ~150 lines) into equiv, changing (a) ensures
   `TreeMirrorRel`->`TreeMirrorRelLk(_,_,Sin)`, (b) requires `GroupOkActs`->a nested-fragment/GroupOkLB
   acts predicate, (c) each recursive call ->`ComputeTreeReverseLk`, (d) the `case LookaroundR(lk,r1)
   => assert false` -> the REAL case: both trees produce `LK(lk,tlk,tc)` or both `LKFail(lk,tlk)`
   (gate agreement from the hypothesis), continuation via `ComputeTreeReverseLk(cont,...)`, inner
   sub-trees tlk EXCLUDED. **Recommended: state the gate agreement as an ABSTRACT hypothesis**
   `RegLookGatesMirror(r, rer)` (structural over r: at each look (lk,r1), `forall inp2 ::
   TreeRes(ComputeTr([Areg(r1)],inp2,Empty,LkDir)).Some? == TreeRes(ComputeTr([Areg(RevL(r1))],
   SwapInput(inp2),Empty,LkDir)).Some?`, recursing into r1) lifted to `ActsLookGatesMirror(acts)`.
   Inherited trivially by sub-regexes/cont. Keeps the builder recursion PURE (no oracle/lids).
2. **B3b-discharge** — `ActsLookGatesMirror` from the oracle: for each look body, `forall inp2` gate
   agreement via `InnerGateAgree` (needs qm/qm' with matching lids + `OracleOkSuffix` original AND
   mirror). This is where oracle+lids enter, SEPARATED from the builder.
3. **B4 `BackBodyGmTieNested`** — compose B3b + `TreeResMirrorLk` ⇒ surface leaf mirror (analogue of
   `LBV.BackBodyGmTie`).
4. **B5 `LkReplayMatchesSpecLBNested`** — engine wire: SURFACE via B4 + T2a engine mirror
   (`BackwardReplayMirrorNested`) + forward `BodyTreeAtCpNested` on RevRE(body); INNER-look gids via
   the backward oracle reconstruction (the L4 `LkReplayMatchesSpecNestedFull` recon_inner pattern,
   direction-generic).
5. **B6** — wire into MainTheorem, lift `NoPosLookbehindRE`, drop `assert false` (LiftSim), perf, API.

### (CAPTURES campaign) BRICK 1 (the builder) COMPLETE — the nested tree mirror is green

`ComputeTrReverseLk` (TreeMirrorLk.dfy, full-file 48/0) proves the nested backward spec tree mirrors
the forward RevL spec tree (`TreeMirrorRelLk`), given the STRING-RELATIVE gate hypothesis
`ActsLookGatesMirror(acts, rer, str)`. Fuel helper `ComputeTreeReverseLk` (copy of reasoning
`ComputeTreeReverse` + `LookaroundR` case using `LookGateAgree`) + fuel-free wrapper. Guarded-only
ensures (both-Some ⇒ rel) sidesteps body None-iff. **KEY CORRECTNESS FIX:** the gate hypothesis MUST
be string-relative (`forall cp' ≤ |str| :: GateAgree at InpOfCp(str, cp')`) — the earlier `forall
inp2` form is UNSATISFIABLE for depth ≥ 2 (a nested inner look's re-walks genuinely disagree at
arbitrary inputs). Threaded `str, cp0` (inp == InpOfCp(str, cp0)) through the builder.

**REMAINING (bricks 2-5, each a scoped chunk):**
- **B4 `BackBodyGmTieNested`** = `ComputeTrReverseLk` + `TreeResMirrorLk` at gm1=gm2=Empty, O={}.
  `TreeResMirrorLk` needs these tree properties of the ComputeTr backward tree `tB` (and forward
  `tF`), which need FRESH establishment lemmas (structural inductions over ComputeTr, like
  `TreeResGmInBounds`):
  1. `CloseDiscLk(tB, {})` — LK-aware close discipline (analogue of `CD.CloseDiscBody`, +LK case
     recursing the continuation) under `NoDupG`.
  2. `GateStableLk(tB, inpB, Backward)` — gate gm-constancy at each LK node, from
     `ComputeTrGmIndepLkRec` + `LkResultGmIndep`.
  3. `GActsOutsideSin(tB, LkBodyGroups(tr))` — surface group actions ∉ LkBodyGroups (uniqueness).
  4. `LkConfinedTreeK(tB, Sin)` — EXISTS (`BackwardBodyConfinedTree`); forward `tF` via
     `ComputeTrLkConfinedK` at Forward.
  Then B4 composes them → surface leaf mirror `GmAgreeOutside(FirstLeaf(tF).1, MirrorGm(FirstLeaf(tB).1,n), Sin)`.
- **B3b-discharge `RegLookGatesMirror` from the oracle** — recurse over the RegElk `re` (lids live
  there, `qm.looks == LmOf(re)`), at each `Re_lookaround(lid, la, r1)` use `InnerGateAgree` with:
  original `qm` + mirror `qm'` (`qm'.looks == LmOf(RevRE(re))`, `qm'.ov == MirrorView(qm.ov, n)`),
  `OracleColsOk` on both str and rstr. Discharges `forall cp'`. Couples to B5 (mirror-oracle setup).
- **B5 `LkReplayMatchesSpecLBNested`** — SURFACE via B4 + T2a `BackwardReplayMirrorNested` + forward
  `BodyTreeAtCpNested`@RevRE(body) (with MirrorView oracle); INNER-look gids via backward oracle
  reconstruction (L4 `recon_inner` pattern). Establishes B3b-discharge's mirror-oracle hypotheses.
- **B6** — lift `NoPosLookbehindRE` through MainTheorem, drop `assert false` (LiftSim), perf, API.

### (CAPTURES campaign) BRICK 2 (discharge) COMPLETE — bricks 1+2 green

`RegLookGatesMirrorDischarge` (TreeMirrorLk.dfy, full-file 52/0) discharges the builder's gate
hypothesis from the oracle: recurse over the RegElk `re` (via `AR.LmapOk`), at each look use
`InnerGateAgree` with original `qm` + RevRE-mirror `qm'` (`qm'.ov==MirrorView`, bodies via
`TranslateRevRE`); `LookGateDischargeOne` does one look/position (endpoint swap `SD.InputAtSwap`).
Oracle hyps inlined (`forall k :: OracleOkAt`), so TreeMirrorLk.dfy stays independent of the gate
side. So: **the nested tree mirror BUILDS (brick 1) and its gate hypothesis is oracle-DISCHARGED
(brick 2), all green.**

**BRICK 3 (B4 `BackBodyGmTieNested`) — the establishment sub-campaign.** Compose builder
(`ComputeTrReverseLk`) + fold (`TreeResMirrorLk`) at gm1=gm2=Empty, O={}. `TreeResMirrorLk` needs
these tree-property establishments of `tB = ComputeTr([Areg(tr)], inpB, Empty, Backward)` (and
forward `tF`), each a fuel-recursion over `ComputeTree` (like the builder helper, ~120 lines):
- `GateStableLk(tB, inpB, Backward)` — ALL-EQUIV, only needs gm-indep (`ComputeTrGmIndepLkRec` +
  `LkResultGmIndep`); the LK case proves `forall gm :: TreeRes(tlk,gm,inp,LkDir).Some?` (pos) from the
  node being LK (gate gm-constant). NO NoDupG. Easiest — start here.
- `GActsOutsideSin(tB, LkBodyGroups(tr))` — surface GroupActionT gids ∉ LkBodyGroups; needs
  `NoDupG(DefGroups(tr))` (surface gids disjoint from inner). Track surface-gid-outside-Sin through
  the recursion.
- `CloseDiscLk(tB, {})` — LK-aware close discipline. The look-free `CD.CloseDiscBody`
  (CloseDiscEstablish.dfy, reasoning) delegates to `CloseDiscComputeTr` (a fuel recursion, requires
  GroupOkL); widen THAT to the nested fragment + add the LK case (recurse continuation, inner
  excluded) — a cross-project edit to linden-reasoning, OR write a fresh equiv twin.
- `LkConfinedTreeK(tB, Sin)` — EXISTS (`BackwardBodyConfinedTree`); forward `tF` via
  `ComputeTrLkConfinedK`@Forward on `RevL(tr)` (with `LkBodyGroups(RevL(tr))==LkBodyGroups(tr)`).
All establishments are direction-generic → apply to `tB`@Backward AND `tF`@Forward(RevL(tr)). Then B4
composes → surface leaf mirror. Then B5 (engine wire + mirror-oracle setup discharges B2's hyps), B6.

### (CAPTURES campaign) B4 establishments 2/3 green — GateStableLk + GActsOutsideSin

TreeMirrorLk.dfy full-file 73/0. Two of the three B4 tree-property establishments landed (both fuel
helper + fuel-free wrapper, mirroring `ComputeTree` case-for-case):
- `ComputeTrGateStable` — `GateStableLk(ComputeTr([Areg(tr)],...), inp, dir)` for `PikeLkRegexRec(tr)`.
  LK case = `LookGateStableAt`, needs ONLY `LkResultGmIndep` (unconditional). Clean.
- `ComputeTrGActsOutside` — `GActsOutsideSin(ComputeTr(...), Sin)` given `RegOpensOutside(tr, Sin)`.
  **Also fixed a latent vacuity: `GADisjoint`'s `Reset` case is now `true`** (a quantifier over a
  nested look resets inner gids ∈ Sin — harmless for `O!!Sin`; only `Open` needs `g∉Sin`). Fold
  re-verified. `RegOpensOutside`/`ActsOpensOutside` predicates + threading helpers added.

**Remaining for B4:**
- **`CloseDiscLk` establishment (the heavy one)** — needs the `StackInv`/`ClosesActs`/`HeadsFresh`/
  `HeadsNoDupDefs` invariant machinery from reasoning's `CloseDiscEstablish.dfy` (`CloseDiscComputeTr`
  requires `StackInv` = `NoDupG(ClosesActs) && HeadsFreshOfCloses && HeadsNoDupDefs && GroupOkActs`).
  Two routes: (a) fresh EQUIV twin replicating that machinery + the LK case (recurse continuation) —
  ~200 lines but the fuel pattern is proven; (b) widen reasoning's `CloseDiscComputeTr` to the
  fragment + add LK case, but it produces reasoning's `CloseDisc` not equiv's `CloseDiscLk`, so a
  bridge or a reasoning-side `CloseDiscLk` is needed. Route (a) is cleaner.
- **`RegOpensOutside(tr, LkBodyGroups(tr))` from `NoDupG(DefGroups(tr))`** — surface Group gids ∉
  LkBodyGroups (partition under NoDupG). Structural induction; check for an existing L4 "surface ∩
  LkBodyGroups = ∅" lemma first.
- **B4 `BackBodyGmTieNested`** — compose: builder (`ComputeTrReverseLk`, needs `RegLookGatesMirror`
  from brick 2's discharge) + `ComputeTrGateStable`×2 (tB, tF) + `ComputeTrGActsOutside`(tB) +
  `BackwardBodyConfinedTree`(tB) + `ComputeTrLkConfinedK`@Forward(tF) + `CloseDiscLk`(tB) →
  `TreeResMirrorLk` → surface leaf mirror `GmAgreeOutside(FirstLeaf(tF).1, MirrorGm(FirstLeaf(tB).1,n), Sin)`.
Then B5 (engine wire + discharge brick 2's mirror-oracle hyps), B6 (integration).

### (CAPTURES campaign) BRICKS 1+2+3 COMPLETE — the SPEC-SIDE nested tree mirror is done

TreeMirrorLk.dfy full-file **98/0**. The entire spec-side is green:
- **B1 builder** `ComputeTrReverseLk` (+ relation `TreeMirrorRelLk`, fold `TreeResMirrorLk`, cruxes
  `InnerGateAgree`/`LookGateAgree`).
- **B2 discharge** `RegLookGatesMirrorDischarge` — the builder's gate hypothesis from the oracle
  (via `AR.LmapOk` + RevRE-mirror `qm'`).
- **B3 (B4) composition** `BackBodyGmTieNested` — the SURFACE leaf mirror
  `GmAgreeOutside(FirstLeaf(tF).1, MirrorGm(FirstLeaf(tB).1, n), Sin)`. Composes the builder + all
  three establishments (`ComputeTrGateStable`, `ComputeTrGActsOutside`, `ComputeTrCloseDiscLk` — the
  last replicating CD's `StackInv`/`ClosesActs` machinery with `PikeLkActionsRec` + the LK case) +
  confinement (`BackwardBodyConfinedTree` tB, `ComputeTrLkConfinedK`@Forward tF via `LkBodyGroupsRevL`)
  + the fold. Discharges: `RegOpensOutsideFromNoDup` (surface Opens avoid LkBodyGroups under NoDupG).
  Fixed TWO latent vacuity bugs (string-relative gate hyp; `GADisjoint` Reset).

**REMAINING (bricks 4-5 = B5, B6):**
- **B5 `LkReplayMatchesSpecLBNested`** — the ENGINE WIRE. Nested analogue of the depth-1
  `LBK.LkReplayMatchesSpecLB` (LookBehindKeystone.dfy). SURFACE tie: `BackBodyGmTieNested` (B4) +
  the engine mirror `BV.BackwardReplayMirrorNested` (T2a) + forward `M.BodyTreeAtCpNested` applied to
  `RevRE(body)` on `rstr` with `MirrorView(ov)` (ties rfF to FirstLeaf(tF)). This ALSO establishes
  B2's mirror-oracle hypotheses (compile `RevRE(body)` → `qm'`, `LmapOk(RevRE(body), qm')`,
  `OracleColsOk(qm', rstr)` via a MirrorView oracle-correctness transport). INNER-look gids: the
  backward oracle reconstruction (L4 `recon_inner`/`FLookLoop` pattern, direction-generic) — the
  separate inner half, as in the L4 forward keystone. Then wrap `BackFreshBodyGmTie`-style at cap=init.
  Large (couples to compilation + engine mirror infra), but the spec-side surface tie it needs is DONE.
- **B6** — lift `NoPosLookbehindRE` through `OracleColumnNested`/`OracleOkRowsNested`/`MainTheorem`,
  wire the green gate atoms (`OracleColumnSpecNested`) + the captures (`LkReplayMatchesSpecLBNested`),
  drop the `assert false` (LiftSim), §18 opaque-at-source perf pass, API (`ApiMatch`/`Supported`).

### (CAPTURES campaign) BRICK 4 (B5) ANALYZED — the crux is MIRROR-ORACLE CORRECTNESS

Studied the depth-1 keystone `LBK.LkReplayMatchesSpecLB` + `LBEngineLeaf` in full. Structure of B5
(nested engine wire):
- ENGINE: `BV.BackwardReplayMirrorNested` (T2a, DONE) — backward run raB of `reverse_regex(body)` =
  mirror of forward run rfF of `RevRE(body)` on rstr with `MirrorView(ov)`.
- ENGINE↔SPEC: forward `M.BodyTreeAtCpNested` applied to `RevRE(body)` — ties rfF to `FirstLeaf(tF)`
  (surface). REQUIRES `OracleOkSuffix(rer, qm', InpOfCp(rstr, mcp))` for the compiled `qm'` of
  `RevRE(body)`.
- SPEC: `BackBodyGmTieNested` (B3, DONE) — `FirstLeaf(tF)` surface ~ `MirrorGm(FirstLeaf(tB))`.
- Compose + `LkResult` fold (`ComputeTrGmIndepLkRec` + `TreeResGmFrameRec`) → surface value tie.

**THE CRUX (the one hard new piece): `OracleOkSuffix(qm', RevRE(body))` — the MIRROR-ORACLE
CORRECTNESS.** For depth-1 it is TRIVIAL: `RevREStaticOk` builds `qm'.looks == map[]` (look-free ⇒
no looks ⇒ vacuous). For NESTED, `RevRE(body)` HAS looks, so this is a real obligation, and:
- It is NOT derivable from `InnerGateAgree` — that is CIRCULAR (`InnerGateAgree(cp)` requires
  `OracleOkAt(qm', n-cp)`, exactly what we're proving).
- It IS a DEPTH-STRATIFIED induction on `NestDepth(body)`: `OracleOkAt(qm', InpOfCp(rstr, k))` for
  body's look `lid` (body `body_lid`) reduces (via `MirrorViewGet` + original `OracleOkAt(qm, n-k)`)
  to the gate agreement `backward-walk(Translate(body_lid))@(n-k) <==> forward-walk(RevL Translate
  body_lid)@k` = `BackBodyGmTieNested(Translate(body_lid))`'s None-iff — which needs
  `ActsLookGatesMirror(Translate(body_lid))`, discharged by `RegLookGatesMirrorDischarge(body_lid)`,
  which needs the mirror-oracle for body_lid's OWN (deeper) looks = **`MirrorOracleOk(body_lid)`, the
  IH one nesting level down.** Base: look-free inner (vacuous; the surface reads mirror via
  `MatchesLReverse`).
- **SUBTLETY to resolve first:** `RegLookGatesMirrorDischarge`/`InnerGateAgree` currently require the
  FULL `OracleColsOk(qm', rstr)` (a forall over ALL of `qm'.looks`), but the IH only gives body_lid's
  looks. Re-state brick 2's oracle requirement as REGEX-SCOPED (only the looks IN the regex being
  discharged) so the IH suffices. Small refactor of brick 2.
- `MirrorOracleOk` can live in TreeMirrorLk.dfy — it needs only `BackBodyGmTieNested`,
  `RegLookGatesMirrorDischarge`, `MIR.MirrorViewGet`, `LL.OracleOkAt`, `AR.LmapOk` (all present, no
  MainTheorem dependency). The ENGINE wire (`LkReplayMatchesSpecLBNested` itself) goes in a NEW file
  including TreeMirrorLk + MainTheorem/keystone infra (like LookBehindKeystone.dfy), and consumes
  `MirrorOracleOk` + `BackBodyGmTieNested` + T2a + forward `BodyTreeAtCpNested`.

NEXT: (1) refactor brick 2 to regex-scoped oracle correctness; (2) prove `MirrorOracleOk` (depth
induction) in TreeMirrorLk.dfy; (3) build `LkReplayMatchesSpecLBNested` engine wire in a new file;
(4) B6 integration.

### (CAPTURES campaign) ⚠️ CRITICAL CORRECTION — the nested tree mirror (bricks 1-3) is VACUOUS

While building B5 I discovered — and PROVED (`GateAgreeIsFalse`, verified) — that the whole
spec-side nested tree mirror this session rests on an UNSATISFIABLE hypothesis:
- `GateAgree(rer, LookBehind, r1, inp2)` compares `backward-walk(r1)@inp2` to
  `backward-walk(RevL(r1))@SwapInput(inp2)`. **`SD.SwapInput` merely swaps pref<->next**, so the
  RevL-side backward read hits `inp2.next[0]` (the char AFTER the point) while the original hits
  `inp2.pref[0]` (the char BEFORE) — opposite sides. Disproved concretely for a single Character
  body: at `Input(['b'],['a'])` the LHS reads 'a' (Some) and the RHS reads 'b' (None).
- Hence `RegLookGatesMirror`/`ActsLookGatesMirror` are FALSE for any nested capturing lookbehind, and
  `ComputeTrReverseLk`, `RegLookGatesMirrorDischarge`, `InnerGateAgree`, `LookGateAgree`, and
  `BackBodyGmTieNested` are all VACUOUS (they verified only because the premise can't be satisfied).
- This is EXACTLY the documented dead-end (`4b829b9`): the ComputeTr RE-WALK tree cannot mirror for
  nested looks — I built on the WRONG tree. `LkGateOk` in `BoolTreeLk` ALSO re-walks (not the oracle),
  so BoolTreeLk doesn't mirror either. The only tree whose inner gates are position-consistent oracle
  bits is the ENGINE tree (`tstar`/`TreeRepRE`), and its mirror IS the engine mirror T2a
  (`BackwardReplayMirrorNested`).

**SOUND / SALVAGEABLE (mirror-independent):** the tree-property establishments `ComputeTrGateStable`,
`ComputeTrGActsOutside`, `ComputeTrCloseDiscLk` (+ `StackInvLk` twin of CD), confinement
`LkBodyGroupsRevL`, `RegOpensOutsideFromNoDup`, `TreeResGmInBounds`, `ConfinedLeafAgree`,
`MirrorGmAgreeOutside`, `RevLPreservesPikeLkRec`, `LookGateStableAt`. These are general ComputeTr-tree
facts, reusable for the correct route.

**THE CORRECT ROUTE (re-affirmed):** SURFACE captures via the ENGINE mirror (T2a — the oracle-gated
checked-tree mirror at the engine level) + INNER-look gids via the direction-generic BACKWARD ORACLE
at ORIGINAL positions (no RevL mirror). Connecting the backward engine run `raB` (of
`reverse_regex(body)`, oracle `ov`) to the spec `LkResult(tB)` needs a DIRECT backward
engine<->spec-backward-tree tie — the "wall" (a `WP.Backward` twin of the L4 forward
`BodyTreeAtCpNested`/`BooleanCorrectLkRec`/`ActionsTreeRepRENested` sim), NOT any RevL/ComputeTr
mirror. That backward-simulation stack is the genuine remaining L5 captures work; this session's
tree-mirror tower does not shortcut it.

[**SUPERSEDED 2026-08-24** — the "backward-simulation wall" conclusion above was itself wrong, or
rather unnecessary: the mirror idea was right and the missing ingredient was the look-KIND FLIP.
See the next section.]

---

## L5 CAPTURES — THE FLIP ROUTE (2026-08-24): the dead-end diagnosed, the wall dissolved, F0 green

**The one-sentence diagnosis.** Every mirror attempt (and the `GateAgreeIsFalse` disproof) used a
kind-PRESERVING reversal (`RevL`/`XRev` keep `Lookbehind` a `Lookbehind`) — inherited from the
engine's `reverse_regex` — under which a mirrored inner look re-walks in the SAME intrinsic
direction over the swapped window and reads the OPPOSITE side of the point. But **the main bytecode
is look-kind-blind**, so that inheritance was an illusion: the spec reversal is free to FLIP
`Lookbehind <-> Lookahead` (the classical duality), under which the mirrored walk reads the SAME
chars and the tree mirror is TRUE. The engine keeps its no-flip reversal; a single compile-level
equation bridges the two.

**Code-validated facts (4-agent recon, file:line):**
1. `CP.compile`'s lookaround case (regex-engine Compiler.dfy:160-165) emits token-identical
   `CheckOracle(lid)` for Lookahead/Lookbehind (`NegCheckOracle` for both negatives); the body never
   enters the main stream; label cost `+1` uniformly; the instruction datatype has no direction
   field. Proof-side twin: NfaRepRE.dfy:1539-1545 (the roadmap's old `:1193-1199` cite was stale).
   Kind survives only in tables (`f_look_types`, `oracle_regex`/`capture_regex` reversal insertions)
   and interpreter dispatch (`oracle_direction`/`capture_direction`).
2. The L4 forward keystone chain is kind-agnostic and semantic-oracle-only:
   `BodyTreeAtCpNested` (MainTheorem.dfy:3836) requires `StaticOkNestedRE` + `NegLooksLookFreeRE` +
   `SizesOkRE` + SEMANTIC `OracleOkSuffix` — NO `NoPosLookbehind`, NO build-level oracle facts, no
   run hypothesis. `LkReplayMatchesSpecNested`:9642's `la.Lookahead?` (:9657) restricts only the
   OUTER replay direction. `FwdPosLooksL`/`FwdPosActsL` are `requires` in EXACTLY 3 lemmas (the
   closedness ladder, :2216/:2257/:2630) with a single caller `MainExtractionNested`:10280.
3. `OracleOkAt` (LookLeaves.dfy:1685) is direction-generic per-lid (`L.LkDir(lk)`); the depth-1 LB
   keystone dodges it VACUOUSLY (`RevREStaticOk` builds `qm'.looks == map[]`,
   LookBehindKeystone.dfy:273) — THE precise nested break point, repaired by the flip
   (`MirrorViewGet`: bit at `n-cp` of `MirrorView` IS `ov[cp]`; the flipped walk reads the same
   chars as the original at `cp`).
4. T2a `BackwardReplayMirrorNested` (BackValue.dfy:159) has NO fragment premise — fully general.
   `SD.ReadCharSwap` (SpanDuality.dfy:531) is the flip transport at the char level: the look-free
   mirror `TM.ComputeTreeReverse` was ALWAYS the flip mirror restricted to bodies with nothing to
   flip; the vacuous no-flip LK case was the one addition that broke its own transport pattern.
5. Depth-1 degeneration: `FlipRE` is the identity on look-free bodies, so the flip route restricts
   EXACTLY to the proven `LkReplayMatchesSpecLB` architecture.

**F0 GREEN (`src/Equiv/FlipRev.dfy`, 18/0, first try):** `FlipLk`/`FlipL`/`FlipRE` +
involutions/laws (LkDir flips, Positivity preserved), `FlipReverseComm`/`FlipSwapAnchorsComm`,
`FlipTransWf`/`TranslateFlip`, **`FlipCompile`/`FlipCompileToBytecode`/`FlipCompileToWrite`**
(compile equality — the wedge), and **`FlipGateAgreeAtDeadEndWitness`** (the flip gate agreement is
TRUE at the exact `GateAgreeIsFalse` witness) + `FlipGateAgreeCharacter` (every input, Character
body).

**The keystone chain (surface):** raB =[T2a]= rfF over `compile(XRev(body))` =[F0]=
`compile(FlipRE(XRev(body)))` =[L4 fwd keystone at the FLIPPED body — its looks are
Lookahead-flavoured, its oracle premise discharged by the new non-circular `MirrorOracleOkNested`]=
`FirstLeaf(tF')` =[the FLIP tree mirror F1/F2 — full `MirrorGm` equality, inner captures
included]= `MirrorGm(FirstLeaf(tB))`. Inner-look gids: the direction-generic recon_inner seam at
original positions (NestDepth recursion), unchanged. The B5 circularity (MirrorOracleOk needed the
mirror which needed MirrorOracleOk) is GONE: the flip mirror is oracle-free/structural.

**Scope v1 = the green gate side's scope:** bodies `NestedFragmentRE` + `NegLooksLookFreeRE` with
lookbehind-only nesting (`GroupOkLB` — matching `OracleColumnSpecNested` and `MatchesL`'s
lookbehind-only look clause, SpanDuality.dfy:120-128). Covers `(?<=a(?<=b)(c))`. For this scope
every inner sub-walk is Backward↔Forward, so F1 needs NO direction-parametrization. Mixed nesting =
a later rung (MatchesL lookahead clause + the twin orientation).

**Brick plan F1–F7, sizes, ordering, and the anti-vacuity discipline (every mirror lemma ships with
an instantiation witness; no agreement hypotheses — the LK case is proven, not assumed): see
`L5_HANDOFF.md` §5 (rewritten this session).** The backward-simulation stack (`BoolTreeLk` twins,
~378 consumers) is SHELVED as a dominated fallback (§5.5).

### FLIP ROUTE EXECUTED — F0–F5 GREEN, THE KEYSTONE IS PROVEN (2026-08-24, session 2)

Six new files, every brick committed on green, each within 0–1 fix iterations:
- `FlipRev.dfy` 18/0 — F0 (flips, `FlipCompileToBytecode`, cured witness).
- `FlipMirror.dfy` 32/0 — F1: `TreeMirrorRelF` (REAL LK/LKFail cases, full sub-tree recursion),
  `TreeResSomeMirrorF` (gm-blind success — the gate verdict, no oracle), fuel transport,
  **`ComputeTreeReverseF`/`ComputeTrReverseF`** (the builder; LookaroundR arm PROVEN),
  `FlipMirrorSatisfiableNested` (anti-vacuity witness), `CloseDiscF`/`AvoidsCR`/`CloseDiscFWiden`/
  `GActsIn`/`TreeResPreservesOpen`, **`TreeResMirrorF`** (exact-`MirrorGm` value fold, inner captures
  included).
- `FlipDisc.dfy` 14/0 — F1c establishment (`ComputeTreeCloseDiscF` = TML's + extended LK case) +
  **F2 `BackBodyGmTieFlip`**.
- `FlipOracle.dfy` 8/0 — **F3 `MirrorOracleColsOk`** (the B5 circularity is dead) + `ColsOkToSuffix`.
- `FlipStatics.dfy` 39/0 — F4 (`XRevIsRevRENested`, `TranslateFlipXRev`, preservation family,
  `FXRCompileFacts`, `FlipLooksMap`/`LmapOkFlipXRev`, `GmOfLiveFXR`, `LBOnlyLooksRE` bridges).
- `FlipKeystone.dfy` 1201/0 — **F5 `LkReplayMatchesSpecLBNested`** (+ `FlipXRevStaticOkNested`,
  `LBEngineLeafFlip`), first try.

The route's soundness is now EMPIRICALLY confirmed end-to-end at the keystone: the value tie the
old plan priced as an XL backward-simulation campaign closed as ~1,900 lines of additive, first-try
bricks. Remaining: F6 (gate step at the LiftSim D5 dead arm + inner gids) and F7 integration —
`L5_HANDOFF.md` §5.6 has the exact pointers and the keystone's consumer contract (note: it needs
ALL-columns oracle correctness, `OE.OracleColsOk`, not a from-cp suffix — the backward body reads
positions ≤ cp).

### L5 F6 GREEN (2026-08-25): the keystone in the backward run's OWN registers; F7 sized honestly

- `FlipGate.dfy` (**1294/0 + 407/0, both first try**): `BackFreshCoreNested` (T2a+F0 core — rfF ==
  MirrorThread(raB), caps involution, wf, readout congruence), **`BackFreshBodyGmTieNested`** (F6a —
  the nested twin of `LBK.BackFreshBodyGmTie`: `SwapGm(LkResult) ~ GmOfLive(body, raB.*)` on the
  surface gids), `CapIdsInLooksFXR`, **`FreshBodyMatchGmOuterLBNested`** (F6b — inner gids are never
  live in the fresh backward match; via the mirror's shared clock bank because
  `MainMatchInsideCapsInitNested` is Forward-only), **`GateCrossCoverageLBNested`** ((E4) coverage:
  every live body group lands in the gate's LkResult). LiftSim: `ThreadRepLkStepCheckOracleRecLB`
  (F6c — the Forward nested gate step's body verbatim under `LkDir == Backward`; the nested `*Rec`
  path carries no inside tie at the gate, and both ingredients are direction-generic).
- **F7 finding (the important one):** the D5 dead arm has THREE obligations. The gate step and the
  KEY-level (E4) coverage (`LookNestBackTTop`, dispatching through `M.FreshBodyMatch`) are
  direction-generic and now have LB atoms. The VALUE-level (E4 DEEP) coverage is NOT: the deep
  carrier `LookNestBackTTopDeep` goes through **`SubFirstLeafAt` (LiftSim:9230), which builds the
  spec sub-tree with `WP.Forward` hard-wired for every lid** (72 uses in ~25 lemmas/predicates, incl.
  `LiftInvRec`, the descent stack, and `LookNestBackTFromBodyReplay` which requires `la.Lookahead?`).
  F7 is therefore a direction-generalization pass (`dir(l)` from `f_look_types[l]`; spec-to-spec, no
  SwapGm in the carrier itself) + the scope lift + all-columns oracle plumbing + the closedness
  ladder LB case — F7a–F7g in `L5_HANDOFF.md` §5.7, multi-session.
