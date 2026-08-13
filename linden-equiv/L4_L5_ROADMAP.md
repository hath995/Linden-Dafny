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
