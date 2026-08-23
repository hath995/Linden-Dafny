// Lookaround campaign (L1), oracle theorem part C3 (§6.2 of
// LOOKAROUND_CAMPAIGN.md): the FBuildLids assembly.
//
// FBuildOracle runs one FFindMatch sweep per lid, maxlook down to 1,
// threading the oracle view. For a lid-unique lookbehind-fragment regex the
// per-lid ingredients line up as follows:
//
//   - LookTablesOk (FFullCompilationLookOk) identifies the build bytecode as
//     compile_to_write(oracle_regex(la, body), lid);
//   - the fragment makes la a lookbehind, so oracle_direction is Forward and
//     init_cp is 0, and the body is capture-free, so oracle_regex collapses
//     to lazy_prefix(body) (RemoveCaptureFreeId);
//   - CompileToWriteClassified classifies the build code (no oracle reads,
//     no CheckNullable, no Accept, WriteOracle(lid) only);
//   - SweepCharacterization (soundness + completeness, PR #1) characterizes
//     the lid's own column: bits before ∪ ReachesWrite positions;
//   - FindMatchOracleFrame keeps every other column untouched, so the
//     per-lid results commute across the FBuildLids recursion;
//   - lids OUTSIDE LookIds(re) (if any) still carry the seed tables' empty
//     bytecode (FCompileExtraLookFrame), and an empty-code sweep writes
//     nothing while ReachesWrite over empty code is false — the same
//     characterization formula covers them with no case split.
//
// The result, FBuildOracleCorrect: after FBuildOracle, column lid holds
// EXACTLY the ReachesWrite positions of that lid's build bytecode (the
// init_view start is all-false). FBuildOracleCorrectAt restates it per
// lookaround with the bytecode in its lazy_prefix(body) form — the interface
// for the §6.3 bridge.
include "NfaRepRE.dfy"
include "LookTables.dfy"
include "OracleReach.dfy"
include "Mirror.dfy"

/** The `FBuildLids` assembly: after the oracle build, each lid's column
    holds exactly the `ReachesWrite` positions of its (classified, forward)
    build bytecode. */
module LindenElkOracleBuild {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import RC = Charclasses
  import NR = LindenElkNfaRep
  import LT = LindenElkLookTables
  import OS = LindenElkOracleSweep
  import ORc = LindenElkOracleReach
  import MIR = LindenElkMirror
  import LC = Chars

  // ===========================================================================
  // Small facts
  // ===========================================================================

  /** Empty code reaches no `WriteOracle` — every fetch reads `Fail`. */
  lemma ReachesWriteEmpty(str: string, cp0: int, lid: int, cp: int)
    ensures !ORc.ReachesWrite([], str, cp0, lid, cp)
  {
    assert forall pc: nat :: RB.get_instr([], pc) == RB.Fail;
  }

  /** `lazy_prefix` adds only a dot-star head, preserving look-freedom. */
  lemma LookFreeLazyPrefix(body: R.regex)
    requires NR.LookFreeRE(body)
    ensures NR.LookFreeRE(R.lazy_prefix(body))
  {
  }

  /** A look-free regex has no lookaround ids. */
  lemma LookFreeNoIds(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures LT.LookIds(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeNoIds(r1); LookFreeNoIds(r2);
    case Re_con(r1, r2) => LookFreeNoIds(r1); LookFreeNoIds(r2);
    case Re_quant(_, _, _, r1) => LookFreeNoIds(r1);
    case Re_capture(_, r1) => LookFreeNoIds(r1);
    case _ =>
  }

  /** `FCompileExtra` never touches the main-ast field, so
      `FFullCompilation(r).f_main_ast == r` (the fold only updates the
      per-lid and per-plus tables). */
  lemma FCompileExtraMainAst(r: R.regex, c: CP.FCompiled)
    ensures CP.FCompileExtra(r, c).f_main_ast == c.f_main_ast
    decreases r
  {
    match r
    case Re_empty => case Re_character(_) => case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      FCompileExtraMainAst(r1, c);
      FCompileExtraMainAst(r2, CP.FCompileExtra(r1, c));
    case Re_con(r1, r2) =>
      FCompileExtraMainAst(r1, c);
      FCompileExtraMainAst(r2, CP.FCompileExtra(r1, c));
    case Re_quant(nul, qid, quant, r1) =>
      var c1 := if quant.min > 0 && quant.max == None && nul != R.NonNullable && quant.greedy
                then c.(f_plus_bc := CP.upd(c.f_plus_bc, qid, CP.compile_reconstruct_nulled(r1)))
                else c;
      FCompileExtraMainAst(r1, c1);
    case Re_capture(_, r1) =>
      FCompileExtraMainAst(r1, c);
    case Re_lookaround(lid, la, body) =>
      var c1 := c.(f_look_types := CP.upd(c.f_look_types, lid, la));
      var c2 := c1.(f_look_cdns := CP.upd(c1.f_look_cdns, lid, LCdn.compile_cdns(body)));
      var c3 := c2.(f_look_ast := CP.upd(c2.f_look_ast, lid, body));
      var c4 := c3.(f_look_build_bc := CP.upd(c3.f_look_build_bc, lid, CP.compile_to_write(CP.oracle_regex(la, body), lid)));
      var c5 := c4.(f_look_capture_bc := CP.upd(c4.f_look_capture_bc, lid, CP.compile_to_bytecode(CP.capture_regex(la, body))));
      FCompileExtraMainAst(body, c5);
  }

  /** An epsilon closure over EMPTY code changes nothing but drains `active`:
      every thread reads `Fail` (out-of-range fetch) and dies; nothing blocks,
      nothing is written. */
  lemma AdvanceEmptyCode(s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction)
    requires |s.processed.true_set| == 0 && |s.processed.false_set| == 0
    ensures var (s', ov') := AI.FAdvanceEpsilon([], s, ov, dir);
      ov' == ov && s'.blocked == s.blocked && s'.bestmatch == s.bestmatch
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    assert RB.get_instr([], t.pc) == RB.Fail;
    assert !AI.bpc_mem(s.processed, t.pc, t.exit_allowed);
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(s.processed, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(s.processed, t.pc, t.exit_allowed);
    AdvanceEmptyCode(s1.(active := s.active[1..]), ov, dir);
  }

  /** A whole `FFindMatch` run over EMPTY code leaves the oracle view
      untouched (the initial state has nothing blocked, and the closure
      blocks nothing). */
  lemma FFindMatchEmpty(str: string, s: AI.VmState, ov: LOr.OracleView, dir: LAnc.direction, cdn: LCdn.cdns)
    requires |s.processed.true_set| == 0 && |s.processed.false_set| == 0
    requires s.blocked == []
    requires dir.Forward? ==> s.context.nextchar == AI.get_char(str, s.cp)
    requires dir.Backward? ==> s.context.nextchar == AI.get_char(str, s.cp - 1)
    ensures AI.FFindMatch([], str, s, ov, dir, cdn).1 == ov
  {
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, dir));
    AdvanceEmptyCode(s0, ov, dir);
  }

  // ===========================================================================
  // Per-lid side conditions
  // ===========================================================================

  /** What one `FBuildLids` iteration needs of lid `i`: either the build
      bytecode is empty (a lid with no lookaround — the sweep is a no-op) or
      it is classified for the sweep lemmas and its recorded flavour builds
      FORWARD (a lookbehind). */
  ghost predicate LidBuildOk(crv: CP.FCompiled, i: int) {
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    bc == []
    || (OS.NoOracleReads(bc) && OS.NoCheckNullable(bc) && OS.WritesOnlyLid(bc, i)
        && OS.NoAccept(bc))
  }

  /** L4 GENERALIZATION of `LidBuildOk` (brick 4b). The one clause that nesting
      breaks is `NoOracleReads`: an OUTER lookaround's build code contains
      INNER gates (`CheckOracle`/`NegCheckOracle`) that read the already-built,
      strictly-HIGHER inner columns (`LidsWellNested`). So we RELAX
      `NoOracleReads(bc)` to `OS.AllGatesAbove(bc, i)` — gates are ADMITTED,
      provided every one reads a column strictly above `i`. The other three
      conjuncts are kept verbatim: build code still emits exactly one
      `WriteOracle` (column `i`), no `CheckNullable`, no `Accept`. Since
      `NoOracleReads(bc) ==> AllGatesAbove(bc, i)`
      (`OS.NoOracleReadsAllGatesAbove`), `LidBuildOk` is the gate-free special
      case — see `LidBuildOkImpliesAbove`. This is the side condition the
      high->low build induction (brick 4c) needs at each nested column. */
  ghost predicate LidBuildOkAbove(crv: CP.FCompiled, i: int) {
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    bc == []
    || (OS.AllGatesAbove(bc, i) && OS.NoCheckNullable(bc) && OS.WritesOnlyLid(bc, i)
        && OS.NoAccept(bc))
  }

  /** The gate-free `LidBuildOk` IMPLIES the gated `LidBuildOkAbove`: the only
      changed clause weakens (`NoOracleReads ==> AllGatesAbove(_, i)` for any
      floor `i`, via `OS.NoOracleReadsAllGatesAbove`), the other three are
      identical. This is what lets the whole existing depth-1 chain feed the L4
      form for free — every column that today satisfies `LidBuildOk` satisfies
      `LidBuildOkAbove` unchanged. */
  lemma LidBuildOkImpliesAbove(crv: CP.FCompiled, i: int)
    requires LidBuildOk(crv, i)
    ensures LidBuildOkAbove(crv, i)
  {
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    if bc != [] {
      OS.NoOracleReadsAllGatesAbove(bc, i);
    }
  }

  /** The direction a lid's oracle is built in: Forward for lookbehinds,
      Backward for lookaheads (`AI.oracle_direction`). */
  ghost function LidDir(crv: CP.FCompiled, i: int): LAnc.direction {
    AI.oracle_direction(
      if 0 <= i < |crv.f_look_types| then crv.f_look_types[i] else R.Lookahead)
  }

  /** "The build sweep for lid `i` records a bit at `cp`", for EITHER
      direction. A forward build (lookbehind) is the plain reachability of its
      bytecode over `str`. A BACKWARD build (lookahead) is the reachability of
      the anchor-swapped bytecode over the REVERSED string at the mirrored
      position -- the transport proved in `Mirror.BackwardSweepCharacterization`,
      which is what lets the forward-only reachability layer serve a backward
      sweep. */
  ghost opaque predicate LidReaches(crv: CP.FCompiled, str: string, i: int, cp: int) {
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    if LidDir(crv, i) == LAnc.Forward
    then ORc.ReachesWrite(bc, str, 0, i, cp)
    else ORc.ReachesWrite(MIR.SwapAnchorsCode(bc), LC.Reverse(str), 0, i,
                          MIR.Mirror(cp, |str|))
  }

  /** A BACKWARD build of an ANCHOR-FREE program: its column is the plain
      FORWARD reachability of the SAME program over the reversed string, at
      the mirrored position. No compile/swap commutation is needed, because
      the swap cannot touch a program with no anchors in it.

      This is the form a lookAHEAD's oracle column takes, and it is what lets
      the existing (forward) C4 characterization be pointed straight at it. */
  lemma LidReachesBackwardNoAnchor(crv: CP.FCompiled, str: string, i: int, cp: int)
    requires LidDir(crv, i) == LAnc.Backward
    requires forall pc: nat :: pc < |AI.get_code_v(crv.f_look_build_bc, i)| ==>
               !AI.get_code_v(crv.f_look_build_bc, i)[pc].AnchorAssertion?
    ensures LidReaches(crv, str, i, cp)
        <==> ORc.ReachesWrite(AI.get_code_v(crv.f_look_build_bc, i), LC.Reverse(str),
                              0, i, MIR.Mirror(cp, |str|))
  {
    reveal LidReaches();
    MIR.SwapAnchorsCodeIdent(AI.get_code_v(crv.f_look_build_bc, i));
  }

  /** An empty build program records nothing, in EITHER direction -- provable
      without knowing which, since both disjuncts are about empty code. */
  lemma LidReachesEmpty(crv: CP.FCompiled, str: string, i: int, cp: int)
    requires AI.get_code_v(crv.f_look_build_bc, i) == []
    ensures !LidReaches(crv, str, i, cp)
  {
    reveal LidReaches();
    ReachesWriteEmpty(str, 0, i, cp);
    MIR.SwapAnchorsCodeLen([]);
    assert MIR.SwapAnchorsCode([]) == [];
    ReachesWriteEmpty(LC.Reverse(str), 0, i, MIR.Mirror(cp, |str|));
  }

  /** On the lookbehind fragment every build is Forward, so `LidReaches`
      collapses to the plain forward reachability the L1 chain consumes. */
  lemma LidReachesForward(crv: CP.FCompiled, str: string, i: int, cp: int)
    requires LidDir(crv, i) == LAnc.Forward
    ensures LidReaches(crv, str, i, cp)
        <==> ORc.ReachesWrite(AI.get_code_v(crv.f_look_build_bc, i), str, 0, i, cp)
  { reveal LidReaches(); }

  // ===========================================================================
  // L4 (brick 4c groundwork): the partial-oracle-VIEW per-lid reachability.
  //
  // `LidReaches` above is the BLIND model — correct only for gate-free build
  // code. Under nesting an outer lid's build code contains INNER gates that the
  // sweep DOES cross (reading the already-built, strictly-higher columns), so
  // the recorded bits are the V-MODEL reachability `ReachesWriteV` against the
  // view carrying those columns. `LidReachesV` is the exact V-analogue of
  // `LidReaches`; the erasure `LidReachesVErasure` proves the two COINCIDE on a
  // gate-free column, for ANY view — so the entire existing blind chain is the
  // ov-erased specialization and only genuinely-nested columns see the view.
  // ===========================================================================

  /** The V-model analogue of `LidReaches`: the build sweep for lid `i` records
      a bit at `cp` when run against the partial oracle view `ov` (which, in the
      high->low build, holds the already-built strictly-higher columns the inner
      gates read). Forward for lookbehinds; the anchor-swapped mirror for the
      backward (lookahead) build, exactly as `LidReaches`. */
  ghost opaque predicate LidReachesV(crv: CP.FCompiled, str: string, ov: LOr.OracleView, i: int, cp: int) {
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    if LidDir(crv, i) == LAnc.Forward
    then ORc.ReachesWriteV(bc, str, ov, 0, i, cp)
    else ORc.ReachesWriteV(MIR.SwapAnchorsCode(bc), LC.Reverse(str), ov, 0, i,
                           MIR.Mirror(cp, |str|))
  }

  /** `SwapAnchorsCode` only rewrites `AnchorAssertion` instructions, so it
      never introduces (or removes) an oracle-consulting instruction: gate-free
      code stays gate-free after the swap. The bridge that lets the backward
      (mirrored) build column reuse the forward erasure. */
  lemma SwapAnchorsCodeNoOracleReads(c: RB.code)
    requires OS.NoOracleReads(c)
    ensures OS.NoOracleReads(MIR.SwapAnchorsCode(c))
  {
    var sc := MIR.SwapAnchorsCode(c);
    forall pc | 0 <= pc < |sc| ensures !sc[pc].CheckOracle? && !sc[pc].NegCheckOracle? {
      assert sc[pc] == (if c[pc].AnchorAssertion? then RB.AnchorAssertion(MIR.SwapAnchor(c[pc].aa)) else c[pc]);
    }
  }

  /** ERASURE (brick 4c bridge): on a gate-free build column the V-model
      per-lid reachability collapses to the blind `LidReaches`, for ANY view —
      the forward build via `ORc.ReachesWriteVErasure`, the backward build the
      same after `SwapAnchorsCodeNoOracleReads`. This is what reconciles the
      partial-view characterization with the existing blind chain on every
      column that remains gate-free (all of them at depth 1). */
  lemma LidReachesVErasure(crv: CP.FCompiled, str: string, ov: LOr.OracleView, i: int, cp: int)
    requires OS.NoOracleReads(AI.get_code_v(crv.f_look_build_bc, i))
    ensures LidReachesV(crv, str, ov, i, cp) == LidReaches(crv, str, i, cp)
  {
    reveal LidReachesV();
    reveal LidReaches();
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    if LidDir(crv, i) == LAnc.Forward {
      ORc.ReachesWriteVErasure(bc, str, ov, 0, i, cp);
    } else {
      SwapAnchorsCodeNoOracleReads(bc);
      ORc.ReachesWriteVErasure(MIR.SwapAnchorsCode(bc), LC.Reverse(str), ov, 0, i,
                               MIR.Mirror(cp, |str|));
    }
  }

  /** Every lid OF the regex satisfies `LidBuildOk`: the fragment makes its
      flavour a lookbehind (Forward) and its body capture-free/look-free/
      plus-fragment, so the recorded build bytecode
      `compile_to_write(lazy_prefix(body), i)` is classified. */
  lemma LookTablesLidBuildOk(r: R.regex, fc: CP.FCompiled, i: nat)
    requires NR.LookBehindFragmentRE(r)
    requires LT.LookTablesOk(r, fc)
    requires i in LT.LookIds(r)
    ensures LidBuildOk(fc, i)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if i in LT.LookIds(r1) { LookTablesLidBuildOk(r1, fc, i); }
      else { LookTablesLidBuildOk(r2, fc, i); }
    case Re_con(r1, r2) =>
      if i in LT.LookIds(r1) { LookTablesLidBuildOk(r1, fc, i); }
      else { LookTablesLidBuildOk(r2, fc, i); }
    case Re_quant(_, _, _, r1) => LookTablesLidBuildOk(r1, fc, i);
    case Re_capture(_, r1) => LookTablesLidBuildOk(r1, fc, i);
    case Re_lookaround(lid, la, body) =>
      LookFreeNoIds(body);   // the body is look-free, so i can only be lid itself
      assert lid >= 0 && (lid as nat) == i;
      // L3a/L3b: the body may CAPTURE, so the oracle is built over the
      // capture-STRIPPED body `remove_capture(body)` (`oracle_regex`); it is
      // capture-free/look-free/plus, so the classification carries unchanged.
      var rcb := R.remove_capture(body);
      NR.RemoveCaptureLookFreeRE(body);       // LookFreeRE(rcb)
      NR.OracleRegexPlusFragment(la, body);   // PlusFragmentRE(oracle_regex(la, body))
      // a lookBEHIND builds lazy_prefix(rcb); a lookAHEAD builds
      // lazy_prefix(reverse_regex(rcb)). Both are classified build programs.
      if la.Lookbehind? || la.NegLookbehind? {
        assert CP.oracle_regex(la, body) == R.lazy_prefix(rcb);
        LookFreeLazyPrefix(rcb);
        NR.CompileToWriteClassified(R.lazy_prefix(rcb), lid);
      } else {
        assert CP.oracle_regex(la, body) == R.lazy_prefix(R.reverse_regex(rcb));
        NR.ReverseLookFreeRE(rcb);
        LookFreeLazyPrefix(R.reverse_regex(rcb));
        NR.CompileToWriteClassified(R.lazy_prefix(R.reverse_regex(rcb)), lid);
      }
  }

  /** Every lid whatsoever satisfies `LidBuildOk` against
      `FFullCompilation(re)`: lids of `re` by the lemma above, all others
      because their rows still hold the seed's empty bytecode
      (`FCompileExtraLookFrame`). */
  /** A row that is not a lookaround of `re` still holds the seed's empty
      bytecode -- the `else` half of `AllLidsBuildOk`, split out so the
      direction bridge can use it too. */
  lemma NonLidRowEmpty(re: R.regex, i: int)
    requires NR.LookBehindFragmentRE(re)
    requires !(i >= 0 && (i as nat) in LT.LookIds(re))
    ensures AI.get_code_v(CP.FFullCompilation(re).f_look_build_bc, i) == []
  {
    var crv := CP.FFullCompilation(re);
    var maxlook := R.max_lookaround(re);
    var maxquant := R.max_quant(re);
    var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
    var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
    var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                             seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                             seq(nlook, k => []), seq(nlook, k => []),
                             seq(nlook, k => []), seq(nquant, k => []));
    assert crv == CP.FCompileExtra(re, seed);
    LT.FCompileExtraLookFrame(re, seed);
    if 0 <= i < |crv.f_look_build_bc| {
      assert LT.AgreeAt(seed, crv, i as nat);
      assert seed.f_look_build_bc[i] == [];
    }
  }

  lemma AllLidsBuildOk(re: R.regex, i: int)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    ensures LidBuildOk(CP.FFullCompilation(re), i)
  {
    var crv := CP.FFullCompilation(re);
    if i >= 0 && (i as nat) in LT.LookIds(re) {
      LT.FFullCompilationLookOk(re);
      LookTablesLidBuildOk(re, crv, i as nat);
    } else {
      // outside LookIds: the fold framed the row, which the seed left empty
      var maxlook := R.max_lookaround(re);
      var maxquant := R.max_quant(re);
      var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
      var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
      var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                               seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                               seq(nlook, k => []), seq(nlook, k => []),
                               seq(nlook, k => []), seq(nquant, k => []));
      assert crv == CP.FCompileExtra(re, seed);
      LT.FCompileExtraLookFrame(re, seed);
      if 0 <= i < |crv.f_look_build_bc| {
        assert LT.AgreeAt(seed, crv, i as nat);
        assert seed.f_look_build_bc[i] == [];
        assert AI.get_code_v(crv.f_look_build_bc, i) == [];
      } else {
        assert AI.get_code_v(crv.f_look_build_bc, i) == [];
      }
    }
  }

  /** ESTABLISHER (brick 4b): every lid satisfies the L4 `LidBuildOkAbove`
      against `FFullCompilation(re)`. On the currently-wired depth-1 fragment
      this factors through `AllLidsBuildOk` (each column is gate-free) and the
      `LidBuildOkImpliesAbove` weakening — the gate clause `AllGatesAbove(bc,i)`
      is discharged from `NoOracleReads(bc)` (the empty-gate-set special case of
      the `NR.GatesAboveClassified` discharge that W6 will use for genuinely
      nested bodies, whose inner gates read strictly above `i` by
      `LT.LidsWellNested`). Feeds the high->low build induction (brick 4c). */
  lemma AllLidsBuildOkAbove(re: R.regex, i: int)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    ensures LidBuildOkAbove(CP.FFullCompilation(re), i)
  {
    AllLidsBuildOk(re, i);
    LidBuildOkImpliesAbove(CP.FFullCompilation(re), i);
  }

  /** A real row of a LOOKBEHIND-fragment regex builds Forward, since the
      fragment forces every lookaround to a lookbehind flavour. */
  lemma LookTablesLidDirForward(r: R.regex, fc: CP.FCompiled, i: nat)
    requires NR.LookBehindFragmentRE(r)
    requires LT.LookTablesOk(r, fc)
    requires i in LT.LookIds(r)
    // only a lookBEHIND row builds Forward; the fragment now admits lookaheads
    ensures 0 <= i < |fc.f_look_types|
    ensures (fc.f_look_types[i].Lookbehind? || fc.f_look_types[i].NegLookbehind?)
            ==> LidDir(fc, i) == LAnc.Forward
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if i in LT.LookIds(r1) { LookTablesLidDirForward(r1, fc, i); }
      else { LookTablesLidDirForward(r2, fc, i); }
    case Re_con(r1, r2) =>
      if i in LT.LookIds(r1) { LookTablesLidDirForward(r1, fc, i); }
      else { LookTablesLidDirForward(r2, fc, i); }
    case Re_quant(_, _, _, r1) => LookTablesLidDirForward(r1, fc, i);
    case Re_capture(_, r1) => LookTablesLidDirForward(r1, fc, i);
    case Re_lookaround(lid, la, body) =>
      LookFreeNoIds(body);
      assert lid >= 0 && (lid as nat) == i;
      assert fc.f_look_types[i] == la;
  }

  /** `LookTablesLidDirForward` for the NESTED fragment: recurses into look
      bodies (which now carry their own lids) instead of stopping at a look-free
      body. A lookBEHIND row still builds Forward. */
  lemma LookTablesLidDirForwardNested(r: R.regex, fc: CP.FCompiled, i: nat)
    requires NR.NestedFragmentRE(r)
    requires LT.LookTablesOk(r, fc)
    requires i in LT.LookIds(r)
    ensures 0 <= i < |fc.f_look_types|
    ensures (fc.f_look_types[i].Lookbehind? || fc.f_look_types[i].NegLookbehind?)
            ==> LidDir(fc, i) == LAnc.Forward
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if i in LT.LookIds(r1) { LookTablesLidDirForwardNested(r1, fc, i); }
      else { LookTablesLidDirForwardNested(r2, fc, i); }
    case Re_con(r1, r2) =>
      if i in LT.LookIds(r1) { LookTablesLidDirForwardNested(r1, fc, i); }
      else { LookTablesLidDirForwardNested(r2, fc, i); }
    case Re_quant(_, _, _, r1) => LookTablesLidDirForwardNested(r1, fc, i);
    case Re_capture(_, r1) => LookTablesLidDirForwardNested(r1, fc, i);
    case Re_lookaround(lid, la, body) =>
      if lid >= 0 && (lid as nat) == i {
        assert fc.f_look_types[i] == la;              // LookEntryOk(fc, lid, la, body)
      } else {
        LookTablesLidDirForwardNested(body, fc, i);   // i in LookIds(body)
      }
  }

  /** On the lookbehind fragment `LidReaches` IS the plain forward
      reachability -- a real row builds Forward, and a row that is not a
      lookaround of `re` holds empty bytecode, where both sides are false.
      This is what keeps the whole L1 chain (which is stated in terms of
      `ReachesWrite`) working unchanged after the generalization. */
  lemma LidReachesIsReachesWrite(re: R.regex, str: string, i: int, cp: int)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    ensures var crv := CP.FFullCompilation(re);
      (LidDir(crv, i) == LAnc.Forward ==>
        (LidReaches(crv, str, i, cp)
         <==> ORc.ReachesWrite(AI.get_code_v(crv.f_look_build_bc, i), str, 0, i, cp)))
  {
    var crv := CP.FFullCompilation(re);
    if i >= 0 && (i as nat) in LT.LookIds(re) {
      LT.FFullCompilationLookOk(re);
      LookTablesLidDirForward(re, crv, i as nat);
      if LidDir(crv, i) == LAnc.Forward { LidReachesForward(crv, str, i, cp); }
    } else {
      NonLidRowEmpty(re, i);
      LidReachesEmpty(crv, str, i, cp);
      ReachesWriteEmpty(str, 0, i, cp);
    }
  }

  // ===========================================================================
  // The FBuildLids induction and the top-level theorem
  // ===========================================================================

  /** `FBuildLids` down from `lid`: every column `1..lid` gains exactly its
      bytecode's `ReachesWrite` positions; everything else is untouched. */
  lemma FBuildLidsCharacterized(crv: CP.FCompiled, str: string, lid: int, ov: LOr.OracleView)
    requires forall i: int :: 1 <= i <= lid ==> LidBuildOk(crv, i)
    requires |ov| == |str| + 1
    requires forall r: int {:trigger ov[r]} :: 0 <= r < |ov| ==> lid < |ov[r]|
    ensures var ov' := AI.FBuildLids(crv, str, lid, ov);
      OS.SameShape(ov, ov')
      && forall i: int, cp: int ::
           LOr.view_get_oracle(ov', cp, i)
           == (LOr.view_get_oracle(ov, cp, i)
               || (1 <= i <= lid && LidReaches(crv, str, i, cp)))
    decreases lid
  {
    if lid < 1 { return; }
    var bc := AI.get_code_v(crv.f_look_build_bc, lid);
    var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
    var dir := AI.oracle_direction(looktype);
    var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
    var initcp := AI.init_cp(dir, |str|);
    var maxcap := R.max_group(crv.f_main_ast);
    var maxlook := R.max_lookaround(crv.f_main_ast);
    var maxquant := R.max_quant(crv.f_main_ast);
    var capture := AReg.init_regs(2 * maxcap + 2);
    var lookmem := AReg.init_regs(maxlook + 1);
    var quant := AReg.init_regs(maxquant + 1);
    var inits := AI.FInitState(bc, initcp, capture, lookmem, quant, 0,
                               AI.cp_context(initcp, str, dir));
    var (_, ov1) := AI.FFindMatch(bc, str, inits, ov, dir, lookcdn);
    assert AI.FBuildLids(crv, str, lid, ov) == AI.FBuildLids(crv, str, lid - 1, ov1);
    if bc == [] {
      FFindMatchEmpty(str, inits, ov, dir, lookcdn);
      assert ov1 == ov;
      FBuildLidsCharacterized(crv, str, lid - 1, ov1);
      forall i: int, cp: int
        ensures LOr.view_get_oracle(AI.FBuildLids(crv, str, lid - 1, ov1), cp, i)
             == (LOr.view_get_oracle(ov, cp, i)
                 || (1 <= i <= lid && LidReaches(crv, str, i, cp)))
      {
        if i == lid {
          assert AI.get_code_v(crv.f_look_build_bc, i) == bc == [];
          LidReachesEmpty(crv, str, i, cp);
        }
      }
    } else {
      assert LidBuildOk(crv, lid);
      assert OS.NoOracleReads(bc) && OS.NoCheckNullable(bc) && OS.WritesOnlyLid(bc, lid)
          && OS.NoAccept(bc);
      assert LidDir(crv, lid) == dir;
      assert AI.get_code_v(crv.f_look_build_bc, lid) == bc;
      // The tail is duplicated under each direction ON PURPOSE. `LidReaches`
      // is an if-then-else on the build direction, so it only unfolds where
      // `dir` is statically known; after an if-else join it is opaque and the
      // forall below cannot close.
      if dir == LAnc.Forward {
        assert initcp == 0;
        ORc.SweepCharacterization(bc, str, ov, lid, lookcdn, capture, lookmem, quant, 0);
        OS.FindMatchOracleFrame(bc, str, inits, ov, dir, lookcdn, lid);
        assert OS.SameShape(ov, ov1);
        assert |ov1| == |str| + 1;
        forall r: int | 0 <= r < |ov1| ensures lid - 1 < |ov1[r]| { assert |ov1[r]| == |ov[r]|; }
        FBuildLidsCharacterized(crv, str, lid - 1, ov1);
        var ov' := AI.FBuildLids(crv, str, lid - 1, ov1);
        forall i: int, cp: int
          ensures LOr.view_get_oracle(ov', cp, i)
               == (LOr.view_get_oracle(ov, cp, i)
                   || (1 <= i <= lid && LidReaches(crv, str, i, cp)))
        {
          if i == lid {
            reveal LidReaches();
            assert LOr.view_get_oracle(ov', cp, i) == LOr.view_get_oracle(ov1, cp, i);
          } else if 1 <= i <= lid - 1 {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          } else {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          }
        }
      } else {
        assert dir == LAnc.Backward && initcp == AI.init_cp(LAnc.Backward, |str|);
        MIR.BackwardSweepCharacterization(bc, str, ov, lid, lookcdn,
                                          2 * maxcap + 2, maxlook + 1, maxquant + 1, |str|);
        OS.FindMatchOracleFrame(bc, str, inits, ov, dir, lookcdn, lid);
        assert OS.SameShape(ov, ov1);
        assert |ov1| == |str| + 1;
        forall r: int | 0 <= r < |ov1| ensures lid - 1 < |ov1[r]| { assert |ov1[r]| == |ov[r]|; }
        FBuildLidsCharacterized(crv, str, lid - 1, ov1);
        var ov' := AI.FBuildLids(crv, str, lid - 1, ov1);
        forall i: int, cp: int
          ensures LOr.view_get_oracle(ov', cp, i)
               == (LOr.view_get_oracle(ov, cp, i)
                   || (1 <= i <= lid && LidReaches(crv, str, i, cp)))
        {
          if i == lid {
            reveal LidReaches();
            assert LOr.view_get_oracle(ov', cp, i) == LOr.view_get_oracle(ov1, cp, i);
          } else if 1 <= i <= lid - 1 {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          } else {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          }
        }
      }
    }
  }

  /** V-MODEL restatement of `FBuildLidsCharacterized` (brick 4c): every column
      `1..lid` gains exactly its build code's `LidReachesV` positions AGAINST THE
      FINAL VIEW `ov'`. On the currently-wired depth-1 fragment every column is
      gate-free (`LidBuildOk` supplies `NoOracleReads`), so this reduces to the
      blind theorem and reconciles column-by-column via `LidReachesVErasure` —
      the `LidReaches` of the blind chain equals `LidReachesV(_, ov', _, _)` for
      the (view-independent) gate-free columns. This lands the V-model
      characterization vocabulary as a proven theorem and isolates the remaining
      L4 crux: a GATE-FUL sweep characterization (the V-model soundness+
      completeness for build columns whose code reads strictly-higher columns),
      which is what a full `LidBuildOkAbove`-gated induction would additionally
      need. See the L4_L5_ROADMAP W3 brick-4 notes. */
  /** `LidBuildOk` supplies gate-freeness of the column: either the build code
      is empty (`NoOracleReads([])` vacuously) or its `NoOracleReads` conjunct
      holds directly. The small bridge the V-model reconciliation needs. */
  lemma LidBuildOkNoOracleReads(crv: CP.FCompiled, i: int)
    requires LidBuildOk(crv, i)
    ensures OS.NoOracleReads(AI.get_code_v(crv.f_look_build_bc, i))
  {}

  lemma FBuildLidsCharacterizedV(crv: CP.FCompiled, str: string, lid: int, ov: LOr.OracleView)
    requires forall i: int :: 1 <= i <= lid ==> LidBuildOk(crv, i)
    requires |ov| == |str| + 1
    requires forall r: int {:trigger ov[r]} :: 0 <= r < |ov| ==> lid < |ov[r]|
    ensures var ov' := AI.FBuildLids(crv, str, lid, ov);
      OS.SameShape(ov, ov')
      && forall i: int, cp: int ::
           LOr.view_get_oracle(ov', cp, i)
           == (LOr.view_get_oracle(ov, cp, i)
               || (1 <= i <= lid && LidReachesV(crv, str, ov', i, cp)))
  {
    FBuildLidsCharacterized(crv, str, lid, ov);
    var ov' := AI.FBuildLids(crv, str, lid, ov);
    forall i: int, cp: int
      ensures LOr.view_get_oracle(ov', cp, i)
           == (LOr.view_get_oracle(ov, cp, i)
               || (1 <= i <= lid && LidReachesV(crv, str, ov', i, cp)))
    {
      if 1 <= i <= lid {
        // LidBuildOk(crv,i): bc==[] (NoOracleReads vacuous) or NoOracleReads(bc)
        LidBuildOkNoOracleReads(crv, i);
        LidReachesVErasure(crv, str, ov', i, cp);
      }
    }
  }

  /** The oracle build preserves the view LENGTH: each lid runs `FFindMatch`
      (which keeps `|ov|` — `MIR.FFindMatchViewLen`), so the whole fold does. */
  lemma FBuildLidsLen(crv: CP.FCompiled, str: string, lid: int, ov: LOr.OracleView)
    ensures |AI.FBuildLids(crv, str, lid, ov)| == |ov|
    decreases lid
  {
    if lid < 1 {
    } else {
      var bytecode := AI.get_code_v(crv.f_look_build_bc, lid);
      var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
      var dir := AI.oracle_direction(looktype);
      var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
      var initcp := AI.init_cp(dir, |str|);
      var maxcap := R.max_group(crv.f_main_ast);
      var maxlook := R.max_lookaround(crv.f_main_ast);
      var maxquant := R.max_quant(crv.f_main_ast);
      var capture := AReg.init_regs(2 * maxcap + 2);
      var lookmem := AReg.init_regs(maxlook + 1);
      var quant := AReg.init_regs(maxquant + 1);
      var inits := AI.FInitState(bytecode, initcp, capture, lookmem, quant, 0,
                                 AI.cp_context(initcp, str, dir));
      var (_, ov1) := AI.FFindMatch(bytecode, str, inits, ov, dir, lookcdn);
      MIR.FFindMatchViewLen(bytecode, str, inits, ov, dir, lookcdn);   // |ov1| == |ov|
      FBuildLidsLen(crv, str, lid - 1, ov1);
    }
  }

  /** `|FBuildOracle(crv, str)| == |str| + 1` — the oracle has one column per
      position. (Threaded to the backward capturing-lookbehind gate as `|ov|`.) */
  lemma FBuildOracleViewLen(crv: CP.FCompiled, str: string)
    ensures |AI.FBuildOracle(crv, str)| == |str| + 1
  {
    var maxlook := R.max_lookaround(crv.f_main_ast);
    FBuildLidsLen(crv, str, maxlook, LOr.init_view(|str|, maxlook + 1));
  }

  /** THE §6.2 theorem: after the oracle build for a lid-unique
      lookbehind-fragment regex, column `lid` holds EXACTLY the
      `ReachesWrite` positions of that lid's build bytecode. */
  lemma FBuildOracleCorrect(re: R.regex, str: string)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    ensures var crv := CP.FFullCompilation(re);
      var ovf := AI.FBuildOracle(crv, str);
      forall lid: int, cp: int ::
        LOr.view_get_oracle(ovf, cp, lid)
        == (1 <= lid <= R.max_lookaround(re) && LidReaches(crv, str, lid, cp))
  {
    var crv := CP.FFullCompilation(re);
    var maxlook0 := R.max_lookaround(re);
    var maxquant0 := R.max_quant(re);
    var nlook := if maxlook0 + 1 >= 0 then maxlook0 + 1 else 0;
    var nquant := if maxquant0 + 1 >= 0 then maxquant0 + 1 else 0;
    var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                             seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                             seq(nlook, k => []), seq(nlook, k => []),
                             seq(nlook, k => []), seq(nquant, k => []));
    assert crv == CP.FCompileExtra(re, seed);
    FCompileExtraMainAst(re, seed);
    assert crv.f_main_ast == re;
    var maxlook := R.max_lookaround(crv.f_main_ast);
    assert maxlook == maxlook0;
    var ov0 := LOr.init_view(|str|, maxlook + 1);
    assert AI.FBuildOracle(crv, str) == AI.FBuildLids(crv, str, maxlook, ov0);
    assert |ov0| == |str| + 1;
    assert forall r: int {:trigger ov0[r]} :: 0 <= r < |ov0| ==> |ov0[r]| == maxlook + 1;
    assert forall cp: int, i: int :: !LOr.view_get_oracle(ov0, cp, i);
    forall i: int | 1 <= i <= maxlook
      ensures LidBuildOk(crv, i)
    {
      AllLidsBuildOk(re, i);
    }
    FBuildLidsCharacterized(crv, str, maxlook, ov0);
  }

  /** V-MODEL capstone (brick 4c): the §6.2 theorem restated against the
      partial-oracle-view reachability, SELF-REFERENTIALLY — column `lid` of the
      finished oracle `ovf` holds exactly the `LidReachesV(_, ovf, _, _)` bits
      (the V-model reachability read against the finished oracle itself). On the
      depth-1 fragment this reduces to `FBuildOracleCorrect` and reconciles per
      column via `LidReachesVErasure` (each column gate-free). This is the shape
      a full nested oracle-correctness theorem takes; landing it now fixes the
      target statement and confines the open work to the gate-ful sweep
      characterization (see `FBuildLidsCharacterizedV`). */
  lemma FBuildOracleCorrectV(re: R.regex, str: string)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    ensures var crv := CP.FFullCompilation(re);
      var ovf := AI.FBuildOracle(crv, str);
      forall lid: int, cp: int ::
        LOr.view_get_oracle(ovf, cp, lid)
        == (1 <= lid <= R.max_lookaround(re) && LidReachesV(crv, str, ovf, lid, cp))
  {
    var crv := CP.FFullCompilation(re);
    var ovf := AI.FBuildOracle(crv, str);
    FBuildOracleCorrect(re, str);
    forall lid: int, cp: int
      ensures LOr.view_get_oracle(ovf, cp, lid)
           == (1 <= lid <= R.max_lookaround(re) && LidReachesV(crv, str, ovf, lid, cp))
    {
      if 1 <= lid <= R.max_lookaround(re) {
        AllLidsBuildOk(re, lid);
        LidBuildOkNoOracleReads(crv, lid);
        LidReachesVErasure(crv, str, ovf, lid, cp);
      }
    }
  }

  // ===========================================================================
  // L4 depth-k (bricks 4c/§6.2): the GATED high->low build induction over the
  // GENUINELY nested `LidBuildOkAbove` (gates admitted, reading strictly-higher
  // columns) — not the gate-free `LidBuildOk` the blind chain erased to.
  //
  // THE REVERSED-SPAN FINDING. `LidReachesV`'s BACKWARD branch reads the
  // reference view `ov` at the REVERSED-frame position — it is the correct
  // characterization only when the build code is GATE-FREE (then the reference
  // view is irrelevant, `LidReachesVErasure`). For a genuinely gate-ful backward
  // (lookAHEAD) build the inner gate at reversed position `q` must read the
  // oracle at the ORIGINAL position `n - q` — i.e. `MirrorView(ov, n)`, exactly
  // what `Mirror.BackwardSweepCharacterizationV` produces — NOT `ov[q]`. So
  // `LidReachesV` (unmirrored) is not the true target for nested lookaheads.
  // `LidReachesVFinal` below is the additive fix: identical to `LidReachesV` on
  // the forward branch, and reading `MirrorView(ov, n)` on the backward branch.
  // On gate-free columns it collapses back to `LidReaches`/`LidReachesV`
  // (`LidReachesVFinalErasure`), so it is a conservative extension of the
  // existing depth-1 target and reconciles both directions cleanly.
  // ===========================================================================

  /** `AgreeAbove` is preserved by the row-permutation `MirrorView`: mirroring
      reflects the positions but keeps each column, so agreement on columns `> k`
      transports to the mirrored views. The bridge the backward reconcile needs
      (`BackwardSweepCharacterizationV`'s reference view is `MirrorView(ov, n)`). */
  lemma AgreeAboveMirror(a: LOr.OracleView, b: LOr.OracleView, k: int, n: int)
    requires n >= 0 && |a| == n + 1 && |b| == n + 1
    requires OS.AgreeAbove(a, b, k)
    ensures OS.AgreeAbove(MIR.MirrorView(a, n), MIR.MirrorView(b, n), k)
  {
    forall cp2: int, l2: int | l2 > k
      ensures OS.CellAgree(MIR.MirrorView(a, n), MIR.MirrorView(b, n), cp2, l2)
    {
      MIR.MirrorViewGet(a, n, MIR.Mirror(cp2, n), l2);   // read MV(a,n) at Mirror(Mirror(cp2))==cp2
      MIR.MirrorViewGet(b, n, MIR.Mirror(cp2, n), l2);
      MIR.MirrorInvolution(cp2, n);
      assert OS.CellAgree(a, b, MIR.Mirror(cp2, n), l2);  // from AgreeAbove(a,b,k), l2 > k
    }
  }

  /** THE CORRECTED V-MODEL TARGET (the reversed-span fix). Identical to
      `LidReachesV` on the FORWARD (lookbehind) branch; on the BACKWARD
      (lookahead) branch it reads the reference view through the position mirror
      `MirrorView(ov, |str|)` — the view the actual backward build's inner gates
      consult — guarded on the view being column-shaped (`|ov| == |str| + 1`),
      the shape every oracle view in the build carries. */
  ghost opaque predicate LidReachesVFinal(crv: CP.FCompiled, str: string, ov: LOr.OracleView, i: int, cp: int) {
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    if LidDir(crv, i) == LAnc.Forward
    then ORc.ReachesWriteV(bc, str, ov, 0, i, cp)
    else if |ov| == |str| + 1
         then ORc.ReachesWriteV(MIR.SwapAnchorsCode(bc), LC.Reverse(str), MIR.MirrorView(ov, |str|),
                                0, i, MIR.Mirror(cp, |str|))
         else false
  }

  /** ERASURE. On a gate-free build column the corrected target collapses to the
      blind `LidReaches`, for ANY (column-shaped) view — the reference view is
      irrelevant when no gate reads it, so `MirrorView` drops out. This is what
      makes `LidReachesVFinal` a conservative extension of `LidReachesV`
      (they coincide on every gate-free column, in both directions). */
  lemma LidReachesVFinalErasure(crv: CP.FCompiled, str: string, ov: LOr.OracleView, i: int, cp: int)
    requires OS.NoOracleReads(AI.get_code_v(crv.f_look_build_bc, i))
    requires |ov| == |str| + 1
    ensures LidReachesVFinal(crv, str, ov, i, cp) == LidReaches(crv, str, i, cp)
  {
    reveal LidReachesVFinal();
    reveal LidReaches();
    var bc := AI.get_code_v(crv.f_look_build_bc, i);
    if LidDir(crv, i) == LAnc.Forward {
      ORc.ReachesWriteVErasure(bc, str, ov, 0, i, cp);
    } else {
      SwapAnchorsCodeNoOracleReads(bc);
      ORc.ReachesWriteVErasure(MIR.SwapAnchorsCode(bc), LC.Reverse(str), MIR.MirrorView(ov, |str|),
                               0, i, MIR.Mirror(cp, |str|));
    }
  }

  /** An empty build column reaches no write, in either direction (empty code is
      gate-free, so the erasure reduces it to `LidReachesEmpty`). */
  lemma LidReachesVFinalEmpty(crv: CP.FCompiled, str: string, ov: LOr.OracleView, i: int, cp: int)
    requires AI.get_code_v(crv.f_look_build_bc, i) == []
    requires |ov| == |str| + 1
    ensures !LidReachesVFinal(crv, str, ov, i, cp)
  {
    LidReachesVFinalErasure(crv, str, ov, i, cp);
    LidReachesEmpty(crv, str, i, cp);
  }

  /** STEP 1 — THE FOLD-LEVEL COLUMN FRAME (the piece #22 identified). Under the
      gated `LidBuildOkAbove` (each column's sweep `WritesOnlyLid` its own
      column), the sub-fold `FBuildLids(crv, str, m, ov)` — which builds columns
      `1..m` — leaves every column `> m` UNCHANGED. Equivalently
      `AgreeAbove(ov, FBuildLids(...), m)`. This is the hypothesis
      `ReachesWriteVBuildFinalReconcile` consumes to move a build-time
      characterization to the final view. Framed per column via
      `OS.FindMatchOracleFrame` and folded down the recursion. */
  lemma FBuildLidsFrameAbove(crv: CP.FCompiled, str: string, m: int, ov: LOr.OracleView)
    requires forall i: int :: 1 <= i <= m ==> LidBuildOkAbove(crv, i)
    ensures var ov' := AI.FBuildLids(crv, str, m, ov);
      forall cp2: int, l2: int :: l2 > m ==>
        LOr.view_get_oracle(ov', cp2, l2) == LOr.view_get_oracle(ov, cp2, l2)
    decreases m
  {
    if m < 1 { return; }
    var bc := AI.get_code_v(crv.f_look_build_bc, m);
    var looktype := if 0 <= m < |crv.f_look_types| then crv.f_look_types[m] else R.Lookahead;
    var dir := AI.oracle_direction(looktype);
    var lookcdn := if 0 <= m < |crv.f_look_cdns| then crv.f_look_cdns[m] else [];
    var initcp := AI.init_cp(dir, |str|);
    var maxcap := R.max_group(crv.f_main_ast);
    var maxlook := R.max_lookaround(crv.f_main_ast);
    var maxquant := R.max_quant(crv.f_main_ast);
    var capture := AReg.init_regs(2 * maxcap + 2);
    var lookmem := AReg.init_regs(maxlook + 1);
    var quant := AReg.init_regs(maxquant + 1);
    var inits := AI.FInitState(bc, initcp, capture, lookmem, quant, 0,
                               AI.cp_context(initcp, str, dir));
    var (_, ov1) := AI.FFindMatch(bc, str, inits, ov, dir, lookcdn);
    assert AI.FBuildLids(crv, str, m, ov) == AI.FBuildLids(crv, str, m - 1, ov1);
    if bc == [] {
      FFindMatchEmpty(str, inits, ov, dir, lookcdn);   // ov1 == ov
    } else {
      assert LidBuildOkAbove(crv, m);
      assert OS.WritesOnlyLid(bc, m);                  // the gate-ful column still writes only m
      OS.FindMatchOracleFrame(bc, str, inits, ov, dir, lookcdn, m);   // cols != m unchanged
    }
    FBuildLidsFrameAbove(crv, str, m - 1, ov1);
    var ov' := AI.FBuildLids(crv, str, m - 1, ov1);
    forall cp2: int, l2: int | l2 > m
      ensures LOr.view_get_oracle(ov', cp2, l2) == LOr.view_get_oracle(ov, cp2, l2)
    {
      // l2 > m ==> l2 > m-1 (recursion: ov' == ov1) and l2 != m (frame: ov1 == ov)
    }
  }

  /** STEP 2 — THE GATED HIGH->LOW BUILD INDUCTION. The genuinely gated form of
      `FBuildLidsCharacterized(V)`: over the gated `LidBuildOkAbove` (build code
      whose gates read strictly-higher, already-built columns), every column
      `1..lid` gains exactly its build code's `LidReachesVFinal` positions
      AGAINST THE FINAL VIEW. Forward columns are characterized by the gate-ful
      `ORc.SweepCharacterizationV`, backward (lookahead) columns by
      `Mirror.BackwardSweepCharacterizationV`; the build-time reading is moved to
      the final view by `ORc.ReachesWriteVBuildFinalReconcile` fed the fold-level
      frame (step 1). The structure mirrors the blind `FBuildLidsCharacterized`,
      swapping the gate-free sweep for the gated one and `LidReaches` for
      `LidReachesVFinal`. */
  lemma FBuildLidsCharacterizedAbove(crv: CP.FCompiled, str: string, lid: int, ov: LOr.OracleView)
    requires forall i: int :: 1 <= i <= lid ==> LidBuildOkAbove(crv, i)
    requires |ov| == |str| + 1
    requires forall r: int {:trigger ov[r]} :: 0 <= r < |ov| ==> lid < |ov[r]|
    ensures var ov' := AI.FBuildLids(crv, str, lid, ov);
      OS.SameShape(ov, ov')
      && forall i: int, cp: int ::
           LOr.view_get_oracle(ov', cp, i)
           == (LOr.view_get_oracle(ov, cp, i)
               || (1 <= i <= lid && LidReachesVFinal(crv, str, ov', i, cp)))
    decreases lid
  {
    if lid < 1 { return; }
    var bc := AI.get_code_v(crv.f_look_build_bc, lid);
    var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
    var dir := AI.oracle_direction(looktype);
    var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
    var initcp := AI.init_cp(dir, |str|);
    var maxcap := R.max_group(crv.f_main_ast);
    var maxlook := R.max_lookaround(crv.f_main_ast);
    var maxquant := R.max_quant(crv.f_main_ast);
    var capture := AReg.init_regs(2 * maxcap + 2);
    var lookmem := AReg.init_regs(maxlook + 1);
    var quant := AReg.init_regs(maxquant + 1);
    var inits := AI.FInitState(bc, initcp, capture, lookmem, quant, 0,
                               AI.cp_context(initcp, str, dir));
    var (_, ov1) := AI.FFindMatch(bc, str, inits, ov, dir, lookcdn);
    var n := |str|;
    assert AI.FBuildLids(crv, str, lid, ov) == AI.FBuildLids(crv, str, lid - 1, ov1);
    if bc == [] {
      FFindMatchEmpty(str, inits, ov, dir, lookcdn);
      assert ov1 == ov;
      FBuildLidsCharacterizedAbove(crv, str, lid - 1, ov1);
      var ov' := AI.FBuildLids(crv, str, lid - 1, ov1);
      forall i: int, cp: int
        ensures LOr.view_get_oracle(ov', cp, i)
             == (LOr.view_get_oracle(ov, cp, i)
                 || (1 <= i <= lid && LidReachesVFinal(crv, str, ov', i, cp)))
      {
        if i == lid {
          assert AI.get_code_v(crv.f_look_build_bc, i) == bc == [];
          FBuildLidsLen(crv, str, lid - 1, ov1);      // |ov'| == |str| + 1
          LidReachesVFinalEmpty(crv, str, ov', i, cp);
        }
      }
    } else {
      assert LidBuildOkAbove(crv, lid);
      assert OS.AllGatesAbove(bc, lid) && OS.NoCheckNullable(bc) && OS.WritesOnlyLid(bc, lid)
          && OS.NoAccept(bc);
      assert LidDir(crv, lid) == dir;
      assert AI.get_code_v(crv.f_look_build_bc, lid) == bc;
      // The tail is split by direction ON PURPOSE (as in FBuildLidsCharacterized):
      // LidReachesVFinal is an if-then-else on the build direction, so it only
      // unfolds where `dir` is statically known.
      if dir == LAnc.Forward {
        assert initcp == 0;
        ORc.SweepCharacterizationV(bc, lid, str, ov, lookcdn, capture, lookmem, quant, 0);
        OS.FindMatchOracleFrame(bc, str, inits, ov, dir, lookcdn, lid);
        assert OS.SameShape(ov, ov1);
        assert |ov1| == |str| + 1;
        forall r: int | 0 <= r < |ov1| ensures lid - 1 < |ov1[r]| { assert |ov1[r]| == |ov[r]|; }
        FBuildLidsCharacterizedAbove(crv, str, lid - 1, ov1);
        FBuildLidsFrameAbove(crv, str, lid - 1, ov1);
        var ov' := AI.FBuildLids(crv, str, lid - 1, ov1);
        FBuildLidsLen(crv, str, lid - 1, ov1);          // |ov'| == |str| + 1
        // AgreeAbove(ov, ov', lid): cols > lid untouched by building lid (frame)
        // and by the sub-fold (step-1 frame).
        forall cp2: int, l2: int | l2 > lid ensures OS.CellAgree(ov, ov', cp2, l2) {}
        assert OS.AgreeAbove(ov, ov', lid);
        forall i: int, cp: int
          ensures LOr.view_get_oracle(ov', cp, i)
               == (LOr.view_get_oracle(ov, cp, i)
                   || (1 <= i <= lid && LidReachesVFinal(crv, str, ov', i, cp)))
        {
          if i == lid {
            reveal LidReachesVFinal();
            assert LOr.view_get_oracle(ov', cp, i) == LOr.view_get_oracle(ov1, cp, i);
            ORc.ReachesWriteVBuildFinalReconcile(bc, str, ov, ov', lid, 0, cp);
          } else if 1 <= i <= lid - 1 {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          } else {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          }
        }
      } else {
        assert dir == LAnc.Backward && initcp == AI.init_cp(LAnc.Backward, |str|);
        MIR.BackwardSweepCharacterizationV(bc, lid, str, ov, lookcdn,
                                           2 * maxcap + 2, maxlook + 1, maxquant + 1, |str|);
        OS.FindMatchOracleFrame(bc, str, inits, ov, dir, lookcdn, lid);
        assert OS.SameShape(ov, ov1);
        assert |ov1| == |str| + 1;
        forall r: int | 0 <= r < |ov1| ensures lid - 1 < |ov1[r]| { assert |ov1[r]| == |ov[r]|; }
        FBuildLidsCharacterizedAbove(crv, str, lid - 1, ov1);
        FBuildLidsFrameAbove(crv, str, lid - 1, ov1);
        var ov' := AI.FBuildLids(crv, str, lid - 1, ov1);
        FBuildLidsLen(crv, str, lid - 1, ov1);          // |ov'| == |str| + 1
        forall cp2: int, l2: int | l2 > lid ensures OS.CellAgree(ov, ov', cp2, l2) {}
        assert OS.AgreeAbove(ov, ov', lid);
        // transport the agreement through the position mirror for the backward
        // reference view, then reconcile the swapped program's reading.
        AgreeAboveMirror(ov, ov', lid, n);
        MIR.SwapPreservesAllGatesAbove(bc, lid);
        forall i: int, cp: int
          ensures LOr.view_get_oracle(ov', cp, i)
               == (LOr.view_get_oracle(ov, cp, i)
                   || (1 <= i <= lid && LidReachesVFinal(crv, str, ov', i, cp)))
        {
          if i == lid {
            reveal LidReachesVFinal();
            assert LOr.view_get_oracle(ov', cp, i) == LOr.view_get_oracle(ov1, cp, i);
            ORc.ReachesWriteVBuildFinalReconcile(MIR.SwapAnchorsCode(bc), LC.Reverse(str),
                                                 MIR.MirrorView(ov, n), MIR.MirrorView(ov', n),
                                                 lid, 0, MIR.Mirror(cp, n));
          } else if 1 <= i <= lid - 1 {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          } else {
            assert LOr.view_get_oracle(ov1, cp, i) == LOr.view_get_oracle(ov, cp, i);
          }
        }
      }
    }
  }

  /** STEP 3 (capstone core) — THE GATED §6.2 THEOREM, isolated on its single
      remaining obligation. Given the per-lid gated side condition
      `LidBuildOkAbove` for EVERY row of `FFullCompilation(re)`, column `lid` of
      the finished oracle holds EXACTLY the `LidReachesVFinal` positions of that
      lid's build bytecode (read against the finished oracle itself). Pure
      composition of the gated induction `FBuildLidsCharacterizedAbove` over the
      all-false initial view. The one open piece for a genuinely nested `re` is
      discharging the `LidBuildOkAbove` hypothesis — the nested build-code
      classification (`NR.GatesAboveClassified` fed `LidsWellNested` + a nested
      `oracle_regex`/write classification); on the depth-1 lookbehind fragment it
      is discharged by `AllLidsBuildOkAbove` (see the corollary below). */
  lemma FBuildOracleCorrectAbove(re: R.regex, str: string)
    requires LT.LookUnique(re)
    requires forall i: int :: LidBuildOkAbove(CP.FFullCompilation(re), i)
    ensures var crv := CP.FFullCompilation(re);
      var ovf := AI.FBuildOracle(crv, str);
      forall lid: int, cp: int ::
        LOr.view_get_oracle(ovf, cp, lid)
        == (1 <= lid <= R.max_lookaround(re) && LidReachesVFinal(crv, str, ovf, lid, cp))
  {
    var crv := CP.FFullCompilation(re);
    var ovf := AI.FBuildOracle(crv, str);
    var maxlook0 := R.max_lookaround(re);
    var maxquant0 := R.max_quant(re);
    var nlook := if maxlook0 + 1 >= 0 then maxlook0 + 1 else 0;
    var nquant := if maxquant0 + 1 >= 0 then maxquant0 + 1 else 0;
    var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                             seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                             seq(nlook, k => []), seq(nlook, k => []),
                             seq(nlook, k => []), seq(nquant, k => []));
    assert crv == CP.FCompileExtra(re, seed);
    FCompileExtraMainAst(re, seed);
    assert crv.f_main_ast == re;
    var maxlook := R.max_lookaround(crv.f_main_ast);
    assert maxlook == maxlook0;
    var ov0 := LOr.init_view(|str|, maxlook + 1);
    assert AI.FBuildOracle(crv, str) == AI.FBuildLids(crv, str, maxlook, ov0);
    assert |ov0| == |str| + 1;
    assert forall r: int {:trigger ov0[r]} :: 0 <= r < |ov0| ==> |ov0[r]| == maxlook + 1;
    assert forall cp: int, i: int :: !LOr.view_get_oracle(ov0, cp, i);
    forall r: int {:trigger ov0[r]} | 0 <= r < |ov0| ensures maxlook < |ov0[r]| {}
    FBuildLidsCharacterizedAbove(crv, str, maxlook, ov0);
  }

  /** STEP 3 (capstone) — the GATED §6.2 theorem, fully closed on the depth-1
      LOOKBEHIND fragment. Discharges the `LidBuildOkAbove` hypothesis of
      `FBuildOracleCorrectAbove` via the establisher `AllLidsBuildOkAbove`, so the
      currently-wired fragment's oracle correctness now flows through the
      GENUINELY GATED induction (`FBuildLidsCharacterizedAbove`) rather than the
      gate-free erasure of `FBuildOracleCorrectV`. The `NestedFragmentRE` version
      is the same composition once the nested establisher discharges the same
      hypothesis. */
  lemma FBuildOracleCorrectAboveLookBehind(re: R.regex, str: string)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    ensures var crv := CP.FFullCompilation(re);
      var ovf := AI.FBuildOracle(crv, str);
      forall lid: int, cp: int ::
        LOr.view_get_oracle(ovf, cp, lid)
        == (1 <= lid <= R.max_lookaround(re) && LidReachesVFinal(crv, str, ovf, lid, cp))
  {
    forall i: int ensures LidBuildOkAbove(CP.FFullCompilation(re), i) {
      AllLidsBuildOkAbove(re, i);
    }
    FBuildOracleCorrectAbove(re, str);
  }

  // ===========================================================================
  // THE NESTED ESTABLISHER (brick 4b at depth k): every lid of a nested-fragment
  // regex satisfies `LidBuildOkAbove` against `FFullCompilation(re)`. This is the
  // L4 analogue of `AllLidsBuildOk`, discharging the ADMITTED-gate form via the
  // nested build-code classification `NR.NestedCompileToWriteClassifiedAbove`
  // (which `NR.GatesAboveClassified` machinery + `LidsWellNested` supply).
  // ===========================================================================

  /** A lid OF a nested-fragment regex satisfies `LidBuildOkAbove`: recurse to the
      lookaround node owning `i` and classify its build code
      `compile_to_write(oracle_regex(la, body), i)`. The build regex is nested,
      lid-unique, and — by `LidsWellNested` — has every gate strictly above `i`,
      so `NR.NestedCompileToWriteClassifiedAbove` supplies the four conjuncts. */
  lemma NestedLidBuildOkAbove(re: R.regex, fc: CP.FCompiled, i: nat)
    requires NR.NestedFragmentRE(re)
    requires LT.LidsWellNested(re)
    requires LT.LookUnique(re)
    requires LT.LookTablesOk(re, fc)
    requires i in LT.LookIds(re)
    ensures LidBuildOkAbove(fc, i)
    decreases re
  {
    match re
    case Re_alt(r1, r2) =>
      if i in LT.LookIds(r1) { NestedLidBuildOkAbove(r1, fc, i); }
      else { NestedLidBuildOkAbove(r2, fc, i); }
    case Re_con(r1, r2) =>
      if i in LT.LookIds(r1) { NestedLidBuildOkAbove(r1, fc, i); }
      else { NestedLidBuildOkAbove(r2, fc, i); }
    case Re_quant(_, _, _, r1) => NestedLidBuildOkAbove(r1, fc, i);
    case Re_capture(_, r1) => NestedLidBuildOkAbove(r1, fc, i);
    case Re_lookaround(lid, la, body) =>
      assert lid >= 0;
      if (i as int) == lid {
        assert LT.LookEntryOk(fc, lid, la, body);
        var og := CP.oracle_regex(la, body);
        NR.OracleRegexNestedFragment(la, body);
        NR.OracleRegexLookUnique(la, body);
        NR.OracleRegexLookIds(la, body);   // LookIds(og) == LookIds(body)
        assert forall x: nat :: x in LT.LookIds(og) ==> x > lid;
        NR.NestedCompileToWriteClassifiedAbove(og, lid);
        assert AI.get_code_v(fc.f_look_build_bc, i) == CP.compile_to_write(og, lid);
      } else {
        assert i in LT.LookIds(body);
        NestedLidBuildOkAbove(body, fc, i);
      }
  }

  /** ESTABLISHER (brick 4b, depth k): every row of `FFullCompilation(re)`
      satisfies `LidBuildOkAbove` for a nested-fragment, well-nested, lid-unique
      `re` — the real lids by `NestedLidBuildOkAbove`, all other rows because they
      still hold the seed's empty bytecode. Discharges the sole hypothesis of
      `FBuildOracleCorrectAbove` for the NESTED fragment. */
  lemma AllLidsBuildOkAboveNested(re: R.regex, i: int)
    requires NR.NestedFragmentRE(re)
    requires LT.LidsWellNested(re)
    requires LT.LookUnique(re)
    ensures LidBuildOkAbove(CP.FFullCompilation(re), i)
  {
    var crv := CP.FFullCompilation(re);
    if i >= 0 && (i as nat) in LT.LookIds(re) {
      LT.FFullCompilationLookOk(re);
      NestedLidBuildOkAbove(re, crv, i as nat);
    } else {
      var maxlook := R.max_lookaround(re);
      var maxquant := R.max_quant(re);
      var nlook := if maxlook + 1 >= 0 then maxlook + 1 else 0;
      var nquant := if maxquant + 1 >= 0 then maxquant + 1 else 0;
      var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                               seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                               seq(nlook, k => []), seq(nlook, k => []),
                               seq(nlook, k => []), seq(nquant, k => []));
      assert crv == CP.FCompileExtra(re, seed);
      LT.FCompileExtraLookFrame(re, seed);
      if 0 <= i < |crv.f_look_build_bc| {
        assert LT.AgreeAt(seed, crv, i as nat);
        assert seed.f_look_build_bc[i] == [];
        assert AI.get_code_v(crv.f_look_build_bc, i) == [];
      } else {
        assert AI.get_code_v(crv.f_look_build_bc, i) == [];
      }
    }
  }

  /** STEP 3 (nested capstone) — THE §6.2 THEOREM FOR THE NESTED FRAGMENT, fully
      closed. For a nested-fragment, well-nested, lid-unique `re` (nesting to ANY
      depth, both lookahead and lookbehind flavours), column `lid` of the built
      oracle holds EXACTLY the `LidReachesVFinal` positions of that lid's build
      code — the genuinely GATED depth-k oracle correctness. Discharges
      `AllLidsBuildOkAboveNested` into `FBuildOracleCorrectAbove`. */
  lemma FBuildOracleCorrectAboveNested(re: R.regex, str: string)
    requires NR.NestedFragmentRE(re)
    requires LT.LidsWellNested(re)
    requires LT.LookUnique(re)
    ensures var crv := CP.FFullCompilation(re);
      var ovf := AI.FBuildOracle(crv, str);
      forall lid: int, cp: int ::
        LOr.view_get_oracle(ovf, cp, lid)
        == (1 <= lid <= R.max_lookaround(re) && LidReachesVFinal(crv, str, ovf, lid, cp))
  {
    forall i: int ensures LidBuildOkAbove(CP.FFullCompilation(re), i) {
      AllLidsBuildOkAboveNested(re, i);
    }
    FBuildOracleCorrectAbove(re, str);
  }

  /** `FBuildOracleCorrect` restated per lookaround, with the bytecode in its
      `lazy_prefix(body)` form — the interface the §6.3 bridge consumes. The
      row facts come from `FFullCompilationLookOk` at the call site. */
  lemma FBuildOracleCorrectAt(re: R.regex, str: string, lid: int, la: R.lookaround, body: R.regex, cp: int)
    requires NR.LookBehindFragmentRE(re)
    requires LT.LookUnique(re)
    requires LT.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires 1 <= lid
    // L3b: the oracle is built over the capture-STRIPPED body (a capturing
    // lookbehind's `oracle_regex` is `lazy_prefix(remove_capture(body))`).
    ensures LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid)
         == ORc.ReachesWrite(CP.compile_to_write(R.lazy_prefix(R.remove_capture(body)), lid), str, 0, lid, cp)
  {
    var crv := CP.FFullCompilation(re);
    FBuildOracleCorrect(re, str);
    // this row is a lookBEHIND, so its build is Forward and LidReaches is the
    // plain reachability the L1 chain consumes
    LidReachesIsReachesWrite(re, str, lid, cp);
    assert CP.oracle_regex(la, body) == R.lazy_prefix(R.remove_capture(body));
    assert AI.get_code_v(crv.f_look_build_bc, lid)
        == CP.compile_to_write(R.lazy_prefix(R.remove_capture(body)), lid);
    // lid is within 1..maxlook: the tables have maxlook+1 rows (seed lengths
    // survive the fold) and LookEntryOk puts lid inside them
    var maxlook0 := R.max_lookaround(re);
    var maxquant0 := R.max_quant(re);
    var nlook := if maxlook0 + 1 >= 0 then maxlook0 + 1 else 0;
    var nquant := if maxquant0 + 1 >= 0 then maxquant0 + 1 else 0;
    var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                             seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                             seq(nlook, k => []), seq(nlook, k => []),
                             seq(nlook, k => []), seq(nquant, k => []));
    assert crv == CP.FCompileExtra(re, seed);
    LT.FCompileExtraLookFrame(re, seed);
    assert |crv.f_look_build_bc| == nlook;
    assert lid <= maxlook0;
  }

  /** `FBuildOracleCorrectAt` for the NESTED fragment: the oracle bit is the
      V-MODEL reachability (`ReachesWriteV`, which crosses inner gates against
      the finished view) of the lid's build bytecode. Same shape as the look-free
      version but off `FBuildOracleCorrectAboveNested` + `LidReachesVFinal`. */
  lemma FBuildOracleCorrectAtNested(re: R.regex, str: string, lid: int, la: R.lookaround, body: R.regex, cp: int)
    requires NR.NestedFragmentRE(re)
    requires LT.LidsWellNested(re)
    requires LT.LookUnique(re)
    requires LT.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires 1 <= lid
    requires 0 <= cp <= |str|
    ensures LOr.view_get_oracle(AI.FBuildOracle(CP.FFullCompilation(re), str), cp, lid)
         <==> ORc.ReachesWriteV(CP.compile_to_write(R.lazy_prefix(R.remove_capture(body)), lid),
                                str, AI.FBuildOracle(CP.FFullCompilation(re), str), 0, lid, cp)
  {
    var crv := CP.FFullCompilation(re);
    var ovf := AI.FBuildOracle(crv, str);
    FBuildOracleCorrectAboveNested(re, str);         // oracle bit == LidReachesVFinal (for 1<=lid<=maxlook)
    assert crv.f_look_types[lid] == la;              // LookEntryOk
    assert LidDir(crv, lid) == LAnc.Forward;         // oracle_direction(lookbehind) == Forward
    // table size: lid <= maxlook0 (identical to the look-free version)
    var maxlook0 := R.max_lookaround(re);
    var maxquant0 := R.max_quant(re);
    var nlook := if maxlook0 + 1 >= 0 then maxlook0 + 1 else 0;
    var nquant := if maxquant0 + 1 >= 0 then maxquant0 + 1 else 0;
    var seed := CP.FCompiled(re, CP.compile_to_bytecode(R.lazy_prefix(re)), LCdn.compile_cdns(re),
                             seq(nlook, k => R.Lookahead), seq(nlook, k => R.Re_empty),
                             seq(nlook, k => []), seq(nlook, k => []),
                             seq(nlook, k => []), seq(nquant, k => []));
    assert crv == CP.FCompileExtra(re, seed);
    LT.FCompileExtraLookFrame(re, seed);
    assert |crv.f_look_build_bc| == nlook;
    assert lid <= maxlook0;
    // LidReachesVFinal (Forward branch) unfolds to ReachesWriteV of the build bytecode
    reveal LidReachesVFinal();
    assert CP.oracle_regex(la, body) == R.lazy_prefix(R.remove_capture(body));
    assert AI.get_code_v(crv.f_look_build_bc, lid)
        == CP.compile_to_write(R.lazy_prefix(R.remove_capture(body)), lid);
  }

  // ===========================================================================
  // The compiler / anchor-swap commutation
  //
  // A lookAHEAD's oracle build runs BACKWARD, and `Mirror.BackwardSweep-
  // Characterization` reads that build as a FORWARD run of `SwapAnchorsCode`
  // of the build bytecode.  To point the existing forward span bridge
  // (`ReachesWriteToMatches`) at it, the swapped bytecode must be recognised
  // as a compiled program.  It is: swapping anchors in the SOURCE regex and
  // then compiling is the same as compiling and then swapping anchors in the
  // BYTECODE, because `compile`'s treelist shape and label arithmetic branch
  // on nothing an anchor swap changes.  This retires the star-shape
  // restriction that previously made the swap the identity.
  // ===========================================================================

  /** `r` with every input anchor swapped (`Begin`<->`End`), structurally
      identical otherwise -- the regex-level analogue of
      `MIR.SwapAnchorsCode`. */
  function SwapAnchorsRegex(r: R.regex): R.regex
    decreases r
  {
    match r
    case Re_empty => r
    case Re_character(_) => r
    case Re_anchor(a) => R.Re_anchor(MIR.SwapAnchor(a))
    case Re_alt(r1, r2) => R.Re_alt(SwapAnchorsRegex(r1), SwapAnchorsRegex(r2))
    case Re_con(r1, r2) => R.Re_con(SwapAnchorsRegex(r1), SwapAnchorsRegex(r2))
    case Re_quant(nul, qid, q, r1) => R.Re_quant(nul, qid, q, SwapAnchorsRegex(r1))
    case Re_capture(cid, r1) => R.Re_capture(cid, SwapAnchorsRegex(r1))
    case Re_lookaround(lid, lk, r1) => R.Re_lookaround(lid, lk, SwapAnchorsRegex(r1))
  }

  /** The swap preserves the compile termination measure (it never changes a
      constructor). */
  lemma SwapAnchorsRsize(r: R.regex)
    ensures CP.rsize(SwapAnchorsRegex(r)) == CP.rsize(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => SwapAnchorsRsize(r1); SwapAnchorsRsize(r2);
    case Re_con(r1, r2) => SwapAnchorsRsize(r1); SwapAnchorsRsize(r2);
    case Re_quant(_, _, _, r1) => SwapAnchorsRsize(r1);
    case Re_capture(_, r1) => SwapAnchorsRsize(r1);
    case Re_lookaround(_, _, r1) => SwapAnchorsRsize(r1);
    case _ =>
  }

  /** `MIR.SwapAnchorsCode` lifted to the compiler's intermediate `treelist`,
      mapped over every leaf's instruction list. */
  function SwapAnchorsTreelist(t: CP.treelist): CP.treelist
    decreases t
  {
    match t
    case Leaf(l) => CP.Leaf(MIR.SwapAnchorsCode(l))
    case Concat(a, b) => CP.Concat(SwapAnchorsTreelist(a), SwapAnchorsTreelist(b))
  }

  /** The treelist swap, mapped over a sequence of treelists. */
  function SwapAnchorsTreelistSeq(ts: seq<CP.treelist>): seq<CP.treelist>
  {
    seq(|ts|, i requires 0 <= i < |ts| => SwapAnchorsTreelist(ts[i]))
  }

  /** The treelist swap distributes over `chain` (Dafny will not unfold
      `chain`'s slice recursion through `SwapAnchorsTreelist` on its own). */
  lemma SwapAnchorsChain(ts: seq<CP.treelist>)
    requires |ts| >= 1
    ensures SwapAnchorsTreelist(CP.chain(ts)) == CP.chain(SwapAnchorsTreelistSeq(ts))
    decreases |ts|
  {
    if |ts| == 1 {
      assert SwapAnchorsTreelistSeq(ts) == [SwapAnchorsTreelist(ts[0])];
    } else {
      SwapAnchorsChain(ts[..|ts| - 1]);
      assert SwapAnchorsTreelistSeq(ts)[..|ts| - 1] == SwapAnchorsTreelistSeq(ts[..|ts| - 1]);
      assert SwapAnchorsTreelistSeq(ts)[|ts| - 1] == SwapAnchorsTreelist(ts[|ts| - 1]);
      assert CP.chain(SwapAnchorsTreelistSeq(ts))
          == CP.Concat(CP.chain(SwapAnchorsTreelistSeq(ts)[..|ts| - 1]),
                       SwapAnchorsTreelistSeq(ts)[|ts| - 1]);
    }
  }

  /** Explicit-arity forms of `SwapAnchorsChain`, with the mapped list written
      out so Dafny can unify it with a compiled `chain([...])`. */
  lemma SwapChain3(a: CP.treelist, b: CP.treelist, c: CP.treelist)
    ensures SwapAnchorsTreelist(CP.chain([a, b, c]))
         == CP.chain([SwapAnchorsTreelist(a), SwapAnchorsTreelist(b), SwapAnchorsTreelist(c)])
  {
    SwapAnchorsChain([a, b, c]);
    assert SwapAnchorsTreelistSeq([a, b, c])
        == [SwapAnchorsTreelist(a), SwapAnchorsTreelist(b), SwapAnchorsTreelist(c)];
  }

  lemma SwapChain4(a: CP.treelist, b: CP.treelist, c: CP.treelist, d: CP.treelist)
    ensures SwapAnchorsTreelist(CP.chain([a, b, c, d]))
         == CP.chain([SwapAnchorsTreelist(a), SwapAnchorsTreelist(b),
                      SwapAnchorsTreelist(c), SwapAnchorsTreelist(d)])
  {
    SwapAnchorsChain([a, b, c, d]);
    assert SwapAnchorsTreelistSeq([a, b, c, d])
        == [SwapAnchorsTreelist(a), SwapAnchorsTreelist(b),
            SwapAnchorsTreelist(c), SwapAnchorsTreelist(d)];
  }

  /** A leaf of control instructions (no anchors) is fixed by the swap. */
  lemma SwapControlLeaf(l: seq<RB.instruction>)
    requires forall i :: 0 <= i < |l| ==> !l[i].AnchorAssertion?
    ensures MIR.SwapAnchorsCode(l) == l
  {
    MIR.SwapAnchorsCodeIdent(l);
  }

  /** The bytecode swap distributes over concatenation (a pointwise map). */
  lemma SwapAnchorsCodeAppend(a: seq<RB.instruction>, b: seq<RB.instruction>)
    ensures MIR.SwapAnchorsCode(a + b) == MIR.SwapAnchorsCode(a) + MIR.SwapAnchorsCode(b)
  {
    assert |MIR.SwapAnchorsCode(a + b)| == |a| + |b|;
    forall i | 0 <= i < |a| + |b|
      ensures MIR.SwapAnchorsCode(a + b)[i]
           == (MIR.SwapAnchorsCode(a) + MIR.SwapAnchorsCode(b))[i]
    {}
  }

  /** ...and therefore over `tl_flatten`. */
  lemma SwapAnchorsFlatten(t: CP.treelist, tail: seq<RB.instruction>)
    ensures MIR.SwapAnchorsCode(CP.tl_flatten(t, tail))
         == CP.tl_flatten(SwapAnchorsTreelist(t), MIR.SwapAnchorsCode(tail))
    decreases t
  {
    match t
    case Leaf(l) =>
      SwapAnchorsCodeAppend(l, tail);
    case Concat(a, b) =>
      SwapAnchorsFlatten(b, tail);
      SwapAnchorsFlatten(a, CP.tl_flatten(b, tail));
  }

  /** THE COMMUTATION, at the `compile` level: compiling the anchor-swapped
      regex yields the anchor-swapped treelist and the SAME next label. The
      companions `RepeatMinSwap`/`RepeatOptionalSwap` cover the mutually
      recursive quantifier helpers. */
  lemma CompileSwap(r: R.regex, nextl: RB.Label, ctype: CP.comp_type)
    ensures CP.compile(SwapAnchorsRegex(r), nextl, ctype).1 == CP.compile(r, nextl, ctype).1
    ensures CP.compile(SwapAnchorsRegex(r), nextl, ctype).0
         == SwapAnchorsTreelist(CP.compile(r, nextl, ctype).0)
    decreases CP.rsize(r), 0
  {
    SwapAnchorsRsize(r);
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_alt(r1, r2) =>
      var (l1, f1) := CP.compile(r1, nextl + 1, ctype);
      var (l2, f2) := CP.compile(r2, f1 + 1, ctype);
      CompileSwap(r1, nextl + 1, ctype);
      CompileSwap(r2, f1 + 1, ctype);
      SwapControlLeaf([RB.Fork(nextl + 1, f1 + 1)]);
      SwapControlLeaf([RB.Jmp(f2)]);
      SwapChain4(CP.Leaf([RB.Fork(nextl + 1, f1 + 1)]), l1, CP.Leaf([RB.Jmp(f2)]), l2);
    case Re_con(r1, r2) =>
      CompileSwap(r1, nextl, ctype);
      var f1 := CP.compile(r1, nextl, ctype).1;
      CompileSwap(r2, f1, ctype);
    case Re_capture(cid, r1) =>
      var (l1, f1) := CP.compile(r1, nextl + 1, ctype);
      CompileSwap(r1, nextl + 1, ctype);
      SwapControlLeaf([RB.SetRegisterToCP(CP.start_reg(cid))]);
      SwapControlLeaf([RB.SetRegisterToCP(CP.end_reg(cid))]);
      SwapChain3(CP.Leaf([RB.SetRegisterToCP(CP.start_reg(cid))]), l1,
                 CP.Leaf([RB.SetRegisterToCP(CP.end_reg(cid))]));
    case Re_lookaround(lid, lk, r1) =>
    case Re_quant(nul, qid, q, r1) =>
      if ctype == CP.Progress {
        if q.min > 0 && q.max == None && nul == R.NonNullable {
          RepeatMinSwap(q.min - 1, qid, r1, nextl, ctype);
          var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := CP.compile(r1, min_f + 1, ctype);
          CompileSwap(r1, min_f + 1, ctype);
          var fork := if q.greedy then RB.Fork(min_f, body_f + 1) else RB.Fork(body_f + 1, min_f);
          SwapControlLeaf([RB.SetQuantToClock(qid, false)]);
          SwapControlLeaf([fork]);
          SwapChain4(min_code, CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code,
                     CP.Leaf([fork]));
        } else if q.min > 0 && q.max == None && nul == R.CINullable && q.greedy {
          RepeatMinSwap(q.min - 1, qid, r1, nextl, ctype);
          var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := CP.compile(r1, min_f + 3, ctype);
          CompileSwap(r1, min_f + 3, ctype);
          SwapControlLeaf([RB.Fork(min_f + 1, body_f + 2), RB.SetQuantToClock(qid, false), RB.BeginLoop]);
          SwapControlLeaf([RB.EndLoop, RB.Fork(min_f + 1, body_f + 3), RB.SetQuantToClock(qid, true)]);
          SwapChain4(min_code,
                     CP.Leaf([RB.Fork(min_f + 1, body_f + 2), RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                     body_code,
                     CP.Leaf([RB.EndLoop, RB.Fork(min_f + 1, body_f + 3), RB.SetQuantToClock(qid, true)]));
        } else if q.min > 0 && q.max == None && nul == R.CDNullable && q.greedy {
          RepeatMinSwap(q.min - 1, qid, r1, nextl, ctype);
          var (min_code, min_f) := CP.repeat_min(q.min - 1, qid, r1, nextl, ctype);
          var (body_code, body_f) := CP.compile(r1, min_f + 3, ctype);
          CompileSwap(r1, min_f + 3, ctype);
          SwapControlLeaf([RB.Fork(min_f + 1, body_f + 2), RB.SetQuantToClock(qid, false), RB.BeginLoop]);
          SwapControlLeaf([RB.EndLoop, RB.Fork(min_f + 1, body_f + 4), RB.CheckNullable(qid), RB.SetQuantToClock(qid, true)]);
          SwapChain4(min_code,
                     CP.Leaf([RB.Fork(min_f + 1, body_f + 2), RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                     body_code,
                     CP.Leaf([RB.EndLoop, RB.Fork(min_f + 1, body_f + 4), RB.CheckNullable(qid), RB.SetQuantToClock(qid, true)]));
        } else {
          RepeatMinSwap(q.min, qid, r1, nextl, ctype);
          var (min_code, min_f) := CP.repeat_min(q.min, qid, r1, nextl, ctype);
          match q.max
          case None =>
            var (iter_code, iter_f) := CP.compile(r1, min_f + 3, ctype);
            CompileSwap(r1, min_f + 3, ctype);
            var fork := if q.greedy then RB.Fork(min_f + 1, iter_f + 2) else RB.Fork(iter_f + 2, min_f + 1);
            SwapControlLeaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]);
            SwapControlLeaf([RB.EndLoop, RB.Jmp(min_f)]);
            SwapChain4(min_code, CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]),
                       iter_code, CP.Leaf([RB.EndLoop, RB.Jmp(min_f)]));
          case Some(mx) =>
            RepeatOptionalSwap(mx - q.min, qid, r1, min_f, ctype, q.greedy);
        }
      } else {
        if q.min == 0 {
        } else if nul == R.NonNullable {
        } else if q.max == None && nul == R.CINullable && q.greedy {
        } else if q.max == None && nul == R.CDNullable && q.greedy {
        } else {
          CompileSwap(r1, nextl + 1, CP.ReconstructNulled);
        }
      }
  }

  lemma RepeatMinSwap(min: int, qid: R.quantid, r: R.regex, nextl: RB.Label, ctype: CP.comp_type)
    ensures CP.repeat_min(min, qid, SwapAnchorsRegex(r), nextl, ctype).1
         == CP.repeat_min(min, qid, r, nextl, ctype).1
    ensures CP.repeat_min(min, qid, SwapAnchorsRegex(r), nextl, ctype).0
         == SwapAnchorsTreelist(CP.repeat_min(min, qid, r, nextl, ctype).0)
    decreases CP.rsize(r) + 1, min
  {
    SwapAnchorsRsize(r);
    if min <= 0 {
    } else {
      var (body_code, new_f) := CP.compile(r, nextl + 1, ctype);
      CompileSwap(r, nextl + 1, ctype);
      var (next_code, next_f) := CP.repeat_min(min - 1, qid, r, new_f, ctype);
      RepeatMinSwap(min - 1, qid, r, new_f, ctype);
      SwapControlLeaf([RB.SetQuantToClock(qid, false)]);
      SwapChain3(CP.Leaf([RB.SetQuantToClock(qid, false)]), body_code, next_code);
    }
  }

  lemma RepeatOptionalSwap(nb: int, qid: R.quantid, r: R.regex, nextl: RB.Label,
                           ctype: CP.comp_type, greedy: bool)
    ensures CP.repeat_optional(nb, qid, SwapAnchorsRegex(r), nextl, ctype, greedy).1
         == CP.repeat_optional(nb, qid, r, nextl, ctype, greedy).1
    ensures CP.repeat_optional(nb, qid, SwapAnchorsRegex(r), nextl, ctype, greedy).0
         == SwapAnchorsTreelist(CP.repeat_optional(nb, qid, r, nextl, ctype, greedy).0)
    decreases CP.rsize(r) + 1, nb
  {
    SwapAnchorsRsize(r);
    if nb <= 0 {
    } else {
      var (body_code, new_f) := CP.compile(r, nextl + 3, ctype);
      CompileSwap(r, nextl + 3, ctype);
      var (next_code, next_f) := CP.repeat_optional(nb - 1, qid, r, new_f + 1, ctype, greedy);
      RepeatOptionalSwap(nb - 1, qid, r, new_f + 1, ctype, greedy);
      var fork := if greedy then RB.Fork(nextl + 1, next_f) else RB.Fork(next_f, nextl + 1);
      SwapControlLeaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]);
      SwapControlLeaf([RB.EndLoop]);
      SwapChain4(CP.Leaf([fork, RB.SetQuantToClock(qid, false), RB.BeginLoop]), body_code,
                 CP.Leaf([RB.EndLoop]), next_code);
    }
  }

  /** THE COMMUTATION, at the `compile_to_write` level -- the form the oracle
      column chain consumes: swapping the anchors of a build program is the
      same as building the anchor-swapped regex. */
  lemma CompileToWriteSwap(r: R.regex, lid: R.lookid)
    ensures MIR.SwapAnchorsCode(CP.compile_to_write(r, lid))
         == CP.compile_to_write(SwapAnchorsRegex(r), lid)
  {
    CompileSwap(r, 0, CP.Progress);
    SwapAnchorsFlatten(CP.compile(r, 0, CP.Progress).0, [RB.WriteOracle(lid)]);
    assert MIR.SwapAnchorsCode([RB.WriteOracle(lid)]) == [RB.WriteOracle(lid)];
  }

  /** `lazy_prefix` (a `.*?` prefix) is anchor-free, so the swap slides through
      it. */
  lemma SwapAnchorsLazyPrefix(r: R.regex)
    ensures SwapAnchorsRegex(R.lazy_prefix(r)) == R.lazy_prefix(SwapAnchorsRegex(r))
  {}

  /** A BACKWARD build's oracle column is the FORWARD reachability of the
      anchor-swapped build program over the reversed string -- the general
      form of `LidReachesBackwardNoAnchor`, with no anchor-free requirement,
      since `LidReaches`'s backward branch is already stated on the swapped
      code. */
  lemma LidReachesBackward(crv: CP.FCompiled, str: string, i: int, cp: int)
    requires LidDir(crv, i) == LAnc.Backward
    ensures LidReaches(crv, str, i, cp)
        <==> ORc.ReachesWrite(MIR.SwapAnchorsCode(AI.get_code_v(crv.f_look_build_bc, i)),
                              LC.Reverse(str), 0, i, MIR.Mirror(cp, |str|))
  {
    reveal LidReaches();
  }
}
