// L5 CAPTURES — BRICK 0: the KIND-FLIP reversal (the missing mirror ingredient).
//
// WHY THIS FILE EXISTS. Every nested-lookbehind spec-mirror attempt died on the
// same rock, proved by `GateAgreeIsFalse` (TreeMirrorLk.dfy): under the
// kind-PRESERVING reversal (`SD.RevL` / `XRev` keep `Lookbehind` a
// `Lookbehind`), a mirrored inner look re-walks its body in the SAME intrinsic
// direction over the swapped window and reads the OPPOSITE side of the point.
// The constraint "the spec reversal must preserve look kinds" was inherited
// from the ENGINE's `reverse_regex` — but that inheritance is an ILLUSION:
//
//   THE MAIN BYTECODE IS LOOK-KIND-BLIND. `CP.compile`'s lookaround case
//   (Compiler.dfy:160-165) emits the SAME single `CheckOracle(lid)` /
//   `NegCheckOracle(lid)` leaf for ahead and behind — only POSITIVITY reaches
//   the instruction stream; the body lives in the per-look tables. So the
//   engine cannot distinguish a regex from its kind-FLIPPED image, and the
//   spec-side reversal is free to flip Lookbehind <-> Lookahead — the
//   CLASSICAL reversal duality, under which a mirrored look walks the OTHER
//   direction over the swapped window and reads the SAME chars
//   (`SD.ReadCharSwap` is exactly this transport at the char level; the
//   look-free mirror `TM.ComputeTreeReverse` is ALREADY the flip mirror
//   restricted to bodies with nothing to flip).
//
// This file proves the two wedge facts, machine-checked:
//   (1) `FlipCompileToBytecode` — `compile_to_bytecode(FlipRE(r)) ==
//       compile_to_bytecode(r)`: the flip is invisible to the engine, so the
//       T2a mirrored forward run of `compile(XRev(body))` IS a run of
//       `compile(FlipRE(XRev(body)))`, whose looks are kind-flipped — i.e.
//       LB-only-nested bodies land in the L4 forward keystone's fragment.
//   (2) `FlipGateAgreeAtDeadEndWitness` / `FlipGateAgreeCharacter` — the FLIP
//       gate agreement is TRUE exactly where the no-flip `GateAgree` is proven
//       FALSE (same witness input), and holds at EVERY input for a Character
//       body. The dead-end was the missing flip, not the mirror idea.
// Plus the plumbing the campaign needs: `FlipL`/`FlipRE` involutions,
// `TranslateFlip` (Translate commutes with the flip), and reverse/anchor-swap
// commutations.
//
// CONSUMED BY (the flip route, see L5_HANDOFF.md §5-NEW): the nested LB
// keystone ties raB (backward replay) to the spec backward tree via
//   T2a `BackwardReplayMirrorNested`  (engine mirror, kind-preserving, DONE)
//   + (1)                            (present the mirrored bytecode as the
//                                     flipped regex's compile)
//   + `LkReplayMatchesSpecNested`-chain at `FlipRE(XRev(body))`
//                                    (the L4 FORWARD keystone — its premises
//                                     carry NO NoPosLookbehind; the flipped
//                                     looks are Lookahead-flavoured)
//   + the FLIP spec tree mirror      (TRUE where the no-flip one is vacuous)
//   + `MirrorOracleOk` for the flipped looks-map under `MirrorView(ov)`
//                                    (non-circular: flip makes the mirrored
//                                     walk read the same chars).
/** L5 brick 0: the look-kind flip — engine-invisible (`FlipCompileToBytecode`),
    Translate-commuting (`TranslateFlip`), and the cure for the `GateAgreeIsFalse`
    dead-end (`FlipGateAgreeAtDeadEndWitness`). */
module LindenElkFlipRev {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import SD = LindenSpanDuality
  import T = LindenElkTranslate
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import OBu = LindenElkOracleBuild

  // ===========================================================================
  // The flips (kind-only; ids, structure, and everything else untouched)
  // ===========================================================================

  /** RegElk look-kind flip: ahead <-> behind, positivity preserved. */
  function FlipLkRE(la: R.lookaround): R.lookaround {
    match la
    case Lookahead => R.Lookbehind
    case Lookbehind => R.Lookahead
    case NegLookahead => R.NegLookbehind
    case NegLookbehind => R.NegLookahead
  }

  /** Linden look-kind flip. */
  function FlipLk(lk: L.Lookaround): L.Lookaround {
    match lk
    case LookAhead => L.LookBehind
    case LookBehind => L.LookAhead
    case NegLookAhead => L.NegLookBehind
    case NegLookBehind => L.NegLookAhead
  }

  /** Flip every look kind in a RegElk regex; nothing else changes. */
  function FlipRE(r: R.regex): R.regex
    decreases r
  {
    match r
    case Re_empty => r
    case Re_character(_) => r
    case Re_anchor(_) => r
    case Re_alt(r1, r2) => R.Re_alt(FlipRE(r1), FlipRE(r2))
    case Re_con(r1, r2) => R.Re_con(FlipRE(r1), FlipRE(r2))
    case Re_quant(nul, qid, q, r1) => R.Re_quant(nul, qid, q, FlipRE(r1))
    case Re_capture(cid, r1) => R.Re_capture(cid, FlipRE(r1))
    case Re_lookaround(lid, la, r1) => R.Re_lookaround(lid, FlipLkRE(la), FlipRE(r1))
  }

  /** Flip every look kind in a Linden regex. */
  function FlipL(r: L.Regex): L.Regex
    decreases r
  {
    match r
    case Epsilon => r
    case Character(_) => r
    case AnchorR(_) => r
    case Disjunction(r1, r2) => L.Disjunction(FlipL(r1), FlipL(r2))
    case Sequence(r1, r2) => L.Sequence(FlipL(r1), FlipL(r2))
    case Quantified(g, mn, d, r1) => L.Quantified(g, mn, d, FlipL(r1))
    case Group(gid, r1) => L.Group(gid, FlipL(r1))
    case LookaroundR(lk, r1) => L.LookaroundR(FlipLk(lk), FlipL(r1))
    case Backreference(_) => r
  }

  // ---------------------------------------------------------------------------
  // Basic laws
  // ---------------------------------------------------------------------------

  /** The flip swaps the walk direction and preserves positivity — the two
      facts that make it the CORRECT reversal companion: `LkDir` composes with
      string reversal, `Positivity` picks Check vs NegCheck. */
  lemma FlipLkLaws(lk: L.Lookaround)
    ensures L.LkDir(FlipLk(lk)) != L.LkDir(lk)
    ensures L.Positivity(FlipLk(lk)) == L.Positivity(lk)
    ensures FlipLk(FlipLk(lk)) == lk
  {}

  lemma FlipLkRELaws(la: R.lookaround)
    ensures FlipLkRE(FlipLkRE(la)) == la
    ensures T.TrLookaround(FlipLkRE(la)) == FlipLk(T.TrLookaround(la))
  {}

  lemma FlipREInvolution(r: R.regex)
    ensures FlipRE(FlipRE(r)) == r
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipREInvolution(r1); FlipREInvolution(r2);
    case Re_con(r1, r2) => FlipREInvolution(r1); FlipREInvolution(r2);
    case Re_quant(_, _, _, r1) => FlipREInvolution(r1);
    case Re_capture(_, r1) => FlipREInvolution(r1);
    case Re_lookaround(_, la, r1) => FlipLkRELaws(la); FlipREInvolution(r1);
    case _ =>
  }

  lemma FlipLInvolution(r: L.Regex)
    ensures FlipL(FlipL(r)) == r
    decreases r
  {
    match r
    case Disjunction(r1, r2) => FlipLInvolution(r1); FlipLInvolution(r2);
    case Sequence(r1, r2) => FlipLInvolution(r1); FlipLInvolution(r2);
    case Quantified(_, _, _, r1) => FlipLInvolution(r1);
    case Group(_, r1) => FlipLInvolution(r1);
    case LookaroundR(lk, r1) => FlipLkLaws(lk); FlipLInvolution(r1);
    case _ =>
  }

  /** The flip commutes with the engine reversal (both are structure-preserving
      node maps touching disjoint payloads). */
  lemma FlipReverseComm(r: R.regex)
    ensures R.reverse_regex(FlipRE(r)) == FlipRE(R.reverse_regex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipReverseComm(r1); FlipReverseComm(r2);
    case Re_con(r1, r2) => FlipReverseComm(r1); FlipReverseComm(r2);
    case Re_quant(_, _, _, r1) => FlipReverseComm(r1);
    case Re_capture(_, r1) => FlipReverseComm(r1);
    case Re_lookaround(_, _, r1) => FlipReverseComm(r1);
    case _ =>
  }

  /** The flip commutes with the anchor swap (disjoint payloads again). */
  lemma FlipSwapAnchorsComm(r: R.regex)
    ensures OBu.SwapAnchorsRegex(FlipRE(r)) == FlipRE(OBu.SwapAnchorsRegex(r))
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipSwapAnchorsComm(r1); FlipSwapAnchorsComm(r2);
    case Re_con(r1, r2) => FlipSwapAnchorsComm(r1); FlipSwapAnchorsComm(r2);
    case Re_quant(_, _, _, r1) => FlipSwapAnchorsComm(r1);
    case Re_capture(_, r1) => FlipSwapAnchorsComm(r1);
    case Re_lookaround(_, _, r1) => FlipSwapAnchorsComm(r1);
    case _ =>
  }

  // ---------------------------------------------------------------------------
  // Translate commutation
  // ---------------------------------------------------------------------------

  /** `TransWf` never looks at a look kind. */
  lemma FlipTransWf(r: R.regex)
    ensures T.TransWf(FlipRE(r)) == T.TransWf(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => FlipTransWf(r1); FlipTransWf(r2);
    case Re_con(r1, r2) => FlipTransWf(r1); FlipTransWf(r2);
    case Re_quant(_, _, _, r1) => FlipTransWf(r1);
    case Re_capture(_, r1) => FlipTransWf(r1);
    case Re_lookaround(_, _, r1) => FlipTransWf(r1);
    case _ =>
  }

  /** Translate commutes with the flip. */
  lemma TranslateFlip(r: R.regex)
    requires T.TransWf(r)
    ensures T.TransWf(FlipRE(r))
    ensures T.Translate(FlipRE(r)) == FlipL(T.Translate(r))
    decreases r
  {
    FlipTransWf(r);
    match r
    case Re_alt(r1, r2) => TranslateFlip(r1); TranslateFlip(r2);
    case Re_con(r1, r2) => TranslateFlip(r1); TranslateFlip(r2);
    case Re_quant(_, _, _, r1) => TranslateFlip(r1);
    case Re_capture(_, r1) => TranslateFlip(r1);
    case Re_lookaround(_, la, r1) => FlipLkRELaws(la); TranslateFlip(r1);
    case _ =>
  }

  // ===========================================================================
  // WEDGE (1): the main bytecode is look-kind-blind
  // ===========================================================================
  //
  // `CP.compile`'s lookaround case emits `CheckOracle(lid)` for BOTH positive
  // kinds and `NegCheckOracle(lid)` for BOTH negative kinds, never destructs
  // the body, and pays `nextl + 1` uniformly — so the flip is invisible to the
  // whole compilation. Mutual induction mirroring compile/repeat_min/
  // repeat_optional's own termination measure.

  lemma FlipRepeatMin(min: int, qid: R.quantid, r: R.regex, nextl: RB.Label, ctype: CP.comp_type)
    ensures CP.repeat_min(min, qid, FlipRE(r), nextl, ctype)
         == CP.repeat_min(min, qid, r, nextl, ctype)
    decreases CP.rsize(r) + 1, min
  {
    if min <= 0 {
    } else {
      FlipCompile(r, nextl + 1, ctype);
      var (_, new_f) := CP.compile(r, nextl + 1, ctype);
      FlipRepeatMin(min - 1, qid, r, new_f, ctype);
    }
  }

  lemma FlipRepeatOptional(nb: int, qid: R.quantid, r: R.regex, nextl: RB.Label,
                           ctype: CP.comp_type, greedy: bool)
    ensures CP.repeat_optional(nb, qid, FlipRE(r), nextl, ctype, greedy)
         == CP.repeat_optional(nb, qid, r, nextl, ctype, greedy)
    decreases CP.rsize(r) + 1, nb
  {
    if nb <= 0 {
    } else {
      FlipCompile(r, nextl + 3, ctype);
      var (_, new_f) := CP.compile(r, nextl + 3, ctype);
      FlipRepeatOptional(nb - 1, qid, r, new_f + 1, ctype, greedy);
    }
  }

  /** THE WEDGE: compiling the kind-flipped regex yields IDENTICAL code and
      labels. The engine cannot see the flip. */
  lemma FlipCompile(r: R.regex, nextl: RB.Label, ctype: CP.comp_type)
    ensures CP.compile(FlipRE(r), nextl, ctype) == CP.compile(r, nextl, ctype)
    decreases CP.rsize(r), 0
  {
    match r
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(lid, la, r1) =>
      // both positive kinds emit CheckOracle(lid); both negatives NegCheckOracle(lid)
    case Re_con(r1, r2) =>
      FlipCompile(r1, nextl, ctype);
      var (_, f1) := CP.compile(r1, nextl, ctype);
      FlipCompile(r2, f1, ctype);
    case Re_alt(r1, r2) =>
      FlipCompile(r1, nextl + 1, ctype);
      var (_, f1) := CP.compile(r1, nextl + 1, ctype);
      FlipCompile(r2, f1 + 1, ctype);
    case Re_capture(cid, r1) =>
      FlipCompile(r1, nextl + 1, ctype);
    case Re_quant(nul, qid, q, r1) =>
      if ctype == CP.Progress {
        if q.min > 0 && q.max == None && nul == R.NonNullable {
          FlipRepeatMin(q.min - 1, qid, r1, nextl, ctype);
          var (_, min_f) := CP.repeat_min(q.min - 1, qid, r1, nextl, ctype);
          FlipCompile(r1, min_f + 1, ctype);
        } else if q.min > 0 && q.max == None && nul == R.CINullable && q.greedy {
          FlipRepeatMin(q.min - 1, qid, r1, nextl, ctype);
          var (_, min_f) := CP.repeat_min(q.min - 1, qid, r1, nextl, ctype);
          FlipCompile(r1, min_f + 3, ctype);
        } else if q.min > 0 && q.max == None && nul == R.CDNullable && q.greedy {
          FlipRepeatMin(q.min - 1, qid, r1, nextl, ctype);
          var (_, min_f) := CP.repeat_min(q.min - 1, qid, r1, nextl, ctype);
          FlipCompile(r1, min_f + 3, ctype);
        } else {
          FlipRepeatMin(q.min, qid, r1, nextl, ctype);
          var (_, min_f) := CP.repeat_min(q.min, qid, r1, nextl, ctype);
          match q.max {
            case None => FlipCompile(r1, min_f + 3, ctype);
            case Some(mx) => FlipRepeatOptional(mx - q.min, qid, r1, min_f, ctype, q.greedy);
          }
        }
      } else {
        if q.min == 0 {
        } else if nul == R.NonNullable {
        } else if q.max == None && nul == R.CINullable && q.greedy {
        } else if q.max == None && nul == R.CDNullable && q.greedy {
        } else {
          FlipCompile(r1, nextl + 1, CP.ReconstructNulled);
        }
      }
  }

  /** The runnable-bytecode corollary the keystone consumes: the T2a mirrored
      forward bytecode `compile_to_bytecode(XRev(body))` IS
      `compile_to_bytecode(FlipRE(XRev(body)))`. */
  lemma FlipCompileToBytecode(r: R.regex)
    ensures CP.compile_to_bytecode(FlipRE(r)) == CP.compile_to_bytecode(r)
  {
    FlipCompile(r, 0, CP.Progress);
  }

  /** Same for the oracle-build form. */
  lemma FlipCompileToWrite(r: R.regex, l: R.lookid)
    ensures CP.compile_to_write(FlipRE(r), l) == CP.compile_to_write(r, l)
  {
    FlipCompile(r, 0, CP.Progress);
  }

  // ===========================================================================
  // WEDGE (2): the flip CURES the `GateAgreeIsFalse` dead-end
  // ===========================================================================

  /** The FLIP gate agreement: the body's LkDir walk at `inp2` vs the
      kind-FLIPPED reversal's walk — in the FLIPPED direction — over the
      swapped window. Contrast `GateAgree` (TreeMirrorLk.dfy), which keeps
      `L.LkDir(lk)` on both sides and is PROVEN unsatisfiable
      (`GateAgreeIsFalse`). */
  ghost predicate FlipGateAgree(rer: LW.RegExpRecord, lk: L.Lookaround, r1: L.Regex, inp2: LC.Input) {
    LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inp2, LG.Empty, L.LkDir(lk)),
               LG.Empty, inp2, L.LkDir(lk)).Some?
    == LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(FlipL(SD.RevL(r1)))], SD.SwapInput(inp2), LG.Empty,
                               L.LkDir(FlipLk(lk))),
                  LG.Empty, SD.SwapInput(inp2), L.LkDir(FlipLk(lk))).Some?
  }

  /** The flip agreement holds AT THE EXACT `GateAgreeIsFalse` WITNESS: same
      look kind, same Character body, same input where the no-flip mirror is
      disproved. The flipped side walks Forward over the swapped window and
      reads the SAME char ('a', the char before the point) that the original
      backward walk reads. */
  lemma FlipGateAgreeAtDeadEndWitness(rer: LW.RegExpRecord, cd: LC.CharDescr)
    requires LC.CharMatch(rer, 'a', cd) && !LC.CharMatch(rer, 'b', cd)
    ensures FlipGateAgree(rer, L.LookBehind, L.Character(cd), LC.Input(['b'], ['a']))
  {
    var r1 := L.Character(cd);
    var inp2 := LC.Input(['b'], ['a']);
    var sinp := SD.SwapInput(inp2);
    assert L.LkDir(L.LookBehind) == WP.Backward;
    assert SD.RevL(r1) == r1 && FlipL(r1) == r1;
    assert L.LkDir(FlipLk(L.LookBehind)) == WP.Forward;
    FU.ComputeTrRw(rer, [LS.Areg(r1)], inp2, LG.Empty, WP.Backward);
    FU.ComputeTrRw(rer, [LS.Areg(r1)], sinp, LG.Empty, WP.Forward);
    assert inp2.pref == ['a'] && inp2.pref[0] == 'a';
    assert LC.ReadChar(rer, cd, inp2, WP.Backward).Some?;
    assert sinp == LC.Input(['a'], ['b']);
    assert sinp.next == ['a'] && sinp.next[0] == 'a';
    assert LC.ReadChar(rer, cd, sinp, WP.Forward).Some?;
  }

  /** Stronger vacuity insurance: for a Character body the flip agreement holds
      at EVERY input (both kinds of positive look) — `SD.ReadCharSwap` is
      exactly the flip transport at the read level. */
  lemma FlipGateAgreeCharacter(rer: LW.RegExpRecord, cd: LC.CharDescr, inp2: LC.Input)
    ensures FlipGateAgree(rer, L.LookBehind, L.Character(cd), inp2)
  {
    var r1 := L.Character(cd);
    var sinp := SD.SwapInput(inp2);
    assert SD.RevL(r1) == r1 && FlipL(r1) == r1;
    assert L.LkDir(L.LookBehind) == WP.Backward;
    assert L.LkDir(FlipLk(L.LookBehind)) == WP.Forward;
    FU.ComputeTrRw(rer, [LS.Areg(r1)], inp2, LG.Empty, WP.Backward);
    FU.ComputeTrRw(rer, [LS.Areg(r1)], sinp, LG.Empty, WP.Forward);
    SD.ReadCharSwap(rer, cd, inp2);
  }
}
