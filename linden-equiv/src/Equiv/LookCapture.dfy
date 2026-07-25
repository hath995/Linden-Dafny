// Lookaround campaign (L1), §6.6: the lookaround CAPTURE pass leaves the
// answer alone.
//
// After the main search, `FBuildCapture` runs `FLookLoop`: for every POSITIVE
// lookaround whose match position was recorded, it replays that lookaround's
// capture bytecode and keeps the replay's registers. MainTheorem used to get
// "this changes nothing" for free from `max_lookaround == 0`; at L1 it is still
// true, but for a reason that has to be proved — the body is capture-free, so:
//
//   * the replay writes no capture register (`NR.NoCaptureInstrRE` +
//     `CM.FFindMatchCapFrame`),
//   * it writes no look register either (its code is look-free, so
//     `CM.FFindMatchLookFrame` at the empty id set),
//   * it writes quant registers only at the BODY's own ids
//     (`PIV.QuantWriteIdsRE` + `CM.FFindMatchQuantFrame`), and the filter never
//     reads those (`PIV.FilterCaptureQcFrameOutside` +
//     `PIV.QuantIdsLooksDisjoint`).
//
// So `filter_reset` over the main ast — which is the whole answer — comes out
// the same. This file assembles those facts; `FLookLoopFilterFrame` is the
// statement `FBuildCaptureUnfold` wants.
include "PikeSimRE.dfy"
include "LookTables.dfy"
include "OracleBuild.dfy"

/** §6.6: the lookaround capture pass is invisible to the final answer. */
module LindenElkLookCapture {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import CP = Compiler
  import AI = ArrayInterp
  import AReg = Array_Regs
  import LOr = Oracle
  import LAnc = Anchors
  import LCdn = Cdn
  import NR = LindenElkNfaRep
  import PIV = LindenElkPikeInv
  import CM = LindenElkClockMono
  import LTB = LindenElkLookTables
  import OBu = LindenElkOracleBuild

  // ===========================================================================
  // One replay
  // ===========================================================================

  /** `PIV.QuantIds` as a set of `int`s — the shape the register frames index
      by. */
  ghost function QIdsInt(r: R.regex): set<int> {
    set q: nat | q in PIV.QuantIds(r) :: q as int
  }

  /** A lookaround-free regex has unique (vacuously) lookaround ids. */
  lemma LookFreeLookUnique(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures LTB.LookUnique(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeLookUnique(r1); LookFreeLookUnique(r2); OBu.LookFreeNoIds(r1); OBu.LookFreeNoIds(r2);
    case Re_con(r1, r2) => LookFreeLookUnique(r1); LookFreeLookUnique(r2); OBu.LookFreeNoIds(r1); OBu.LookFreeNoIds(r2);
    case Re_quant(_, _, _, r1) => LookFreeLookUnique(r1);
    case Re_capture(_, r1) => LookFreeLookUnique(r1);
    case _ =>
  }

  /** The compiled capture bytecode of an L1 lookaround is classified: no
      capture write, no gate, and every quant write inside the body's ids. */
  lemma CaptureCodeClassified(la: R.lookaround, body: R.regex)
    requires NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.QuantUnique(body)
    requires la.Lookbehind? || la.NegLookbehind?
    ensures var code := CP.compile_to_bytecode(CP.capture_regex(la, body));
      CM.NoCaptureWriteCode(code)
      && CM.LookChecksInside(code, {})
      && CM.QuantWritesInside(code, QIdsInt(body))
  {
    var cr := CP.capture_regex(la, body);
    PIV.CaptureRegexFragment(la, body);
    PIV.ReverseQuantUnique(body);
    assert PIV.QuantUnique(cr) by {
      if la.Lookbehind? { assert cr == R.reverse_regex(body); } else { assert cr == R.Re_empty; }
    }
    LookFreeLookUnique(cr);
    var code := CP.compile_to_bytecode(cr);
    var next := CP.compile(cr, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(cr);
    var endl: nat := next as nat;
    assert NR.NfaRepRE(cr, code, 0, endl)
        && NR.GetPcRE(code, endl) == Some(RB.Accept) && |code| == endl + 1;

    forall pc: nat | pc < |code|
      ensures !code[pc].SetRegisterToCP?
      ensures !code[pc].CheckOracle? && !code[pc].NegCheckOracle?
      ensures code[pc].SetQuantToClock? ==>
                code[pc].sq >= 0 && (code[pc].sq as nat) in PIV.QuantIds(body)
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc != endl {
        assert pc < endl;
        NR.NoCaptureInstrRE(cr, code, 0, endl, pc);
        PIV.LookCheckIdsRE(cr, code, 0, endl, pc);
        PIV.QuantWriteIdsRE(cr, code, 0, endl, pc);
        OBu.LookFreeNoIds(cr);                       // look-free: LookIds(cr) == {}
        if la.Lookbehind? {
          PIV.ReverseQuantIds(body);
          assert cr == R.reverse_regex(body);
        }
      }
    }
  }

  // ===========================================================================
  // The whole loop — NOT YET PROVED
  // ===========================================================================
  //
  // The remaining statement is
  //
  //   lemma FLookLoopFilterFrame(crv, str, lid, maxlook, cap, lk, qt, ov, mainast)
  //     requires LookBehindFragmentRE(mainast) && QuantUnique(mainast)
  //     requires forall l :: get_cp(lk, l).Some? && lid <= l <= maxlook ==>
  //                <l names a real node of mainast, with its table row and its
  //                 L1 body facts, and QuantIds(body) <= QuantIdsInLooks(mainast)>
  //     ensures var res := FLookLoop(crv, str, lid, maxlook, cap, lk, qt, ov);
  //       filter_reset(mainast, res.0, res.1, res.2, -1)
  //         == filter_reset(mainast, cap, lk, qt, -1)
  //     decreases maxlook - lid
  //
  // by induction on `maxlook - lid`. Per step: `None`/non-capture-type lids
  // recurse unchanged; a recorded positive lid replays
  // `compile_to_bytecode(capture_regex(la, body))`, and
  //
  //   * `CaptureCodeClassified` + `CM.FFindMatchCapFrame` give `ncap == cap`,
  //   * `CaptureCodeClassified` + `CM.FFindMatchLookFrame` (at the empty id
  //     set) give `nlk == lk`,
  //   * `CaptureCodeClassified` + `CM.FFindMatchQuantFrame` give `nqt == qt`
  //     outside the body's ids, which by `PIV.QuantIdsLooksDisjoint` are
  //     disjoint from `QuantIdsOutsideLooks(mainast)`, so
  //     `PIV.FilterCaptureFullOutside` leaves the filter where it was,
  //   * `FReconstructPlus` is the identity by `FNulledPlusIdentity`, whose
  //     all-negative-quant-values hypothesis survives the replay (its writes
  //     are `SetQuantToClock(_, false)`, i.e. value `None`).
  //
  // The invariant the induction carries is that the look bank is unchanged and
  // the quant values stay negative, so the hypotheses hold at `lid + 1`.
}
