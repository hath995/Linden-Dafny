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
  import NI = LindenElkNestInv
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

  /** A capture-free regex has (vacuously) unique capture ids. */
  lemma CaptureFreeCapUnique(r: R.regex)
    requires NR.CaptureFreeRE(r)
    ensures PIV.CapUnique(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      CaptureFreeCapUnique(r1); CaptureFreeCapUnique(r2);
      PIV.CaptureFreeNoCapIds(r1); PIV.CaptureFreeNoCapIds(r2);
    case Re_con(r1, r2) =>
      CaptureFreeCapUnique(r1); CaptureFreeCapUnique(r2);
      PIV.CaptureFreeNoCapIds(r1); PIV.CaptureFreeNoCapIds(r2);
    case Re_quant(_, _, _, r1) => CaptureFreeCapUnique(r1);
    case Re_lookaround(_, _, r1) => CaptureFreeCapUnique(r1);
    case _ =>
  }

  /** The compiled capture bytecode of an L1 lookaround is classified: no
      capture write, no gate, and every quant write inside the body's ids. */
  lemma CaptureCodeClassified(la: R.lookaround, body: R.regex)
    requires NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    requires PIV.QuantUnique(body)
    ensures var code := CP.compile_to_bytecode(CP.capture_regex(la, body));
      CM.NoCaptureWriteCode(code)
      && CM.LookChecksInside(code, {})
      && CM.NoLookWriteCode(code)
      && CM.QuantWritesInside(code, QIdsInt(body))
      && (forall pc: nat :: pc < |code| ==> (code[pc].SetQuantToClock? ==> !code[pc].sb))
  {
    var cr := CP.capture_regex(la, body);
    PIV.CaptureRegexFragment(la, body);
    PIV.ReverseQuantUnique(body);
    assert PIV.QuantUnique(cr) by {
      // three shapes: reversed body (lookbehind), the body itself
      // (lookahead), or empty (either negative flavour)
      if la.Lookbehind? { assert cr == R.reverse_regex(body); }
      else if la.Lookahead? { assert cr == body; }
      else { assert cr == R.Re_empty; }
    }
    LookFreeLookUnique(cr);
    PIV.CaptureFreeNoCapIds(cr);
    CaptureFreeCapUnique(cr);
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
      ensures code[pc].SetQuantToClock? ==> !code[pc].sb
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc != endl {
        assert pc < endl;
        NR.NoCaptureInstrRE(cr, code, 0, endl, pc);
        NI.CodeShapeAt(cr, code, 0, endl, pc);       // pins `!bb` on every stamp
        PIV.LookCheckIdsRE(cr, code, 0, endl, pc);
        PIV.QuantWriteIdsRE(cr, code, 0, endl, pc);
        OBu.LookFreeNoIds(cr);                       // look-free: LookIds(cr) == {}
        if la.Lookbehind? {
          PIV.ReverseQuantIds(body);
          assert cr == R.reverse_regex(body);
        } else if la.Lookahead? {
          assert cr == body;                         // ids are the body's own
        }
      }
    }
  }

  /** A LOOK-free body's compiled bytecode writes no look register — it has no
      `CheckOracle`/`NegCheckOracle` at all (their `col`/`ncl` would have to be
      in `LookIds(body) == {}`). Capture-independent; the L3a analogue of the
      `NoLookWriteCode` conjunct of `CaptureCodeClassified`, without needing
      capture-freeness. Feeds `FFindMatchLookEq` for a capturing lookahead replay. */
  lemma NoLookWriteBody(body: R.regex)
    requires NR.LookBehindFragmentRE(body) && NR.LookFreeRE(body)
    ensures CM.NoLookWriteCode(CP.compile_to_bytecode(body))
  {
    var code := CP.compile_to_bytecode(body);
    var next := CP.compile(body, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(body);
    var endl: nat := next as nat;
    LookFreeLookUnique(body);
    OBu.LookFreeNoIds(body);            // LookIds(body) == {}
    forall pc: nat | pc < |code|
      ensures !code[pc].CheckOracle? && !code[pc].NegCheckOracle?
    {
      assert NR.GetPcRE(code, pc) == Some(code[pc]);
      if pc < endl {
        PIV.LookCheckIdsRE(body, code, 0, endl, pc);   // any gate's id would be in {}
      } else {
        assert code[pc] == RB.Accept;
      }
    }
  }

  // ===========================================================================
  // The whole loop — PROVED, in MainTheorem.dfy
  // ===========================================================================
  //
  // `MainTheorem.FLookLoopFilterFrame` closes this out: for an L1 main ast,
  //
  //   filter_reset(mainast, FLookLoop(...)) == filter_reset(mainast, cap, lk, qt)
  //
  // by induction on `maxlook - lid`, with `ReplayFrames` packaging one replay's
  // register facts (capture bank untouched, look bank identical, quant bank
  // agreeing outside the body's ids, result still quant-final) and
  // `FilterUnmoved` showing the filter cannot see the difference. It lives
  // there rather than here because it needs `QuantRegsFinal` and
  // `FNulledPlusIdentity`, which are MainTheorem's.
}
