// Lookaround campaign (L1), §6.6: the two tables the entry has to hand the
// construction, and the proof that they tell the truth.
//
//   LmOf(re) — the lookaround table: lid |-> (translated flavour, translated
//   body). Built by walking `re`, exactly as MainTheorem's `QmOfRE` builds the
//   quantifier table, and correct (`LmapOkOfLmOf`) once lids are unique.
//
//   OracleOkSuffix — the oracle column at every position tells the truth about
//   every row. Discharged by chaining `OS.OracleColumnSpec` (the campaign's
//   engine-to-spec oracle theorem) over the rows, which is why this file is
//   the meeting point of the table machinery and the oracle theorem.
//
// Everything here is stated over `T.InputAt` rather than a string+cp pair
// where the construction needs it, so the walk's inputs and the oracle's
// columns line up without dragging the string through the tree layers.
include "LookLeaves.dfy"
include "LookTables.dfy"
include "PikeInvRE.dfy"

/** §6.6: the lookaround table `LmOf`, its correctness (`LmapOkOfLmOf`), and
    the `OracleOkSuffix` discharge that feeds the entry construction. */
module LindenElkOracleEntry {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LS = Semantics
  import LT = Tree
  import FU = FunctionalUtils
  import SSx = StrictSuffix
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import LOr = Oracle
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import TR = LindenElkTreeRep
  import LTB = LindenElkLookTables
  import PIV = LindenElkPikeInv
  import SD = LindenSpanDuality
  import SAPI = LindenSemanticsReasoning
  import OS = LindenElkOracleSpec
  import LL = LindenElkLookLeaves

  // ===========================================================================
  // The lookaround table
  // ===========================================================================

  /** Builds the lookaround half of the static tables: each lookaround id maps
      to its translated flavour and body — the link `CheckOracle(lid)` erases.
      The `QmOfRE` of the lid namespace. */
  ghost function LmOf(re: R.regex): map<int, (L.Lookaround, L.Regex)>
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => map[]
    case Re_character(_) => map[]
    case Re_anchor(_) => map[]
    case Re_alt(r1, r2) => LmOf(r1) + LmOf(r2)
    case Re_con(r1, r2) => LmOf(r1) + LmOf(r2)
    case Re_quant(_, _, _, r1) => LmOf(r1)
    case Re_capture(_, r1) => LmOf(r1)
    case Re_lookaround(lid, la, r1) =>
      LmOf(r1)[lid := (T.TrLookaround(la), T.Translate(r1))]
  }

  /** `LmOf(re)`'s domain is exactly `re`'s lookaround ids. */
  lemma LmOfDom(re: R.regex)
    requires T.TransWf(re) && LTB.LookUnique(re)
    ensures forall k: int :: k in LmOf(re) <==> (k >= 0 && (k as nat) in LTB.LookIds(re))
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LmOfDom(r1); LmOfDom(r2);
    case Re_con(r1, r2) => LmOfDom(r1); LmOfDom(r2);
    case Re_quant(_, _, _, r1) => LmOfDom(r1);
    case Re_capture(_, r1) => LmOfDom(r1);
    case Re_lookaround(lid, la, r1) => LmOfDom(r1);
    case _ =>
  }

  /** A lookaround-free regex contributes no row. */
  lemma LookFreeLmOfEmpty(re: R.regex)
    requires T.TransWf(re) && NR.LookFreeRE(re)
    ensures LmOf(re) == map[]
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeLmOfEmpty(r1); LookFreeLmOfEmpty(r2);
    case Re_con(r1, r2) => LookFreeLmOfEmpty(r1); LookFreeLmOfEmpty(r2);
    case Re_quant(_, _, _, r1) => LookFreeLmOfEmpty(r1);
    case Re_capture(_, r1) => LookFreeLmOfEmpty(r1);
    case _ =>
  }

  /** Every row of `LmOf(re)` really is some lookaround node of `re`, with all
      the facts the oracle theorem asks of that node: its table row is correct,
      it is a lookBEHIND, and its body is in the L1 body fragment. Uniqueness of
      lids is what makes the row unambiguous. */
  lemma LmOfInv(re: R.regex, fc: CP.FCompiled, lid: int)
    returns (la: R.lookaround, body: R.regex)
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires LTB.LookUnique(re) && LTB.LookTablesOk(re, fc)
    requires PIV.QuantUnique(re)
    requires lid in LmOf(re)
    ensures T.TransWf(body)
    ensures LmOf(re)[lid] == (T.TrLookaround(la), T.Translate(body))
    ensures LTB.LookEntryOk(fc, lid, la, body)
    // the fragment admits BOTH flavours over the whole plus fragment (the
    // lookAHEAD star-shape restriction is retired -- see OracleColumnSpecLookahead)
    ensures NR.CaptureFreeRE(body) && NR.LookFreeRE(body) && NR.PlusFragmentRE(body)
    ensures lid >= 0 && (lid as nat) in LTB.LookIds(re)
    // the quant half: `body` sits under a lookaround, so every id it owns is
    // one of `re`'s in-look ids -- the disjointness the capture pass replays on
    ensures PIV.QuantUnique(body)
    ensures forall q: nat :: q in PIV.QuantIds(body) ==> q in PIV.QuantIdsInLooks(re)
    decreases re
  {
    LmOfDom(re);
    match re
    case Re_alt(r1, r2) =>
      LmOfDom(r1); LmOfDom(r2);
      if lid in LmOf(r2) {
        la, body := LmOfInv(r2, fc, lid);
      } else {
        assert lid in LmOf(r1);
        la, body := LmOfInv(r1, fc, lid);
        assert (lid as nat) !in LTB.LookIds(r2);
      }
    case Re_con(r1, r2) =>
      LmOfDom(r1); LmOfDom(r2);
      if lid in LmOf(r2) {
        la, body := LmOfInv(r2, fc, lid);
      } else {
        assert lid in LmOf(r1);
        la, body := LmOfInv(r1, fc, lid);
        assert (lid as nat) !in LTB.LookIds(r2);
      }
    case Re_quant(_, _, _, r1) => la, body := LmOfInv(r1, fc, lid);
    case Re_capture(_, r1) => la, body := LmOfInv(r1, fc, lid);
    case Re_lookaround(lid0, la0, r1) =>
      LmOfDom(r1);
      // the body of an L1 lookaround is look-FREE, so it owns no row: the id
      // can only be this node's own
      LookFreeLmOfEmpty(r1);
      assert lid == lid0;
      la, body := la0, r1;
      assert (lid0 as nat) !in LTB.LookIds(r1);         // LookUnique
      assert LmOf(re)[lid] == (T.TrLookaround(la0), T.Translate(r1));
  }

  /** THE table-correctness lemma: a table built by `LmOf` satisfies `LmapOk` —
      every lookaround node finds its own row. */
  lemma LmapOkOfLmOf(re: R.regex, qm: AR.QMap)
    requires T.TransWf(re) && LTB.LookUnique(re)
    requires qm.looks == LmOf(re)
    ensures AR.LmapOk(re, qm)
    decreases re
  {
    IsLookSubRefl(re);
    LmapOkSub(re, qm, re);
  }

  /** `LmapOk` transfers from a table that AGREES with `LmOf(sub)` on `sub`'s
      own ids — the sub-term step of `LmapOkOfLmOf`, where the ambient table is
      the parent's (bigger) one. */
  lemma LmapOkSub(sub: R.regex, qm: AR.QMap, parent: R.regex)
    requires T.TransWf(sub) && T.TransWf(parent) && LTB.LookUnique(parent)
    requires qm.looks == LmOf(parent)
    requires IsLookSub(sub, parent)
    ensures AR.LmapOk(sub, qm)
    decreases sub
  {
    IsLookSubChild(sub);
    match sub
    case Re_alt(r1, r2) =>
      IsLookSubTrans(r1, sub, parent); IsLookSubTrans(r2, sub, parent);
      LmapOkSub(r1, qm, parent); LmapOkSub(r2, qm, parent);
    case Re_con(r1, r2) =>
      IsLookSubTrans(r1, sub, parent); IsLookSubTrans(r2, sub, parent);
      LmapOkSub(r1, qm, parent); LmapOkSub(r2, qm, parent);
    case Re_quant(_, _, _, r1) =>
      IsLookSubTrans(r1, sub, parent); LmapOkSub(r1, qm, parent);
    case Re_capture(_, r1) =>
      IsLookSubTrans(r1, sub, parent); LmapOkSub(r1, qm, parent);
    case Re_lookaround(lid, la, r1) =>
      LookSubRow(sub, parent, lid, la, r1);
      IsLookSubTrans(r1, sub, parent);
      LmapOkSub(r1, qm, parent);
    case _ =>
  }

  /** `sub` occurs inside `parent` (structurally), which is what lets a row of
      `parent`'s table serve `sub`'s nodes. */
  ghost predicate IsLookSub(sub: R.regex, parent: R.regex)
    decreases parent
  {
    sub == parent
    || (match parent
        case Re_alt(r1, r2) => IsLookSub(sub, r1) || IsLookSub(sub, r2)
        case Re_con(r1, r2) => IsLookSub(sub, r1) || IsLookSub(sub, r2)
        case Re_quant(_, _, _, r1) => IsLookSub(sub, r1)
        case Re_capture(_, r1) => IsLookSub(sub, r1)
        case Re_lookaround(_, _, r1) => IsLookSub(sub, r1)
        case _ => false)
  }

  /** `IsLookSub` is reflexive and transitive, and every immediate child of a
      node is a sub-term of it — the plumbing the descent needs. */
  lemma IsLookSubRefl(r: R.regex)
    ensures IsLookSub(r, r)
  {}

  lemma IsLookSubTrans(a: R.regex, b: R.regex, c: R.regex)
    requires IsLookSub(a, b) && IsLookSub(b, c)
    ensures IsLookSub(a, c)
    decreases c
  {
    if b == c { return; }
    match c
    case Re_alt(r1, r2) => if IsLookSub(b, r1) { IsLookSubTrans(a, b, r1); } else { IsLookSubTrans(a, b, r2); }
    case Re_con(r1, r2) => if IsLookSub(b, r1) { IsLookSubTrans(a, b, r1); } else { IsLookSubTrans(a, b, r2); }
    case Re_quant(_, _, _, r1) => IsLookSubTrans(a, b, r1);
    case Re_capture(_, r1) => IsLookSubTrans(a, b, r1);
    case Re_lookaround(_, _, r1) => IsLookSubTrans(a, b, r1);
    case _ =>
  }

  /** Each immediate child is a sub-term. */
  lemma IsLookSubChild(r: R.regex)
    ensures r.Re_alt? ==> IsLookSub(r.e1, r) && IsLookSub(r.e2, r)
    ensures r.Re_con? ==> IsLookSub(r.c1, r) && IsLookSub(r.c2, r)
    ensures r.Re_quant? ==> IsLookSub(r.qr, r)
    ensures r.Re_capture? ==> IsLookSub(r.capr, r)
    ensures r.Re_lookaround? ==> IsLookSub(r.lr, r)
  {
    if r.Re_alt? { IsLookSubRefl(r.e1); IsLookSubRefl(r.e2); }
    if r.Re_con? { IsLookSubRefl(r.c1); IsLookSubRefl(r.c2); }
    if r.Re_quant? { IsLookSubRefl(r.qr); }
    if r.Re_capture? { IsLookSubRefl(r.capr); }
    if r.Re_lookaround? { IsLookSubRefl(r.lr); }
  }

  /** A lookaround node inside `parent` owns its row in `parent`'s table. */
  lemma LookSubRow(sub: R.regex, parent: R.regex, lid: int, la: R.lookaround, body: R.regex)
    requires T.TransWf(parent) && LTB.LookUnique(parent)
    requires sub == R.Re_lookaround(lid, la, body)
    requires IsLookSub(sub, parent)
    ensures T.TransWf(sub) && T.TransWf(body)
    ensures lid in LmOf(parent) && LmOf(parent)[lid] == (T.TrLookaround(la), T.Translate(body))
    decreases parent
  {
    if sub == parent {
      LmOfDom(body);
      assert (lid as nat) !in LTB.LookIds(body);
    } else {
      match parent
      case Re_alt(r1, r2) =>
        LmOfDom(r1); LmOfDom(r2);
        if IsLookSub(sub, r1) {
          LookSubRow(sub, r1, lid, la, body);
          assert (lid as nat) in LTB.LookIds(r1);
          assert (lid as nat) !in LTB.LookIds(r2);
        } else {
          LookSubRow(sub, r2, lid, la, body);
        }
      case Re_con(r1, r2) =>
        LmOfDom(r1); LmOfDom(r2);
        if IsLookSub(sub, r1) {
          LookSubRow(sub, r1, lid, la, body);
          assert (lid as nat) in LTB.LookIds(r1);
          assert (lid as nat) !in LTB.LookIds(r2);
        } else {
          LookSubRow(sub, r2, lid, la, body);
        }
      case Re_quant(_, _, _, r1) => LookSubRow(sub, r1, lid, la, body);
      case Re_capture(_, r1) => LookSubRow(sub, r1, lid, la, body);
      case Re_lookaround(lid0, la0, r1) =>
        LmOfDom(r1);
        LookSubRow(sub, r1, lid, la, body);
        assert (lid as nat) in LTB.LookIds(r1);
        assert lid != lid0;                            // LookUnique
      case _ =>
    }
  }

  // ===========================================================================
  // Walk inputs are string positions
  // ===========================================================================

  /** The initial input is position 0. */
  lemma InitInputAt(str: string)
    ensures LC.InitInput(str) == T.InputAt(str, 0)
  {
    assert str[0..] == str && str[..0] == [];
  }

  /** Every input the forward walk can still reach from position `k` IS a
      string position — the fact that lets the construction's `Input`-indexed
      oracle hypothesis be discharged column by column. */
  lemma SuffixIsInputAt(str: string, k: nat, inp: LC.Input)
    requires k <= |str|
    requires SSx.StrictSuffixForward(inp, T.InputAt(str, k).next, T.InputAt(str, k).pref)
    ensures exists m: nat :: k < m <= |str| && inp == T.InputAt(str, m)
    decreases |str| - k
  {
    var cur := T.InputAt(str, k);
    assert cur.next == str[k..];
    assert |cur.next| > 0;                         // else StrictSuffixForward is false
    var nxt := LC.Input(cur.next[1..], [cur.next[0]] + cur.pref);
    assert nxt == T.InputAt(str, k + 1) by {
      assert str[k..][1..] == str[k + 1..];
      assert str[..k + 1] == str[..k] + [str[k]];
      SAPI.ReverseSnoc(str[..k], str[k]);
    }
    if nxt == inp {
      assert k < k + 1 <= |str|;
    } else {
      SuffixIsInputAt(str, k + 1, inp);
    }
  }

  // ===========================================================================
  // The oracle hypothesis
  // ===========================================================================

  /** THE discharge: with the campaign's oracle theorem instantiated at every
      row and every column, the entry construction's oracle hypothesis holds
      from the initial input. */
  lemma OracleOkFromColumns(rer: LW.RegExpRecord, re: R.regex, str: string, qm: AR.QMap)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(re) && NR.LookBehindFragmentRE(re)
    requires LTB.LookUnique(re) && PIV.QuantUnique(re)
    requires forall x: nat :: x in LTB.LookIds(re) ==> 1 <= x
    requires qm.looks == LmOf(re)
    requires qm.ov == AI.FBuildOracle(CP.FFullCompilation(re), str)
    ensures LL.OracleOkSuffix(rer, qm, LC.InitInput(str))
  {
    LTB.FFullCompilationLookOk(re);
    var fc := CP.FFullCompilation(re);
    InitInputAt(str);
    forall inp: LC.Input | inp == LC.InitInput(str) || SSx.IsStrictSuffix(inp, LC.InitInput(str), WP.Forward)
      ensures LL.OracleOkAt(rer, qm, inp)
    {
      var cp: nat;
      if inp == LC.InitInput(str) {
        cp := 0;
      } else {
        assert SSx.StrictSuffixForward(inp, T.InputAt(str, 0).next, T.InputAt(str, 0).pref);
        SuffixIsInputAt(str, 0, inp);
        var m: nat :| 0 < m <= |str| && inp == T.InputAt(str, m);
        cp := m;
      }
      assert inp == T.InputAt(str, cp) && cp <= |str|;
      T.ReverseProps(str[..cp]);
      assert TR.CpOf(inp) == cp;
      forall lid: int, lk: L.Lookaround, r1: L.Regex
        | lid in qm.looks && qm.looks[lid] == (lk, r1)
        ensures LOr.view_get_oracle(qm.ov, TR.CpOf(inp), lid)
            <==> LT.TreeRes(FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk)),
                            LG.Empty, inp, L.LkDir(lk)).Some?
      {
        var la, body := LmOfInv(re, fc, lid);
        assert lk == T.TrLookaround(la) && r1 == T.Translate(body);
        assert 1 <= lid;                              // ids start at 1 after annotate
        LTB.LookIdsLeMax(re);
        // each flavour has its own column spec, and `LkDir` picks the matching
        // walk direction -- which is exactly why `OracleOkAt` is stated in
        // terms of LkDir rather than a fixed direction
        if la.Lookbehind? || la.NegLookbehind? {
          assert L.LkDir(lk) == WP.Backward;
          OS.OracleColumnSpec(rer, re, str, lid, la, body, cp, LG.Empty);
        } else {
          assert L.LkDir(lk) == WP.Forward;
          OS.OracleColumnSpecLookahead(rer, re, str, lid, la, body, cp, LG.Empty);
        }
      }
    }
  }
}
