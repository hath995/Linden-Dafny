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
  import OBV = LindenElkOracleBridgeV
  import MIR = LindenElkMirror
  import LN = WarblreNumeric
  import LAnc = Anchors
  import ODV = LindenElkOracleDecompV
  import OBu = LindenElkOracleBuild
  import OMV = LindenElkOracleMirrorV
  import ORc = LindenElkOracleReach

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

  // ===========================================================================
  // L5: the NESTED-aware span transfer, `MatchesV` <==> `MatchesL`
  // (direct-backward; no mirror, no simulation)
  // ===========================================================================

  /** Oracle correctness in the shape the look case reads: every position's
      per-lid bit matches the body's own directional walk (`OracleOkAt`). */
  ghost predicate OracleColsOk(rer: LW.RegExpRecord, qm: AR.QMap, str: string) {
    forall k: int :: 0 <= k <= |str| ==> LL.OracleOkAt(rer, qm, T.InputAt(str, k))
  }

  /** `CpOf(InputAt(str, i)) == i`. */
  lemma InputAtFacts(str: string, i: int)
    requires 0 <= i <= |str|
    ensures TR.CpOf(T.InputAt(str, i)) == i
  {
    MIR.ReverseLen(str[..i]);
  }

  /** Direct-backward span equivalence: a nested-lookbehind body's backward walk
      succeeds iff some `[m, i)` spans it -- the generalized (`GroupOkLB`) span
      duality, both halves (my L5 (A) work). */
  lemma BackWalkSpanLB(rer: LW.RegExpRecord, rL: L.Regex, str: string, i: int)
    requires SD.GroupOkLB(rL)
    requires 0 <= i <= |str|
    ensures SD.SuccActs(rer, [LS.Areg(rL)], T.InputAt(str, i), LG.Empty, WP.Backward)
        <==> (exists m: int {:trigger SD.MatchesL(rer, rL, str, m, i)} ::
                0 <= m <= i && SD.MatchesL(rer, rL, str, m, i))
  {
    if SD.SuccActs(rer, [LS.Areg(rL)], T.InputAt(str, i), LG.Empty, WP.Backward) {
      var m := SD.SpanDualitySoundLB(rer, rL, str, i, LG.Empty);
      assert 0 <= m <= i && SD.MatchesL(rer, rL, str, m, i);
      assert exists m2: int :: 0 <= m2 <= i && SD.MatchesL(rer, rL, str, m2, i);
    }
    if exists m: int :: 0 <= m <= i && SD.MatchesL(rer, rL, str, m, i) {
      var m: int :| 0 <= m <= i && SD.MatchesL(rer, rL, str, m, i);
      SD.SpanDualityCompleteLB(rer, rL, str, m, i, LG.Empty);
      assert SD.SuccActs(rer, [LS.Areg(rL)], T.InputAt(str, i), LG.Empty, WP.Backward);
    }
  }

  /** `MatchesIterV` cons: prepend one span onto a `k`-chain. */
  lemma IterVConsRE(r: R.regex, k: nat, str: string, ov: LOr.OracleView, i: int, m: int, j: int)
    requires OBV.MatchesV(r, str, ov, i, m) && OBV.MatchesIterV(r, k, str, ov, m, j)
    ensures OBV.MatchesIterV(r, k + 1, str, ov, i, j)
  {}

  /** The nested-lookbehind gate, isolated (small VC): the zero-width Linden
      look predicate `MatchesL(LookaroundR(lk, r1L))` at `i` holds exactly when
      the oracle bit agrees with `lk`'s positivity. Chains `OracleOkAt` (bit <==>
      backward walk) with `BackWalkSpanLB` (walk <==> body span) and folds
      `MatchesL`'s own look clause -- so the existential matching stays LOCAL to
      this lemma, and callers see only a clean boolean. */
  lemma LookGateSpec(rer: LW.RegExpRecord, qm: AR.QMap, lk: L.Lookaround, r1L: L.Regex,
                     str: string, i: int, lid: int)
    requires lk.LookBehind? || lk.NegLookBehind?
    requires SD.GroupOkLB(r1L)
    requires 0 <= i <= |str|
    requires lid in qm.looks && qm.looks[lid] == (lk, r1L)
    requires LL.OracleOkAt(rer, qm, T.InputAt(str, i))
    ensures SD.MatchesL(rer, L.LookaroundR(lk, r1L), str, i, i)
        <==> (if lk.LookBehind? then LOr.view_get_oracle(qm.ov, i, lid)
              else !LOr.view_get_oracle(qm.ov, i, lid))
  {
    InputAtFacts(str, i);                            // TR.CpOf(InputAt(str,i)) == i
    assert L.LkDir(lk) == WP.Backward;
    LL.OracleOkAtGet(rer, qm, T.InputAt(str, i), lid, lk, r1L);
    var succ := SD.SuccActs(rer, [LS.Areg(r1L)], T.InputAt(str, i), LG.Empty, WP.Backward);
    assert LOr.view_get_oracle(qm.ov, i, lid) <==> succ;                   // OracleOkAtGet
    var lookL := L.LookaroundR(lk, r1L);
    // Prove `MatchesL(lookL) <==> succ` (for a positive lookbehind) or its
    // negation, by WITNESS -- never by existential equivalence. `succ <==> ∃m`.
    if succ {
      var m := SD.SpanDualitySoundLB(rer, r1L, str, i, LG.Empty);         // MatchesL(r1L, m, i), 0<=m<=i
      if lk.LookBehind? {
        assert SD.MatchesL(rer, lookL, str, i, i);                        // Positivity <==> ∃m (m witnesses)
      } else {
        assert !SD.MatchesL(rer, lookL, str, i, i);                       // Positivity false but ∃m
      }
    } else {
      // succ false: no span ends at i (else BwdComplete would make succ hold).
      forall m: int | 0 <= m <= i ensures !SD.MatchesL(rer, r1L, str, m, i) {
        if SD.MatchesL(rer, r1L, str, m, i) {
          SD.SpanDualityCompleteLB(rer, r1L, str, m, i, LG.Empty);        // would give succ
          assert false;
        }
      }
      if lk.LookBehind? {
        assert !SD.MatchesL(rer, lookL, str, i, i);                       // Positivity true but no ∃m
      } else {
        assert SD.MatchesL(rer, lookL, str, i, i);                        // Positivity false and no ∃m
      }
    }
  }

  /** L5 span transfer: for a NESTED-lookbehind body (`GroupOkLB` after
      `Translate`), the oracle-gated span `MatchesV` agrees with the Linden span
      `MatchesL`. The look case is the direct-backward gate: `MatchesV` reads the
      oracle bit, `OracleOkAt` equates it to the body's BACKWARD walk succeeding,
      and `SpanDuality{Complete,Sound}LB` equates THAT to a body span -- exactly
      `MatchesL`'s lookbehind clause. No mirror, no simulation. */
  lemma MatchesVTransfer(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(re)
    requires NR.NestedFragmentRE(re)
    requires SD.GroupOkLB(T.Translate(re))
    requires AR.LmapOk(re, qm)
    requires OracleColsOk(rer, qm, str)
    requires 0 <= i && j <= |str|
    ensures OBV.MatchesV(re, str, qm.ov, i, j) <==> SD.MatchesL(rer, T.Translate(re), str, i, j)
    decreases CP.rsize(re), 0, 0
  {
    match re
    case Re_empty =>
    case Re_character(c) =>
      if j == i + 1 {
        assert 0 <= i < |str|;
        assert AI.get_char(str, i) == Some(str[i]);
        T.CharSemAgree(rer, c, str[i]);
      }
    case Re_anchor(a) =>
      if i == j {
        OS.CtxAtIsCpContext(str, i);
        T.AnchorSemAgree(rer, a, str, i, LAnc.Forward);
      }
    case Re_alt(r1, r2) =>
      MatchesVTransfer(rer, qm, r1, str, i, j);
      MatchesVTransfer(rer, qm, r2, str, i, j);
    case Re_con(r1, r2) =>
      if OBV.MatchesV(re, str, qm.ov, i, j) {
        assert OBV.MatchesV(R.Re_con(r1, r2), str, qm.ov, i, j);
        var m: int :| OBV.MatchesV(r1, str, qm.ov, i, m) && OBV.MatchesV(r2, str, qm.ov, m, j);
        OBV.MatchesVBounds(r1, str, qm.ov, i, m);
        OBV.MatchesVBounds(r2, str, qm.ov, m, j);
        MatchesVTransfer(rer, qm, r1, str, i, m);
        MatchesVTransfer(rer, qm, r2, str, m, j);
        assert SD.MatchesL(rer, T.Translate(r2), str, m, j);
      }
      if SD.MatchesL(rer, T.Translate(re), str, i, j) {
        assert SD.MatchesL(rer, L.Sequence(T.Translate(r1), T.Translate(r2)), str, i, j);
        var m: int :| SD.MatchesL(rer, T.Translate(r1), str, i, m)
                   && SD.MatchesL(rer, T.Translate(r2), str, m, j);
        SD.MatchesLBounds(rer, T.Translate(r1), str, i, m);
        SD.MatchesLBounds(rer, T.Translate(r2), str, m, j);
        MatchesVTransfer(rer, qm, r1, str, i, m);
        MatchesVTransfer(rer, qm, r2, str, m, j);
      }
    case Re_quant(nul, qid, q, r1) =>
      if OBV.MatchesV(re, str, qm.ov, i, j) {
        assert OBV.MatchesV(R.Re_quant(nul, qid, q, r1), str, qm.ov, i, j);
        var k: nat :| q.min <= k && (q.max.Some? ==> k <= q.max.value)
                   && OBV.MatchesIterV(r1, k, str, qm.ov, i, j);
        OS.QuantBoundsAgree(q, k);
        OBV.MatchesIterVBounds(r1, k, str, qm.ov, i, j);
        IterVTransfer(rer, qm, r1, k, str, i, j);
        assert SD.MatchesL(rer, L.Quantified(q.greedy, q.min as nat, T.TrDelta(q),
                                             T.Translate(r1)), str, i, j);
      }
      if SD.MatchesL(rer, T.Translate(re), str, i, j) {
        assert SD.MatchesL(rer, L.Quantified(q.greedy, q.min as nat, T.TrDelta(q),
                                             T.Translate(r1)), str, i, j);
        var k: nat :| (q.min as nat) <= k
                   && (match T.TrDelta(q) case Inf => true case NN(dx) => k <= (q.min as nat) + dx)
                   && SD.IterL(rer, T.Translate(r1), k, str, i, j);
        OS.QuantBoundsAgree(q, k);
        SD.IterLBounds(rer, T.Translate(r1), k, str, i, j);
        IterVTransfer(rer, qm, r1, k, str, i, j);
      }
    case Re_capture(cid, r1) =>
      MatchesVTransfer(rer, qm, r1, str, i, j);
    case Re_lookaround(lid, la, r1) =>
      var lk := T.TrLookaround(la);
      assert T.Translate(re) == L.LookaroundR(lk, T.Translate(r1));
      assert lk.LookBehind? || lk.NegLookBehind?;    // from GroupOkLB(Translate(look))
      assert SD.GroupOkLB(T.Translate(r1));
      assert lid in qm.looks && qm.looks[lid] == (lk, T.Translate(r1));   // AR.LmapOk
      MatchesVLookCase(rer, qm, lid, la, r1, str, i, j);
  }

  /** The look case of `MatchesVTransfer`, isolated (its own VC): a nested
      lookBEHIND's oracle-gated span `MatchesV` agrees with its Linden zero-width
      `MatchesL` clause. Kept separate so the quantifier chaining (`oracle <==>
      span`) does not compete with the rest of the transfer for solver budget. */
  lemma MatchesVLookCase(rer: LW.RegExpRecord, qm: AR.QMap, lid: int, la: R.lookaround,
                         r1: R.regex, str: string, i: int, j: int)
    requires T.TransWf(R.Re_lookaround(lid, la, r1))
    requires (T.TrLookaround(la)).LookBehind? || (T.TrLookaround(la)).NegLookBehind?
    requires SD.GroupOkLB(T.Translate(r1))
    requires lid in qm.looks && qm.looks[lid] == (T.TrLookaround(la), T.Translate(r1))
    requires OracleColsOk(rer, qm, str)
    requires 0 <= i && j <= |str|
    ensures OBV.MatchesV(R.Re_lookaround(lid, la, r1), str, qm.ov, i, j)
        <==> SD.MatchesL(rer, L.LookaroundR(T.TrLookaround(la), T.Translate(r1)), str, i, j)
  {
    var lk := T.TrLookaround(la);
    var look := R.Re_lookaround(lid, la, r1);
    var lookL := L.LookaroundR(lk, T.Translate(r1));
    if i == j && 0 <= i <= |str| {
      assert LL.OracleOkAt(rer, qm, T.InputAt(str, i));                   // OracleColsOk at k == i
      LookGateSpec(rer, qm, lk, T.Translate(r1), str, i, lid);
      // LookGateSpec: MatchesL(lookL) <==> (lk.LookBehind? ? oracle : !oracle).
      // MatchesV(look) (i==j) = (la.Lookahead?||la.Lookbehind? ? oracle : !oracle),
      // and la.Lookbehind? <==> lk.LookBehind?, la not Lookahead -- the same bool.
      var ora := LOr.view_get_oracle(qm.ov, i, lid);
      if la.Lookbehind? {
        assert lk.LookBehind?;
        assert OBV.MatchesV(look, str, qm.ov, i, j) <==> ora;
      } else {
        assert la.NegLookbehind? && lk.NegLookBehind?;
        assert OBV.MatchesV(look, str, qm.ov, i, j) <==> !ora;
      }
    } else {
      // off the diagonal both sides are false (both require i == j).
      assert !OBV.MatchesV(R.Re_lookaround(lid, la, r1), str, qm.ov, i, j);
      assert !SD.MatchesL(rer, L.LookaroundR(lk, T.Translate(r1)), str, i, j);
    }
  }

  /** `MatchesIterV` <==> `IterL`, the iteration companion of `MatchesVTransfer`. */
  lemma IterVTransfer(rer: LW.RegExpRecord, qm: AR.QMap, r: R.regex, k: nat, str: string, i: int, j: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(r)
    requires NR.NestedFragmentRE(r)
    requires SD.GroupOkLB(T.Translate(r))
    requires AR.LmapOk(r, qm)
    requires OracleColsOk(rer, qm, str)
    requires 0 <= i && j <= |str|
    ensures OBV.MatchesIterV(r, k, str, qm.ov, i, j) <==> SD.IterL(rer, T.Translate(r), k, str, i, j)
    decreases CP.rsize(r), 1, k
  {
    if k > 0 {
      if OBV.MatchesIterV(r, k, str, qm.ov, i, j) {
        var m := OBV.MatchesIterVHead(r, k, str, qm.ov, i, j);
        OBV.MatchesVBounds(r, str, qm.ov, i, m);
        OBV.MatchesIterVBounds(r, k - 1, str, qm.ov, m, j);
        MatchesVTransfer(rer, qm, r, str, i, m);
        IterVTransfer(rer, qm, r, k - 1, str, m, j);
        SD.IterLCons(rer, T.Translate(r), k - 1, str, i, m, j);
      }
      if SD.IterL(rer, T.Translate(r), k, str, i, j) {
        var m := SD.IterLHead(rer, T.Translate(r), k, str, i, j);
        SD.MatchesLBounds(rer, T.Translate(r), str, i, m);
        SD.IterLBounds(rer, T.Translate(r), k - 1, str, m, j);
        MatchesVTransfer(rer, qm, r, str, i, m);
        IterVTransfer(rer, qm, r, k - 1, str, m, j);
        IterVConsRE(r, k - 1, str, qm.ov, i, m, j);
      }
    }
  }

  /** The value bridge: a nested-lookbehind body's oracle-recorder hit
      (`RecorderHitV` = some `MatchesV` span ends at `cp`) is EXACTLY the success
      of the body's BACKWARD walk from `cp`. Chains `MatchesVTransfer` (MatchesV
      <==> MatchesL) with `SpanDuality{Complete,Sound}LB` (span <==> walk),
      witness-based through `RecorderHitV`'s intro/inv. This is what a nested
      `OracleColumnSpec` composes with the oracle-build side
      (`oracle bit <==> RecorderHitV`, the V-model). */
  lemma RecorderHitVBackWalk(rer: LW.RegExpRecord, qm: AR.QMap, body: R.regex, str: string, cp: int)
    requires !rer.ignoreCase && !rer.multiline
    requires T.TransWf(body)
    requires NR.NestedFragmentRE(body)
    requires SD.GroupOkLB(T.Translate(body))
    requires AR.LmapOk(body, qm)
    requires OracleColsOk(rer, qm, str)
    requires 0 <= cp <= |str|
    ensures ODV.RecorderHitV(body, str, qm.ov, cp)
        <==> SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), LG.Empty, WP.Backward)
  {
    if ODV.RecorderHitV(body, str, qm.ov, cp) {
      var i := ODV.RecorderHitVInv(body, str, qm.ov, cp);   // MatchesV(body, i, cp), 0<=i<=cp
      MatchesVTransfer(rer, qm, body, str, i, cp);          // MatchesL(Translate(body), i, cp)
      SD.SpanDualityCompleteLB(rer, T.Translate(body), str, i, cp, LG.Empty);   // SuccActs
    }
    if SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), LG.Empty, WP.Backward) {
      var i := SD.SpanDualitySoundLB(rer, T.Translate(body), str, cp, LG.Empty);   // MatchesL(Translate(body), i, cp)
      MatchesVTransfer(rer, qm, body, str, i, cp);          // MatchesV(body, i, cp)
      ODV.RecorderHitVIntro(body, str, qm.ov, cp, i);       // RecorderHitV
    }
  }

  /** THE nested capstone: for a nested-lookbehind body, the oracle bit at `cp`
      for `lid` holds EXACTLY when the body's BACKWARD walk from `cp` succeeds --
      the direct-backward analogue of `OS.OracleColumnSpec`, with NO mirror and
      NO backward simulation. Composes the oracle-build side
      (`FBuildOracleCorrectAtNested`: bit <==> `ReachesWriteV`), the V-span
      bridges (`ReachesWriteVToMatchesV`/`MatchesVToReachesWriteV` +
      capture-blindness `MatchesVRemoveCapture`), and the value bridge
      `RecorderHitVBackWalk`. This is what §6.5's `OracleOk` for a nested column
      consumes. */
  lemma OracleColumnSpecNested(rer: LW.RegExpRecord, qm: AR.QMap, re: R.regex, str: string,
                               lid: int, la: R.lookaround, body: R.regex, cp: int)
    requires !rer.ignoreCase && !rer.multiline
    requires NR.NestedFragmentRE(re)
    requires LTB.LidsWellNested(re)
    requires LTB.LookUnique(re)
    requires LTB.LookEntryOk(CP.FFullCompilation(re), lid, la, body)
    requires la.Lookbehind? || la.NegLookbehind?
    requires NR.NestedFragmentRE(body)
    requires T.TransWf(body)
    requires SD.GroupOkLB(T.Translate(body))
    requires AR.LmapOk(body, qm)
    requires qm.ov == AI.FBuildOracle(CP.FFullCompilation(re), str)
    requires OracleColsOk(rer, qm, str)
    requires 1 <= lid
    requires 0 <= cp <= |str|
    ensures LOr.view_get_oracle(qm.ov, cp, lid)
        <==> SD.SuccActs(rer, [LS.Areg(T.Translate(body))], T.InputAt(str, cp), LG.Empty, WP.Backward)
  {
    var ovf := qm.ov;
    var rcb := R.remove_capture(body);
    OMV.RemoveCaptureNestedFragment(body);                  // NestedFragmentRE(rcb)
    OBu.FBuildOracleCorrectAtNested(re, str, lid, la, body, cp);
    // oracle bit <==> ReachesWriteV(compile_to_write(lazy_prefix(rcb), lid), str, ovf, 0, lid, cp)
    // First: oracle bit <==> RecorderHitV(body), by the ReachesWriteV <-> MatchesV chain.
    if LOr.view_get_oracle(ovf, cp, lid) {
      var i := ODV.ReachesWriteVToMatchesV(rcb, lid, str, ovf, cp);   // MatchesV(rcb, i, cp)
      OMV.MatchesVRemoveCapture(body, str, ovf, i, cp);              // MatchesV(body, i, cp)
      ODV.RecorderHitVIntro(body, str, ovf, cp, i);                  // RecorderHitV(body)
    }
    if ODV.RecorderHitV(body, str, ovf, cp) {
      var i := ODV.RecorderHitVInv(body, str, ovf, cp);             // MatchesV(body, i, cp)
      OMV.MatchesVRemoveCapture(body, str, ovf, i, cp);            // MatchesV(rcb, i, cp)
      OBV.MatchesVToReachesWriteV(rcb, lid, str, ovf, i, cp);       // ReachesWriteV(rcb) => oracle bit
    }
    // Then: RecorderHitV(body) <==> backward walk.
    RecorderHitVBackWalk(rer, qm, body, str, cp);
  }
}
