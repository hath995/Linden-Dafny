// §2.5b STAGE 2, RUNG F (F-a) — the LIVE-STAMP register invariant.
//
// Rung E's readout theorem (`NRO.ReconReadout`: `GmOfLive` after
// `FNulledPlus` is `GmOfLiveR` before) needs, of the thread it runs on, that
// every SET stamp `q` has
//   * a STALE body: every capture/quant clock inside `QidBody(re, q)` is below
//     `q`'s own clock (the reconstruction's writes must win `filter_capture`'s
//     clock comparison), and
//   * when its quantifier chain is fresh, PRESENT capture ancestors
//     (`PathPresentQ` — the capture-blind readout agrees with `filter_capture`).
// `StampLiveOk` is that per-thread register fact. It is NOT positional: the
// positional input is consumed at the write sites, where the caller supplies
//   * a capture write's group is outside every stamped body
//     (`NST.NestStampTopCapSite`),
//   * a quant write's quantifier is enclosed by no stamped quantifier
//     (`NST.NestStampTopQuantSite` → `PIV.NoStampedAbove`),
//   * a true stamp's quantifier is outside looks with present ancestors
//     (`NST.TrueStampSite`),
// and the VM's clock discipline (every write uses a clock above every stored
// one: `FAdvanceEpsilon` bumps `clock` before the write). Look writes and
// every non-writing instruction leave the three banks it reads untouched.
//
// Why the stale body survives: a stamp is set at the CIN exit `e1 + 2`, after
// the body ran (or was skipped) with clocks below the stamp's; afterwards no
// write lands inside the body while the stamp is set (the sites above), and a
// clock mark of an ENCLOSING quantifier makes the stamp's chain stale for good
// (its clock is above the stamp's — `QChainFreshAncGe`).
module LindenElkStampLive {
  import opened Std.Wrappers
  import R = RegElkRegex
  import CP = Compiler
  import AI = ArrayInterp
  import PIV = LindenElkPikeInv

  // =========================================================================
  // 1. The invariant.
  // =========================================================================

  /** Every capture/quant clock of `r` is below `K` (the raw-bank twin of
      `NRR.RegsStale`). */
  ghost predicate BodyStale(r: R.regex, cc: seq<int>, qc: seq<int>, K: int) {
    (forall c: nat :: c in PIV.CapIds(r) ==>
       AI.get_idx(cc, CP.start_reg(c)) < K && AI.get_idx(cc, CP.end_reg(c)) < K)
    && (forall q: nat :: q in PIV.QuantIds(r) ==> AI.get_idx(qc, q) < K)
  }

  /** THE live-stamp invariant over a thread's capture clocks `cc`, quant clocks
      `qc` and quant stamps `qcp`. Opaque (AGENTS.md §2.4): it rides the
      per-thread positional bundle as an atom. */
  opaque ghost predicate StampLiveOk(re: R.regex, cc: seq<int>, qc: seq<int>, qcp: seq<int>) {
    forall q: nat :: q in PIV.QuantIds(re) && AI.get_idx(qcp, q) >= 0 ==>
      q in PIV.QuantIdsOutsideLooks(re)
      && BodyStale(PIV.QidBody(re, q), cc, qc, AI.get_idx(qc, q))
      && (PIV.QChainFresh(re, qc, -1, q) ==> PIV.PathPresentQ(re, cc, qc, -1, q))
  }

  /** Read one stamp's facts off the invariant. */
  lemma StampLiveAt(re: R.regex, cc: seq<int>, qc: seq<int>, qcp: seq<int>, q: nat)
    requires StampLiveOk(re, cc, qc, qcp)
    requires q in PIV.QuantIds(re) && AI.get_idx(qcp, q) >= 0
    ensures q in PIV.QuantIdsOutsideLooks(re)
    ensures BodyStale(PIV.QidBody(re, q), cc, qc, AI.get_idx(qc, q))
    ensures PIV.QChainFresh(re, qc, -1, q) ==> PIV.PathPresentQ(re, cc, qc, -1, q)
  {
    reveal StampLiveOk;
  }

  /** No stamp set: vacuous (the entry thread, every look-body thread). */
  lemma StampLiveInit(re: R.regex, cc: seq<int>, qc: seq<int>, qcp: seq<int>)
    requires forall q: int :: AI.get_idx(qcp, q) < 0
    ensures StampLiveOk(re, cc, qc, qcp)
  {
    reveal StampLiveOk;
  }

  // =========================================================================
  // 2. Structural helpers on quantifier ids.
  // =========================================================================

  /** Disjoint sets: membership in one excludes the other. */
  lemma DisjNot(A: set<nat>, B: set<nat>, x: nat)
    requires A * B == {}
    ensures (x in A ==> x !in B) && (x in B ==> x !in A)
  {
    if x in A && x in B { assert x in A * B; }
  }

  lemma QuantIdsQidBodySub(r: R.regex, q: nat)
    requires q in PIV.QuantIds(r)
    ensures PIV.QuantIds(PIV.QidBody(r, q)) <= PIV.QuantIds(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => if q in PIV.QuantIds(r1) { QuantIdsQidBodySub(r1, q); } else { QuantIdsQidBodySub(r2, q); }
    case Re_con(r1, r2) => if q in PIV.QuantIds(r1) { QuantIdsQidBodySub(r1, q); } else { QuantIdsQidBodySub(r2, q); }
    case Re_quant(_, qid0, _, r1) => if qid0 >= 0 && (qid0 as nat) == q {} else { QuantIdsQidBodySub(r1, q); }
    case Re_capture(_, r1) => QuantIdsQidBodySub(r1, q);
    case Re_lookaround(_, _, r1) => QuantIdsQidBodySub(r1, q);
  }

  /** A quantifier is not inside its own body. */
  lemma QidBodyNotSelf(r: R.regex, q: nat)
    requires PIV.QuantUnique(r) && q in PIV.QuantIds(r)
    ensures q !in PIV.QuantIds(PIV.QidBody(r, q))
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if q in PIV.QuantIds(r1) { QidBodyNotSelf(r1, q); } else { QidBodyNotSelf(r2, q); }
    case Re_con(r1, r2) =>
      if q in PIV.QuantIds(r1) { QidBodyNotSelf(r1, q); } else { QidBodyNotSelf(r2, q); }
    case Re_quant(_, qid0, _, r1) => if qid0 >= 0 && (qid0 as nat) == q {} else { QidBodyNotSelf(r1, q); }
    case Re_capture(_, r1) => QidBodyNotSelf(r1, q);
    case Re_lookaround(_, _, r1) => QidBodyNotSelf(r1, q);
  }

  /** Outside looks, a fresh chain puts `q`'s clock at or above the threshold. */
  lemma QChainFreshGe(r: R.regex, qc: seq<int>, mx: int, q: nat)
    requires PIV.QuantUnique(r)
    requires q in PIV.QuantIds(r) && q in PIV.QuantIdsOutsideLooks(r)
    requires PIV.QChainFresh(r, qc, mx, q)
    ensures AI.get_idx(qc, q) >= mx
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q);
      if q in PIV.QuantIds(r1) {
        assert q !in PIV.QuantIds(r2);
        assert PIV.QChainFresh(r1, qc, mx, q);
        QChainFreshGe(r1, qc, mx, q);
      } else {
        assert PIV.QChainFresh(r2, qc, mx, q);
        QChainFreshGe(r2, qc, mx, q);
      }
    case Re_con(r1, r2) =>
      PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q);
      if q in PIV.QuantIds(r1) {
        assert q !in PIV.QuantIds(r2);
        assert PIV.QChainFresh(r1, qc, mx, q);
        QChainFreshGe(r1, qc, mx, q);
      } else {
        assert PIV.QChainFresh(r2, qc, mx, q);
        QChainFreshGe(r2, qc, mx, q);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == q {
      } else {
        QChainFreshGe(r1, qc, AI.get_idx(qc, qid0), q);
      }
    case Re_capture(_, r1) => QChainFreshGe(r1, qc, mx, q);
    case Re_lookaround(_, _, _) =>
  }

  /** Outside looks, a fresh chain through an enclosing quantifier `q0` puts
      `q`'s clock at or above `q0`'s. */
  lemma QChainFreshAncGe(r: R.regex, qc: seq<int>, mx: int, q0: nat, q: nat)
    requires PIV.QuantUnique(r)
    requires q0 in PIV.QuantIds(r) && q in PIV.QuantIds(PIV.QidBody(r, q0))
    requires q in PIV.QuantIds(r) && q in PIV.QuantIdsOutsideLooks(r)
    requires PIV.QChainFresh(r, qc, mx, q)
    ensures AI.get_idx(qc, q) >= AI.get_idx(qc, q0)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q); DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q0);
      if q0 in PIV.QuantIds(r1) {
        QuantIdsQidBodySub(r1, q0);
        assert PIV.QidBody(r, q0) == PIV.QidBody(r1, q0);
        assert q in PIV.QuantIds(r1) && q !in PIV.QuantIds(r2);
        assert PIV.QChainFresh(r1, qc, mx, q);
        QChainFreshAncGe(r1, qc, mx, q0, q);
      } else {
        QuantIdsQidBodySub(r2, q0);
        assert PIV.QidBody(r, q0) == PIV.QidBody(r2, q0);
        assert q in PIV.QuantIds(r2) && q !in PIV.QuantIds(r1);
        assert PIV.QChainFresh(r2, qc, mx, q);
        QChainFreshAncGe(r2, qc, mx, q0, q);
      }
    case Re_con(r1, r2) =>
      PIV.QuantIdsOutsideLooksSub(r1); PIV.QuantIdsOutsideLooksSub(r2);
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q); DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q0);
      if q0 in PIV.QuantIds(r1) {
        QuantIdsQidBodySub(r1, q0);
        assert PIV.QidBody(r, q0) == PIV.QidBody(r1, q0);
        assert q in PIV.QuantIds(r1) && q !in PIV.QuantIds(r2);
        assert PIV.QChainFresh(r1, qc, mx, q);
        QChainFreshAncGe(r1, qc, mx, q0, q);
      } else {
        QuantIdsQidBodySub(r2, q0);
        assert PIV.QidBody(r, q0) == PIV.QidBody(r2, q0);
        assert q in PIV.QuantIds(r2) && q !in PIV.QuantIds(r1);
        assert PIV.QChainFresh(r2, qc, mx, q);
        QChainFreshAncGe(r2, qc, mx, q0, q);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == q0 {
        assert q in PIV.QuantIds(r1) && q != q0;
        QChainFreshGe(r1, qc, AI.get_idx(qc, qid0), q);
      } else {
        QuantIdsQidBodySub(r1, q0);
        assert q in PIV.QuantIds(r1);
        QChainFreshAncGe(r1, qc, AI.get_idx(qc, qid0), q0, q);
      }
    case Re_capture(_, r1) => QChainFreshAncGe(r1, qc, mx, q0, q);
    case Re_lookaround(_, _, _) =>
  }

  /** A quant-clock write at `q0` is invisible to `q`'s chain freshness unless
      `q0` encloses `q` (or is `q`). */
  lemma QChainFreshOff(r: R.regex, qc: seq<int>, qc': seq<int>, mx: int, q0: nat, q: nat)
    requires PIV.QuantUnique(r)
    requires q in PIV.QuantIds(r) && q != q0
    requires forall x: int :: x != q0 as int ==> AI.get_idx(qc', x) == AI.get_idx(qc, x)
    requires q0 in PIV.QuantIds(r) ==> q !in PIV.QuantIds(PIV.QidBody(r, q0))
    ensures PIV.QChainFresh(r, qc', mx, q) == PIV.QChainFresh(r, qc, mx, q)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q); DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q0);
      if q in PIV.QuantIds(r1) {
        assert q0 in PIV.QuantIds(r1) ==> PIV.QidBody(r, q0) == PIV.QidBody(r1, q0);
        QChainFreshOff(r1, qc, qc', mx, q0, q);
      } else {
        assert q0 in PIV.QuantIds(r2) ==> q0 !in PIV.QuantIds(r1) && PIV.QidBody(r, q0) == PIV.QidBody(r2, q0);
        QChainFreshOff(r2, qc, qc', mx, q0, q);
      }
    case Re_con(r1, r2) =>
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q); DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q0);
      if q in PIV.QuantIds(r1) {
        assert q0 in PIV.QuantIds(r1) ==> PIV.QidBody(r, q0) == PIV.QidBody(r1, q0);
        QChainFreshOff(r1, qc, qc', mx, q0, q);
      } else {
        assert q0 in PIV.QuantIds(r2) ==> q0 !in PIV.QuantIds(r1) && PIV.QidBody(r, q0) == PIV.QidBody(r2, q0);
        QChainFreshOff(r2, qc, qc', mx, q0, q);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == q {
      } else {
        assert q in PIV.QuantIds(r1);
        assert qid0 != q0 as int;
        QChainFreshOff(r1, qc, qc', AI.get_idx(qc, qid0), q0, q);
      }
    case Re_capture(_, r1) => QChainFreshOff(r1, qc, qc', mx, q0, q);
    case Re_lookaround(_, _, r1) => QChainFreshOff(r1, qc, qc', -1, q0, q);
  }

  /** The `PathPresentQ` twin of `QChainFreshOff` (here `q == q0` is allowed:
      the descent stops AT `q`'s node without reading its clock). */
  lemma PathPresentQOff(r: R.regex, cc: seq<int>, qc: seq<int>, qc': seq<int>, mx: int, q0: nat, q: nat)
    requires PIV.QuantUnique(r)
    requires q in PIV.QuantIds(r)
    requires forall x: int :: x != q0 as int ==> AI.get_idx(qc', x) == AI.get_idx(qc, x)
    requires q0 in PIV.QuantIds(r) ==> q !in PIV.QuantIds(PIV.QidBody(r, q0))
    ensures PIV.PathPresentQ(r, cc, qc', mx, q) == PIV.PathPresentQ(r, cc, qc, mx, q)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q); DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q0);
      if q in PIV.QuantIds(r1) {
        assert q0 in PIV.QuantIds(r1) ==> PIV.QidBody(r, q0) == PIV.QidBody(r1, q0);
        PathPresentQOff(r1, cc, qc, qc', mx, q0, q);
      } else {
        assert q0 in PIV.QuantIds(r2) ==> q0 !in PIV.QuantIds(r1) && PIV.QidBody(r, q0) == PIV.QidBody(r2, q0);
        PathPresentQOff(r2, cc, qc, qc', mx, q0, q);
      }
    case Re_con(r1, r2) =>
      assert PIV.QuantUnique(r1) && PIV.QuantUnique(r2) && PIV.QuantIds(r1) * PIV.QuantIds(r2) == {};
      DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q); DisjNot(PIV.QuantIds(r1), PIV.QuantIds(r2), q0);
      if q in PIV.QuantIds(r1) {
        assert q0 in PIV.QuantIds(r1) ==> PIV.QidBody(r, q0) == PIV.QidBody(r1, q0);
        PathPresentQOff(r1, cc, qc, qc', mx, q0, q);
      } else {
        assert q0 in PIV.QuantIds(r2) ==> q0 !in PIV.QuantIds(r1) && PIV.QidBody(r, q0) == PIV.QidBody(r2, q0);
        PathPresentQOff(r2, cc, qc, qc', mx, q0, q);
      }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == q {
      } else {
        assert q in PIV.QuantIds(r1);
        assert qid0 != q0 as int;
        PathPresentQOff(r1, cc, qc, qc', AI.get_idx(qc, qid0), q0, q);
      }
    case Re_capture(_, r1) => PathPresentQOff(r1, cc, qc, qc', mx, q0, q);
    case Re_lookaround(_, _, r1) => PathPresentQOff(r1, cc, qc, qc', mx, q0, q);
  }

  /** Raising one capture clock to a value above every quant clock keeps every
      enclosing capture present. */
  lemma PathPresentQRaise(r: R.regex, cc: seq<int>, cc': seq<int>, qc: seq<int>, mx: int, q: nat, k: int, v: int)
    requires q in PIV.QuantIds(r)
    requires forall j: int :: j != k ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires AI.get_idx(cc', k) == v && v >= 0 && v >= mx
    requires forall x: int :: AI.get_idx(qc, x) <= v
    requires PIV.PathPresentQ(r, cc, qc, mx, q)
    ensures PIV.PathPresentQ(r, cc', qc, mx, q)
    decreases r
  {
    match r
    case Re_alt(r1, r2) =>
      if q in PIV.QuantIds(r1) { PathPresentQRaise(r1, cc, cc', qc, mx, q, k, v); } else { PathPresentQRaise(r2, cc, cc', qc, mx, q, k, v); }
    case Re_con(r1, r2) =>
      if q in PIV.QuantIds(r1) { PathPresentQRaise(r1, cc, cc', qc, mx, q, k, v); } else { PathPresentQRaise(r2, cc, cc', qc, mx, q, k, v); }
    case Re_quant(_, qid0, _, r1) =>
      if qid0 >= 0 && (qid0 as nat) == q {
      } else {
        PathPresentQRaise(r1, cc, cc', qc, AI.get_idx(qc, qid0), q, k, v);
      }
    case Re_capture(_, r1) => PathPresentQRaise(r1, cc, cc', qc, mx, q, k, v);
    case Re_lookaround(_, _, r1) => PathPresentQRaise(r1, cc, cc', qc, mx, q, k, v);
  }

  // =========================================================================
  // 3. The write steps.
  // =========================================================================

  /** A capture write outside the body leaves it stale. */
  lemma BodyStaleCapWrite(r: R.regex, cc: seq<int>, cc': seq<int>, qc: seq<int>, K: int, gid: nat, k: int)
    requires k == CP.start_reg(gid) || k == CP.end_reg(gid)
    requires gid !in PIV.CapIds(r)
    requires forall j: int :: j != k ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires BodyStale(r, cc, qc, K)
    ensures BodyStale(r, cc', qc, K)
  {
    forall c: nat | c in PIV.CapIds(r)
      ensures AI.get_idx(cc', CP.start_reg(c)) < K && AI.get_idx(cc', CP.end_reg(c)) < K
    {
      assert c != gid;
      assert CP.start_reg(c) != k && CP.end_reg(c) != k;
    }
  }

  /** `SetRegisterToCP(start_reg(gid) | end_reg(gid))` at a site outside every
      stamped body, writing a clock above every quant clock. */
  lemma StampLiveCapWrite(re: R.regex, cc: seq<int>, cc': seq<int>, qc: seq<int>, qcp: seq<int>,
                          gid: nat, k: int, v: int)
    requires StampLiveOk(re, cc, qc, qcp)
    requires k == CP.start_reg(gid) || k == CP.end_reg(gid)
    requires forall A: nat :: A in PIV.QuantIds(re) && AI.get_idx(qcp, A) >= 0
               ==> gid !in PIV.CapIds(PIV.QidBody(re, A))
    requires forall j: int :: j != k ==> AI.get_idx(cc', j) == AI.get_idx(cc, j)
    requires AI.get_idx(cc', k) == v && v >= 0
    requires forall x: int :: AI.get_idx(qc, x) <= v
    ensures StampLiveOk(re, cc', qc, qcp)
  {
    reveal StampLiveOk;
    forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(qcp, q) >= 0
      ensures q in PIV.QuantIdsOutsideLooks(re)
              && BodyStale(PIV.QidBody(re, q), cc', qc, AI.get_idx(qc, q))
              && (PIV.QChainFresh(re, qc, -1, q) ==> PIV.PathPresentQ(re, cc', qc, -1, q))
    {
      BodyStaleCapWrite(PIV.QidBody(re, q), cc, cc', qc, AI.get_idx(qc, q), gid, k);
      if PIV.QChainFresh(re, qc, -1, q) {
        PathPresentQRaise(re, cc, cc', qc, -1, q, k, v);
      }
    }
  }

  /** BOTH quant writes `SetQuantToClock(q0, b)` (the mark `s0 < 0`, the true
      stamp `s0 >= 0`) at a site enclosed by no stamped quantifier, with a clock
      above every stored one. A true stamp brings its own site facts. */
  lemma StampLiveQuantWrite(re: R.regex, cc: seq<int>, qc: seq<int>, qcp: seq<int>,
                            qc': seq<int>, qcp': seq<int>, q0: nat, clk: int, s0: int)
    requires PIV.QuantUnique(re)
    requires q0 in PIV.QuantIds(re)
    requires StampLiveOk(re, cc, qc, qcp)
    requires PIV.QuantWriteAt(qc, qcp, qc', qcp', q0, clk, s0)
    requires PIV.NoStampedAbove(re, qcp, q0)
    requires forall x: int :: AI.get_idx(qc, x) < clk
    requires forall x: int :: AI.get_idx(cc, x) < clk
    requires s0 >= 0 ==> q0 in PIV.QuantIdsOutsideLooks(re) && PIV.PathPresentQ(re, cc, qc, -1, q0)
    ensures StampLiveOk(re, cc, qc', qcp')
  {
    reveal StampLiveOk;
    forall q: nat | q in PIV.QuantIds(re) && AI.get_idx(qcp', q) >= 0
      ensures q in PIV.QuantIdsOutsideLooks(re)
              && BodyStale(PIV.QidBody(re, q), cc, qc', AI.get_idx(qc', q))
              && (PIV.QChainFresh(re, qc', -1, q) ==> PIV.PathPresentQ(re, cc, qc', -1, q))
    {
      QidBodyNotSelf(re, q);
      QuantIdsQidBodySub(re, q);
      if q == q0 {
        assert s0 >= 0;
        assert AI.get_idx(qc', q) == clk;
        forall x: nat | x in PIV.QuantIds(PIV.QidBody(re, q)) ensures AI.get_idx(qc', x) < clk {
          assert x != q0;
        }
        PathPresentQOff(re, cc, qc, qc', -1, q0, q0);
      } else {
        assert AI.get_idx(qcp, q) >= 0 && AI.get_idx(qc', q) == AI.get_idx(qc, q);
        assert q0 !in PIV.QuantIds(PIV.QidBody(re, q));
        forall x: nat | x in PIV.QuantIds(PIV.QidBody(re, q))
          ensures AI.get_idx(qc', x) == AI.get_idx(qc, x)
        {
          assert x != q0;
        }
        if q in PIV.QuantIds(PIV.QidBody(re, q0)) {
          if PIV.QChainFresh(re, qc', -1, q) {
            QChainFreshAncGe(re, qc', -1, q0, q);
            assert false;
          }
        } else {
          QChainFreshOff(re, qc, qc', -1, q0, q);
          PathPresentQOff(re, cc, qc, qc', -1, q0, q);
        }
      }
    }
  }
}
