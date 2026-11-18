// (G4a) Capture-free lookarounds inside a greedy CIN plus body (`((?=a)|a?)+`), and (G5a-2a) inside a greedy
// CDN plus body (`((?=a)|b)+`): the scope, machine B's entry, and the frame facts and tie transports that
// replace `RF.CinBodiesLookFreeRE` at the top regex. Design: linden-equiv/endgame/G4a-design.md, G5a2-design.md.
//
// A look body keeps the strong condition: `M.LookBodiesPlusGateRE` asks `RF.CinBodiesLookFreeRE` at every look
// node. (G4b-1) At the top regex a nullable plus body may hold CAPTURING looks off its empty paths: every look an
// empty path can cross is capture-free (`ELk.EmptyPathLooksCapFree`, `(a(?=(b))|c?)+`). A lid the reconstruction
// may re-set (`ELk.LooksQE`) has no carrier content; every other lid keeps its record, and either its ancestors
// keep their clocks or one of them sits in a stamped body, where the stamp's stale body kills the lid's presence
// (`ELk.StampedAncKillsPresence`); the replay only raises quant clocks (`ELk.ReplayQuantClkMono`).
module LindenElkCinLooks {
  import opened Std.Wrappers
  import R = RegElkRegex
  import L = Regex
  import LG = Groups
  import LT = Tree
  import AI = ArrayInterp
  import AReg = Array_Regs
  import CP = Compiler
  import LOr = Oracle
  import LW = WarblreRegExpRecord
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import NUL = LindenElkNullable
  import PIV = LindenElkPikeInv
  import NI = LindenElkNestInv
  import LTB = LindenElkLookTables
  import LL = LindenElkLookLeaves
  import CW = LindenElkCinWalk
  import M = LindenElkMain
  import NRR = LindenElkNulledReconRegs
  import NRC = LindenElkNulledRecon
  import RF = LindenElkReconFrame
  import CLP = LindenElkCinLookPaths
  import FRD = LindenElkFinalReadout
  import TM = LindenElkTwoMachines
  import ELk = LindenElkEmptyLooks
  import NPL = LindenElkNulledPlusLk
  import PSM = LindenElkPikeSim
  import SL = LindenElkStampLive
  import opened LindenElkLiftSimCore
  import opened LindenElkLiftSimOracle

  // =========================================================================
  // 1. The scope.
  // =========================================================================

  /** Every greedy nullable plus body's lookarounds capture nothing (CIN: G4a; CDN: G5a-2a); a look body is in
      the look-free CIN fragment (what `M.LookBodiesPlusGateRE` asks at a look node). */
  ghost predicate CinLooksCapFreeRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinLooksCapFreeRE(r1) && CinLooksCapFreeRE(r2)
    case Re_con(r1, r2) => CinLooksCapFreeRE(r1) && CinLooksCapFreeRE(r2)
    // (G4b-1) a stamp body: every look an empty path can cross is capture-free (others may capture)
    case Re_quant(nul, qid, q, body) =>
      (ELk.StampNode(nul, q) ==> ELk.EmptyPathLooksCapFree(body))
      && CinLooksCapFreeRE(body)
    case Re_capture(_, r1) => CinLooksCapFreeRE(r1)
    // (G5b-1/2/3) a positive look body (either direction, any depth) may hold a greedy CDN plus, and every look inside
    // a nullable plus body there is capture-free; (G5b-3) a negative body is unrestricted (never replayed)
    case Re_lookaround(_, la, r1) =>
      (NRC.PositiveLk(la) ==> RF.StampLooksCapFreeRE(r1)) && LookStampOkRE(r1)
    case _ => true
  }

  /** (G5b-1/2/3) At every positive look node, every look inside a greedy nullable plus body (CIN or CDN) is
      capture-free. */
  ghost predicate LookStampOkRE(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookStampOkRE(r1) && LookStampOkRE(r2)
    case Re_con(r1, r2) => LookStampOkRE(r1) && LookStampOkRE(r2)
    case Re_quant(_, _, _, r1) => LookStampOkRE(r1)
    case Re_capture(_, r1) => LookStampOkRE(r1)
    case Re_lookaround(_, la, r1) => (NRC.PositiveLk(la) ==> RF.StampLooksCapFreeRE(r1)) && LookStampOkRE(r1)
    case _ => true
  }

  /** (G5b-1) `RF.StampBodiesLookFreeRE`, compiled. */
  predicate StampBodiesLookFreeX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampBodiesLookFreeX(r1) && StampBodiesLookFreeX(r2)
    case Re_con(r1, r2) => StampBodiesLookFreeX(r1) && StampBodiesLookFreeX(r2)
    case Re_quant(nul, qid, q, body) =>
      (q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy ==> NR.LookFreeRE(body))
      && StampBodiesLookFreeX(body)
    case Re_capture(_, r1) => StampBodiesLookFreeX(r1)
    case Re_lookaround(_, _, r1) => StampBodiesLookFreeX(r1)
    case _ => true
  }

  lemma StampBodiesLookFreeXSound(re: R.regex)
    requires StampBodiesLookFreeX(re)
    ensures RF.StampBodiesLookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampBodiesLookFreeXSound(r1); StampBodiesLookFreeXSound(r2);
    case Re_con(r1, r2) => StampBodiesLookFreeXSound(r1); StampBodiesLookFreeXSound(r2);
    case Re_quant(_, _, _, r1) => StampBodiesLookFreeXSound(r1);
    case Re_capture(_, r1) => StampBodiesLookFreeXSound(r1);
    case Re_lookaround(_, _, r1) => StampBodiesLookFreeXSound(r1);
    case _ =>
  }

  /** (G5b-3) `RF.StampLooksCapFreeRE`, compiled. */
  predicate StampLooksCapFreeX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampLooksCapFreeX(r1) && StampLooksCapFreeX(r2)
    case Re_con(r1, r2) => StampLooksCapFreeX(r1) && StampLooksCapFreeX(r2)
    case Re_quant(nul, qid, q, body) =>
      (q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy ==> LooksCapFreeX(body))
      && StampLooksCapFreeX(body)
    case Re_capture(_, r1) => StampLooksCapFreeX(r1)
    case Re_lookaround(_, _, r1) => StampLooksCapFreeX(r1)
    case _ => true
  }

  lemma StampLooksCapFreeXSound(re: R.regex)
    requires StampLooksCapFreeX(re)
    ensures RF.StampLooksCapFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => StampLooksCapFreeXSound(r1); StampLooksCapFreeXSound(r2);
    case Re_con(r1, r2) => StampLooksCapFreeXSound(r1); StampLooksCapFreeXSound(r2);
    case Re_quant(nul, qid, q, body) =>
      StampLooksCapFreeXSound(body);
      if q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy { LooksCapFreeXSound(body); }
    case Re_capture(_, r1) => StampLooksCapFreeXSound(r1);
    case Re_lookaround(_, _, r1) => StampLooksCapFreeXSound(r1);
    case _ =>
  }

  /** (G5b-1) `LookStampOkRE`, compiled. */
  predicate LookStampOkX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookStampOkX(r1) && LookStampOkX(r2)
    case Re_con(r1, r2) => LookStampOkX(r1) && LookStampOkX(r2)
    case Re_quant(_, _, _, r1) => LookStampOkX(r1)
    case Re_capture(_, r1) => LookStampOkX(r1)
    case Re_lookaround(_, la, r1) => ((la.Lookahead? || la.Lookbehind?) ==> StampLooksCapFreeX(r1)) && LookStampOkX(r1)
    case _ => true
  }

  lemma LookStampOkXSound(re: R.regex)
    requires LookStampOkX(re)
    ensures LookStampOkRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookStampOkXSound(r1); LookStampOkXSound(r2);
    case Re_con(r1, r2) => LookStampOkXSound(r1); LookStampOkXSound(r2);
    case Re_quant(_, _, _, r1) => LookStampOkXSound(r1);
    case Re_capture(_, r1) => LookStampOkXSound(r1);
    case Re_lookaround(_, la, r1) =>
      if la.Lookahead? || la.Lookbehind? { StampLooksCapFreeXSound(r1); }
      LookStampOkXSound(r1);
    case _ =>
  }

  /** Every lookaround body of `r` is capture-free (executable). */
  predicate LooksCapFreeX(r: R.regex)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LooksCapFreeX(r1) && LooksCapFreeX(r2)
    case Re_con(r1, r2) => LooksCapFreeX(r1) && LooksCapFreeX(r2)
    case Re_quant(_, _, _, r1) => LooksCapFreeX(r1)
    case Re_capture(_, r1) => LooksCapFreeX(r1)
    case Re_lookaround(_, _, r1) => NR.CaptureFreeRE(r1)
    case _ => true
  }

  lemma LooksCapFreeXSound(r: R.regex)
    requires LooksCapFreeX(r)
    ensures PIV.CapIdsInLooks(r) == {}
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LooksCapFreeXSound(r1); LooksCapFreeXSound(r2);
    case Re_con(r1, r2) => LooksCapFreeXSound(r1); LooksCapFreeXSound(r2);
    case Re_quant(_, _, _, r1) => LooksCapFreeXSound(r1);
    case Re_capture(_, r1) => LooksCapFreeXSound(r1);
    case Re_lookaround(_, _, r1) => PIV.CaptureFreeNoCapIds(r1);
    case _ =>
  }

  lemma LookFreeLooksCapFreeX(r: R.regex)
    requires NR.LookFreeRE(r)
    ensures LooksCapFreeX(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => LookFreeLooksCapFreeX(r1); LookFreeLooksCapFreeX(r2);
    case Re_con(r1, r2) => LookFreeLooksCapFreeX(r1); LookFreeLooksCapFreeX(r2);
    case Re_quant(_, _, _, r1) => LookFreeLooksCapFreeX(r1);
    case Re_capture(_, r1) => LookFreeLooksCapFreeX(r1);
    case _ =>
  }

  /** Every greedy CI-nullable plus has a look-free body (executable; moved from MainCinLk). */
  predicate CinBodiesLookFreeX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinBodiesLookFreeX(r1) && CinBodiesLookFreeX(r2)
    case Re_con(r1, r2) => CinBodiesLookFreeX(r1) && CinBodiesLookFreeX(r2)
    case Re_quant(nul, qid, q, body) =>
      (q.min != 0 && q.max == None && nul == R.CINullable && q.greedy ==> NR.LookFreeRE(body))
      && CinBodiesLookFreeX(body)
    case Re_capture(_, r1) => CinBodiesLookFreeX(r1)
    case Re_lookaround(_, _, r1) => CinBodiesLookFreeX(r1)
    case _ => true
  }

  lemma CinBodiesLookFreeXSound(re: R.regex)
    requires CinBodiesLookFreeX(re)
    ensures RF.CinBodiesLookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinBodiesLookFreeXSound(r1); CinBodiesLookFreeXSound(r2);
    case Re_con(r1, r2) => CinBodiesLookFreeXSound(r1); CinBodiesLookFreeXSound(r2);
    case Re_quant(_, _, _, r1) => CinBodiesLookFreeXSound(r1);
    case Re_capture(_, r1) => CinBodiesLookFreeXSound(r1);
    case Re_lookaround(_, _, r1) => CinBodiesLookFreeXSound(r1);
    case _ =>
  }

  /** `CinLooksCapFreeRE`, compiled (for `API.Supported`). */
  predicate CinLooksCapFreeX(re: R.regex)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinLooksCapFreeX(r1) && CinLooksCapFreeX(r2)
    case Re_con(r1, r2) => CinLooksCapFreeX(r1) && CinLooksCapFreeX(r2)
    case Re_quant(nul, qid, q, body) =>
      (q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy ==> EmptyPathLooksCapFreeX(body))
      && CinLooksCapFreeX(body)
    case Re_capture(_, r1) => CinLooksCapFreeX(r1)
    case Re_lookaround(_, la, r1) =>
      ((la.Lookahead? || la.Lookbehind?) ==> StampLooksCapFreeX(r1)) && LookStampOkX(r1)
    case _ => true
  }

  /** (G4b-1) `ELk.EmptyPathLooksCapFree`, compiled: the engine's own nullability (`R.nullable`) decides which
      half of a sequence an empty path can cross. */
  predicate EmptyPathLooksCapFreeX(r: R.regex)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => EmptyPathLooksCapFreeX(r1) && EmptyPathLooksCapFreeX(r2)
    case Re_con(r1, r2) =>
      (R.nullable(r2) != R.NonNullable ==> EmptyPathLooksCapFreeX(r1))
      && (R.nullable(r1) != R.NonNullable ==> EmptyPathLooksCapFreeX(r2))
    case Re_quant(_, _, q, r1) => q.min == 0 || EmptyPathLooksCapFreeX(r1)
    case Re_capture(_, r1) => EmptyPathLooksCapFreeX(r1)
    case Re_lookaround(_, _, b) => NR.CaptureFreeRE(b)
    case _ => true
  }

  lemma EmptyPathLooksCapFreeXSound(r: R.regex)
    requires T.TransWf(r) && EmptyPathLooksCapFreeX(r)
    ensures ELk.EmptyPathLooksCapFree(r)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => EmptyPathLooksCapFreeXSound(r1); EmptyPathLooksCapFreeXSound(r2);
    case Re_con(r1, r2) =>
      if ELk.MayNull(r2) {
        if R.nullable(r2) == R.NonNullable { NUL.TransNonNullable(r2); assert false; }
        EmptyPathLooksCapFreeXSound(r1);
      }
      if ELk.MayNull(r1) {
        if R.nullable(r1) == R.NonNullable { NUL.TransNonNullable(r1); assert false; }
        EmptyPathLooksCapFreeXSound(r2);
      }
    case Re_quant(_, _, q, r1) => if q.min != 0 { EmptyPathLooksCapFreeXSound(r1); }
    case Re_capture(_, r1) => EmptyPathLooksCapFreeXSound(r1);
    case Re_lookaround(_, _, b) => PIV.CaptureFreeNoCapIds(b);
    case _ =>
  }

  lemma CinLooksCapFreeXSound(re: R.regex)
    requires T.TransWf(re) && CinLooksCapFreeX(re)
    ensures CinLooksCapFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinLooksCapFreeXSound(r1); CinLooksCapFreeXSound(r2);
    case Re_con(r1, r2) => CinLooksCapFreeXSound(r1); CinLooksCapFreeXSound(r2);
    case Re_quant(nul, qid, q, body) =>
      CinLooksCapFreeXSound(body);
      if q.min != 0 && q.max == None && nul != R.NonNullable && q.greedy { EmptyPathLooksCapFreeXSound(body); }
    case Re_capture(_, r1) => CinLooksCapFreeXSound(r1);
    case Re_lookaround(_, la, r1) =>
      LookStampOkXSound(r1);
      if la.Lookahead? || la.Lookbehind? { StampLooksCapFreeXSound(r1); }
    case _ =>
  }

  // =========================================================================
  // 2. Machine B's entry: `CW.CinOk` holds for capture-free look bodies.
  // =========================================================================

  lemma CapFreeLooksLkBodies(r: R.regex, S: set<LG.GroupId>)
    requires T.TransWf(r) && PIV.CapIdsInLooks(r) == {}
    ensures LL.LkBodiesInS(T.Translate(r), S)
    decreases r
  {
    match r
    case Re_alt(r1, r2) => CapFreeLooksLkBodies(r1, S); CapFreeLooksLkBodies(r2, S);
    case Re_con(r1, r2) => CapFreeLooksLkBodies(r1, S); CapFreeLooksLkBodies(r2, S);
    case Re_quant(_, _, _, r1) => CapFreeLooksLkBodies(r1, S);
    case Re_capture(_, r1) => CapFreeLooksLkBodies(r1, S);
    case Re_lookaround(_, _, r1) =>
      PIV.DefGroupsCapIds(r1);
      assert PIV.CapIds(r1) == {};
      assert LL.DefGroupsIn(T.Translate(r1), S);
      reveal LL.LookBodyInS();
    case _ =>
  }

  /** `TM.TranslateCinOkCdn` under the G4a scope: the body of a greedy nullable plus, CIN or CDN, has
      capture-free look bodies, and its groups lie in `G`. */
  lemma TranslateCinOkG4(r: R.regex, G: set<LG.GroupId>)
    requires T.TransWf(r) && NR.NestedFragmentCdnRE(r)
    requires CinLooksCapFreeRE(r) && NRC.CdnTopRE(r)
    requires forall g: nat :: g in PIV.CapIdsOutsideLooks(r) ==> g in G
    ensures CW.CinOk(T.Translate(r), G)
    decreases r
  {
    NRC.CdnTopChild(r);
    match r
    case Re_alt(r1, r2) => TranslateCinOkG4(r1, G); TranslateCinOkG4(r2, G);
    case Re_con(r1, r2) => TranslateCinOkG4(r1, G); TranslateCinOkG4(r2, G);
    case Re_capture(_, r1) => TranslateCinOkG4(r1, G);
    case Re_lookaround(_, _, _) =>
    case Re_quant(nul, qid, q, body) =>
      TranslateCinOkG4(body, G);
      var tb := T.Translate(body);
      assert T.Translate(r) == L.Quantified(q.greedy, q.min as nat, T.TrDelta(q), tb);
      if q.min > 0 && (CW.CinGreedyL(q.greedy, T.TrDelta(q), tb) || CW.CdnGreedyL(q.greedy, T.TrDelta(q), tb)) {
        CW.NulGreedyFacts(q.greedy, T.TrDelta(q), tb);   // greedy, Inf, the body is not NonNullable
        assert q.max == None;
        if nul == R.NonNullable {
          NUL.TransNonNullable(body);
          assert false;
        }
        assert nul == R.CINullable || nul == R.CDNullable;
        assert ELk.StampNode(nul, q) && ELk.EmptyPathLooksCapFree(body);   // `CinLooksCapFreeRE`, CIN or CDN
        TM.EPCFTranslate(body);   // (G4b-1) machine B's arm: the crossed looks are group-free
        TM.OutLkTranslate(body);
        assert NPL.OutLk(tb) <= G;
      }
    case _ =>
  }

  // =========================================================================
  // 3. (G4b-1) The reconstruction's look set at the stamped set, and the ancestor frame.
  // =========================================================================

  /** The scope outside look bodies, as `ELk.LooksQECapFree` reads it. */
  lemma CinLooksTop(re: R.regex)
    requires CinLooksCapFreeRE(re)
    ensures ELk.StampLooksCapFreeTop(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => CinLooksTop(r1); CinLooksTop(r2);
    case Re_con(r1, r2) => CinLooksTop(r1); CinLooksTop(r2);
    case Re_quant(_, _, _, body) => CinLooksTop(body);
    case Re_capture(_, r1) => CinLooksTop(r1);
    case _ =>
  }

  /** The capture half of `CLP.QsAvoidLookBodyS`: the reconstruction writes no capture inside a look (scope-free). */
  lemma CapsQAvoidLookBody(r: R.regex, Q: set<int>, lid: nat)
    requires lid in LTB.LookIds(r) && PIV.CapUnique(r)
    ensures ELk.CapsQO(r, Q) * PIV.CaptureRegs(NI.LookBodyOfRE(r, lid)) == {}
  {
    var b := NI.LookBodyOfRE(r, lid);
    ELk.CapsQOOutside(r, Q);
    NI.LookBodyCapsIn(r, lid);
    PIV.CaptureRegsIsSet(b);
    PIV.CaptureRegsSetMono(PIV.CapIds(b), PIV.CapIdsInLooks(r));
    PIV.CapIdsLooksDisjoint(r);
    PIV.CaptureRegsSetDisjoint(PIV.CapIdsOutsideLooks(r), PIV.CapIdsInLooks(r));
  }

  /** The stamp-liveness facts of the winner at its stamped set. */
  lemma BodyStaleAtStamps(re: R.regex, best: AI.Thread, Q: set<int>)
    requires PSM.BestLiveRE(re, best) && Q == ELk.StampSet(best.quant_regs.a_cp)
    ensures forall q: nat :: q in PIV.QuantIds(re) && (q as int) in Q ==>
              SL.BodyStale(PIV.QidBody(re, q), best.capture_regs.a_clk, best.quant_regs.a_clk,
                           AI.get_idx(best.quant_regs.a_clk, q))
  {
    reveal PSM.BestLiveRE();
    forall q: nat | q in PIV.QuantIds(re) && (q as int) in Q
      ensures SL.BodyStale(PIV.QidBody(re, q), best.capture_regs.a_clk, best.quant_regs.a_clk,
                           AI.get_idx(best.quant_regs.a_clk, q))
    {
      assert AI.get_idx(best.quant_regs.a_cp, q) >= 0;
      SL.StampLiveAt(re, best.capture_regs.a_clk, best.quant_regs.a_clk, best.quant_regs.a_cp, q);
    }
  }

  // =========================================================================
  // 4. The frame at the reconstructed winner and the tie transports.
  // =========================================================================

  /** (G4b-1) The frame of the reconstruction at the stamped set `Q`: the look bank equal outside `ELk.LooksQE`, the
      capture clocks outside `ELk.CapsQO`, the quant clocks outside `RF.QuantsQ`, and every quant clock only rose. */
  ghost predicate ClkFrameG4(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread) {
    |a.look_regs.a_cp| == |b.look_regs.a_cp|
    && (forall k :: k !in ELk.LooksQE(re, Q) ==>
          AI.get_idx(a.look_regs.a_cp, k) == AI.get_idx(b.look_regs.a_cp, k)
          && AI.get_idx(a.look_regs.a_clk, k) == AI.get_idx(b.look_regs.a_clk, k))
    && (forall k :: k !in ELk.CapsQO(re, Q) ==> AI.get_idx(a.capture_regs.a_clk, k) == AI.get_idx(b.capture_regs.a_clk, k))
    && (forall k :: k !in RF.QuantsQ(re, Q) ==> AI.get_idx(a.quant_regs.a_clk, k) == AI.get_idx(b.quant_regs.a_clk, k))
    && ELk.QClkGe(a.quant_regs, b.quant_regs.a_clk)
  }

  /** A lid whose ancestors avoid the stamped bodies keeps its path facts. */
  lemma AncFrameAvoid(re: R.regex, Q: set<int>, a: AI.Thread, b: AI.Thread, lid: nat)
    requires lid in LTB.LookIds(re)
    requires CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q) == {} && CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q) == {}
    requires ClkFrameG4(re, Q, a, b)
    ensures forall mx :: NI.LookPathPresent(re, a.capture_regs.a_clk, a.quant_regs.a_clk, mx, lid)
                         == NI.LookPathPresent(re, b.capture_regs.a_clk, b.quant_regs.a_clk, mx, lid)
    ensures forall mx :: NI.MxAtLidLk(re, a.quant_regs.a_clk, mx, lid) == NI.MxAtLidLk(re, b.quant_regs.a_clk, mx, lid)
  {
    ELk.CapsOSub(re, Q);
    var cc1 := a.capture_regs.a_clk;
    var cc2 := b.capture_regs.a_clk;
    var qc1 := a.quant_regs.a_clk;
    var qc2 := b.quant_regs.a_clk;
    assert forall k :: k in CLP.AncCapRegs(re, lid) ==> AI.get_idx(cc1, k) == AI.get_idx(cc2, k) by {
      forall k | k in CLP.AncCapRegs(re, lid) ensures AI.get_idx(cc1, k) == AI.get_idx(cc2, k) {
        if k in ELk.CapsQO(re, Q) { assert k in CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q); }
      }
    }
    assert forall k :: k in CLP.AncQuants(re, lid) ==> AI.get_idx(qc1, k) == AI.get_idx(qc2, k) by {
      forall k | k in CLP.AncQuants(re, lid) ensures AI.get_idx(qc1, k) == AI.get_idx(qc2, k) {
        if k in RF.QuantsQ(re, Q) { assert k in CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q); }
      }
    }
    forall mx ensures NI.LookPathPresent(re, cc1, qc1, mx, lid) == NI.LookPathPresent(re, cc2, qc2, mx, lid)
                      && NI.MxAtLidLk(re, qc1, mx, lid) == NI.MxAtLidLk(re, qc2, mx, lid) {
      CLP.LookPathFrame(re, cc1, qc1, cc2, qc2, mx, lid);
    }
  }

  /** The three readers of a look record see only `get_cp(lk, l)`. */
  lemma GetCpCong(a: AReg.Regs, b: AReg.Regs, l: int)
    requires |a.a_cp| == |b.a_cp| && AI.get_idx(a.a_cp, l) == AI.get_idx(b.a_cp, l)
    ensures AReg.get_cp(a, l) == AReg.get_cp(b, l)
  {}

  lemma FreshBodyCong(crv: CP.FCompiled, str: string, l: int, a: AReg.Regs, b: AReg.Regs,
                      ov: LOr.OracleView, ncap: int, nlook: int, nquant: int)
    requires AReg.get_cp(a, l) == AReg.get_cp(b, l)
    ensures M.FreshBodyMatchPlus(crv, str, l, a, ov, ncap, nlook, nquant)
            == M.FreshBodyMatchPlus(crv, str, l, b, ov, ncap, nlook, nquant)
  {
    reveal M.FreshBodyMatchPlus();
  }

  lemma SubFirstLeafCong(rer: LW.RegExpRecord, crv: CP.FCompiled, str: string, l: int, a: AReg.Regs, b: AReg.Regs)
    requires AReg.get_cp(a, l) == AReg.get_cp(b, l)
    ensures SubFirstLeafAt(rer, crv, str, l, a) == SubFirstLeafAt(rer, crv, str, l, b)
  {}

  /** OkT: a re-set lid has no carrier content; a kept lid either keeps its ancestors' clocks or has an ancestor in
      a stamped body, where the winner's stale body kills its presence (so B's OkT names none of its groups). */
  lemma TieOkTTransportG4(re: R.regex, Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                          gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread)
    requires CinLooksCapFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires PSM.BestLiveRE(re, best) && Q == ELk.StampSet(best.quant_regs.a_cp)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestOkTTop(re, S, gmB, best)
    ensures LookNestOkTTop(re, S, gm, th)
  {
    CinLooksTop(re);
    BodyStaleAtStamps(re, best, Q);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (lid in LTB.LookIds(re)
                          && exists g: LG.GroupId :: g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)))
      ensures NI.LookPathPresent(re, th.capture_regs.a_clk, th.quant_regs.a_clk, -1, lid)
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= 0
              && AI.get_idx(th.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, th.quant_regs.a_clk, -1, lid)
    {
      var g: LG.GroupId :| g in S && g in gm && g in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      if (lid as int) in ELk.LooksQE(re, Q) { ELk.LooksQECapFree(re, Q, lid); assert false; }
      assert g !in G by { if g in G { assert g in G * S; } }
      assert g in gmB;
      assert exists g0: LG.GroupId :: g0 in S && g0 in gmB && g0 in PIV.CapIds(NI.LookBodyOfRE(re, lid));
      assert NI.LookPathPresent(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid)
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= 0
             && AI.get_idx(best.look_regs.a_clk, lid as int) >= NI.MxAtLidLk(re, best.quant_regs.a_clk, -1, lid);
      if CLP.AncCapRegs(re, lid) * RF.CapsQ(re, Q) != {} || CLP.AncQuants(re, lid) * RF.QuantsQ(re, Q) != {} {
        ELk.StampedAncKillsPresence(re, best.capture_regs.a_clk, best.quant_regs.a_clk, -1, lid, Q);
        assert false;
      }
      AncFrameAvoid(re, Q, th, best, lid);
      assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
    }
  }

  /** BackT: a kept lid keeps its record, and its dominance moves down to the winner (the replay only raised quant
      clocks). */
  lemma TieBackTransportG4(re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                           Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                           gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                           ncap: int, nlook: int, nquant: int)
    requires CinLooksCapFreeRE(re) && LTB.LookUnique(re)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestBackTTop(re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTop(re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    CinLooksTop(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ensures var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
              rf.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                  && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                       rf.value.look_regs, rf.value.quant_regs)
                  ==> g in gm
    {
      if (lid as int) in ELk.LooksQE(re, Q) {
        ELk.LooksQECapFree(re, Q, lid);   // no group of the body: the conclusion is vacuous
      } else {
        GetCpCong(th.look_regs, best.look_regs, lid as int);
        FreshBodyCong(crv, str, lid as int, th.look_regs, best.look_regs, ov, ncap, nlook, nquant);
        assert M.MatchedPosLA(crv, best.look_regs, lid as int);
        assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
        ELk.LookPathDomMono(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk,
                            best.quant_regs.a_clk, lid);
        assert NI.LookPathDom(re, AI.get_idx(best.look_regs.a_clk, lid as int), best.quant_regs.a_clk, lid);
        var rf := M.FreshBodyMatchPlus(crv, str, lid as int, th.look_regs, ov, ncap, nlook, nquant);
        if rf.Some? {
          forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
                                 && g in PIV.GmOfLive(NI.LookBodyOfRE(re, lid), rf.value.capture_regs,
                                                      rf.value.look_regs, rf.value.quant_regs)
            ensures g in gm
          {
            assert g !in G by { if g in G { assert g in G * S; } }
            assert g in gmB;
          }
        }
      }
    }
  }

  lemma TieDeepTransportG4(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                           Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                           gmB: LG.GroupMap, gm: LG.GroupMap, best: AI.Thread, th: AI.Thread,
                           ncap: int, nlook: int, nquant: int)
    requires CinLooksCapFreeRE(re) && LTB.LookUnique(re)
    requires G * S == {} && LL.GmAgreeOutside(gmB, gm, G)
    requires ClkFrameG4(re, Q, th, best)
    requires LookNestBackTTopDeep(rer, re, crv, str, ov, S, gmB, best, ncap, nlook, nquant)
    ensures LookNestBackTTopDeep(rer, re, crv, str, ov, S, gm, th, ncap, nlook, nquant)
  {
    CinLooksTop(re);
    forall lid: nat | lid in NI.TopLookIds(re)
                      && (M.MatchedPosLA(crv, th.look_regs, lid as int)
                          && lid in LTB.LookIds(re)
                          && NI.LookPathDom(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk, lid))
      ensures var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
              lsub.Some? ==>
                forall g: LG.GroupId ::
                  g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid)) ==>
                    (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
                    && (g in gm ==> g in lsub.value)
    {
      if (lid as int) in ELk.LooksQE(re, Q) {
        ELk.LooksQECapFree(re, Q, lid);   // no group of the body: the conclusion is vacuous
      } else {
        GetCpCong(th.look_regs, best.look_regs, lid as int);
        SubFirstLeafCong(rer, crv, str, lid as int, th.look_regs, best.look_regs);
        assert M.MatchedPosLA(crv, best.look_regs, lid as int);
        assert AI.get_idx(th.look_regs.a_clk, lid as int) == AI.get_idx(best.look_regs.a_clk, lid as int);
        ELk.LookPathDomMono(re, AI.get_idx(th.look_regs.a_clk, lid as int), th.quant_regs.a_clk,
                            best.quant_regs.a_clk, lid);
        assert NI.LookPathDom(re, AI.get_idx(best.look_regs.a_clk, lid as int), best.quant_regs.a_clk, lid);
        var lsub := SubFirstLeafAt(rer, crv, str, lid as int, th.look_regs);
        if lsub.Some? {
          forall g: LG.GroupId | g in S && g in PIV.CapIds(NI.LookBodyOfRE(re, lid))
            ensures (g in lsub.value ==> g in gm && gm[g] == lsub.value[g])
                    && (g in gm ==> g in lsub.value)
          {
            assert g !in G by { if g in G { assert g in G * S; } }
            assert (g in gmB <==> g in gm) && (g in gmB ==> gmB[g] == gm[g]);
          }
        }
      }
    }
  }

  /** THE TRANSPORT under the G4b-1 scope, at the winner's stamped set. */
  lemma TieTransportG4(rer: LW.RegExpRecord, re: R.regex, crv: CP.FCompiled, str: string, ov: LOr.OracleView,
                       Q: set<int>, S: set<LG.GroupId>, G: set<LG.GroupId>,
                       bleaf: LT.Leaf, leaf: LT.Leaf, best: AI.Thread, th: AI.Thread,
                       ncap: int, nlook: int, nquant: int)
    requires CinLooksCapFreeRE(re) && PIV.CapUnique(re) && PIV.QuantUnique(re) && LTB.LookUnique(re)
    requires PSM.BestLiveRE(re, best) && Q == ELk.StampSet(best.quant_regs.a_cp)
    requires G * S == {} && LL.GmAgreeOutside(bleaf.1, leaf.1, G)
    requires ClkFrameG4(re, Q, th, best)
    requires BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(bleaf), Some(best), ncap, nlook, nquant)
    requires GmtTieOutside(re, th, leaf.1, S)   // machine A
    ensures BestTieLkNestedTop(rer, re, crv, str, ov, S, Some(leaf), Some(th), ncap, nlook, nquant)
  {
    TieOkTTransportG4(re, Q, S, G, bleaf.1, leaf.1, best, th);
    TieBackTransportG4(re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, th, ncap, nlook, nquant);
    TieDeepTransportG4(rer, re, crv, str, ov, Q, S, G, bleaf.1, leaf.1, best, th, ncap, nlook, nquant);
  }
}
