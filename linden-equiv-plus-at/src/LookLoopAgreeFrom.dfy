// (G3a, P3 A5) `QCI.FLookLoopAgree` over a SUFFIX of the look loop. The look loop at row `lid`
// only replays rows `[lid, maxlook]`, so it is enough that those rows' bodies avoid the quant set
// `D`. G3a uses it per row: after row `l` reconstructs a nulled plus, the loop continues on banks
// whose quant positions differ from the synthetic winner's only on `QIdsOuter(body_l)`, and every
// later row is either unrelated to `body_l` (`QuantUnique`) or lies inside one of its looks.
module LindenElkLookLoopAgreeFrom {
  import opened Std.Wrappers
  import AI = ArrayInterp
  import AReg = Array_Regs
  import R = RegElkRegex
  import CP = Compiler
  import LOr = Oracle
  import QCI = LindenElkQuantCpIrrel

  /** `QCI.LookAstsAvoid` restricted to the rows `[lid, maxlook]`. */
  ghost predicate LookAstsAvoidFrom(crv: CP.FCompiled, lid: int, maxlook: int, D: set<int>) {
    forall l :: lid <= l <= maxlook && 0 <= l < |crv.f_look_ast| ==> QCI.QidsOf(crv.f_look_ast[l]) * D == {}
  }

  /** The whole-table premise implies every suffix's. */
  lemma LookAstsAvoidFromAll(crv: CP.FCompiled, lid: int, maxlook: int, D: set<int>)
    requires QCI.LookAstsAvoid(crv, D)
    ensures LookAstsAvoidFrom(crv, lid, maxlook, D)
  {}

  lemma FLookLoopAgreeFrom(crv: CP.FCompiled, str: string, lid: int, maxlook: int,
                           cap: AReg.Regs, lk: AReg.Regs, q1: AReg.Regs, q2: AReg.Regs, ov: LOr.OracleView,
                           D: set<int>)
    requires QCI.QAgree(q1, q2, D)
    requires LookAstsAvoidFrom(crv, lid, maxlook, D)
    ensures var r1 := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, q1, ov);
            var r2 := AI.FLookLoop(crv, str, lid, maxlook, cap, lk, q2, ov);
            r1.0 == r2.0 && r1.1 == r2.1 && QCI.QAgree(r1.2, r2.2, D) && r1.3 == r2.3
    decreases maxlook - lid
  {
    if lid > maxlook { return; }
    var next := lid + 1;
    match AReg.get_cp(lk, lid) {
      case None => FLookLoopAgreeFrom(crv, str, next, maxlook, cap, lk, q1, q2, ov, D);
      case Some(cp) =>
        var looktype := if 0 <= lid < |crv.f_look_types| then crv.f_look_types[lid] else R.Lookahead;
        if AI.capture_type(looktype) {
          var bytecode := AI.get_code_v(crv.f_look_capture_bc, lid);
          var dir := AI.capture_direction(looktype);
          var lookcdn := if 0 <= lid < |crv.f_look_cdns| then crv.f_look_cdns[lid] else [];
          var lookast := if 0 <= lid < |crv.f_look_ast| then crv.f_look_ast[lid] else R.Re_empty;
          assert QCI.QidsOf(lookast) * D == {};
          QCI.FFindMatchPlusAgree(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, q1, q2, 0, lookcdn, D);
          var (res1, ova) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, q1, 0, lookcdn);
          var (res2, ovb) := AI.FFindMatchPlus(bytecode, lookast, crv.f_plus_bc, str, ov, dir, cp, cap, lk, q2, 0, lookcdn);
          var (nc1, nl1, nq1) := match res1 case None => (cap, lk, q1) case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          var (nc2, nl2, nq2) := match res2 case None => (cap, lk, q2) case Some(t) => (t.capture_regs, t.look_regs, t.quant_regs);
          assert nc1 == nc2 && nl1 == nl2 && QCI.QAgree(nq1, nq2, D) && ova == ovb;
          FLookLoopAgreeFrom(crv, str, next, maxlook, nc1, nl1, nq1, nq2, ova, D);
        } else {
          FLookLoopAgreeFrom(crv, str, next, maxlook, cap, lk, q1, q2, ov, D);
        }
    }
  }
}
