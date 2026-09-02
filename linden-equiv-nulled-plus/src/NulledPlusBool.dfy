// §2.5b stage 2, rung C: the BOOLEAN-TREE side of the priority theorem — what the
// tree construction (`ActionsTreeRep*`) can use directly. The construction is driven
// by `EL.BoolTreeLk` (flag-based, group-map-free) trees; rung A's `CinPlusPriority`
// is stated on `IsTree` trees at a group map. The bridge is `BoolTreeLk` determinism
// + `EncodeEqualLkRec`, under the ENCODING INVARIANT `EncOk` the construction
// threads: some flag correctly encodes the stack's checks, and if it differs from
// the construction's own flag that is only the do-while's lift (CannotExit → CanExit
// on a shielded stack), where the two flags' trees coincide (`CE.BoolFlagLiftRec`).
/** Rung C's boolean-tree bridge: the encoding invariant threaded by the tree
    construction, `BoolTreeLk` determinism, the tree-location bound for empty
    paths, and `CinPlusPriority` restated on `BoolTreeLk` trees. */
module LindenElkNulledPlusBool {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import LT = Tree
  import BS = BooleanSemantics
  import FS = FunctionalSemantics
  import FU = FunctionalUtils
  import NUL = LindenElkNullable
  import EL = LindenElkEntryLk
  import CE = LindenElkCheckErase
  import LL = LindenElkLookLeaves
  import TR = LindenElkTreeRep
  import NP = LindenElkNulledPlus
  import NT = LindenElkNulledPlusTie

  // ===========================================================================
  // The encoding invariant
  // ===========================================================================

  /** Some flag `b2` correctly encodes `acts`' checks at `inp`; if it is not the
      construction's flag `b`, then `b2` is `CannotExit`, `b` is `CanExit`, and
      the stack is shielded (every check sits behind a NonNullable regex) —
      the do-while lift's situation, where both flags produce the same tree. */
  ghost predicate EncOk(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool) {
    exists b2: BS.LoopBool ::
      BS.BoolEncoding(b2, inp, acts)
      && (b2 != b ==> b2 == BS.CannotExit && b == BS.CanExit && CE.ShieldedActs(acts))
  }

  lemma EncOkIntro(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires BS.BoolEncoding(b, inp, acts)
    ensures EncOk(acts, inp, b)
  {}

  lemma NoChecksEncoding(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?
    ensures BS.BoolEncoding(b, inp, acts)
    decreases |acts|
  {
    if |acts| > 0 {
      forall i | 0 <= i < |acts[1..]| ensures !acts[1..][i].Acheck? { assert acts[1..][i] == acts[i + 1]; }
      NoChecksEncoding(acts[1..], inp, b);
    }
  }

  /** A check-free prefix is transparent to the encoding. */
  lemma EncodingPrefixNoChecks(parts: LS.Actions, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires forall p :: 0 <= p < |parts| ==> !parts[p].Acheck?
    ensures BS.BoolEncoding(b, inp, parts + cont) <==> BS.BoolEncoding(b, inp, cont)
    decreases |parts|
  {
    if |parts| == 0 {
      assert parts + cont == cont;
    } else {
      var rest := parts[1..];
      forall p | 0 <= p < |rest| ensures !rest[p].Acheck? { assert rest[p] == parts[p + 1]; }
      EncodingPrefixNoChecks(rest, cont, inp, b);
      assert parts + cont == [parts[0]] + (rest + cont);
      match parts[0]
      case Areg(r) => BS.EncodeNext(b, inp, rest + cont, r);
      case Aclose(g) => BS.EncodeClose(b, inp, rest + cont, g);
      case Acheck(_) =>
    }
  }

  /** Peeling a head that is not a NonNullable regex (a `Aclose`, or an `Areg`
      that cannot shield) keeps the invariant at the same flag. */
  lemma EncOkTailReg(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires EncOk(acts, inp, b)
    requires |acts| > 0 && !acts[0].Acheck?
    requires !(acts[0].Areg? && NUL.NonNullableL(acts[0].r))
    ensures EncOk(acts[1..], inp, b)
  {
    var cont := acts[1..];
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts)
      && (b2 != b ==> b2 == BS.CannotExit && b == BS.CanExit && CE.ShieldedActs(acts));
    assert BS.BoolEncoding(b2, inp, cont);
    if b2 != b { CE.ShieldedTail(acts); }
  }

  /** Peeling a check at `CanExit` (the construction only recurses past a
      passing check): the rest is encoded at `CanExit`. */
  lemma EncOkTailCheck(acts: LS.Actions, inp: LC.Input)
    requires EncOk(acts, inp, BS.CanExit)
    requires |acts| > 0 && acts[0].Acheck?
    ensures EncOk(acts[1..], inp, BS.CanExit)
  {
    var cont := acts[1..];
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts)
      && (b2 != BS.CanExit ==> b2 == BS.CannotExit && CE.ShieldedActs(acts));
    if b2 == BS.CanExit {
      assert BS.BoolEncoding(BS.CanExit, inp, cont);
    } else {
      // a check at index 0 has no shield before it
      assert acts[0].Acheck?;
      assert exists j :: 0 <= j < 0 && acts[j].Areg? && NUL.NonNullableL(acts[j].r);
      assert false;
    }
  }

  /** Expanding a regex head into check-free `parts` (the construction's
      Disjunction/Sequence/Group/forced-quantifier steps) keeps the invariant,
      provided a NonNullable head leaves a NonNullable part behind. */
  lemma EncOkExpand(acts: LS.Actions, parts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires EncOk(acts, inp, b)
    requires |acts| > 0 && acts[0].Areg?
    requires forall p :: 0 <= p < |parts| ==> !parts[p].Acheck?
    requires NUL.NonNullableL(acts[0].r) ==>
               exists p :: 0 <= p < |parts| && parts[p].Areg? && NUL.NonNullableL(parts[p].r)
    ensures EncOk(parts + acts[1..], inp, b)
  {
    var cont := acts[1..];
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts)
      && (b2 != b ==> b2 == BS.CannotExit && b == BS.CanExit && CE.ShieldedActs(acts));
    assert BS.BoolEncoding(b2, inp, cont);
    EncodingPrefixNoChecks(parts, cont, inp, b2);
    if b2 != b { CE.ShieldedCons(parts, acts); }
  }

  /** Reading a character: the rest is encoded at `CanExit` on the advanced input. */
  lemma EncOkRead(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool, nextinp: LC.Input)
    requires EncOk(acts, inp, b)
    requires |acts| > 0 && acts[0].Areg?
    requires |inp.next| > 0 && nextinp == LC.Input(inp.next[1..], [inp.next[0]] + inp.pref)
    ensures EncOk(acts[1..], nextinp, BS.CanExit)
  {
    var cont := acts[1..];
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts);
    assert BS.BoolEncoding(b2, inp, cont);
    assert inp == LC.Input([inp.next[0]] + inp.next[1..], inp.pref);
    BS.TrueEncoding(inp.next[1..], inp.next[0], inp.pref, cont, b2);
  }

  /** Some flag encodes the stack (the invariant minus the flag relation). */
  ghost predicate Encodable(acts: LS.Actions, inp: LC.Input) {
    exists b2: BS.LoopBool :: BS.BoolEncoding(b2, inp, acts)
  }

  lemma EncOkEncodable(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires EncOk(acts, inp, b)
    ensures Encodable(acts, inp)
  {}

  /** Peeling any regex/close head keeps encodability (no flag relation kept). */
  lemma EncodableTail(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires EncOk(acts, inp, b)
    requires |acts| > 0 && !acts[0].Acheck?
    ensures Encodable(acts[1..], inp)
  {
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts);
    assert BS.BoolEncoding(b2, inp, acts[1..]);
  }

  /** The iteration list of a free quantifier at `inp`, at `CannotExit`. */
  lemma EncOkIter(r1: L.Regex, qn: L.Regex, cont: LS.Actions, inp: LC.Input)
    requires Encodable(cont, inp)
    ensures EncOk([LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont, inp, BS.CannotExit)
  {
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, cont);
    BS.EncodeNext(b2, inp, cont, qn);
    var rest := [LS.Areg(qn)] + cont;
    var chk := [LS.Acheck(inp)] + rest;
    assert chk[0] == LS.Acheck(inp) && chk[1..] == rest;
    assert BS.BoolEncoding(BS.CannotExit, inp, chk);
    BS.EncodeNext(BS.CannotExit, inp, chk, r1);
    assert [LS.Areg(r1)] + chk == [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont;
  }

  /** The do-while's lifted iteration list (NonNullable body) at `CanExit`. */
  lemma EncOkIterLift(r1: L.Regex, qn: L.Regex, cont: LS.Actions, inp: LC.Input)
    requires Encodable(cont, inp)
    requires NUL.NonNullableL(r1)
    ensures EncOk([LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont, inp, BS.CanExit)
  {
    var il := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont;
    EncOkIter(r1, qn, cont, inp);
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, il)
      && (b2 != BS.CannotExit ==> b2 == BS.CannotExit && BS.CannotExit == BS.CanExit && CE.ShieldedActs(il));
    assert b2 == BS.CannotExit;
    assert CE.ShieldedActs(il) by {
      forall i | 0 <= i < |il| && il[i].Acheck?
        ensures exists j :: 0 <= j < i && il[j].Areg? && NUL.NonNullableL(il[j].r)
      {
        assert il[0] == LS.Areg(r1);
        assert i > 0;
      }
    }
  }

  // ===========================================================================
  // Determinism and the bridge to IsTree
  // ===========================================================================

  least lemma BoolTreeLkDetermNP(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input,
                               b: BS.LoopBool, t1: LT.Tree, t2: LT.Tree)
    requires EL.BoolTreeLk(rer, acts, inp, b, t1)
    requires EL.BoolTreeLk(rer, acts, inp, b, t2)
    ensures t1 == t2
  {
    if |acts| == 0 {
    } else {
      var cont := acts[1..];
      match acts[0]
      case Acheck(strcheck) =>
        if b == BS.CanExit {
          match t1 { case Progress(c1) => match t2 { case Progress(c2) =>
                BoolTreeLkDetermNP(rer, cont, inp, BS.CanExit, c1, c2); case _ => } case _ => }
        }
      case Aclose(gid) =>
        match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
              BoolTreeLkDetermNP(rer, cont, inp, b, c1, c2); case _ => } case _ => }
      case Areg(r) =>
        match r
        case Epsilon => BoolTreeLkDetermNP(rer, cont, inp, b, t1, t2);
        case Character(cd) =>
          match LC.ReadChar(rer, cd, inp, WP.Forward) {
            case None =>
            case Some(pair) =>
              match t1 { case Read(cc1, c1) => match t2 { case Read(cc2, c2) =>
                    BoolTreeLkDetermNP(rer, cont, pair.1, BS.CanExit, c1, c2); case _ => } case _ => }
          }
        case Disjunction(r1, r2) =>
          match t1 { case Choice(a1, b1t) => match t2 { case Choice(a2, b2t) =>
                BoolTreeLkDetermNP(rer, [LS.Areg(r1)] + cont, inp, b, a1, a2);
                BoolTreeLkDetermNP(rer, [LS.Areg(r2)] + cont, inp, b, b1t, b2t); case _ => } case _ => }
        case Sequence(r1, r2) =>
          BoolTreeLkDetermNP(rer, [LS.Areg(r1), LS.Areg(r2)] + cont, inp, b, t1, t2);
        case Quantified(greedy, min, delta, r1) =>
          var gidl := L.DefGroups(r1);
          if min > 0 {
            var q1 := L.Quantified(greedy, min - 1, delta, r1);
            match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
                  BoolTreeLkDetermNP(rer, [LS.Areg(r1), LS.Areg(q1)] + cont, inp, b, c1, c2); case _ => } case _ => }
          } else if delta == LN.NN(0) {
            BoolTreeLkDetermNP(rer, cont, inp, b, t1, t2);
          } else {
            var qn := L.Quantified(greedy, 0, FS.NoiPred(delta), r1);
            var iacts := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(qn)] + cont;
            match t1 {
              case Choice(a1, b1t) =>
                match t2 {
                  case Choice(a2, b2t) =>
                    var it1 := if greedy then a1 else b1t;  var sk1 := if greedy then b1t else a1;
                    var it2 := if greedy then a2 else b2t;  var sk2 := if greedy then b2t else a2;
                    match it1 {
                      case GroupActionT(g1, ti1) =>
                        match it2 {
                          case GroupActionT(g2, ti2) =>
                            BoolTreeLkDetermNP(rer, iacts, inp, BS.CannotExit, ti1, ti2);
                            BoolTreeLkDetermNP(rer, cont, inp, b, sk1, sk2);
                          case _ =>
                        }
                      case _ =>
                    }
                  case _ =>
                }
              case _ =>
            }
          }
        case Group(gid, r1) =>
          match t1 { case GroupActionT(g1, c1) => match t2 { case GroupActionT(g2, c2) =>
                BoolTreeLkDetermNP(rer, [LS.Areg(r1), LS.Aclose(gid)] + cont, inp, b, c1, c2); case _ => } case _ => }
        case AnchorR(a) =>
          if LS.AnchorSatisfied(rer, a, inp) {
            match t1 { case AnchorPass(a1, c1) => match t2 { case AnchorPass(a2, c2) =>
                  BoolTreeLkDetermNP(rer, cont, inp, b, c1, c2); case _ => } case _ => }
          }
        case LookaroundR(lk, r1) =>
          // LkGateOk pins tlk == ComputeTr(rer,[Areg(r1)],inp,Empty,LkDir(lk)) on BOTH
          // sides; its verdict LkResult(lk,tlk,Empty,inp).Some? is single-valued.
          var tlkc := FU.ComputeTr(rer, [LS.Areg(r1)], inp, LG.Empty, L.LkDir(lk));
          match t1 {
            case LK(l1, k1, c1) =>
              assert k1 == tlkc;
              match t2 {
                case LK(l2, k2, c2) =>
                  assert k2 == tlkc;
                  BoolTreeLkDetermNP(rer, cont, inp, b, c1, c2);
                case LKFail(l2, k2) =>
                  assert k2 == tlkc;   // both verdicts read LkResult(lk,tlkc,Empty,inp).Some?
                  assert false;
                case _ =>
              }
            case LKFail(l1, k1) =>
              assert k1 == tlkc;
              match t2 {
                case LK(l2, k2, c2) => assert k2 == tlkc; assert false;
                case LKFail(l2, k2) => assert k2 == tlkc;
                case _ =>
              }
            case _ =>
          }
        case Backreference(_) =>
    }
  }
  /** THE BRIDGE: under the invariant, the construction's `BoolTreeLk` tree is
      the `IsTree` tree at EVERY group map. */
  lemma EncTreeIsTree(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, b: BS.LoopBool, t: LT.Tree, gm: LG.GroupMap)
    requires EL.PikeLkActionsRec(acts)
    requires EncOk(acts, inp, b)
    requires EL.BoolTreeLk(rer, acts, inp, b, t)
    ensures LS.IsTree(rer, acts, inp, gm, WP.Forward, t)
  {
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts)
      && (b2 != b ==> b2 == BS.CannotExit && b == BS.CanExit && CE.ShieldedActs(acts));
    var tt := FU.ComputeTr(rer, acts, inp, gm, WP.Forward);
    FU.ComputeTrIsTree(rer, acts, inp, gm, WP.Forward);
    EL.EncodeEqualLkRec(rer, inp, acts, b2, tt, gm);
    if b2 != b { CE.BoolFlagLiftRec(rer, acts, inp, tt); }
    BoolTreeLkDetermNP(rer, acts, inp, b, t, tt);
  }

  /** Under the invariant a `BoolTreeLk` tree exists at the construction's flag. */
  lemma EncTreeExists(rer: LW.RegExpRecord, acts: LS.Actions, inp: LC.Input, b: BS.LoopBool) returns (t: LT.Tree)
    requires EL.PikeLkActionsRec(acts)
    requires EncOk(acts, inp, b)
    ensures EL.BoolTreeLk(rer, acts, inp, b, t)
  {
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, acts)
      && (b2 != b ==> b2 == BS.CannotExit && b == BS.CanExit && CE.ShieldedActs(acts));
    t := FU.ComputeTr(rer, acts, inp, LG.Empty, WP.Forward);
    FU.ComputeTrIsTree(rer, acts, inp, LG.Empty, WP.Forward);
    EL.EncodeEqualLkRec(rer, inp, acts, b2, t, LG.Empty);
    if b2 != b { CE.BoolFlagLiftRec(rer, acts, inp, t); }
  }

  // ===========================================================================
  // Chains
  // ===========================================================================

  lemma ChainTEqChain(p: seq<LG.GroupAction>, t: LT.Tree)
    ensures TR.ChainT(p, t) == NP.Chain(p, t)
    decreases |p|
  {
    if |p| > 0 { ChainTEqChain(p[1..], t); }
  }

  lemma RACongChainOutside(p: seq<LG.GroupAction>, a: LT.Tree, b: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires NP.ResAgreeAtOutside(a, b, inp, S)
    ensures NP.ResAgreeAtOutside(NP.Chain(p, a), NP.Chain(p, b), inp, S)
    decreases |p|
  {
    if |p| > 0 {
      RACongChainOutside(p[1..], a, b, inp, S);
      NP.RACongGroupOutside(p[0], NP.Chain(p[1..], a), NP.Chain(p[1..], b), inp, S);
    }
  }

  // ===========================================================================
  // Location: the continuation's tree sits inside `[Areg(r)] + cont`'s when
  // `r` has an empty path — so it is PSize-smaller (the construction's measure)
  // ===========================================================================

  /** If `r` has an empty path at `inp`, SOME `BoolTreeLk` tree of `cont` (at the
      same flag) is no larger than the tree of `[Areg(r)] + cont`. */
  lemma BoolTreeLkEmptyPathSub(rer: LW.RegExpRecord, r: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool, tt: LT.Tree)
    returns (tc: LT.Tree)
    requires EL.BoolTreeLk(rer, [LS.Areg(r)] + cont, inp, b, tt)
    requires NP.FirstEmptyPathL(rer, r, inp).Some?
    ensures EL.BoolTreeLk(rer, cont, inp, b, tc)
    ensures CE.PSize(tc) <= CE.PSize(tt)
    ensures forall SS: set<LG.GroupId> :: CE.LkConfinedTree(tt, SS) ==> CE.LkConfinedTree(tc, SS)
    ensures forall SS: set<LG.GroupId> :: CE.LkConfinedTreeK(tt, SS) ==> CE.LkConfinedTreeK(tc, SS)
    decreases NT.RSizeL(r), NT.MinOfL(r)
  {
    var acts := [LS.Areg(r)] + cont;
    assert acts[0] == LS.Areg(r) && acts[1..] == cont;
    var solo := [LS.Areg(r)];
    assert solo[0] == LS.Areg(r) && solo[1..] == [];
    assert NP.FirstEmptyPathA(rer, [], inp) == Some([]);
    match r
    case Epsilon =>
      tc := tt;
    case Character(_) =>
      assert false;
    case Disjunction(r1, r2) =>
      assert [LS.Areg(r1)] + [] == [LS.Areg(r1)] && [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      match tt {
        case Choice(ta, tb) =>
          if NP.FirstEmptyPathL(rer, r1, inp).Some? {
            tc := BoolTreeLkEmptyPathSub(rer, r1, cont, inp, b, ta);
          } else {
            assert NP.FirstEmptyPathL(rer, r2, inp).Some?;
            tc := BoolTreeLkEmptyPathSub(rer, r2, cont, inp, b, tb);
          }
        case _ => assert false;
      }
    case Sequence(r1, r2) =>
      assert [LS.Areg(r1), LS.Areg(r2)] + cont == [LS.Areg(r1)] + ([LS.Areg(r2)] + cont);
      assert [LS.Areg(r1), LS.Areg(r2)] + [] == [LS.Areg(r1)] + [LS.Areg(r2)];
      assert [LS.Areg(r2)] + [] == [LS.Areg(r2)];
      NT.FirstEmptyPathAComp(rer, r1, [LS.Areg(r2)], inp);
      assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, solo, inp);
      assert NP.FirstEmptyPathA(rer, solo, inp) == NP.FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(r2)] + [], inp);
      assert NP.FirstEmptyPathL(rer, r1, inp).Some? && NP.FirstEmptyPathL(rer, r2, inp).Some?;
      var tm := BoolTreeLkEmptyPathSub(rer, r1, [LS.Areg(r2)] + cont, inp, b, tt);
      tc := BoolTreeLkEmptyPathSub(rer, r2, cont, inp, b, tm);
    case Quantified(greedy, min, delta, r1) =>
      var gidl := L.DefGroups(r1);
      if min > 0 {
        var qn := L.Quantified(greedy, min - 1, delta, r1);
        assert NT.RSizeL(qn) == NT.RSizeL(r) && NT.MinOfL(qn) < NT.MinOfL(r);
        assert [LS.Areg(r1), LS.Areg(qn)] + cont == [LS.Areg(r1)] + ([LS.Areg(qn)] + cont);
        assert [LS.Areg(r1), LS.Areg(qn)] + [] == [LS.Areg(r1)] + [LS.Areg(qn)];
        assert [LS.Areg(qn)] + [] == [LS.Areg(qn)];
        NT.FirstEmptyPathAComp(rer, r1, [LS.Areg(qn)], inp);
        assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, solo, inp);
        assert NP.FirstEmptyPathA(rer, solo, inp)
            == NT.PrePath(LG.Reset(gidl), NP.FirstEmptyPathA(rer, [LS.Areg(r1), LS.Areg(qn)] + [], inp));
        assert NP.FirstEmptyPathL(rer, r1, inp).Some? && NP.FirstEmptyPathL(rer, qn, inp).Some?;
        match tt {
          case GroupActionT(g, t1) =>
            var tm := BoolTreeLkEmptyPathSub(rer, r1, [LS.Areg(qn)] + cont, inp, b, t1);
            tc := BoolTreeLkEmptyPathSub(rer, qn, cont, inp, b, tm);
          case _ => assert false;
        }
      } else if delta == LN.NN(0) {
        tc := tt;
      } else {
        match tt {
          case Choice(ta, tb) =>
            tc := if greedy then tb else ta;
          case _ => assert false;
        }
      }
    case Group(gid, r1) =>
      assert [LS.Areg(r1), LS.Aclose(gid)] + cont == [LS.Areg(r1)] + ([LS.Aclose(gid)] + cont);
      assert [LS.Areg(r1), LS.Aclose(gid)] + [] == [LS.Areg(r1)] + [LS.Aclose(gid)];
      assert [LS.Aclose(gid)][0] == LS.Aclose(gid) && [LS.Aclose(gid)][1..] == [];
      assert [LG.Close(gid)] + [] == [LG.Close(gid)];
      assert NP.FirstEmptyPathA(rer, [LS.Aclose(gid)], inp) == Some([LG.Close(gid)]);
      NT.FirstEmptyPathAComp(rer, r1, [LS.Aclose(gid)], inp);
      assert NP.FirstEmptyPathL(rer, r, inp) == NP.FirstEmptyPathA(rer, solo, inp);
      assert NP.FirstEmptyPathA(rer, solo, inp)
          == NT.PrePath(LG.Open(gid), NP.FirstEmptyPathA(rer, [LS.Areg(r1), LS.Aclose(gid)] + [], inp));
      assert NP.FirstEmptyPathL(rer, r1, inp).Some?;
      match tt {
        case GroupActionT(g, t1) =>
          var tm := BoolTreeLkEmptyPathSub(rer, r1, [LS.Aclose(gid)] + cont, inp, b, t1);
          var cl := [LS.Aclose(gid)] + cont;
          assert cl[0] == LS.Aclose(gid) && cl[1..] == cont;
          match tm {
            case GroupActionT(g2, t2) => tc := t2;
            case _ => assert false;
          }
        case _ => assert false;
      }
    case AnchorR(a) =>
      assert LS.AnchorSatisfied(rer, a, inp);
      match tt {
        case AnchorPass(a2, t1) => tc := t1;
        case _ => assert false;
      }
    case LookaroundR(lk, r1) =>
      assert NP.LkVerdictL(rer, lk, r1, inp);
      match tt {
        case LK(lk2, tlk, t1) => tc := t1;
        case LKFail(lk2, tlk) => assert false;
        case _ => assert false;
      }
    case Backreference(_) =>
      assert false;
  }

  // ===========================================================================
  // THE PRIORITY THEOREM on BoolTreeLk trees
  // ===========================================================================

  /** `CinPlusPriority` for the construction: the CIN-greedy plus's spec tree
      `t` (flag `b`) is first-result-equivalent outside `S` to the engine's shape
      built from the iteration tree `ti` (flag `CannotExit`) and the
      continuation tree `tcont` (flag `b`), chained through the body's first
      empty path. */
  lemma CinPlusPriorityBool(rer: LW.RegExpRecord, r1: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool,
                            S: set<LG.GroupId>, t: LT.Tree, ti: LT.Tree, tcont: LT.Tree)
    requires EL.PikeLkRegexRec(r1) && EL.PikeLkActionsRec(cont)
    requires LL.LkBodiesInS(r1, S) && LL.LkActsInS(cont, S)
    requires NUL.CINullableL(r1)
    requires EncOk(cont, inp, b)
    requires EL.BoolTreeLk(rer, [LS.Areg(L.Quantified(true, 1, LN.Inf, r1))] + cont, inp, b, t)
    requires EL.BoolTreeLk(rer, [LS.Areg(r1), LS.Acheck(inp), LS.Areg(L.Quantified(true, 0, LN.Inf, r1))] + cont, inp, BS.CannotExit, ti)
    requires EL.BoolTreeLk(rer, cont, inp, b, tcont)
    ensures NP.FirstEmptyPathL(rer, r1, inp).Some?
    ensures var gidl := L.DefGroups(r1);
            var p := NP.FirstEmptyPathL(rer, r1, inp).value;
            NP.ResAgreeAtOutside(LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti),
                                           LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont))),
                                 t, inp, S)
  {
    var gidl := L.DefGroups(r1);
    var plus := L.Quantified(true, 1, LN.Inf, r1);
    var star := L.Quantified(true, 0, LN.Inf, r1);
    var pacts := [LS.Areg(plus)] + cont;
    var ia := [LS.Areg(r1), LS.Acheck(inp), LS.Areg(star)] + cont;
    assert EL.PikeLkRegexRec(plus) && EL.PikeLkRegexRec(star);
    assert EL.PikeLkActionRec(LS.Areg(plus)) && EL.PikeLkActionRec(LS.Areg(star))
        && EL.PikeLkActionRec(LS.Areg(r1)) && EL.PikeLkActionRec(LS.Acheck(inp));
    EL.PikeLkActionsRecConsIff(LS.Areg(plus), cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(star), cont);
    EL.PikeLkActionsRecConsIff(LS.Acheck(inp), [LS.Areg(star)] + cont);
    EL.PikeLkActionsRecConsIff(LS.Areg(r1), [LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert ia == [LS.Areg(r1)] + ([LS.Acheck(inp)] + ([LS.Areg(star)] + cont));
    assert EL.PikeLkActionsRec(pacts) && EL.PikeLkActionsRec(ia);
    EncOkConsPlus(plus, cont, inp, b);
    EncOkEncodable(cont, inp, b);
    EncOkIter(r1, star, cont, inp);
    // one group map at a time: bridge all three trees, then rung A
    var gm0 := LG.Empty;
    EncTreeIsTree(rer, pacts, inp, b, t, gm0);
    EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm0));
    EncTreeIsTree(rer, cont, inp, b, tcont, gm0);
    NP.CinPlusPriority(rer, r1, cont, inp, gm0, S, t, ti, tcont);
    var p := NP.FirstEmptyPathL(rer, r1, inp).value;
    var tcin := LT.Choice(LT.GroupActionT(LG.Reset(gidl), ti), LT.GroupActionT(LG.Reset(gidl), NP.Chain(p, tcont)));
    forall gm: LG.GroupMap
      ensures var rc := LT.TreeRes(tcin, gm, inp, WP.Forward);
              var rp := LT.TreeRes(t, gm, inp, WP.Forward);
              (rc.Some? <==> rp.Some?)
              && (rc.Some? ==> rc.value.0 == rp.value.0 && LL.GmAgreeOutside(rc.value.1, rp.value.1, S))
    {
      EncTreeIsTree(rer, pacts, inp, b, t, gm);
      EncTreeIsTree(rer, ia, inp, BS.CannotExit, ti, LG.GMReset(gidl, gm));
      EncTreeIsTree(rer, cont, inp, b, tcont, gm);
      NP.CinPlusPriority(rer, r1, cont, inp, gm, S, t, ti, tcont);
    }
  }

  /** Pushing the (non-NonNullable) plus onto an encoded continuation. */
  lemma EncOkConsPlus(plus: L.Regex, cont: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires EncOk(cont, inp, b)
    ensures EncOk([LS.Areg(plus)] + cont, inp, b)
  {
    var acts := [LS.Areg(plus)] + cont;
    assert acts[0] == LS.Areg(plus) && acts[1..] == cont;
    var b2: BS.LoopBool :| BS.BoolEncoding(b2, inp, cont)
      && (b2 != b ==> b2 == BS.CannotExit && b == BS.CanExit && CE.ShieldedActs(cont));
    BS.EncodeNext(b2, inp, cont, plus);
    if b2 != b {
      assert CE.ShieldedActs(acts) by {
        forall i | 0 <= i < |acts| && acts[i].Acheck?
          ensures exists j :: 0 <= j < i && acts[j].Areg? && NUL.NonNullableL(acts[j].r)
        {
          assert i > 0 && cont[i - 1].Acheck?;
          var j0: int :| 0 <= j0 < i - 1 && cont[j0].Areg? && NUL.NonNullableL(cont[j0].r);
          assert acts[j0 + 1] == cont[j0];
        }
      }
    }
  }

  /** A check-free stack satisfies the invariant at any flag. */
  lemma EncOkNoChecks(acts: LS.Actions, inp: LC.Input, b: BS.LoopBool)
    requires forall i :: 0 <= i < |acts| ==> !acts[i].Acheck?
    ensures EncOk(acts, inp, b)
  {
    NoChecksEncoding(acts, inp, b);
  }

  /** The consumers' readout: first-result agreement outside `S` at the empty
      map is `FirstLeaf` agreement outside `S` (`FirstLeaf` IS `TreeRes` at `Empty`). */
  lemma RAFirstLeafOutside(t1: LT.Tree, t2: LT.Tree, inp: LC.Input, S: set<LG.GroupId>)
    requires NP.ResAgreeAtOutside(t1, t2, inp, S)
    ensures (LT.FirstLeaf(t1, inp).None? <==> LT.FirstLeaf(t2, inp).None?)
    ensures LT.FirstLeaf(t1, inp).Some? ==>
              LT.FirstLeaf(t1, inp).value.0 == LT.FirstLeaf(t2, inp).value.0
              && LL.GmAgreeOutside(LT.FirstLeaf(t1, inp).value.1, LT.FirstLeaf(t2, inp).value.1, S)
  {
    var r1 := LT.TreeRes(t1, LG.Empty, inp, WP.Forward);
    var r2 := LT.TreeRes(t2, LG.Empty, inp, WP.Forward);
    assert (r1.Some? <==> r2.Some?) && (r1.Some? ==> r1.value.0 == r2.value.0 && LL.GmAgreeOutside(r1.value.1, r2.value.1, S));
  }

  /** Outside the empty set, first-result agreement is first-leaf EQUALITY. */
  lemma RAFirstLeafEmpty(t1: LT.Tree, t2: LT.Tree, inp: LC.Input)
    requires NP.ResAgreeAtOutside(t1, t2, inp, {})
    ensures LT.FirstLeaf(t1, inp) == LT.FirstLeaf(t2, inp)
  {
    RAFirstLeafOutside(t1, t2, inp, {});
    var r1 := LT.FirstLeaf(t1, inp);
    var r2 := LT.FirstLeaf(t2, inp);
    if r1.Some? {
      var g1 := r1.value.1;
      var g2 := r2.value.1;
      assert LL.GmAgreeOutside(g1, g2, {});
      assert g1 == g2 by {
        forall g ensures (g in g1 <==> g in g2) && (g in g1 ==> g1[g] == g2[g]) {
          assert g !in {};
        }
      }
    }
  }
}
