// Phase 4b (layer 1): Linden-side representation predicates over RegElk code.
//
// NfaRepL relates a LINDEN regex to RegElk bytecode; characters are related
// SEMANTICALLY (ExpectationMatches: the char_expectation accepts exactly the
// chars the CharDescr matches), so the whole tree-simulation argument can be
// carried out on the Linden side, mirroring Linden's proven PikeEquiv
// development as closely as possible.
//
// qm: the quantifier-groups map qid -> DefGroups(translated body). RegElk's
// SetQuantToClock instruction carries only a qid, but the tree's Reset node
// carries the group list — qm restores the connection (and is the bedrock of
// the Phase-4 clock/filter_reset denotation). QmapOk pins qm against the
// (annotated) regex; discharging QmapOk for annotate output is a separate
// uniqueness lemma (deferred to the assembly).
//
// The bridge TransNfaRep turns Phase-4a's compiler adherence (NfaRepRE over
// the RegElk AST) into NfaRepL over the translated regex, using CharSemAgree.
//
// ActionsRepL is the continuation representation (port of Linden NFA.dfy's
// ActionsRep): RegElk's star back-edge is an explicit Jmp (Linden uses
// EndLoop(l) instead), which the jump_bc rule absorbs — Acheck is represented
// by the fall-through EndLoop alone.
/** Phase 4b layer 1: representation predicates relating a **Linden** `Regex`/`Actions`
    continuation to RegElk bytecode. `NfaRepL` and `ActionsRepL` are the Linden-side
    analogues of RegElk's own `NfaRepRE`/`ActionsRepRE` (Phase 4a), reached via the
    translation bridge `TransNfaRep`; characters are related semantically through
    `ExpectationMatches` rather than syntactically, so the tree-simulation argument in
    later layers can be carried out entirely on the Linden side. */
module LindenElkActionsRep {
  import opened Std.Wrappers
  import LW = WarblreRegExpRecord
  import WP = WarblrePrimitives
  import LC = Chars
  import LG = Groups
  import L = Regex
  import LN = WarblreNumeric
  import LS = Semantics
  import R = RegElkRegex
  import RC = Charclasses
  import RB = Bytecode
  import CP = Compiler
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import NUL = LindenElkNullable
  import LOr = Oracle

  // The erased-id tables: RegElk's bytecode carries bare integer ids where the
  // Linden AST carries structure, so the Linden-side representation predicates
  // need a table per erased id namespace.
  //   quants: qid -> groups reset by that quantifier's iterations, on the
  //           TRANSLATED (Linden) side (recovers what `SetQuantToClock(qid, _)`
  //           drops).
  //   looks:  lid -> the (flavour, body) that `CheckOracle(lid)` /
  //           `NegCheckOracle(lid)` assert (recovers what the single-instruction
  //           lookaround encoding drops).
  //   ov:     the lookaround oracle the main pass reads. It belongs with the
  //           tables rather than as a separate parameter: the main pass never
  //           writes it (the build passes ran first), so it is as static as
  //           `quants`/`looks` are, and bundling keeps the whole
  //           NfaRepL/TreeRepRE/simulation stack at one table parameter.
  /** The static tables the Linden-side representation predicates consult:
      quantifier reset groups by `qid`, lookaround (flavour, body) pairs by
      `lid`, and the oracle bits the lookaround instructions test. Bundled in
      one record so the whole `NfaRepL`/`TreeRepRE`/simulation stack threads a
      single table parameter. */
  datatype QMap = QMap(quants: map<int, LG.GroupSet>,
                       looks: map<int, (L.Lookaround, L.Regex)>,
                       ov: LOr.OracleView)

  // qm agrees with every quantifier of the (annotated) RegElk regex.
  /** `qm` correctly records, for every quantifier in the (annotated) RegElk regex
      `re`, the `DefGroups` of that quantifier's translated body — i.e. `qm` is a
      faithful reset-group table for `re`. */
  ghost predicate QmapOk(re: R.regex, qm: QMap)
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => QmapOk(r1, qm) && QmapOk(r2, qm)
    case Re_con(r1, r2) => QmapOk(r1, qm) && QmapOk(r2, qm)
    case Re_quant(nul, qid, q, r1) =>
      qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1)) && QmapOk(r1, qm)
    case Re_capture(_, r1) => QmapOk(r1, qm)
    case Re_lookaround(_, _, r1) => QmapOk(r1, qm)
  }

  // qm's lookaround table agrees with every lookaround of the (annotated)
  // RegElk regex — the `QmapOk` of the second namespace.
  /** `qm.looks` correctly records, for every lookaround `(lid, la, body)` in the
      (annotated) RegElk regex `re`, that lid's translated flavour and body — the
      link the single-instruction `CheckOracle(lid)` encoding erases, and the one
      the oracle-bit reasoning needs to know WHICH body a bit speaks about. */
  ghost predicate LmapOk(re: R.regex, qm: QMap)
    requires T.TransWf(re)
    decreases re
  {
    match re
    case Re_empty => true
    case Re_character(_) => true
    case Re_anchor(_) => true
    case Re_alt(r1, r2) => LmapOk(r1, qm) && LmapOk(r2, qm)
    case Re_con(r1, r2) => LmapOk(r1, qm) && LmapOk(r2, qm)
    case Re_quant(_, _, _, r1) => LmapOk(r1, qm)
    case Re_capture(_, r1) => LmapOk(r1, qm)
    case Re_lookaround(lid, la, r1) =>
      lid in qm.looks && qm.looks[lid] == (T.TrLookaround(la), T.Translate(r1))
      && LmapOk(r1, qm)
  }

  /** A lookaround flavour asserts a match (rather than its absence) — the
      `CheckOracle` / `NegCheckOracle` split in the bytecode. */
  predicate PositiveL(lk: L.Lookaround) {
    lk.LookAhead? || lk.LookBehind?
  }

  // ===========================================================================
  // Semantic character agreement and expectation-level reading
  // ===========================================================================

  // ce accepts exactly the characters cd matches (under rer).
  /** `ce` (a RegElk `char_expectation`) accepts exactly the characters that `cd`
      (a Linden `CharDescr`) matches under `rer` — the semantic bridge between
      RegElk's and Linden's character representations. */
  ghost predicate ExpectationMatches(rer: LW.RegExpRecord, ce: RC.char_expectation, cd: LC.CharDescr) {
    forall ch: char :: RC.is_accepted(Some(ch), ce) <==> LC.CharMatch(rer, ch, cd)
  }

  // Reading a character through a char_expectation (forward), mirroring
  // Linden's ReadChar but with RegElk's acceptance test.
  /** Reads one character forward through a `char_expectation`, mirroring Linden's
      `ReadChar` but testing acceptance with RegElk's `is_accepted`. */
  function ReadCharE(ce: RC.char_expectation, i: LC.Input): Option<(char, LC.Input)> {
    if |i.next| == 0 then None
    else if RC.is_accepted(Some(i.next[0]), ce)
         then Some((i.next[0], LC.Input(i.next[1..], [i.next[0]] + i.pref)))
         else None
  }

  // Under ExpectationMatches, expectation-reading IS Linden's ReadChar.
  /** Under `ExpectationMatches`, `ReadCharE` and Linden's `ReadChar` compute the same
      result — expectation-based reading agrees with the reference semantics'
      character reading. */
  lemma ReadAgree(rer: LW.RegExpRecord, ce: RC.char_expectation, cd: LC.CharDescr, i: LC.Input)
    requires ExpectationMatches(rer, ce, cd)
    ensures ReadCharE(ce, i) == LC.ReadChar(rer, cd, i, WP.Forward)
  {}

  // ===========================================================================
  // NfaRepL: Linden regex represented in RegElk code
  // ===========================================================================

  /** The Linden-side compiled-code representation predicate: `r` is represented as
      RegElk bytecode `c` running from `pc1` to `pc2`. Structurally mirrors `NfaRepRE`
      but is stated over a *Linden* `Regex` (post-translation) and restricted to the
      star fragment — `LookaroundR`/`AnchorR`/`Backreference` have no rule and are
      unrepresented. */
  /** The instruction at `pc` is a fork with a backward arm — only the
      do-while scheme emits one; the pivot for the zero-width `Acheck` and
      the loop-view star arm below. */
  ghost predicate BackForkAt(c: RB.code, pc: nat) {
    match NR.GetPcRE(c, pc)
    case Some(Fork(x, y)) => x >= 0 && y >= 0 && (x as nat <= pc || y as nat <= pc)
    case _ => false
  }

  /** `k` forced copies of `r1`'s block, each headed by a `SetQuantToClock`
      whose `qid` maps (through `qm`) to `r1`'s reset groups — the Linden-side
      mirror of `NfaRepRE`'s `NfaRepMinRE` (and of the model's `NfaRepMin`,
      whose `ResetRegs(gidl)` head carries the group list directly). */
  ghost predicate NfaRepMinL(rer: LW.RegExpRecord, qm: QMap, k: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat)
    decreases r1, k + 2
  {
    if k == 0 then pc1 == pc2
    else
      var body := pc1 + 1;
      var rest := k - 1;
      exists e1: nat ::
        (exists qid: int ::
           NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
           && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && NfaRepL(rer, qm, r1, c, body, e1)
        && NfaRepMinL(rer, qm, rest, r1, c, e1, pc2)
  }

  /** `k` optional fork-guarded layers of `r1`'s block, every fork skipping to
      the common `pc2` and each layer's `EndLoop` falling through to the next —
      the Linden-side mirror of `NfaRepRE`'s `NfaRepOptRE`. */
  ghost predicate NfaRepOptL(rer: LW.RegExpRecord, qm: QMap, k: nat, greedy: bool, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat)
    decreases r1, k + 2
  {
    if k == 0 then pc1 == pc2
    else exists e1: nat ::
      NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
      && (exists qid: int ::
            NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
      && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
      && NfaRepL(rer, qm, r1, c, pc1 + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NfaRepOptL(rer, qm, k - 1, greedy, r1, c, e1 + 1, pc2)
  }

  /** The GENERIC unbounded-`min` layout (SUPPORTED_FRAGMENT 2.5a): `min` forced
      copies of `r1`'s block ending at `em`, then the ordinary star loop
      (fork / clock-mark / `BeginLoop` / body / `EndLoop` / back-edge). Factored
      out of `NfaRepL`'s `Inf` arm as its own predicate -- written inline there,
      its `exists` makes the Dafny 4.11 Boogie translation ill-formed. */
  ghost predicate NfaRepGenL(rer: LW.RegExpRecord, qm: QMap, min: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat)
    // above `NfaRepMinL`'s `r1, min + 2` (which it calls) and `NfaRepL`'s `r1, 1`
    decreases r1, min + 3
  {
    // The trigger is EXPLICIT: left to infer one, Dafny 4.11 emits an ill-formed
    // Boogie axiom for this quantifier ("undeclared identifier: _t#0#1", 44
    // resolution errors, translator crash). The conjunct that trips it is the
    // back-edge `GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))` -- the star arm gets
    // away with the same shape only because its jump target is the PARAMETER
    // `pc1` rather than a bound variable.
    exists em: nat, e1: nat
      {:trigger NfaRepMinL(rer, qm, min, r1, c, pc1, em), NfaRepL(rer, qm, r1, c, em + 3, e1)} ::
      NfaRepMinL(rer, qm, min, r1, c, pc1, em)
      && NR.GetPcRE(c, em) == Some(RB.Fork(e1 + 2, em + 1))
      && (exists qid: int ::
            NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
      && NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
      && NfaRepL(rer, qm, r1, c, em + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))
      && pc2 == e1 + 2
  }

  /** The CIN-GREEDY end-fork layout (SUPPORTED_FRAGMENT 2.5b): min-1 forced
      copies of `r1`'s block ending at the head fork `em`, then a guarded loop
      whose EXIT path stamps `SetQuantToClock(qid, true)` — recording "the
      mandatory iteration matched empty here" for the nulled-plus capture
      reconstruction. Both the head fork's re-entry and the end fork's re-entry
      target the stamp at `em + 1`; the two stamps share ONE `qid` (the inner
      existential binds both). Factored out of `NfaRepL`'s `Inf` arm as its own
      predicate with an explicit trigger, exactly like `NfaRepGenL` (an inline
      `exists` there makes the Dafny 4.11 Boogie translation ill-formed). */
  ghost predicate NfaRepCinL(rer: LW.RegExpRecord, qm: QMap, min: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat)
    requires min > 0
    // above `NfaRepMinL`'s `r1, (min-1) + 2` (which it calls) and `NfaRepL`'s `r1, 1`
    decreases r1, min + 3
  {
    exists em: nat, e1: nat
      {:trigger NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em), NfaRepL(rer, qm, r1, c, em + 3, e1)} ::
      NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
      && NR.GetPcRE(c, em) == Some(RB.Fork(em + 1, e1 + 2))
      && (exists qid: int ::
            NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
            && NR.GetPcRE(c, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
      && NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
      && NfaRepL(rer, qm, r1, c, em + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(c, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
      && pc2 == e1 + 3
  }

  ghost predicate NfaRepL(rer: LW.RegExpRecord, qm: QMap, r: L.Regex, c: RB.code, pc1: nat, pc2: nat)
    decreases r, 1
  {
    match r
    case Epsilon => pc1 == pc2
    case Character(cd) =>
      pc2 == pc1 + 1
      && exists ce :: NR.GetPcRE(c, pc1) == Some(RB.Consume(ce)) && ExpectationMatches(rer, ce, cd)
    case Disjunction(r1, r2) =>
      exists e1: nat ::
        NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NfaRepL(rer, qm, r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NfaRepL(rer, qm, r2, c, e1 + 1, pc2)
    case Sequence(r1, r2) =>
      exists e1: nat :: NfaRepL(rer, qm, r1, c, pc1, e1) && NfaRepL(rer, qm, r2, c, e1, pc2)
    case Quantified(greedy, min, delta, r1) =>
      if min == 0 && delta == LN.Inf then
        // the star: fast-path arm, kept verbatim for star-fragment consumers
        (exists e1: nat ::
          NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && (exists qid: int ::
                NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
                && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NfaRepL(rer, qm, r1, c, pc1 + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2)
        // ... or the LOOP VIEW: the star seen from the do-while's backward
        // fork, its stamp and body region BEHIND the pc - how the residual
        // star is represented at the loop's decision point; only NonNullable
        // bodies loop this way (the do-while's standing justification), and
        // the construction needs that fact to shield the dissolved check
        || (NUL.NonNullableL(r1) && exists em: nat ::
          NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(em, pc1 + 1) else RB.Fork(pc1 + 1, em))
          && em <= pc1
          && (exists qid: int ::
                NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
                && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
          && NfaRepL(rer, qm, r1, c, em + 1, pc1)
          && pc2 == pc1 + 1)
      else
        // bounded {min,min+kx}: min forced copies, then kx optional layers;
        // unbounded min > 0 is the engine's do-while, represented only for
        // NonNullable bodies
        (match delta
         case Inf =>
           // The do-while arm and the GENERIC arm (SUPPORTED_FRAGMENT 2.5a) are
           // written as GUARD-DISJOINT DISJUNCTS, not an `if`: an if-then-else
           // expression inside this nested `match delta` arm makes Boogie
           // translation fail ("undeclared identifier: _t#0#1").
           min > 0
           && ((NUL.NonNullableL(r1)
                && exists em: nat, e1: nat ::
                     NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
                     && (exists qid: int ::
                           NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
                           && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                     && NfaRepL(rer, qm, r1, c, em + 1, e1)
                     && NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                     && pc2 == e1 + 1)
               // the GENERIC scheme: a nullable body under an unbounded min > 0
               // compiles to `min` forced copies followed by the ordinary star
               // loop at `em` -- and only for a LAZY quantifier.
               // No `Acheck` has to be manufactured here, which is why this arm
               // carries no nullability hypothesis. Its body lives in
               // `NfaRepGenL` because an `exists` written inline in this nested
               // `match delta` arm makes Dafny 4.11 emit an ill-formed Boogie
               // axiom ("undeclared identifier: _t#0#1").
               || (!NUL.NonNullableL(r1) && !greedy
                   && NfaRepGenL(rer, qm, min, r1, c, pc1, pc2))
               // the CIN-GREEDY end-fork scheme (§2.5b): a CI-nullable body
               // under a GREEDY unbounded min > 0. The `!NonNullableL` conjunct
               // is redundant (CINotNonNullableL) but keeps the three disjuncts
               // SYNTACTICALLY guard-disjoint. The CDN-greedy scheme
               // (CheckNullable) stays out of the fragment.
               || (!NUL.NonNullableL(r1) && greedy && NUL.CINullableL(r1)
                   && NfaRepCinL(rer, qm, min, r1, c, pc1, pc2)))
         case NN(kx) =>
           exists em: nat ::
             NfaRepMinL(rer, qm, min, r1, c, pc1, em)
             && NfaRepOptL(rer, qm, kx, greedy, r1, c, em, pc2))
    case Group(gid, r1) =>
      exists e1: nat ::
        NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
        && NfaRepL(rer, qm, r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
        && pc2 == e1 + 1
    case LookaroundR(lk, r1) =>
      // the main pass carries only the oracle consultation: one zero-width
      // instruction, whose bare `lid` the `looks` table maps back to this
      // lookaround's flavour and body (the quantifier idiom for erased ids)
      pc2 == pc1 + 1
      && exists lid: int ::
           NR.GetPcRE(c, pc1) == Some(if PositiveL(lk) then RB.CheckOracle(lid)
                                                       else RB.NegCheckOracle(lid))
           && lid in qm.looks && qm.looks[lid] == (lk, r1)
    case AnchorR(la) =>
      pc2 == pc1 + 1
      && exists a: R.anchor ::
           NR.GetPcRE(c, pc1) == Some(RB.AnchorAssertion(a)) && T.TrAnchor(a) == la
    case Backreference(_) => false
  }

  /** Introduction lemma for the bounded-quantifier arm of `NfaRepL` (mirror of
      `NfaRepRE`'s `NfaRepREQuantIntro`): package the forced-copy and
      optional-layer chains without exposing the existential. */
  lemma NfaRepLQuantIntro(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, kx: nat, r1: L.Regex, c: RB.code, pc1: nat, em: nat, pc2: nat)
    requires NfaRepMinL(rer, qm, min, r1, c, pc1, em)
    requires NfaRepOptL(rer, qm, kx, greedy, r1, c, em, pc2)
    ensures NfaRepL(rer, qm, L.Quantified(greedy, min, LN.NN(kx), r1), c, pc1, pc2)
  {
  }

  /** Inversion lemma for the bounded-quantifier arm of `NfaRepL`: recover the
      seam label between the forced copies and the optional layers. */
  lemma NfaRepLQuantInv(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, kx: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat) returns (em: nat)
    requires NfaRepL(rer, qm, L.Quantified(greedy, min, LN.NN(kx), r1), c, pc1, pc2)
    ensures NfaRepMinL(rer, qm, min, r1, c, pc1, em)
    ensures NfaRepOptL(rer, qm, kx, greedy, r1, c, em, pc2)
  {
    em :| NfaRepMinL(rer, qm, min, r1, c, pc1, em)
      && NfaRepOptL(rer, qm, kx, greedy, r1, c, em, pc2);
  }

  /** Introduction lemma for the do-while arm of `NfaRepL`. */
  lemma NfaRepLPlusIntro(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, r1: L.Regex, c: RB.code, pc1: nat, em: nat, e1: nat, pc2: nat, qid: int)
    requires min > 0 && NUL.NonNullableL(r1)
    requires NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
    requires NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NfaRepL(rer, qm, r1, c, em + 1, e1)
    requires NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
    requires pc2 == e1 + 1
    ensures NfaRepL(rer, qm, L.Quantified(greedy, min, LN.Inf, r1), c, pc1, pc2)
  {
  }

  /** Inversion lemma for the do-while arm of `NfaRepL`. */
  lemma NfaRepLPlusInv(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat) returns (em: nat, e1: nat)
    requires min > 0
    // 2.5a made the unbounded arm a two-way `if` on the body's nullability;
    // the do-while side must now be selected by the caller.
    requires NUL.NonNullableL(r1)
    requires NfaRepL(rer, qm, L.Quantified(greedy, min, LN.Inf, r1), c, pc1, pc2)
    ensures NUL.NonNullableL(r1)
    ensures NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
    ensures exists qid: int ::
      NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
      && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    ensures NfaRepL(rer, qm, r1, c, em + 1, e1)
    ensures NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
    ensures pc2 == e1 + 1
  {
    var mn1 := min - 1;
    em, e1 :|
      NfaRepMinL(rer, qm, mn1, r1, c, pc1, em)
      && (exists qid: int ::
            NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
      && NfaRepL(rer, qm, r1, c, em + 1, e1)
      && NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
      && pc2 == e1 + 1;
  }

  /** Introduction lemma for the GENERIC arm of `NfaRepL` (§2.5a): `min` forced
      copies ending at `em`, then the ordinary star loop. */
  lemma NfaRepLGenIntro(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, r1: L.Regex, c: RB.code, pc1: nat, em: nat, e1: nat, pc2: nat, qid: int)
    requires min > 0 && !NUL.NonNullableL(r1) && !greedy
    requires NfaRepMinL(rer, qm, min, r1, c, pc1, em)
    requires NR.GetPcRE(c, em) == Some(RB.Fork(e1 + 2, em + 1))
    requires NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
    requires NfaRepL(rer, qm, r1, c, em + 3, e1)
    requires NR.GetPcRE(c, e1) == Some(RB.EndLoop)
    requires NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))
    requires pc2 == e1 + 2
    ensures NfaRepL(rer, qm, L.Quantified(greedy, min, LN.Inf, r1), c, pc1, pc2)
  {
  }

  /** Inversion lemma for the GENERIC arm of `NfaRepL` (§2.5a): recover the end
      of the forced copies and the end of the loop body. */
  lemma NfaRepLGenInv(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat) returns (em: nat, e1: nat)
    requires min > 0
    // §2.5b split the nullable side on greediness; the GENERIC side must now
    // be selected by the caller (LAZY).
    requires !NUL.NonNullableL(r1) && !greedy
    requires NfaRepL(rer, qm, L.Quantified(greedy, min, LN.Inf, r1), c, pc1, pc2)
    ensures NfaRepMinL(rer, qm, min, r1, c, pc1, em)
    ensures NR.GetPcRE(c, em) == Some(RB.Fork(e1 + 2, em + 1))
    ensures exists qid: int ::
      NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    ensures NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
    ensures NfaRepL(rer, qm, r1, c, em + 3, e1)
    ensures NR.GetPcRE(c, e1) == Some(RB.EndLoop)
    ensures NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))
    ensures pc2 == e1 + 2
  {
    em, e1 :|
      NfaRepMinL(rer, qm, min, r1, c, pc1, em)
      && NR.GetPcRE(c, em) == Some(RB.Fork(e1 + 2, em + 1))
      && (exists qid: int ::
            NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
      && NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
      && NfaRepL(rer, qm, r1, c, em + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(em))
      && pc2 == e1 + 2;
  }

  /** Introduction lemma for the CIN-GREEDY end-fork arm of `NfaRepL` (§2.5b). */
  lemma NfaRepLCinIntro(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, r1: L.Regex, c: RB.code, pc1: nat, em: nat, e1: nat, pc2: nat, qid: int)
    requires min > 0 && !NUL.NonNullableL(r1) && greedy && NUL.CINullableL(r1)
    requires NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
    requires NR.GetPcRE(c, em) == Some(RB.Fork(em + 1, e1 + 2))
    requires NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
    requires NR.GetPcRE(c, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    requires NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
    requires NfaRepL(rer, qm, r1, c, em + 3, e1)
    requires NR.GetPcRE(c, e1) == Some(RB.EndLoop)
    requires NR.GetPcRE(c, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
    requires pc2 == e1 + 3
    ensures NfaRepL(rer, qm, L.Quantified(greedy, min, LN.Inf, r1), c, pc1, pc2)
  {
    assert NfaRepCinL(rer, qm, min, r1, c, pc1, pc2);
  }

  /** Inversion lemma for the CIN-GREEDY end-fork arm of `NfaRepL` (§2.5b):
      recover the head fork and the loop-body end; the two stamps share one
      `qid`. */
  lemma NfaRepLCinInv(rer: LW.RegExpRecord, qm: QMap, greedy: bool, min: nat, r1: L.Regex, c: RB.code, pc1: nat, pc2: nat) returns (em: nat, e1: nat)
    requires min > 0
    requires !NUL.NonNullableL(r1) && greedy
    requires NfaRepL(rer, qm, L.Quantified(greedy, min, LN.Inf, r1), c, pc1, pc2)
    ensures NUL.CINullableL(r1)
    ensures NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
    ensures NR.GetPcRE(c, em) == Some(RB.Fork(em + 1, e1 + 2))
    ensures exists qid: int ::
      NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
      && NR.GetPcRE(c, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
      && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1)
    ensures NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
    ensures NfaRepL(rer, qm, r1, c, em + 3, e1)
    ensures NR.GetPcRE(c, e1) == Some(RB.EndLoop)
    ensures NR.GetPcRE(c, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
    ensures pc2 == e1 + 3
  {
    assert NfaRepCinL(rer, qm, min, r1, c, pc1, pc2);
    em, e1 :|
      NfaRepMinL(rer, qm, min - 1, r1, c, pc1, em)
      && NR.GetPcRE(c, em) == Some(RB.Fork(em + 1, e1 + 2))
      && (exists qid: int ::
            NR.GetPcRE(c, em + 1) == Some(RB.SetQuantToClock(qid, false))
            && NR.GetPcRE(c, e1 + 2) == Some(RB.SetQuantToClock(qid, true))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
      && NR.GetPcRE(c, em + 2) == Some(RB.BeginLoop)
      && NfaRepL(rer, qm, r1, c, em + 3, e1)
      && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
      && NR.GetPcRE(c, e1 + 1) == Some(RB.Fork(em + 1, e1 + 3))
      && pc2 == e1 + 3;
  }

  // ===========================================================================
  // The bridge: compiler adherence (RegElk AST) ==> NfaRepL (translated regex)
  // ===========================================================================

  /** The annotation agreement, BOTH ways: `NUL.NonNullableL` on the translated
      regex holds exactly when the engine's `R.nullable` says `NonNullable`.
      `NUL.TransNonNullable` is only the forward half; the §2.5a bridge needs the
      converse to know that a body the engine did NOT annotate `NonNullable`
      translates to a body `NfaRepL`'s GENERIC arm accepts.

      The two definitions are constructor-for-constructor mirrors:
      `null_or(n1,n2) == NonNullable <==> n1 == NonNullable && n2 == NonNullable`
      (Disjunction: both) and `null_and(n1,n2) == NonNullable <==> n1 ==
      NonNullable || n2 == NonNullable` (Sequence: either); `Re_quant` is
      `CINullable` at `min == 0` and the body's nullability otherwise
      (Quantified: `min > 0 && NonNullableL(body)`); `Re_empty`/`Re_anchor`/
      `Re_lookaround` are never `NonNullable`, matching `false`. */
  lemma TransNullableAgree(re: R.regex)
    requires T.TransWf(re)
    ensures NUL.NonNullableL(T.Translate(re)) <==> R.nullable(re) == R.NonNullable
    decreases re
  {
    match re
    case Re_empty =>
    case Re_character(_) =>
    case Re_anchor(_) =>
    case Re_lookaround(_, _, _) =>
    case Re_alt(r1, r2) =>
      TransNullableAgree(r1);
      TransNullableAgree(r2);
    case Re_con(r1, r2) =>
      TransNullableAgree(r1);
      TransNullableAgree(r2);
    case Re_quant(nul, qid, q, r1) =>
      TransNullableAgree(r1);
    case Re_capture(cid, r1) =>
      TransNullableAgree(r1);
  }


  /** The bridge lemma: RegElk's own compiler-adherence predicate `NfaRepRE` over a
      RegElk AST `re`, combined with a well-formed translation and a correct `qm`,
      implies `NfaRepL` over `Translate(re)` — compiler correctness on the RegElk side
      transports to the Linden side. */
  /** `TransNfaRep` for the forced-copy chains: `NfaRepMinRE` over the RegElk
      body transports to `NfaRepMinL` over its translation. */
  lemma TransNfaRepMin(rer: LW.RegExpRecord, qm: QMap, k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.LookBehindFragmentRE(r1) && T.TransWf(r1) && !rer.ignoreCase
    requires QmapOk(r1, qm) && LmapOk(r1, qm)
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1))
    requires NR.NfaRepMinRE(k, qid, r1, c, pc1, pc2)
    ensures NfaRepMinL(rer, qm, k, T.Translate(r1), c, pc1, pc2)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, c, e1, pc2);
      TransNfaRep(rer, qm, r1, c, pc1 + 1, e1);
      TransNfaRepMin(rer, qm, k - 1, qid, r1, c, e1, pc2);
      assert (exists qd: int ::
           NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qd, false))
           && qd in qm.quants && qm.quants[qd] == L.DefGroups(T.Translate(r1)))
        && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 1, e1)
        && NfaRepMinL(rer, qm, k - 1, T.Translate(r1), c, e1, pc2);
    }
  }

  /** `TransNfaRep` for the optional-layer chains: `NfaRepOptRE` over the
      RegElk body transports to `NfaRepOptL` over its translation. */
  lemma TransNfaRepOpt(rer: LW.RegExpRecord, qm: QMap, k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.LookBehindFragmentRE(r1) && T.TransWf(r1) && !rer.ignoreCase
    requires QmapOk(r1, qm) && LmapOk(r1, qm)
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1))
    requires NR.NfaRepOptRE(k, greedy, qid, r1, c, pc1, pc2)
    ensures NfaRepOptL(rer, qm, k, greedy, T.Translate(r1), c, pc1, pc2)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
        && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, c, pc1 + 3, e1)
        && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pc2);
      TransNfaRep(rer, qm, r1, c, pc1 + 3, e1);
      TransNfaRepOpt(rer, qm, k - 1, greedy, qid, r1, c, e1 + 1, pc2);
      assert NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
        && (exists qd: int ::
              NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qd, false))
              && qd in qm.quants && qm.quants[qd] == L.DefGroups(T.Translate(r1)))
        && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
        && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 3, e1)
        && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
        && NfaRepOptL(rer, qm, k - 1, greedy, T.Translate(r1), c, e1 + 1, pc2);
    }
  }

  lemma TransNfaRep(rer: LW.RegExpRecord, qm: QMap, re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.LookBehindFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm) && LmapOk(re, qm)
    requires NR.NfaRepRE(re, c, pc1, pc2)
    ensures NfaRepL(rer, qm, T.Translate(re), c, pc1, pc2)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_anchor(a) =>
      assert NR.GetPcRE(c, pc1) == Some(RB.AnchorAssertion(a));
      assert T.Translate(re) == L.AnchorR(T.TrAnchor(a));
    case Re_character(ch) =>
      assert NR.GetPcRE(c, pc1) == Some(RB.Consume(T.ExpectationOf(ch)));
      forall x: char ensures RC.is_accepted(Some(x), T.ExpectationOf(ch)) <==> LC.CharMatch(rer, x, T.CharToCd(ch)) {
        T.CharSemAgree(rer, ch, x);
      }
      assert ExpectationMatches(rer, T.ExpectationOf(ch), T.CharToCd(ch));
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      TransNfaRep(rer, qm, r1, c, pc1 + 1, e1);
      TransNfaRep(rer, qm, r2, c, e1 + 1, pc2);
      assert NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
          && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 1, e1)
          && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
          && NfaRepL(rer, qm, T.Translate(r2), c, e1 + 1, pc2);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      TransNfaRep(rer, qm, r1, c, pc1, e1);
      TransNfaRep(rer, qm, r2, c, e1, pc2);
      assert NfaRepL(rer, qm, T.Translate(r1), c, pc1, e1) && NfaRepL(rer, qm, T.Translate(r2), c, e1, pc2);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pc1 + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2;
        TransNfaRep(rer, qm, r1, c, pc1 + 3, e1);
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, 0, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        assert NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
            && (exists qd: int ::
                  NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qd, false))
                  && qd in qm.quants && qm.quants[qd] == L.DefGroups(T.Translate(r1)))
            && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
            && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 3, e1)
            && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
            && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
            && pc2 == e1 + 2;
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        TransNfaRepMin(rer, qm, mn, qid, r1, c, pc1, em);
        TransNfaRepOpt(rer, qm, kx, q.greedy, qid, r1, c, em, pc2);
        assert T.TrDelta(q) == LN.NN(kx);
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.NN(kx), T.Translate(r1));
        NfaRepLQuantIntro(rer, qm, q.greedy, mn, kx, T.Translate(r1), c, pc1, em, pc2);
      } else if nul != R.NonNullable && !q.greedy {
        // the GENERIC scheme (§2.5a): transport the forced chain and the star
        // loop. `TransNullableAgree` is what turns the engine's "not annotated
        // NonNullable" into the `!NonNullableL` the GENERIC arm asks for.
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        TransNfaRepMin(rer, qm, mn, qid, r1, c, pc1, em);
        TransNfaRep(rer, qm, r1, c, em + 3, e1);
        TransNullableAgree(r1);
        assert !NUL.NonNullableL(T.Translate(r1));
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        NfaRepLGenIntro(rer, qm, q.greedy, mn, T.Translate(r1), c, pc1, em, e1, pc2, qid);
      } else if nul != R.NonNullable {
        // the CIN-GREEDY end-fork scheme (§2.5b): transport the forced chain
        // and the loop body; `NfaRepRECinInv` pins `nul == CINullable`, and
        // `TransCINullable` (through `TransWf`'s `nul == R.nullable(r1)`)
        // turns it into the `CINullableL` the CIN arm asks for.
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        TransNfaRepMin(rer, qm, mn - 1, qid, r1, c, pc1, em);
        TransNfaRep(rer, qm, r1, c, em + 3, e1);
        TransNullableAgree(r1);
        NUL.TransCINullable(r1);
        assert !NUL.NonNullableL(T.Translate(r1)) && NUL.CINullableL(T.Translate(r1));
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        NfaRepLCinIntro(rer, qm, q.greedy, mn, T.Translate(r1), c, pc1, em, e1, pc2, qid);
      } else {
        // the do-while: transport the forced chain and the guaranteed body,
        // and carry NonNullableL through the annotation agreement
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        TransNfaRepMin(rer, qm, mn - 1, qid, r1, c, pc1, em);
        TransNfaRep(rer, qm, r1, c, em + 1, e1);
        NUL.TransNonNullable(r1);
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        NfaRepLPlusIntro(rer, qm, q.greedy, mn, T.Translate(r1), c, pc1, em, e1, pc2, qid);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      TransNfaRep(rer, qm, r1, c, pc1 + 1, e1);
      assert T.Translate(re) == L.Group(cid as nat, T.Translate(r1));
      assert CP.start_reg((cid as nat) as int) == CP.start_reg(cid);
      assert CP.end_reg((cid as nat) as int) == CP.end_reg(cid);
      assert NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg((cid as nat) as int)))
          && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 1, e1)
          && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg((cid as nat) as int)))
          && pc2 == e1 + 1;
    case Re_lookaround(lid, la, r1) =>
      // one zero-width instruction; the `looks` row carries the erased link
      var lk := T.TrLookaround(la);
      assert T.Translate(re) == L.LookaroundR(lk, T.Translate(r1));
      assert PositiveL(lk) <==> (la.Lookahead? || la.Lookbehind?);
      assert lid in qm.looks && qm.looks[lid] == (lk, T.Translate(r1));
      assert NR.GetPcRE(c, pc1) == Some(if PositiveL(lk) then RB.CheckOracle(lid)
                                                         else RB.NegCheckOracle(lid));
  }

  // ===========================================================================
  // Lookaround-free regexes need no lookaround table
  // ===========================================================================

  /** A lookaround-free regex constrains no row of `qm.looks`, so `LmapOk`
      holds of any table — what lets the narrower fragments' entry points keep
      their signatures while the bridge gained its `LmapOk` precondition. */
  lemma LookFreeLmapOk(re: R.regex, qm: QMap)
    requires T.TransWf(re) && NR.LookFreeRE(re)
    ensures LmapOk(re, qm)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => LookFreeLmapOk(r1, qm); LookFreeLmapOk(r2, qm);
    case Re_con(r1, r2) => LookFreeLmapOk(r1, qm); LookFreeLmapOk(r2, qm);
    case Re_quant(_, _, _, r1) => LookFreeLmapOk(r1, qm);
    case Re_capture(_, r1) => LookFreeLmapOk(r1, qm);
    case _ =>
  }

  /** The plus fragment admits no lookaround node at all. */
  lemma PlusFragmentLookFree(re: R.regex)
    requires NR.PlusFragmentRE(re)
    ensures NR.LookFreeRE(re)
    decreases re
  {
    match re
    case Re_alt(r1, r2) => PlusFragmentLookFree(r1); PlusFragmentLookFree(r2);
    case Re_con(r1, r2) => PlusFragmentLookFree(r1); PlusFragmentLookFree(r2);
    case Re_quant(_, _, _, r1) => PlusFragmentLookFree(r1);
    case Re_capture(_, r1) => PlusFragmentLookFree(r1);
    case _ =>
  }

  /** `LmapOk` for free on the plus fragment: no lookarounds, no rows. */
  lemma PlusFragmentLmapOk(re: R.regex, qm: QMap)
    requires T.TransWf(re) && NR.PlusFragmentRE(re)
    ensures LmapOk(re, qm)
  {
    PlusFragmentLookFree(re);
    LookFreeLmapOk(re, qm);
  }

  // ===========================================================================
  // Label monotonicity for NfaRepL (mirror of NfaRepIncrRE)
  // ===========================================================================

  /** `NfaRepIncrL` for forced-copy chains. */
  lemma NfaRepIncrMinL(rer: LW.RegExpRecord, qm: QMap, k: nat, r1: L.Regex, c: RB.code, start: nat, endl: nat)
    requires NfaRepMinL(rer, qm, k, r1, c, start, endl)
    ensures start <= endl
    decreases r1, k + 2
  {
    if k > 0 {
      var e1: nat :| (exists qid: int ::
            NR.GetPcRE(c, start) == Some(RB.SetQuantToClock(qid, false))
            && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && NfaRepL(rer, qm, r1, c, start + 1, e1)
        && NfaRepMinL(rer, qm, k - 1, r1, c, e1, endl);
      NfaRepIncrL(rer, qm, r1, c, start + 1, e1);
      NfaRepIncrMinL(rer, qm, k - 1, r1, c, e1, endl);
    }
  }

  /** `NfaRepIncrL` for optional-layer chains. */
  lemma NfaRepIncrOptL(rer: LW.RegExpRecord, qm: QMap, k: nat, greedy: bool, r1: L.Regex, c: RB.code, start: nat, endl: nat)
    requires NfaRepOptL(rer, qm, k, greedy, r1, c, start, endl)
    ensures start <= endl
    decreases r1, k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(c, start) == Some(if greedy then RB.Fork(start + 1, endl) else RB.Fork(endl, start + 1))
        && (exists qid: int ::
              NR.GetPcRE(c, start + 1) == Some(RB.SetQuantToClock(qid, false))
              && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
        && NR.GetPcRE(c, start + 2) == Some(RB.BeginLoop)
        && NfaRepL(rer, qm, r1, c, start + 3, e1)
        && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
        && NfaRepOptL(rer, qm, k - 1, greedy, r1, c, e1 + 1, endl);
      NfaRepIncrL(rer, qm, r1, c, start + 3, e1);
      NfaRepIncrOptL(rer, qm, k - 1, greedy, r1, c, e1 + 1, endl);
    }
  }

  /** Labels only increase through `NfaRepL` blocks — the Linden-side mirror of
      `NfaRepIncrRE`, needed wherever a fork's arms must be shown forward. */
  lemma NfaRepIncrL(rer: LW.RegExpRecord, qm: QMap, r: L.Regex, c: RB.code, start: nat, endl: nat)
    requires NfaRepL(rer, qm, r, c, start, endl)
    ensures start <= endl
    decreases r, 1
  {
    match r
    case Epsilon =>
    case Character(_) =>
    case AnchorR(_) =>
    case Disjunction(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, start) == Some(RB.Fork(start + 1, e1 + 1))
        && NfaRepL(rer, qm, r1, c, start + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(endl))
        && NfaRepL(rer, qm, r2, c, e1 + 1, endl);
      NfaRepIncrL(rer, qm, r1, c, start + 1, e1);
      NfaRepIncrL(rer, qm, r2, c, e1 + 1, endl);
    case Sequence(r1, r2) =>
      var e1: nat :| NfaRepL(rer, qm, r1, c, start, e1) && NfaRepL(rer, qm, r2, c, e1, endl);
      NfaRepIncrL(rer, qm, r1, c, start, e1);
      NfaRepIncrL(rer, qm, r2, c, e1, endl);
    case Quantified(greedy, min, delta, r1) =>
      if min == 0 && delta == LN.Inf {
        if exists e1: nat ::
             NR.GetPcRE(c, start) == Some(if greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
             && (exists qid: int ::
                   NR.GetPcRE(c, start + 1) == Some(RB.SetQuantToClock(qid, false))
                   && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
             && NR.GetPcRE(c, start + 2) == Some(RB.BeginLoop)
             && NfaRepL(rer, qm, r1, c, start + 3, e1)
             && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
             && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(start))
             && endl == e1 + 2 {
          var e1: nat :| NR.GetPcRE(c, start) == Some(if greedy then RB.Fork(start + 1, e1 + 2) else RB.Fork(e1 + 2, start + 1))
            && NfaRepL(rer, qm, r1, c, start + 3, e1)
            && endl == e1 + 2;
          NfaRepIncrL(rer, qm, r1, c, start + 3, e1);
        } else {
          // the loop view: endl == start + 1
        }
      } else {
        match delta {
          case Inf =>
            if NUL.NonNullableL(r1) {
              // the do-while
              var em: nat, e1: nat :|
                NfaRepMinL(rer, qm, min - 1, r1, c, start, em)
                && (exists qid: int ::
                      NR.GetPcRE(c, em) == Some(RB.SetQuantToClock(qid, false))
                      && qid in qm.quants && qm.quants[qid] == L.DefGroups(r1))
                && NfaRepL(rer, qm, r1, c, em + 1, e1)
                && NR.GetPcRE(c, e1) == Some(if greedy then RB.Fork(em, e1 + 1) else RB.Fork(e1 + 1, em))
                && endl == e1 + 1;
              NfaRepIncrMinL(rer, qm, min - 1, r1, c, start, em);
              NfaRepIncrL(rer, qm, r1, c, em + 1, e1);
            } else if !greedy {
              // the GENERIC scheme (§2.5a): min forced copies, then the star loop
              var em, e1 := NfaRepLGenInv(rer, qm, greedy, min, r1, c, start, endl);
              NfaRepIncrMinL(rer, qm, min, r1, c, start, em);
              NfaRepIncrL(rer, qm, r1, c, em + 3, e1);
            } else {
              // the CIN-GREEDY end-fork scheme (§2.5b)
              var em, e1 := NfaRepLCinInv(rer, qm, greedy, min, r1, c, start, endl);
              NfaRepIncrMinL(rer, qm, min - 1, r1, c, start, em);
              NfaRepIncrL(rer, qm, r1, c, em + 3, e1);
            }
          case NN(kx) =>
            var em: nat :| NfaRepMinL(rer, qm, min, r1, c, start, em)
              && NfaRepOptL(rer, qm, kx, greedy, r1, c, em, endl);
            NfaRepIncrMinL(rer, qm, min, r1, c, start, em);
            NfaRepIncrOptL(rer, qm, kx, greedy, r1, c, em, endl);
        }
      }
    case Group(gid, r1) =>
      var e1: nat :| NR.GetPcRE(c, start) == Some(RB.SetRegisterToCP(CP.start_reg(gid as int)))
        && NfaRepL(rer, qm, r1, c, start + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
        && endl == e1 + 1;
      NfaRepIncrL(rer, qm, r1, c, start + 1, e1);
    case LookaroundR(_, _) =>
    case Backreference(_) =>
  }

  // ===========================================================================
  // Action / actions representation (port of Linden ActionRep / ActionsRep)
  // ===========================================================================

  /** A single continuation `Action` (`Areg`/`Acheck`/`Aclose`) represented at bytecode
      positions `pc1`..`pc2`: `Areg` delegates to `NfaRepL`, `Acheck` is RegElk's
      fall-through `EndLoop`, and `Aclose` is the `SetRegisterToCP` that closes a
      capture group. */
  ghost predicate ActionRepL(rer: LW.RegExpRecord, qm: QMap, a: LS.Action, c: RB.code, pc1: nat, pc2: nat) {
    match a
    case Areg(r) => NfaRepL(rer, qm, r, c, pc1, pc2)
    // RegElk's EndLoop falls through; the explicit back-Jmp that follows it in
    // star blocks is absorbed by ActionsRepL's jump_bc rule.
    case Acheck(_) =>
      (pc2 == pc1 + 1 && NR.GetPcRE(c, pc1) == Some(RB.EndLoop))
      // ... or zero-width at a backward fork: the check dissolves into the
      // do-while's decision point, consumed with the Choice by tr_plus
      || (pc2 == pc1 && BackForkAt(c, pc1))
    case Aclose(gid) => pc2 == pc1 + 1 && NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.end_reg(gid as int)))
  }

  /** An action-stack continuation `acts` represented starting at `pc` (port of Linden
      `NFA.dfy`'s `ActionsRep`): the empty stack ⟷ `Accept` (`empty_bc`), `cons` ⟷ one
      `ActionRepL` step followed by the rest (`cons_bc`), plus a `jump_bc` rule
      absorbing RegElk's explicit back-`Jmp` at star boundaries (where Linden instead
      uses an implicit `EndLoop(l)`). */
  least predicate ActionsRepL(rer: LW.RegExpRecord, qm: QMap, acts: LS.Actions, c: RB.code, pc: nat) {
    (|acts| == 0 && NR.GetPcRE(c, pc) == Some(RB.Accept))                                       // empty_bc
    || (|acts| > 0 && exists pcmid: nat ::
          ActionRepL(rer, qm, acts[0], c, pc, pcmid) && ActionsRepL(rer, qm, acts[1..], c, pcmid)) // cons_bc
    || (exists pcstart: nat ::
          NR.GetPcRE(c, pc) == Some(RB.Jmp(pcstart)) && ActionsRepL(rer, qm, acts, c, pcstart))    // jump_bc
  }

  // intro helpers (ports of Linden's cons/empty reasoning patterns)
  /** Introduction rule: representing the head action then the tail continuation
      suffices to conclude `ActionsRepL` for the whole `[a] + acts` stack. */
  lemma ActionsRepLCons(rer: LW.RegExpRecord, qm: QMap, a: LS.Action, acts: LS.Actions, c: RB.code, pc: nat, pcmid: nat)
    requires ActionRepL(rer, qm, a, c, pc, pcmid)
    requires ActionsRepL(rer, qm, acts, c, pcmid)
    ensures ActionsRepL(rer, qm, [a] + acts, c, pc)
  {
    var na := [a] + acts;
    assert na[0] == a && na[1..] == acts;
  }

  /** Introduction rule: a `Jmp` to an already-represented continuation is itself a
      representation of that continuation (the `jump_bc` case of `ActionsRepL`). */
  lemma ActionsRepLJmp(rer: LW.RegExpRecord, qm: QMap, acts: LS.Actions, c: RB.code, pc: nat, pcstart: nat)
    requires NR.GetPcRE(c, pc) == Some(RB.Jmp(pcstart))
    requires ActionsRepL(rer, qm, acts, c, pcstart)
    ensures ActionsRepL(rer, qm, acts, c, pc)
  {}

  // The top-level continuation fact: for a fragment regex re, the compiled
  // bytecode represents the single-action continuation [Areg(Translate(re))]
  // at pc 0 (with Accept as the empty continuation at the end label).
  /** Top-level continuation fact: for a star-fragment regex `re`,
      `CP.compile_to_bytecode(re)` represents the single-action continuation
      `[Areg(Translate(re))]` at `pc` 0 — the entry point later simulation lemmas
      build on. */
  /** `CompileToBytecodeActionsRep` widened to the plus fragment. */
  /** The whole compiled program represents the single spec action, on the
      lookbehind fragment -- the widest gate the table reasoning supports. The
      caller supplies `LmapOk` (the plus-fragment corollary below derives it
      from look-freeness instead). */
  lemma CompileToBytecodeActionsRepLookBehind(rer: LW.RegExpRecord, qm: QMap, re: R.regex)
    requires NR.LookBehindFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm) && LmapOk(re, qm)
    ensures var code := CP.compile_to_bytecode(re);
      ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
  {
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    NR.CompileToBytecodeRepLookBehind(re);
    TransNfaRep(rer, qm, re, code, 0, next as nat);
    assert ActionsRepL(rer, qm, [], code, next as nat);
    var single := [LS.Areg(T.Translate(re))];
    assert ActionRepL(rer, qm, single[0], code, 0, next as nat);
    assert single[1..] == [];
    assert ActionsRepL(rer, qm, single, code, 0);
  }

  // =========================================================================
  // L4 depth-k (ADDITIVE): TransNfaRep{,Min,Opt}Nested -- the NfaRepRE ->
  // ActionsRepL bridge widened from LookBehindFragmentRE to NestedFragmentRE.
  // The lookaround case maps a single zero-width gate (no body recursion), so
  // the depth-1 proof ports verbatim under the wider fragment predicate.
  // =========================================================================

  /** `TransNfaRepNested` for the forced-copy chains: `NfaRepMinRE` over the RegElk
      body transports to `NfaRepMinL` over its translation. */
  lemma TransNfaRepMinNested(rer: LW.RegExpRecord, qm: QMap, k: nat, qid: R.quantid, r1: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.NestedFragmentRE(r1) && T.TransWf(r1) && !rer.ignoreCase
    requires QmapOk(r1, qm) && LmapOk(r1, qm)
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1))
    requires NR.NfaRepMinRE(k, qid, r1, c, pc1, pc2)
    ensures NfaRepMinL(rer, qm, k, T.Translate(r1), c, pc1, pc2)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qid, false))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.NfaRepMinRE(k - 1, qid, r1, c, e1, pc2);
      TransNfaRepNested(rer, qm, r1, c, pc1 + 1, e1);
      TransNfaRepMinNested(rer, qm, k - 1, qid, r1, c, e1, pc2);
      assert (exists qd: int ::
           NR.GetPcRE(c, pc1) == Some(RB.SetQuantToClock(qd, false))
           && qd in qm.quants && qm.quants[qd] == L.DefGroups(T.Translate(r1)))
        && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 1, e1)
        && NfaRepMinL(rer, qm, k - 1, T.Translate(r1), c, e1, pc2);
    }
  }

  /** `TransNfaRepNested` for the optional-layer chains: `NfaRepOptRE` over the
      RegElk body transports to `NfaRepOptL` over its translation. */
  lemma TransNfaRepOptNested(rer: LW.RegExpRecord, qm: QMap, k: nat, greedy: bool, qid: R.quantid, r1: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.NestedFragmentRE(r1) && T.TransWf(r1) && !rer.ignoreCase
    requires QmapOk(r1, qm) && LmapOk(r1, qm)
    requires qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1))
    requires NR.NfaRepOptRE(k, greedy, qid, r1, c, pc1, pc2)
    ensures NfaRepOptL(rer, qm, k, greedy, T.Translate(r1), c, pc1, pc2)
    decreases CP.rsize(r1), k + 2
  {
    if k > 0 {
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
        && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
        && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
        && NR.NfaRepRE(r1, c, pc1 + 3, e1)
        && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
        && NR.NfaRepOptRE(k - 1, greedy, qid, r1, c, e1 + 1, pc2);
      TransNfaRepNested(rer, qm, r1, c, pc1 + 3, e1);
      TransNfaRepOptNested(rer, qm, k - 1, greedy, qid, r1, c, e1 + 1, pc2);
      assert NR.GetPcRE(c, pc1) == Some(if greedy then RB.Fork(pc1 + 1, pc2) else RB.Fork(pc2, pc1 + 1))
        && (exists qd: int ::
              NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qd, false))
              && qd in qm.quants && qm.quants[qd] == L.DefGroups(T.Translate(r1)))
        && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
        && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 3, e1)
        && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
        && NfaRepOptL(rer, qm, k - 1, greedy, T.Translate(r1), c, e1 + 1, pc2);
    }
  }

  lemma TransNfaRepNested(rer: LW.RegExpRecord, qm: QMap, re: R.regex, c: RB.code, pc1: nat, pc2: nat)
    requires NR.NestedFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm) && LmapOk(re, qm)
    requires NR.NfaRepRE(re, c, pc1, pc2)
    ensures NfaRepL(rer, qm, T.Translate(re), c, pc1, pc2)
    decreases CP.rsize(re), 1
  {
    match re
    case Re_empty =>
    case Re_anchor(a) =>
      assert NR.GetPcRE(c, pc1) == Some(RB.AnchorAssertion(a));
      assert T.Translate(re) == L.AnchorR(T.TrAnchor(a));
    case Re_character(ch) =>
      assert NR.GetPcRE(c, pc1) == Some(RB.Consume(T.ExpectationOf(ch)));
      forall x: char ensures RC.is_accepted(Some(x), T.ExpectationOf(ch)) <==> LC.CharMatch(rer, x, T.CharToCd(ch)) {
        T.CharSemAgree(rer, ch, x);
      }
      assert ExpectationMatches(rer, T.ExpectationOf(ch), T.CharToCd(ch));
    case Re_alt(r1, r2) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
        && NR.NfaRepRE(r2, c, e1 + 1, pc2);
      TransNfaRepNested(rer, qm, r1, c, pc1 + 1, e1);
      TransNfaRepNested(rer, qm, r2, c, e1 + 1, pc2);
      assert NR.GetPcRE(c, pc1) == Some(RB.Fork(pc1 + 1, e1 + 1))
          && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 1, e1)
          && NR.GetPcRE(c, e1) == Some(RB.Jmp(pc2))
          && NfaRepL(rer, qm, T.Translate(r2), c, e1 + 1, pc2);
    case Re_con(r1, r2) =>
      var e1: nat :| NR.NfaRepRE(r1, c, pc1, e1) && NR.NfaRepRE(r2, c, e1, pc2);
      TransNfaRepNested(rer, qm, r1, c, pc1, e1);
      TransNfaRepNested(rer, qm, r2, c, e1, pc2);
      assert NfaRepL(rer, qm, T.Translate(r1), c, pc1, e1) && NfaRepL(rer, qm, T.Translate(r2), c, e1, pc2);
    case Re_quant(nul, qid, q, r1) =>
      if q.min == 0 && q.max == None {
        var e1: nat :| NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
          && NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qid, false))
          && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
          && NR.NfaRepRE(r1, c, pc1 + 3, e1)
          && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
          && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
          && pc2 == e1 + 2;
        TransNfaRepNested(rer, qm, r1, c, pc1 + 3, e1);
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, 0, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        assert NR.GetPcRE(c, pc1) == Some(if q.greedy then RB.Fork(pc1 + 1, e1 + 2) else RB.Fork(e1 + 2, pc1 + 1))
            && (exists qd: int ::
                  NR.GetPcRE(c, pc1 + 1) == Some(RB.SetQuantToClock(qd, false))
                  && qd in qm.quants && qm.quants[qd] == L.DefGroups(T.Translate(r1)))
            && NR.GetPcRE(c, pc1 + 2) == Some(RB.BeginLoop)
            && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 3, e1)
            && NR.GetPcRE(c, e1) == Some(RB.EndLoop)
            && NR.GetPcRE(c, e1 + 1) == Some(RB.Jmp(pc1))
            && pc2 == e1 + 2;
      } else if q.max.Some? {
        var em := NR.NfaRepREQuantInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        var kx := (q.max.value - q.min) as nat;
        TransNfaRepMinNested(rer, qm, mn, qid, r1, c, pc1, em);
        TransNfaRepOptNested(rer, qm, kx, q.greedy, qid, r1, c, em, pc2);
        assert T.TrDelta(q) == LN.NN(kx);
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.NN(kx), T.Translate(r1));
        NfaRepLQuantIntro(rer, qm, q.greedy, mn, kx, T.Translate(r1), c, pc1, em, pc2);
      } else if nul != R.NonNullable && !q.greedy {
        // the GENERIC scheme (§2.5a): transport the forced chain and the star
        // loop. `TransNullableAgree` is what turns the engine's "not annotated
        // NonNullable" into the `!NonNullableL` the GENERIC arm asks for.
        var em, e1 := NR.NfaRepREGenInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        TransNfaRepMinNested(rer, qm, mn, qid, r1, c, pc1, em);
        TransNfaRepNested(rer, qm, r1, c, em + 3, e1);
        TransNullableAgree(r1);
        assert !NUL.NonNullableL(T.Translate(r1));
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        NfaRepLGenIntro(rer, qm, q.greedy, mn, T.Translate(r1), c, pc1, em, e1, pc2, qid);
      } else if nul != R.NonNullable {
        // the CIN-GREEDY end-fork scheme (§2.5b): transport the forced chain
        // and the loop body (mirror of the depth-1 bridge's CIN branch).
        var em, e1 := NR.NfaRepRECinInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        TransNfaRepMinNested(rer, qm, mn - 1, qid, r1, c, pc1, em);
        TransNfaRepNested(rer, qm, r1, c, em + 3, e1);
        TransNullableAgree(r1);
        NUL.TransCINullable(r1);
        assert !NUL.NonNullableL(T.Translate(r1)) && NUL.CINullableL(T.Translate(r1));
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        NfaRepLCinIntro(rer, qm, q.greedy, mn, T.Translate(r1), c, pc1, em, e1, pc2, qid);
      } else {
        // the do-while: transport the forced chain and the guaranteed body,
        // and carry NonNullableL through the annotation agreement
        var em, e1 := NR.NfaRepREPlusInv(nul, qid, q, r1, c, pc1, pc2);
        var mn := q.min as nat;
        TransNfaRepMinNested(rer, qm, mn - 1, qid, r1, c, pc1, em);
        TransNfaRepNested(rer, qm, r1, c, em + 1, e1);
        NUL.TransNonNullable(r1);
        assert T.TrDelta(q) == LN.Inf;
        assert T.Translate(re) == L.Quantified(q.greedy, mn, LN.Inf, T.Translate(r1));
        assert qid in qm.quants && qm.quants[qid] == L.DefGroups(T.Translate(r1));
        NfaRepLPlusIntro(rer, qm, q.greedy, mn, T.Translate(r1), c, pc1, em, e1, pc2, qid);
      }
    case Re_capture(cid, r1) =>
      var e1: nat :| NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg(cid)))
        && NR.NfaRepRE(r1, c, pc1 + 1, e1)
        && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg(cid)))
        && pc2 == e1 + 1;
      TransNfaRepNested(rer, qm, r1, c, pc1 + 1, e1);
      assert T.Translate(re) == L.Group(cid as nat, T.Translate(r1));
      assert CP.start_reg((cid as nat) as int) == CP.start_reg(cid);
      assert CP.end_reg((cid as nat) as int) == CP.end_reg(cid);
      assert NR.GetPcRE(c, pc1) == Some(RB.SetRegisterToCP(CP.start_reg((cid as nat) as int)))
          && NfaRepL(rer, qm, T.Translate(r1), c, pc1 + 1, e1)
          && NR.GetPcRE(c, e1) == Some(RB.SetRegisterToCP(CP.end_reg((cid as nat) as int)))
          && pc2 == e1 + 1;
    case Re_lookaround(lid, la, r1) =>
      // one zero-width instruction; the `looks` row carries the erased link
      var lk := T.TrLookaround(la);
      assert T.Translate(re) == L.LookaroundR(lk, T.Translate(r1));
      assert PositiveL(lk) <==> (la.Lookahead? || la.Lookbehind?);
      assert lid in qm.looks && qm.looks[lid] == (lk, T.Translate(r1));
      assert NR.GetPcRE(c, pc1) == Some(if PositiveL(lk) then RB.CheckOracle(lid)
                                                         else RB.NegCheckOracle(lid));
  }

  /** L4 depth-k (ADDITIVE): the nested-fragment analogue of
      `CompileToBytecodeActionsRepLookBehind`. The whole compiled program
      represents the single spec action for a NESTED-fragment `re`, routed
      through `CompileToBytecodeRepNested` + `TransNfaRepNested`. */
  lemma CompileToBytecodeActionsRepNested(rer: LW.RegExpRecord, qm: QMap, re: R.regex)
    requires NR.NestedFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm) && LmapOk(re, qm)
    ensures var code := CP.compile_to_bytecode(re);
      ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
  {
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    NR.CompileToBytecodeRepNested(re);
    TransNfaRepNested(rer, qm, re, code, 0, next as nat);
    assert ActionsRepL(rer, qm, [], code, next as nat);
    var single := [LS.Areg(T.Translate(re))];
    assert ActionRepL(rer, qm, single[0], code, 0, next as nat);
    assert single[1..] == [];
    assert ActionsRepL(rer, qm, single, code, 0);
  }


  lemma CompileToBytecodeActionsRepPlus(rer: LW.RegExpRecord, qm: QMap, re: R.regex)
    requires NR.PlusFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm)
    ensures var code := CP.compile_to_bytecode(re);
      ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
  {
    NR.PlusIsLookBehindFragmentRE(re);
    PlusFragmentLmapOk(re, qm);
    CompileToBytecodeActionsRepLookBehind(rer, qm, re);
  }

  /** `CompileToBytecodeActionsRepPlus` restricted to the quantifier
      fragment. */
  lemma CompileToBytecodeActionsRepQuant(rer: LW.RegExpRecord, qm: QMap, re: R.regex)
    requires NR.QuantFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm)
    ensures var code := CP.compile_to_bytecode(re);
      ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
  {
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    NR.QuantIsPlusFragmentRE(re);
    NR.CompileToBytecodeRepQuant(re);
    NR.PlusIsLookBehindFragmentRE(re);
    PlusFragmentLmapOk(re, qm);
    TransNfaRep(rer, qm, re, code, 0, next as nat);
    assert ActionsRepL(rer, qm, [], code, next as nat);
    var single := [LS.Areg(T.Translate(re))];
    assert ActionRepL(rer, qm, single[0], code, 0, next as nat);
    assert single[1..] == [];
    assert ActionsRepL(rer, qm, single, code, 0);
  }

  lemma CompileToBytecodeActionsRep(rer: LW.RegExpRecord, qm: QMap, re: R.regex)
    requires NR.AnchorFragmentRE(re) && T.TransWf(re) && !rer.ignoreCase
    requires QmapOk(re, qm)
    ensures var code := CP.compile_to_bytecode(re);
      ActionsRepL(rer, qm, [LS.Areg(T.Translate(re))], code, 0)
  {
    var code := CP.compile_to_bytecode(re);
    var next := CP.compile(re, 0, CP.Progress).1;
    NR.AnchorIsQuantFragmentRE(re);
    NR.QuantIsPlusFragmentRE(re);
    NR.CompileToBytecodeRepAnchor(re);
    NR.PlusIsLookBehindFragmentRE(re);
    PlusFragmentLmapOk(re, qm);
    TransNfaRep(rer, qm, re, code, 0, next as nat);
    assert ActionsRepL(rer, qm, [], code, next as nat);
    var single := [LS.Areg(T.Translate(re))];
    assert ActionRepL(rer, qm, single[0], code, 0, next as nat);
    assert single[1..] == [];
    assert ActionsRepL(rer, qm, single, code, 0);
  }
}
