/* ==========================================================================
   Mirror.dfy — the string-reversal isomorphism (L2 groundwork)

   A BACKWARD run of bytecode `c` over `str` is isomorphic to a FORWARD run
   of `c` over `Reverse(str)` under the position mirror `cp |-> |str| - cp`,
   provided `BeginInput`/`EndInput` are swapped in `c`.

   The point of this file is to buy backward execution WITHOUT re-proving the
   forward reachability/simulation layers with flipped arithmetic. See
   L2_INVESTIGATION.md for why this route was chosen over parameterizing the
   ~1080-line `OracleReach` family by direction.

   STATUS: the isomorphism is PROVEN, end to end -- see `FFindMatchMirror`.
   A Backward run of `c` over `str` equals a Forward run of
   `SwapAnchorsCode(c)` over `Reverse(str)`, with every recorded position
   (the cursor, the registers, the oracle columns) reflected through
   `cp |-> |str| - cp`.

   Layers: (1) context correspondence + anchor swap; (2) the epsilon phase
   with `cp` fixed; (3) the oracle-view mirror; (3b) the cdn table; (4) the
   register/thread/state mirror; (5) the epsilon phase through the full
   mirror; (6) FConsume and the FFindMatch induction.

   NOT yet done: applying it. The payoff is that the forward-only
   reachability layer (`OracleReach`, ~1080 lines) and the forward-only
   simulation (`PikeSimRE`, `requires dir == Forward`) become usable for
   backward runs by transport, rather than being re-proved with flipped
   arithmetic. `FBuildLids` runs a lookAHEAD's oracle build Backward, so
   that is where this plugs in first.
   ========================================================================== */
include "PikeSimRE.dfy"
include "OracleReach.dfy"

module LindenElkMirror {
  import opened Std.Wrappers
  import R = RegElkRegex
  import RB = Bytecode
  import AI = ArrayInterp
  import LAnc = Anchors
  import LC = Chars
  import AReg = Array_Regs
  import LOr = Oracle
  import LCdn = Cdn
  import RC = Charclasses
  import OS = LindenElkOracleSweep
  import ORc = LindenElkOracleReach

  // ==========================================================================
  // The position mirror
  // ==========================================================================

  /** Reflecting a position through the middle of the string: a Backward run
      sitting at `cp` in `str` corresponds to a Forward run sitting at
      `Mirror(cp, |str|)` in `Reverse(str)`. An involution on `[0, n]`. */
  function Mirror(cp: int, n: int): int { n - cp }

  lemma MirrorInvolution(cp: int, n: int)
    ensures Mirror(Mirror(cp, n), n) == cp
  {}

  /** `Reverse` reads a string back to front: index `k` of the reversal is
      index `|s| - 1 - k` of the original. */
  lemma ReverseIndex<T>(s: seq<T>, k: int)
    requires 0 <= k < |s|
    ensures |LC.Reverse(s)| == |s|
    ensures LC.Reverse(s)[k] == s[|s| - 1 - k]
    decreases |s|
  {
    ReverseLen(s);
    if |s| > 0 {
      ReverseLen(s[1..]);
      if k < |s| - 1 {
        ReverseIndex(s[1..], k);
        assert LC.Reverse(s)[k] == LC.Reverse(s[1..])[k];
      }
    }
  }

  lemma ReverseLen<T>(s: seq<T>)
    ensures |LC.Reverse(s)| == |s|
    decreases |s|
  { if |s| > 0 { ReverseLen(s[1..]); } }

  /** Reading a character through the mirror: the character a Backward run
      finds at `cp` is the one a Forward run finds at `Mirror(cp, |str|)` of
      the reversed string, and vice versa. The two `get_char` facts that make
      the context correspondence below work out. */
  lemma GetCharMirror(str: string, cp: int)
    ensures AI.get_char(str, cp) == AI.get_char(LC.Reverse(str), Mirror(cp, |str|) - 1)
    ensures AI.get_char(str, cp - 1) == AI.get_char(LC.Reverse(str), Mirror(cp, |str|))
  {
    ReverseLen(str);
    var n := |str|;
    if 0 <= cp < n {
      ReverseIndex(str, n - cp - 1);
      assert LC.Reverse(str)[n - cp - 1] == str[cp];
    }
    if 0 <= cp - 1 < n {
      ReverseIndex(str, n - cp);
      assert LC.Reverse(str)[n - cp] == str[cp - 1];
    }
  }

  // ==========================================================================
  // The context correspondence
  // ==========================================================================

  /** THE foundational fact: a Backward run's character window at `cp` over
      `str` is LITERALLY the same window a Forward run sees at `Mirror(cp)`
      over `Reverse(str)`.

      This is not a coincidence of the mirror -- `cp_context` already swaps
      `prevchar`/`nextchar` for `Backward` (Interpreter.dfy), which is exactly
      the swap that reversing the string undoes. */
  lemma CpContextMirror(str: string, cp: int)
    ensures AI.cp_context(cp, str, LAnc.Backward)
         == AI.cp_context(Mirror(cp, |str|), LC.Reverse(str), LAnc.Forward)
  {
    GetCharMirror(str, cp);
  }

  // ==========================================================================
  // The anchor swap
  // ==========================================================================

  /** `BeginInput <-> EndInput`; the boundary anchors are direction-blind.
      Reversing the string swaps which end is which, so a program run
      backward must have its input anchors swapped to run forward. */
  function SwapAnchor(a: R.anchor): R.anchor {
    match a
    case BeginInput => R.EndInput
    case EndInput => R.BeginInput
    case WordBoundary => R.WordBoundary
    case NonWordBoundary => R.NonWordBoundary
  }

  lemma SwapAnchorInvolution(a: R.anchor)
    ensures SwapAnchor(SwapAnchor(a)) == a
  {}

  /** The anchor half of the isomorphism, on a FIXED context: asking anchor
      `a` of a Backward run is asking `SwapAnchor(a)` of a Forward run.

      Together with `CpContextMirror` (which says the contexts ARE the same
      pair) this is what lets a backward program be replayed forward. */
  lemma IsSatisfiedMirror(a: R.anchor, ctx: LAnc.char_context)
    ensures LAnc.is_satisfied(a, ctx, LAnc.Backward)
        <==> LAnc.is_satisfied(SwapAnchor(a), ctx, LAnc.Forward)
  {}

  /** The two halves combined, at a position: the assertion a Backward run
      makes at `cp` over `str` holds exactly when the swapped assertion holds
      for the Forward run at the mirrored position over the reversed string. */
  lemma AnchorAtMirror(a: R.anchor, str: string, cp: int)
    ensures LAnc.is_satisfied(a, AI.cp_context(cp, str, LAnc.Backward), LAnc.Backward)
        <==> LAnc.is_satisfied(SwapAnchor(a),
                               AI.cp_context(Mirror(cp, |str|), LC.Reverse(str), LAnc.Forward),
                               LAnc.Forward)
  {
    CpContextMirror(str, cp);
    IsSatisfiedMirror(a, AI.cp_context(cp, str, LAnc.Backward));
  }

  // ==========================================================================
  // The bytecode transform
  // ==========================================================================

  /** `c` with every input anchor swapped; every other instruction is left
      alone, so the program's SHAPE -- and therefore the Pike VM's thread
      priority order -- is untouched. That invariance is the reason this
      route can also serve the capture layer, where priority decides the
      answer. */
  function SwapAnchorsCode(c: RB.code): RB.code
    ensures |SwapAnchorsCode(c)| == |c|
  {
    seq(|c|, i requires 0 <= i < |c| =>
      match c[i]
      case AnchorAssertion(a) => RB.AnchorAssertion(SwapAnchor(a))
      case instr => instr)
  }

  lemma SwapAnchorsCodeLen(c: RB.code)
    ensures |SwapAnchorsCode(c)| == |c|
  {}

  lemma SwapAnchorsCodeInvolution(c: RB.code)
    ensures SwapAnchorsCode(SwapAnchorsCode(c)) == c
  {
    forall i | 0 <= i < |c| ensures SwapAnchorsCode(SwapAnchorsCode(c))[i] == c[i] {
      if c[i].AnchorAssertion? { SwapAnchorInvolution(c[i].aa); }
    }
  }

  /** `get_instr` through the transform, total in `pc` (out of range both
      read `Fail`). This is what a caller needs to know that the swapped
      program takes the SAME branch at a non-anchor instruction. */
  lemma GetInstrSwap(c: RB.code, pc: int)
    ensures !RB.get_instr(c, pc).AnchorAssertion? ==>
              RB.get_instr(SwapAnchorsCode(c), pc) == RB.get_instr(c, pc)
    ensures RB.get_instr(c, pc).AnchorAssertion? ==>
              RB.get_instr(SwapAnchorsCode(c), pc)
                == RB.AnchorAssertion(SwapAnchor(RB.get_instr(c, pc).aa))
  {}

  /** Pointwise: outside anchors the two programs are the same instruction. */
  predicate SwapAnchorsCodeNonAnchorAt(c: RB.code, pc: nat)
    requires pc < |c|
  {
    if c[pc].AnchorAssertion? then SwapAnchorsCode(c)[pc] == RB.AnchorAssertion(SwapAnchor(c[pc].aa))
    else SwapAnchorsCode(c)[pc] == c[pc]
  }

  /** The transform touches nothing but anchors -- the fact every downstream
      frame/rep lemma will need. */
  lemma SwapAnchorsCodeNonAnchor(c: RB.code, pc: nat)
    requires pc < |c|
    ensures !c[pc].AnchorAssertion? ==> SwapAnchorsCode(c)[pc] == c[pc]
    ensures c[pc].AnchorAssertion? ==>
              SwapAnchorsCode(c)[pc] == RB.AnchorAssertion(SwapAnchor(c[pc].aa))
  {}

  // ==========================================================================
  // Layer 2: the epsilon phase needs NO mirroring at all
  // ==========================================================================

  /** `FAdvanceEpsilon` consults `dir` in exactly ONE place -- the
      `AnchorAssertion` case. Every other case reads `s1.cp`, `ov` or `cdn`,
      none of which mention the direction, and the character window is carried
      IN the state (`s1.context`) rather than recomputed from `dir`.

      So at the epsilon level the isomorphism costs nothing: the same state and
      the same oracle view, run with the anchors swapped. No position mirror is
      needed here because an epsilon phase does not move `cp` -- the mirror
      only enters where the string is actually read (`FConsume`). */
  lemma FAdvanceEpsilonSwap(c: RB.code, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c)
          && |s.processed.false_set| == RB.size(c)
    ensures AI.FAdvanceEpsilon(c, s, ov, LAnc.Backward)
         == AI.FAdvanceEpsilon(SwapAnchorsCode(c), s, ov, LAnc.Forward)
    decreases AI.unprocessed(s.processed), |s.active|
  {
    var cs := SwapAnchorsCode(c);
    assert RB.size(cs) == RB.size(c);
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    var i2 := RB.get_instr(cs, t.pc);
    // the two programs agree everywhere except an anchor's argument
    assert 0 <= t.pc < |c| ==> SwapAnchorsCodeNonAnchorAt(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonSwap(c, s.(active := ac), ov);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      FAdvanceEpsilonSwap(c, s1.(blocked := nb, isblocked := ni, active := ac), ov);
    case Accept =>
    case Jmp(x) => FAdvanceEpsilonSwap(c, s1.(active := [t.(pc := x)] + ac), ov);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      FAdvanceEpsilonSwap(c, s1.(active := [newt, t.(pc := y)] + ac), ov);
    case SetRegisterToCP(reg) =>
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock),
                   pc := t.pc + 1);
      FAdvanceEpsilonSwap(c, s1.(active := [t'] + ac), ov);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      FAdvanceEpsilonSwap(c, s1.(active := [t'] + ac), ov);
    case CheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        var t' := t.(pc := t.pc + 1,
                     look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        FAdvanceEpsilonSwap(c, s1.(active := [t'] + ac), ov);
      } else {
        FAdvanceEpsilonSwap(c, s1.(active := ac), ov);
      }
    case NegCheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        FAdvanceEpsilonSwap(c, s1.(active := ac), ov);
      } else {
        FAdvanceEpsilonSwap(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      }
    case WriteOracle(l) =>
      FAdvanceEpsilonSwap(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l));
    case BeginLoop =>
      FAdvanceEpsilonSwap(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov);
    case EndLoop =>
      if t.exit_allowed {
        FAdvanceEpsilonSwap(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        FAdvanceEpsilonSwap(c, s1.(active := ac), ov);
      }
    case CheckNullable(qid) =>
      if LCdn.cdn_get(s1.cdn, qid) {
        FAdvanceEpsilonSwap(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        FAdvanceEpsilonSwap(c, s1.(active := ac), ov);
      }
    case AnchorAssertion(a) =>
      // THE case: same context, swapped anchor, same verdict
      IsSatisfiedMirror(a, s1.context);
      if LAnc.is_satisfied(a, s1.context, LAnc.Backward) {
        FAdvanceEpsilonSwap(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else {
        FAdvanceEpsilonSwap(c, s1.(active := ac), ov);
      }
    case Fail =>
      FAdvanceEpsilonSwap(c, s1.(active := ac), ov);
  }

  // ==========================================================================
  // Layer 3 (NEXT): FFindMatch -- where the position mirror finally enters
  // ==========================================================================

  /* ---------------------------------------------------------------------
     STATUS / NEXT STEP.

     Proven above: the character window correspondence (CpContextMirror), the
     anchor swap (AnchorAtMirror), the code transform and its involution, and
     the epsilon-phase isomorphism (FAdvanceEpsilonSwap) -- which turned out
     to need NO mirroring, because FAdvanceEpsilon consults `dir` in exactly
     one place (AnchorAssertion) and carries its character window in the state
     rather than recomputing it from `dir`.

     What FFindMatch still needs, read off its body (Interpreter.dfy:384):

       1. `build_cdn_v(cdn, s.cp, ov, s.context, dir)` -- a mirror lemma; this
          is the one remaining consumer of `dir` that has not been examined.
       2. `incr_cp(cp, Backward) = cp - 1` vs `+1` forward. Checked: the mirror
          maps them correctly, since Mirror(cp - 1) = n - cp + 1 = Mirror(cp) + 1.
       3. `get_char(str, s3.cp - cp_offset(dir))` for the new context char.
          Checked by hand: backward reads str[cp-2] at the next position, and
          the forward run over the reversal reads the same character.
       4. The oracle view must now be MIRRORED (hence `MirrorView` above), and
          with it the register banks, whose recorded cp values are positions.
          For the L2 ORACLE BUILD this is lighter than it looks: the build
          regex is `remove_capture`d, so there are no capture writes, and C2/C3
          (ReachF / ReachesWrite) reason about pc/cp reachability with no
          registers at all. (A `MirrorView` reflecting the columns is the
          natural shape; deliberately NOT declared here, so nothing in the
          codebase carries an uninterpreted function.)

     ENCOURAGING: the recursion measures already correspond. FFindMatch
     decreases `s.cp` backward and `|str| - s.cp` forward; over the reversed
     string the forward measure is `n - Mirror(cp) = cp`, i.e. THE SAME
     MEASURE. The induction should line up without reindexing.
     --------------------------------------------------------------------- */

  // ==========================================================================
  // Layer 3: the oracle view mirror
  // ==========================================================================

  /** An oracle view with its COLUMNS reflected. The view is indexed by
      position (`n + 1` rows for a string of length `n`), so a Backward run
      reading column `cp` corresponds to a Forward run reading `Mirror(cp)`.
      Not needed before `FFindMatch` -- the epsilon phase holds `cp` fixed. */
  function MirrorView(ov: LOr.OracleView, n: int): LOr.OracleView
    requires n >= 0 && |ov| == n + 1
    // stated as ensures, not lemmas: downstream needs the ROW CONTENTS to be
    // automatic. Instantiating a separate row lemma at the mirrored index
    // `n - i` would not fire when discharging the sweep layer's column-shape
    // precondition -- the same reason SwapAnchorsCode carries its length here.
    ensures |MirrorView(ov, n)| == n + 1
    ensures forall k: int :: 0 <= k < n + 1 ==> MirrorView(ov, n)[k] == ov[n - k]
  {
    seq(n + 1, k requires 0 <= k < n + 1 => ov[n - k])
  }

  lemma MirrorViewLen(ov: LOr.OracleView, n: int)
    requires n >= 0 && |ov| == n + 1
    ensures |MirrorView(ov, n)| == n + 1
  {}

  lemma MirrorViewInvolution(ov: LOr.OracleView, n: int)
    requires n >= 0 && |ov| == n + 1
    ensures MirrorView(MirrorView(ov, n), n) == ov
  {
    forall k | 0 <= k < n + 1 ensures MirrorView(MirrorView(ov, n), n)[k] == ov[k] {}
  }

  /** Reading through the mirror. */
  lemma MirrorViewGet(ov: LOr.OracleView, n: int, cp: int, lid: int)
    requires n >= 0 && |ov| == n + 1
    ensures LOr.view_get_oracle(MirrorView(ov, n), Mirror(cp, n), lid)
         == LOr.view_get_oracle(ov, cp, lid)
  {
    if 0 <= cp <= n {
      assert MirrorView(ov, n)[n - cp] == ov[cp];
    }
  }

  /** Writing through the mirror. */
  lemma MirrorViewSet(ov: LOr.OracleView, n: int, cp: int, lid: int)
    requires n >= 0 && |ov| == n + 1
    ensures MirrorView(LOr.view_set_oracle(ov, cp, lid), n)
         == LOr.view_set_oracle(MirrorView(ov, n), Mirror(cp, n), lid)
  {
    var lhs := MirrorView(LOr.view_set_oracle(ov, cp, lid), n);
    var rhs := LOr.view_set_oracle(MirrorView(ov, n), Mirror(cp, n), lid);
    forall k | 0 <= k < n + 1 ensures lhs[k] == rhs[k] {
      if 0 <= cp <= n && 0 <= lid < |ov[cp]| {
        if k == n - cp {
          assert lhs[k] == ov[cp][lid := true];
        } else {
          assert n - k != cp;
        }
      }
    }
  }

  // ==========================================================================
  // Layer 3b: the cdn table
  // ==========================================================================

  /** The anchor swap pushed through a cdn formula. `interpret_cdn_v` consults
      `dir` in exactly one place -- `CDN_anchor` -- so this is the same move as
      `SwapAnchorsCode`, one layer down. */
  function SwapAnchorsFormula(f: LCdn.cdn_formula): LCdn.cdn_formula
    decreases f
  {
    match f
    case CDN_true => f
    case CDN_false => f
    case CDN_and(f1, f2) => LCdn.CDN_and(SwapAnchorsFormula(f1), SwapAnchorsFormula(f2))
    case CDN_or(o1, o2) => LCdn.CDN_or(SwapAnchorsFormula(o1), SwapAnchorsFormula(o2))
    case CDN_quant(q) => f
    case CDN_look(l) => f
    case CDN_neglook(l) => f
    case CDN_anchor(a) => LCdn.CDN_anchor(SwapAnchor(a))
  }

  function SwapAnchorsCdns(cs: LCdn.cdns): LCdn.cdns {
    seq(|cs|, i requires 0 <= i < |cs| => (cs[i].0, SwapAnchorsFormula(cs[i].1)))
  }

  /** A cdn formula evaluates the same backward as its swap does forward, at
      mirrored position against the mirrored view. */
  lemma InterpretCdnMirror(f: LCdn.cdn_formula, cp: int, ov: LOr.OracleView, n: int,
                           t: LCdn.cdn_table, ctx: LAnc.char_context)
    requires n >= 0 && |ov| == n + 1
    ensures LCdn.interpret_cdn_v(f, cp, ov, t, ctx, LAnc.Backward)
         == LCdn.interpret_cdn_v(SwapAnchorsFormula(f), Mirror(cp, n), MirrorView(ov, n), t,
                                 ctx, LAnc.Forward)
    decreases f
  {
    match f
    case CDN_and(f1, f2) =>
      InterpretCdnMirror(f1, cp, ov, n, t, ctx);
      InterpretCdnMirror(f2, cp, ov, n, t, ctx);
    case CDN_or(o1, o2) =>
      InterpretCdnMirror(o1, cp, ov, n, t, ctx);
      InterpretCdnMirror(o2, cp, ov, n, t, ctx);
    case CDN_look(l) => MirrorViewGet(ov, n, cp, l);
    case CDN_neglook(l) => MirrorViewGet(ov, n, cp, l);
    case CDN_anchor(a) => IsSatisfiedMirror(a, ctx);
    case _ =>
  }

  lemma BuildCdnRecMirror(cs: LCdn.cdns, cp: int, ov: LOr.OracleView, n: int,
                          ctx: LAnc.char_context, table: LCdn.cdn_table)
    requires n >= 0 && |ov| == n + 1
    ensures LCdn.build_cdn_rec_v(cs, cp, ov, ctx, LAnc.Backward, table)
         == LCdn.build_cdn_rec_v(SwapAnchorsCdns(cs), Mirror(cp, n), MirrorView(ov, n), ctx,
                                 LAnc.Forward, table)
    decreases |cs|
  {
    if |cs| == 0 { return; }
    InterpretCdnMirror(cs[0].1, cp, ov, n, table, ctx);
    var eval := LCdn.interpret_cdn_v(cs[0].1, cp, ov, table, ctx, LAnc.Backward);
    var table' := if eval then LCdn.cdn_set_true(table, cs[0].0) else table;
    assert SwapAnchorsCdns(cs)[1..] == SwapAnchorsCdns(cs[1..]);
    BuildCdnRecMirror(cs[1..], cp, ov, n, ctx, table');
  }

  /** `build_cdn_v` through the mirror -- the last consumer of `dir` in
      `FFindMatch`'s body that had not been checked. It behaves exactly like
      the others: swap the anchors, mirror the position and the view. */
  lemma BuildCdnMirror(cs: LCdn.cdns, cp: int, ov: LOr.OracleView, n: int,
                       ctx: LAnc.char_context)
    requires n >= 0 && |ov| == n + 1
    ensures LCdn.build_cdn_v(cs, cp, ov, ctx, LAnc.Backward)
         == LCdn.build_cdn_v(SwapAnchorsCdns(cs), Mirror(cp, n), MirrorView(ov, n), ctx,
                             LAnc.Forward)
  {
    BuildCdnRecMirror(cs, cp, ov, n, ctx, LCdn.init_cdn());
  }

  // ==========================================================================
  // Layer 4: mirroring the recorded positions (registers, threads, states)
  // ==========================================================================

  /** A stored register value through the mirror. `-1` means UNSET and must
      stay unset; a real position `v` reflects to `n - v`. */
  function MirrorCpVal(v: int, n: int): int { if v >= 0 then n - v else v }

  /** A register bank with every recorded POSITION reflected. Clocks are not
      positions and are left alone. */
  function MirrorRegs(r: AReg.Regs, n: int): AReg.Regs {
    AReg.ARegs(seq(|r.a_cp|, i requires 0 <= i < |r.a_cp| => MirrorCpVal(r.a_cp[i], n)),
               r.a_clk)
  }

  /** Writing a position commutes with the mirror. */
  lemma SetRegMirror(r: AReg.Regs, k: int, cp: int, clk: int, n: int)
    requires cp >= 0
    ensures AReg.set_reg(MirrorRegs(r, n), k, Some(Mirror(cp, n)), clk)
         == MirrorRegs(AReg.set_reg(r, k, Some(cp), clk), n)
  {
    if 0 <= k < |r.a_cp| && 0 <= k < |r.a_clk| {
      var lhs := AReg.set_reg(MirrorRegs(r, n), k, Some(Mirror(cp, n)), clk);
      var rhs := MirrorRegs(AReg.set_reg(r, k, Some(cp), clk), n);
      assert |lhs.a_cp| == |rhs.a_cp|;
      forall i | 0 <= i < |lhs.a_cp| ensures lhs.a_cp[i] == rhs.a_cp[i] {}
    }
  }

  /** Clearing a register commutes with the mirror (the `None` write). */
  lemma SetRegNoneMirror(r: AReg.Regs, k: int, clk: int, n: int)
    ensures AReg.set_reg(MirrorRegs(r, n), k, None, clk)
         == MirrorRegs(AReg.set_reg(r, k, None, clk), n)
  {
    if 0 <= k < |r.a_cp| && 0 <= k < |r.a_clk| {
      var lhs := AReg.set_reg(MirrorRegs(r, n), k, None, clk);
      var rhs := MirrorRegs(AReg.set_reg(r, k, None, clk), n);
      forall i | 0 <= i < |lhs.a_cp| ensures lhs.a_cp[i] == rhs.a_cp[i] {}
    }
  }

  function MirrorThread(t: AI.Thread, n: int): AI.Thread {
    AI.Thread(t.pc, MirrorRegs(t.capture_regs, n), MirrorRegs(t.look_regs, n),
              MirrorRegs(t.quant_regs, n), t.exit_allowed)
  }

  function MirrorThreads(ts: seq<AI.Thread>, n: int): seq<AI.Thread> {
    seq(|ts|, i requires 0 <= i < |ts| => MirrorThread(ts[i], n))
  }

  function MirrorBlocked(bs: seq<(AI.Thread, RC.char_expectation)>, n: int)
    : seq<(AI.Thread, RC.char_expectation)>
  {
    seq(|bs|, i requires 0 <= i < |bs| => (MirrorThread(bs[i].0, n), bs[i].1))
  }

  /** A whole VM state through the mirror: the position and every recorded
      position reflected, everything else (pcs, flags, clock, the processed
      sets, the character window) untouched. */
  function MirrorState(s: AI.VmState, n: int): AI.VmState {
    AI.VmSt(Mirror(s.cp, n), MirrorThreads(s.active, n), s.processed,
            MirrorBlocked(s.blocked, n), s.isblocked,
            (match s.bestmatch case None => None case Some(t) => Some(MirrorThread(t, n))),
            s.context, s.clock, s.cdn)
  }

  lemma MirrorThreadsCons(t: AI.Thread, ts: seq<AI.Thread>, n: int)
    ensures MirrorThreads([t] + ts, n) == [MirrorThread(t, n)] + MirrorThreads(ts, n)
  {
    var lhs := MirrorThreads([t] + ts, n);
    var rhs := [MirrorThread(t, n)] + MirrorThreads(ts, n);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  lemma MirrorThreadsTail(ts: seq<AI.Thread>, n: int)
    requires |ts| > 0
    ensures MirrorThreads(ts, n)[1..] == MirrorThreads(ts[1..], n)
  {
    var lhs := MirrorThreads(ts, n)[1..];
    var rhs := MirrorThreads(ts[1..], n);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  /** `add_thread` (the block list) commutes with the mirror. */
  lemma AddThreadMirror(t: AI.Thread, ce: RC.char_expectation,
                        bl: seq<(AI.Thread, RC.char_expectation)>, ib: AI.pcset, n: int)
    ensures AI.add_thread(MirrorThread(t, n), ce, MirrorBlocked(bl, n), ib).0
         == MirrorBlocked(AI.add_thread(t, ce, bl, ib).0, n)
    ensures AI.add_thread(MirrorThread(t, n), ce, MirrorBlocked(bl, n), ib).1
         == AI.add_thread(t, ce, bl, ib).1
  {
    if AI.pc_mem(ib, t.pc) { return; }
    var lhs := MirrorBlocked(bl, n) + [(MirrorThread(t, n), ce)];
    var rhs := MirrorBlocked(bl + [(t, ce)], n);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  // ==========================================================================
  // Layer 5: the epsilon phase through the FULL mirror
  // ==========================================================================

  /** An epsilon phase only ever `view_set_oracle`s, which preserves the
      view's shape. Needed so `MirrorView` is well-formed on the result. */
  lemma FAdvanceEpsilonViewLen(c: RB.code, s: AI.VmState, ov: LOr.OracleView)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    ensures |AI.FAdvanceEpsilon(c, s, ov, LAnc.Backward).1| == |ov|
    decreases AI.unprocessed(s.processed), |s.active|
  {
    if |s.active| == 0 { return; }
    var t := s.active[0];
    var ac := s.active[1..];
    var i := RB.get_instr(c, t.pc);
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      FAdvanceEpsilonViewLen(c, s.(active := ac), ov); return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      FAdvanceEpsilonViewLen(c, s1.(blocked := nb, isblocked := ni, active := ac), ov);
    case Accept =>
    case Jmp(x) => FAdvanceEpsilonViewLen(c, s1.(active := [t.(pc := x)] + ac), ov);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      FAdvanceEpsilonViewLen(c, s1.(active := [newt, t.(pc := y)] + ac), ov);
    case SetRegisterToCP(reg) =>
      FAdvanceEpsilonViewLen(c, s1.(active := [t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock), pc := t.pc + 1)] + ac), ov);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      FAdvanceEpsilonViewLen(c, s1.(active := [t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1)] + ac), ov);
    case CheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) {
        FAdvanceEpsilonViewLen(c, s1.(active := [t.(pc := t.pc + 1, look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock))] + ac), ov);
      } else { FAdvanceEpsilonViewLen(c, s1.(active := ac), ov); }
    case NegCheckOracle(l) =>
      if LOr.view_get_oracle(ov, s1.cp, l) { FAdvanceEpsilonViewLen(c, s1.(active := ac), ov); }
      else { FAdvanceEpsilonViewLen(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov); }
    case WriteOracle(l) =>
      FAdvanceEpsilonViewLen(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l));
    case BeginLoop =>
      FAdvanceEpsilonViewLen(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac), ov);
    case EndLoop =>
      if t.exit_allowed { FAdvanceEpsilonViewLen(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov); }
      else { FAdvanceEpsilonViewLen(c, s1.(active := ac), ov); }
    case CheckNullable(qid) =>
      if LCdn.cdn_get(s1.cdn, qid) { FAdvanceEpsilonViewLen(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov); }
      else { FAdvanceEpsilonViewLen(c, s1.(active := ac), ov); }
    case AnchorAssertion(a) =>
      if LAnc.is_satisfied(a, s1.context, LAnc.Backward) {
        FAdvanceEpsilonViewLen(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov);
      } else { FAdvanceEpsilonViewLen(c, s1.(active := ac), ov); }
    case Fail => FAdvanceEpsilonViewLen(c, s1.(active := ac), ov);
  }

  /** THE epsilon-phase isomorphism, now with the position mirror: running
      `c` BACKWARD on a state, then mirroring, is the same as mirroring first
      and running the anchor-swapped program FORWARD.

      `FAdvanceEpsilonSwap` was the `cp`-fixed special case; this is the form
      `FFindMatch` needs, where the recorded positions (registers, oracle
      columns) all reflect. */
  lemma FAdvanceEpsilonMirror(c: RB.code, s: AI.VmState, ov: LOr.OracleView, n: int)
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires n >= 0 && |ov| == n + 1 && 0 <= s.cp <= n
    ensures |AI.FAdvanceEpsilon(c, s, ov, LAnc.Backward).1| == n + 1
    ensures AI.FAdvanceEpsilon(SwapAnchorsCode(c), MirrorState(s, n), MirrorView(ov, n),
                               LAnc.Forward)
         == (MirrorState(AI.FAdvanceEpsilon(c, s, ov, LAnc.Backward).0, n),
             MirrorView(AI.FAdvanceEpsilon(c, s, ov, LAnc.Backward).1, n))
    decreases AI.unprocessed(s.processed), |s.active|
  {
    FAdvanceEpsilonViewLen(c, s, ov);
    var cs := SwapAnchorsCode(c);
    var ms := MirrorState(s, n);
    var mv := MirrorView(ov, n);
    assert RB.size(cs) == RB.size(c);
    assert ms.cp == Mirror(s.cp, n) && ms.cp >= 0;
    if |s.active| == 0 { return; }
    assert |ms.active| == |s.active|;
    var t := s.active[0];
    var ac := s.active[1..];
    assert ms.active[0] == MirrorThread(t, n);
    MirrorThreadsTail(s.active, n);
    assert ms.active[1..] == MirrorThreads(ac, n);
    var i := RB.get_instr(c, t.pc);
    GetInstrSwap(c, t.pc);            // the forward run reads the same instruction
    if AI.bpc_mem(s.processed, t.pc, t.exit_allowed) {
      assert MirrorState(s.(active := ac), n) == ms.(active := MirrorThreads(ac, n));
      FAdvanceEpsilonMirror(c, s.(active := ac), ov, n);
      return;
    }
    var b0 := s.processed;
    var s1 := s.(clock := s.clock + 1, processed := AI.bpc_add(b0, t.pc, t.exit_allowed));
    AI.UnprocessedAdd(b0, t.pc, t.exit_allowed);
    assert s1.cp == s.cp;
    var ms1 := MirrorState(s1, n);
    // s1 differs from s only in clock/processed, so the mirrored thread list
    // is unchanged -- Fork builds its new thread out of ms1.active[0]
    assert ms1.active == ms.active;
    assert ms1.active[0] == MirrorThread(t, n);
    assert ms1.active[1..] == MirrorThreads(ac, n);
    match i
    case Consume(ce) =>
      var (nb, ni) := AI.add_thread(t, ce, s1.blocked, s1.isblocked);
      AddThreadMirror(t, ce, s1.blocked, s1.isblocked, n);
      var s2 := s1.(blocked := nb, isblocked := ni, active := ac);
      assert MirrorState(s2, n)
          == ms1.(blocked := MirrorBlocked(nb, n), isblocked := ni,
                  active := MirrorThreads(ac, n));
      FAdvanceEpsilonMirror(c, s2, ov, n);
    case Accept =>
      // both runs stop here; the winner is the mirrored thread
      assert MirrorThreads([], n) == [];
      assert MirrorState(s1.(active := [], bestmatch := Some(t)), n)
          == ms1.(active := [], bestmatch := Some(MirrorThread(t, n)));
    case Jmp(x) =>
      MirrorThreadsCons(t.(pc := x), ac, n);
      FAdvanceEpsilonMirror(c, s1.(active := [t.(pc := x)] + ac), ov, n);
    case Fork(x, y) =>
      var newt := AI.Thread(x, t.capture_regs, t.look_regs, t.quant_regs, t.exit_allowed);
      // the forward run forks the MIRRORED thread; same object either way
      assert MirrorThread(newt, n)
          == AI.Thread(x, MirrorRegs(t.capture_regs, n), MirrorRegs(t.look_regs, n),
                       MirrorRegs(t.quant_regs, n), t.exit_allowed);
      assert MirrorThread(t.(pc := y), n) == MirrorThread(t, n).(pc := y);
      MirrorThreadsCons(t.(pc := y), ac, n);
      MirrorThreadsCons(newt, [t.(pc := y)] + ac, n);
      assert [newt, t.(pc := y)] + ac == [newt] + ([t.(pc := y)] + ac);
      assert MirrorThreads([newt, t.(pc := y)] + ac, n)
          == [MirrorThread(newt, n)] + ([MirrorThread(t, n).(pc := y)] + MirrorThreads(ac, n));
      assert MirrorState(s1.(active := [newt, t.(pc := y)] + ac), n)
          == ms1.(active := [MirrorThread(newt, n)]
                            + ([MirrorThread(t, n).(pc := y)] + MirrorThreads(ac, n)));
      // the forward run builds [a, b] + c; match it to the [a] + ([b] + c) shape
      assert [MirrorThread(newt, n), MirrorThread(t, n).(pc := y)] + MirrorThreads(ac, n)
          == [MirrorThread(newt, n)]
             + ([MirrorThread(t, n).(pc := y)] + MirrorThreads(ac, n));
      FAdvanceEpsilonMirror(c, s1.(active := [newt, t.(pc := y)] + ac), ov, n);
    case SetRegisterToCP(reg) =>
      SetRegMirror(t.capture_regs, reg, s1.cp, s1.clock, n);
      var t' := t.(capture_regs := AReg.set_reg(t.capture_regs, reg, Some(s1.cp), s1.clock),
                   pc := t.pc + 1);
      MirrorThreadsCons(t', ac, n);
      FAdvanceEpsilonMirror(c, s1.(active := [t'] + ac), ov, n);
    case SetQuantToClock(q, b) =>
      var ocp := if b then Some(s1.cp) else None;
      if b { SetRegMirror(t.quant_regs, q, s1.cp, s1.clock, n); }
      else { SetRegNoneMirror(t.quant_regs, q, s1.clock, n); }
      var t' := t.(quant_regs := AReg.set_reg(t.quant_regs, q, ocp, s1.clock), pc := t.pc + 1);
      MirrorThreadsCons(t', ac, n);
      FAdvanceEpsilonMirror(c, s1.(active := [t'] + ac), ov, n);
    case CheckOracle(l) =>
      MirrorViewGet(ov, n, s1.cp, l);
      if LOr.view_get_oracle(ov, s1.cp, l) {
        SetRegMirror(t.look_regs, l, s1.cp, s1.clock, n);
        var t' := t.(pc := t.pc + 1,
                     look_regs := AReg.set_reg(t.look_regs, l, Some(s1.cp), s1.clock));
        MirrorThreadsCons(t', ac, n);
        FAdvanceEpsilonMirror(c, s1.(active := [t'] + ac), ov, n);
      } else {
        FAdvanceEpsilonMirror(c, s1.(active := ac), ov, n);
      }
    case NegCheckOracle(l) =>
      MirrorViewGet(ov, n, s1.cp, l);
      if LOr.view_get_oracle(ov, s1.cp, l) {
        FAdvanceEpsilonMirror(c, s1.(active := ac), ov, n);
      } else {
        MirrorThreadsCons(t.(pc := t.pc + 1), ac, n);
        FAdvanceEpsilonMirror(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, n);
      }
    case WriteOracle(l) =>
      MirrorViewSet(ov, n, s1.cp, l);
      FAdvanceEpsilonMirror(c, s1.(active := ac), LOr.view_set_oracle(ov, s1.cp, l), n);
    case BeginLoop =>
      MirrorThreadsCons(t.(exit_allowed := false, pc := t.pc + 1), ac, n);
      FAdvanceEpsilonMirror(c, s1.(active := [t.(exit_allowed := false, pc := t.pc + 1)] + ac),
                            ov, n);
    case EndLoop =>
      if t.exit_allowed {
        MirrorThreadsCons(t.(pc := t.pc + 1), ac, n);
        FAdvanceEpsilonMirror(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, n);
      } else {
        FAdvanceEpsilonMirror(c, s1.(active := ac), ov, n);
      }
    case CheckNullable(qid) =>
      if LCdn.cdn_get(s1.cdn, qid) {
        MirrorThreadsCons(t.(pc := t.pc + 1), ac, n);
        FAdvanceEpsilonMirror(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, n);
      } else {
        FAdvanceEpsilonMirror(c, s1.(active := ac), ov, n);
      }
    case AnchorAssertion(a) =>
      IsSatisfiedMirror(a, s1.context);
      if LAnc.is_satisfied(a, s1.context, LAnc.Backward) {
        MirrorThreadsCons(t.(pc := t.pc + 1), ac, n);
        FAdvanceEpsilonMirror(c, s1.(active := [t.(pc := t.pc + 1)] + ac), ov, n);
      } else {
        FAdvanceEpsilonMirror(c, s1.(active := ac), ov, n);
      }
    case Fail =>
      FAdvanceEpsilonMirror(c, s1.(active := ac), ov, n);
  }

  // ==========================================================================
  // Layer 6: FConsume and the FFindMatch induction
  // ==========================================================================

  lemma MirrorBlockedTail(bs: seq<(AI.Thread, RC.char_expectation)>, n: int)
    requires |bs| > 0
    ensures MirrorBlocked(bs, n)[0] == (MirrorThread(bs[0].0, n), bs[0].1)
    ensures MirrorBlocked(bs, n)[1..] == MirrorBlocked(bs[1..], n)
  {
    var lhs := MirrorBlocked(bs, n)[1..];
    var rhs := MirrorBlocked(bs[1..], n);
    forall i | 0 <= i < |lhs| ensures lhs[i] == rhs[i] {}
  }

  /** `FConsume` takes no direction at all -- it only promotes blocked threads
      whose expectation the current character satisfies -- so it commutes with
      the mirror outright. */
  lemma FConsumeMirror(s: AI.VmState, n: int)
    ensures AI.FConsume(MirrorState(s, n)) == MirrorState(AI.FConsume(s), n)
    decreases |s.blocked|
  {
    if |s.blocked| == 0 { return; }
    MirrorBlockedTail(s.blocked, n);
    var t := s.blocked[0].0;
    var ce := s.blocked[0].1;
    var s1 := s.(blocked := s.blocked[1..]);
    assert MirrorState(s1, n) == MirrorState(s, n).(blocked := MirrorBlocked(s.blocked[1..], n));
    var s2 := if RC.is_accepted(s1.context.nextchar, ce)
              then s1.(active := [t.(exit_allowed := true, pc := t.pc + 1)] + s1.active)
              else s1;
    if RC.is_accepted(s1.context.nextchar, ce) {
      MirrorThreadsCons(t.(exit_allowed := true, pc := t.pc + 1), s1.active, n);
      assert MirrorThread(t.(exit_allowed := true, pc := t.pc + 1), n)
          == MirrorThread(t, n).(exit_allowed := true, pc := t.pc + 1);
    }
    FConsumeMirror(s2, n);
  }

  /** THE isomorphism: a BACKWARD run of `c` over `str` is a FORWARD run of
      the anchor-swapped program over `Reverse(str)`, with every position --
      the cursor, the registers, the oracle columns -- reflected.

      This is what buys backward execution without re-proving the forward
      reachability and simulation layers with flipped arithmetic. */
  lemma FFindMatchMirror(c: RB.code, str: string, s: AI.VmState, ov: LOr.OracleView,
                         cdn: LCdn.cdns, n: int)
    requires n == |str|
    requires |s.processed.true_set| == RB.size(c) && |s.processed.false_set| == RB.size(c)
    requires |ov| == n + 1
    requires 0 <= s.cp <= n
    requires s.context.nextchar == AI.get_char(str, s.cp - 1)
    // the same fact read through the mirror. Implied by the line above via
    // GetCharMirror, but a precondition inside an `ensures` has to be
    // well-formed WITHOUT calling a lemma, so it is stated here and callers
    // discharge it with GetCharMirror.
    requires s.context.nextchar == AI.get_char(LC.Reverse(str), n - s.cp)
    ensures |AI.FFindMatch(c, str, s, ov, LAnc.Backward, cdn).1| == n + 1
    ensures AI.FFindMatch(SwapAnchorsCode(c), LC.Reverse(str), MirrorState(s, n),
                          MirrorView(ov, n), LAnc.Forward, SwapAnchorsCdns(cdn))
         == ((match AI.FFindMatch(c, str, s, ov, LAnc.Backward, cdn).0
              case None => None
              case Some(t) => Some(MirrorThread(t, n))),
             MirrorView(AI.FFindMatch(c, str, s, ov, LAnc.Backward, cdn).1, n))
    decreases s.cp
  {
    ReverseLen(str);
    GetCharMirror(str, s.cp);
    var cs := SwapAnchorsCode(c);
    var rstr := LC.Reverse(str);
    var ms := MirrorState(s, n);
    var mv := MirrorView(ov, n);
    assert ms.context.nextchar == AI.get_char(rstr, ms.cp);

    // --- the cdn table -----------------------------------------------------
    BuildCdnMirror(cdn, s.cp, ov, n, s.context);
    var s0 := s.(cdn := LCdn.build_cdn_v(cdn, s.cp, ov, s.context, LAnc.Backward));
    assert MirrorState(s0, n) == ms.(cdn := s0.cdn);

    // --- the epsilon phase -------------------------------------------------
    FAdvanceEpsilonMirror(c, s0, ov, n);
    var (s1, ov1) := AI.FAdvanceEpsilon(c, s0, ov, LAnc.Backward);
    assert |ov1| == n + 1;
    assert s1.cp == s0.cp == s.cp && s1.context == s.context;

    if |s1.blocked| == 0 { return; }
    match s1.context.nextchar
    case None =>
    case Some(_) =>
      // --- consume and step ------------------------------------------------
      FConsumeMirror(s1, n);
      var s2 := AI.FConsume(s1);
      assert s2.cp == s1.cp && s2.context == s1.context;
      var s3 := s2.(processed := AI.init_bpcset(RB.size(c)),
                    isblocked := AI.init_pcset(RB.size(c)),
                    cdn := LCdn.init_cdn(), cp := AI.incr_cp(s2.cp, LAnc.Backward));
      assert s3.cp == s.cp - 1;
      // the character window advances the same way on both sides
      assert AI.get_char(str, s.cp - 1).Some? ==> 0 <= s.cp - 1 < n;
      GetCharMirror(str, s3.cp);
      var newchar := AI.get_char(str, s3.cp - AI.cp_offset(LAnc.Backward));
      assert newchar == AI.get_char(rstr, Mirror(s3.cp, n));
      var s4 := s3.(context := LAnc.update_context(s3.context, newchar));
      assert MirrorState(s3, n)
          == MirrorState(s2, n).(processed := AI.init_bpcset(RB.size(cs)),
                                 isblocked := AI.init_pcset(RB.size(cs)),
                                 cdn := LCdn.init_cdn(),
                                 cp := AI.incr_cp(Mirror(s2.cp, n), LAnc.Forward));
      assert MirrorState(s4, n) == MirrorState(s3, n).(context := s4.context);
      assert 0 <= s4.cp <= n;
      assert s4.context.nextchar == AI.get_char(str, s4.cp - 1);
      GetCharMirror(str, s4.cp);
      assert s4.context.nextchar == AI.get_char(LC.Reverse(str), n - s4.cp);
      FFindMatchMirror(c, str, s4, ov1, cdn, n);
  }

  // ==========================================================================
  // Layer 7: the payoff -- a BACKWARD oracle build IS a forward run
  // ==========================================================================

  /** A freshly initialized bank records no positions, so the mirror fixes it. */
  lemma MirrorInitRegs(k: int, n: int)
    ensures MirrorRegs(AReg.init_regs(k), n) == AReg.init_regs(k)
  {
    var lhs := MirrorRegs(AReg.init_regs(k), n);
    var rhs := AReg.init_regs(k);
    assert |lhs.a_cp| == |rhs.a_cp|;
    forall i | 0 <= i < |lhs.a_cp| ensures lhs.a_cp[i] == rhs.a_cp[i] {}
  }

  /** The backward build's START state mirrors to the standard FORWARD start
      state over the reversed string: `init_cp(Backward, n)` is `n`, whose
      mirror is `0`, and the two initial character windows coincide by
      `CpContextMirror`. */
  lemma FInitStateMirror(c: RB.code, str: string, cap: AReg.Regs, lk: AReg.Regs,
                         qt: AReg.Regs, n: int)
    requires n == |str|
    ensures MirrorState(AI.FInitState(c, AI.init_cp(LAnc.Backward, n), cap, lk, qt, 0,
                                      AI.cp_context(AI.init_cp(LAnc.Backward, n), str,
                                                    LAnc.Backward)), n)
         == AI.FInitState(SwapAnchorsCode(c), 0, MirrorRegs(cap, n), MirrorRegs(lk, n),
                          MirrorRegs(qt, n), 0,
                          AI.cp_context(0, LC.Reverse(str), LAnc.Forward))
  {
    CpContextMirror(str, n);
    assert AI.init_cp(LAnc.Backward, n) == n;
    assert Mirror(n, n) == 0;
    var bt := AI.init_thread(cap, lk, qt);
    assert MirrorThread(bt, n)
        == AI.init_thread(MirrorRegs(cap, n), MirrorRegs(lk, n), MirrorRegs(qt, n));
    assert MirrorThreads([bt], n) == [MirrorThread(bt, n)];
    assert MirrorBlocked([], n) == [];
  }

  /** THE PAYOFF. A lookaround whose oracle is built BACKWARD -- i.e. a
      lookAHEAD (`oracle_direction(Lookahead) == Backward`) -- produces
      exactly the mirror of the oracle a FORWARD run of the anchor-swapped
      program over the reversed string produces.

      So the forward-only reachability layer (`OracleReach`) and the
      forward-only simulation (`PikeSimRE`) can characterize a backward build
      by transport, instead of being re-proved with flipped arithmetic. */
  lemma BackwardBuildIsForward(bc: RB.code, str: string, ov: LOr.OracleView,
                               cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int, n: int)
    requires n == |str| && |ov| == n + 1
    ensures
      var initcp := AI.init_cp(LAnc.Backward, n);
      var inits := AI.FInitState(bc, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                                 AReg.init_regs(nquant), 0,
                                 AI.cp_context(initcp, str, LAnc.Backward));
      var initsF := AI.FInitState(SwapAnchorsCode(bc), 0, AReg.init_regs(ncap),
                                  AReg.init_regs(nlook), AReg.init_regs(nquant), 0,
                                  AI.cp_context(0, LC.Reverse(str), LAnc.Forward));
      // stated as mirror-of-backward == forward: `MirrorView` needs its
      // argument's length, and only the backward run's is established here
      |AI.FFindMatch(bc, str, inits, ov, LAnc.Backward, cdn).1| == n + 1
      && MirrorView(AI.FFindMatch(bc, str, inits, ov, LAnc.Backward, cdn).1, n)
         == AI.FFindMatch(SwapAnchorsCode(bc), LC.Reverse(str), initsF,
                          MirrorView(ov, n), LAnc.Forward, SwapAnchorsCdns(cdn)).1
  {
    var initcp := AI.init_cp(LAnc.Backward, n);
    var ctx := AI.cp_context(initcp, str, LAnc.Backward);
    var inits := AI.FInitState(bc, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                               AReg.init_regs(nquant), 0, ctx);
    MirrorInitRegs(ncap, n); MirrorInitRegs(nlook, n); MirrorInitRegs(nquant, n);
    FInitStateMirror(bc, str, AReg.init_regs(ncap), AReg.init_regs(nlook),
                     AReg.init_regs(nquant), n);
    ReverseLen(str);
    GetCharMirror(str, initcp);
    assert inits.cp == n && 0 <= inits.cp <= n;
    assert inits.context.nextchar == AI.get_char(str, inits.cp - 1);
    assert inits.context.nextchar == AI.get_char(LC.Reverse(str), n - inits.cp);
    assert |inits.processed.true_set| == RB.size(bc)
        && |inits.processed.false_set| == RB.size(bc);
    FFindMatchMirror(bc, str, inits, ov, cdn, n);
  }

  // ==========================================================================
  // Layer 8: transporting the FORWARD sweep characterization to a
  //          BACKWARD build
  // ==========================================================================

  /** The anchor swap preserves every classification the sweep layer gates on:
      it rewrites anchor ARGUMENTS only, so oracle reads, nullability checks,
      write columns and accepts are all untouched. */
  lemma SwapPreservesClassification(c: RB.code, lid: int)
    ensures OS.NoOracleReads(c) ==> OS.NoOracleReads(SwapAnchorsCode(c))
    ensures OS.NoCheckNullable(c) ==> OS.NoCheckNullable(SwapAnchorsCode(c))
    ensures OS.WritesOnlyLid(c, lid) ==> OS.WritesOnlyLid(SwapAnchorsCode(c), lid)
    ensures OS.NoAccept(c) ==> OS.NoAccept(SwapAnchorsCode(c))
  {
    forall pc | 0 <= pc < |c| ensures SwapAnchorsCodeNonAnchorAt(c, pc) {}
  }

  /** THE TRANSPORT. `SweepCharacterization` is forward-only; this is its
      BACKWARD counterpart, obtained not by re-proving it but by running the
      isomorphism underneath it.

      A backward build's oracle column at `cp` is set exactly when the
      anchor-swapped program, run FORWARD over the reversed string, reaches a
      write at the mirrored position. */
  lemma BackwardSweepCharacterization(c: RB.code, str: string, ov: LOr.OracleView, lid: int,
                                      cdn: LCdn.cdns, ncap: int, nlook: int, nquant: int,
                                      n: int)
    requires n == |str| && |ov| == n + 1
    requires OS.NoOracleReads(c) && OS.NoCheckNullable(c) && OS.WritesOnlyLid(c, lid)
          && OS.NoAccept(c)
    requires forall i: int :: 0 <= i < |ov| ==> 0 <= lid < |ov[i]|
    ensures
      var initcp := AI.init_cp(LAnc.Backward, n);
      var s := AI.FInitState(c, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                             AReg.init_regs(nquant), 0,
                             AI.cp_context(initcp, str, LAnc.Backward));
      var ov' := AI.FFindMatch(c, str, s, ov, LAnc.Backward, cdn).1;
      forall cp: int :: LOr.view_get_oracle(ov', cp, lid)
        == (LOr.view_get_oracle(ov, cp, lid)
            || ORc.ReachesWrite(SwapAnchorsCode(c), LC.Reverse(str), 0, lid,
                                Mirror(cp, n)))
  {
    ReverseLen(str);
    var cs := SwapAnchorsCode(c);
    var rstr := LC.Reverse(str);
    var mv := MirrorView(ov, n);
    SwapPreservesClassification(c, lid);
    // the column-shape hypothesis, transported. MirrorView's row `ensures`
    // makes mv[j] == ov[n - j] available without instantiating a lemma, which
    // is what previously refused to fire at the mirrored index.
    assert |mv| == n + 1;
    forall j: int | 0 <= j < |mv| ensures 0 <= lid < |mv[j]| {
      assert mv[j] == ov[n - j];
      assert 0 <= n - j < |ov|;
    }
    assert |rstr| < |mv|;

    assert OS.NoOracleReads(cs) && OS.NoCheckNullable(cs);
    assert OS.WritesOnlyLid(cs, lid) && OS.NoAccept(cs);
    assert |rstr| < |mv|;
    assert forall i: int :: 0 <= i < |mv| ==> 0 <= lid < |mv[i]|;
    // the forward statement, on the swapped program over the reversed string
    ORc.SweepCharacterization(cs, rstr, mv, lid, SwapAnchorsCdns(cdn),
                              AReg.init_regs(ncap), AReg.init_regs(nlook),
                              AReg.init_regs(nquant), 0);
    // ... and the isomorphism identifying that run with the backward build
    BackwardBuildIsForward(c, str, ov, cdn, ncap, nlook, nquant, n);

    var initcp := AI.init_cp(LAnc.Backward, n);
    var sb := AI.FInitState(c, initcp, AReg.init_regs(ncap), AReg.init_regs(nlook),
                            AReg.init_regs(nquant), 0,
                            AI.cp_context(initcp, str, LAnc.Backward));
    var ovb := AI.FFindMatch(c, str, sb, ov, LAnc.Backward, cdn).1;
    forall cp: int
      ensures LOr.view_get_oracle(ovb, cp, lid)
           == (LOr.view_get_oracle(ov, cp, lid)
               || ORc.ReachesWrite(cs, rstr, 0, lid, Mirror(cp, n)))
    {
      MirrorViewGet(ovb, n, cp, lid);
      MirrorViewGet(ov, n, cp, lid);
    }
  }
}
