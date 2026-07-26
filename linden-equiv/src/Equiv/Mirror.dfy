/* ==========================================================================
   Mirror.dfy — the string-reversal isomorphism (L2 groundwork)

   A BACKWARD run of bytecode `c` over `str` is isomorphic to a FORWARD run
   of `c` over `Reverse(str)` under the position mirror `cp |-> |str| - cp`,
   provided `BeginInput`/`EndInput` are swapped in `c`.

   The point of this file is to buy backward execution WITHOUT re-proving the
   forward reachability/simulation layers with flipped arithmetic. See
   L2_INVESTIGATION.md for why this route was chosen over parameterizing the
   ~1080-line `OracleReach` family by direction.

   Layer 1 (this file, so far): the two facts the whole route rests on --
   the context correspondence and the anchor swap.
   ========================================================================== */
include "PikeSimRE.dfy"

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
  function SwapAnchorsCode(c: RB.code): RB.code {
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
}
