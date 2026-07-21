// Phase 4b (layer 2): TreeRepRE — a Linden backtracking tree represented in
// RegElk bytecode starting at a pc (port of Linden Engine/TreeRep.dfy).
//
// Differences from Linden's TreeRep, forced by RegElk's instruction set:
//  - the Reset node is carried by SetQuantToClock(qid, false), with the group
//    list recovered through the quantifier-groups map qm;
//  - EndLoop falls through (Progress continues at pc+1; the star's explicit
//    back-Jmp is then a tr_jmp stutter);
//  - reading is via char_expectations (ReadCharE), semantically tied to
//    CharDescrs at the NfaRepL layer (ExpectationMatches), not here;
//  - the loop flag is RegElk's plain bool exit_allowed (true = Linden CanExit).
include "ActionsRepRE.dfy"

/** Phase 4b layer 2: relates a Linden backtracking `Tree` to RegElk bytecode starting
    at a program counter (port of Linden `Engine/TreeRep.dfy`). Builds on
    `LindenElkActionsRep`'s `NfaRepL`/`ActionsRepL` for the code-shape side and adapts
    three RegElk-specific deltas: `Reset` carried by `SetQuantToClock`, `Progress` via
    fall-through `EndLoop`, and the loop flag as a plain bool. */
module LindenElkTreeRep {
  import opened Std.Wrappers
  import LC = Chars
  import LG = Groups
  import LT = Tree
  import LS = Semantics
  import LW = WarblreRegExpRecord
  import R = RegElkRegex
  import RC = Charclasses
  import RB = Bytecode
  import CP = Compiler
  import RA = Anchors
  import T = LindenElkTranslate
  import NR = LindenElkNfaRep
  import AR = LindenElkActionsRep
  import PS = PikeSubset

  /** RegElk's `char_context` at a Linden `Input`'s position (forward scan):
      `prevchar` is the last-consumed character (head of the reversed prefix),
      `nextchar` the next unread one — what the VM's anchor check consults. */
  function CtxOf(inp: LC.Input): RA.char_context {
    RA.CharContext(if |inp.pref| == 0 then None else Some(inp.pref[0]),
                   if |inp.next| == 0 then None else Some(inp.next[0]))
  }

  /** THE anchor agreement, Input-level: RegElk's `is_satisfied` at the
      position's context coincides with Linden's `AnchorSatisfied` — under
      non-multiline, which is all the fixed `TheRer` flag record ever uses. */
  lemma AnchorAgreeInput(rer: LW.RegExpRecord, a: R.anchor, inp: LC.Input)
    requires !rer.multiline
    ensures RA.is_satisfied(a, CtxOf(inp), RA.Forward)
        <==> LS.AnchorSatisfied(rer, T.TrAnchor(a), inp)
  {
    if |inp.pref| > 0 { T.WordCharIff(rer, inp.pref[0]); }
    if |inp.next| > 0 { T.WordCharIff(rer, inp.next[0]); }
  }

  /** `t` is the backtracking tree corresponding to bytecode `code` running from `pc`
      at input `inp` with loop-exit flag `b` (`b` mirrors Linden's `CanExit`). One
      disjunct per bytecode shape — `tr_match`, `tr_jmp`, `tr_begin`, `tr_reset`,
      `tr_choice`, `tr_read`, `tr_progress`, `tr_open`, `tr_close`, `tr_readfail`,
      `tr_progressfail` — mirroring Linden's `TreeRep` inductive relation. */
  least predicate TreeRepRE(qm: AR.QMap, t: LT.Tree, code: RB.code, pc: nat, inp: LC.Input, b: bool)
  {
    // tr_match
    (NR.GetPcRE(code, pc) == Some(RB.Accept) && t == LT.Match)
    // tr_jmp
    || (exists nextpc: int :: NR.GetPcRE(code, pc) == Some(RB.Jmp(nextpc)) && nextpc >= 0
          && TreeRepRE(qm, t, code, nextpc as nat, inp, b))
    // tr_begin
    || (NR.GetPcRE(code, pc) == Some(RB.BeginLoop) && TreeRepRE(qm, t, code, pc + 1, inp, false))
    // tr_reset (RegElk: the SetQuantToClock marker carries the Reset node)
    || (t.GroupActionT? && t.g.Reset? && exists qid: int ::
          NR.GetPcRE(code, pc) == Some(RB.SetQuantToClock(qid, false))
          && qid in qm && qm[qid] == t.g.gl
          && TreeRepRE(qm, t.t, code, pc + 1, inp, b))
    // tr_choice (forward forks only: every compiled fork except the
    // do-while's is forward, and the direction split keeps determinism)
    || (t.Choice? && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && pcl as nat > pc && pcr as nat > pc
          && TreeRepRE(qm, t.t1, code, pcl as nat, inp, b)
          && TreeRepRE(qm, t.t2, code, pcr as nat, inp, b))
    // tr_plus: at a fork with a BACKWARD arm (only the do-while emits one),
    // the checked star iteration's Progress guard is consumed together with
    // the Choice - the guard passed because the NonNullable body consumed
    // (b == true is exactly that fact at the boolean layer)
    || (t.Progress? && t.t.Choice? && b == true && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc)
          && TreeRepRE(qm, t.t.t1, code, pcl as nat, inp, true)
          && TreeRepRE(qm, t.t.t2, code, pcr as nat, inp, true))
    // tr_plusfail: the dissolved guard at a backward fork fails when no
    // progress was made (mirrors tr_progressfail; unreachable for
    // NonNullable bodies, but the checked derivations state it)
    || (t == LT.Mismatch && b == false && exists pcl: int, pcr: int ::
          NR.GetPcRE(code, pc) == Some(RB.Fork(pcl, pcr)) && pcl >= 0 && pcr >= 0
          && (pcl as nat <= pc || pcr as nat <= pc))
    // tr_read
    || (t.Read? && exists ce, nextinp ::
          NR.GetPcRE(code, pc) == Some(RB.Consume(ce))
          && AR.ReadCharE(ce, inp) == Some((t.c, nextinp))
          && TreeRepRE(qm, t.t, code, pc + 1, nextinp, true))
    // tr_progress (EndLoop falls through in RegElk)
    || (t.Progress? && b == true
          && NR.GetPcRE(code, pc) == Some(RB.EndLoop)
          && TreeRepRE(qm, t.t, code, pc + 1, inp, true))
    // tr_open
    || (t.GroupActionT? && t.g.Open?
          && NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.start_reg(t.g.g as int)))
          && TreeRepRE(qm, t.t, code, pc + 1, inp, b))
    // tr_close
    || (t.GroupActionT? && t.g.Close?
          && NR.GetPcRE(code, pc) == Some(RB.SetRegisterToCP(CP.end_reg(t.g.g as int)))
          && TreeRepRE(qm, t.t, code, pc + 1, inp, b))
    // tr_anchorpass (zero-width: no input, group, or flag change; the
    // instruction's anchor translates to the tree node's)
    || (t.AnchorPass? && exists a: R.anchor ::
          NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
          && T.TrAnchor(a) == t.a
          && RA.is_satisfied(a, CtxOf(inp), RA.Forward)
          && TreeRepRE(qm, t.t, code, pc + 1, inp, b))
    // tr_anchorfail
    || (t == LT.Mismatch && exists a: R.anchor ::
          NR.GetPcRE(code, pc) == Some(RB.AnchorAssertion(a))
          && !RA.is_satisfied(a, CtxOf(inp), RA.Forward))
    // tr_readfail
    || (t == LT.Mismatch && exists ce ::
          NR.GetPcRE(code, pc) == Some(RB.Consume(ce)) && AR.ReadCharE(ce, inp) == None)
    // tr_progressfail
    || (t == LT.Mismatch && b == false && NR.GetPcRE(code, pc) == Some(RB.EndLoop))
  }

  // Determinism: at a fixed (pc, inp, b) the represented tree is unique.
  // (Port of Linden's TreeRepDeterm; the qm tie makes the Reset payload
  // unique, and SetRegisterToCP register parity separates open from close.)
  /** Determinism: at a fixed `(pc, inp, b)` the represented tree is unique (port of
      Linden's `TreeRepDeterm`). Relies on `qm` pinning the `Reset` payload and on
      `SetRegisterToCP` register parity (`start_reg`/`end_reg`) to separate `Open`
      from `Close`. */
  least lemma TreeRepDetermRE(qm: AR.QMap, code: RB.code, pc: nat, inp: LC.Input, b: bool, t1: LT.Tree, t2: LT.Tree)
    requires TreeRepRE(qm, t1, code, pc, inp, b)
    requires TreeRepRE(qm, t2, code, pc, inp, b)
    ensures t1 == t2
  {
    match NR.GetPcRE(code, pc)
    case Some(Accept) =>            // both tr_match
    case Some(Jmp(np)) =>           // both tr_jmp
      TreeRepDetermRE(qm, code, np as nat, inp, b, t1, t2);
    case Some(BeginLoop) =>         // both tr_begin
      TreeRepDetermRE(qm, code, pc + 1, inp, false, t1, t2);
    case Some(SetQuantToClock(qid, bb)) =>  // both tr_reset (only bb == false has a rule)
      match t1 {
        case GroupActionT(g1, tc1) =>
          match t2 {
            case GroupActionT(g2, tc2) =>
              assert g1 == LG.Reset(qm[qid]) && g2 == LG.Reset(qm[qid]);
              TreeRepDetermRE(qm, code, pc + 1, inp, b, tc1, tc2);
            case _ =>
          }
        case _ =>
      }
    case Some(Fork(pl, pr)) =>
      if pl >= 0 && pr >= 0 && pl as nat > pc && pr as nat > pc {
        // forward fork: both tr_choice
        match t1 {
          case Choice(ta1, tb1) =>
            match t2 {
              case Choice(ta2, tb2) =>
                TreeRepDetermRE(qm, code, pl as nat, inp, b, ta1, ta2);
                TreeRepDetermRE(qm, code, pr as nat, inp, b, tb1, tb2);
              case _ =>
            }
          case _ =>
        }
      } else if !b {
        // backward-arm fork at b == false: both tr_plusfail (Mismatch)
      } else {
        // backward-arm fork: both tr_plus (only representable at b == true)
        match t1 {
          case Progress(tc1) =>
            match t2 {
              case Progress(tc2) =>
                match tc1 {
                  case Choice(ta1, tb1) =>
                    match tc2 {
                      case Choice(ta2, tb2) =>
                        TreeRepDetermRE(qm, code, pl as nat, inp, true, ta1, ta2);
                        TreeRepDetermRE(qm, code, pr as nat, inp, true, tb1, tb2);
                      case _ =>
                    }
                  case _ =>
                }
              case _ =>
            }
          case _ =>
        }
      }
    case Some(Consume(ce)) =>       // tr_read (Some) or tr_readfail (None)
      match AR.ReadCharE(ce, inp) {
        case None =>                // both Mismatch
        case Some(pair) =>
          match t1 {
            case Read(c1, tc1) =>
              match t2 {
                case Read(c2, tc2) =>
                  TreeRepDetermRE(qm, code, pc + 1, pair.1, true, tc1, tc2);
                case _ =>
              }
            case _ =>
          }
      }
    case Some(EndLoop) =>           // tr_progress (b) or tr_progressfail (!b)
      if b {
        match t1 {
          case Progress(tc1) =>
            match t2 {
              case Progress(tc2) =>
                TreeRepDetermRE(qm, code, pc + 1, inp, true, tc1, tc2);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(SetRegisterToCP(reg)) =>  // tr_open (even reg) xor tr_close (odd reg)
      match t1 {
        case GroupActionT(g1, tc1) =>
          match t2 {
            case GroupActionT(g2, tc2) =>
              // parity: start_reg(g) == 2g, end_reg(g) == 2g+1 — an instruction
              // register is either an open for a unique gid or a close for a
              // unique gid, never both.
              assert g1.Open? ==> reg == 2 * (g1.g as int);
              assert g1.Close? ==> reg == 2 * (g1.g as int) + 1;
              assert g2.Open? ==> reg == 2 * (g2.g as int);
              assert g2.Close? ==> reg == 2 * (g2.g as int) + 1;
              assert g1 == g2;
              TreeRepDetermRE(qm, code, pc + 1, inp, b, tc1, tc2);
            case _ =>
          }
        case _ =>
      }
    case Some(AnchorAssertion(a)) =>  // tr_anchorpass (satisfied) or tr_anchorfail
      if RA.is_satisfied(a, CtxOf(inp), RA.Forward) {
        match t1 {
          case AnchorPass(a1, tc1) =>
            match t2 {
              case AnchorPass(a2, tc2) =>
                TreeRepDetermRE(qm, code, pc + 1, inp, b, tc1, tc2);
              case _ =>
            }
          case _ =>
        }
      }
    case Some(_) =>                 // CheckOracle/NegCheckOracle/WriteOracle/
                                    // CheckNullable/Fail:
                                    // no TreeRepRE rule — vacuous
    case None =>                    // vacuous
  }

  /** `PikeSubtree` congruences in their own verification conditions (the
      definitional unfolds are fuel-fragile inside the big inversion below). */
  lemma PikeSubtreeStep(t: LT.Tree)
    requires t.Read? || t.Progress? || t.GroupActionT? || t.AnchorPass?
    requires PS.PikeSubtree(t.t)
    ensures PS.PikeSubtree(t)
  {
    if t.Read? {
      assert t == LT.Read(t.c, t.t);
    } else if t.Progress? {
      assert t == LT.Progress(t.t);
    } else if t.GroupActionT? {
      assert t == LT.GroupActionT(t.g, t.t);
    } else {
      assert t == LT.AnchorPass(t.a, t.t);
    }
  }

  lemma PikeSubtreeChoice(t: LT.Tree)
    requires t.Choice? && PS.PikeSubtree(t.t1) && PS.PikeSubtree(t.t2)
    ensures PS.PikeSubtree(t)
  {
    assert t == LT.Choice(t.t1, t.t2);
  }

  lemma PikeSubtreeLeaf(t: LT.Tree)
    requires t.Match? || t.Mismatch?
    ensures PS.PikeSubtree(t)
  {
    if t.Match? {
      assert t == LT.Match;
    } else {
      assert t == LT.Mismatch;
    }
  }

  // Represented trees are pike-shaped: no rule produces a lookaround or
  // backreference node — what the PikeTree machine's invariant needs of the
  // checked tree it is initialized with.
  /** Represented trees are `PikeSubtree`s: no `TreeRepRE` rule produces
      `LK`/`LKFail`/`ReadBackRef` nodes. */
  least lemma TreeRepPikeSubtree(qm: AR.QMap, t: LT.Tree, code: RB.code, pc: nat, inp: LC.Input, b: bool)
    requires TreeRepRE(qm, t, code, pc, inp, b)
    ensures PS.PikeSubtree(t)
  {
    match NR.GetPcRE(code, pc)
    case Some(Accept) =>            // Match
      PikeSubtreeLeaf(t);
    case Some(Jmp(np)) =>
      TreeRepPikeSubtree(qm, t, code, np as nat, inp, b);
    case Some(BeginLoop) =>
      TreeRepPikeSubtree(qm, t, code, pc + 1, inp, false);
    case Some(SetQuantToClock(qid, bb)) =>
      match t {
        case GroupActionT(g, tc) =>
          TreeRepPikeSubtree(qm, tc, code, pc + 1, inp, b);
          PikeSubtreeStep(t);
        case _ =>
      }
    case Some(Fork(pl, pr)) =>
      if pl >= 0 && pr >= 0 && pl as nat > pc && pr as nat > pc {
        match t {
          case Choice(t1, t2) =>
            TreeRepPikeSubtree(qm, t1, code, pl as nat, inp, b);
            TreeRepPikeSubtree(qm, t2, code, pr as nat, inp, b);
            PikeSubtreeChoice(t);
          case _ =>
        }
      } else if b {
        match t {
          case Progress(tc) =>
            match tc {
              case Choice(t1, t2) =>
                TreeRepPikeSubtree(qm, t1, code, pl as nat, inp, true);
                TreeRepPikeSubtree(qm, t2, code, pr as nat, inp, true);
                PikeSubtreeChoice(tc);
                PikeSubtreeStep(t);
              case _ =>
            }
          case _ =>
        }
      } else {
        assert t == LT.Mismatch;   // only tr_plusfail matches
        PikeSubtreeLeaf(t);
      }
    case Some(Consume(ce)) =>
      match AR.ReadCharE(ce, inp) {
        case None =>
          assert t == LT.Mismatch;   // only tr_readfail matches
          PikeSubtreeLeaf(t);
        case Some(pair) =>
          match t {
            case Read(c, tc) =>
              TreeRepPikeSubtree(qm, tc, code, pc + 1, pair.1, true);
              PikeSubtreeStep(t);
            case _ =>
          }
      }
    case Some(EndLoop) =>
      if b {
        match t {
          case Progress(tc) =>
            TreeRepPikeSubtree(qm, tc, code, pc + 1, inp, true);
            PikeSubtreeStep(t);
          case _ =>
        }
      } else {
        assert t == LT.Mismatch;   // only tr_progressfail matches
        PikeSubtreeLeaf(t);
      }
    case Some(SetRegisterToCP(reg)) =>
      match t {
        case GroupActionT(g, tc) =>
          TreeRepPikeSubtree(qm, tc, code, pc + 1, inp, b);
          PikeSubtreeStep(t);
        case _ =>
      }
    case Some(AnchorAssertion(a)) =>
      if RA.is_satisfied(a, CtxOf(inp), RA.Forward) {
        match t {
          case AnchorPass(a2, tc) =>
            TreeRepPikeSubtree(qm, tc, code, pc + 1, inp, b);
            PikeSubtreeStep(t);
          case _ =>
        }
      } else {
        assert t == LT.Mismatch;   // only tr_anchorfail matches
        PikeSubtreeLeaf(t);
      }
    case Some(_) =>                 // no rule — vacuous
    case None =>                    // vacuous
  }
}
