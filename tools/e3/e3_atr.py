#!/usr/bin/env python3
"""Extract ActionsTreeRepFRE{,Nested}'s Quantified arm into ATR_QuantMin/NN/Star{,Nested} helpers (the file's ATR_* convention)."""
import re, sys
P='/home/aaron/code/Linden-Dafny-l4/linden-equiv/src/Equiv/ActionsTreeRepRE.dfy'
L=open(P).read().split('\n')
def find(pred, start, end=None):
    for i in range(start, end or len(L)):
        if pred(L[i]): return i+1
    raise SystemExit('anchor not found from %d' % start)
def dedent(lines, n): return [l[n:] if l.startswith(' '*n) else l.lstrip() if l.strip() else '' for l in lines]
out=[]; cursor=1   # 1-based line cursor over L
for sfx in ['', 'Nested']:
    par=find(lambda l: l.startswith('  lemma {:isolate_assertions} ActionsTreeRepFRE%s(' % sfx), cursor-1)
    tmpl=find(lambda l: l.startswith('  lemma ATR_Group%s(' % sfx), par)
    tclose=find(lambda l: l=='  {', tmpl-1)
    header=L[tmpl-1:tclose-1]
    cs=find(lambda l: l=='        case Quantified(greedy, min, delta, r1) => {', par)
    gidl=cs+1; assert L[gidl-1].strip()=='var gidl := L.DefGroups(r1);'
    mif=find(lambda l: l=='          if min > 0 {', cs); mret=find(lambda l: l=='            return;', mif); assert L[mret]=='          }'
    nif=find(lambda l: l=='          if delta.NN? {', mret); nret=find(lambda l: l=='            return;', nif); assert L[nret]=='          }'
    star=nret+2; assert L[star-1].strip().startswith('assert min == 0 && delta == LN.Inf;'), L[star-1]
    cclose=find(lambda l: l=='        }', star); assert 'case Group' in L[cclose]
    def helper(name, guard, body_lines):
        h=[l.replace('ATR_Group%s(' % sfx, name+'(').replace('gid: LG.GroupId, r1: L.Regex', 'greedy: bool, min: nat, delta: LN.NoI, r1: L.Regex').replace('L.Group(gid, r1)', 'L.Quantified(greedy, min, delta, r1)') for l in header]
        h.insert(len(h)-3, '    requires %s' % guard)   # before the two ensures + decreases
        assert h[-1].strip().startswith('decreases') and h[-4].strip().startswith('requires'), h[-4:]
        pro=['    assert acts == [acts[0]] + cont;', '    EL.PikeLkActions%sConsIff(acts[0], cont);' % ('Rec' if sfx else ''), '    var gidl := L.DefGroups(r1);']
        return ['  /** (2026-08-29 E3) the `Quantified` arm of `ActionsTreeRepFRE%s`, %s — extracted from a 350-line' % (sfx, guard),
                '      case so each branch is its own VC (the parent no longer needs `{:isolate_assertions}`). */'] + h + ['  {'] + pro + dedent(body_lines, 8) + ['  }', '']
    hMin=helper('ATR_QuantMin'+sfx, 'min > 0', L[mif:mret-1])
    hNN=helper('ATR_QuantNN'+sfx, 'min == 0 && delta.NN?', L[nif:nret-1])
    hStar=helper('ATR_QuantStar'+sfx, 'min == 0 && delta == LN.Inf', L[star-1:cclose-1])
    args='rer, qm, acts, cont, code, pc, pcmid, inp, b, t, n, greedy, min, delta, r1, S'
    dispatch=['        case Quantified(greedy, min, delta, r1) => {',
              '          if min > 0 { tstar := ATR_QuantMin%s(%s); }' % (sfx, args),
              '          else if delta.NN? { tstar := ATR_QuantNN%s(%s); }' % (sfx, args),
              '          else { tstar := ATR_QuantStar%s(%s); }' % (sfx, args),
              '        }']
    out += L[cursor-1:par-1] + hMin + hNN + hStar
    parent=L[par-1:cs-1] + dispatch + L[cclose:]   # rest of file from the case close on... but only up to the next twin: handle by cursor
    # emit parent header..case-start, dispatch, then continue from cclose+1 (the `case Group` line) with the cursor
    out += [L[par-1].replace('{:isolate_assertions} ','')] + L[par:cs-1] + dispatch
    cursor=cclose+1
out += L[cursor-1:]
open(P,'w').write('\n'.join(out)); print('written; helpers:', [n for n in ('ATR_QuantMin','ATR_QuantNN','ATR_QuantStar','ATR_QuantMinNested','ATR_QuantNNNested','ATR_QuantStarNested') if ('lemma '+n+'(') in '\n'.join(out)])
