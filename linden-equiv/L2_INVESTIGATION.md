# L2 Investigation — how to get backward execution

Status: **design analysis, no proofs written.** Every claim marked (verified)
was read out of the source at the cited location or checked numerically;
claims marked (inferred) are judgement calls that a prototype would settle.

The campaign doc (`LOOKAROUND_CAMPAIGN.md` §4) framed L2 as a two-way choice:

> Sub-choice: parameterize the rep/sim by direction (mechanical, wide) vs.
> prove the reversal once at the tree level and keep the pipeline forward
> (preferable if tractable). The big one.

This investigation finds a **third option that neither branch of that choice
anticipated**, and recommends it: reverse the *string*, not the regex, and
reuse the forward machinery wholesale.

---

## 1. What L2 actually needs

The direction matrix, read out of `Compiler.dfy` and `Interpreter.dfy`
(verified — `oracle_regex` Compiler.dfy:255, `capture_regex` Compiler.dfy:268,
`oracle_direction` Interpreter.dfy:38, `capture_direction` Interpreter.dfy:49):

| flavour | oracle build regex | oracle dir | capture regex | capture dir |
|---|---|---|---|---|
| Lookbehind | `lazy_prefix(remove_capture(l))` | Forward | `reverse_regex(l)` | **Backward** |
| Lookahead | `lazy_prefix(reverse_regex(remove_capture(l)))` | **Backward** | `l` | Forward |

Two consequences that matter for planning:

1. **L2 = a backward ORACLE build.** For capture-free lookaheads, the only new
   direction work is the build sweep. Nothing else about lookaheads is new —
   the gate instructions (`CheckOracle`/`NegCheckOracle`) the Pike simulation
   consumes are the same ones L1 already taught it to handle.

2. **L3a is nearly free once L2 lands** (and this is the reverse of the
   intuition): a lookAHEAD's capture pass runs **Forward**, which the existing
   forward-only stack already supports. It is the lookBEHIND capture pass that
   runs Backward. So the ladder's natural order is L2 → L3a → L3b, not
   L3 as one rung.

---

## 2. Where the forward assumption actually lives

- `ReachF` (`OracleReach.dfy:76`) has **no direction parameter**, and the
  forwardness is *structural*, not a hypothesis: the consume clause steps
  `cp - 1`, and `ReachFGeStart` (line 95) proves `cp >= cp0`. (verified)
  `OracleReach.dfy` is **1080 lines**.
- `PikeSimRE.dfy:2426` — the simulation correctness carries
  `requires dir == LAnc.Forward`. (verified)
- `NfaRepRE`, `ActionsRepRE`, `TreeRepRE`, `ActionsTreeRepRE` — **zero**
  mentions of direction. They are forward by construction. (verified by grep)
- `FBuildOracleCorrect` (`OracleBuild.dfy:317`) is already *nesting*-agnostic
  and threads `dir` from `oracle_direction`, but rests on the forward sweep
  layer. (verified)

So "make the stack bidirectional" means, at minimum, re-proving the 1080-line
reachability layer with flipped arithmetic, plus the sim.

---

## 3. Route B — the string-reversal isomorphism (recommended)

**Claim.** A Backward run of bytecode `c` over `str` is *isomorphic* to a
Forward run of `c` over `reverse(str)` under the position mirror
`cp ↦ |str| - cp`, provided `BeginInput`/`EndInput` are swapped in `c`.

### Evidence

`cp_context(cp, str, dir)` (Interpreter.dfy:217) already **swaps prev/next**
for `Backward`:

```dafny
case Forward  => CharContext(prevop, nextop)
case Backward => CharContext(nextop, prevop)
```

and `init_cp(Backward, n) = n` (Interpreter.dfy:70). Checked numerically over
`"abcd"`: the Backward-at-`cp` context and the Forward-at-`|str|-cp` context
over the reversed string are **identical at every position**, and consumption
agrees — Backward at `cp` reads `str[cp-1]` and moves to `cp-1`; Forward at
`|str|-cp` reads `rstr[|str|-cp]` (the same character) and moves to
`|str|-(cp-1)`, the mirror. (verified numerically)

**Anchors are the one wrinkle, and they are well-behaved.** `is_satisfied`
(`Anchors.dfy:46`) swaps `BeginInput`/`EndInput` on `Backward`. Since the
*context* is already the same pair under the mirror, this means precisely:

> Backward-`BeginInput` ≡ Forward-`EndInput` on the same context.

So the isomorphism needs a `Begin ↔ End` swap applied to the bytecode. This is
consistent with `reverse_regex` **not** touching anchors
(`Regex.dfy:243`, `case Re_anchor(a) => Re_anchor(a)` — verified): the engine
delegates anchor handling to `is_satisfied`'s `dir`, so a reversal that also
changed the string has to make the swap explicit.

### Why this is the best route

- **One theorem instead of ~1080 lines re-proved.** Every existing forward
  lemma lifts, rather than being duplicated with flipped arithmetic.
- **It preserves thread priority.** The bytecode is unchanged (modulo the
  anchor swap), so the Pike VM's thread order — the thing that decides which
  leaf wins — is identical on both sides. This is why the route also unblocks
  **L3's engine side**, where the priority order is exactly what a
  capture-level correspondence must preserve. (inferred, but it follows from
  the bytecode being the same object)
- It sidesteps the tree-level reversal entirely, and with it the greedy/lazy
  priority question that made Route C look risky.

### Open questions a prototype must settle

1. **Oracle view indexing.** The build *writes* columns at mirrored positions,
   so the resulting `OracleView` comes out reversed and needs un-mirroring in
   the final statement. For nested lookarounds the build also *reads* inner
   columns, which would then need mirroring on read. Expressible, but it is
   real bookkeeping. (inferred)
2. **The anchor-swap transform needs its own rep lemma** — that
   `swap_anchors(c)` still `NfaRepRE`-represents the swapped regex.
3. **`cdns` (the condition table)** — not examined for direction assumptions.
4. **Recursion structure.** `FFindMatch`'s `decreases` is `|str| - s.cp`
   forward and `s.cp` backward; the isomorphism must be stated so those line
   up. (verified the decreases differs; the fix is inferred)

---

## 4. Routes rejected

**Route A — parameterize the sweep/sim by direction.** Honest fallback, and it
does work. Cost: `ReachF` and its ~1080-line lemma family gain a `dir` and
every arithmetic step flips (`cp-1` ↔ `cp+1`, `cp >= cp0` ↔ `cp <= cp0`), plus
`PikeSimRE`'s `dir == Forward`. Wide, mechanical, high nuisance-failure rate.
Choose this only if Route B's prototype fails.

**Route C — tree-level reversal (`Backward ∘ reverse_regex ≡ Forward`).** The
doc's preferred option. The boolean/oracle half is fine, but for captures the
statement must identify the *highest-priority* leaf, and it is not clear
greedy/lazy priority survives regex reversal. Route B avoids the question by
never reversing the regex — it reverses the string and keeps the program.

---

## 5. Recommended next step

Prototype Route B on the smallest possible probe, in this order:

1. `FAdvanceEpsilon` — the epsilon closure, which does **not** move `cp`.
   State: backward closure over `str` at `cp` ≅ forward closure over
   `reverse(str)` at `|str|-cp`, with anchors swapped. If the context
   correspondence is as exact as §3 says, this should be close to routine.
2. One `FConsume` step — the position mirror is the only new content.
3. If both land, the full `FFindMatch` isomorphism is an induction over the
   same measure, and the oracle-view un-mirroring (§3, open question 1) is the
   remaining real work.

If step 1 does not go through cleanly, that is the signal to fall back to
Route A and budget for the wide sweep.
