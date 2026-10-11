# The cyclic/open ascent dichotomy, formalised — 2026-10-11 (LEAN slot)

**File:** `TworowD4Kernel/CyclicAscent.lean`, namespace `TworowD4Kernel.CyclicAscent`.
**Status:** sorry-free, 15 declarations, standard three axioms only.

## What is proved

A binary word is a map to `Bool`; an *ascent* is a position reading `false` whose successor
reads `true`. Two readings of "successor":

| | index type | ascent-free locus | count |
|---|---|---|---|
| cyclic | `ZMod h` | **constant** words | **2**, for every `h ≥ 1` |
| open | `Fin (n+1)` | **antitone** words `1^a 0^{h-a}` | **h + 1 = n + 2** |

- `ZMod.const_of_succ_le` — the content. A word on `ZMod h` that never increases along the
  cyclic successor is *constant*, not merely antitone.
- `ZMod.exists_ascent_of_not_const` — contrapositive: a non-constant cyclic word has an ascent.
- `ZMod.ascentFree_iff_const`, `ZMod.card_ascentFree` (= 2).
- `Fin.ascentFree_iff_antitone`, `Fin.ascentFree_iff_exists_threshold`, `Fin.card_ascentFree`
  (= n + 2).
- `card_ascentFree_lt` — strictly more open witnesses than cyclic ones, for every `h ≥ 2`.

## Two things the session brief got wrong, and one it got right

**Right:** it predicted declaration 2 would be a wrapper around something Mathlib already has,
and that the cyclic case would be the real work. Both held.

**Wrong 1 — the route.** The brief named `List.Chain' (· ≥ ·)` and a sorted-descending-list
reading for the open case. The actual one-line input is `Fin.antitone_iff_succ_le`
(`Mathlib.Order.Fin.Basic`), whose statement
`Antitone f ↔ ∀ i : Fin n, f i.succ ≤ f i.castSucc` is *literally* the local no-ascent
condition, with no list in sight. No `List` lemma is used anywhere in the file.

**Wrong 2 — the difficulty of the cyclic case.** The brief budgeted most of the slot for
declaration 1 and expected `Nat.find` / strong induction / `Finset.exists_min_image` — "walk
forward from a `false` to the first `true`, its predecessor is the ascent". That walk is never
needed. Taking the contrapositive first turns the whole thing into eight lines:

> no ascent ⟺ `θ (i+1) ≤ θ i` for all `i`. Iterate: `θ (i + n) ≤ θ i` for every **natural**
> `n`. And in `ZMod h` with `h ≥ 1`, `1` generates — every `j` is `i + n` — so the inequality
> holds between *every ordered pair in both directions*, and `Bool.le_antisymm` collapses the
> word to a constant.

The pigeonhole walk was an artifact of attacking the existential form directly. Proving the
*stronger* statement (constant, not just "has an ascent") is what made it easy; `exists_natCast_add`
is the only cyclic-specific input in the file.

## Why `NeZero h` is necessary — about the statement, not about my proof

`not_const_of_succ_le_zmod_zero`: `ZMod 0` is `ℤ`, where `1` does not generate.
`θ i := decide (i < 0)` steps down along the successor everywhere and is not constant. So
`const_of_succ_le` is **false** at `h = 0`. That is a counterexample, not an `exit 1`.

Likewise `h ≥ 2` is necessary for the strict gap and not an artifact:
`card_ascentFree_eq_at_one` proves both counts equal `2` at `h = 1`, where the single letter is
its own cyclic successor and the two readings coincide.

## Verification actually run

- `#print axioms` on all 15 declarations: standard three only. `not_ascent_iff` depends on
  **none** (it is `decide`). Note the output was **17 lines** for **15 records** — one axiom
  list wraps across three lines — so a `grep -c` here would have read 12.
- **Planted-sorry propagation.** `sorry` at the dependency root `not_ascent_iff`:
  **9 of 15** declarations go `sorryAx`-contaminated, **6 correctly spared**
  (`exists_natCast_add`, `le_of_natCast_add`, `const_of_succ_le`, `thr_injective`,
  `not_const_of_succ_le_int`, `not_const_of_succ_le_zmod_zero`). The spared set audits the
  docstring for free: `const_of_succ_le` does **not** route through the ascent↔inequality
  translation, confirming that layer is cosmetic and the rigidity argument is independent of it.
  Output grew 17 → 30 lines while the record count stayed 15.
- **Eight brute-force `decide` checks** over the whole function space at `h = 1,2,3,4`, sharing
  no lemma with the proofs — only the `Finset` definitions. Cyclic: `2,2,2,2`. Open: `2,3,4,5`.
- **Negative control on those checks:** asserting the wrong count (open `h=3` as 5, cyclic
  `h=3` as 3) produces **2 errors / 2 arms**. The `decide` instrument fires.

## Provenance

Combinatorial half of the Q410 theorem,
`projects/proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex` — no cyclically `ψ`-graded
weight carries Warnaar's determinant. Korff's index set is arXiv:1110.6356 Def 5.5. The
companion `ord_{t=1}` count is **not** formalised here; see the honest scope note in the
registry child node `cyclic-open-dichotomy-formalised`.
