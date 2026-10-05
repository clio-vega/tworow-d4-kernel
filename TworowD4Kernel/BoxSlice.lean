/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ParityObstruction

/-!
# `Lemma boxslice`: a box slice is M-convex, with *every* partner admissible

Formalisation of **Lemma `boxslice`** (Step A of the route to (Q)) of
`projects/proofs/2026-10-04-c3-Q-lorentzian.tex`, registry node
`Q-stepA-bead-support-box-slice` in `proofs/registry/cylindric-lorentzian.json`.

The node's statement:

> for integers `p ≤ q` and `d`, `B = {α ∈ ℤⁿ : p ≤ α ≤ q, ∑ αᵢ = d}` is M-convex, and
> **every** `j` with `α_j < β_j` is an admissible exchange partner — each of the four
> needed inequalities comes from one strict inequality between `α, β` plus one box
> constraint, each spent once.  Applied with `n = 3`, `p = (0,0,0)`, `q = (h,h,h−l)`,
> `d = h` this gives `supp P̃^{(l,h)}` M-convex.

## What was already here, and what this file adds

**Finding (2026-10-05 c3).**  The *all-partners* content is **not new**.  It is
`SublevelMConvex.ex_box_sum` (`SublevelMConvex.lean:170`), whose docstring already says
"For **every** `l` with `y l < y' l` the surgered vector stays in the box and on the
hyperplane … This is already the statement that a box meets a hyperplane M-convexly."
That lemma was proved on 2026-10-04 as the easy half of `thm:M`, in the same file as the
`ex`/`sum_ex` vocabulary this file was briefed to reuse.  The brief for this session
asserted the all-partners strengthening "is genuinely not `mConvex_inS`" — true, but it
*is* `ex_box_sum`, and the brief checked only `mConvex_inS`.

What is genuinely added here, and why it is worth adding:

1. **Hypothesis weakening.**  `ex_box_sum` assumes `InS P Q σ j` — box *and* the defect
   bound `kfun y ≤ j` — and then discards the bound (`⟨hyP, hyQ, hyS, -⟩`).  So the box
   slice statement was only available wrapped in the sublevel machinery (`kfun`,
   `negPart`), which it does not use.  `InBox` mentions neither.  This is what lets the
   Lean side be cited by (Q) Step A without dragging in `thm:M`.
2. **A named predicate** `InBox`, so `MConvex {y | InBox P Q σ y}` is statable at all.
   `mConvex_boxSlice` did not exist in any form.
3. **The intended instance** `beadSupport` (`m = 3`, `P = 0`, `Q = (h,h,h−l)`, `σ = h`),
   which is where the Lean side meets the `.tex` side.

`lem:constsum` of the same `.tex` ("an M-convex set has constant coordinate sum") is
likewise **already formalised**, as `ParityObstruction.sum_eq_of_mConvex`
(`ParityObstruction.lean:223`); it is not re-proved here.

## The node's accounting, checked

The node says "each of the four needed inequalities comes from one strict inequality
between `α, β` plus one box constraint, each spent once."  Proved directly in
`boxSlice_all_partners`, the four touched-coordinate goals consume:

| goal              | strict ineq. | box constraint |
|-------------------|--------------|----------------|
| `P i ≤ y i − 1`   | `hi`         | `P i ≤ y' i`   |
| `y i − 1 ≤ Q i`   | —            | `y i ≤ Q i`    |
| `P l ≤ y l + 1`   | —            | `P l ≤ y l`    |
| `y l + 1 ≤ Q l`   | `hl`         | `y' l ≤ Q l`   |

So two of the four need a strict inequality and two need only `y`'s own box constraint:
the accounting is **correct in the direction that matters** (nothing beyond one strict
plus one box is consumed, and no hypothesis instance is used twice) and mildly
over-stated — two goals are cheaper than claimed.  Each of the six hypothesis instances
in the table is spent exactly once; `hi` and `hl` are each spent a second time, together,
only to derive `i ≠ l`.  No goal needed more than `omega` on top of its row.

## Conventions

`ex i l y` is the paper's `α − eᵢ + e_l`, reused verbatim from `SublevelMConvex`.
`MConvex` is `ParityObstruction.MConvex`, Murota's one-sided B-EXC⁻.
-/

namespace TworowD4Kernel.BoxSlice

open Finset SublevelMConvex ParityObstruction

/-- `y ∈ B = { y ∈ ∏_c [P_c, Q_c] : ∑_c y_c = σ }`, the node's
`{α ∈ ℤⁿ : p ≤ α ≤ q, ∑ αᵢ = d}`.

This is `SublevelMConvex.InS` with its fourth conjunct `kfun y ≤ j` deleted — *not*
weakened, deleted: `negPart` and `kfun` do not occur. -/
def InBox {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ) (y : Fin m → ℤ) : Prop :=
  (∀ c, P c ≤ y c) ∧ (∀ c, y c ≤ Q c) ∧ (∑ c, y c = σ)

/-! ### The all-partners exchange, proved directly -/

/-- **Lemma `boxslice`, all-partners half.**  For `y, y'` in the box slice and *any* pair
`i, l` with `y' i < y i` and `y l < y' l`, the surgered vector `y − eᵢ + e_l` is again in
the box slice.  The exchange partner is not merely existential: every index that moves the
right way works.

Proved directly from `InBox`, consuming exactly the six hypothesis instances tabulated in
the module docstring.  Cf. `SublevelMConvex.ex_box_sum`, which is this statement under the
stronger hypothesis `InS P Q σ j`; `boxSlice_all_partners_via_exBoxSum` below derives this
one from that one. -/
theorem boxSlice_all_partners {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ)
    {y y' : Fin m → ℤ} (hy : InBox P Q σ y) (hy' : InBox P Q σ y')
    {i l : Fin m} (hi : y' i < y i) (hl : y l < y' l) :
    InBox P Q σ (ex i l y) := by
  obtain ⟨hyP, hyQ, hyS⟩ := hy
  obtain ⟨hyP', hyQ', -⟩ := hy'
  have hil : i ≠ l := by rintro rfl; omega
  refine ⟨?_, ?_, by rw [sum_ex]; exact hyS⟩
  · intro c
    rcases eq_or_ne c i with rfl | hci
    · rw [ex_apply_self y hil]
      have := hyP' c; omega
    · rcases eq_or_ne c l with rfl | hcl
      · rw [ex_apply_other y hil]
        have := hyP c; omega
      · rw [ex_apply_off y hci hcl]; exact hyP c
  · intro c
    rcases eq_or_ne c i with rfl | hci
    · rw [ex_apply_self y hil]
      have := hyQ c; omega
    · rcases eq_or_ne c l with rfl | hcl
      · rw [ex_apply_other y hil]
        have := hyQ' c; omega
      · rw [ex_apply_off y hci hcl]; exact hyQ c

/-! ### The same statement, derived from `ex_box_sum`

`ex_box_sum` needs a defect bound `kfun y ≤ j` for a *common* `j`.  Laundering it away is
the whole content of the weakening: take `j := max (kfun y) (kfun y')`, which bounds both
by construction, so the hypothesis is satisfiable for free and carries no information. -/

/-- `InBox` upgrades to `InS` at any `j` bounding the defect. -/
lemma inS_of_inBox {m : ℕ} {P Q : Fin m → ℤ} {σ j : ℤ} {y : Fin m → ℤ}
    (hy : InBox P Q σ y) (hj : kfun y ≤ j) : InS P Q σ j y :=
  ⟨hy.1, hy.2.1, hy.2.2, hj⟩

/-- `InS` forgets down to `InBox`. -/
lemma inBox_of_inS {m : ℕ} {P Q : Fin m → ℤ} {σ j : ℤ} {y : Fin m → ℤ}
    (hy : InS P Q σ j y) : InBox P Q σ y :=
  ⟨hy.1, hy.2.1, hy.2.2.1⟩

/-- `boxSlice_all_partners` again, this time *derived* from `SublevelMConvex.ex_box_sum`
by saturating its defect bound.  Statement identical to `boxSlice_all_partners` — the two
proofs are independent (one reads the box constraints directly, one routes through
`thm:M`'s easy half).  On why no "they agree" theorem follows, see the note below. -/
theorem boxSlice_all_partners_via_exBoxSum {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ)
    {y y' : Fin m → ℤ} (hy : InBox P Q σ y) (hy' : InBox P Q σ y')
    {i l : Fin m} (hi : y' i < y i) (hl : y l < y' l) :
    InBox P Q σ (ex i l y) := by
  obtain ⟨-, h1, h2, h3⟩ :=
    ex_box_sum (j := max (kfun y) (kfun y'))
      (inS_of_inBox hy (le_max_left _ _)) (inS_of_inBox hy' (le_max_right _ _)) hi hl
  exact ⟨h1, h2, h3⟩

/-! **No "the two proofs agree" theorem is stated here, and that is deliberate.**  I wrote
one (`boxSlice_all_partners = boxSlice_all_partners_via_exBoxSum`) and it closed by `rfl`
on the first build — because `InBox` is a `Prop` and Lean has *definitional proof
irrelevance*, so **any** two proofs of **any** proposition are equal by `rfl`.  Such a
theorem cannot fail and therefore checks nothing; it would have been a vacuous control
banked as corroboration (`memory: a-pass-count-does-not-report-the-rank-of-the-test`).
What the two routes genuinely give is two independent *derivations* of one statement — the
statement is shared by inspection of the two signatures above, which is not a theorem. -/

/-! ### M-convexity of the box slice, by two routes -/

/-- **Lemma `boxslice`.**  A box slice is M-convex.  From the all-partners exchange plus
`exists_lt_of_sums_eq` (some coordinate must move the other way, since the sums agree). -/
theorem mConvex_boxSlice {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ) :
    MConvex {y : Fin m → ℤ | InBox P Q σ y} := by
  intro y hy y' hy' i hi
  obtain ⟨l, hl⟩ := exists_lt_of_sums_eq (by rw [hy.2.2, hy'.2.2]) hi
  exact ⟨l, hl, boxSlice_all_partners P Q σ hy hy' hi hl⟩

/-- On a box with lower bound `P`, the defect is bounded by `∑_c (−P_c)_+` outright, since
`negPart` is antitone.  So the sublevel constraint of `InS` at that `j` is **vacuous**. -/
lemma kfun_le_of_lower {m : ℕ} {P : Fin m → ℤ} {y : Fin m → ℤ} (hP : ∀ c, P c ≤ y c) :
    kfun y ≤ ∑ c, SublevelMConvex.negPart (P c) :=
  Finset.sum_le_sum fun c _ => SublevelMConvex.negPart_le_negPart_of_le (hP c)

/-- The box slice **is** a sublevel set, at the saturating `j`. -/
theorem inBox_iff_inS_saturated {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ) (y : Fin m → ℤ) :
    InBox P Q σ y ↔ InS P Q σ (∑ c, SublevelMConvex.negPart (P c)) y :=
  ⟨fun hy => inS_of_inBox hy (kfun_le_of_lower hy.1), inBox_of_inS⟩

/-- `mConvex_boxSlice` again, derived from `ParityObstruction.mConvex_inS` with the defect
bound saturated so that it is vacuous.  Second, independent route: this one never looks at
a box constraint, it rewrites the set and invokes `thm:M`. -/
theorem mConvex_boxSlice_via_inS {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ) :
    MConvex {y : Fin m → ℤ | InBox P Q σ y} := by
  have hset : {y : Fin m → ℤ | InBox P Q σ y}
      = {y : Fin m → ℤ | InS P Q σ (∑ c, SublevelMConvex.negPart (P c)) y} := by
    ext y; exact inBox_iff_inS_saturated P Q σ y
  rw [hset]
  exact mConvex_inS P Q σ (∑ c, SublevelMConvex.negPart (P c))

/-- The constant-coordinate-sum consequence, instantiated for the box slice.  This is
`ParityObstruction.sum_eq_of_mConvex` (= the `.tex`'s `lem:constsum`, already formalised
2026-10-04) applied to `mConvex_boxSlice`; it is *not* a new proof.  Recorded here only so
the two halves of the registry node meet in one place. -/
theorem sum_eq_of_inBox {m : ℕ} (P Q : Fin m → ℤ) (σ : ℤ) {y y' : Fin m → ℤ}
    (hy : InBox P Q σ y) (hy' : InBox P Q σ y') : ∑ c, y c = ∑ c, y' c :=
  sum_eq_of_mConvex (mConvex_boxSlice P Q σ) hy hy'

/-! ### The intended instance: `supp P̃^{(l,h)}`

`m = 3`, `P = (0,0,0)`, `Q = (h, h, h − l)`, `σ = h`.  This is the bead-support box slice
of Step A of (Q) (`2026-10-04-c3-Q-lorentzian.tex`, node
`Q-stepA-bead-support-box-slice`), the point at which the Lean side meets the `.tex`. -/

/-- The upper corner `(h, h, h − l)` of the bead-support box. -/
def beadQ (l h : ℤ) : Fin 3 → ℤ := ![h, h, h - l]

/-- `supp P̃^{(l,h)} = {α ∈ ℤ³ : 0 ≤ α ≤ (h,h,h−l), ∑ αᵢ = h}`. -/
def beadSupport (l h : ℤ) (y : Fin 3 → ℤ) : Prop := InBox 0 (beadQ l h) h y

/-- **Step A of (Q), the instance actually consumed.**  The bead support is M-convex. -/
theorem mConvex_beadSupport (l h : ℤ) :
    MConvex {y : Fin 3 → ℤ | beadSupport l h y} :=
  mConvex_boxSlice 0 (beadQ l h) h

/-- All-partners, on the instance. -/
theorem beadSupport_all_partners (l h : ℤ) {y y' : Fin 3 → ℤ}
    (hy : beadSupport l h y) (hy' : beadSupport l h y')
    {i j : Fin 3} (hi : y' i < y i) (hj : y j < y' j) :
    beadSupport l h (ex i j y) :=
  boxSlice_all_partners 0 (beadQ l h) h hy hy' hi hj

/-! ### Non-vacuity and the negative control

`memory: a theorem whose hypotheses are never satisfiable type-checks perfectly`, and
`memory: a-pass-count-does-not-report-the-rank-of-the-test`.  Both guards are on the
*instance*, not on the general box, because the instance is the thing that could be empty:
`beadQ` has a coordinate `h − l` that goes negative for `l > h`. -/
section Witness

/-- `(1,1,1) ∈ supp P̃^{(0,3)}`: hypotheses satisfiable. -/
lemma bead_mem_a : beadSupport 0 3 ![1, 1, 1] := by
  refine ⟨?_, ?_, ?_⟩ <;> [skip; skip; decide] <;>
    intro c <;> fin_cases c <;> simp [beadQ]

/-- `(2,1,0) ∈ supp P̃^{(0,3)}`. -/
lemma bead_mem_b : beadSupport 0 3 ![2, 1, 0] := by
  refine ⟨?_, ?_, ?_⟩ <;> [skip; skip; decide] <;>
    intro c <;> fin_cases c <;> simp [beadQ]

/-- **Non-vacuity witness.**  The hypotheses of `beadSupport_all_partners` are satisfiable
at `l = 0, h = 3` with `i = 0, j = 2`, and the move it licenses is genuine: it carries
`(2,1,0)` to `(1,1,1)`, not to itself. -/
theorem beadSupport_all_partners_witness :
    beadSupport 0 3 (ex 0 2 ![2, 1, 0]) ∧ ex (0 : Fin 3) 2 ![2, 1, 0] = ![1, 1, 1] := by
  refine ⟨beadSupport_all_partners 0 3 bead_mem_b bead_mem_a (i := 0) (j := 2)
      (by norm_num) (by decide), ?_⟩
  funext c; fin_cases c <;> simp [ex]

/-- **Control that does not fire, with its silence explained**
(`memory: a-silent-control-needs-its-silence-explained`).  I planted this expecting a
partner violating `hl` to leave the box.  It does not: at `l = 0, h = 3`, with
`y = (2,1,0)` and `j = 1` (where `y 1 = y' 1`, so `hl` fails), the surgered vector
`(1,2,0)` is still in `supp P̃^{(0,3)}`.

The silence is **not** a missed bug and **not** vacuity.  The true statement is scoped:
`hl` is what *guarantees* `y l + 1 ≤ Q l`, and when `y l` happens to sit strictly below
`Q l` already, the guarantee is not needed.  So `hl` is **sufficient, not necessary**, and
no single instance can show it necessary — a counterexample must pick a box where the
partner coordinate is *saturated* at `Q`.  `bead_hl_load_bearing` below does exactly that
(`l = h = 3`, so `Q 2 = 0` and `y 2 = 0` is saturated), and it fires. -/
theorem bead_hl_not_necessary_at_l_zero :
    beadSupport 0 3 (ex 0 1 ![2, 1, 0]) := by
  refine ⟨?_, ?_, ?_⟩ <;> [skip; skip; (simp [ex, Fin.sum_univ_three])] <;>
    intro c <;> fin_cases c <;> simp [beadQ, ex]

/-- **Negative control 2: `hl` is load-bearing.**  Take `y = (3,0,0)`, `y' = (0,3,0)` in
`supp P̃^{(0,3)}` and `i = 0`.  The index `j = 2` has `y 2 = y' 2` (so `hl` fails) and the
surgered vector `(2,0,1)` stays in the box — no contradiction there.  But at `l = 3`,
`h = 3`, where `Q = (3,3,0)`, the same `i = 0`, `j = 2` surgery on `y = (3,0,0)` produces
`(2,0,1)`, whose third coordinate exceeds `Q 2 = 0`.  So the conclusion of
`beadSupport_all_partners` is **false** for a partner violating `hl`: the hypothesis is
not decoration. -/
theorem bead_hl_load_bearing :
    beadSupport 3 3 ![3, 0, 0] ∧ ¬ beadSupport 3 3 (ex 0 2 ![3, 0, 0]) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro c; fin_cases c <;> simp
  · intro c; fin_cases c <;> simp [beadQ]
  · simp [Fin.sum_univ_three]
  · rintro ⟨-, hQ, -⟩
    have := hQ 2
    simp [beadQ, ex] at this

/-- **Negative control 3: the box slice is not all of the box.**  `(0,0,0)` satisfies both
box bounds of `supp P̃^{(0,3)}` and is not in it, because `∑ = 0 ≠ 3`.  So the hyperplane
conjunct of `InBox` is load-bearing. -/
theorem bead_sum_load_bearing :
    (∀ c, (0 : Fin 3 → ℤ) c ≤ (0 : Fin 3 → ℤ) c) ∧
      (∀ c, (0 : Fin 3 → ℤ) c ≤ beadQ 0 3 c) ∧ ¬ beadSupport 0 3 0 := by
  refine ⟨fun c => le_refl _, ?_, ?_⟩
  · intro c; fin_cases c <;> simp [beadQ]
  · rintro ⟨-, -, hs⟩
    simp at hs

end Witness

end TworowD4Kernel.BoxSlice
