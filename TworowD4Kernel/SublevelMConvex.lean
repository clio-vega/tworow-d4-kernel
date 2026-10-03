/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Theorem M: box ∩ hyperplane ∩ negative-part sublevel sets are M-convex

Formalisation of **Theorem M** (`thm:M`) of
`projects/proofs/2026-10-04-width-vector-M-convexity.tex`.

> Let `B = ∏_{i=1}^m [P_i, Q_i] ⊆ ℤ^m` be a box, let `σ ∈ ℤ`, and put
> `k(y) = ∑_i (−y_i)_+`.  Then for every `j` the set
> `S_j = { y ∈ B : ∑_i y_i = σ, k(y) ≤ j }` is M-convex.

The main declaration is `SublevelMConvex.sublevel_symm_exchange`, which proves the
**symmetric** exchange axiom (Murota's B-EXC): one and the same `l` works for `y` and
for `y'`.  That is what the paper's proof delivers (last line of the proof of `thm:M`:
"which is the symmetric exchange axiom"), and it is strictly stronger than the one-sided
form proved for a different set in `MConvexExchange.insupp_exchange`.

## Relation to the rest of this development

`MConvexExchange.insupp_exchange` / `SortedBridge.insupp_iff_sorted` prove the exchange
axiom for `J = {α ∈ ℕ^ℓ : α([ℓ]) = |λ̂|, α(S) ≤ Λ_{|S|}}`.  **They do not apply here.**
`S_j` is a *box* intersected with a hyperplane and with a sublevel set; the box
constraints are not of the form `α(S) ≤ Λ_{|S|}`, `S_j` is not contained in `ℕ^m`, and
an intersection of two M-convex sets need not be M-convex.  So this file is
self-contained over Mathlib; nothing from the dominance-order pillar is reused.

## What is load-bearing, and the control

`prop:sharp` of the same paper proves the analogue for a *general* separable convex
`φ = ∑_i φ_i(y_i)` is **false**.  So this cannot be, and is not, a corollary of
separable-convex theory.  The proof consumes exactly two properties of
`φ(t) = (−t)_+` beyond convexity, and they are isolated here as named lemmas which the
main proof cites:

* `negPart_antitone`  — non-increasing.  Fixes the signs of the increments; consumed in
  Case 3 (`negPart_le_negPart_of_le`).
* `negPart_lipschitz_lower` — 1-Lipschitz (the lower half, which is the half used).
  Consumed in Case 2.

A proof of `sublevel_symm_exchange` that never invoked both would be proving something
else.  The negative control is `Control.sharp_witness_exchange_fails` at the end of the
file: a machine-checked separable **convex** `φ` on an explicit box whose sublevel set
violates the exchange axiom.

## Conventions

Vectors are `Fin m → ℤ` (not `ℕ → ℤ` as in `RobinHood`), so that no index-range side
condition is needed and the quantifier over `i` is literally the paper's.  `ex i l y` is
the paper's `y - e_i + e_l`; the paper's `y' + e_i - e_l` is `ex l i y'`.
-/

namespace TworowD4Kernel.SublevelMConvex

open Finset

/-! ### The negative part, and its two load-bearing properties -/

/-- `negPart t = (−t)_+ = max (−t) 0`, the paper's `\pospart{-t}`.

Stated as a literal `max` on `ℤ` rather than via Mathlib's lattice `negPart` so that
every statement about it below is decidable arithmetic, hence falsifiable inside Lean. -/
def negPart (t : ℤ) : ℤ := max (-t) 0

@[simp] lemma negPart_of_nonneg {t : ℤ} (h : 0 ≤ t) : negPart t = 0 := by
  simp only [negPart]; omega

@[simp] lemma negPart_of_nonpos {t : ℤ} (h : t ≤ 0) : negPart t = -t := by
  simp only [negPart]; omega

lemma negPart_nonneg (t : ℤ) : 0 ≤ negPart t := by simp only [negPart]; omega

/-- **Load-bearing property 1: `negPart` is non-increasing.**  `prop:sharp` of the paper
shows Theorem M fails for separable convex `φ` in general; this is one of the two extra
properties of `(−t)_+` that the proof consumes. -/
lemma negPart_antitone : Antitone negPart := by
  intro a b hab
  simp only [negPart]
  omega

lemma negPart_le_negPart_of_le {a b : ℤ} (h : a ≤ b) : negPart b ≤ negPart a :=
  negPart_antitone h

/-- **Load-bearing property 2: `negPart` is 1-Lipschitz**, in the lower form the proof of
Theorem M actually consumes (Case 2): a downward step of size `a - b` can decrease
`negPart` by at most `a - b`. -/
lemma negPart_lipschitz_lower {a b : ℤ} (h : b ≤ a) :
    -(a - b) ≤ negPart a - negPart b := by
  simp only [negPart]; omega

/-- The full 1-Lipschitz statement, for the record.  Only `negPart_lipschitz_lower` is
used below. -/
lemma negPart_lipschitz (a b : ℤ) : |negPart a - negPart b| ≤ |a - b| := by
  simp only [negPart]
  rcases abs_cases (a - b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases abs_cases (max (-a) 0 - max (-b) 0) with ⟨g1, g2⟩ | ⟨g1, g2⟩ <;> omega

/-- A unit step **down** raises `negPart` by `1` exactly when the coordinate was `≤ 0`.
The paper's `p = 𝟙[y_i ≤ 0]` and `q'_l = 𝟙[y'_l ≤ 0]`. -/
lemma negPart_step_down (t : ℤ) :
    negPart (t - 1) - negPart t = if t ≤ 0 then 1 else 0 := by
  simp only [negPart]; split_ifs <;> omega

/-- A unit step **up** lowers `negPart` by `1` exactly when the coordinate was `≤ -1`.
The paper's `q_l = -𝟙[y_l ≤ -1]` and `p' = -𝟙[y'_i ≤ -1]`. -/
lemma negPart_step_up (t : ℤ) :
    negPart (t + 1) - negPart t = if t ≤ -1 then -1 else 0 := by
  simp only [negPart]; split_ifs <;> omega

/-! ### The set `S_j`, and the surgery `y - e_i + e_l` -/

/-- `k y = ∑_i (−y_i)_+`, the paper's defect `k(y)` of `eq:Lam`. -/
def kfun {m : ℕ} (y : Fin m → ℤ) : ℤ := ∑ c, negPart (y c)

/-- `ex i l y` is the paper's `y - e_i + e_l`. -/
def ex {m : ℕ} (i l : Fin m) (y : Fin m → ℤ) : Fin m → ℤ :=
  fun c => y c - (if c = i then 1 else 0) + (if c = l then 1 else 0)

/-- `y ∈ S_j = { y ∈ ∏_i [P_i, Q_i] : ∑_i y_i = σ, k(y) ≤ j }`. -/
def InS {m : ℕ} (P Q : Fin m → ℤ) (σ j : ℤ) (y : Fin m → ℤ) : Prop :=
  (∀ c, P c ≤ y c) ∧ (∀ c, y c ≤ Q c) ∧ (∑ c, y c = σ) ∧ kfun y ≤ j

lemma ex_apply_self {m : ℕ} (y : Fin m → ℤ) {i l : Fin m} (hil : i ≠ l) :
    ex i l y i = y i - 1 := by
  simp [ex, hil]

lemma ex_apply_other {m : ℕ} (y : Fin m → ℤ) {i l : Fin m} (hil : i ≠ l) :
    ex i l y l = y l + 1 := by
  simp [ex, Ne.symm hil]

lemma ex_apply_off {m : ℕ} (y : Fin m → ℤ) {i l c : Fin m} (hi : c ≠ i) (hl : c ≠ l) :
    ex i l y c = y c := by
  simp [ex, hi, hl]

/-- The surgery preserves the coordinate sum.  (`i = l` is allowed: then it is the
identity.) -/
lemma sum_ex {m : ℕ} (y : Fin m → ℤ) (i l : Fin m) : ∑ c, ex i l y c = ∑ c, y c := by
  classical
  simp only [ex, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' Finset.univ i (fun _ => (1 : ℤ)),
    Finset.sum_ite_eq' Finset.univ l (fun _ => (1 : ℤ))]
  simp

/-- The defect under the surgery: only the two touched coordinates contribute. -/
lemma kfun_ex {m : ℕ} (y : Fin m → ℤ) {i l : Fin m} (hil : i ≠ l) :
    kfun (ex i l y) - kfun y
      = (negPart (y i - 1) - negPart (y i)) + (negPart (y l + 1) - negPart (y l)) := by
  classical
  have hsum : ∑ c ∈ ({i, l} : Finset (Fin m)), (negPart (ex i l y c) - negPart (y c))
      = ∑ c : Fin m, (negPart (ex i l y c) - negPart (y c)) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro c _ hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [ex_apply_off y hc.1 hc.2]
    ring
  rw [kfun, kfun, ← Finset.sum_sub_distrib, ← hsum, Finset.sum_pair hil,
    ex_apply_self y hil, ex_apply_other y hil]

/-! ### Box and hyperplane: the easy half (`j = ∞`) -/

/-- *Box and hyperplane* paragraph of the proof of `thm:M`.  For **every** `l` with
`y l < y' l` the surgered vector stays in the box and on the hyperplane; only `k ≤ j`
can fail.  This is already the statement that a box meets a hyperplane M-convexly. -/
lemma ex_box_sum {m : ℕ} {P Q : Fin m → ℤ} {σ j : ℤ} {y y' : Fin m → ℤ}
    (hy : InS P Q σ j y) (hy' : InS P Q σ j y') {i l : Fin m}
    (hi : y' i < y i) (hl : y l < y' l) :
    i ≠ l ∧ (∀ c, P c ≤ ex i l y c) ∧ (∀ c, ex i l y c ≤ Q c) ∧ (∑ c, ex i l y c = σ) := by
  obtain ⟨hyP, hyQ, hyS, -⟩ := hy
  obtain ⟨hyP', hyQ', hyS', -⟩ := hy'
  have hil : i ≠ l := by rintro rfl; omega
  refine ⟨hil, ?_, ?_, by rw [sum_ex]; exact hyS⟩
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

/-! ### `D ≠ ∅` -/

/-- Since `∑ y = ∑ y' = σ` and `y i > y' i`, some coordinate goes the other way. -/
lemma exists_lt_of_sums_eq {m : ℕ} {y y' : Fin m → ℤ} (h : ∑ c, y c = ∑ c, y' c)
    {i : Fin m} (hi : y' i < y i) : ∃ l, y l < y' l := by
  by_contra hcon
  push_neg at hcon
  have : ∑ c, y' c < ∑ c, y c :=
    Finset.sum_lt_sum (fun c _ => hcon c) ⟨i, Finset.mem_univ i, hi⟩
  omega

/-! ### The two Case-2 / Case-3 comparisons

These are the only places the two load-bearing properties of `negPart` enter. -/

/-- **Case 2's comparison.**  If `y i ≥ 1`, `y' i ≥ 0`, and every `l` with `y l < y' l`
has `y' l ≤ 0`, then `k(y) > k(y')`.

Consumes `negPart_lipschitz_lower` (1-Lipschitz). -/
lemma kfun_gt_of_case2 {m : ℕ} {y y' : Fin m → ℤ} (hsum : ∑ c, y c = ∑ c, y' c)
    {i : Fin m} (hi : y' i < y i) (hyi : 1 ≤ y i) (hyi' : 0 ≤ y' i)
    (hbad : ∀ l, y l < y' l → y' l ≤ 0) : kfun y' < kfun y := by
  have key : ∑ t, (y' t - y t) < ∑ t, (negPart (y t) - negPart (y' t)) := by
    refine Finset.sum_lt_sum (fun t _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases lt_or_ge (y t) (y' t) with hlt | hge
      · -- `t ∈ D`: both coordinates are `≤ 0`, so the term is *exactly* `y' t - y t`.
        have h0 : y' t ≤ 0 := hbad t hlt
        have h1 : y t ≤ 0 := by omega
        rw [negPart_of_nonpos h1, negPart_of_nonpos h0]
        omega
      · -- `t ∉ D`: this is the 1-Lipschitz bound.
        have := negPart_lipschitz_lower (a := y t) (b := y' t) hge
        omega
    · -- At `t = i` the bound is strict: both negative parts vanish.
      have e1 : negPart (y i) = 0 := negPart_of_nonneg (by omega)
      have e2 : negPart (y' i) = 0 := negPart_of_nonneg hyi'
      rw [e1, e2]
      omega
  have hL : ∑ t, (y' t - y t) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]; ring
  have hR : ∑ t, (negPart (y t) - negPart (y' t)) = kfun y - kfun y' := by
    rw [Finset.sum_sub_distrib]; rfl
  omega

/-- **Case 3's comparison.**  If `y i ≤ 0`, `y' i ≤ -1`, `y' i < y i`, and every `l` with
`y l < y' l` has `y l ≥ 0`, then `k(y) < k(y')`.

Consumes `negPart_antitone` (non-increasing). -/
lemma kfun_lt_of_case3 {m : ℕ} {y y' : Fin m → ℤ}
    {i : Fin m} (hyi : y i ≤ 0) (hi : y' i < y i)
    (hbad : ∀ l, y l < y' l → 0 ≤ y l) : kfun y < kfun y' := by
  have key : ∑ t, (negPart (y t) - negPart (y' t)) < ∑ _t : Fin m, (0 : ℤ) := by
    refine Finset.sum_lt_sum (fun t _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases lt_or_ge (y t) (y' t) with hlt | hge
      · -- `t ∈ D`: both negative parts vanish.
        have h0 : 0 ≤ y t := hbad t hlt
        rw [negPart_of_nonneg h0, negPart_of_nonneg (by omega : (0:ℤ) ≤ y' t)]
        omega
      · -- `t ∉ D`: this is antitonicity.
        have := negPart_le_negPart_of_le hge
        omega
    · -- At `t = i` the bound is strict.
      rw [negPart_of_nonpos hyi, negPart_of_nonpos (by omega : y' i ≤ 0)]
      omega
  have hL : ∑ t, (negPart (y t) - negPart (y' t)) = kfun y - kfun y' := by
    rw [Finset.sum_sub_distrib]; rfl
  simp only [Finset.sum_const, smul_zero] at key
  omega

/-! ### Theorem M -/

/-- **Theorem M** (`thm:M` of `2026-10-04-width-vector-M-convexity.tex`).

For every box `∏_i [P_i, Q_i] ⊆ ℤ^m`, every `σ`, and every `j`, the set
`S_j = { y : P ≤ y ≤ Q, ∑ y = σ, k y ≤ j }` satisfies the **symmetric** M-convex
exchange axiom (B-EXC): for `y, y' ∈ S_j` and `i` with `y i > y' i` there is an `l` with
`y l < y' l` such that *both* `y - e_i + e_l` and `y' + e_i - e_l` lie in `S_j`.

The proof is the paper's, case for case.  The two properties of `(−t)_+` that
`prop:sharp` shows are load-bearing enter through `kfun_gt_of_case2`
(`negPart_lipschitz_lower`) and `kfun_lt_of_case3` (`negPart_antitone`). -/
theorem sublevel_symm_exchange {m : ℕ} {P Q : Fin m → ℤ} {σ j : ℤ} {y y' : Fin m → ℤ}
    (hy : InS P Q σ j y) (hy' : InS P Q σ j y') {i : Fin m} (hi : y' i < y i) :
    ∃ l, y l < y' l ∧ InS P Q σ j (ex i l y) ∧ InS P Q σ j (ex l i y') := by
  classical
  have hsum : ∑ c, y c = ∑ c, y' c := by rw [hy.2.2.1, hy'.2.2.1]
  have hky : kfun y ≤ j := hy.2.2.2
  have hky' : kfun y' ≤ j := hy'.2.2.2
  -- `D ≠ ∅`.
  obtain ⟨l0, hl0⟩ := exists_lt_of_sums_eq hsum hi
  -- A packaging step: once `l` is chosen and both defects are bounded, we are done.
  have assemble : ∀ l : Fin m, y l < y' l → kfun (ex i l y) ≤ j → kfun (ex l i y') ≤ j →
      ∃ l, y l < y' l ∧ InS P Q σ j (ex i l y) ∧ InS P Q σ j (ex l i y') := by
    intro l hl h1 h2
    obtain ⟨hil, hP, hQ, hS⟩ := ex_box_sum hy hy' hi hl
    obtain ⟨-, hP', hQ', hS'⟩ := ex_box_sum hy' hy (i := l) (l := i) hl hi
    exact ⟨l, hl, ⟨hP, hQ, hS, h1⟩, ⟨hP', hQ', hS', h2⟩⟩
  -- The increments, as in the *Increments* paragraph of the proof.
  have incY : ∀ l : Fin m, i ≠ l →
      kfun (ex i l y) = kfun y + (if y i ≤ 0 then 1 else 0) + (if y l ≤ -1 then -1 else 0) := by
    intro l hil
    have h := kfun_ex y hil
    rw [negPart_step_down (y i), negPart_step_up (y l)] at h
    omega
  have incY' : ∀ l : Fin m, i ≠ l →
      kfun (ex l i y') = kfun y' + (if y' l ≤ 0 then 1 else 0) + (if y' i ≤ -1 then -1 else 0) := by
    intro l hil
    have h := kfun_ex y' (Ne.symm hil)
    rw [negPart_step_down (y' l), negPart_step_up (y' i)] at h
    omega
  have hil0 : i ≠ l0 := by rintro rfl; omega
  rcases le_or_gt (y i) 0 with hc3 | hyi1
  · -- **Case 3**: `y i ≤ 0`, hence `y' i ≤ -1`.
    have hy'i : y' i ≤ -1 := by omega
    rcases le_or_gt (kfun y) (j - 1) with hlow | hhigh
    · refine assemble l0 hl0 ?_ ?_
      · rw [incY l0 hil0]; split_ifs <;> omega
      · rw [incY' l0 hil0]; split_ifs <;> omega
    · -- `k y = j`: need an `l ∈ D` with `y l ≤ -1`.
      have hkeq : kfun y = j := by omega
      have hex : ∃ l, y l < y' l ∧ y l ≤ -1 := by
        by_contra hcon
        push_neg at hcon
        have hbad : ∀ l, y l < y' l → 0 ≤ y l := by
          intro l hl; have := hcon l hl; omega
        have := kfun_lt_of_case3 hc3 hi hbad
        omega
      obtain ⟨l, hl, hlneg⟩ := hex
      have hil : i ≠ l := by rintro rfl; omega
      refine assemble l hl ?_ ?_
      · rw [incY l hil]; split_ifs <;> omega
      · rw [incY' l hil]; split_ifs <;> omega
  · -- `y i ≥ 1`.
    rcases lt_or_ge (y' i) 0 with hc1 | hc2
    · -- **Case 1**: `y' i ≤ -1`.  Every `l ∈ D` works.
      refine assemble l0 hl0 ?_ ?_
      · rw [incY l0 hil0]; split_ifs <;> omega
      · rw [incY' l0 hil0]; split_ifs <;> omega
    · -- **Case 2**: `y i ≥ 1`, `y' i ≥ 0`.
      rcases le_or_gt (kfun y') (j - 1) with hlow | hhigh
      · refine assemble l0 hl0 ?_ ?_
        · rw [incY l0 hil0]; split_ifs <;> omega
        · rw [incY' l0 hil0]; split_ifs <;> omega
      · -- `k y' = j`: need an `l ∈ D` with `y' l ≥ 1`.
        have hkeq : kfun y' = j := by omega
        have hex : ∃ l, y l < y' l ∧ 1 ≤ y' l := by
          by_contra hcon
          push_neg at hcon
          have hbad : ∀ l, y l < y' l → y' l ≤ 0 := by
            intro l hl; have := hcon l hl; omega
          have := kfun_gt_of_case2 hsum hi (by omega) hc2 hbad
          omega
        obtain ⟨l, hl, hlpos⟩ := hex
        have hil : i ≠ l := by rintro rfl; omega
        refine assemble l hl ?_ ?_
        · rw [incY l hil]; split_ifs <;> omega
        · rw [incY' l hil]; split_ifs <;> omega


/-! ### Non-vacuity, and why the *choice* of `l` is real content

`memory: a theorem whose hypotheses are never satisfiable type-checks perfectly`, and
`memory: a hypothesis can be never-satisfied, not false`.  Two guards.

The second is the sharper one.  `sublevel_symm_exchange` is an existential over `l ∈ D`;
if every `l ∈ D` always worked, the statement would be the *box-and-hyperplane* half
alone (`ex_box_sum`) and the sublevel clause would be decoration.  It is not:
`choice_of_l_matters` exhibits `y, y'` at `k = j` with `D = {1, 3}` where `l = 1`
**leaves** `S_j` and only `l = 3` works.  That instance is exactly Case 2's hard
sub-case (`y i ≥ 1`, `y' i ≥ 0`, `k y' = j`), i.e. the one place
`negPart_lipschitz_lower` is consumed.
-/

namespace Witness

/-- The cube `[-3,3]^4`. -/
def Pc : Fin 4 → ℤ := fun _ => -3
def Qc : Fin 4 → ℤ := fun _ => 3

def ya : Fin 4 → ℤ := ![1, -2, -1, -1]
def yb : Fin 4 → ℤ := ![0, -1, -3, 1]

lemma ya_mem : InS Pc Qc (-3) 4 ya := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [kfun, negPart, ya, Fin.sum_univ_four]

lemma yb_mem : InS Pc Qc (-3) 4 yb := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [kfun, negPart, yb, Fin.sum_univ_four]

/-- Non-vacuity: the hypotheses of `sublevel_symm_exchange` are satisfiable, with `j`
**tight** (`k ya = k yb = 4 = j`), so the sublevel clause is active. -/
theorem hypotheses_satisfiable :
    kfun ya = 4 ∧ kfun yb = 4 ∧
      ∃ l, ya l < yb l ∧ InS Pc Qc (-3) 4 (ex 0 l ya) ∧ InS Pc Qc (-3) 4 (ex l 0 yb) := by
  refine ⟨by simp [kfun, negPart, ya, Fin.sum_univ_four],
          by simp [kfun, negPart, yb, Fin.sum_univ_four], ?_⟩
  exact sublevel_symm_exchange ya_mem yb_mem (i := 0) (by decide)

/-- **The choice of `l` is load-bearing.**  `D = {1, 3}`; `l = 1` leaves `S_j` (on the
`y'` side, `k` rises to `5 > 4`) and `l = 3` works.  So the existential in
`sublevel_symm_exchange` is not discharged by an arbitrary element of `D`, and the
theorem is strictly more than `ex_box_sum`. -/
theorem choice_of_l_matters :
    (ya 1 < yb 1 ∧ ya 3 < yb 3) ∧
      ¬ InS Pc Qc (-3) 4 (ex 1 0 yb) ∧
      (InS Pc Qc (-3) 4 (ex 0 3 ya) ∧ InS Pc Qc (-3) 4 (ex 3 0 yb)) := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, ?_⟩
  · rintro ⟨-, -, -, hk⟩
    rw [show kfun (ex 1 0 yb) = 5 by
      simp [kfun, negPart, ex, yb, Fin.sum_univ_four]] at hk
    omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro c; fin_cases c <;> simp [ex, ya, Pc]
    · intro c; fin_cases c <;> simp [ex, ya, Qc]
    · simp [ex, ya, Fin.sum_univ_four]
    · rw [show kfun (ex 0 3 ya) = 3 by
        simp [kfun, negPart, ex, ya, Fin.sum_univ_four]]
      omega
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro c; fin_cases c <;> simp [ex, yb, Pc]
    · intro c; fin_cases c <;> simp [ex, yb, Qc]
    · simp [ex, yb, Fin.sum_univ_four]
    · rw [show kfun (ex 3 0 yb) = 4 by
        simp [kfun, negPart, ex, yb, Fin.sum_univ_four]]

end Witness

/-! ### Negative control: `prop:sharp` — general separable convex `φ` fails

`prop:sharp` of `2026-10-04-width-vector-M-convexity.tex` states that the analogue of
Theorem M with a general separable convex `φ(y) = ∑_i φ_i(y_i)` in place of
`k(y) = ∑_i (−y_i)_+` is **false**, with witness `m = 3`,
`B = [−2,−1] × [−2,1] × [−2,1]`, `σ = −1`, level `6`, and sublevel set
`S = {(−2,1,0), (−1,−1,1), (−1,0,0), (−1,1,−1)}`.

The paper does **not** exhibit `φ` (it was found by random search).  The `φ` below is
reconstructed here and reproduces the paper's `S` exactly:

    φ_0 ≡ 0,    φ_1(t) = (t+1)_+,    φ_2(t) = 6·(t)_+

— each convex on all of `ℤ` (`sharp_phi_convex`).  Note `φ_1` and `φ_2` are
**non-decreasing**, i.e. they violate the `negPart_antitone` half, and `φ_2` is
`6`-Lipschitz, violating the `negPart_lipschitz_lower` half.

This is what makes Theorem M content rather than a corollary of separable-convex theory
on base polyhedra.
-/

namespace Control

def Pw : Fin 3 → ℤ := ![-2, -2, -2]
def Qw : Fin 3 → ℤ := ![-1, 1, 1]

/-- The reconstructed separable convex `φ` of `prop:sharp`. -/
def phi (c : Fin 3) (t : ℤ) : ℤ :=
  if c = 1 then max 0 (t + 1) else if c = 2 then 6 * max 0 t else 0

def Phi (z : Fin 3 → ℤ) : ℤ := ∑ c, phi c (z c)

/-- The `φ`-sublevel analogue of `InS`: box, hyperplane, and `Φ ≤ 6`. -/
def InT (z : Fin 3 → ℤ) : Prop :=
  (∀ c, Pw c ≤ z c) ∧ (∀ c, z c ≤ Qw c) ∧ (∑ c, z c = -1) ∧ Phi z ≤ 6

def zy : Fin 3 → ℤ := ![-1, -1, 1]
def zy' : Fin 3 → ℤ := ![-2, 1, 0]

/-- Each `φ_c` is convex on `ℤ` (midpoint form: `2 φ(t) ≤ φ(t−1) + φ(t+1)`). -/
theorem sharp_phi_convex :
    ∀ (c : Fin 3) (t : ℤ), 2 * phi c t ≤ phi c (t - 1) + phi c (t + 1) := by
  intro c t
  fin_cases c <;> simp only [phi] <;> norm_num <;> omega

lemma zy_mem : InT zy := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [Phi, phi, zy, Fin.sum_univ_three]

lemma zy'_mem : InT zy' := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [Phi, phi, zy', Fin.sum_univ_three]

/-- **Negative control = `prop:sharp`.**  With the convex separable `φ` above, the
exchange axiom **fails** at `(zy, zy', i = 0)`: the only `l` with `zy l < zy' l` is
`l = 1`, and `zy − e₀ + e₁ = (−2, 0, 1) ∉ S`.

The last conjunct records *where* it fails: the surgered point is still in the box and
still on the hyperplane `∑ = −1`; it is the **sublevel** constraint that breaks
(`Φ = 7 > 6`).  So the failure is not a box artefact. -/
theorem sharp_witness_exchange_fails :
    InT zy ∧ InT zy' ∧ zy' 0 < zy 0 ∧
      (∀ l, zy l < zy' l → l = 1) ∧ zy 1 < zy' 1 ∧
      ¬ InT (ex 0 1 zy) ∧
      ((∀ c, Pw c ≤ ex 0 1 zy c) ∧ (∀ c, ex 0 1 zy c ≤ Qw c) ∧
        (∑ c, ex 0 1 zy c = -1) ∧ Phi (ex 0 1 zy) = 7) := by
  have hbox : (∀ c, Pw c ≤ ex 0 1 zy c) ∧ (∀ c, ex 0 1 zy c ≤ Qw c) ∧
      (∑ c, ex 0 1 zy c = -1) ∧ Phi (ex 0 1 zy) = 7 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c; fin_cases c <;> simp [ex, zy, Pw]
    · intro c; fin_cases c <;> simp [ex, zy, Qw]
    · simp [ex, zy, Fin.sum_univ_three]
    · simp [Phi, phi, ex, zy, Fin.sum_univ_three]
  refine ⟨zy_mem, zy'_mem, by decide, ?_, by decide, ?_, hbox⟩
  · intro l hl; fin_cases l <;> simp_all [zy, zy']
  · rintro ⟨-, -, -, hk⟩
    rw [hbox.2.2.2] at hk
    omega

end Control

end TworowD4Kernel.SublevelMConvex
