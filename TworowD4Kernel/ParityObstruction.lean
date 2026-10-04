/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.HalfWidthL1
import TworowD4Kernel.SublevelMConvex

/-!
# The parity obstruction: a cylindric width-vector set is not M-convex

Formalisation of **`lem:P`** of `projects/proofs/2026-10-04-width-vector-M-convexity.tex`,
together with the structural refutation of **(H1)** ("the width-vector set `W` is M-convex")
that `lem:P` was measured in order to support.

The paper states `lem:P` with a count (13,522 slices satisfying it, 22,451 failing) and
reads the failures as evidence.  They are not evidence: they are a *theorem*.  Every
ingredient is already sorry-free in `TworowD4Kernel.HalfWidthL1`, and this file derives the
obstruction from those ingredients with no counterexample search at all.

## The argument in one line

`HalfWidthL1.twoHalfWidth_eq_sub_l1` gives `∑ᵢ wᵢ = n - ‖y‖₁`, and `‖y‖₁ ≡ ∑ᵢ yᵢ (mod 2)`
because `|t| = t + 2(−t)₊`.  On a fixed slice `∑ᵢ yᵢ` is constant, so the coordinate sums of
the width vectors lie in **one parity coset at spacing 2**.  An M-convex set has *constant*
coordinate sum.  Hence a slice carrying two distinct `‖y‖₁` values has a width-vector set
that is not M-convex — and the two sums differ by at least `2`, never by `1`.

## What is new here and what is a rename

* `l1Dist_eq_sum_devSeq_add_two_mul_defect` and `l1Dist_emod_two_eq` are new, and consume
  **no hypotheses at all** (see the discipline note below).
* `widthSum_eq` is, up to the definitional `- m` in `HalfWidthL1.twoHalfWidth`, *literally*
  `HalfWidthL1.twoHalfWidth_eq_sub_l1`.  It is stated anyway, in the paper's `G + m - ‖y‖₁`
  form with `G = n - m`, so that a reader checking `lem:P` against this development finds
  the paper's own expression; it is a rename, not a result, and its proof says so.
* `sum_eq_of_mConvex` and `not_mConvex_of_two_sums` are new.  **`MConvex` is defined here
  for the first time in this development**: despite the file names, neither
  `MConvexExchange` nor `SublevelMConvex` ever abstracts the predicate — each proves an
  exchange axiom for one concrete set (`InSupp`, `InS`).  `mConvex_inS` below checks the
  definition against `SublevelMConvex.sublevel_symm_exchange` so that the predicate
  introduced here is demonstrably the one Theorem M verifies.

## Hypothesis discipline

Stated throughout with `HalfWidthL1.Per`, never `GreedyChain.IsCylindric`: `Per` is the
weaker hypothesis and hence the stronger theorem (`HalfWidthL1.Per.of_isCylindric`).
Each theorem below records in its docstring which hypotheses it actually **consumes**.
Three of them turn out to consume none, and `sum_eq_of_mConvex` needs only the *one-sided*
exchange axiom, not Murota's symmetric one — so the obstruction applies to strictly more
sets than Theorem M's.

No `sorry`, no `native_decide`, no local axioms.
-/

namespace TworowD4Kernel.ParityObstruction

open HalfWidthL1 SublevelMConvex GreedyChain

variable {n m : ℕ} {lam nu nu' : ℤ → ℤ}

/-! ### `lem:P`, part 1: the `ℓ¹` distance splits off an even number

This is the whole parity content, and it is a *pointwise* fact about `|t| = t + 2(−t)₊`.
It consumes **no hypotheses**: not `Per lam`, not `Per nu`, not `0 < m`.  The `Per lam` in
`l1Dist_eq_of_per` below is needed only to evaluate `∑ yᵢ` in closed form, never for the
splitting itself. -/

/-- **`lem:P`, the splitting.**  `‖y‖₁ = ∑ᵢ yᵢ + 2 k(ν)`, where `k` is `HalfWidthL1.defect`.

Hypotheses consumed: **none**.  This identity appears inside the proof of
`HalfWidthL1.twoHalfWidth_eq_sub_two_mul_defect` as an unnamed `have` (with `Per lam`
in scope, which it does not use); extracting it is what makes the parity statement
available. -/
theorem l1Dist_eq_sum_devSeq_add_two_mul_defect (m : ℕ) (lam nu : ℤ → ℤ) :
    l1Dist m lam nu
      = (∑ j ∈ Finset.range m, devSeq lam nu ((j : ℤ) + 1)) + 2 * defect m lam nu := by
  unfold l1Dist defect
  have hterm : ∀ j ∈ Finset.range m,
      |devSeq lam nu ((j : ℤ) + 1)|
        = devSeq lam nu ((j : ℤ) + 1)
            + 2 * max (aSeq lam ((j : ℤ) + 1) - nu ((j : ℤ) + 1)) 0 := by
    intro j _
    unfold devSeq
    rcases abs_cases (nu ((j : ℤ) + 1) - aSeq lam ((j : ℤ) + 1)) with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The closed form of the splitting.  Hypotheses consumed: `Per n m lam` only (via
`HalfWidthL1.sum_devSeq`), to evaluate `∑ᵢ yᵢ = S_ν - A`.  `Per n m nu` is **not** needed. -/
theorem l1Dist_eq_of_per (hlam : Per n m lam) :
    l1Dist m lam nu = (u m nu - (u m lam - (n : ℤ) + m)) + 2 * defect m lam nu := by
  rw [l1Dist_eq_sum_devSeq_add_two_mul_defect, sum_devSeq hlam]

/-- **`lem:P`, the parity.**  `‖y‖₁ ≡ ∑ᵢ yᵢ (mod 2)`.  Hypotheses consumed: **none**. -/
theorem l1Dist_emod_two_eq (m : ℕ) (lam nu : ℤ → ℤ) :
    l1Dist m lam nu % 2 = (∑ j ∈ Finset.range m, devSeq lam nu ((j : ℤ) + 1)) % 2 := by
  rw [l1Dist_eq_sum_devSeq_add_two_mul_defect]
  omega

/-- Two `ν` on a **common slice** (equal weight `u m nu`) have `ℓ¹` distances that differ by
an even number.  Hypotheses consumed: `Per n m lam` only.

This is the precise sense in which the width-vector coordinate sums lie in *one parity
coset at spacing 2*, which is the half of `lem:P` the paper does not isolate. -/
theorem two_dvd_l1Dist_sub (hlam : Per n m lam) (hslice : u m nu = u m nu') :
    (2 : ℤ) ∣ l1Dist m lam nu - l1Dist m lam nu' := by
  rw [l1Dist_eq_of_per hlam, l1Dist_eq_of_per hlam, hslice]
  exact ⟨defect m lam nu - defect m lam nu', by ring⟩

/-! ### `lem:P`, part 2: the width-vector sum

`HalfWidthL1.twoHalfWidth` is *defined* as `(∑ᵢ wᵢ) - m`, so the identity below is
`HalfWidthL1.twoHalfWidth_eq_sub_l1` with the definitional `- m` moved across.  It is a
**rename of an existing theorem, not a new one**; it is stated only so that the paper's
own expression `G + m - ‖y‖₁` occurs verbatim in the development. -/

/-- **`lem:P`, the width sum.**  `∑ᵢ wᵢ(ν) = G + m - ‖y‖₁` with `G = n - m`.

Hypotheses consumed: `Per n m lam` and `Per n m nu`, both inherited from
`HalfWidthL1.twoHalfWidth_eq_sub_l1` — `Per nu` genuinely enters there, through the cyclic
shift `∑ (y_{i+1})₋ = ∑ (yᵢ)₋`. -/
theorem widthSum_eq (hlam : Per n m lam) (hnu : Per n m nu) :
    ∑ j ∈ Finset.range m, shapeWidth lam nu ((j : ℤ) + 1)
      = (((n : ℤ) - m) + m) - l1Dist m lam nu := by
  have h := twoHalfWidth_eq_sub_l1 hlam hnu
  unfold twoHalfWidth at h
  omega

/-- The width vector of a slice as a point of `ℤᵐ`, which is where M-convexity lives. -/
def widthVec (m : ℕ) (lam nu : ℤ → ℤ) : Fin m → ℤ :=
  fun c => shapeWidth lam nu ((c : ℤ) + 1)

/-- `∑_c widthVec c` is the `Finset.range` sum of `widthSum_eq`. -/
theorem sum_widthVec (m : ℕ) (lam nu : ℤ → ℤ) :
    ∑ c, widthVec m lam nu c
      = ∑ j ∈ Finset.range m, shapeWidth lam nu ((j : ℤ) + 1) := by
  simp only [widthVec]
  rw [Fin.sum_univ_eq_sum_range (fun j => shapeWidth lam nu ((j : ℤ) + 1)) m]

/-- `∑ᵢ wᵢ(ν) = n - ‖y‖₁` on the vector, in the form the obstruction consumes. -/
theorem sum_widthVec_eq (hlam : Per n m lam) (hnu : Per n m nu) :
    ∑ c, widthVec m lam nu c = (n : ℤ) - l1Dist m lam nu := by
  rw [sum_widthVec, widthSum_eq hlam hnu]; ring

/-! ### M-convexity, and the fact that it pins the coordinate sum -/

/-- `MConvex S` is the **one-sided** exchange axiom (B-EXC⁻) of Murota:

> for all `y, y' ∈ S` and every `i` with `yᵢ > y'ᵢ` there is a `j` with `y_j < y'_j` and
> `y - eᵢ + e_j ∈ S`.

The surgery is `SublevelMConvex.ex`, reused rather than redefined.

Murota's *symmetric* axiom additionally demands `y' + eᵢ - e_j ∈ S` for the same `j`.
Only the one-sided form is required below, which makes `sum_eq_of_mConvex` apply to
strictly more sets — in particular to `MConvexExchange.InSupp`, for which only the
one-sided axiom is proved. -/
def MConvex {m : ℕ} (S : Set (Fin m → ℤ)) : Prop :=
  ∀ y ∈ S, ∀ y' ∈ S, ∀ i : Fin m, y' i < y i → ∃ l, y l < y' l ∧ ex i l y ∈ S

/-- Since `∑ y' < ∑ y`, some coordinate goes the other way.  The strict-inequality
companion of `SublevelMConvex.exists_lt_of_sums_eq`. -/
theorem exists_lt_of_sum_lt {m : ℕ} {y y' : Fin m → ℤ} (h : ∑ c, y' c < ∑ c, y c) :
    ∃ i, y' i < y i := by
  by_contra hcon
  push_neg at hcon
  have : ∑ c, y c ≤ ∑ c, y' c := Finset.sum_le_sum fun c _ => hcon c
  omega

/-- The surgery moves `y` two steps closer to `y'` in `ℓ¹`, when `i` and `l` are chosen as
the exchange axiom chooses them.  Hypotheses consumed: `y' i < y i` and `y l < y' l`. -/
theorem l1_ex_sub {m : ℕ} {y y' : Fin m → ℤ} {i l : Fin m}
    (hi : y' i < y i) (hl : y l < y' l) :
    ∑ c, |ex i l y c - y' c| = (∑ c, |y c - y' c|) - 2 := by
  classical
  have hil : i ≠ l := by intro h; rw [h] at hi; omega
  have e1 : |y i - 1 - y' i| = |y i - y' i| - 1 := by
    rcases abs_cases (y i - y' i) with ⟨e, _⟩ | ⟨e, _⟩ <;>
      rcases abs_cases (y i - 1 - y' i) with ⟨f, _⟩ | ⟨f, _⟩ <;> omega
  have e2 : |y l + 1 - y' l| = |y l - y' l| - 1 := by
    rcases abs_cases (y l - y' l) with ⟨e, _⟩ | ⟨e, _⟩ <;>
      rcases abs_cases (y l + 1 - y' l) with ⟨f, _⟩ | ⟨f, _⟩ <;> omega
  -- Only the two touched coordinates contribute, exactly as in `SublevelMConvex.kfun_ex`.
  have hsum : ∑ c ∈ ({i, l} : Finset (Fin m)), (|ex i l y c - y' c| - |y c - y' c|)
      = ∑ c : Fin m, (|ex i l y c - y' c| - |y c - y' c|) := by
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro c _ hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [ex_apply_off y hc.1 hc.2]
    ring
  rw [Finset.sum_pair hil, ex_apply_self y hil, ex_apply_other y hil, e1, e2,
    Finset.sum_sub_distrib] at hsum
  omega

/-- The descent that powers `sum_eq_of_mConvex`: no `y, y' ∈ S` with `∑ y' < ∑ y` can sit at
`ℓ¹` distance `≤ N`.  Induction on `N`; each exchange step spends exactly `2`. -/
theorem no_sum_lt_of_mConvex {m : ℕ} {S : Set (Fin m → ℤ)} (hS : MConvex S) :
    ∀ N : ℕ, ∀ y y' : Fin m → ℤ, y ∈ S → y' ∈ S → (∑ c, y' c) < (∑ c, y c) →
      (∑ c, |y c - y' c|) ≤ (N : ℤ) → False := by
  intro N
  induction N with
  | zero =>
    intro y y' _ _ hlt hle
    -- `‖y - y'‖₁ ≥ |∑ (yᵢ - y'ᵢ)| > 0` contradicts `‖y - y'‖₁ ≤ 0`.
    have hb : |∑ c, (y c - y' c)| ≤ ∑ c, |y c - y' c| := Finset.abs_sum_le_sum_abs _ _
    have hs : ∑ c, (y c - y' c) = (∑ c, y c) - ∑ c, y' c := by
      rw [Finset.sum_sub_distrib]
    rcases abs_cases (∑ c, (y c - y' c)) with ⟨e, _⟩ | ⟨e, _⟩ <;>
      simp only [Nat.cast_zero] at hle <;> omega
  | succ k ih =>
    intro y y' hy hy' hlt hle
    obtain ⟨i, hi⟩ := exists_lt_of_sum_lt hlt
    obtain ⟨l, hl, hmem⟩ := hS y hy y' hy' i hi
    refine ih (ex i l y) y' hmem hy' ?_ ?_
    · rw [sum_ex]; exact hlt
    · rw [l1_ex_sub hi hl]
      push_cast at hle ⊢
      omega

/-- **An M-convex set has constant coordinate sum.**  Hypotheses consumed: the one-sided
exchange axiom only.  Not `0 < m` (for `m = 0` both sums are `0`), and no finiteness,
boundedness or nonemptiness assumption on `S`. -/
theorem sum_eq_of_mConvex {m : ℕ} {S : Set (Fin m → ℤ)} (hS : MConvex S)
    {y y' : Fin m → ℤ} (hy : y ∈ S) (hy' : y' ∈ S) : ∑ c, y c = ∑ c, y' c := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact no_sum_lt_of_mConvex hS (∑ c, |y' c - y c|).toNat y' y hy' hy h
      (by rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun c _ => abs_nonneg _)])
  · exact no_sum_lt_of_mConvex hS (∑ c, |y c - y' c|).toNat y y' hy hy' h
      (by rw [Int.toNat_of_nonneg (Finset.sum_nonneg fun c _ => abs_nonneg _)])

/-- **The obstruction, abstractly.**  A set containing two points with different coordinate
sums is not M-convex.  This is the contrapositive of `sum_eq_of_mConvex`. -/
theorem not_mConvex_of_two_sums {m : ℕ} {S : Set (Fin m → ℤ)}
    {y y' : Fin m → ℤ} (hy : y ∈ S) (hy' : y' ∈ S) (hne : (∑ c, y c) ≠ ∑ c, y' c) :
    ¬ MConvex S := fun hS => hne (sum_eq_of_mConvex hS hy hy')

/-- The predicate introduced here is the one **Theorem M** verifies: the sublevel set
`S_j` of `SublevelMConvex.InS` is `MConvex`, by
`SublevelMConvex.sublevel_symm_exchange` (which proves the stronger, symmetric axiom).

This is a check on the *definition*, not a new result: without it, `MConvex` could be
misstated (wrong direction of an inequality, say) and every theorem above would still
typecheck while applying to nothing. -/
theorem mConvex_inS {m : ℕ} (P Q : Fin m → ℤ) (σ j : ℤ) :
    MConvex {y : Fin m → ℤ | InS P Q σ j y} := by
  intro y hy y' hy' i hi
  obtain ⟨l, hl, hz, -⟩ := sublevel_symm_exchange hy hy' hi
  exact ⟨l, hl, hz⟩

/-! ### (H1) is refuted: the width-vector set of a slice is not M-convex -/

/-- **The refutation of (H1), in contrapositive form.**  If a set `S` containing the width
vectors of two `ν` on a common slice is M-convex, then those two `ν` have equal `ℓ¹`
distance.  Hypotheses consumed: `Per lam`, `Per nu`, `Per nu'`; **not** the slice condition,
and **not** `defect_nonneg`. -/
theorem l1Dist_eq_of_mConvex {m : ℕ} {S : Set (Fin m → ℤ)} (hS : MConvex S)
    (hlam : Per n m lam) (hnu : Per n m nu) (hnu' : Per n m nu')
    (h1 : widthVec m lam nu ∈ S) (h2 : widthVec m lam nu' ∈ S) :
    l1Dist m lam nu = l1Dist m lam nu' := by
  have h := sum_eq_of_mConvex hS h1 h2
  rw [sum_widthVec_eq hlam hnu, sum_widthVec_eq hlam hnu'] at h
  omega

/-- **(H1) is false.**  A set containing the width vectors of two `ν` with distinct `ℓ¹`
distance is not M-convex.  No slice condition, no counterexample search. -/
theorem widthSet_not_mConvex {m : ℕ} {S : Set (Fin m → ℤ)}
    (hlam : Per n m lam) (hnu : Per n m nu) (hnu' : Per n m nu')
    (h1 : widthVec m lam nu ∈ S) (h2 : widthVec m lam nu' ∈ S)
    (hne : l1Dist m lam nu ≠ l1Dist m lam nu') :
    ¬ MConvex S :=
  fun hS => hne (l1Dist_eq_of_mConvex hS hlam hnu hnu' h1 h2)

/-- **The sums differ by at least `2`, never by `1`** — the sharp form of `lem:P`, and the
reason the obstruction is *structural* rather than an accident of small cases.  On a common
slice the two width-vector coordinate sums are congruent mod `2`, so if they differ at all
they differ by at least `2`.  Hypotheses consumed: `Per lam`, `Per nu`, `Per nu'`, and the
slice condition `u m nu = u m nu'`. -/
theorem two_le_abs_sum_sub (hlam : Per n m lam) (hnu : Per n m nu) (hnu' : Per n m nu')
    (hslice : u m nu = u m nu') (hne : l1Dist m lam nu ≠ l1Dist m lam nu') :
    2 ≤ |(∑ c, widthVec m lam nu c) - ∑ c, widthVec m lam nu' c| := by
  obtain ⟨t, ht⟩ := two_dvd_l1Dist_sub hlam hslice
  rw [sum_widthVec_eq hlam hnu, sum_widthVec_eq hlam hnu']
  have htne : t ≠ 0 := by intro h; rw [h] at ht; omega
  rcases abs_cases ((n : ℤ) - l1Dist m lam nu - ((n : ℤ) - l1Dist m lam nu')) with
    ⟨e, _⟩ | ⟨e, _⟩ <;> rcases lt_or_gt_of_ne htne with h | h <;> omega

end TworowD4Kernel.ParityObstruction
