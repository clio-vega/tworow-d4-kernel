/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.GreedyChain
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith

/-!
# The half-width of a cylindric slice is an `ℓ¹` distance

Formalisation of `§`"The half-width is an `ℓ¹` distance" of
`projects/proofs/2026-10-03-M-positive-part-concave.tex` (cited below as [Mpos]):

* `lem:w`  / `eq:w`      → `shapeWidth_eq`
* `eq:y`   (`∑ gᵢ = n-m`) → `sum_gapSeq`
* `thm:l1` / `eq:l1`     → `twoHalfWidth_eq_sub_l1`, `halfWidth_eq_sub_half_l1`
* `thm:l1` / `eq:defect` → `twoHalfWidth_eq_sub_two_mul_defect`, `twoHalfWidth_eq_sub_of_slice`,
                           `centre_sub_halfWidth_eq_defect`
* `thm:l1`, last sentence → `defect_eq_zero_iff_hStrip`, `halfWidth_eq_centre_iff_hStrip`
* `cor:tentfree`         → `twoHalfWidth_midpoint_concave`, `twoHalfWidth_le_of_slice`,
                           `twoHalfWidth_eq_iff_hStrip`, `halfWidth_midpoint_concave`,
                           `halfWidth_le_centre`

The ambient combinatorial model (`def:shape`, `eq:hstrip`, bead coordinates) is
`GreedyChain`; it is WZZ's cylindric skew Schur setting, arXiv:2401.14632 §5, transported
to bead coordinates by `prop:dictionary` of
`projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex`, following Lam–Postnikov.

## Why the development is `ℤ`-valued, with `ℚ` paid back at the end

The paper's half-width is `Λ(ν) = ½(∑ᵢ wᵢ(ν) - m)`, which lies in `½ℤ` and not in `ℤ`.
The `½` is the *only* reason a rational would enter this file.  Every statement of
`thm:l1` and `cor:tentfree` is an identity or an inequality between `½ℤ`-valued
quantities, so each is equivalent to the statement obtained by doubling it, and no step
of either proof ever divides by `2`.  Every proof in this file therefore works with

  `twoHalfWidth = 2Λ ∈ ℤ`,

which keeps `omega` available on the `max`/`min`/`|·|` arithmetic that is the whole
content of `lem:w`.

Carrying `2Λ` rather than `Λ` is a *rescaling of the statement*, so it is not by itself
the paper's statement, and a reader checking `thm:l1` against this file would otherwise
find no `Λ` in it.  The final section closes that gap rather than arguing it away: it
defines `halfWidth = twoHalfWidth / 2 : ℚ` and proves `eq:l1`, `eq:defect` and
`cor:tentfree` in their literal `Λ`, `(n-m)/2`, `c = (d-b)/2` forms
(`halfWidth_eq_sub_half_l1`, `centre_sub_halfWidth_eq_defect`,
`halfWidth_midpoint_concave`, `halfWidth_le_centre`, `halfWidth_eq_centre_iff_hStrip`).
Those five are the declarations that match the paper verbatim; the `twoHalfWidth` ones
are the same content doubled, and are what the rest of the development should cite.

## Naming

`Convolution.lean` already defines `width` for the *window* width `B - A`.  That is a
different object from the shape width `wᵢ(ν)` of this file.  The object here is
consistently `shapeWidth`, never `width`.

## Scope

This file formalises `thm:l1` and the two parts of `cor:tentfree` that follow from it.
It does **not** formalise `rem:Mconcave` of
`projects/proofs/2026-10-02-m3-concentricity.tex` — that remark is **refuted** by [Mpos],
whose main theorem is the counterexample at `n - m = 6` — and it does **not** bear on
condition (A): by [Mpos]'s quotation of `thm:blind`, no statement about the half-width
profile alone can close (A).

No `sorry`, no `native_decide`, no local axioms.
-/

namespace TworowD4Kernel.HalfWidthL1

open GreedyChain

variable {n m : ℕ} {lam nu mu : ℤ → ℤ}

/-! ### The hypothesis `thm:l1` actually consumes -/

/-- `Per n m x` is `x (i + m) = x i + n`, i.e. `GreedyChain.IsCylindric.per` on its own,
with the strict increase `IsCylindric.inc` dropped.

This is the *only* part of `def:shape` that `thm:l1` consumes: no proof below uses `inc`,
for either `λ` or `ν`.  Stating the hypothesis as `Per` matters for faithfulness, not just
economy.  `thm:l1` is asserted in [Mpos] "for every `m ≥ 1`, every cylindric `μ ⊆ λ` and
every `ν ∈ ℤᵐ`" — the `ν` there is an arbitrary point of the fundamental domain under the
cyclic convention `ν_{i+m} = νᵢ + n`, with **no** monotonicity.  Requiring
`IsCylindric n m nu` would therefore state a strictly weaker theorem than the paper's,
and `eq:l1` is used in [Mpos] precisely on `ν` off the support, where `fᵥ = 0`. -/
def Per (n m : ℕ) (x : ℤ → ℤ) : Prop := ∀ i : ℤ, x (i + m) = x i + n

/-- A cylindric shape is in particular `Per`; so every statement below applies to the
shapes of `GreedyChain`. -/
theorem Per.of_isCylindric {x : ℤ → ℤ} (h : IsCylindric n m x) : Per n m x := h.per

/-! ### The sequences of `eq:y` -/

/-- `aᵢ = λ_{i-1} + 1`, the point of `ℤᵐ` the half-width measures the distance to.
Cyclically `a₁ = λ_m - n + 1`, which is automatic here because `lam` is defined on all of
`ℤ` and `IsCylindric.per` gives `λ₀ = λ_m - n`. -/
def aSeq (lam : ℤ → ℤ) (i : ℤ) : ℤ := lam (i - 1) + 1

/-- `gᵢ = λᵢ - λ_{i-1} - 1 ≥ 0`, the gap sequence of `eq:y`. -/
def gapSeq (lam : ℤ → ℤ) (i : ℤ) : ℤ := lam i - lam (i - 1) - 1

/-- `yᵢ = νᵢ - aᵢ`, the deviation of `eq:y`. -/
def devSeq (lam nu : ℤ → ℤ) (i : ℤ) : ℤ := nu i - aSeq lam i

/-! ### The window ends and the shape width -/

/-- `Lᵢ(ν) = max (νᵢ, λ_{i-1} + 1)`. -/
def lowEnd (lam nu : ℤ → ℤ) (i : ℤ) : ℤ := max (nu i) (lam (i - 1) + 1)

/-- `Rᵢ(ν) = min (ν_{i+1} - 1, λᵢ)`. -/
def highEnd (lam nu : ℤ → ℤ) (i : ℤ) : ℤ := min (nu (i + 1) - 1) (lam i)

/-- `wᵢ(ν) = Rᵢ(ν) - Lᵢ(ν) + 1`, the **shape** width.  Not `width`, which is the window
width `B - A` of `Convolution.lean`. -/
def shapeWidth (lam nu : ℤ → ℤ) (i : ℤ) : ℤ := highEnd lam nu i - lowEnd lam nu i + 1

/-- `2Λ(ν) = ∑_{i=1}^{m} wᵢ(ν) - m`.  See the module docstring for why `2Λ` and not `Λ`. -/
def twoHalfWidth (m : ℕ) (lam nu : ℤ → ℤ) : ℤ :=
  (∑ j ∈ Finset.range m, shapeWidth lam nu ((j : ℤ) + 1)) - m

/-- `k(ν) = ∑_{i=1}^{m} (aᵢ - νᵢ)₊`, the defect of `eq:defect`. -/
def defect (m : ℕ) (lam nu : ℤ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range m, max (aSeq lam ((j : ℤ) + 1) - nu ((j : ℤ) + 1)) 0

/-- `∑_{i=1}^{m} |yᵢ|`, the `ℓ¹` distance from `ν` to `a` over one fundamental domain. -/
def l1Dist (m : ℕ) (lam nu : ℤ → ℤ) : ℤ :=
  ∑ j ∈ Finset.range m, |devSeq lam nu ((j : ℤ) + 1)|

/-! ### Telescoping over a fundamental domain -/

/-- Telescoping on `ℤ`-indexed sequences, in the form the cyclic closure of `eq:y` needs. -/
theorem sum_succ_sub (h : ℤ → ℤ) (m : ℕ) :
    ∑ j ∈ Finset.range m, (h ((j : ℤ) + 1) - h (j : ℤ)) = h (m : ℤ) - h 0 := by
  have := Finset.sum_range_sub (f := fun j : ℕ => h (j : ℤ)) m
  simpa using this

/-- A sum over the fundamental domain `{1, …, m}` of an `m`-periodic sequence is unchanged
by a cyclic shift.  This is what makes the `(y_{i+1})₋` terms of `eq:w` recombine with the
`(yᵢ)₊` terms into `|yᵢ|`. -/
theorem sum_shift_of_periodic (h : ℤ → ℤ) (m : ℕ) (hp : ∀ i : ℤ, h (i + m) = h i) :
    ∑ j ∈ Finset.range m, h ((j : ℤ) + 1 + 1) = ∑ j ∈ Finset.range m, h ((j : ℤ) + 1) := by
  have key := sum_succ_sub (fun i => h (i + 1)) m
  have h0 : h ((m : ℤ) + 1) = h (0 + 1) := by
    have := hp 1
    rw [show (1 : ℤ) + (m : ℤ) = (m : ℤ) + 1 by ring] at this
    simpa using this
  rw [h0] at key
  have : (∑ j ∈ Finset.range m, h ((j : ℤ) + 1 + 1))
      - (∑ j ∈ Finset.range m, h ((j : ℤ) + 1)) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa using key
  omega

/-! ### `lem:w`: the width vector in closed form -/

/-- `eq:w`: `wᵢ(ν) = gᵢ - (y_{i+1})₋ - (yᵢ)₊ + 1`.  No hypotheses: a pointwise identity
between `max`/`min` expressions, true for every `ν ∈ ℤᵐ` and every `λ`. -/
theorem shapeWidth_eq (lam nu : ℤ → ℤ) (i : ℤ) :
    shapeWidth lam nu i
      = gapSeq lam i - max (-devSeq lam nu (i + 1)) 0 - max (devSeq lam nu i) 0 + 1 := by
  unfold shapeWidth highEnd lowEnd gapSeq devSeq aSeq
  have : (i + 1) - 1 = i := by ring
  rw [this]
  omega

/-! ### The two sums of `eq:y` -/

/-- The cyclic closure of `eq:y`: `∑_{i=1}^{m} gᵢ = n - m`.  This is the only place the
cylindricity of `λ` is used in `thm:l1`. -/
theorem sum_gapSeq (hlam : Per n m lam) :
    ∑ j ∈ Finset.range m, gapSeq lam ((j : ℤ) + 1) = (n : ℤ) - m := by
  have key := sum_succ_sub lam m
  have hper : lam (m : ℤ) = lam 0 + n := by
    have := hlam 0
    simpa using this
  have hg : ∀ j ∈ Finset.range m,
      gapSeq lam ((j : ℤ) + 1) = (lam ((j : ℤ) + 1) - lam (j : ℤ)) - 1 := by
    intro j _
    unfold gapSeq
    rw [show ((j : ℤ) + 1) - 1 = (j : ℤ) by ring]
  rw [Finset.sum_congr rfl hg, Finset.sum_sub_distrib, key, hper]
  simp

/-- `∑_{i=1}^{m} aᵢ = |λ| - n + m`, where `|λ| = u m lam` is the weight over one
fundamental domain. -/
theorem sum_aSeq (hlam : Per n m lam) :
    ∑ j ∈ Finset.range m, aSeq lam ((j : ℤ) + 1) = u m lam - n + m := by
  have hsplit : ∀ j ∈ Finset.range m,
      aSeq lam ((j : ℤ) + 1) = lam ((j : ℤ) + 1) - gapSeq lam ((j : ℤ) + 1) := by
    intro j _
    unfold aSeq gapSeq
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, sum_gapSeq hlam]
  unfold u
  ring

/-- `∑_{i=1}^{m} yᵢ = Sᵥ - A`, i.e. the `σ` of `eq:sigma` before the slice is imposed. -/
theorem sum_devSeq (hlam : Per n m lam) :
    ∑ j ∈ Finset.range m, devSeq lam nu ((j : ℤ) + 1) = u m nu - (u m lam - n + m) := by
  unfold devSeq
  rw [Finset.sum_sub_distrib, sum_aSeq hlam]
  unfold u
  ring

/-- `y` is `m`-periodic: this is where the cylindricity of `ν` is used. -/
theorem devSeq_periodic (hlam : Per n m lam) (hnu : Per n m nu) (i : ℤ) :
    devSeq lam nu (i + m) = devSeq lam nu i := by
  unfold devSeq aSeq
  have h1 : nu (i + m) = nu i + n := hnu i
  have h2 : lam (i + (m : ℤ) - 1) = lam (i - 1) + n := by
    have := hlam (i - 1)
    rw [show (i - 1) + (m : ℤ) = i + (m : ℤ) - 1 by ring] at this
    exact this
  rw [h1, h2]
  ring

/-! ### `thm:l1` -/

/-- **`thm:l1`, `eq:l1`.**  `2Λ(ν) = (n - m) - ∑_{i=1}^{m} |νᵢ - aᵢ|`: the half-width is
affine in the `ℓ¹` distance from `ν` to the point `a = (λ_{i-1} + 1)ᵢ`. -/
theorem twoHalfWidth_eq_sub_l1 (hlam : Per n m lam) (hnu : Per n m nu) :
    twoHalfWidth m lam nu = ((n : ℤ) - m) - l1Dist m lam nu := by
  unfold twoHalfWidth l1Dist
  have hw : ∀ j ∈ Finset.range m,
      shapeWidth lam nu ((j : ℤ) + 1)
        = (gapSeq lam ((j : ℤ) + 1) + 1) - max (-devSeq lam nu ((j : ℤ) + 1 + 1)) 0
            - max (devSeq lam nu ((j : ℤ) + 1)) 0 := by
    intro j _
    rw [shapeWidth_eq]
    ring
  rw [Finset.sum_congr rfl hw]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    sum_gapSeq hlam]
  -- the cyclic shift: `∑ (y_{i+1})₋ = ∑ (yᵢ)₋`
  have hshiftper : ∀ i : ℤ,
      max (-devSeq lam nu (i + m)) 0 = max (-devSeq lam nu i) 0 := by
    intro i; rw [devSeq_periodic hlam hnu]
  rw [sum_shift_of_periodic (fun i => max (-devSeq lam nu i) 0) m hshiftper]
  -- and `(yᵢ)₊ + (yᵢ)₋ = |yᵢ|` termwise
  have habs : ∀ j ∈ Finset.range m,
      |devSeq lam nu ((j : ℤ) + 1)|
        = max (-devSeq lam nu ((j : ℤ) + 1)) 0 + max (devSeq lam nu ((j : ℤ) + 1)) 0 := by
    intro j _
    rcases abs_cases (devSeq lam nu ((j : ℤ) + 1)) with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  rw [Finset.sum_congr rfl habs, Finset.sum_add_distrib]
  simp
  ring

/-- **`thm:l1`, `eq:defect`**, in the form that does not mention `μ`, `b` or `d`:
`2Λ(ν) = (|λ| - Sᵥ) - 2k(ν)`.  The slice version is `twoHalfWidth_eq_sub_of_slice`. -/
theorem twoHalfWidth_eq_sub_two_mul_defect
    (hlam : Per n m lam) (hnu : Per n m nu) :
    twoHalfWidth m lam nu = (u m lam - u m nu) - 2 * defect m lam nu := by
  rw [twoHalfWidth_eq_sub_l1 hlam hnu]
  -- `|yᵢ| = yᵢ + 2 (yᵢ)₋` and `(yᵢ)₋ = (aᵢ - νᵢ)₊`
  have hterm : ∀ j ∈ Finset.range m,
      |devSeq lam nu ((j : ℤ) + 1)|
        = devSeq lam nu ((j : ℤ) + 1)
            + 2 * max (aSeq lam ((j : ℤ) + 1) - nu ((j : ℤ) + 1)) 0 := by
    intro j _
    unfold devSeq
    rcases abs_cases (nu ((j : ℤ) + 1) - aSeq lam ((j : ℤ) + 1)) with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
  have hsum : l1Dist m lam nu
      = (u m nu - (u m lam - (n : ℤ) + m)) + 2 * defect m lam nu := by
    unfold l1Dist defect
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, sum_devSeq hlam,
      ← Finset.mul_sum]
  rw [hsum]
  ring

/-- **`thm:l1`, `eq:defect`** on the slice `Sᵥ = |μ| + b`, with `d = |λ/μ|`:
`2Λ(ν) = (d - b) - 2k(ν)`, i.e. `c - Λ = k` with `c = (d-b)/2`. -/
theorem twoHalfWidth_eq_sub_of_slice {b d : ℤ}
    (hlam : Per n m lam) (hnu : Per n m nu)
    (hd : u m lam - u m mu = d) (hslice : u m nu = u m mu + b) :
    twoHalfWidth m lam nu = (d - b) - 2 * defect m lam nu := by
  rw [twoHalfWidth_eq_sub_two_mul_defect hlam hnu, hslice]
  omega

/-! ### `k = 0` characterises horizontal strips -/

/-- Each summand of `k` is nonnegative. -/
theorem defect_nonneg : 0 ≤ defect m lam nu := by
  unfold defect
  exact Finset.sum_nonneg fun j _ => le_max_right _ _

/-- A property that is `m`-periodic and holds on the fundamental domain `{1, …, m}` holds
on all of `ℤ`.  Needed to land `defect_eq_zero_iff_hStrip` on `GreedyChain.HStrip`, which
is a statement about every `i : ℤ`. -/
theorem forall_of_forall_range (hm : 0 < m) (P : ℤ → Prop)
    (hper : ∀ i : ℤ, P (i + m) ↔ P i) (h : ∀ j ∈ Finset.range m, P ((j : ℤ) + 1)) :
    ∀ i : ℤ, P i := by
  have hmul : ∀ q : ℤ, ∀ i : ℤ, P (i + m * q) ↔ P i := by
    intro q
    induction q using Int.induction_on with
    | zero => intro i; simp
    | succ k ih =>
      intro i
      rw [show i + (m : ℤ) * ((k : ℤ) + 1) = (i + (m : ℤ) * (k : ℤ)) + m by ring, hper, ih]
    | pred k ih =>
      intro i
      have e : i + (m : ℤ) * (-(k : ℤ) - 1) + m = i + (m : ℤ) * (-(k : ℤ)) := by ring
      rw [← hper (i + (m : ℤ) * (-(k : ℤ) - 1)), e]
      exact ih i
  intro i
  have hmz : (0 : ℤ) < (m : ℤ) := by exact_mod_cast hm
  have h1 : 0 ≤ (i - 1) % (m : ℤ) := Int.emod_nonneg _ (by omega)
  have h2 : (i - 1) % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos _ hmz
  have hdiv : (i - 1) % (m : ℤ) + (m : ℤ) * ((i - 1) / (m : ℤ)) = i - 1 :=
    Int.emod_add_mul_ediv _ _
  have hmem : ((i - 1) % (m : ℤ)).toNat ∈ Finset.range m := by
    rw [Finset.mem_range]; omega
  have hcast : ((((i - 1) % (m : ℤ)).toNat : ℕ) : ℤ) = (i - 1) % (m : ℤ) :=
    Int.toNat_of_nonneg h1
  have hP := h _ hmem
  rw [hcast] at hP
  have heq : i = ((i - 1) % (m : ℤ) + 1) + (m : ℤ) * ((i - 1) / (m : ℤ)) := by omega
  rw [heq, hmul]
  exact hP

/-- **`thm:l1`, last sentence.**  On a `ν` contained in `λ`, the defect vanishes exactly
when `λ/ν` is a horizontal strip.  `GreedyChain.HStrip nu lam` unfolds to
`νᵢ ≤ λᵢ ∧ λᵢ < ν_{i+1}`, which is the paper's bead-coordinate criterion
`λ_{i-1} < νᵢ ≤ λᵢ`. -/
theorem defect_eq_zero_iff_hStrip (hm : 0 < m)
    (hlam : Per n m lam) (hnu : Per n m nu) (hsub : Sub nu lam) :
    defect m lam nu = 0 ↔ HStrip nu lam := by
  constructor
  · intro h0
    have hzero : ∀ j ∈ Finset.range m,
        max (aSeq lam ((j : ℤ) + 1) - nu ((j : ℤ) + 1)) 0 = 0 := by
      intro j hj
      have hnn : ∀ k ∈ Finset.range m,
          0 ≤ max (aSeq lam ((k : ℤ) + 1) - nu ((k : ℤ) + 1)) 0 := fun k _ => le_max_right _ _
      exact le_antisymm
        (by
          have := Finset.single_le_sum hnn hj
          unfold defect at h0
          omega)
        (le_max_right _ _)
    have hperP : ∀ i : ℤ, (aSeq lam (i + m) ≤ nu (i + m)) ↔ (aSeq lam i ≤ nu i) := by
      intro i
      unfold aSeq
      have h1 : nu (i + m) = nu i + n := hnu i
      have h2 : lam (i + (m : ℤ) - 1) = lam (i - 1) + n := by
        have := hlam (i - 1)
        rw [show (i - 1) + (m : ℤ) = i + (m : ℤ) - 1 by ring] at this
        exact this
      rw [h1, h2]
      omega
    have hall : ∀ i : ℤ, aSeq lam i ≤ nu i :=
      forall_of_forall_range hm (fun i => aSeq lam i ≤ nu i) hperP
        (fun j hj => by have := hzero j hj; omega)
    intro i
    refine ⟨hsub i, ?_⟩
    have := hall (i + 1)
    unfold aSeq at this
    rw [show (i + 1) - 1 = i by ring] at this
    omega
  · intro hstrip
    unfold defect
    refine Finset.sum_eq_zero fun j _ => ?_
    have := (hstrip ((j : ℤ))).2
    unfold aSeq
    rw [show ((j : ℤ) + 1) - 1 = (j : ℤ) by ring]
    omega

/-! ### `cor:tentfree`: the two parts of the tent lemma that are now free -/

/-- `cor:tentfree`, first part: `2Λ` is concave, being a constant minus an `ℓ¹` norm.  On
`ℤᵐ` concavity is stated at integral midpoints: if `ν + ν' = 2σ` pointwise then
`2Λ(ν) + 2Λ(ν') ≤ 2 · 2Λ(σ)`. -/
theorem twoHalfWidth_midpoint_concave
    (hlam : Per n m lam) (hnu : Per n m nu) {nu' sig : ℤ → ℤ}
    (hnu' : Per n m nu') (hsig : Per n m sig)
    (hmid : ∀ i : ℤ, nu i + nu' i = 2 * sig i) :
    twoHalfWidth m lam nu + twoHalfWidth m lam nu' ≤ 2 * twoHalfWidth m lam sig := by
  rw [twoHalfWidth_eq_sub_l1 hlam hnu, twoHalfWidth_eq_sub_l1 hlam hnu',
    twoHalfWidth_eq_sub_l1 hlam hsig]
  have key : 2 * l1Dist m lam sig ≤ l1Dist m lam nu + l1Dist m lam nu' := by
    unfold l1Dist
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have hm' := hmid ((j : ℤ) + 1)
    unfold devSeq
    rcases abs_cases (nu ((j : ℤ) + 1) - aSeq lam ((j : ℤ) + 1)) with ⟨e1, _⟩ | ⟨e1, _⟩ <;>
      rcases abs_cases (nu' ((j : ℤ) + 1) - aSeq lam ((j : ℤ) + 1)) with ⟨e2, _⟩ | ⟨e2, _⟩ <;>
        rcases abs_cases (sig ((j : ℤ) + 1) - aSeq lam ((j : ℤ) + 1)) with ⟨e3, _⟩ | ⟨e3, _⟩ <;>
          omega
  omega

/-- `cor:tentfree`, second part: on a slice, `2Λ ≤ d - b`, with equality exactly when
`λ/ν` is a horizontal strip; and `2Λ ∈ (d-b) - 2ℤ_{≥0}`. -/
theorem twoHalfWidth_le_of_slice {b d : ℤ}
    (hlam : Per n m lam) (hnu : Per n m nu)
    (hd : u m lam - u m mu = d) (hslice : u m nu = u m mu + b) :
    twoHalfWidth m lam nu ≤ d - b := by
  rw [twoHalfWidth_eq_sub_of_slice hlam hnu hd hslice]
  have := defect_nonneg (m := m) (lam := lam) (nu := nu)
  omega

/-- `cor:tentfree`, equality case: `2Λ = d - b` exactly on the horizontal strips. -/
theorem twoHalfWidth_eq_iff_hStrip {b d : ℤ} (hm : 0 < m)
    (hlam : Per n m lam) (hnu : Per n m nu) (hsub : Sub nu lam)
    (hd : u m lam - u m mu = d) (hslice : u m nu = u m mu + b) :
    twoHalfWidth m lam nu = d - b ↔ HStrip nu lam := by
  rw [twoHalfWidth_eq_sub_of_slice hlam hnu hd hslice,
    ← defect_eq_zero_iff_hStrip hm hlam hnu hsub]
  omega

/-! ### The paper's `Λ` itself, over `ℚ`

`twoHalfWidth` carries `2Λ` so that the whole development above is `ℤ`-valued (see the
module docstring).  This last section pays the `½` back, so that the *literal* statements
of `thm:l1` and `cor:tentfree` -- the ones with `Λ`, `(n-m)/2` and `c = (d-b)/2` in them --
are theorems in the file and not only consequences of it.  Each is one `push_cast; ring`
from its doubled form; nothing new is proved here. -/

/-- `Λ(ν) = ½(∑_{i=1}^{m} wᵢ(ν) - m) ∈ ℚ`, the paper's half-width. -/
def halfWidth (m : ℕ) (lam nu : ℤ → ℤ) : ℚ := (twoHalfWidth m lam nu : ℚ) / 2

/-- **`thm:l1`, `eq:l1`, verbatim**: `Λ(ν) = (n-m)/2 - ½ ∑_{i=1}^{m} |νᵢ - aᵢ|`. -/
theorem halfWidth_eq_sub_half_l1 (hlam : Per n m lam) (hnu : Per n m nu) :
    halfWidth m lam nu = ((n : ℚ) - m) / 2 - (1 / 2) * (l1Dist m lam nu : ℚ) := by
  unfold halfWidth
  rw [twoHalfWidth_eq_sub_l1 hlam hnu]
  push_cast
  ring

/-- **`thm:l1`, `eq:defect`, verbatim**: on the slice `Sᵥ = |μ| + b`, with `c = (d-b)/2`,
`c - Λ(ν) = k(ν)`. -/
theorem centre_sub_halfWidth_eq_defect {b d : ℤ}
    (hlam : Per n m lam) (hnu : Per n m nu)
    (hd : u m lam - u m mu = d) (hslice : u m nu = u m mu + b) :
    ((d : ℚ) - b) / 2 - halfWidth m lam nu = (defect m lam nu : ℚ) := by
  unfold halfWidth
  rw [twoHalfWidth_eq_sub_of_slice hlam hnu hd hslice]
  push_cast
  ring

/-- `cor:tentfree`, first part, verbatim: `Λ` is concave at integral midpoints. -/
theorem halfWidth_midpoint_concave
    (hlam : Per n m lam) (hnu : Per n m nu) {nu' sig : ℤ → ℤ}
    (hnu' : Per n m nu') (hsig : Per n m sig)
    (hmid : ∀ i : ℤ, nu i + nu' i = 2 * sig i) :
    halfWidth m lam nu + halfWidth m lam nu' ≤ 2 * halfWidth m lam sig := by
  have h := twoHalfWidth_midpoint_concave hlam hnu hnu' hsig hmid
  unfold halfWidth
  have : ((twoHalfWidth m lam nu + twoHalfWidth m lam nu' : ℤ) : ℚ)
      ≤ ((2 * twoHalfWidth m lam sig : ℤ) : ℚ) := by exact_mod_cast h
  push_cast at this
  linarith

/-- `cor:tentfree`, second part, verbatim: on a slice `Λ ≤ c`, with equality exactly when
`λ/ν` is a horizontal strip. -/
theorem halfWidth_le_centre {b d : ℤ}
    (hlam : Per n m lam) (hnu : Per n m nu)
    (hd : u m lam - u m mu = d) (hslice : u m nu = u m mu + b) :
    halfWidth m lam nu ≤ ((d : ℚ) - b) / 2 := by
  have h := twoHalfWidth_le_of_slice hlam hnu hd hslice
  have : ((twoHalfWidth m lam nu : ℤ) : ℚ) ≤ ((d - b : ℤ) : ℚ) := by exact_mod_cast h
  unfold halfWidth
  push_cast at this
  linarith

/-- `cor:tentfree`, equality case, verbatim. -/
theorem halfWidth_eq_centre_iff_hStrip {b d : ℤ} (hm : 0 < m)
    (hlam : Per n m lam) (hnu : Per n m nu) (hsub : Sub nu lam)
    (hd : u m lam - u m mu = d) (hslice : u m nu = u m mu + b) :
    halfWidth m lam nu = ((d : ℚ) - b) / 2 ↔ HStrip nu lam := by
  rw [← twoHalfWidth_eq_iff_hStrip hm hlam hnu hsub hd hslice]
  unfold halfWidth
  constructor
  · intro h
    have hq : ((twoHalfWidth m lam nu : ℤ) : ℚ) = ((d - b : ℤ) : ℚ) := by push_cast; linarith
    exact_mod_cast hq
  · intro h
    rw [h]
    push_cast
    ring

end TworowD4Kernel.HalfWidthL1
