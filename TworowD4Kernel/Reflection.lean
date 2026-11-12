/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.AlternantExpansion

/-!
# `lem:reflect`: `ι Ψ_θ = (−1)^r e^{2r} Ψ_{θ∨}`

Formalises `lem:reflect` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
L304–L345 (Clio, 2026-10-23, registry node `clio-Q559-reflection-identity`):

> Let `ι` be the `ℚ`-algebra automorphism with `ι(w_t) = w_t⁻¹`. Then for all `r ≥ 0` and
> `θ ∈ ℤ^r`, `ι(Ψ^C_{(1^r),θ}(M)) = (−1)^r e^{2r} Ψ^C_{(1^r),θ∨}(M)`, with `m∨_j = −m_j`,
> i.e. `θ∨_j = −θ_j − 2j + 2` (`j` 1-indexed), `e = ∏_t w_t`.

## Which `θ∨` (measured before writing Lean)

The repository's `rhoShift` is 0-indexed (paper `m = rhoShift + 1`, `rhoShiftPaper_eq`), so
"negate the ρ-shift" has two readings. `scratch/1112_lem_reflect.py` (exact `Fraction`,
60 random admissible signed points, `r ≤ 3`, `n ∈ r…r+2`, straight from `eq:Psidef`):

* paper reading, `θ∨_j = −θ_j − 2j` (0-indexed `j`): **60/60**;
* repository-`rhoShift` reading, `θ∨_j = −θ_j − 2j + 2`: **10/60** (the 10 are points where
  both sides happen to be 0; the control separates).

So `thetaVee` below is the paper's, and `rhoShiftPaper_thetaVee` is the paper's `m∨ = −m`.

## Route (a deviation from the paper's proof, recorded)

The paper applies `ι` to `thm:alt` and transforms `B(T)` and `det/V` separately. The same
three elementary identities (L320–L325) already hold **per head injection** of `eq:Psidef`:
the diagonal factor gives `−X_j^{2+2j} · (θ ↦ θ∨)`, each ordered pair `j < k` gives `X_j²`,
each cross factor gives `w_t²`, and the exponents total `2r` on every `X_j`. So the Lean
proof is termwise on `psiHead`, and **does not use `thm:alt`**. This is the paper's
computation on a finer index set, not new mathematics; the statement is the paper's.
-/

namespace TworowD4Kernel.Reflection

open Finset
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction

variable {ι : Type*} {K : Type*} [DecidableEq ι] [Field K]

/-- The paper's `θ∨` (`.tex` L312), `θ∨_j = −θ_j − 2j + 2` with `j` 1-indexed; here `j` is
0-indexed. -/
def thetaVee {r : ℕ} (θ : Fin r → ℤ) : Fin r → ℤ := fun j => -θ j - 2 * (j.val : ℤ)

/-- **`m∨ = −m`** for the paper's ρ-shift (`.tex` L312). -/
theorem rhoShiftPaper_thetaVee {r : ℕ} (θ : Fin r → ℤ) :
    rhoShiftPaper (thetaVee θ) = -rhoShiftPaper θ := by
  funext j; simp only [rhoShiftPaper, thetaVee, Pi.neg_apply]; ring

/-- `θ∨` is an involution. -/
theorem thetaVee_thetaVee {r : ℕ} (θ : Fin r → ℤ) : thetaVee (thetaVee θ) = θ := by
  funext j; simp only [thetaVee]; ring

/-! ## The three elementary identities (`.tex` L320–L325) -/

/-- Diagonal: `(1 − x²) x^{−θ} = −x^{2+2j} (1 − x^{−2}) x^{−θ−2j}`. -/
theorem diag_reflect {x : K} (hx : x ≠ 0) (θ : ℤ) (j : ℕ) :
    (1 - (x⁻¹)⁻¹ ^ 2) * x⁻¹ ^ θ =
      -(x ^ (2 + 2 * j)) * ((1 - x⁻¹ ^ 2) * x ^ (-θ - 2 * (j : ℤ))) := by
  have hy : x⁻¹ ^ θ = x ^ (-θ - 2 * (j : ℤ)) * x ^ (2 * j) := by
    rw [inv_zpow', ← zpow_natCast, ← zpow_add₀ hx]
    congr 1; push_cast; ring
  rw [inv_inv, hy]
  field_simp
  ring

/-- Pair and cross factors: `(1 − ab)/(1 − b/a) = a² (1 − 1/(ab))/(1 − a/b)`. -/
theorem pair_reflect {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    (1 - (a⁻¹ * b⁻¹)⁻¹) / (1 - a⁻¹ / b⁻¹) = a ^ 2 * ((1 - (a * b)⁻¹) / (1 - a / b)) := by
  have h1 : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have h2 : a - b ≠ 0 := sub_ne_zero.2 hab
  rw [inv_div_inv, mul_inv, inv_inv, inv_inv]
  field_simp
  ring

omit [DecidableEq ι] in
theorem crossFactor_inv (w : ι → K) {t i : ι} (ht : w t ≠ 0) (hi : w i ≠ 0)
    (hti : w t ≠ w i) :
    crossFactor (fun s => (w s)⁻¹) t i = w t ^ 2 * crossFactor w t i :=
  pair_reflect ht hi hti

/-! ## One head injection -/

/-- `∏_j ∏_{k > j} X_j² = ∏_j X_j^{2(r−1−j)}`. -/
theorem prod_pairs_sq {r : ℕ} (X : Fin r → K) :
    ∏ j : Fin r, ∏ _k ∈ Finset.univ.filter (j < ·), X j ^ 2 =
      ∏ j : Fin r, X j ^ (2 * (r - 1 - j.val)) := by
  refine Finset.prod_congr rfl fun j _ => ?_
  have hfilt : Finset.univ.filter (j < ·) = Ioi j := by ext k; simp
  rw [hfilt, Finset.prod_const, Fin.card_Ioi, ← pow_mul, mul_comm]

/-- **The reflection, one head injection.** -/
theorem term_reflect (w : ι → K) (M : Finset ι) {r : ℕ} (θ : Fin r → ℤ) {h : Fin r → ι}
    (hadm : Admissible w M) (hmem : ∀ j, h j ∈ M) (hh : Function.Injective h) :
    AlternantExpansion.headTerm (fun s => (w s)⁻¹) M θ h =
      (-1) ^ r * (∏ t ∈ M, w t) ^ (2 * r) *
        AlternantExpansion.headTerm w M (thetaVee θ) h := by
  have h0 : ∀ j, w (h j) ≠ 0 := fun j => hadm.1 _ (hmem j)
  have hne : ∀ j k, j ≠ k → w (h j) ≠ w (h k) := fun j k hjk =>
    hadm.2 _ (hmem j) _ (hmem k) (hh.ne hjk)
  -- diagonal
  have hD : ∏ j, (1 - ((w (h j))⁻¹)⁻¹ ^ 2) * (w (h j))⁻¹ ^ θ j =
      (-1) ^ r * (∏ j : Fin r, w (h j) ^ (2 + 2 * j.val)) *
        ∏ j, (1 - (w (h j))⁻¹ ^ 2) * w (h j) ^ thetaVee θ j := by
    rw [Finset.prod_congr rfl fun j _ => diag_reflect (h0 j) (θ j) j.val]
    rw [Finset.prod_mul_distrib, Finset.prod_neg]
    simp [thetaVee, Finset.card_univ]
  -- pairs
  have hP : ∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
        (1 - ((w (h j))⁻¹ * (w (h k))⁻¹)⁻¹) / (1 - (w (h j))⁻¹ / (w (h k))⁻¹) =
      (∏ j : Fin r, w (h j) ^ (2 * (r - 1 - j.val))) *
        ∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
          (1 - (w (h j) * w (h k))⁻¹) / (1 - w (h j) / w (h k)) := by
    rw [← prod_pairs_sq (fun j => w (h j)), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k hk => ?_
    have hjk : j ≠ k := (Finset.mem_filter.1 hk).2.ne
    exact pair_reflect (h0 j) (h0 k) (hne j k hjk)
  -- cross
  have hC : ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor (fun s => (w s)⁻¹) t (h j) =
      (∏ t ∈ M \ Finset.univ.image h, w t) ^ (2 * r) *
        ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor w t (h j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    obtain ⟨htM, htimg⟩ := Finset.mem_sdiff.1 ht
    have hneq : ∀ j, w t ≠ w (h j) := fun j e => by
      refine htimg ?_
      by_cases htj : t = h j
      · exact htj ▸ Finset.mem_image_of_mem _ (Finset.mem_univ _)
      · exact absurd e (hadm.2 _ htM _ (hmem j) htj)
    rw [Finset.prod_congr rfl fun j _ => crossFactor_inv w (hadm.1 _ htM) (h0 j) (hneq j),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul]
  -- e = ∏_{img h} · ∏_{M \ img h}
  have himgM : Finset.univ.image h ⊆ M := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy; exact hmem j
  have he : ∏ t ∈ M, w t = (∏ j, w (h j)) * ∏ t ∈ M \ Finset.univ.image h, w t := by
    rw [← Finset.prod_sdiff himgM, Finset.prod_image hh.injOn, mul_comm]
  -- exponents: (2 + 2j) + 2(r − 1 − j) = 2r
  have hX : (∏ j : Fin r, w (h j) ^ (2 + 2 * j.val)) *
      (∏ j : Fin r, w (h j) ^ (2 * (r - 1 - j.val))) = (∏ j, w (h j)) ^ (2 * r) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_add]
    congr 1
    have := j.isLt
    omega
  unfold AlternantExpansion.headTerm
  rw [hD, hP, hC, he, mul_pow, ← hX]
  ring

/-! ## `lem:reflect` -/

/-- **`lem:reflect`** (Q559 `.tex` L304–L345; `clio-Q559-reflection-identity`). At every
admissible `M` (nonzero, pairwise distinct `w`), evaluating `Ψ^C_{(1^r),θ}(M)` at `w⁻¹`
gives `(−1)^r e^{2r} Ψ^C_{(1^r),θ∨}(M)`, with `e = ∏_{t ∈ M} w_t` and the paper's `θ∨`. -/
theorem lem_reflect (w : ι → K) (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ)
    (hadm : Admissible w M) :
    psiHead (fun t => (w t)⁻¹) M r θ =
      (-1) ^ r * (∏ t ∈ M, w t) ^ (2 * r) * psiHead w M r (thetaVee θ) := by
  rw [AlternantExpansion.psiHead_eq_sum_headTerm, AlternantExpansion.psiHead_eq_sum_headTerm,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hh
  exact term_reflect w M θ hadm hh.1 hh.2

/-! ## Lesions (each asked as "derive `False` from the lesioned statement")

`Admissible` is two hypotheses: **N** (`w_t ≠ 0`; equivalently `e ≠ 0`) and **D** (pairwise
distinct). Pre-registered predictions: dropping N is refutable at `r = 1`, `M = {0}`,
`w = 0`, `θ = 0` (LHS `= 1` because `0⁻¹ = 0` and `0^0 = 1`, RHS `= 0` because `e = 0`);
dropping D is **not** refutable in Lean, because a coincidence `w_j = w_k` (or `w_t = X_j`)
kills the same denominator `1 − a/b` on **both** sides, and `x/0 = 0` makes both sides `0`.
The pair {N, D} is jointly fatal already through N's witness (`|M| = 1`, so D is vacuous). -/

/-- **Lesion N (drop `w ≠ 0`): refutable.** -/
theorem lesionN_refutable :
    ¬ ∀ (w : ℕ → ℚ) (M : Finset ℕ) (r : ℕ) (θ : Fin r → ℤ),
      (∀ s ∈ M, ∀ t ∈ M, s ≠ t → w s ≠ w t) →
      psiHead (fun t => (w t)⁻¹) M r θ =
        (-1) ^ r * (∏ t ∈ M, w t) ^ (2 * r) * psiHead w M r (thetaVee θ) := by
  intro H
  have h := H (fun _ => 0) {0} 1 0 (fun s hs t ht hst => by
    simp only [Finset.mem_singleton] at hs ht; exact absurd (hs.trans ht.symm) hst)
  have hI : headInjections ({0} : Finset ℕ) 1 = {fun _ => 0} := by
    ext g
    simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, -⟩; funext j; exact hg j
    · rintro rfl; exact ⟨fun _ => rfl, fun i j _ => Subsingleton.elim i j⟩
  simp only [psiHead, hI, Finset.sum_singleton, Finset.prod_singleton] at h
  norm_num [thetaVee] at h

/-- `pair_reflect` without distinctness: at `a = b` both sides are `0` (`x / 0 = 0`). -/
theorem pair_reflect' {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    (1 - (a⁻¹ * b⁻¹)⁻¹) / (1 - a⁻¹ / b⁻¹) = a ^ 2 * ((1 - (a * b)⁻¹) / (1 - a / b)) := by
  by_cases hab : a = b
  · subst hab; simp [div_self ha, div_self (inv_ne_zero ha)]
  · exact pair_reflect ha hb hab

omit [DecidableEq ι] in
theorem crossFactor_inv' (w : ι → K) {t i : ι} (ht : w t ≠ 0) (hi : w i ≠ 0) :
    crossFactor (fun s => (w s)⁻¹) t i = w t ^ 2 * crossFactor w t i :=
  pair_reflect' ht hi

/-- **Lesion D (drop distinctness): removable in Lean**, Lean-verified. This is the totalised
`x/0 = 0` statement, *wider* not stronger: at a coincidence both sides are the junk value `0`,
and in the paper's field `ℚ(w_1,…,w_n)` of indeterminates coincidences do not occur. -/
theorem lem_reflect_of_ne_zero (w : ι → K) (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ)
    (h0 : ∀ t ∈ M, w t ≠ 0) :
    psiHead (fun t => (w t)⁻¹) M r θ =
      (-1) ^ r * (∏ t ∈ M, w t) ^ (2 * r) * psiHead w M r (thetaVee θ) := by
  rw [AlternantExpansion.psiHead_eq_sum_headTerm, AlternantExpansion.psiHead_eq_sum_headTerm,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hh
  obtain ⟨hmem, hh⟩ := hh
  have hj : ∀ j, w (h j) ≠ 0 := fun j => h0 _ (hmem j)
  have hD : ∏ j, (1 - ((w (h j))⁻¹)⁻¹ ^ 2) * (w (h j))⁻¹ ^ θ j =
      (-1) ^ r * (∏ j : Fin r, w (h j) ^ (2 + 2 * j.val)) *
        ∏ j, (1 - (w (h j))⁻¹ ^ 2) * w (h j) ^ thetaVee θ j := by
    rw [Finset.prod_congr rfl fun j _ => diag_reflect (hj j) (θ j) j.val]
    rw [Finset.prod_mul_distrib, Finset.prod_neg]
    simp [thetaVee, Finset.card_univ]
  have hP : ∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
        (1 - ((w (h j))⁻¹ * (w (h k))⁻¹)⁻¹) / (1 - (w (h j))⁻¹ / (w (h k))⁻¹) =
      (∏ j : Fin r, w (h j) ^ (2 * (r - 1 - j.val))) *
        ∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
          (1 - (w (h j) * w (h k))⁻¹) / (1 - w (h j) / w (h k)) := by
    rw [← prod_pairs_sq (fun j => w (h j)), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => pair_reflect' (hj j) (hj k)
  have hC : ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor (fun s => (w s)⁻¹) t (h j) =
      (∏ t ∈ M \ Finset.univ.image h, w t) ^ (2 * r) *
        ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor w t (h j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t ht => ?_
    have htM := (Finset.mem_sdiff.1 ht).1
    rw [Finset.prod_congr rfl fun j _ => crossFactor_inv' w (h0 t htM) (hj j),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← pow_mul]
  have himgM : Finset.univ.image h ⊆ M := fun y hy => by
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy; exact hmem j
  have he : ∏ t ∈ M, w t = (∏ j, w (h j)) * ∏ t ∈ M \ Finset.univ.image h, w t := by
    rw [← Finset.prod_sdiff himgM, Finset.prod_image hh.injOn, mul_comm]
  have hX : (∏ j : Fin r, w (h j) ^ (2 + 2 * j.val)) *
      (∏ j : Fin r, w (h j) ^ (2 * (r - 1 - j.val))) = (∏ j, w (h j)) ^ (2 * r) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_add]
    congr 1
    have := j.isLt
    omega
  unfold AlternantExpansion.headTerm
  rw [hD, hP, hC, he, mul_pow, ← hX]
  ring

/-- **Lesion θ∨ (repository-`rhoShift` reading, `θ∨_j = −θ_j − 2j + 2`): refutable**, at
`r = 1`, `M = {0}`, `w = 2`, `θ = 0`: LHS `= (1 − 4)·1 = −3`, RHS `= −4 · (3/4) · 2² = −12`. -/
theorem lesionVee_refutable :
    ¬ ∀ (w : ℕ → ℚ) (M : Finset ℕ) (r : ℕ) (θ : Fin r → ℤ), Admissible w M →
      psiHead (fun t => (w t)⁻¹) M r θ =
        (-1) ^ r * (∏ t ∈ M, w t) ^ (2 * r) *
          psiHead w M r (fun j => -θ j - 2 * (j.val : ℤ) + 2) := by
  intro H
  have h := H (fun _ => 2) {0} 1 0 ⟨fun _ _ => by norm_num, fun s hs t ht hst => by
    simp only [Finset.mem_singleton] at hs ht; exact absurd (hs.trans ht.symm) hst⟩
  have hI : headInjections ({0} : Finset ℕ) 1 = {fun _ => 0} := by
    ext g
    simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · rintro ⟨hg, -⟩; funext j; exact hg j
    · rintro rfl; exact ⟨fun _ => rfl, fun i j _ => Subsingleton.elim i j⟩
  simp only [psiHead, hI, Finset.sum_singleton, Finset.prod_singleton] at h
  norm_num at h

/-! ## Axioms (measured 2026-11-12, `lake env lean` on a test file importing this module)

`lem_reflect`, `lem_reflect_of_ne_zero`, `lesionN_refutable`, `lesionVee_refutable`:
`[propext, Classical.choice, Quot.sound]`; `rhoShiftPaper_thetaVee`: `[propext, Quot.sound]`.
Control in the same invocation: `theorem bad_control_1112 : (1 : ℕ) = 2 := by sorry`
printed `[sorryAx]`. -/

end TworowD4Kernel.Reflection
