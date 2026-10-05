/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.LinearAlgebra.QuadraticForm.Real
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `lem:minor`: a symmetric matrix with one positive eigenvalue has nonpositive 2x2 minors

Formalisation of `lem:minor` from `proofs/2026-10-04-c3-Q-lorentzian.tex`, lines 487-510.

Statement: if `M` is a symmetric real `n x n` matrix with at most one positive eigenvalue and
with `M i i >= 0` for every `i`, then `M i i * M j j - M i j ^ 2 <= 0` for all `i, j`.

This is the step that turns "the Hessian has at most one positive eigenvalue" into the pairwise
inequality `k a ^ 2 >= k (a-1) * k (a+1)`, i.e. it is how PF2 is concluded.

## Why this is formalised rather than scripted

The only independent check this lemma ever had was a broken instrument: a sympy
`Poly.count_roots` based "exact positive eigenvalue count" that counts *distinct* roots, so
`4 * I 2` scored as having one positive eigenvalue. Its 600-matrix validation run reported zero
disagreements because random integer matrices almost never have a repeated eigenvalue -- it
sampled around its own defect. A single *false* violation of this lemma is what exposed it.

## How the hypothesis is stated

"At most one positive eigenvalue" is formalised as `sigPos Q <= 1`, where `Q` is the quadratic
form `x` maps to `x dotProduct (M *mulVec x)` and `sigPos` is Mathlib's Sylvester inertia index
(`sigPos`: the maximal `finrank` of a subspace on which `Q` is positive definite).
By the uniqueness half of Sylvester's law of inertia this is *mathematically* exactly the number
of positive eigenvalues counted with multiplicity.

**That bridge is NOT formalised, here or in Mathlib.** This file proves the `sigPos` form only.
An earlier draft of this docstring pointed the reader at a lemma
`sigPos_le_one_iff_card_pos_eigenvalues` "below"; no such declaration exists and none ever did.
The missing statement is

  `sigPos M.toQuadraticForm' = {k | 0 < hM.eigenvalues k}.ncard`  (`hM : M.IsHermitian`)

whose proof needs the `QuadraticMap.IsometryEquiv` from `M.toQuadraticForm'` to
`weightedSumSquares R hM.eigenvalues` induced by `Matrix.IsHermitian.spectral_theorem`, which is
unbuilt. Mathlib has `sigPos` and it has `Matrix.IsHermitian.eigenvalues`; nothing connects them,
and there is no Cauchy interlacing in Mathlib either.

This is a gap in *coverage*, not in the mathematics, and it costs the application nothing: the
paper proof never counts an eigenvalue. It produces a 2-dimensional positive-definite subspace and
contradicts a dimension bound, so `sigPos <= 1` is the hypothesis it actually uses.
-/

namespace TworowD4Kernel

open Matrix QuadraticForm QuadraticMap

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form of a matrix evaluates as `x ↦ x ⬝ᵥ (M *ᵥ x)`. -/
lemma toQuadraticForm'_apply (M : Matrix n n ℝ) (x : n → ℝ) :
    M.toQuadraticForm' x = x ⬝ᵥ (M *ᵥ x) := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply', dotProduct_mulVec]

omit [DecidableEq n] in
/-- A sum over `univ` of a function vanishing off `{i, j}` is the sum of its two values. -/
lemma sum_eq_pair {i j : n} (hij : i ≠ j) (f : n → ℝ)
    (hf : ∀ k, k ≠ i → k ≠ j → f k = 0) : ∑ k, f k = f i + f j := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({i, j} : Finset n))]
  · rw [Finset.sum_pair hij]
  · intro k _ hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact hf k hk.1 hk.2

/-- On the coordinate plane spanned by `e i` and `e j`, the quadratic form of a symmetric `M` is
the binary form `M i i * x i ^ 2 + 2 * M i j * x i * x j + M j j * x j ^ 2`. -/
lemma toQuadraticForm'_apply_of_mem_spanSubset (M : Matrix n n ℝ) (hsymm : M.IsSymm)
    {i j : n} (hij : i ≠ j) {x : n → ℝ} (hx : x ∈ Pi.spanSubset ℝ ({i, j} : Set n)) :
    M.toQuadraticForm' x
      = M i i * x i ^ 2 + 2 * M i j * (x i * x j) + M j j * x j ^ 2 := by
  have hz : ∀ k, k ≠ i → k ≠ j → x k = 0 := by
    intro k hki hkj
    exact Pi.mem_spanSubset_iff.mp hx k (by simp [hki, hkj])
  have hmv : ∀ k, (M *ᵥ x) k = M k i * x i + M k j * x j := by
    intro k
    rw [mulVec, dotProduct]
    exact sum_eq_pair hij _ fun l hli hlj ↦ by rw [hz l hli hlj, mul_zero]
  rw [toQuadraticForm'_apply, dotProduct]
  rw [sum_eq_pair hij _ fun k hki hkj ↦ by rw [hz k hki hkj, zero_mul]]
  rw [hmv i, hmv j]
  have hji : M j i = M i j := by
    have := hsymm
    rw [Matrix.IsSymm] at this
    calc M j i = Mᵀ i j := rfl
    _ = M i j := by rw [this]
  rw [hji]
  ring

/-- **`lem:minor`**, in the Sylvester-signature form of the hypothesis.

If `M` is a symmetric real matrix whose quadratic form is positive definite on no
two-dimensional subspace (`sigPos ≤ 1`, i.e. `M` has at most one positive eigenvalue) and whose
diagonal entries are nonnegative, then every `2 × 2` principal minor is nonpositive. -/
theorem minor_nonpos_of_sigPos_le_one (M : Matrix n n ℝ) (hsymm : M.IsSymm)
    (hdiag : ∀ i, 0 ≤ M i i) (hsig : sigPos M.toQuadraticForm' ≤ 1)
    (i j : n) : M i i * M j j - M i j ^ 2 ≤ 0 := by
  -- The diagonal case is an identity, not an inequality.
  rcases eq_or_ne i j with rfl | hij
  · have h : M i i * M i i - M i i ^ 2 = 0 := by ring
    linarith
  -- Off-diagonal: suppose the minor is positive and build a 2-dimensional positive definite
  -- subspace, contradicting `sigPos ≤ 1`.
  by_contra hcon
  have hdet : 0 < M i i * M j j - M i j ^ 2 := not_le.mp hcon
  -- `M i i` is nonzero, hence strictly positive: `M i i * M j j > M i j ^ 2 ≥ 0`.
  have ha : 0 < M i i := by
    rcases lt_or_eq_of_le (hdiag i) with h | h
    · exact h
    · exact absurd hdet (by rw [← h]; nlinarith [sq_nonneg (M i j)])
  -- The coordinate plane `V = span {e i, e j}` has dimension 2.
  have hdim : Module.finrank ℝ (Pi.spanSubset ℝ ({i, j} : Set n)) = 2 := by
    rw [Pi.dim_spanSubset, Set.ncard_pair hij]
  -- `M.toQuadraticForm'` is positive definite on `V`.
  have hposdef : (M.toQuadraticForm'.restrict (Pi.spanSubset ℝ ({i, j} : Set n))).PosDef := by
    intro y hy
    rw [QuadraticMap.restrict_apply]
    obtain ⟨x, hx⟩ := y
    have hne : x ≠ 0 := by simpa using hy
    have hz : ∀ k, k ≠ i → k ≠ j → x k = 0 := fun k hki hkj ↦
      Pi.mem_spanSubset_iff.mp hx k (by simp [hki, hkj])
    rw [toQuadraticForm'_apply_of_mem_spanSubset M hsymm hij hx]
    rcases eq_or_ne (x j) 0 with hj0 | hj0
    · -- `x j = 0`, so `x i ≠ 0` and the form is `M i i * x i ^ 2 > 0`.
      have hi0 : x i ≠ 0 := by
        intro hi0
        refine hne (funext fun k ↦ ?_)
        rcases eq_or_ne k i with rfl | hki
        · simpa using hi0
        rcases eq_or_ne k j with rfl | hkj
        · simpa using hj0
        · simpa using hz k hki hkj
      have hsq : 0 < x i ^ 2 := by positivity
      rw [hj0]
      nlinarith
    · -- `x j ≠ 0`: complete the square,
      -- `M i i * q = (M i i * x i + M i j * x j) ^ 2 + det * x j ^ 2`.
      have hsq : 0 < x j ^ 2 := by positivity
      have h1 : 0 < (M i i * M j j - M i j ^ 2) * x j ^ 2 := mul_pos hdet hsq
      nlinarith [sq_nonneg (M i i * x i + M i j * x j)]
  -- Contradiction: `2 = finrank V ≤ sigPos ≤ 1`.
  have h2 : 2 ≤ sigPos M.toQuadraticForm' := by
    rw [← hdim]
    exact le_sigPos_of_posDef M.toQuadraticForm' hposdef
  omega

end TworowD4Kernel
