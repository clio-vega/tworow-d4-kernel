/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-!
# The ρ-shifted vanishing law

Formalises `thm:vanish` of
`projects/proofs/2026-10-22-c2-Q553-residue-groupings-and-head-collapse.tex`
(Clio, 22 Oct 2026, L388–L397), the forward direction only.

## The paper's statement

> **Theorem (ρ-shifted vanishing law).** If `θ_j - θ_k = k - j` for some `j < k`, then
> `Ψ^C_{(1^r),θ}(M) = 0` identically in `w`, for every `M`.
>
> *Proof.* `θ_j - θ_k = k - j` is exactly `m_j = m_k` for `m_j = θ_j + j - 1`. Then the
> matrix `(x_i^{m_j})` has two equal columns, so its determinant is zero for every `T`,
> and every summand of `thm:alt` vanishes.

The alternant expansion `thm:alt` (L341–L363) is **not** formalised here; it is the
unformalised layer, and it is the reason the parent registry node stays at `proved`.
What is formalised is the proof's two actual steps, and their composition:

* **(A) the index bridge** — `exists_rhoTie_iff_not_injective`: the hypothesis
  `∃ j ≠ k, θ_j - θ_k = k - j` is *equivalent* to `m` failing to be injective;
* **(B) the determinant half** — `det_zpow_eq_zero_of_not_injective` /
  `det_npow_eq_zero_of_not_injective`: a non-injective exponent vector gives two equal
  columns, hence a zero alternant;
* **(C) the composition** — `det_alternant_eq_zero_of_rhoTie` and its `j < k` form
  `det_alternant_eq_zero_of_rhoTie_lt`, which is the paper's hypothesis verbatim.

## Indexing: the paper is 1-indexed, `Fin r` is not

The paper's `j` runs over `1, …, r`; Lean's `j : Fin r` has `j.val ∈ {0, …, r-1}`.
So the paper's `m_j = θ_j + j - 1` is, in these coordinates, `θ j + j.val`, whereas
`rhoShift` below is `θ j + j.val - 1` — the brief's literal formula, and the paper's `m`
shifted by the constant `-1`. The constant is inert: `rhoShift_sub_const_injective_iff`
records that *every* constant shift leaves the hypothesis and the conclusion unchanged,
so nothing below depends on which convention is chosen.

## `zpow` or `npow`: which statement is the paper's

`m_j ∈ ℤ`, so `x_i ^ m_j` is a `zpow` and the paper's alternant is a *Laurent* alternant
over nonzero `w`-values (`Setup`, L41: "specialised to nonzero scalars"). That is the
`zpow` statement, and it is the one `det_alternant_eq_zero_of_rhoTie` proves. The `npow`
statement is proved separately rather than substituted for it.
-/

namespace TworowD4Kernel.RhoShiftVanishing

open Matrix

variable {r : ℕ}

/-- The ρ-shift `m_j = θ_j + j - 1`, in `Fin r`'s 0-indexed coordinates.

See the module docstring: this is the brief's literal formula, which is the paper's `m`
shifted by `-1` because the paper indexes from `1`. The shift is inert. -/
def rhoShift (θ : Fin r → ℤ) (j : Fin r) : ℤ := θ j + (j.val : ℤ) - 1

/-- Two ρ-shifted indices collide exactly when the paper's wall equation holds.
This is the whole content of the first sentence of the paper's proof. -/
theorem rhoShift_eq_iff (θ : Fin r → ℤ) (j k : Fin r) :
    rhoShift θ j = rhoShift θ k ↔ θ j - θ k = (k.val : ℤ) - (j.val : ℤ) := by
  unfold rhoShift
  omega

/-- **(A) The index bridge.** The paper's hypothesis is *equivalent* to non-injectivity of
the ρ-shift — not merely sufficient for it. -/
theorem exists_rhoTie_iff_not_injective (θ : Fin r → ℤ) :
    (∃ j k : Fin r, j ≠ k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) ↔
      ¬ Function.Injective (rhoShift θ) := by
  rw [Function.not_injective_iff]
  constructor
  · rintro ⟨j, k, hne, h⟩
    exact ⟨j, k, (rhoShift_eq_iff θ j k).2 h, hne⟩
  · rintro ⟨j, k, heq, hne⟩
    exact ⟨j, k, hne, (rhoShift_eq_iff θ j k).1 heq⟩

/-! ### L4: the additive constant in the ρ-shift is inert -/

/-- A constant shift cannot create or destroy a collision. -/
theorem injective_add_const_iff {α : Type*} (m : α → ℤ) (c : ℤ) :
    Function.Injective (fun a => m a + c) ↔ Function.Injective m := by
  constructor
  · intro h a b hab
    exact h (by simpa using congrArg (· + c) hab)
  · intro h a b hab
    exact h (by simpa using hab)

/-- The paper's own 1-indexed `m_j = θ_j + j - 1`, with `j` running over `1, …, r`. -/
def rhoShiftPaper (θ : Fin r → ℤ) (j : Fin r) : ℤ := θ j + ((j.val : ℤ) + 1) - 1

/-- The paper's `m` is this file's `rhoShift` plus the constant `1`. -/
theorem rhoShiftPaper_eq (θ : Fin r → ℤ) :
    rhoShiftPaper θ = fun j => rhoShift θ j + 1 := by
  funext j; unfold rhoShiftPaper rhoShift; omega

/-- Hence the two indexing conventions give the *same* vanishing hypothesis: L4 graded. -/
theorem injective_rhoShiftPaper_iff (θ : Fin r → ℤ) :
    Function.Injective (rhoShiftPaper θ) ↔ Function.Injective (rhoShift θ) := by
  rw [rhoShiftPaper_eq]; exact injective_add_const_iff _ 1

/-! ### (B) The determinant half: a repeated exponent is a repeated column -/

/-- **(B), `npow` arm.** Over any commutative ring, with *no* hypothesis on `x`. -/
theorem det_npow_eq_zero_of_not_injective {R : Type*} [CommRing R] (x : Fin r → R)
    (m : Fin r → ℕ) (hm : ¬ Function.Injective m) :
    (Matrix.of fun i j => x i ^ m j).det = 0 := by
  obtain ⟨j, k, heq, hne⟩ := Function.not_injective_iff.1 hm
  exact Matrix.det_zero_of_column_eq hne fun i => by simp [heq]

/-- **(B), `zpow` arm** — the paper's Laurent alternant. Note the absence of `x i ≠ 0`:
`zpow` is total on a `GroupWithZero`, and two equal columns are two equal columns whether
or not the entries are units. See `det_zpow_shift` for where invertibility *is* spent. -/
theorem det_zpow_eq_zero_of_not_injective {K : Type*} [Field K] (x : Fin r → K)
    (m : Fin r → ℤ) (hm : ¬ Function.Injective m) :
    (Matrix.of fun i j => x i ^ m j).det = 0 := by
  obtain ⟨j, k, heq, hne⟩ := Function.not_injective_iff.1 hm
  exact Matrix.det_zero_of_column_eq hne fun i => by simp [heq]

/-- Shifting every exponent by a constant `c` multiplies the determinant by the monomial
`∏ i, x i ^ c`. **This** is the statement that needs `x i ≠ 0`, and the vanishing law does
not use it. -/
theorem det_zpow_shift {K : Type*} [Field K] (x : Fin r → K) (hx : ∀ i, x i ≠ 0)
    (m : Fin r → ℤ) (c : ℤ) :
    (Matrix.of fun i j => x i ^ (m j + c)).det
      = (∏ i, x i ^ c) * (Matrix.of fun i j => x i ^ m j).det := by
  have h : (Matrix.of fun i j => x i ^ (m j + c))
      = Matrix.of fun i j => (x i ^ c) * (x i ^ m j) := by
    ext i j; simp [zpow_add₀ (hx i), mul_comm]
  rw [h, Matrix.det_mul_column]
  rfl

/-! ### (C) The composition — the paper's theorem -/

/-- **(C) The ρ-shifted vanishing law**, hypothesis as `j ≠ k`. -/
theorem det_alternant_eq_zero_of_rhoTie {K : Type*} [Field K] (x : Fin r → K)
    (θ : Fin r → ℤ)
    (h : ∃ j k : Fin r, j ≠ k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) :
    (Matrix.of fun i j => x i ^ (rhoShift θ j)).det = 0 :=
  det_zpow_eq_zero_of_not_injective x _ ((exists_rhoTie_iff_not_injective θ).1 h)

/-- **(C) The ρ-shifted vanishing law**, hypothesis verbatim as the paper states it
(`thm:vanish`, L388–L390: "if `θ_j - θ_k = k - j` for some `j < k`"). L1 is graded by the
fact that this is derived from the `j ≠ k` form by supplying `ne_of_lt`. -/
theorem det_alternant_eq_zero_of_rhoTie_lt {K : Type*} [Field K] (x : Fin r → K)
    (θ : Fin r → ℤ)
    (h : ∃ j k : Fin r, j < k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) :
    (Matrix.of fun i j => x i ^ (rhoShift θ j)).det = 0 := by
  obtain ⟨j, k, hlt, heq⟩ := h
  exact det_alternant_eq_zero_of_rhoTie x θ ⟨j, k, ne_of_lt hlt, heq⟩

/-- L1, the other direction: the `j < k` hypothesis is *equivalent* to the `j ≠ k` one, so
weakening `j < k` to `j ≠ k` is free. -/
theorem rhoTie_lt_iff_ne (θ : Fin r → ℤ) :
    (∃ j k : Fin r, j < k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) ↔
      (∃ j k : Fin r, j ≠ k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) := by
  constructor
  · rintro ⟨j, k, hlt, heq⟩; exact ⟨j, k, ne_of_lt hlt, heq⟩
  · rintro ⟨j, k, hne, heq⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨j, k, hlt, heq⟩
    · exact ⟨k, j, hgt, by omega⟩

/-! ### L3: the hypothesis's own quantifier range carries `2 ≤ r` -/

/-- The binder `2 ≤ r` is **absent**, not removable: `∃ j k : Fin r, j ≠ k` already
implies it, so the quantifier range is carrying the hypothesis. -/
theorem rhoTie_forces_two_le (θ : Fin r → ℤ)
    (h : ∃ j k : Fin r, j ≠ k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) : 2 ≤ r := by
  obtain ⟨j, k, hne, -⟩ := h
  have hv : j.val ≠ k.val := fun hv => hne (Fin.ext hv)
  have hj := j.isLt
  have hk := k.isLt
  omega

/-! ### Positive controls

`θ = (0, -1)` at `r = 2` is the degenerate flipped term `Ψ^C_{(1,1),(0,-1)} ≡ 0` of the
22 Oct session (`thm:vanish` discussion, L453). The second control is the one that shows
the theorem is not vacuous. -/

/-- Control A1: the tie hypothesis genuinely holds at `θ = (0, -1)`. -/
theorem control_tie_hypothesis :
    ∃ j k : Fin 2, j ≠ k ∧
      (![(0 : ℤ), -1]) j - (![(0 : ℤ), -1]) k = (k.val : ℤ) - (j.val : ℤ) :=
  ⟨0, 1, by decide, by decide⟩

/-- Control A2: and the determinant really is `0`, computed directly, not via the
theorem. -/
theorem control_tie_det_zero :
    (Matrix.of fun i j => (![(2 : ℚ), 3] i) ^ (rhoShift ![(0 : ℤ), -1] j)).det = 0 := by
  simp [Matrix.det_fin_two, rhoShift]

/-- Control B1 (non-vacuity): at `θ = (0, 0)` the ρ-shift *is* injective, so the theorem
does not apply. -/
theorem control_no_tie_injective : Function.Injective (rhoShift ![(0 : ℤ), 0]) := by
  decide

/-- Control B2 (non-vacuity): and there the determinant is **nonzero**, so the vanishing
law is not vacuously true of every `θ`. -/
theorem control_no_tie_det_ne_zero :
    (Matrix.of fun i j => (![(2 : ℚ), 3] i) ^ (rhoShift ![(0 : ℤ), 0] j)).det ≠ 0 := by
  simp [Matrix.det_fin_two, rhoShift]
  norm_num

end TworowD4Kernel.RhoShiftVanishing
