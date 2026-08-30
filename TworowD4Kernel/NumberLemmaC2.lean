/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.D0ClosedForms
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# The Number Lemma of the three-row `c = 2` even-`|J*|` closure (`d = 4`)

This file formalises the load-bearing arithmetic fact of §3 of the **three-row `c = 2` family
closure** (`~/projects/proofs/2026-06-13-threerow-c2-Jstar-even.md`, "Number Lemma"). It is the
2-adic kernel of the `c = 2` Compensation Lemma `T(j) ≥ 1 − v₂(j)` — and `c = 2` is the **first**
three-row family where the second generator `4` is real (the tie set can be `{0, 4}`, not just
`{0, 2}`). The `1 − v₂(j)` deficit on the right, which the Number Lemma supplies, is exactly what
lets both `j = 2` and `j = 4` reach the tie threshold.

## The lemma

Writing `v₂ = padicValNat 2`, for **even** `F ≥ 2` and `4 ≤ j ≤ F + 3`,

> `v₂(F) + 1 ≤ v₂(C(F+3, j)) + v₂(j(j−1)(j−2)(j−3))`.

### The range `j ≤ F + 3`

The paper states the Number Lemma for "every `j ≥ 4`" and proves it via the subset-of-a-subset
identity `C(F+3,j)·C(j,4) = C(F+3,4)·C(F−1,j−4)`, which (as a *valuation* identity) is only valid
while every binomial is nonzero, i.e. `j ≤ F + 3`. In the application the index obeys
`j ≤ b ≤ F + 3` (with `F ∈ {a, b−1}`, so `F + 3 ∈ {a+3, b+2} ≥ b`), so this is exactly the range
that is used; we state it as a hypothesis. The bound was numerically confirmed over all even
`F ≤ 1000`, `4 ≤ j ≤ F + 3` (zero counterexamples).

## Proof outline (faithful to §3)

Let `φ = v₂(F)`. Two ingredients:
* `v₂(j(j−1)(j−2)(j−3)) = 3 + v₂(C(j,4))`, since `j(j−1)(j−2)(j−3) = 4! · C(j,4) = 24 · C(j,4)`
  (`Nat.descFactorial_eq_factorial_mul_choose`) and `v₂(24) = 3`.
* The subset identity gives `v₂(C(F+3,j)) + v₂(C(j,4)) = v₂(C(F+3,4)) + v₂(C(F−1,j−4)) ≥
  v₂(C(F+3,4))`; and `3 + v₂(C(F+3,4)) = v₂(F(F+1)(F+2)(F+3)) = φ + v₂(F+2)` (only `F` and `F+2`
  are even among four consecutive integers), with `v₂(F+2) ≥ 1`, so `v₂(C(F+3,4)) ≥ φ − 2`.

Adding `3`: `v₂(C(F+3,j)) + v₂(j(j−1)(j−2)(j−3)) = [v₂(C(F+3,j)) + v₂(C(j,4))] + 3 ≥
v₂(C(F+3,4)) + 3 ≥ (φ − 2) + 3 = φ + 1`.

## References

`2026-06-13-threerow-c2-Jstar-even.md`, §3 (the Compensation Lemma and its reduction to the Number
Lemma). Reuses the `vz` valuation wrapper of `D0ClosedForms.lean`.
-/

namespace TworowD4Kernel

open Nat

/-- `n.descFactorial 4 = n(n−1)(n−2)(n−3)`, the four-factor falling factorial written out. -/
theorem descFactorial_four (n : ℕ) :
    n.descFactorial 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  rw [show (4 : ℕ) = 3 + 1 from rfl, Nat.descFactorial_succ, show (3 : ℕ) = 2 + 1 from rfl,
    Nat.descFactorial_succ, show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ,
    Nat.descFactorial_one]
  generalize n - 1 = a; generalize n - 2 = b; generalize n - 3 = c
  ring

/-- `v₂(24) = 3`, since `24 = 2³ · 3`. -/
theorem vz_twentyfour : vz 24 = 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : padicValNat 2 24 = 3 := by
    rw [show (24 : ℕ) = 2 ^ 3 * 3 from rfl, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  simp only [vz, this]; norm_num

/-- The product-to-binomial bridge `n(n−1)(n−2)(n−3) = 24 · C(n,4)` (both sides vanish for
`n < 4`, so no lower bound on `n` is needed). -/
theorem fourProduct_eq (n : ℕ) :
    n * (n - 1) * (n - 2) * (n - 3) = 24 * n.choose 4 := by
  rw [← descFactorial_four, Nat.descFactorial_eq_factorial_mul_choose, show (4 : ℕ)! = 24 from rfl]

/-- **The Number Lemma** (`2026-06-13-threerow-c2-Jstar-even.md`, §3).

For **even** `F ≥ 2` and `4 ≤ j ≤ F + 3`,

> `v₂(F) + 1 ≤ v₂(C(F+3, j)) + v₂(j(j−1)(j−2)(j−3))`.

This is the pure number-theoretic core of the `c = 2` Compensation Lemma — the place where the
second generator `4` becomes real. The hypothesis `j ≤ F + 3` is the application range and is
exactly where the subset-of-a-subset valuation identity is valid (see the module docstring). -/
theorem number_lemma_C2 (F j : ℕ) (hF2 : 2 ∣ F) (hF : 2 ≤ F) (hj4 : 4 ≤ j) (hjF : j ≤ F + 3) :
    padicValNat 2 F + 1 ≤
      padicValNat 2 ((F + 3).choose j) + padicValNat 2 (j * (j - 1) * (j - 2) * (j - 3)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- nonzero binomials in range
  have hcj4 : j.choose 4 ≠ 0 := (Nat.choose_pos hj4).ne'
  have hcFj : (F + 3).choose j ≠ 0 := (Nat.choose_pos (by omega : j ≤ F + 3)).ne'
  have hcF4 : (F + 3).choose 4 ≠ 0 := (Nat.choose_pos (by omega : 4 ≤ F + 3)).ne'
  have hcF1 : (F - 1).choose (j - 4) ≠ 0 := (Nat.choose_pos (by omega : j - 4 ≤ F - 1)).ne'
  -- (1) `v₂(j(j−1)(j−2)(j−3)) = 3 + v₂(C(j,4))`
  have hprod : vz (j * (j - 1) * (j - 2) * (j - 3)) = 3 + vz (j.choose 4) := by
    rw [fourProduct_eq j, vz_mul (by norm_num) hcj4, vz_twentyfour]
  -- (2) subset identity ⟹ `v₂(C(F+3,j)) + v₂(C(j,4)) ≥ v₂(C(F+3,4))`
  have hsubset : (F + 3).choose j * j.choose 4 = (F + 3).choose 4 * (F - 1).choose (j - 4) := by
    have h := Nat.choose_mul (n := F + 3) (k := j) (s := 4) hj4
    rwa [show F + 3 - 4 = F - 1 by omega] at h
  have hsub_vz : vz ((F + 3).choose j) + vz (j.choose 4)
      = vz ((F + 3).choose 4) + vz ((F - 1).choose (j - 4)) := by
    rw [← vz_mul hcFj hcj4, ← vz_mul hcF4 hcF1, hsubset]
  have hsub_ge : vz ((F + 3).choose 4) ≤ vz ((F + 3).choose j) + vz (j.choose 4) := by
    have hnn : (0 : ℤ) ≤ vz ((F - 1).choose (j - 4)) := by
      simp only [vz]; exact Int.natCast_nonneg _
    linarith
  -- (3) `3 + v₂(C(F+3,4)) = φ + v₂(F+2)`, hence `v₂(C(F+3,4)) ≥ φ − 2`
  have hFprod : (F + 3) * (F + 2) * (F + 1) * F = 24 * (F + 3).choose 4 := by
    have h := fourProduct_eq (F + 3)
    rwa [show F + 3 - 1 = F + 2 by omega, show F + 3 - 2 = F + 1 by omega,
      show F + 3 - 3 = F by omega] at h
  have hFprod_vz : vz ((F + 3) * (F + 2) * (F + 1) * F)
      = vz (F + 3) + vz (F + 2) + vz (F + 1) + vz F := by
    rw [vz_mul (by positivity) (by omega), vz_mul (by positivity) (by omega),
      vz_mul (by omega) (by omega)]
  have hodd1 : vz (F + 1) = 0 := by
    have h : padicValNat 2 (F + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    simp [vz, h]
  have hodd3 : vz (F + 3) = 0 := by
    have h : padicValNat 2 (F + 3) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
    simp [vz, h]
  have hev2 : (1 : ℤ) ≤ vz (F + 2) := by
    simp only [vz]
    have : 1 ≤ padicValNat 2 (F + 2) :=
      one_le_padicValNat_of_dvd (by omega) (by omega)
    exact_mod_cast this
  have hC4 : (3 : ℤ) + vz ((F + 3).choose 4) = vz F + vz (F + 2) := by
    have h24 : vz ((F + 3) * (F + 2) * (F + 1) * F) = 3 + vz ((F + 3).choose 4) := by
      rw [hFprod, vz_mul (by norm_num) hcF4, vz_twentyfour]
    rw [hFprod_vz, hodd1, hodd3] at h24
    linarith
  -- assemble: `φ + 1 ≤ v₂(C(F+3,j)) + (3 + v₂(C(j,4)))`
  have hφ : vz F = (padicValNat 2 F : ℤ) := by simp only [vz]
  have hCfinal : vz ((F + 3).choose j) = (padicValNat 2 ((F + 3).choose j) : ℤ) := by
    simp only [vz]
  have key : (padicValNat 2 F : ℤ) + 1
      ≤ (padicValNat 2 ((F + 3).choose j) : ℤ)
        + (padicValNat 2 (j * (j - 1) * (j - 2) * (j - 3)) : ℤ) := by
    have hprodcast : (padicValNat 2 (j * (j - 1) * (j - 2) * (j - 3)) : ℤ)
        = 3 + vz (j.choose 4) := by rw [← hprod]; simp only [vz]
    rw [← hCfinal, hprodcast]
    -- v₂(C(F+3,j)) + 3 + v₂(C(j,4)) ≥ v₂(C(F+3,4)) + 3 ≥ (φ-2)+3 = φ+1
    linarith [hsub_ge, hC4, hev2, hφ]
  exact_mod_cast key

end TworowD4Kernel
