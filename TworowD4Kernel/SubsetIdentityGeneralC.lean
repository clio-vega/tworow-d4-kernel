/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.NumberLemmaC2
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The general-`c` subset and central-tip identities, and the `c = 3` Number Lemma

This file formalises the two pure-`Nat.choose` identities that are the load-bearing combinatorial
core of the general-`c` Number Lemma `NL_c` (the proof note `2026-06-14-numberlemma-general-c.md`).
Both are stated over `ℕ`, parametrised by `c`. They are exactly the pieces that `number_lemma_C2`
hard-codes at `c = 2`, here lifted to arbitrary `c`.

As a corollary — the secondary goal of the cycle — we assemble the `c = 3` instance of the Number
Lemma (`NL_3`), `v₂ C(F+5, j) + v₂(j^{(6)}) ≥ v₂(F) + 3`, mirroring the assembly of
`number_lemma_C2`.

## Main results

* `TworowD4Kernel.choose_mul_choose_subset` (Move 1, "the subset-of-a-subset identity"): for
  `2*c ≤ j`,
  `C(F + 2c − 1, j) · C(j, 2c) = C(F + 2c − 1, 2c) · C(F − 1, j − 2c)`.
  This is `Nat.choose_mul` read with `n = F + 2c − 1`, `s = 2c`; the only arithmetic is
  `(F + 2c − 1) − 2c = F − 1`.

* `TworowD4Kernel.descFactorial_two_mul_eq` (Move 2, "the central tip"): the falling-factorial /
  binomial bridge `j^{(2c)} = (2c)! · C(j, 2c)`, i.e.
  `j.descFactorial (2*c) = (2*c)! * j.choose (2*c)`.
  This is `Nat.descFactorial_eq_factorial_mul_choose` at `k = 2c`.

* `TworowD4Kernel.number_lemma_C3` (the `c = 3` Number Lemma): for **even** `F ≥ 2` and
  `6 ≤ j ≤ F + 5`,
  `v₂(F) + 3 ≤ v₂(C(F+5, j)) + v₂(j(j−1)(j−2)(j−3)(j−4)(j−5))`.
  The constant `+3 = β(3)` is taken from the PROVE output, not invented.

## Proof outline of `NL_3` (faithful to §2 of the proof at `c = 3`)

Let `φ = v₂(F)`. Three ingredients:
* `v₂(j^{(6)}) = v₂(720) + v₂(C(j,6)) = 4 + v₂(C(j,6))` (central-tip identity, `v₂(6!) = 4`).
* The subset identity gives `v₂(C(F+5,j)) + v₂(C(j,6)) = v₂(C(F+5,6)) + v₂(C(F−1,j−6)) ≥
  v₂(C(F+5,6))`.
* The **anchor**: `720·C(F+5,6) = F(F+1)(F+2)(F+3)(F+4)(F+5)`, a product of six consecutive
  integers starting at the even `F`; hence `4 + v₂(C(F+5,6)) = v₂(F) + v₂(F+2) + v₂(F+4)` (only the
  three even offsets survive). Among the two consecutive halves `F/2 + 1`, `F/2 + 2` one is even,
  so `v₂(F+2) + v₂(F+4) ≥ 3`, giving `v₂(C(F+5,6)) ≥ φ − 1` (the bound `NL_3` consumes).

Adding `4`: `v₂(C(F+5,j)) + v₂(j^{(6)}) = [v₂(C(F+5,j)) + v₂(C(j,6))] + 4 ≥ v₂(C(F+5,6)) + 4 =
φ + v₂(F+2) + v₂(F+4) ≥ φ + 3`.

## References

`2026-06-14-numberlemma-general-c.md`, §2 (Moves 1–3 and the anchor minimisation, here at `c = 3`)
and `2026-06-13-threerow-c2-Jstar-even.md`, §3 (the `c = 2` template that is generalised). Reuses
the `vz` valuation wrapper of `D0ClosedForms.lean`.
-/

namespace TworowD4Kernel

open Nat

/-! ## Primary — the two general-`c` `Nat.choose` identities -/

/-- **Move 1 — the subset-of-a-subset identity (load-bearing), general `c`.**

For naturals `F`, `c`, `j` with `2*c ≤ j`,
`C(F + 2c − 1, j) · C(j, 2c) = C(F + 2c − 1, 2c) · C(F − 1, j − 2c)`.

Both sides count "choose `j` of `F + 2c − 1`, then `2c` of those `j`" = "choose `2c` of
`F + 2c − 1`, then the remaining `j − 2c` from the other `F − 1`". This is `Nat.choose_mul` with
`n = F + 2c − 1`, `s = 2c`; the only arithmetic is `(F + 2c − 1) − 2c = F − 1`. The `c = 2` instance
`C(F+3,j)·C(j,4) = C(F+3,4)·C(F−1,j−4)` is the `hsubset` step of `number_lemma_C2`. -/
theorem choose_mul_choose_subset (F c j : ℕ) (hj : 2 * c ≤ j) :
    (F + 2 * c - 1).choose j * j.choose (2 * c)
      = (F + 2 * c - 1).choose (2 * c) * (F - 1).choose (j - 2 * c) := by
  have h := Nat.choose_mul (n := F + 2 * c - 1) (k := j) (s := 2 * c) hj
  rwa [show F + 2 * c - 1 - 2 * c = F - 1 by omega] at h

/-- **Move 2 — the central-tip identity, general `c`.**

The falling factorial `j^{(2c)} = j(j−1)⋯(j−2c+1)` (here `Nat.descFactorial j (2*c)`) equals
`(2c)! · C(j, 2c)`. This is `Nat.descFactorial_eq_factorial_mul_choose` specialised to block size
`2c`; it converts the inhomogeneous tip `−(2c)!·C(j,2c)` of the `2c`-tic `Q_c` between its
falling-factorial and binomial forms, and pins `v₂(j^{(2c)}) = v₂((2c)!) + v₂(C(j,2c))`. -/
theorem descFactorial_two_mul_eq (j c : ℕ) :
    j.descFactorial (2 * c) = (2 * c)! * j.choose (2 * c) :=
  Nat.descFactorial_eq_factorial_mul_choose j (2 * c)

/-! ## Secondary — the `c = 3` Number Lemma `NL_3` -/

/-- `n.descFactorial 6 = n(n−1)(n−2)(n−3)(n−4)(n−5)`, the six-factor falling factorial written
out (the `c = 3` analogue of `descFactorial_four`). -/
theorem descFactorial_six (n : ℕ) :
    n.descFactorial 6 = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) := by
  rw [show (6 : ℕ) = 5 + 1 from rfl, Nat.descFactorial_succ, show (5 : ℕ) = 4 + 1 from rfl,
    Nat.descFactorial_succ, show (4 : ℕ) = 3 + 1 from rfl, Nat.descFactorial_succ,
    show (3 : ℕ) = 2 + 1 from rfl, Nat.descFactorial_succ, show (2 : ℕ) = 1 + 1 from rfl,
    Nat.descFactorial_succ, Nat.descFactorial_one]
  generalize n - 1 = a; generalize n - 2 = b; generalize n - 3 = d; generalize n - 4 = e
  generalize n - 5 = f
  ring

/-- `v₂(720) = 4`, since `720 = 2⁴ · 45` (this is `v₂(6!)`). -/
theorem vz_720 : vz 720 = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : padicValNat 2 720 = 4 := by
    rw [show (720 : ℕ) = 2 ^ 4 * 45 from rfl, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
  simp only [vz, this]; norm_num

/-- The product-to-binomial bridge `n(n−1)(n−2)(n−3)(n−4)(n−5) = 720 · C(n,6)` (both sides vanish
for `n < 6`, so no lower bound on `n` is needed). The `c = 3` analogue of `fourProduct_eq`. -/
theorem sixProduct_eq (n : ℕ) :
    n * (n - 1) * (n - 2) * (n - 3) * (n - 4) * (n - 5) = 720 * n.choose 6 := by
  rw [← descFactorial_six, Nat.descFactorial_eq_factorial_mul_choose, show (6 : ℕ)! = 720 from rfl]

/-- If `4 ∣ n` and `n ≠ 0` then `v₂(n) ≥ 2`. Used at the anchor-minimisation step of `NL_3`,
where among the two consecutive integers `F/2 + 1`, `F/2 + 2` the even one forces one of `F + 2`,
`F + 4` to be divisible by `4`. -/
theorem vz_two_le_of_four_dvd {n : ℕ} (hn : n ≠ 0) (h4 : 4 ∣ n) : (2 : ℤ) ≤ vz n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h : 2 ≤ padicValNat 2 n :=
    (padicValNat_dvd_iff_le (p := 2) hn).mp (by rw [show (2 : ℕ) ^ 2 = 4 from rfl]; exact h4)
  simp only [vz]; exact_mod_cast h

/-- **The Number Lemma at `c = 3` (`NL_3`).**

For **even** `F ≥ 2` and `6 ≤ j ≤ F + 5`,

> `v₂(F) + 3 ≤ v₂(C(F+5, j)) + v₂(j(j−1)(j−2)(j−3)(j−4)(j−5))`.

The constant `+3 = β(3)` is the sharp anchor from `2026-06-14-numberlemma-general-c.md`. This is
the `c = 3` instance of `NL_c` and the tip bound that closes Gap 1 of the three-row `c = 3`
even-`|J*|` analysis; the hypothesis `j ≤ F + 5` is the application range, exactly where the
subset-of-a-subset valuation identity is valid. -/
theorem number_lemma_C3 (F j : ℕ) (hF2 : 2 ∣ F) (hF : 2 ≤ F) (hj6 : 6 ≤ j) (hjF : j ≤ F + 5) :
    padicValNat 2 F + 3 ≤
      padicValNat 2 ((F + 5).choose j) +
        padicValNat 2 (j * (j - 1) * (j - 2) * (j - 3) * (j - 4) * (j - 5)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- nonzero binomials in range
  have hcj6 : j.choose 6 ≠ 0 := (Nat.choose_pos hj6).ne'
  have hcFj : (F + 5).choose j ≠ 0 := (Nat.choose_pos (by omega : j ≤ F + 5)).ne'
  have hcF6 : (F + 5).choose 6 ≠ 0 := (Nat.choose_pos (by omega : 6 ≤ F + 5)).ne'
  have hcF1 : (F - 1).choose (j - 6) ≠ 0 := (Nat.choose_pos (by omega : j - 6 ≤ F - 1)).ne'
  -- (1) `v₂(j(j−1)⋯(j−5)) = 4 + v₂(C(j,6))`
  have hprod : vz (j * (j - 1) * (j - 2) * (j - 3) * (j - 4) * (j - 5)) = 4 + vz (j.choose 6) := by
    rw [sixProduct_eq j, vz_mul (by norm_num) hcj6, vz_720]
  -- (2) subset identity ⟹ `v₂(C(F+5,j)) + v₂(C(j,6)) ≥ v₂(C(F+5,6))`
  have hsubset : (F + 5).choose j * j.choose 6 = (F + 5).choose 6 * (F - 1).choose (j - 6) := by
    have h := choose_mul_choose_subset F 3 j (by omega)
    simpa using h
  have hsub_ge : vz ((F + 5).choose 6) ≤ vz ((F + 5).choose j) + vz (j.choose 6) := by
    have hsub_vz : vz ((F + 5).choose j) + vz (j.choose 6)
        = vz ((F + 5).choose 6) + vz ((F - 1).choose (j - 6)) := by
      rw [← vz_mul hcFj hcj6, ← vz_mul hcF6 hcF1, hsubset]
    have hnn : (0 : ℤ) ≤ vz ((F - 1).choose (j - 6)) := by
      simp only [vz]; exact Int.natCast_nonneg _
    linarith
  -- (3) anchor: `720·C(F+5,6) = F(F+1)⋯(F+5)`, so `4 + v₂(C(F+5,6)) = v₂F + v₂(F+2) + v₂(F+4)`
  have hFprod : (F + 5) * (F + 4) * (F + 3) * (F + 2) * (F + 1) * F = 720 * (F + 5).choose 6 := by
    have h := sixProduct_eq (F + 5)
    rwa [show F + 5 - 1 = F + 4 by omega, show F + 5 - 2 = F + 3 by omega,
      show F + 5 - 3 = F + 2 by omega, show F + 5 - 4 = F + 1 by omega,
      show F + 5 - 5 = F by omega] at h
  have hFprod_vz : vz ((F + 5) * (F + 4) * (F + 3) * (F + 2) * (F + 1) * F)
      = vz (F + 5) + vz (F + 4) + vz (F + 3) + vz (F + 2) + vz (F + 1) + vz F := by
    rw [vz_mul (by positivity) (by omega), vz_mul (by positivity) (by omega),
      vz_mul (by positivity) (by omega), vz_mul (by positivity) (by omega),
      vz_mul (by omega) (by omega)]
  -- the three odd offsets contribute `0`
  have hodd1 : vz (F + 1) = 0 := by
    simp [vz, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ (F + 1) by omega)]
  have hodd3 : vz (F + 3) = 0 := by
    simp [vz, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ (F + 3) by omega)]
  have hodd5 : vz (F + 5) = 0 := by
    simp [vz, padicValNat.eq_zero_of_not_dvd (show ¬ 2 ∣ (F + 5) by omega)]
  have hanchor : (4 : ℤ) + vz ((F + 5).choose 6) = vz F + vz (F + 2) + vz (F + 4) := by
    have h720 : vz ((F + 5) * (F + 4) * (F + 3) * (F + 2) * (F + 1) * F)
        = 4 + vz ((F + 5).choose 6) := by
      rw [hFprod, vz_mul (by norm_num) hcF6, vz_720]
    rw [hFprod_vz, hodd1, hodd3, hodd5] at h720
    linarith
  -- (4) anchor minimisation: `v₂(F+2) + v₂(F+4) ≥ 3` (one of `F+2`, `F+4` is divisible by `4`)
  have hev2 : (1 : ℤ) ≤ vz (F + 2) := by
    simp only [vz]
    exact_mod_cast one_le_padicValNat_of_dvd (by omega) (by omega)
  have hev4 : (1 : ℤ) ≤ vz (F + 4) := by
    simp only [vz]
    exact_mod_cast one_le_padicValNat_of_dvd (by omega) (by omega)
  have hmin : (3 : ℤ) ≤ vz (F + 2) + vz (F + 4) := by
    rcases (by omega : F % 4 = 0 ∨ F % 4 = 2) with h0 | h2
    · -- `F ≡ 0 (mod 4)` ⟹ `4 ∣ F + 4`
      have := vz_two_le_of_four_dvd (n := F + 4) (by omega) (by omega)
      linarith
    · -- `F ≡ 2 (mod 4)` ⟹ `4 ∣ F + 2`
      have := vz_two_le_of_four_dvd (n := F + 2) (by omega) (by omega)
      linarith
  -- assemble: `φ + 3 ≤ v₂(C(F+5,j)) + (4 + v₂(C(j,6)))`
  have key : (padicValNat 2 F : ℤ) + 3
      ≤ (padicValNat 2 ((F + 5).choose j) : ℤ)
        + (padicValNat 2 (j * (j - 1) * (j - 2) * (j - 3) * (j - 4) * (j - 5)) : ℤ) := by
    have hCfinal : ((padicValNat 2 ((F + 5).choose j) : ℤ)) = vz ((F + 5).choose j) := by
      simp only [vz]
    have hprodcast : ((padicValNat 2 (j * (j - 1) * (j - 2) * (j - 3) * (j - 4) * (j - 5)) : ℤ))
        = 4 + vz (j.choose 6) := by rw [← hprod]; simp only [vz]
    have hφ : ((padicValNat 2 F : ℤ)) = vz F := by simp only [vz]
    rw [hCfinal, hprodcast, hφ]
    linarith [hsub_ge, hanchor, hmin]
  exact_mod_cast key

end TworowD4Kernel
