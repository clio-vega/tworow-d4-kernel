/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ArithKernel
import Mathlib.Data.Nat.Choose.Basic

/-!
# The `D₀(j)` closed forms of the two-row `d = 4` law (`b ≡ 0 (mod 4)`, §3, Lemma 1)

This file formalises **Lemma 1** of §3 of the `b ≡ 0 (mod 4)` proof
(`~/projects/proofs/2026-06-08-tworow-d4-b0mod4-proved.md`): the two closed forms for the
`m`-independent offset `D₀(j)` that drives the tie analysis (§5) and hence the whole `b ≡ 0`
case of the two-row `d = 4` fiber-vanishing law.

## The offset

In the term decomposition `v₂(τ_j) − a = D₀(j) + S_j(m)` (§3), the offset is
`D₀(j) = h + v₂(R!) − v₂(j!) − v₂(β_j!)`, with `h := ⌊j/2⌋` and
`β_j = R − h` for `j` odd, `R + 1 − h` for `j` even. Because the even-case value
`v₂(C(R, h−1)) − v₂(h)` can be **negative**, `D₀` genuinely lives in `ℤ`, and these lemmas are
stated over `ℤ` (the valuations `padicValNat 2 _` are cast in via `vz`).

## Main results

* `TworowD4Kernel.D0_odd` — for `j = 2h + 1` odd (`β_j = R − h`):
  `h + v₂(R!) − v₂((2h+1)!) − v₂((R−h)!) = v₂(C(R, h))`.

* `TworowD4Kernel.D0_even` — for `j = 2h` even (`β_j = R + 1 − h`):
  `h + v₂(R!) − v₂((2h)!) − v₂((R+1−h)!) = v₂(C(R, h−1)) − v₂(h)`.

Both reduce, via the additive choose-factorisation `vz_choose`
(`v₂(C(R,h)) + v₂(h!) + v₂((R−h)!) = v₂(R!)`, the `padicValNat` shadow of
`Nat.choose_mul_factorial_mul_factorial`) and the doubling identity
`padicValNat_two_factorial_two_mul` (`v₂((2h)!) = h + v₂(h!)`, from the companion kernel file),
to elementary `ℤ`-linear arithmetic — exactly the bookkeeping of §3.

## References

`2026-06-08-tworow-d4-b0mod4-proved.md`, §3 (Lemma 1) and §2 (the `j = 1` term, where `a` is
pinned).
-/

namespace TworowD4Kernel

open Nat

/-- The 2-adic valuation of a natural number, cast to `ℤ`. The offset `D₀(j)` of §3 can be
negative (even case `v₂(C(R,h−1)) − v₂(h)`), so the closed forms are stated over `ℤ`. -/
def vz (n : ℕ) : ℤ := (padicValNat 2 n : ℤ)

@[simp] theorem vz_def (n : ℕ) : vz n = (padicValNat 2 n : ℤ) := rfl

/-- Multiplicativity of `vz` on nonzero arguments (the `ℤ`-cast of `padicValNat.mul`). -/
theorem vz_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : vz (a * b) = vz a + vz b := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  simp only [vz, padicValNat.mul ha hb, Nat.cast_add]

/-- **The additive choose-factorisation.** For `h ≤ R`,
`v₂(C(R, h)) + v₂(h!) + v₂((R−h)!) = v₂(R!)`. This is the `vz` image of the integer identity
`C(R,h) · h! · (R−h)! = R!` (`Nat.choose_mul_factorial_mul_factorial`), and is the single source
of both closed forms in Lemma 1. -/
theorem vz_choose {R h : ℕ} (hh : h ≤ R) :
    vz (R.choose h) + vz h ! + vz (R - h)! = vz R ! := by
  have hch : R.choose h ≠ 0 := (Nat.choose_pos hh).ne'
  have hf : h ! ≠ 0 := Nat.factorial_ne_zero h
  have hf' : (R - h)! ≠ 0 := Nat.factorial_ne_zero _
  have key : R.choose h * h ! * (R - h)! = R ! := Nat.choose_mul_factorial_mul_factorial hh
  calc vz (R.choose h) + vz h ! + vz (R - h)!
      = vz (R.choose h * h ! * (R - h)!) := by
        rw [vz_mul (mul_ne_zero hch hf) hf', vz_mul hch hf]
    _ = vz R ! := by rw [key]

/-- `vz ((k+1)!) = vz (k+1) + vz (k!)`, the `vz` image of `Nat.factorial_succ`. -/
theorem vz_factorial_succ (k : ℕ) : vz (k + 1)! = vz (k + 1) + vz k ! := by
  rw [Nat.factorial_succ, vz_mul (Nat.succ_ne_zero k) (Nat.factorial_ne_zero k)]

/-- `v₂((2h)!) = h + v₂(h!)`, the doubling identity, cast to `ℤ`.
Wraps `padicValNat_two_factorial_two_mul` from the companion `b ≡ 1` kernel file. -/
theorem vz_two_mul_factorial (h : ℕ) : vz (2 * h)! = (h : ℤ) + vz h ! := by
  simp only [vz, padicValNat_two_factorial_two_mul, Nat.cast_add]

/-- `v₂((2h+1)!) = v₂((2h)!)`: the odd factor `2h+1` contributes no power of 2. -/
theorem vz_two_mul_succ_factorial (h : ℕ) : vz (2 * h + 1)! = vz (2 * h)! := by
  have hodd : padicValNat 2 (2 * h + 1) = 0 := padicValNat.eq_zero_of_not_dvd (by omega)
  rw [Nat.factorial_succ, vz_mul (Nat.succ_ne_zero _) (Nat.factorial_ne_zero _), vz, hodd]
  simp

/-- **Lemma 1, odd case.** For `j = 2h + 1` (so `h = ⌊j/2⌋`, `β_j = R − h`) and `h ≤ R`, the
`m`-independent offset evaluates to the binomial valuation:
`h + v₂(R!) − v₂((2h+1)!) − v₂((R−h)!) = v₂(C(R, h))`.

This is `D₀(j) = v₂(C(R, h))` for `j` odd (§3, Lemma 1). The `h`'s cancel via
`v₂((2h+1)!) = v₂((2h)!) = h + v₂(h!)`, leaving the choose-factorisation. -/
theorem D0_odd (R h : ℕ) (hh : h ≤ R) :
    (h : ℤ) + vz R ! - vz (2 * h + 1)! - vz (R - h)! = vz (R.choose h) := by
  rw [vz_two_mul_succ_factorial, vz_two_mul_factorial]
  have hc := vz_choose hh
  linarith

/-- **Lemma 1, even case.** For `j = 2h` (so `h = ⌊j/2⌋`, `β_j = R + 1 − h`) and `1 ≤ h ≤ R + 1`,
the `m`-independent offset evaluates to:
`h + v₂(R!) − v₂((2h)!) − v₂((R+1−h)!) = v₂(C(R, h−1)) − v₂(h)`.

This is `D₀(j) = v₂(C(R, h−1)) − v₂(h)` for `j` even (§3, Lemma 1). The extra `− v₂(h)` term
comes from peeling one factor off `h! = h · (h−1)!`; it is what makes `D₀` possibly negative
(`≥ −v₂(h)`, used in §4–§5). The proof uses `vz_choose` at `h − 1` and `R − (h−1) = R + 1 − h`. -/
theorem D0_even (R h : ℕ) (hh1 : 1 ≤ h) (hh2 : h ≤ R + 1) :
    (h : ℤ) + vz R ! - vz (2 * h)! - vz (R + 1 - h)! = vz (R.choose (h - 1)) - vz h := by
  rw [vz_two_mul_factorial]
  -- choose-factorisation at `h - 1`, with `R - (h-1)` rewritten to `R + 1 - h`
  have hle : h - 1 ≤ R := by omega
  have hrh : R - (h - 1) = R + 1 - h := by omega
  have hc := vz_choose hle
  rw [hrh] at hc
  -- `h! = h · (h-1)!`, so `vz h! = vz h + vz (h-1)!`
  have hfs : vz h ! = vz h + vz (h - 1)! := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    rw [vz_factorial_succ]
    simp
  linarith

end TworowD4Kernel
