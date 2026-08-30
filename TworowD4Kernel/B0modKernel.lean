/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-!
# Arithmetic kernel of the two-row `d = 4` law for `b ≡ 0 (mod 4)`

This file formalises the two self-contained arithmetic primitives that are load-bearing in the
2-adic proof of the two-row `d = 4` fiber-vanishing law for the family `b ≡ 0 (mod 4)`
(`~/projects/proofs/2026-06-08-tworow-d4-b0mod4-proved.md`). As with the companion file for the
`b ≡ 1 (mod 4)` class, the full theorem rests on generating-function machinery not present in
Mathlib; these primitives are the parts of the argument a skeptic would most want machine-checked.

## Main results

* `TworowD4Kernel.padicValNat_two_choose_eq` (§3, "the `h consecutive integers ÷ h!` engine"):
  the valuation identity
  `v₂(C(R, h)) = v₂((R)_h) − v₂(h!)`
  underlying every closed form `D₀(j)` in §3 of the proof. Here `(R)_h = Nat.descFactorial R h`
  is the falling factorial; the identity is the `padicValNat` shadow of
  `(R)_h = h! · C(R, h)`.

* `TworowD4Kernel.odd_add_three` and `TworowD4Kernel.odd_sum_of_odd_card`
  (§6, "three odds sum to an odd"): the parity-counting primitive that rescues the law when
  domination fails. The first is the bare three-term instance actually invoked (`m` odd: the ties
  are `{1, 2, 3}`); the second packages the general statement "a sum over an odd-cardinality index
  set of odd values is odd".

## References

The informal proof is `2026-06-08-tworow-d4-b0mod4-proved.md`; §3 (the descFactorial/choose
valuation engine, Lemma 1) and §6 (the parity count) are referenced inline.
-/

namespace TworowD4Kernel

open Nat Finset

/-- **§3 — the `h consecutive integers ÷ h!` engine.**

For `h ≤ R`, the 2-adic valuation of the binomial coefficient `C(R, h)` is the valuation of the
falling factorial `(R)_h = R(R-1)⋯(R-h+1)` (here `Nat.descFactorial R h`) minus the valuation of
`h!`:
`v₂(C(R, h)) = v₂((R)_h) − v₂(h!)`.

This is the valuation form of the integer identity `(R)_h = h! · C(R, h)` and is the kernel fact
behind every closed form `D₀(j)` in §3 (Lemma 1) of the `b ≡ 0 (mod 4)` proof: a product of `h`
consecutive integers is divisible by `h!`, and the quotient is the binomial coefficient whose
valuation drives the tie analysis. The hypothesis `h ≤ R` is exactly what makes `C(R, h)` nonzero
(needed for multiplicativity of `padicValNat`). -/
theorem padicValNat_two_choose_eq (R h : ℕ) (hh : h ≤ R) :
    padicValNat 2 (Nat.choose R h) =
      padicValNat 2 (Nat.descFactorial R h) - padicValNat 2 (Nat.factorial h) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hch : Nat.choose R h ≠ 0 := (Nat.choose_pos hh).ne'
  have hfac : Nat.factorial h ≠ 0 := Nat.factorial_ne_zero h
  rw [Nat.descFactorial_eq_factorial_mul_choose, padicValNat.mul hfac hch,
    Nat.add_sub_cancel_left]

/-- **§6 — three odds sum to an odd (the bare instance).**

`Odd a → Odd b → Odd c → Odd (a + b + c)`. This is the exact parity step invoked in §6 for `m` odd,
where the valuation-minimal terms are precisely `j ∈ {1, 2, 3}` and each contributes an odd
reduced term `τ_j / 2^a`, so their sum keeps an odd leading 2-adic digit and `v₂(I_b(m)) = a`. -/
theorem odd_add_three {a b c : ℕ} (ha : Odd a) (hb : Odd b) (hc : Odd c) :
    Odd (a + b + c) :=
  (ha.add_odd hb).add_odd hc

/-- **§6 — odd count of odds sums to an odd (general form).**

If every value `f i` over a finite index set `s` is odd and the cardinality `s.card` is odd, then
the sum `∑ i ∈ s, f i` is odd. This packages "the number of valuation-minimal terms is odd (1 for
`m` even, 3 for `m` odd), so their reduced sum is odd", the parity count that rescues the law in §6
when strict domination fails. -/
theorem odd_sum_of_odd_card {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, Odd (f i)) (hcard : Odd s.card) :
    Odd (∑ i ∈ s, f i) := by
  -- Work mod 2: each `f i ≡ 1`, so the sum `≡ s.card ≡ 1`.
  rw [Nat.odd_iff] at hcard ⊢
  rw [Finset.sum_nat_mod]
  have hsum : (∑ i ∈ s, f i % 2) = ∑ _i ∈ s, 1 := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Nat.odd_iff.mp (hf i hi)]
  rw [hsum, Finset.sum_const, smul_eq_mul, mul_one]
  exact hcard

end TworowD4Kernel
