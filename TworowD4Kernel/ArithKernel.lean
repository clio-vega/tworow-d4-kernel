/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Arithmetic kernel of the two-row `d = 4` law for `b ≡ 1 (mod 4)`

This file holds the two self-contained arithmetic lemmas that are load-bearing in the
2-adic proof of the two-row `d = 4` fiber-vanishing law for the infinite family `b ≡ 1 (mod 4)`
(`~/projects/proofs/2026-06-07-tworow-d4-b1mod4-proved.md`). The full theorem rests on
generating-function machinery not present in Mathlib; these two lemmas are the part of the
argument a skeptic would most want machine-checked, namely the valuation bookkeeping.

## Main results

* `TworowD4Kernel.descFactorial_eq_factorial_mul_self_mul_choose_pred` (§2.1, "the `j = 1` term
  is exact"): the integer identity
  `(m)_{R+1} = R! · (m · C(m-1, R))`
  that makes `τ₁(m) = (m)_{R+1} / R!` an honest integer and pins its 2-adic valuation.

* `TworowD4Kernel.padicValNat_two_factorial_two_mul` (§2.3, "the 2-adic doubling identity"): the
  load-bearing valuation step
  `v₂((2h)!) = h + v₂(h!)`,
  here obtained directly from Mathlib's Legendre-theorem corollary `padicValNat_factorial_mul`.

## Implementation note

These two theorems previously lived in the root module `TworowD4Kernel`. They were moved to
this leaf (Mathlib-only imports) because `TworowD4Kernel.D0ClosedForms` needs the doubling
identity, while the root aggregator imports — transitively — `D0ClosedForms` itself:

```
TworowD4Kernel → SubsetIdentityGeneralC → NumberLemmaC2 → D0ClosedForms → TworowD4Kernel
```

That cycle broke `lake build` outright. The root now re-exports this file, so the fully
qualified names `TworowD4Kernel.descFactorial_eq_factorial_mul_self_mul_choose_pred` and
`TworowD4Kernel.padicValNat_two_factorial_two_mul` are unchanged for any downstream user.

## References

The informal proof is `2026-06-07-tworow-d4-b1mod4-proved.md`; the relevant sections are
referenced inline (§2.1 and §2.3).
-/

namespace TworowD4Kernel

open Nat

/-- **§2.1 — the falling-factorial / binomial bridge ("the `j = 1` term is exact").**

For integers `m ≥ R + 1 ≥ 1` the falling factorial `(m)_{R+1} = m(m-1)⋯(m-R)` (here
`Nat.descFactorial m (R + 1)`) factors as `R! · (m · C(m-1, R))`. This is the identity that
makes `τ₁(m) = (m)_{R+1} / R!` an honest integer in §2.1 of the proof and pins its valuation
`v₂(τ₁(m)) = v₂((m)_{R+1}) - v₂(R!)`. -/
theorem descFactorial_eq_factorial_mul_self_mul_choose_pred (m R : ℕ) (h : R + 1 ≤ m) :
    Nat.descFactorial m (R + 1) = R ! * (m * Nat.choose (m - 1) R) := by
  -- Since `R + 1 ≤ m`, `m` is a successor; write `m = k + 1` so that `m - 1 = k`.
  obtain _ | k := m
  · exact absurd h (by omega)
  · simp only [Nat.add_sub_cancel]
    -- `(m)_{R+1} = (R+1)! · C(m, R+1)` and `(R+1)! = (R+1) · R!`;
    -- `(k+1) · C(k, R) = C(k+1, R+1) · (R+1)` is `Nat.add_one_mul_choose_eq`.
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.factorial_succ,
      Nat.add_one_mul_choose_eq]
    ring

/-- **§2.3 — the 2-adic doubling identity.**

`v₂((2h)!) = h + v₂(h!)` for every `h`. This is the load-bearing valuation step used to evaluate
the closed form for `D_j` in §2.3. It is the `p = 2` instance of Legendre's theorem in the form
`padicValNat p (p * n)! = padicValNat p n! + n` (`Nat.padicValNat_factorial_mul`). -/
theorem padicValNat_two_factorial_two_mul (h : ℕ) :
    padicValNat 2 (2 * h)! = h + padicValNat 2 h ! := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_factorial_mul, Nat.add_comm]

end TworowD4Kernel
