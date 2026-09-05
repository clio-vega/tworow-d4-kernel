/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat

/-!
# The `r = 1` signed count

Formalises the `r = 1` signed count of `proofs/2026-09-04-Q81-nested-bracket.tex`, the
displayed computation inside the proof of `thm:wit` (lines 511--515):

> For general `k` the `r = 1` count is the same computation: with `ρ(1) = m < k`, unimodality
> forces the indices before the peak to be `m` together with an arbitrary subset
> `T ⊆ {m+1, …, k-1}` in increasing order, the rest following in decreasing order, so the
> signed count is `∑_T (-1)^(|T|+1) = -(1-1)^(k-1-m)`, which is `0` for `m ≤ k-2` and `-1`
> for `m = k-1`; and for `m = k` the unique admissible chain `ρ = (k, k-1, …, 1)` gives `+1`.

This is a finite-combinatorics fragment: no ribbons, no `t`, no Maya diagram. The
combinatorial content is Mathlib's `Finset.sum_powerset_neg_one_pow_card_of_nonempty`, so
the proofs below are short. **The value here is not difficulty**; it is that the paper's
prose elides two boundaries, and Lean forces both into the open.

## The two boundaries the paper's prose elides

1. **`m ≤ k-2` is `0` because the index set is nonempty.** At `m = k-1` the set
   `{m+1, …, k-1}` is *empty*, the sum is the single term `T = ∅`, and the value is `-1`.
   The closed form `-(1-1)^(k-1-m)` reproduces both branches *only under the convention
   `0^0 = 1`*. Lean makes you say which convention you mean: `signedSubsetCount_eq_neg_zero_pow`
   is true precisely because `Monoid.npow` gives `(0 : ℤ) ^ 0 = 1`.

2. **`m = k` is not an instance of the sum.** The paper's hypothesis `ρ(1) = m < k` is
   load-bearing: `signedSubsetCount_self` shows the sum model evaluated at `m = k` returns
   `-1`, whereas the paper's value there is `+1`. The `m = k` case rests on a different
   argument — the unique admissible chain — and must not be folded in.

## What this does NOT do

It does not close the `k ≥ 4` gap. This is one of three pieces; the `r = 2` count and the
vanishing of the `r ≥ 3` counts remain open.
-/

namespace TworowD4Kernel

open Finset

/-- The `r = 1` signed count at peak `k` with `ρ(1) = m`, as a sum over the subsets
`T ⊆ {m+1, …, k-1}` that may precede the peak. The exponent is `|T| + 1`: the indices before
the peak are `T` *together with* `m`, and the sign is `(-1)` to the number of them.

This models the paper's count only for `m < k`; see `signedSubsetCount_self`. -/
def signedSubsetCount (k m : ℕ) : ℤ :=
  ∑ T ∈ (Finset.Ico (m + 1) k).powerset, (-1 : ℤ) ^ (T.card + 1)

/-- Pulling the `+1` in the exponent out as an overall sign. -/
lemma signedSubsetCount_eq_neg_sum (k m : ℕ) :
    signedSubsetCount k m = -∑ T ∈ (Finset.Ico (m + 1) k).powerset, (-1 : ℤ) ^ T.card := by
  simp only [signedSubsetCount, pow_succ, ← Finset.sum_mul]
  ring

/-- **`m ≤ k-2`: the count vanishes.** The reason is that the index set `{m+1, …, k-1}` is
*nonempty*, so the alternating sum over its powerset cancels. -/
theorem signedSubsetCount_eq_zero {k m : ℕ} (h : m + 2 ≤ k) : signedSubsetCount k m = 0 := by
  rw [signedSubsetCount_eq_neg_sum,
    Finset.sum_powerset_neg_one_pow_card_of_nonempty (Finset.nonempty_Ico.mpr (by omega)),
    neg_zero]

/-- **`m = k-1`: the count is `-1`.** Here `{m+1, …, k-1}` is *empty*; the sum is the single
term `T = ∅`, contributing `(-1)^(0+1)`. Stated in `succ` form to avoid truncated subtraction. -/
theorem signedSubsetCount_of_succ (k : ℕ) : signedSubsetCount (k + 1) k = -1 := by
  simp [signedSubsetCount]

/-- The same statement in the paper's `k - 1` notation, under `1 ≤ k`. -/
theorem signedSubsetCount_pred {k : ℕ} (hk : 1 ≤ k) : signedSubsetCount k (k - 1) = -1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simpa using signedSubsetCount_of_succ j

/-- **The closed form, with the convention made explicit.** `-(1-1)^(k-1-m)` in the paper is
`-(0 : ℤ)^(k-1-m)` here, and it reproduces *both* branches only because Lean's `0 ^ 0 = 1`.
At `m = k-1` the exponent `k-1-m` is `0` and this is the `-1` branch; for `m ≤ k-2` the
exponent is positive and this is the `0` branch. -/
theorem signedSubsetCount_eq_neg_zero_pow {k m : ℕ} (h : m < k) :
    signedSubsetCount k m = -(0 : ℤ) ^ (k - 1 - m) := by
  rcases Nat.lt_or_ge (m + 1) k with hlt | hge
  · rw [signedSubsetCount_eq_zero (by omega), zero_pow (by omega), neg_zero]
  · obtain rfl : k = m + 1 := by omega
    rw [signedSubsetCount_of_succ]
    norm_num

/-- **The `m = k` boundary: the sum model does not extend.** Evaluated at `m = k` the sum
returns `-1`, but the paper's `r = 1` count at `m = k` is `+1`, coming from the unique
admissible chain `ρ = (k, k-1, …, 1)`. So the hypothesis `m < k` in
`signedSubsetCount_eq_neg_zero_pow` is load-bearing and the `m = k` case is a genuinely
separate argument, not a specialisation. -/
theorem signedSubsetCount_self (k : ℕ) : signedSubsetCount k k = -1 := by
  simp [signedSubsetCount]

end TworowD4Kernel
