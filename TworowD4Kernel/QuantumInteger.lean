/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# The quantum integer and the coefficient identity behind C4

This file is **not** part of the two-row `d = 4` kernel development; it shares the project only
because that project is the available Mathlib harness. It formalises the single algebraic
identity that carries the whole proof of Conjecture C4 of the ribbon-sign programme,

> `P_e = B_{-1}^{[e]} + (q - q⁻¹) · C_e^{(1)}`  on level-1 Uglov Fock space,

whose informal proof is `~/projects/proofs/2026-08-14-C4-iijima-B1.tex` (Theorem 3.1, eq. (3.4)).
That proof is a coefficient-by-coefficient comparison on the standard basis `{|λ⟩}`: for an
`e`-ribbon of height `h`, the coefficient of `|μ⟩` in `P_e|λ⟩` is `(-q)^h`, the coefficient in
`B_{-1}^{[e]}|λ⟩` is `(-q⁻¹)^h`, and the entire mathematical content of the theorem is the
displayed line

> `(-q)^h - (-q⁻¹)^h = (-1)^h (q^h - q^{-h}) = (-1)^h (q - q⁻¹) [h]_q`.

**Only that line is formalised here.** Ribbons, partitions, abaci and the crystal operators are
deliberately out of scope: they are months of work, and none of the risk in C4 lives there.

## Setting

We work over an arbitrary commutative ring `R` with `q : Rˣ` a *unit*, so negative powers are
`zpow` in `Rˣ` and no Laurent-polynomial machinery is needed. The intended instance is
`R = ℤ[q, q⁻¹]` with `q` the standard unit, which is exactly the coefficient ring of `𝓕_e`.
`qpow q n` denotes `q ^ n` for `n : ℤ`, pushed into `R`.

## Main results

* `Clio.QuantumInteger.qpow_sub_qpow_inv` — the only real content:
  `q^n - q^{-n} = (q - q⁻¹) · [n]_q`.
* `Clio.QuantumInteger.C4_coefficient_identity` — the displayed line of the C4 proof:
  `(-q)^n - (-q⁻¹)^n = (-1)^n · ((q - q⁻¹) · [n]_q)`.
* `Clio.QuantumInteger.qInt_one` and `Clio.QuantumInteger.qInt_inv` — the two sanity checks that
  pin the definition of `[n]_q` against a misreading: it specialises to `n` at `q = 1`, and it is
  bar-invariant (`q ↦ q⁻¹` fixes it).

## References

* The informal proof: `~/projects/proofs/2026-08-14-C4-iijima-B1.tex`, §3.
* The Heisenberg mode `B_{-1}^{[e]}` at level 1 is Uglov's; the level-`ℓ` formula used to identify
  it is Iijima, *An algebraic construction of the ... Fock space* (arXiv:1207.6161), eq. (9).
* The `q`-specialised corollary of the transpose twist is Leclerc–Thibon, ASPM 28 (2000),
  Prop. 7.10 at `k = 1` (not used here; recorded for provenance).
-/

namespace Clio.QuantumInteger

variable {R : Type*} [CommRing R]

/-- `qpow q n` is the integer power `q ^ n` of the unit `q`, viewed in `R`.

Using `Rˣ` rather than a field lets `q⁻¹` exist without inverting anything else in `R`, which is
what the coefficient ring `ℤ[q, q⁻¹]` of Uglov Fock space actually provides. -/
def qpow (q : Rˣ) (n : ℤ) : R := ((q ^ n : Rˣ) : R)

/-- The quantum integer `[n]_q = q^{n-1} + q^{n-3} + ⋯ + q^{-(n-1)}`, as a `Finset.range n` sum
with `ℤ`-exponents `n - 1 - 2k`.

This is the convention of `2026-08-14-C4-iijima-B1.tex`, §3: `[0]_q = 0`, `[1]_q = 1`,
`[2]_q = q + q⁻¹`. -/
def qInt (q : Rˣ) (n : ℕ) : R := ∑ k ∈ Finset.range n, qpow q ((n : ℤ) - 1 - 2 * k)

@[simp]
theorem qpow_zero (q : Rˣ) : qpow q 0 = 1 := by simp [qpow]

theorem qpow_add (q : Rˣ) (a b : ℤ) : qpow q a * qpow q b = qpow q (a + b) := by
  simp only [qpow, ← Units.val_mul, zpow_add]

theorem qpow_natPow (q : Rˣ) (a : ℤ) (n : ℕ) : qpow q a ^ n = qpow q (a * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, qpow_add]
    congr 1
    push_cast
    ring

theorem qpow_inv (q : Rˣ) (a : ℤ) : qpow q⁻¹ a = qpow q (-a) := by
  simp only [qpow, inv_zpow, ← zpow_neg]

@[simp]
theorem qInt_zero (q : Rˣ) : qInt q 0 = (0 : R) := by simp [qInt]

@[simp]
theorem qInt_one_index (q : Rˣ) : qInt q 1 = (1 : R) := by
  rw [qInt]
  norm_num

/-- **The only real content of the C4 proof.**

`q^n - q^{-n} = (q - q⁻¹) · [n]_q`.

The proof is the telescope `(q - q⁻¹) · q^{n-1-2k} = q^{n-2k} - q^{n-2(k+1)}`, summed over
`k ∈ Finset.range n`. -/
theorem qpow_sub_qpow_inv (q : Rˣ) (n : ℕ) :
    qpow q (n : ℤ) - qpow q (-(n : ℤ)) = (qpow q 1 - qpow q (-1)) * qInt q n := by
  set f : ℕ → R := fun k => qpow q ((n : ℤ) - 2 * k) with hf
  have h0 : f 0 = qpow q (n : ℤ) := by simp [hf]
  have hn : f n = qpow q (-(n : ℤ)) := by
    simp only [hf]
    congr 1
    ring
  have key : ∀ k ∈ Finset.range n,
      (qpow q 1 - qpow q (-1)) * qpow q ((n : ℤ) - 1 - 2 * k) = f k - f (k + 1) := by
    intro k _
    have e1 : (1 : ℤ) + ((n : ℤ) - 1 - 2 * k) = (n : ℤ) - 2 * k := by ring
    have e2 : (-1 : ℤ) + ((n : ℤ) - 1 - 2 * k) = (n : ℤ) - 2 * ((k + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    simp only [hf]
    rw [sub_mul, qpow_add, qpow_add, e1, e2]
  rw [qInt, Finset.mul_sum, Finset.sum_congr rfl key, Finset.sum_range_sub' f n, h0, hn]

/-- **The displayed line of `2026-08-14-C4-iijima-B1.tex`, §3** (the proof of Theorem 3.1):

`(-q)^n - (-q⁻¹)^n = (-1)^n · ((q - q⁻¹) · [n]_q)`.

For `n = h` the height of an `e`-ribbon, the left side is the difference of the `|μ⟩`-coefficients
of `P_e|λ⟩` and `B_{-1}^{[e]}|λ⟩`, and the right side is `(q - q⁻¹)` times the `|μ⟩`-coefficient of
`C_e^{(1)}|λ⟩`. Extending `ℤ[q, q⁻¹]`-linearly over the standard basis gives
`P_e = B_{-1}^{[e]} + (q - q⁻¹) C_e^{(1)}`; that extension step is *not* formalised here. -/
theorem C4_coefficient_identity (q : Rˣ) (n : ℕ) :
    (-qpow q 1) ^ n - (-qpow q (-1)) ^ n
      = (-1) ^ n * ((qpow q 1 - qpow q (-1)) * qInt q n) := by
  rw [neg_pow (qpow q 1) n, neg_pow (qpow q (-1)) n, qpow_natPow, qpow_natPow, one_mul,
    neg_one_mul, ← mul_sub, qpow_sub_qpow_inv]

/-! ### Sanity checks on the definition of `[n]_q`

Both pin `qInt` against a misreading of the exponent convention: the classical specialisation and
bar-invariance. -/

/-- `[n]_q` specialises to `n` at `q = 1`. -/
@[simp]
theorem qInt_one (n : ℕ) : qInt (1 : Rˣ) n = (n : R) := by
  simp [qInt, qpow]

/-- `[n]_q` is bar-invariant: the involution `q ↦ q⁻¹` fixes it. -/
theorem qInt_inv (q : Rˣ) (n : ℕ) : qInt q⁻¹ n = qInt q n := by
  rw [qInt, qInt, ← Finset.sum_range_reflect (fun k : ℕ => qpow q ((n : ℤ) - 1 - 2 * k)) n]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [qpow_inv]
  congr 1
  have hc : ((n - 1 - k : ℕ) : ℤ) = (n : ℤ) - 1 - (k : ℤ) := by omega
  rw [hc]
  ring

end Clio.QuantumInteger
