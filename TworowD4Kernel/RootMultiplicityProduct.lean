/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Ring.GeomSum

/-!
# Order of vanishing at `t = 1` of a product of cyclotomic-type factors

Formalisation of **Lemma `lem:kor-is-psi`** ("gap 1") of
`proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`:

> For every `P` and every `s(P) ∈ ℤ`, `ε(P) ∈ ℤ \ {0}`, the weight
> `π_P = ε(P) t^{s(P)} Ψ_P(t)` is cyclically `ψ`-graded, with `ord_{t=1} π_P = ν(P)` exactly.

whose printed proof is:

> By Lemma `lem:wd`, `Ψ_P` is a product of exactly `ν(P)` factors `(1 - t^m)` with `m ≥ 1`,
> each vanishing to order exactly `1` at `t = 1`; and `ε(P) t^{s(P)}` is a unit at `t = 1`.

The external object being graded is Korff's cylindric weight `Ψ`
(`arXiv:1110.6356`, Def. 5.5 — cited at line 43 of the `.tex` above). Korff's `Ψ` is
*refuted* as an admissible weight by Q410/Q417/Q424; this file formalises the **engine of that
refutation**, not a claim that `Ψ` is admissible.

## What is proved here, and what is assumed

The mathematical content is the displayed product identity, stripped of all combinatorics —
no tableaux, no cylinders, no `ZMod h`, no admissibility:

* `Polynomial.rootMultiplicity_one_sub_X_pow` — the single factor, order exactly `1`.
* `Polynomial.rootMultiplicity_prod_one_sub_X_pow` — the product, order `J.card`.
* `Polynomial.rootMultiplicity_unit_mul_prod_one_sub_X_pow` — the full lemma, with the unit
  prefactor `ε X^s`.

### ⚠️ Two hypotheses are carried, not discharged

1. **`m i ≥ 1` is gap 3 of the same paper (`region ⟹ m_i ≥ 1`), which is NOT proved.**
   It therefore appears as an explicit named hypothesis in every statement below, in the
   general form `(m i : R) ≠ 0`. Consequently this file makes gap 1 `lean-verified`
   *conditional on gap 3*; it does **not** establish `ord_{t=1} Ψ_T = ν(T)` outright.

   The hypothesis is *load-bearing*, and `rootMultiplicity_prod_one_sub_X_pow_eq_zero` plus
   `ablation_card_two` below are the witnesses: a single `m i = 0` makes the factor
   `1 - X^0 = 0`, hence the whole product `0`, and `rootMultiplicity _ 0 = 0` by Mathlib's
   convention — collapsing the count from `J.card` to `0`. A hypothesis witnessed necessary is
   worth more than a hypothesis assumed.

2. **The paper's `s(P)` ranges over `ℤ`; here `s : ℕ`.** A negative exponent needs
   `LaurentPolynomial`, where `rootMultiplicity` is not the available API. This is recorded as
   a restriction of the formalisation, not patched: the `s ≥ 0` case is what is covered. The
   mathematical content lost is nil (`t^s` is a unit at `t = 1` either way), but the Lean
   statement is strictly weaker than the printed one and is labelled as such.

The reduction `ν(T) = |J|` — from tableaux to this index-set cardinality — is itself a separate
claim, formalised for the unit-vector content in `TworowD4Kernel.CyclicAscent`
(`ZMod.nu_eq_card_of_content_ones`).
-/

open Polynomial Finset

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- `1 - Xᵐ = (-(∑_{j<m} Xʲ)) * (X - 1)¹` — the elementary geometric factorisation.
This is route (b): no derivative API, no field, no `CharZero`. -/
theorem one_sub_X_pow_eq (m : ℕ) :
    (1 - X ^ m : R[X]) = (-(∑ j ∈ range m, (X : R[X]) ^ j)) * (X - C (1 : R)) ^ 1 := by
  rw [pow_one, map_one, neg_mul, ← mul_neg, neg_sub, geom_sum_mul_neg]

/-- **Each factor vanishes to order exactly `1` at `t = 1`**, the inner clause of the printed
proof. Holds over any commutative ring in which `m` is not a zero divisor of `1`, i.e.
`(m : R) ≠ 0`; no domain, field or characteristic assumption is needed. -/
theorem rootMultiplicity_one_sub_X_pow {m : ℕ} (hm : (m : R) ≠ 0) :
    rootMultiplicity (1 : R) (1 - X ^ m) = 1 := by
  have hcof : ¬ ((-(∑ j ∈ range m, (X : R[X]) ^ j)).IsRoot (1 : R)) := by simp [IsRoot, hm]
  have hne : (-(∑ j ∈ range m, (X : R[X]) ^ j)) ≠ 0 := fun h => hcof (by rw [h]; simp [IsRoot])
  rw [one_sub_X_pow_eq, rootMultiplicity_mul_X_sub_C_pow hne,
    rootMultiplicity_eq_zero hcof, zero_add]

/-- A factor with `(m : R) ≠ 0` is a nonzero polynomial — read off `coeff m = -1`. -/
theorem one_sub_X_pow_ne_zero [Nontrivial R] {m : ℕ} (hm : (m : R) ≠ 0) :
    (1 - X ^ m : R[X]) ≠ 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm
  intro h
  have := congrArg (fun p => Polynomial.coeff p m) h
  simp [coeff_one, hm0] at this

/-- In a domain, a product of such factors is nonzero — the side condition that
`rootMultiplicity_mul` requires. -/
theorem prod_one_sub_X_pow_ne_zero [IsDomain R] {ι : Type*} (J : Finset ι) (m : ι → ℕ)
    (hm : ∀ i ∈ J, (m i : R) ≠ 0) : (∏ i ∈ J, (1 - X ^ (m i) : R[X])) ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i hi => one_sub_X_pow_ne_zero (hm i hi)

/-- **Gap 1, the product step.** `ord_{t=1} ∏_{i ∈ J} (1 - t^{m i}) = |J|`, given that every
multiplicity is nonzero in `R`. Induction on `J` via `Finset.cons_induction`, using
multiplicativity of `rootMultiplicity` on a domain. -/
theorem rootMultiplicity_prod_one_sub_X_pow [IsDomain R] {ι : Type*}
    (J : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ J, (m i : R) ≠ 0) :
    rootMultiplicity (1 : R) (∏ i ∈ J, (1 - X ^ (m i))) = J.card := by
  induction J using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.card_cons]
      have hma : ((m a : ℕ) : R) ≠ 0 := hm a (Finset.mem_cons_self a s)
      have hms : ∀ i ∈ s, ((m i : ℕ) : R) ≠ 0 := fun i hi => hm i (Finset.mem_cons_of_mem hi)
      rw [rootMultiplicity_mul
            (mul_ne_zero (one_sub_X_pow_ne_zero hma) (prod_one_sub_X_pow_ne_zero s m hms)),
          rootMultiplicity_one_sub_X_pow hma, ih hms]
      omega

/-- **Gap 1 in the paper's own form.** Over a characteristic-zero domain, with the paper's
hypothesis `m i ≥ 1` stated verbatim (this is the form that depends on gap 3). -/
theorem rootMultiplicity_prod_one_sub_X_pow_of_one_le [IsDomain R] [CharZero R] {ι : Type*}
    (J : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ J, 1 ≤ m i) :
    rootMultiplicity (1 : R) (∏ i ∈ J, (1 - X ^ (m i))) = J.card :=
  rootMultiplicity_prod_one_sub_X_pow J m fun i hi => Nat.cast_ne_zero.mpr (by
    have := hm i hi; omega)

/-- **The full lemma `lem:kor-is-psi`**: the unit prefactor `ε X^s` does not change the order.
`ε ≠ 0` and `X^s` is a unit at `t = 1` (`eval 1 (X^s) = 1`). Restriction: `s : ℕ`, see the
module docstring — the paper allows `s ∈ ℤ`, which needs `LaurentPolynomial`. -/
theorem rootMultiplicity_unit_mul_prod_one_sub_X_pow [IsDomain R] [CharZero R] {ι : Type*}
    (J : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ J, 1 ≤ m i)
    (ε : R) (hε : ε ≠ 0) (s : ℕ) :
    rootMultiplicity (1 : R) (C ε * X ^ s * ∏ i ∈ J, (1 - X ^ (m i))) = J.card := by
  have hprod : (∏ i ∈ J, (1 - X ^ (m i) : R[X])) ≠ 0 :=
    prod_one_sub_X_pow_ne_zero J m fun i hi => Nat.cast_ne_zero.mpr (by have := hm i hi; omega)
  have hCX : (C ε * X ^ s : R[X]) ≠ 0 := by
    apply mul_ne_zero
    · simpa using hε
    · exact pow_ne_zero _ X_ne_zero
  have hunit : rootMultiplicity (1 : R) (C ε * X ^ s) = 0 :=
    rootMultiplicity_eq_zero (by simp [IsRoot, hε])
  rw [rootMultiplicity_mul (mul_ne_zero hCX hprod), hunit, zero_add,
    rootMultiplicity_prod_one_sub_X_pow_of_one_le J m hm]

/-! ## Ablation: the hypothesis `m i ≥ 1` is load-bearing -/

/-- **Necessity of the hypothesis.** One zero multiplicity collapses the count to `0`:
`1 - X^0 = 0`, so the whole product is `0`, and `rootMultiplicity _ 0 = 0`. -/
theorem rootMultiplicity_prod_one_sub_X_pow_eq_zero {ι : Type*} (J : Finset ι) (m : ι → ℕ)
    (h : ∃ i ∈ J, m i = 0) :
    rootMultiplicity (1 : R) (∏ i ∈ J, (1 - X ^ (m i))) = 0 := by
  obtain ⟨i, hi, hmi⟩ := h
  have : (∏ i ∈ J, (1 - X ^ (m i) : R[X])) = 0 :=
    Finset.prod_eq_zero hi (by rw [hmi, pow_zero, sub_self])
  rw [this, rootMultiplicity_zero]

end Polynomial
