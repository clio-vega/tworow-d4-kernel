/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Order parity of a self-reciprocal polynomial

Formalisation of Q105 Lemma 3.3 (`lem:selfrec`) of
`proofs/2026-09-08-c2-Q105-two-plus-t.tex`:

> If `0 ≠ Π ∈ ℚ[t]` satisfies `Π(t) = tᴺ Π(1/t)`, then `mult_{t=-1} Π ≡ N (mod 2)`.

## Statement of the hypothesis

`Π(t) = tᴺ Π(1/t)` is not directly expressible in `R[X]` (it needs Laurent polynomials), so
it is rendered here as the pair

* `P.natDegree ≤ N`, and
* `P.reflect N = P`.

Under `P.natDegree ≤ N` the polynomial `P.reflect N = ∑_{i≤N} P.coeff (N-i) • Xⁱ` *is* `tᴺ P(1/t)`,
so the pair is exactly the paper's hypothesis. The degree bound is not decoration: it is forced
by the paper's identity (a genuine equality of Laurent polynomials makes `deg Π ≤ N`), and it is
load-bearing here. Without it the statement is **false** — take `N = 1`, `P = X ^ 2`, which
satisfies `reflect 1 P = P` since `coeff 0 = coeff 1 = 0`, yet has multiplicity `0` at `t = -1`
while `N` is odd. See `TworowD4KernelTests` for that counterexample as an executable check.

## The proof

The paper argues over `ℚ̄`, factoring `Π` into root pairs `{ρ, 1/ρ}` and separately showing that
the multiplicity at `t = +1` is even. That route wants an algebraic closure and root multisets.
The induction used here needs neither, and is a genuine simplification of the printed proof:

* `Polynomial.IsSelfReciprocal.eval_neg_one_eq_zero_of_odd` — if `N` is odd then `P(-1) = 0`,
  because `P(-1) = (-1)ᴺ P(-1) = -P(-1)`. One substitution, no factorisation.
* `Polynomial.IsSelfReciprocal.of_mul_X_add_one` — dividing out `(X + 1)` preserves
  self-reciprocality and drops `N` by one, by `reflect_mul` and cancelling the nonzerodivisor
  `X + 1`.
* `Polynomial.IsSelfReciprocal.rootMultiplicity_neg_one_emod_two` — induct on `N`.

In particular the paper's preliminary reduction to the case `Π(0) ≠ 0` (writing `Π = t^α Q`) is
**removable**: `of_mul_X_add_one` goes through verbatim when `P`'s constant term vanishes.

## Scope

This formalises Lemma 3.3 **only**. It does not formalise Lemma 3.2 (self-reciprocality of
`Π_{νλ}` itself) nor Theorem B(i) (the power-sum order computation); both need the ring of
symmetric functions and plethysm, which this repository does not have.
-/

namespace TworowD4Kernel

open Polynomial

variable {R : Type*} [CommRing R]

/-- `P` is self-reciprocal of degree bound `N`: the polynomial rendering of `P(t) = tᴺ P(1/t)`.

The `natDegree` bound is part of the definition; see the module docstring for why it cannot be
dropped. -/
structure IsSelfReciprocal (N : ℕ) (P : R[X]) : Prop where
  natDegree_le : P.natDegree ≤ N
  reflect_eq : P.reflect N = P

namespace IsSelfReciprocal

/-- **Step (a).** A self-reciprocal polynomial of odd `N` vanishes at `t = -1`.

`P(-1) = (-1)ᴺ P(-1) = -P(-1)`, so `2 P(-1) = 0`. This is the only step that uses `2 ≠ 0`. -/
theorem eval_neg_one_eq_zero_of_odd [NoZeroDivisors R] (h2 : (2 : R) ≠ 0)
    {N : ℕ} {P : R[X]} (h : IsSelfReciprocal N P) (hN : Odd N) :
    P.eval (-1) = 0 := by
  letI : Invertible (-1 : R) := ⟨-1, by ring, by ring⟩
  have hinv : (⅟(-1 : R)) = -1 := rfl
  have key := eval₂_reflect_mul_pow (RingHom.id R) (-1 : R) N P h.natDegree_le
  rw [h.reflect_eq] at key
  simp only [eval₂_id, hN.neg_one_pow, mul_neg_one, hinv] at key
  -- `key : -P(-1) = P(-1)`, so `2 P(-1) = 0`.
  have hsum : (2 : R) * P.eval (-1) = 0 := by
    rw [two_mul]
    calc P.eval (-1) + P.eval (-1) = -P.eval (-1) + P.eval (-1) := by rw [key]
      _ = 0 := by simp
  rcases mul_eq_zero.mp hsum with h' | h'
  · exact absurd h' h2
  · exact h'

/-- `reflect 1 (X + 1) = X + 1`: the palindrome `1 + t` is its own reversal. -/
theorem reflect_one_X_add_one :
    ((X + 1 : R[X])).reflect 1 = X + 1 := by
  rw [reflect_add, reflect_one]
  simpa using add_comm (1 : R[X]) X

/-- **Step (b).** Dividing out `(X + 1)` preserves self-reciprocality and drops `N` by one.

`(1 + t) Q(t) = P(t) = tᴺ P(1/t) = (1 + t) t^{N-1} Q(1/t)`, and `X + 1` is a nonzerodivisor. -/
theorem of_mul_X_add_one [NoZeroDivisors R] [Nontrivial R]
    {N : ℕ} {P Q : R[X]} (h : IsSelfReciprocal (N + 1) P) (hPQ : P = (X + 1) * Q) :
    IsSelfReciprocal N Q := by
  have hX1 : (X + 1 : R[X]) ≠ 0 := by
    simpa [sub_neg_eq_add] using (monic_X_sub_C (-1 : R)).ne_zero
  have hdeg : Q.natDegree ≤ N := by
    rcases eq_or_ne Q 0 with rfl | hQ
    · simp
    · have := h.natDegree_le
      rw [hPQ, show (X + 1 : R[X]) = X - C (-1) by rw [map_neg, map_one, sub_neg_eq_add],
        (monic_X_sub_C (-1 : R)).natDegree_mul' hQ, natDegree_X_sub_C] at this
      omega
  refine ⟨hdeg, ?_⟩
  have hone : (X + 1 : R[X]).natDegree ≤ 1 := by
    simpa [sub_neg_eq_add] using (natDegree_X_sub_C (-1 : R)).le
  have hmul : P.reflect (1 + N) = (X + 1) * Q.reflect N := by
    rw [hPQ, reflect_mul _ _ hone hdeg, reflect_one_X_add_one]
  rw [Nat.add_comm 1 N, h.reflect_eq, hPQ] at hmul
  exact (mul_right_injective₀ hX1 hmul).symm

/-- **Q105 Lemma 3.3.** If `P ≠ 0` is self-reciprocal of degree bound `N`, then the order of
vanishing of `P` at `t = -1` has the same parity as `N`.

Cited in `proofs/2026-09-08-c2-Q105-two-plus-t.tex` as `lem:selfrec`, where it is used by
Theorem B(ii) to pin the vertex-side order function to `(m + n) mod 2`. -/
theorem rootMultiplicity_neg_one_emod_two [NoZeroDivisors R] [Nontrivial R] (h2 : (2 : R) ≠ 0) :
    ∀ {N : ℕ} {P : R[X]}, P ≠ 0 → IsSelfReciprocal N P →
      P.rootMultiplicity (-1) % 2 = N % 2 := by
  intro N
  induction N with
  | zero =>
    intro P _ h
    obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨P.coeff 0, eq_C_of_natDegree_le_zero h.natDegree_le⟩
    rw [rootMultiplicity_C]
  | succ N ih =>
    intro P hP h
    by_cases hroot : P.IsRoot (-1)
    · obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr hroot
      rw [map_neg, map_one, sub_neg_eq_add] at hQ
      have hQ0 : Q ≠ 0 := by rintro rfl; exact hP (by simp [hQ])
      have hmul : P.rootMultiplicity (-1) = Q.rootMultiplicity (-1) + 1 := by
        rw [hQ, show (X + 1 : R[X]) = X - C (-1) by rw [map_neg, map_one, sub_neg_eq_add],
          mul_comm, ← pow_one (X - C (-1 : R)), rootMultiplicity_mul_X_sub_C_pow hQ0]
      have := ih hQ0 (h.of_mul_X_add_one hQ)
      omega
    · -- `P(-1) ≠ 0` forces the multiplicity to be `0`; step (a) then forces `N + 1` even.
      have hNeven : ¬ (N + 1) % 2 = 1 := fun hm =>
        hroot (h.eval_neg_one_eq_zero_of_odd h2 (Nat.odd_iff.mpr hm))
      rw [rootMultiplicity_eq_zero hroot]
      omega

end IsSelfReciprocal

/-! ## Non-vacuity and sharpness

The hypothesis of `rootMultiplicity_neg_one_emod_two` is satisfiable, and its `natDegree`
clause cannot be dropped. Both are asserted in the module docstring, so both are proved here.
-/

/-- Non-vacuity: `1 + t` is self-reciprocal with `N = 1`, and its order at `t = -1` is `1`. -/
theorem isSelfReciprocal_one_X_add_one : IsSelfReciprocal 1 (X + 1 : ℤ[X]) :=
  ⟨by simpa [sub_neg_eq_add] using (natDegree_X_sub_C (-1 : ℤ)).le,
    IsSelfReciprocal.reflect_one_X_add_one⟩

theorem rootMultiplicity_neg_one_X_add_one :
    ((X + 1 : ℤ[X])).rootMultiplicity (-1) = 1 := by
  rw [show (X + 1 : ℤ[X]) = X - C (-1) by rw [map_neg, map_one, sub_neg_eq_add]]
  exact rootMultiplicity_X_sub_C_self

/-- Sharpness: `t²` satisfies `reflect 1 P = P` — its coefficients in degrees `0` and `1` both
vanish — but has `natDegree 2 > 1`. Its order at `t = -1` is `0`, of the wrong parity for
`N = 1`. So the `natDegree_le` field of `IsSelfReciprocal` is load-bearing, not decoration. -/
theorem reflect_one_X_sq : ((X : ℤ[X]) ^ 2).reflect 1 = X ^ 2 := by
  rw [reflect_monomial, revAt_eq_self_of_lt (by norm_num)]

theorem rootMultiplicity_neg_one_X_sq : ((X : ℤ[X]) ^ 2).rootMultiplicity (-1) = 0 :=
  rootMultiplicity_eq_zero (by norm_num [IsRoot])

/-- **Q105 Lemma 3.3 over `ℚ`** — the paper's statement verbatim.

`proofs/2026-09-08-c2-Q105-two-plus-t.tex`, `lem:selfrec`. -/
theorem rootMultiplicity_neg_one_emod_two_rat {N : ℕ} {P : ℚ[X]} (hP : P ≠ 0)
    (h : IsSelfReciprocal N P) : P.rootMultiplicity (-1) % 2 = N % 2 :=
  IsSelfReciprocal.rootMultiplicity_neg_one_emod_two (by norm_num) hP h

/-- The same over `ℤ`, which is the form the application wants: the coefficients of `Π_{νλ}`
are Littlewood–Richardson-type non-negative integers. -/
theorem rootMultiplicity_neg_one_emod_two_int {N : ℕ} {P : ℤ[X]} (hP : P ≠ 0)
    (h : IsSelfReciprocal N P) : P.rootMultiplicity (-1) % 2 = N % 2 :=
  IsSelfReciprocal.rootMultiplicity_neg_one_emod_two (by norm_num) hP h

/-- The parity conclusion genuinely fails for `X ^ 2` at `N = 1`. -/
theorem not_rootMultiplicity_emod_two_of_natDegree_gt :
    ((X : ℤ[X]) ^ 2).rootMultiplicity (-1) % 2 ≠ 1 % 2 := by
  rw [rootMultiplicity_neg_one_X_sq]
  norm_num

end TworowD4Kernel
