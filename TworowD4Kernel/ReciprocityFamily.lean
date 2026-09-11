/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import TworowD4Kernel.ReciprocityCertificate

/-!
# The `μ = (n)` inconsistency family, uniformly in `n ≥ 4`

`TworowD4Kernel.ReciprocityCertificate` certifies a single cell — `n = 4`, `μ = (4)` — of the
inconsistency of the Khanna–Loehr local identity, by exhibiting a left null vector of a
transcribed `5 × 4` matrix. This file proves the same obstruction **uniformly in `n`**, for the
one-row partition `μ = (n)` and every `n ≥ 4`, and it does so without the certificate vector:
the argument runs on the *equation system* and is four lines of ring arithmetic.

## Source

`~/projects/proofs/2026-09-10-c2-Q140-local-identity-certificate-family.tex`, Lemma `lem:rows`
and Theorem `thm:mainrow` (registry node `Q140-certificate-family-mu-equals-n`, `proved`).
The reciprocity being tested for deformation is the Adin–Bauer / Khanna–Loehr inversion
reciprocity, arXiv:2505.10783, §2.

## Scope — what is and is not formalised

Read the registry before reading the theorems.

* **Formalised here:** the inconsistency of the *divided* local system for `μ = (n)`, all
  `n ≥ 4`, over an arbitrary `CommRing`; its consistency at `t = -1`; and a bridge to the
  `n = 4` matrix of `ReciprocityCertificate`.
* **Not formalised, and not claimed:** Lemma `lem:rows` itself. That the rows of `M^{(μ)}` for
  `μ = (n)` take the stated two-term shape `t^{m+1} w_{b-1} + t^m w_a` is *rim-hook
  combinatorics*, and it is the input to `no_solution_general`, supplied here as the hypothesis
  `hE`. Nothing below derives it. The `n = 4` matrix `ReciprocityCertificate.M` remains
  **transcribed** from the paper's table, not derived; `M_mulVec_eq` checks the transcription
  against `lem:rows` entry by entry, which is a calibration, not a derivation.
* **Not formalised:** anything quantified over `μ`. Theorem `thm:local` of the *earlier* paper
  (`2026-09-10-Q129-...`), which asserted inconsistency for every `μ ⊢ n` with `4 ≤ n ≤ 7`, is
  **false**; its registry node `Q129-local-identity-unsolvable` is `dead-end`. Its corrected
  replacement `thm:class` classifies the consistent cells, and was stated in the Q140 paper as
  verified to `n ≤ 9`; the reflection-graph paper `~/projects/proofs/`
  `2026-09-11-Q143-graph-criterion.tex` closes its two combinatorial gaps and upgrades it to
  proved for all `μ` and all `n`. **None of that is formalised here.** This file speaks only
  about `μ = (n)`.

## The system

By `lem:rows`, for `μ = (n)` every row of the local-identity matrix is zero, or the all-ones
row, or has exactly two nonzero entries. After dividing each two-term row by the common power
of `t` in it, the homogeneous system is exactly

`E (a, b) : t * w (b - 1) + w a = 0` for all `a ≥ b ≥ 1` with `a + b ≤ n`,

together with the inhomogeneous row `G : ∑ k ∈ range n, w k = 1`.

## The proof, in five steps

1. `E (a, 1)` is available for every `1 ≤ a ≤ n - 1`, and gives `w a = -(t * w 0)`.
2. `E (2, 2)` is available **precisely when `n ≥ 4`**, and gives `t * w 1 + w 2 = 0`.
3. Substituting step 1 at `a = 1, 2` into step 2 gives `t * (t + 1) * w 0 = 0`.
4. `G` with step 1 gives `w 0 * (1 - (n - 1) * t) = 1`, so `w 0` is a **unit**.
5. Multiplying step 3 by that inverse gives `t * (t + 1) = 0`.

Step 4 is what lets the whole argument live over an arbitrary `CommRing`: the paper divides by
`t (t + 1)` in `ℚ(t)` to conclude `w 0 = 0`, but one may instead multiply by the *inverse of
`w 0`*, which the inhomogeneous row hands over for free. No division is used anywhere.

Note where the hypothesis `4 ≤ n` enters: in **exactly one place**, as the availability of the
single equation `E (2, 2)`, whose index constraint is `2 + 2 ≤ n`. At `n = 3` the system is
consistent (`w = (-1, t, t) / (2t - 1)`), so the hypothesis is load-bearing and not an artefact.

## Main results

* `no_solution_general` — over any `CommRing`, `E` and `G` with `4 ≤ n` force `t (t + 1) = 0`.
* `reciprocity_does_not_deform_general` — hence over `ℚ[X]` with `t = X`, no solution, for
  every `n ≥ 4`.
* `consistent_at_neg_one_general` — the live population: at `t = -1` the uniform `w ≡ u` solves
  the system whenever `(n : R) * u = 1`, e.g. `u = 1/n` over `ℚ`.
* `M_mulVec_eq`, `n4_no_solution_via_general` — the bridge to the transcribed `n = 4` matrix.
-/

namespace TworowD4Kernel.ReciprocityFamily

open Finset Matrix

variable {R : Type*} [CommRing R]

/-- **The obstruction, uniformly in `n`.** Theorem `thm:mainrow` of
`2026-09-10-c2-Q140-local-identity-certificate-family.tex`, for `μ = (n)`.

If the divided local system `E` (hypothesis `hE`) together with the inhomogeneous row `G`
(hypothesis `hG`) has a solution `w` over a commutative ring, then `t * (t + 1) = 0`.

Over `ℚ(t)` — or over any ring in which `t (t + 1)` is not a zero divisor, in particular
`ℚ[X]` with `t = X` — this is a contradiction, so the system is inconsistent. Over an
arbitrary `CommRing` the conclusion is the sharper statement: a solution exists only where
`t (t + 1)` vanishes, which at `t = -1` it does — see `consistent_at_neg_one_general`.

The hypothesis `4 ≤ n` is used exactly once, to make `E (2, 2)` available. -/
theorem no_solution_general (t : R) (n : ℕ) (hn : 4 ≤ n) (w : ℕ → R)
    (hE : ∀ a b : ℕ, 1 ≤ b → b ≤ a → a + b ≤ n → t * w (b - 1) + w a = 0)
    (hG : ∑ k ∈ range n, w k = 1) :
    t * (t + 1) = 0 := by
  -- Write `n = m + 1`; the hypothesis `4 ≤ n` becomes `3 ≤ m`.
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- **Step 1.** `E (a, 1)` for every `1 ≤ a ≤ m`.
  have step1 : ∀ a : ℕ, 1 ≤ a → a + 1 ≤ m + 1 → w a = -(t * w 0) := by
    intro a ha han
    have h := hE a 1 le_rfl ha han
    norm_num at h
    linear_combination h
  -- **Step 2.** `E (2, 2)`, available because `2 + 2 ≤ n`. This is the only use of `4 ≤ n`.
  have step2 : t * w 1 + w 2 = 0 := by
    have h := hE 2 2 (by norm_num) le_rfl (by omega)
    norm_num at h
    linear_combination h
  -- **Step 3.** Substitute step 1 at `a = 1, 2` into step 2.
  have h1 : w 1 = -(t * w 0) := step1 1 le_rfl (by omega)
  have h2 : w 2 = -(t * w 0) := step1 2 (by omega) (by omega)
  have step3 : t * (t + 1) * w 0 = 0 := by
    rw [h1, h2] at step2; linear_combination -step2
  -- **Step 4.** The inhomogeneous row makes `w 0` a unit.
  rw [Finset.sum_range_succ'] at hG
  have hsum : ∑ i ∈ range m, w (i + 1) = ∑ _i ∈ range m, -(t * w 0) :=
    Finset.sum_congr rfl fun i hi => step1 (i + 1) (by omega) (by simp at hi; omega)
  rw [hsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hG
  have step4 : w 0 * (1 - (m : R) * t) = 1 := by linear_combination hG
  -- **Step 5.** Multiply step 3 by that inverse. No division anywhere.
  linear_combination (1 - (m : R) * t) * step3 - t * (t + 1) * step4

/-- **The live population.** At `t = -1` the very same system *is* consistent, for every `n`,
with the uniform witness `w ≡ u` for any `u` inverting `n`.

This is Theorem `thm:euler` of the source paper specialised to `μ = (n)`: at `t = -1` the
Euler degree operator `∑_L p_L p_L^⊥ = n · id` gives `wtB(μ, γ) = (-1)^{ht(μ/γ)} / n`, which
for `μ = (n)` is the uniform `1/n`.

Stated over an arbitrary `CommRing` one cannot divide by `n`, so invertibility is a
hypothesis rather than a construction; `consistent_at_neg_one_rat` supplies the witness
`u = 1/n` over `ℚ`. Without this theorem, `reciprocity_does_not_deform_general` would be an
emptiness with no live population beside it. -/
theorem consistent_at_neg_one_general (n : ℕ) (u : R) (hu : (n : R) * u = 1) :
    ∃ w : ℕ → R,
      (∀ a b : ℕ, 1 ≤ b → b ≤ a → a + b ≤ n → (-1 : R) * w (b - 1) + w a = 0) ∧
      ∑ k ∈ range n, w k = 1 :=
  ⟨fun _ => u, fun _ _ _ _ _ => by ring, by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; exact hu⟩

/-- The anchor witness over `ℚ`: `w k = 1 / n` for all `k`. At `n = 4` this is the
`(1/4, 1/4, 1/4, 1/4)` of `ReciprocityCertificate.consistent_at_neg_one`. -/
theorem consistent_at_neg_one_rat (n : ℕ) (hn : 1 ≤ n) :
    ∃ w : ℕ → ℚ,
      (∀ a b : ℕ, 1 ≤ b → b ≤ a → a + b ≤ n → (-1 : ℚ) * w (b - 1) + w a = 0) ∧
      ∑ k ∈ range n, w k = 1 := by
  refine consistent_at_neg_one_general n (1 / (n : ℚ)) ?_
  have : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **Corollary `cor:answer`, formalised for `μ = (n)`.** Over `ℚ[X]` with `t = X`, the local
identity has no solution, for every `n ≥ 4`. So the inversion reciprocity does not deform
along `t` — one failing family suffices, since the Khanna–Loehr identity is required at every
`μ`.

Scope: this is the family `μ = (n)`. It is not a statement about any other `μ`. -/
theorem reciprocity_does_not_deform_general (n : ℕ) (hn : 4 ≤ n) :
    ¬ ∃ w : ℕ → Polynomial ℚ,
      (∀ a b : ℕ, 1 ≤ b → b ≤ a → a + b ≤ n →
        (Polynomial.X : Polynomial ℚ) * w (b - 1) + w a = 0) ∧
      ∑ k ∈ range n, w k = 1 := by
  rintro ⟨w, hE, hG⟩
  have key := no_solution_general (Polynomial.X : Polynomial ℚ) n hn w hE hG
  -- `X * (X + 1) = 0` in `ℚ[X]`; evaluate at `1`, where it reads `2 = 0`.
  have hev := congrArg (Polynomial.eval (1 : ℚ)) key
  simp at hev

/-!
## Non-vacuity, and the negative control as a theorem
-/

/-- **The negative control, internalised.** The hypothesis `4 ≤ n` of `no_solution_general`
cannot be weakened to `3 ≤ n`, and this is a theorem rather than an experiment: over `ℚ` at
`t = 2` and `n = 3` the system *has* a solution — the paper's `w = (-1, t, t) / (2t - 1)`,
here `(-1/3, 2/3, 2/3)` — while the would-be conclusion `t * (t + 1) = 6` is nonzero.

The reason is visible in the proof of `no_solution_general`: the equation `E (2, 2)` requires
`2 + 2 ≤ n`, and it is the only place `4 ≤ n` is used. On this witness `E (2, 2)` would read
`2 * w 1 + w 2 = 2` — see `n3_fails_E22` — so it is exactly the missing equation. -/
theorem n3_consistent_at_two :
    ∃ w : ℕ → ℚ,
      (∀ a b : ℕ, 1 ≤ b → b ≤ a → a + b ≤ 3 → (2 : ℚ) * w (b - 1) + w a = 0) ∧
      (∑ k ∈ range 3, w k = 1) ∧ (2 : ℚ) * (2 + 1) ≠ 0 := by
  refine ⟨fun k => if k = 0 then -1/3 else 2/3, ?_, ?_, by norm_num⟩
  · intro a b hb hba hab
    have hb1 : b = 1 := by omega
    subst hb1
    have ha : a = 1 ∨ a = 2 := by omega
    rcases ha with rfl | rfl <;> norm_num
  · norm_num [Finset.sum_range_succ]

/-- The missing equation named. On the `n = 3` witness of `n3_consistent_at_two`, `E (2, 2)`
reads `2 * (2/3) + 2/3 = 2 ≠ 0`. -/
theorem n3_fails_E22 : (2 : ℚ) * (2/3) + 2/3 ≠ 0 := by norm_num

/-- Non-vacuity of the conclusion: the obstruction `t * (t + 1)` is genuinely nonzero away
from `t ∈ {0, -1}`; at `t = 2` over `ℤ` it is `6`. Shadowed by a `#guard` in
`TworowD4KernelTests`. -/
theorem obstruction_nonvacuous : (2 : ℤ) * (2 + 1) = 6 := by decide

/-- Non-vacuity of the anchor hypothesis `(n : R) * u = 1` at `n = 4`, denominators cleared:
`4 * 1 = 4`, i.e. `u = 1/4` is the witness matching
`ReciprocityCertificate.consistent_at_neg_one`. Shadowed by a `#guard`. -/
theorem anchor_n4_nonvacuous : (4 : ℚ) * (1/4) = 1 := by norm_num

/-!
## The bridge to the transcribed `n = 4` matrix

Without this section the `n = 4` file and this one would be two unconnected claims. The bridge
runs in two steps.
-/

/-- **Calibration.** The transcribed `5 × 4` matrix `ReciprocityCertificate.M` — copied from the
paper's displayed table and independently sympy-checked — has exactly the rows that `lem:rows`
predicts at `n = 4`, `μ = (4)`: the all-ones row `G` for `λ = (4)`, and for
`λ = (a, b, 1^m)` the two-term row `t^m * (t * w_{b-1} + w_a)`.

Row order is `(4), (3,1), (2,2), (2,1,1), (1,1,1,1)`, i.e.
`(a,b,m) = (3,1,0), (2,2,0), (2,1,1), (1,1,2)`. Holds over any `CommRing` — no division. -/
theorem M_mulVec_eq (t : R) (v : ℕ → R) :
    ReciprocityCertificate.M t *ᵥ (fun i : Fin 4 => v i) =
      ![∑ k ∈ range 4, v k,
        t ^ 0 * (t * v 0 + v 3),
        t ^ 0 * (t * v 1 + v 2),
        t ^ 1 * (t * v 0 + v 2),
        t ^ 2 * (t * v 0 + v 1)] := by
  funext i
  fin_cases i <;>
    simp [ReciprocityCertificate.M, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Finset.sum_range_succ] <;> ring

/-- **The bridge.** `ReciprocityCertificate.reciprocity_does_not_deform` — the `n = 4` cell,
originally proved via the hand certificate `cert` — re-derived from `no_solution_general` at
`n = 4`.

Two independent routes to one statement: the old proof pairs a left null vector with `b`, this
one runs the five-step elimination. They agree, which is the calibration the `n = 4`
transcription buys.

Why over `ℚ[X]` and not an arbitrary `CommRing`: passing from the matrix rows to the divided
system `E` means cancelling the factors `t^m` of `M_mulVec_eq` — legitimate here because `ℚ[X]`
is a domain and `X ≠ 0`, but *not* over an arbitrary commutative ring, where `t` may be a zero
divisor. That cancellation is precisely the paper's phrase "after dividing each row by the
common power of `t` in its row", and this is the one place it costs a hypothesis. -/
theorem n4_no_solution_via_general :
    ¬ ∃ w : Fin 4 → Polynomial ℚ,
      ReciprocityCertificate.M (Polynomial.X : Polynomial ℚ) *ᵥ w = ReciprocityCertificate.b := by
  rintro ⟨w, hw⟩
  set X := (Polynomial.X : Polynomial ℚ) with hX
  -- Extend `w` to `ℕ → ℚ[X]` by zero, so that it can be fed to `no_solution_general`.
  set v : ℕ → Polynomial ℚ := fun k => if h : k < 4 then w ⟨k, h⟩ else 0 with hv
  have hvw : (fun i : Fin 4 => v i) = w := by
    funext i; simp [hv, i.isLt]
  rw [← hvw, M_mulVec_eq] at hw
  have hX0 : X ≠ 0 := Polynomial.X_ne_zero
  -- Read off the five rows.
  have r0 := congrFun hw 0
  have r1 := congrFun hw 1
  have r2 := congrFun hw 2
  have r3 := congrFun hw 3
  have r4 := congrFun hw 4
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, pow_zero, one_mul, pow_one, Fin.isValue,
    cons_val_zero, ReciprocityCertificate.b, cons_val_one, Matrix.cons_val, mul_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at r0 r1 r2 r3 r4
  -- Cancel the powers of `X` in rows `(2,1,1)` and `(1,1,1,1)`.
  have e31 : X * v 0 + v 3 = 0 := r1
  have e22 : X * v 1 + v 2 = 0 := r2
  -- `simp` has already discharged the `X^m * _ = 0` split, leaving a disjunction.
  have e21 : X * v 0 + v 2 = 0 := r3.resolve_left hX0
  have e11 : X * v 0 + v 1 = 0 := r4.resolve_left hX0
  -- Feed the four equations, in the indexing of `E`, to the general theorem.
  refine absurd (no_solution_general X 4 le_rfl v ?_ ?_) ?_
  · intro a b hb hba hab
    have : b = 1 ∨ b = 2 := by omega
    rcases this with rfl | rfl
    · have : a = 1 ∨ a = 2 ∨ a = 3 := by omega
      rcases this with rfl | rfl | rfl
      · simpa using e11
      · simpa using e21
      · simpa using e31
    · have : a = 2 := by omega
      subst this
      simpa using e22
  · simpa using r0
  · -- `X * (X + 1) ≠ 0` in `ℚ[X]`: evaluate at `1`.
    intro hcon
    have hev := congrArg (Polynomial.eval (1 : ℚ)) hcon
    simp [hX] at hev

end TworowD4Kernel.ReciprocityFamily
