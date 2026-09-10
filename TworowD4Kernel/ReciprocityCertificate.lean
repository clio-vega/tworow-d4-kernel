/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The `n = 4`, `μ = (4)` inconsistency certificate for ribbon reciprocity

This file formalises **one cell**, `n = 4` and `μ = (4)`, of the inconsistency of the
Khanna–Loehr local identity. It makes **no** claim for any other `μ`, and **none** for
general `n`. Nothing here is a formalisation of a statement quantified over `μ` or over `n`.

## Source, and a correction carried into it

The certificate below is the one displayed in
`~/projects/proofs/2026-09-10-Q129-reciprocity-does-not-deform.tex` (Theorem `thm:local`,
and the proof headed "Proof of Theorem thm:local at `n = 4`, `μ = (4)`"). The reciprocity
being tested for deformation is the Adin–Bauer / Khanna–Loehr inversion reciprocity
(arXiv:2505.10783, §2).

**That theorem's quantifier has since been refuted.** `thm:local` asserted inconsistency for
*every* `μ ⊢ n` with `4 ≤ n ≤ 7`; `~/projects/proofs/2026-09-10-c2-Q140-local-identity-`
`certificate-family.tex` (Theorem `thm:class`) exhibits the consistent cells
`n = 4, μ = (2,2)` and `n = 5, μ ∈ {(3,2), (2,2,1)}`. The registry node
`Q129-local-identity-unsolvable` is `dead-end` in consequence.

**The cell formalised here is not affected**, and is the reason the scope note above is
narrow. It survives as the `n = 4` member of the certificate family of `thm:mainrow`
(`μ = (n)`, all `n ≥ 4`) in that same corrected paper. Concretely `cert` below is `t · c⁽⁴⁾`
for the family's `c⁽ⁿ⁾`, checked entrywise; that stray factor of `t` is a normalisation
artefact of the earlier paper and is exactly why the obstruction here reads `t² (t + 1)`
rather than the family's `t (t + 1)`. The extra root at `t = 0` is therefore **not** a second
anchor. Only the root at `t = -1` is structural — see `consistent_at_neg_one`.

This file does not formalise `thm:class`, `thm:mainrow`, or the family `c⁽ⁿ⁾`. Those remain
paper results; their registry nodes are unchanged by this file.

## The statement

Let `μ = (4)`, whose rim-hook predecessors are `∅, (1), (2), (3)`. With unknowns
`wₖ = wtB((4), (k))` (and `w₀ = wtB((4), ∅)`), the local identity `eq:local` reads
`M t *ᵥ w = b`, where the rows of `M t` are indexed by
`(4), (3,1), (2,2), (2,1,1), (1,1,1,1)` — see `M` below. Over `ℚ(t)` — here realised, more
strongly, over the polynomial ring `ℚ[X]` — this system has **no** solution, while at the
anchor `t = -1` it does.

## Main results

* `TworowD4Kernel.ReciprocityCertificate.cert_annihilates` — `cert t ᵥ* M t = 0`, the four
  polynomial identities of the paper proof, one per column.
* `TworowD4Kernel.ReciprocityCertificate.cert_pairing` — `cert t ⬝ᵥ b = t ^ 2 * (t + 1)`.
* `TworowD4Kernel.ReciprocityCertificate.no_solution` — over any commutative ring, a solution
  forces `t ^ 2 * (t + 1) = 0`.
* `TworowD4Kernel.ReciprocityCertificate.reciprocity_does_not_deform` — over `ℚ[X]` with
  `t = X` there is no solution.
* `TworowD4Kernel.ReciprocityCertificate.consistent_at_neg_one` — and at `t = -1` there is
  one, namely the uniform `w = (1/4, 1/4, 1/4, 1/4)`.

The last two together are the content: the failure is not a blanket emptiness, it is a
statement that `t = -1` is special.

## A note on the certificate at the anchor

`cert (-1) = (0, 0, -4, -4, -4) ≠ 0` still annihilates `M (-1)`; what dies at `t = -1` is the
*pairing* `cert t ⬝ᵥ b`, not the certificate. This is visible in `cert_pairing` at `t = -1`
and matches the paper's remark that `rank (M) = rank [M | b] = 4` there.
-/

namespace TworowD4Kernel.ReciprocityCertificate

open Matrix

variable {R : Type*} [CommRing R]

/-- The `5 × 4` coefficient matrix of the local identity at `n = 4`, `μ = (4)`.

Rows are the partitions `λ ⊢ 4` in the order `(4), (3,1), (2,2), (2,1,1), (1,1,1,1)`;
columns are the unknowns `w₀, w₁, w₂, w₃`. Transcribed from the displayed table in
`2026-09-10-Q129-reciprocity-does-not-deform.tex`. -/
def M (t : R) : Matrix (Fin 5) (Fin 4) R :=
  !![1, 1, 1, 1;
     t, 0, 0, 1;
     0, t, 1, 0;
     t ^ 2, 0, t, 0;
     t ^ 3, t ^ 2, 0, 0]

/-- The right-hand side `b = (1, 0, 0, 0, 0)ᵀ` of the local identity. It does not depend
on `t`. -/
def b : Fin 5 → R := ![1, 0, 0, 0, 0]

/-- The inconsistency certificate `c` of the paper proof: a left null vector of `M t` that
pairs nontrivially with `b`. -/
def cert (t : R) : Fin 5 → R :=
  ![t ^ 2 * (t + 1), -(t ^ 2 * (t + 1)), -(t * (3 * t - 1)), -(t - 1) ^ 2, 2 * (t - 1)]

/-- `c M = 0`: the four polynomial identities of the paper proof, one per column. -/
theorem cert_annihilates (t : R) : cert t ᵥ* M t = 0 := by
  funext j
  fin_cases j <;>
    simp [cert, M, Matrix.vecMul, dotProduct, Fin.sum_univ_five] <;> ring

/-- `c b = t² (t + 1)`. -/
theorem cert_pairing (t : R) : cert t ⬝ᵥ (b : Fin 5 → R) = t ^ 2 * (t + 1) := by
  simp [cert, b, dotProduct, Fin.sum_univ_five]

/-- The certificate argument, over an arbitrary commutative ring: if the local system has a
solution then `t² (t + 1) = 0`. -/
theorem no_solution (t : R) (h : ∃ w : Fin 4 → R, M t *ᵥ w = b) : t ^ 2 * (t + 1) = 0 := by
  obtain ⟨w, hw⟩ := h
  have key : cert t ⬝ᵥ (M t *ᵥ w) = cert t ⬝ᵥ (b : Fin 5 → R) := by rw [hw]
  rw [Matrix.dotProduct_mulVec, cert_annihilates, zero_dotProduct, cert_pairing] at key
  exact key.symm

/-- **The `n = 4`, `μ = (4)` cell.** Over `ℚ[X]` with `t = X`, the local identity `eq:local`
has no solution, so the inversion reciprocity does not deform along `t` at this cell.

Scope: this is one cell. It is the `n = 4` member of the `μ = (n)` family of `thm:mainrow`,
and it is *not* a proof of that family, nor of any statement quantified over `μ`. Some other
cells at this `n` are consistent — `n = 4, μ = (2,2)` is — which is why the quantifier must
stay where it is. -/
theorem reciprocity_does_not_deform :
    ¬ ∃ w : Fin 4 → Polynomial ℚ, M (Polynomial.X : Polynomial ℚ) *ᵥ w = b := by
  intro h
  have key := no_solution (Polynomial.X : Polynomial ℚ) h
  -- Evaluate the resulting polynomial identity `X² (X + 1) = 0` at `1`, where it reads `2 = 0`.
  have hev := congrArg (Polynomial.eval (1 : ℚ)) key
  simp at hev

/-- The sharp complement: at the anchor `t = -1` the very same system **is** consistent, with
the uniform witness `w = (1/4, 1/4, 1/4, 1/4)`.

Without this, `reciprocity_does_not_deform` would be an emptiness with no live population
beside it; with it, the pair says that `t = -1` is special. -/
theorem consistent_at_neg_one : ∃ w : Fin 4 → ℚ, M (-1 : ℚ) *ᵥ w = b :=
  ⟨![1 / 4, 1 / 4, 1 / 4, 1 / 4], by
    funext i
    fin_cases i <;> simp [M, b, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> norm_num⟩

/-!
## Non-vacuity witnesses

Everything above is an identity in an indeterminate `t`, so it would all be equally provable
of a matrix that was accidentally zero. The three checks below are decidable instances over
`ℤ` that pin the actual numbers, and are shadowed by `#guard`s in `TworowD4KernelTests`.
-/

/-- Non-vacuity: the certificate really annihilates a numerically instantiated `M`. -/
theorem cert_annihilates_nonvacuous : cert (2 : ℤ) ᵥ* M (2 : ℤ) = 0 := by decide

/-- Non-vacuity: and the pairing really is nonzero there — `t² (t + 1) = 12` at `t = 2`. -/
theorem cert_pairing_nonvacuous : cert (2 : ℤ) ⬝ᵥ (b : Fin 5 → ℤ) = 12 := by decide

/-- Non-vacuity: `M` is not the zero matrix, and the anchor witness is genuinely a solution.
This is `consistent_at_neg_one` cleared of denominators: `M (-1) *ᵥ (1,1,1,1) = (4,0,0,0,0)`. -/
theorem consistent_at_neg_one_nonvacuous :
    M (-1 : ℤ) *ᵥ ![1, 1, 1, 1] = ![4, 0, 0, 0, 0] := by decide

end TworowD4Kernel.ReciprocityCertificate
