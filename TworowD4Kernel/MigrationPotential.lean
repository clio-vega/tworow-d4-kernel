/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.List.Chain
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.NormNum

/-!
# The migration potential: `Δφ = 1` makes path length a state function, `Δφ = ±1` does not

Formalisation of the abstract core of
`projects/proofs/2026-10-05-c3-migration-length-grading.tex` (Theorem 1) and of
Corollary 2 (`cor:irred`) of
`projects/proofs/2026-10-06-migration-vertical-step-gap.tex`.  Registry:
`proofs/registry/migration-length-grading.json`, node `potential-phi` and its child
`gap-vertical-step-orientation`/`no-potential-can-close-the-gap`.

The mathematical setting is Purbhoo's migration of a mosaic to its Littlewood–Richardson
tableau (arXiv:0705.1184, §3.1 for the step rule, §4 for the wake).  A *migration length*
`ℓ(M)` is the number of hexagon rotations performed along one journey.  The 2026-10-05
finding is that `ℓ` is not a grading on `c^λ_{μν}`, because migration carries an exact
potential: on the `ℤ⁴` lift of a mosaic, `φ(a,b,c,e) = b + e` satisfies `Δφ = 1` at every
step, so `ℓ` is a potential difference and depends only on the endpoints.

## What is formalised here, and what is not

Everything below is *abstract*: `step` is an arbitrary relation on an arbitrary type and
`φ` an arbitrary `ℤ`-valued function.  That is deliberate, and it is the whole scope line:

* `length_eq_potential_diff` is the telescoping argument, which is the part of the paper
  proof where an unstated hypothesis could hide.  Lean refuses to let the `+1` be
  anything else.
* `length_eq_of_endpoints` (gradedness) and `sum_pow_length` (the generating function is
  a monomial) are its two corollaries, and they *are* the two statements the paper uses.
* `no_potential_of_step_symm` is Corollary 2 of the 10-06 note: a mutually inverse pair
  of steps admits **no** potential with `Δφ = +1`.
* `pm_one_not_graded` exhibits a concrete relation for which the `±1` relaxation makes
  path length **not** a function of the endpoints.

What is **not** formalised, and is not formalisable from these statements:

* that `φ(a,b,c,e) = b + e` actually has `Δφ = 1` on actual migration steps.  That is the
  classification of §"Classification of steps" of the 10-05 note — an exhaustive
  enumeration over `90` hexagon regions, every tiling, every rhombus, every rotation — and
  it is `computed`, not `proved`.
* Proposition 1 of the 10-06 note (the two strictly vertical steps are the two tilings of
  the zonogon `R ⊕ [0,1]u₆₀`, hence mutually inverse).  That is again an exhaustive
  geometric enumeration.  `no_potential_of_step_symm` is the *abstract* half of that
  Corollary: granted mutual inversion, no potential exists.  The geometric half is its
  hypothesis, supplied from outside.
* Hypothesis (G) (`hyp-G-no-strip-below`), that the backward vertical direction is never
  realised, on which Theorem 1 of the 10-05 note rests.  It is unproved, empirically null
  over `3111` steps, and nothing here bears on it.

So this file does not prove Theorem 1.  It proves that Theorem 1's `Δφ = 1` hypothesis is
**load-bearing**: `pm_one_not_graded` is a type-checked witness that weakening it to `±1`
destroys the conclusion, and `no_potential_of_step_symm` is a type-checked witness that the
gap cannot be repaired by choosing a better potential.

## Relation to Mathlib

Mathlib's nearest object is `GradeOrder` (`Mathlib/Order/Grade.lean`), which fixes the
relation to the covering relation `⋖` of a preorder and the grade to land in a graded
order; it then *derives* `grade b = grade a + 1` from `a ⋖ b`.  Here the implication runs
the other way — the `+1` is the hypothesis and the relation is arbitrary — and a migration
step is not presented as a covering relation of any order on mosaics, so `GradeOrder` does
not apply.  A search of `Mathlib.Data.List.Chain` for a conclusion of the form
`l.length = f (getLast …) - f (head …)` found none; the telescoping below is three lines,
which is presumably why.
-/

namespace TworowD4Kernel.MigrationPotential

open List

variable {α : Type*}

/-! ### Task 1 — the potential lemma -/

/-- **The potential lemma.**  If `φ` increases by exactly `1` along every `step`, then the
length of any `step`-chain from `a` to `b` is `φ b - φ a`.  This is the telescoping
argument of Theorem 1 of `2026-10-05-c3-migration-length-grading.tex`: with
`φ(a,b,c,e) = b + e` on the `ℤ⁴` lift of a mosaic and `step` a Purbhoo migration step
(arXiv:0705.1184 §3.1), it says the migration length `ℓ(M)` is a potential difference.

The hypothesis `h` is where the whole content sits; see `pm_one_not_graded` for what
happens when it is weakened to `±1`. -/
theorem length_eq_potential_diff (step : α → α → Prop) (φ : α → ℤ)
    (h : ∀ x y, step x y → φ y = φ x + 1) {a b : α} {l : List α}
    (hchain : IsChain step (a :: l))
    (hlast : (a :: l).getLast (cons_ne_nil a l) = b) :
    (l.length : ℤ) = φ b - φ a := by
  induction l generalizing a with
  | nil =>
    simp only [getLast_singleton] at hlast
    subst hlast
    simp
  | cons c t ih =>
    obtain ⟨hstep, htail⟩ := isChain_cons_cons.1 hchain
    have hlast' : (c :: t).getLast (cons_ne_nil c t) = b := by
      rwa [getLast_cons_cons] at hlast
    have := ih htail hlast'
    have hc : φ c = φ a + 1 := h a c hstep
    simp only [length_cons]
    push_cast
    omega

/-! ### Task 2 — the two corollaries the paper uses -/

/-- **Gradedness.**  Any two `step`-paths with the same endpoints have the same length.
This is what makes `ℓ(M)` independent of the order in which the rhombi of the flock are
migrated — measured empirically as `ℓ` order-independent in `0 / 362` mosaics while the
output tableau is order-dependent in `67 / 362` (registry node `t1-order-independence`).
That dissociation is the evidence for the potential; this is its reason. -/
theorem length_eq_of_endpoints (step : α → α → Prop) (φ : α → ℤ)
    (h : ∀ x y, step x y → φ y = φ x + 1) {a b : α} {l₁ l₂ : List α}
    (hc₁ : IsChain step (a :: l₁)) (he₁ : (a :: l₁).getLast (cons_ne_nil a l₁) = b)
    (hc₂ : IsChain step (a :: l₂)) (he₂ : (a :: l₂).getLast (cons_ne_nil a l₂) = b) :
    l₁.length = l₂.length := by
  have h₁ := length_eq_potential_diff step φ h hc₁ he₁
  have h₂ := length_eq_potential_diff step φ h hc₂ he₂
  omega

/-- **The generating function is a monomial.**  If every member of a finite family of
journeys has the same length `ℓ₀`, then `∑ q ^ ℓ M = |F| · q ^ ℓ₀`.  Combined with
`length_eq_of_endpoints` and the positive control `#mosaics = c^λ_{μν}` (registry node
`positive-control-lr-counts`), this is why `G(q) = c^λ_{μν} · q ^ ℓ₀` and `ℓ` refines
nothing.

Deliberately stated with no nonemptiness hypothesis: it is true vacuously for `F = ∅`,
and the honest remark is that this corollary is *small* — it is `Finset.sum_congr` on a
constant function. The mathematics is all in `length_eq_of_endpoints`. -/
theorem sum_pow_length {R : Type*} [CommSemiring R] {β : Type*} (F : Finset β)
    (ℓ : β → ℕ) (ℓ₀ : ℕ) (q : R) (h : ∀ M ∈ F, ℓ M = ℓ₀) :
    ∑ M ∈ F, q ^ ℓ M = (F.card : R) * q ^ ℓ₀ := by
  rw [Finset.sum_congr rfl (fun M hM => by rw [h M hM])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ### Task 3 — the `±1` relaxation is not enough -/

/-- **Corollary 2 of `2026-10-06-migration-vertical-step-gap.tex` (`cor:irred`), abstract
half.**  If two states are mutually `step`-reachable in one step, then *no* function has
`Δ = +1` on every step.  Hence the vertical-orientation gap cannot be closed by replacing
`φ(a,b,c,e) = b + e` with a better potential — it can only be closed by showing one of the
two directions is never realised (Hypothesis (G)).

The hypothesis `step a b ∧ step b a` is supplied from outside, by Proposition 1 of that
note: the two strictly vertical steps share the hexagon `R ⊕ [0,1]u₆₀`, are its two
tilings, and are interchanged by its central symmetry.  That geometric fact is an
exhaustive enumeration and is *not* formalised here. -/
theorem no_potential_of_step_symm {step : α → α → Prop} {a b : α}
    (hab : step a b) (hba : step b a) :
    ¬ ∃ φ : α → ℤ, ∀ x y, step x y → φ y = φ x + 1 := by
  rintro ⟨φ, h⟩
  have h₁ := h a b hab
  have h₂ := h b a hba
  omega

/-- **The `±1` relaxation destroys gradedness.**  There is a relation and a `φ` with
`Δφ = ±1` at every step for which two chains share their endpoints and have different
lengths.  So the `Δφ = +1` of `length_eq_potential_diff` is load-bearing, not cosmetic:
with `±1` the conclusion genuinely fails.

The witness is `step x y ↔ y = x + 1 ∨ y = x - 1` on `ℤ` with `φ = id`, and the two paths
`0 → 1` (length `1`) and `0 → 1 → 2 → 1` (length `3`), the last step backward.  This is
the abstract shadow of the gap: `91` of `707` computed migration steps were strictly
vertical, all `91` took `+1`, and nothing proves `-1` cannot occur. -/
theorem pm_one_not_graded :
    ∃ (β : Type) (step : β → β → Prop) (φ : β → ℤ) (a b : β) (l₁ l₂ : List β),
      (∀ x y, step x y → φ y = φ x + 1 ∨ φ y = φ x - 1) ∧
      IsChain step (a :: l₁) ∧ (a :: l₁).getLast (cons_ne_nil a l₁) = b ∧
      IsChain step (a :: l₂) ∧ (a :: l₂).getLast (cons_ne_nil a l₂) = b ∧
      l₁.length ≠ l₂.length := by
  refine ⟨ℤ, fun x y => y = x + 1 ∨ y = x - 1, id, 0, 1, [1], [1, 2, 1], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hxy
  · exact isChain_pair.2 (Or.inl (by omega))
  · rfl
  · exact .cons_cons (Or.inl (by omega)) (.cons_cons (Or.inl (by omega))
      (.cons_cons (Or.inr (by omega)) (.singleton _)))
  · rfl
  · decide

/-- **Why the witness of `pm_one_not_graded` escapes `length_eq_potential_diff`.**  The
relation `y = x ± 1` on `ℤ` admits *no* potential with `Δφ = +1`, and it fails for exactly
the reason `no_potential_of_step_symm` names: `0 → 1` and `1 → 0` are both steps, a
mutually inverse pair.

This is the consistency check that makes the pair (`length_eq_of_endpoints`,
`pm_one_not_graded`) a genuine dissociation rather than an accident: the counterexample
relation is not merely one for which `φ = id` happens to take `-1` somewhere, it is one
no reparametrisation can fix.  It is the abstract shadow of Corollary 2 of the 10-06 note
— if the backward vertical migration step is ever realised, the `ℓ`-grading is not
recoverable by choosing a different height function. -/
theorem pm_one_witness_has_no_potential :
    ¬ ∃ φ : ℤ → ℤ, ∀ x y : ℤ, (y = x + 1 ∨ y = x - 1) → φ y = φ x + 1 :=
  no_potential_of_step_symm (step := fun x y : ℤ => y = x + 1 ∨ y = x - 1)
    (a := 0) (b := 1) (Or.inl (by omega)) (Or.inr (by omega))

end TworowD4Kernel.MigrationPotential
