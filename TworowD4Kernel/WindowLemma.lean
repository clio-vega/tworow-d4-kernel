/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-!
# The window lemma

> In any `N` consecutive integers, each residue class mod `N` occurs exactly once.

This is the purely arithmetic engine behind the bound `a ≤ ℓ - 1` in the closed-form
theorem `thm:closed` of `proofs/2026-09-01-Q63-wedge-fock-normalisation.tex` (§`sec:closed`).
There the `ℓ` runners of an abacus are the residue classes mod `N` in Uglov's indexation
`k = c + n(d-1) - n ℓ μ`, and the locality argument needs to know that a window of `N`
consecutive positions meets every runner exactly once -- no more (which bounds the number
of beads that can move) and no fewer (which is what makes the bound attained).

Two forms are given, because the downstream argument uses both:

* `window_residues_bijective` -- the *indexing* form: `i ↦ p + i` is a bijection
  `Fin N ≃ ZMod N`. Used when one wants to name the runner of the `i`-th position.
* `card_window_eq_one` -- the *counting* form: each fibre of `k ↦ k mod N` over the window
  `Ico p (p + N)` is a singleton. Used when one wants to count beads on a fixed runner.

The statements are phrased over `ZMod N` rather than over `Int.emod`, because that is
what the mathematics actually uses: the runner index is an element of a cyclic group of
order `N`, not a distinguished representative in `[0, N)`.

Mathlib has all the ingredients (`ZMod.intCast_zmod_eq_zero_iff_dvd`,
`Int.eq_zero_of_abs_lt_dvd`, `ZMod.val_lt`) but, as of `v4.30.0`, neither statement
in this form; searched under `Mathlib/Data/ZMod/`, `Mathlib/Order/Interval/Finset/` and
for `ExistsUnique` over `Ico`.
-/

namespace TworowD4Kernel

open Finset

section Window

variable (N : ℕ) [NeZero N]

/-- The canonical representative of the class `r` inside the window `[p, p + N)`. -/
private def windowRep (p : ℤ) (r : ZMod N) : ℤ :=
  p + ((r - (p : ZMod N)).val : ℕ)

private lemma windowRep_mem (p : ℤ) (r : ZMod N) : windowRep N p r ∈ Finset.Ico p (p + N) := by
  have h : (r - (p : ZMod N)).val < N := ZMod.val_lt _
  simp only [windowRep, Finset.mem_Ico]
  omega

private lemma windowRep_cast (p : ℤ) (r : ZMod N) : ((windowRep N p r : ℤ) : ZMod N) = r := by
  simp only [windowRep]
  push_cast
  simp

/-- **Window lemma, indexing form.** The `N` consecutive integers `p, p+1, …, p+N-1`
represent the `N` residue classes mod `N` bijectively. -/
theorem window_residues_bijective (p : ℤ) :
    Function.Bijective (fun i : Fin N => ((p + i : ℤ) : ZMod N)) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp [ZMod.card]⟩
  intro i j hij
  simp only at hij
  push_cast at hij
  have h : ((i : ℕ) : ZMod N) = ((j : ℕ) : ZMod N) := by
    exact add_left_cancel hij
  have h' := congrArg ZMod.val h
  rw [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt] at h'
  exact Fin.ext h'

/-- **Window lemma, counting form.** Inside a window of `N` consecutive integers there is
exactly one integer in each residue class mod `N`. -/
theorem card_window_eq_one (p : ℤ) (r : ZMod N) :
    ((Finset.Ico p (p + N)).filter (fun k : ℤ => (k : ZMod N) = r)).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨windowRep N p r, ?_⟩
  have hNpos : (0 : ℤ) < N := by
    have := Nat.pos_of_neZero N
    exact_mod_cast this
  have hw := windowRep_mem N p r
  have hwc := windowRep_cast N p r
  rw [Finset.mem_Ico] at hw
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    -- `k` and `windowRep N p r` are congruent mod `N` and both lie in a window of width `N`.
    have hdvd : (N : ℤ) ∣ (k - windowRep N p r) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [h3, hwc, sub_self]
    have habs : |k - windowRep N p r| < (N : ℤ) := by
      rw [abs_lt]
      omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  · rintro rfl
    exact ⟨⟨hw.1, hw.2⟩, hwc⟩

end Window

end TworowD4Kernel
