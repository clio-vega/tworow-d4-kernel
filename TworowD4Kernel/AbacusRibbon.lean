/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Adding and removing an `e`-ribbon on the abacus

This module fixes, as a type rather than as prose, the **direction** of the ribbon operators
of `proofs/2026-08-31-Q59-commutator-rigidity.tex`.

## Why this file exists

The Definition in that paper (`N_e^{(h)}` and `R_e(t) = ∑_h t^h N_e^{(h)}`) says that
`N_e^{(h)}` **adds** an `e`-ribbon of height `h`, and the reference implementation
`fock_ell.py::R_e` moves a bead `b ↦ b + e`. The DREAM note of 2026-09-03 recorded the
opposite gloss ("`N_e^{(h)}` removes") and read off `R_e(-1) = p_e^⊥`; the error survived a
full cycle while both primary sources were correct. Prose loses direction; a definition does
not.

## The mathematics being formalised

Bead sets are `Finset ℤ`, the same convention as `TworowD4Kernel.WindowBridge`. (A genuine
Maya set `M(λ) = {λ_j - j}` is cofinite in `ℤ_{<0}`, hence infinite; every statement below is
about the *local* combinatorics near the moved bead, which is insensitive to the tail, so a
`Finset` model is faithful for exactly these lemmas and not for statements about `|λ|`.)

Lemma `lem:dict`(iii) of the paper reads: the `e`-ribbons addable to `λ` are in bijection with
the `b ∈ M` such that `b + e ∉ M`; the resulting `μ` has `M(μ) = M \ {b} ∪ {b+e}`; the ribbon's
cells have contents `b+1, …, b+e`; and its height is `h = #(M ∩ (b, b+e))`. That is
`addRibbon` and `ribbonHeight` verbatim. This is the classical abacus dictionary, as used by
Uglov (`arXiv:math/9905196`) and Leclerc–Thibon (`arXiv:q-alg/9512031`).

## What is proved, and what the proofs turned out *not* to need

* `addRibbon_removeRibbon` / `removeRibbon_addRibbon` — mutually inverse on their domains.
  These need only the two side conditions, **not** `0 < e`.
* `addRibbon_notMem_self` — `b ∉ addRibbon e M b`. This one *does* need `0 < e`, and it is
  what makes the round trip a statement about removing a ribbon rather than a coincidence of
  `insert`/`erase`: at `e = 0` the "removal" of `addRibbon e M b` at `b + e` is not a legal
  removal at all.
* `sum_addRibbon` / `sum_removeRibbon` — the bead sum goes **up** by `e` on adding and **down**
  by `e` on removing. This is the direction statement with an orientation attached: it is the
  shadow of `|μ| = |λ| + e`, and it is the one lemma here that cannot be satisfied by the
  opposite convention.
* `ribbonHeight_addRibbon` — the height read back off the result equals the height read off the
  source. **No hypotheses at all are needed**: the beads strictly between `b` and `b + e` are
  untouched by the move, the inserted bead sits at the closed end and the erased bead at the
  other, so both fall outside the open window.
* `ribbonHeight_le_sub_one`, `ribbonHeight_lt` — the `t`-degree bound `deg_t R_e(t) ≤ e - 1`
  asserted by the paper. Again **no ribbon side conditions are needed**: this is pure window
  counting, `M ∩ (b, b+e) ⊆ Ioo b (b+e)` and `#Ioo b (b+e) = e - 1`. Recording that the
  hypotheses are inert is the point of formalising it.
* Attainment at both ends (`ribbonHeight_Ico`, `ribbonHeight_singleton`), for every `e`, with
  the side conditions checked — bounds are attained, not merely bounded.
* Non-vacuity witnesses for every hypothesis set, and one deliberate **negative**:
  `exists_addRibbon_not_removeRibbon_of_mem` shows the round trip genuinely fails when the side
  condition `b + e ∉ M` is dropped, so the inverse lemmas are not vacuously ranging over a
  trivial domain.
-/

namespace TworowD4Kernel

open Finset

/-- Add an `e`-ribbon at the bead `b`: move the bead from `b` to `b + e`.
Intended domain: `b ∈ M` and `b + e ∉ M` (paper `lem:dict`(iii)). -/
def addRibbon (e : ℕ) (M : Finset ℤ) (b : ℤ) : Finset ℤ := insert (b + e) (M.erase b)

/-- Remove an `e`-ribbon at the bead `c`: move the bead from `c` down to `c - e`.
Intended domain: `c ∈ M` and `c - e ∉ M`. -/
def removeRibbon (e : ℕ) (M : Finset ℤ) (c : ℤ) : Finset ℤ := insert (c - e) (M.erase c)

/-- The height (spin) of the `e`-ribbon added at `b`: the number of beads lying strictly
between `b` and `b + e`. Paper `lem:dict`(iii): `h = #(M ∩ (b, b+e))`. -/
def ribbonHeight (e : ℕ) (M : Finset ℤ) (b : ℤ) : ℕ :=
  (M.filter (fun x => b < x ∧ x < b + e)).card

section Membership

variable (e : ℕ) (M : Finset ℤ) (b : ℤ)

@[simp]
theorem mem_addRibbon {x : ℤ} : x ∈ addRibbon e M b ↔ x = b + e ∨ (x ≠ b ∧ x ∈ M) := by
  simp [addRibbon]

@[simp]
theorem mem_removeRibbon {x : ℤ} : x ∈ removeRibbon e M b ↔ x = b - e ∨ (x ≠ b ∧ x ∈ M) := by
  simp [removeRibbon]

/-- The bead really did move **up**: `b + e` is occupied after adding. -/
theorem addRibbon_mem_self : b + e ∈ addRibbon e M b := by simp

/-- ... and `b` is vacated. This is the statement that needs `0 < e`, and it is what makes
`removeRibbon e (addRibbon e M b) (b + e)` a *legal* removal rather than an accident. -/
theorem addRibbon_notMem_self (he : 0 < e) : b ∉ addRibbon e M b := by
  intro hmem
  rw [mem_addRibbon] at hmem
  rcases hmem with h | ⟨h, -⟩
  · omega
  · exact h rfl

end Membership

section Inverse

variable {e : ℕ} {M : Finset ℤ} {b c : ℤ}

/-- Removing the ribbon just added returns the original bead set.
No positivity hypothesis is needed; see `addRibbon_notMem_self` for where `0 < e` does enter. -/
theorem addRibbon_removeRibbon (hb : b ∈ M) (hbe : b + e ∉ M) :
    removeRibbon e (addRibbon e M b) (b + e) = M := by
  have hne : b + (e : ℤ) ∉ M.erase b := fun h => hbe (mem_of_mem_erase h)
  have hsub : b + (e : ℤ) - e = b := by ring
  rw [removeRibbon, addRibbon, erase_insert hne, hsub, insert_erase hb]

/-- Adding back the ribbon just removed returns the original bead set. -/
theorem removeRibbon_addRibbon (hc : c ∈ M) (hce : c - e ∉ M) :
    addRibbon e (removeRibbon e M c) (c - e) = M := by
  have hne : c - (e : ℤ) ∉ M.erase c := fun h => hce (mem_of_mem_erase h)
  have hadd : c - (e : ℤ) + e = c := by ring
  rw [addRibbon, removeRibbon, erase_insert hne, hadd, insert_erase hc]

end Inverse

section Sum

variable {e : ℕ} {M : Finset ℤ} {b c : ℤ}

/-- Adding an `e`-ribbon raises the bead sum by exactly `e`. This is the orientation of the
operator: the abacus shadow of `|μ| = |λ| + e`. The opposite convention would give `- e`. -/
theorem sum_addRibbon (hb : b ∈ M) (hbe : b + e ∉ M) :
    ∑ x ∈ addRibbon e M b, x = (∑ x ∈ M, x) + e := by
  have hne : b + (e : ℤ) ∉ M.erase b := fun h => hbe (mem_of_mem_erase h)
  have herase : ∑ x ∈ M.erase b, x = (∑ x ∈ M, x) - b :=
    eq_sub_of_add_eq (Finset.sum_erase_add M _ hb)
  rw [addRibbon, Finset.sum_insert hne, herase]
  ring

/-- Removing an `e`-ribbon lowers the bead sum by exactly `e`. -/
theorem sum_removeRibbon (hc : c ∈ M) (hce : c - e ∉ M) :
    ∑ x ∈ removeRibbon e M c, x = (∑ x ∈ M, x) - e := by
  have hne : c - (e : ℤ) ∉ M.erase c := fun h => hce (mem_of_mem_erase h)
  have herase : ∑ x ∈ M.erase c, x = (∑ x ∈ M, x) - c :=
    eq_sub_of_add_eq (Finset.sum_erase_add M _ hc)
  rw [removeRibbon, Finset.sum_insert hne, herase]
  ring

end Sum

section Height

variable (e : ℕ) (M : Finset ℤ) (b : ℤ)

/-- The height of the added ribbon, read back off the result, is the height read off the
source. Unconditional: the beads strictly between `b` and `b + e` are exactly the ones the
move does not touch. -/
theorem ribbonHeight_addRibbon : ribbonHeight e (addRibbon e M b) b = ribbonHeight e M b := by
  unfold ribbonHeight
  congr 1
  ext x
  simp only [mem_filter, mem_addRibbon, ne_eq]
  constructor
  · rintro ⟨hx | ⟨-, hm⟩, h1, h2⟩
    · exact absurd (hx ▸ h2) (lt_irrefl _)
    · exact ⟨hm, h1, h2⟩
  · rintro ⟨hm, h1, h2⟩
    exact ⟨Or.inr ⟨fun hxb => absurd (hxb ▸ h1) (lt_irrefl _), hm⟩, h1, h2⟩

/-- `deg_t R_e(t) ≤ e - 1`: the ribbon height never exceeds `e - 1`.
The ribbon side conditions `b ∈ M`, `b + e ∉ M` are **not** used — this is window counting. -/
theorem ribbonHeight_le_sub_one : ribbonHeight e M b ≤ e - 1 := by
  have hsub : M.filter (fun x => b < x ∧ x < b + e) ⊆ Finset.Ioo b (b + (e : ℤ)) := by
    intro x hx
    exact Finset.mem_Ioo.2 (mem_filter.1 hx).2
  have hcard := Finset.card_le_card hsub
  rw [Int.card_Ioo] at hcard
  unfold ribbonHeight
  omega

/-- The strict form of the degree bound, as the paper states it. -/
theorem ribbonHeight_lt (he : 0 < e) : ribbonHeight e M b < e := by
  have := ribbonHeight_le_sub_one e M b
  omega

end Height

section Attainment

variable (e : ℕ) (b : ℤ)

/-- The upper bound `e - 1` is **attained**: pack the whole window `[b, b+e)` with beads. -/
theorem ribbonHeight_Ico : ribbonHeight e (Finset.Ico b (b + (e : ℤ))) b = e - 1 := by
  have hfil : (Finset.Ico b (b + (e : ℤ))).filter (fun x => b < x ∧ x < b + e)
      = Finset.Ioo b (b + (e : ℤ)) := by
    ext x
    simp only [mem_filter, Finset.mem_Ico, Finset.mem_Ioo]
    omega
  unfold ribbonHeight
  rw [hfil, Int.card_Ioo]
  omega

/-- Side conditions for the maximal witness, so it is a genuine ribbon. -/
theorem ribbonHeight_Ico_sideConditions (he : 0 < e) :
    b ∈ Finset.Ico b (b + (e : ℤ)) ∧ b + (e : ℤ) ∉ Finset.Ico b (b + (e : ℤ)) := by
  constructor
  · simp only [Finset.mem_Ico]; omega
  · simp only [Finset.mem_Ico]; omega

/-- The lower bound `0` is attained: a lone bead has no beads above it in the window. -/
theorem ribbonHeight_singleton : ribbonHeight e ({b} : Finset ℤ) b = 0 := by
  unfold ribbonHeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro x hx
  rw [Finset.mem_singleton] at hx
  omega

/-- Side conditions for the minimal witness. -/
theorem ribbonHeight_singleton_sideConditions (he : 0 < e) :
    b ∈ ({b} : Finset ℤ) ∧ b + (e : ℤ) ∉ ({b} : Finset ℤ) := by
  refine ⟨Finset.mem_singleton_self b, ?_⟩
  simp only [Finset.mem_singleton]
  omega

end Attainment

section NonVacuity

/-- Non-vacuity for the inverse lemmas: a concrete `e`, `M`, `b` satisfying **both** side
conditions, on which the round trip is an equality of nonempty bead sets. -/
theorem addRibbon_removeRibbon_nonvacuous :
    (0 : ℤ) ∈ ({0, 1} : Finset ℤ) ∧ (0 : ℤ) + (3 : ℕ) ∉ ({0, 1} : Finset ℤ) ∧
      removeRibbon 3 (addRibbon 3 ({0, 1} : Finset ℤ) 0) (0 + (3 : ℕ)) = ({0, 1} : Finset ℤ) := by
  refine ⟨by decide, by decide, addRibbon_removeRibbon (by decide) (by decide)⟩

/-- Non-vacuity for the height lemmas at an intermediate value: not `0`, not `e - 1`.
Here `e = 3`, `M = {0, 2}`, `b = 0`: the single bead at `2` lies in the window `(0,3)`. -/
theorem ribbonHeight_nonvacuous :
    (0 : ℤ) ∈ ({0, 2} : Finset ℤ) ∧ (0 : ℤ) + (3 : ℕ) ∉ ({0, 2} : Finset ℤ) ∧
      ribbonHeight 3 ({0, 2} : Finset ℤ) 0 = 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Non-vacuity for the maximal-height witness, instantiated: `e = 3` gives height `2`. -/
theorem ribbonHeight_Ico_nonvacuous : ribbonHeight 3 (Finset.Ico (0 : ℤ) 3) 0 = 2 := by
  have := ribbonHeight_Ico 3 (0 : ℤ)
  norm_num at this ⊢
  exact this

/-- Non-vacuity for `sum_addRibbon`: the bead sum of `{0,1}` is `1`, and after adding the
`3`-ribbon at `0` it is `4`. Direction, with a number attached. -/
theorem sum_addRibbon_nonvacuous :
    ∑ x ∈ addRibbon 3 ({0, 1} : Finset ℤ) 0, x = (∑ x ∈ ({0, 1} : Finset ℤ), x) + 3 := by
  have := sum_addRibbon (e := 3) (M := ({0, 1} : Finset ℤ)) (b := 0) (by decide) (by decide)
  norm_num at this ⊢
  exact this

end NonVacuity

section NegativeControl

/-- **Deliberate negative.** Drop the side condition `b + e ∉ M` and the round trip fails:
with `e = 2`, `M = {0, 2}`, `b = 0` the bead at `0` is moved onto the occupied site `2`, the
two beads collide, and the removal cannot undo the collision. So `addRibbon_removeRibbon` is
not true of the larger domain, and its hypothesis `hbe` is doing work. -/
theorem exists_addRibbon_not_removeRibbon_of_mem :
    ∃ (e : ℕ) (M : Finset ℤ) (b : ℤ), 0 < e ∧ b ∈ M ∧ b + (e : ℤ) ∈ M ∧
      removeRibbon e (addRibbon e M b) (b + (e : ℤ)) ≠ M :=
  ⟨2, ({0, 2} : Finset ℤ), 0, by omega, by decide, by decide, by decide⟩

/-- The same failure, with the two sides exhibited explicitly rather than as a `≠`. -/
theorem addRibbon_collision :
    removeRibbon 2 (addRibbon 2 ({0, 2} : Finset ℤ) 0) (0 + (2 : ℕ)) = ({0} : Finset ℤ) := by
  decide

end NegativeControl

end TworowD4Kernel
