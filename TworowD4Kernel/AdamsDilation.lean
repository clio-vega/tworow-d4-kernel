/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.RibbonTranspose

/-!
# The abacus shadow of the Adams intertwiner: dilation multiplies SIZE, fixes HEIGHT

## What this file formalises, and what it does not

The paper result is `proofs/2026-09-09-c2-Q130-divisor-ladder-is-an-intertwiner.tex`,
Theorem `thm:intertwine` and Proposition `prop:descent`:
`R_{de}(-1) ∘ ψ^e = ψ^e ∘ R_d(-1)`, where `ψ^e : p_m ↦ p_{em}` is the `e`-th Adams
operation on symmetric functions.

**The Adams operation `ψ^e` itself is NOT formalised here.** There is no `Sym` in this
development, no power sums and no plethysm. What *is* formalised is the operation `ψ^e`
induces on the abacus — the `e`-fold **dilation of a runner**, `x ↦ e * x + r` — and the
two combinatorial facts about ribbon moves that carry the whole content of the theorem.
Everything below is a statement about `Finset ℤ`; the bridge from `ψ^e` to `dilate` is the
classical `e`-quotient/`e`-core dictionary and is taken on paper, not here.

## The sentence being machine-checked

**`ψ^e` divides ribbon SIZE, not ribbon COUNT.** Under the dilation:

* a `d`-ribbon upstairs becomes a single `(d * e)`-ribbon downstairs
  (`image_dilate_addRibbon`) — the size is multiplied, and it is still *one* ribbon;
* its height is **unchanged** (`ribbonHeight_image_dilate`) — the window
  `(eb+r, eb+r+de)` meets the dilated set exactly in the dilates of `M ∩ (b, b+d)`.

Since the sign that `R_e(-1)` reads off a ribbon is `(-1)^hgt` and nothing else
(`AbacusRibbon.ribbonHeight`, paper `lem:dict`(iii)), the second fact says the intertwiner
is **sign-preserving** while the first says the size multiplies. That is the exact shape of
the Q130 refutation: a *vector* exponent (the `e` in `ψ^e`, which rescales sizes) was reused
as an *operator composition count* (an `e`-fold product `R_d(-1)^e`, which would multiply
signs). The two are different, and the difference is invisible in prose.

## The dictionary

`AbacusRibbon` fixes the convention: `addRibbon d M b = insert (b+d) (M.erase b)` moves a
bead **up** by `d`, and `ribbonHeight d M b = #(M ∩ (b, b+d))` counts the beads strictly
inside the open window. This is the classical abacus dictionary as used by Uglov
(`arXiv:math/9905196`, §4) and Leclerc-Thibon (`arXiv:q-alg/9512031`, §3); the paper's
`lem:dict`(iii) is the statement being used.

## The pin test, run per statement

`0 < e` is **load-bearing for both** statements here, and this is checked rather than
assumed — `dilate_zero_not_height_preserving` exhibits an explicit `e = 0` counterexample to
the height claim (height `2` upstairs against `0` downstairs). That is *not* the pattern of
`AbacusRibbon`, where `ribbonHeight_le_sub_one` needs no hypothesis at all and only
`addRibbon_notMem_self` needs `0 < e`.
-/

namespace TworowD4Kernel

open Finset

namespace AdamsDilation

/-- The `e`-fold dilation of the runner with residue `r`: the map the Adams operation
`ψ^e : p_m ↦ p_{em}` induces on the abacus. A bead at `x` is sent to `e * x + r`. -/
def dilate (e : ℕ) (r : ℤ) (x : ℤ) : ℤ := (e : ℤ) * x + r

@[simp]
theorem dilate_apply (e : ℕ) (r x : ℤ) : dilate e r x = (e : ℤ) * x + r := rfl

section Injectivity

variable {e : ℕ} (r : ℤ)

/-- Dilation is injective as soon as `e ≠ 0`. This is what lets `Finset.image` commute with
`erase`, and it is the only place `e ≠ 0` is used in `image_dilate_addRibbon`. -/
theorem dilate_injective (he : e ≠ 0) : Function.Injective (dilate e r) := by
  intro x y hxy
  simp only [dilate_apply, add_left_inj] at hxy
  exact mul_left_cancel₀ (by exact_mod_cast he) hxy

end Injectivity

section Ribbon

variable (e : ℕ) (r : ℤ) (d : ℕ) (M : Finset ℤ) (b : ℤ)

/-- The dilate of the far end of a `d`-ribbon is the far end of a `(d * e)`-ribbon. This one
line is where the **size multiplication** happens: `e * (b + d) + r = (e * b + r) + d * e`. -/
theorem dilate_add (e : ℕ) (r : ℤ) (d : ℕ) (b : ℤ) :
    dilate e r (b + (d : ℤ)) = dilate e r b + ((d * e : ℕ) : ℤ) := by
  simp only [dilate_apply]
  push_cast
  ring

/-- **Statement 1: dilation intertwines the ribbon move.**
A `d`-ribbon added at `b` upstairs becomes a single `(d * e)`-ribbon added at `dilate e r b`
downstairs. Note the right-hand side is `addRibbon (d * e)` — *one* ribbon of `e` times the
size, not `e` ribbons.

Requires `e ≠ 0`, purely for injectivity of `dilate` (`Finset.image_erase`). -/
theorem image_dilate_addRibbon (he : e ≠ 0) :
    (addRibbon d M b).image (dilate e r)
      = addRibbon (d * e) (M.image (dilate e r)) (dilate e r b) := by
  simp only [addRibbon, Finset.image_insert, Finset.image_erase (dilate_injective r he),
    dilate_add]

/-- The window downstairs meets the dilated set exactly in the dilates of the window
upstairs. This is the load-bearing computation: `e*b+r < e*x+r < e*b+r+d*e` is equivalent to
`b < x < b + d` once `e > 0`, so no bead enters or leaves the window under dilation. -/
theorem dilate_mem_ribbonWindow (he : 0 < e) (x : ℤ) :
    dilate e r x ∈ ribbonWindow (d * e) (dilate e r b) ↔ x ∈ ribbonWindow d b := by
  have he' : (0 : ℤ) < (e : ℤ) := by exact_mod_cast he
  have key : ∀ u v : ℤ, ((e : ℤ) * u + r < (e : ℤ) * v + r) ↔ u < v := by
    intro u v
    rw [add_lt_add_iff_right]
    exact Int.mul_lt_mul_left he'
  rw [mem_ribbonWindow, mem_ribbonWindow, ← dilate_add]
  simp only [dilate_apply]
  exact and_congr (key b x) (key x (b + (d : ℤ)))

/-- The set-level form of the previous lemma. -/
theorem image_dilate_inter_ribbonWindow (he : 0 < e) :
    (M.image (dilate e r)) ∩ ribbonWindow (d * e) (dilate e r b)
      = (M ∩ ribbonWindow d b).image (dilate e r) := by
  ext y
  simp only [Finset.mem_inter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (dilate_mem_ribbonWindow e r d b he x).mp hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hw⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (dilate_mem_ribbonWindow e r d b he x).mpr hw⟩

/-- **Statement 2: dilation preserves the height.**
The `(d * e)`-ribbon downstairs has exactly the height of the `d`-ribbon upstairs.
**Size scales, height does not.**

Routed through `ribbonHeight_eq_card_inter`, so this is a cardinality-of-image argument
under an injection, not an induction. `0 < e` is genuinely load-bearing here — see
`dilate_zero_not_height_preserving`. -/
theorem ribbonHeight_image_dilate (he : 0 < e) :
    ribbonHeight (d * e) (M.image (dilate e r)) (dilate e r b) = ribbonHeight d M b := by
  rw [ribbonHeight_eq_card_inter, ribbonHeight_eq_card_inter,
    image_dilate_inter_ribbonWindow e r d M b he,
    Finset.card_image_of_injective _ (dilate_injective r he.ne')]

/-- **Statement 3, the refutation as a corollary.** The sign that `R_e(-1)` reads off a
ribbon is `(-1)^hgt`. Statement 2 therefore says the intertwiner is **sign-preserving**,
while statement 1 says the ribbon size is multiplied by `e`. Powers multiply multiplicities;
conjugations reindex sizes — and `ψ^e` is the second kind of thing. -/
theorem sign_ribbonHeight_image_dilate (he : 0 < e) :
    (-1 : ℤ) ^ (ribbonHeight (d * e) (M.image (dilate e r)) (dilate e r b))
      = (-1 : ℤ) ^ (ribbonHeight d M b) := by
  rw [ribbonHeight_image_dilate e r d M b he]

end Ribbon

section NonVacuity

/-! ### Non-vacuity — separating the theorem from its degenerate slices

The motivating case `d = 1, e = 2` (boxes ↦ dominoes) is **degenerate for the height**:
`ribbonHeight 1 M b = 0` for every `M` and `b`, since the window `Ioo b (b+1)` is empty. A
witness at `d = 1` therefore says nothing at all about statement 2 — it would confirm
`0 = 0`. Every witness below has `d ≥ 3`. -/

/-- The `d = 1` slice really is blind: the height is `0` on both sides whatever `M` is, so
`ribbonHeight_image_dilate` at `d = 1` is the identity `0 = 0`. Recorded so that the
witnesses that follow are visibly *not* of this kind. -/
theorem ribbonHeight_one_degenerate (M : Finset ℤ) (b : ℤ) : ribbonHeight 1 M b = 0 := by
  have hw : Finset.Ioo b (b + 1) = (∅ : Finset ℤ) := by
    ext x
    simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false, not_and, not_lt]
    omega
  simp only [ribbonHeight_eq_card_inter, ribbonWindow, Nat.cast_one, hw, Finset.inter_empty,
    Finset.card_empty]

/-- The primary witness, `d = 3`, `e = 2`, `r = 0`, `M = {0,1,2}`, `b = 0`: the dilated bead
set is `{0,2,4}`. -/
theorem image_dilate_three_two : ({0, 1, 2} : Finset ℤ).image (dilate 2 0) = {0, 2, 4} := by
  decide

/-- Upstairs: a `3`-ribbon of height `2`, with **both side conditions** holding, so this is a
legal ribbon move and not an arbitrary bead set. -/
theorem witness_upstairs :
    ribbonHeight 3 ({0, 1, 2} : Finset ℤ) 0 = 2 ∧
      (0 : ℤ) ∈ ({0, 1, 2} : Finset ℤ) ∧ (0 : ℤ) + (3 : ℤ) ∉ ({0, 1, 2} : Finset ℤ) := by
  decide

/-- Downstairs: a ribbon of size `6 = 3 * 2` — the size really did multiply — whose height is
**still `2`**, again with both side conditions holding. -/
theorem witness_downstairs :
    ribbonHeight 6 (({0, 1, 2} : Finset ℤ).image (dilate 2 0)) (dilate 2 0 0) = 2 ∧
      dilate 2 0 0 ∈ ({0, 1, 2} : Finset ℤ).image (dilate 2 0) ∧
      dilate 2 0 0 + (6 : ℤ) ∉ ({0, 1, 2} : Finset ℤ).image (dilate 2 0) := by
  decide

/-- Statement 1, instantiated and computed: the dilate of the `3`-ribbon move is the single
`6`-ribbon move. -/
theorem witness_addRibbon :
    (addRibbon 3 ({0, 1, 2} : Finset ℤ) 0).image (dilate 2 0)
      = addRibbon 6 (({0, 1, 2} : Finset ℤ).image (dilate 2 0)) (dilate 2 0 0) := by
  decide

/-- A second witness whose height is **strictly between** the two extremes `0` and `d - 1`,
so neither endpoint of `ribbonHeight_le_sub_one` is doing the work: `d = 4`, `e = 3`,
`M = {0,1}`, height `1`, and `0 < 1 < 3`. -/
theorem witness_strictly_interior :
    ribbonHeight 4 ({0, 1} : Finset ℤ) 0 = 1 ∧
      ribbonHeight 12 (({0, 1} : Finset ℤ).image (dilate 3 0)) (dilate 3 0 0) = 1 ∧
      0 < ribbonHeight 4 ({0, 1} : Finset ℤ) 0 ∧
      ribbonHeight 4 ({0, 1} : Finset ℤ) 0 < 4 - 1 := by
  decide

end NonVacuity

section PinTest

/-! ### The pin test, run per statement

`AbacusRibbon` records that `0 < e` is *inert* for `ribbonHeight_le_sub_one` and
*load-bearing* for `addRibbon_notMem_self`. The same question has to be asked again here,
separately for each statement, rather than inherited
(→ `a-fixed-parameter-can-be-the-whole-obstruction`). The answer: **load-bearing for both.**
For statement 1 it is injectivity of `dilate`; for statement 2 it is exhibited below. -/

/-- **`0 < e` is load-bearing for statement 2.** At `e = 0` the map `dilate 0 r` is the
constant `r`, the image collapses to a single bead, and the window `Ioo r (r + 0)` is empty —
so the height reads `0` downstairs against `2` upstairs. Statement 2 is therefore false
without the hypothesis, not merely unproved. -/
theorem dilate_zero_not_height_preserving :
    ribbonHeight (3 * 0) (({0, 1, 2} : Finset ℤ).image (dilate 0 0)) (dilate 0 0 0)
      ≠ ribbonHeight 3 ({0, 1, 2} : Finset ℤ) 0 := by
  decide

end PinTest

section NegativeControl

/-! ### Negative controls — each must *move* a prediction

A control that cancels identically invalidates itself, not the claim
(→ `a-negative-control-must-move-a-prediction`). Each control below is a concrete
disequality. -/

/-- **Statement 2 is a fact about dilation, not a triviality of the window.** Take the *same*
downstairs window — size `12` at base `0` — but a bead set `{0,3,4}` that is **not** a
dilated image (`4` is not `3 * x`). The height is `2`, against `1` for the dilated set
`{0,3}`. So the window alone does not force the height; the dilation does. -/
theorem not_dilated_height_differs :
    ribbonHeight 12 (({0, 3, 4} : Finset ℤ)) 0
      ≠ ribbonHeight 12 (({0, 1} : Finset ℤ).image (dilate 3 0)) (dilate 3 0 0) := by
  decide

/-- **The size genuinely multiplies.** Reading the dilated configuration with the *original*
ribbon size `3` instead of `3 * 2 = 6` gives the wrong height, so `addRibbon (d * e)` in
statement 1 cannot be weakened to `addRibbon d`. -/
theorem size_must_multiply :
    ribbonHeight 3 (({0, 1, 2} : Finset ℤ).image (dilate 2 0)) (dilate 2 0 0)
      ≠ ribbonHeight 3 ({0, 1, 2} : Finset ℤ) 0 := by
  decide

/-! #### `R_4` is not `R_2^2`: size against count

This is the error the whole file exists to pin. `ψ^2` turns one `2`-ribbon into one
`4`-ribbon — that is `image_dilate_addRibbon`, *one* ribbon whose size doubled. The operator
`R_2(-1)^2` is a different thing: it is a *composition*, and it reaches configurations in
which **two different beads** each moved by `2`. Those configurations are not `4`-ribbon
moves at all.

Witness: `M = {0,5}`. Moving the bead `0 ↦ 2` and then the bead `5 ↦ 7` reaches `{2,7}`,
which has the same total displacement `4` as a single `4`-ribbon move but is not equal to
either of the two `4`-ribbon moves available on `M`. -/

/-- Two dominoes at two *different* beads reach `{2,7}`. -/
theorem two_dominoes_two_beads :
    addRibbon 2 (addRibbon 2 ({0, 5} : Finset ℤ) 0) 5 = {2, 7} := by decide

/-- ... and `{2,7}` is not reachable by any single `4`-ribbon move on `{0,5}`. There are
exactly two beads to move, and neither gives `{2,7}`. So `R_4` and `R_2^2` differ already at
the level of which bead sets they reach: **powers multiply multiplicities, conjugations
reindex sizes.** -/
theorem four_ribbon_ne_two_dominoes :
    addRibbon 4 ({0, 5} : Finset ℤ) 0 ≠ ({2, 7} : Finset ℤ) ∧
      addRibbon 4 ({0, 5} : Finset ℤ) 5 ≠ ({2, 7} : Finset ℤ) := by
  decide

end NegativeControl

end AdamsDilation

end TworowD4Kernel
