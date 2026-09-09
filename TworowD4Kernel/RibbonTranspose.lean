/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.AbacusRibbon

/-!
# Transposition complements the ribbon window: `hgt(R) + hgt(Rᵀ) = e - 1`

This module formalises the combinatorial identity that **forces the exponent** in

  `ω Rₑ(t) ω = t^(e-1) Rₑ(1/t)`,

namely `Lemma lem:transpose` of `proofs/2026-09-09-Q104-hyperbola-as-fixed-point-set.tex`:
for a connected border strip `λ/μ` of size `e`,

  `hgt(λ/μ) + hgt(λ'/μ') = e - 1`.

The paper proves it by step-counting: reading the `e` cells of the strip from one end to
the other, each of the `e - 1` steps between consecutive cells is either a row-change or a
column-change; row-changes number `ρ - 1 = hgt(λ/μ)` and column-changes `γ - 1`, and
transposition exchanges rows with columns.

## What the identity *is*, on the abacus

Under the abacus dictionary of `TworowD4Kernel.AbacusRibbon`, a size-`e` ribbon added at a
bead `b` moves that bead from `b` to `b + e`, and

  `ribbonHeight e M b = #(M ∩ (b, b+e))`

counts the beads lying **strictly** between `b` and `b + e` — the row-changes. The
column-changes are then the *gaps*: the sites of the open window `(b, b+e)` that carry no
bead. So the paper's step-count is, on the abacus, the single statement

  `#(beads in window) + #(gaps in window) = #(window) = e - 1`,

and the `e - 1` of the exponent is literally the cardinality of the open window. That is
what this file proves. The bound `ribbonHeight_le_sub_one` of `AbacusRibbon` is then the
corollary: `e - 1` is not an artefact of estimation, it is a window size that transposition
*complements*.

## Convention audit (done, not assumed)

`ribbonHeight` is defined in `AbacusRibbon` as `(M.filter (fun x => b < x ∧ x < b + e)).card`
— the **open** window `Ioo b (b+e)`, which has `e - 1` sites, not the half-open `Ico b (b+e)`,
which has `e`. Both existing attainment theorems are consistent with the open reading
(`ribbonHeight_Ico = e - 1` on a window packed with `e` beads of which `e - 1` are interior;
`ribbonHeight_singleton = 0`, since `b` itself is not interior). `ribbonWindow` below is
therefore `Ioo`, and `card_ribbonWindow` records the count. The informal `2670`-pair check in
the source paper counts row-changes, i.e. interior beads, so it uses the same convention.

## Scope

This file formalises the **combinatorial identity that forces the exponent**. It does *not*
formalise `ω Rₑ(t) ω = t^(e-1) Rₑ(1/t)` itself, which needs the ring of symmetric functions
and the operator `Rₑ`. The transposed configuration is modelled *window-locally*
(`transposeConfig`): conjugating a partition reflects and complements the whole Maya diagram,
and the complement of a `Finset ℤ` is not a `Finset`, so the global involution is deliberately
not built here. `transposeConfig` reflects through the window's midpoint and exchanges beads
with gaps inside the window, leaving `M` untouched outside it — which is what conjugation does
to the window, and the window is all `ribbonHeight` reads.

## Main results

* `card_ribbonWindow` — the open window has exactly `e - 1` sites.
* `ribbonHeight_eq_card_inter` — `ribbonHeight` is window-intersection cardinality.
* `card_insert_ribbonWindow` — the open/half-open conventions differ by exactly the endpoint `b`.
* `ribbonHeight_transposeConfig` — the conjugate height is `e - 1 - hgt`.
* `ribbonHeight_add_ribbonHeight_transposeConfig` — **the target**: `hgt + hgtᵀ = e - 1`.
* `ribbonHeight_le_sub_one_of_transpose` — the `AbacusRibbon` bound, re-derived as a corollary.
* Non-vacuity at `e = 4` with `hgt = 2 ≠ 1 = hgtᵀ`, so the witness is *not* the self-conjugate
  fixed point, together with the ribbon side conditions for both configurations.
* Negative controls: dropping the complement (`ribbonHeight_reflect_not_transpose`) or using
  `M` itself (`ribbonHeight_self_not_complementary`) both break the identity.
-/

namespace TworowD4Kernel

open Finset

section Window

variable (e : ℕ) (b : ℤ)

/-- The open window of a size-`e` ribbon at `b`: the sites strictly between `b` and `b + e`.
These are exactly the sites `ribbonHeight` counts beads on. -/
def ribbonWindow (e : ℕ) (b : ℤ) : Finset ℤ := Finset.Ioo b (b + (e : ℤ))

@[simp]
theorem mem_ribbonWindow {x : ℤ} : x ∈ ribbonWindow e b ↔ b < x ∧ x < b + (e : ℤ) := by
  simp [ribbonWindow]

/-- The window has exactly `e - 1` sites. This is the `e - 1` of the exponent.

No `0 < e` hypothesis is needed: at `e = 0` the window is empty and `e - 1 = 0` in `ℕ`, so
both sides are `0`. The hypothesis is therefore **removable**, and is not carried; the
degenerate case is instead pinned by `ribbonWindow_zero` and excluded from the load-bearing
reading by the `e = 4` non-vacuity witnesses. -/
theorem card_ribbonWindow : (ribbonWindow e b).card = e - 1 := by
  rw [ribbonWindow, Int.card_Ioo]
  omega

/-- The degenerate case, named rather than hidden: at `e = 0` the window is empty, so the
main identity reads `0 + 0 = 0`. -/
theorem ribbonWindow_zero : ribbonWindow 0 b = ∅ := by
  ext x
  simp only [mem_ribbonWindow, Finset.notMem_empty, iff_false, Nat.cast_zero, add_zero]
  omega

/-- The window is nonempty exactly when there is a ribbon step to record, i.e. `2 ≤ e`. -/
theorem ribbonWindow_nonempty_iff : (ribbonWindow e b).Nonempty ↔ 2 ≤ e := by
  constructor
  · rintro ⟨x, hx⟩
    rw [mem_ribbonWindow] at hx
    omega
  · intro he
    exact ⟨b + 1, by rw [mem_ribbonWindow]; omega⟩

/-- The left endpoint `b` is **not** in the window: the window is open. -/
theorem notMem_ribbonWindow_left : b ∉ ribbonWindow e b := by
  simp only [mem_ribbonWindow]
  omega

/-- **The convention, stated as a theorem.** The half-open window `[b, b+e)` has `e` sites and
the open window `(b, b+e)` has `e - 1`; they differ by exactly the left endpoint `b`.

Here `0 < e` is genuinely **load-bearing**, unlike in `card_ribbonWindow`: at `e = 0` the left
side is `1` (the window is empty and `insert b ∅ = {b}`) while the right side is `0`. -/
theorem card_insert_ribbonWindow (he : 0 < e) : (insert b (ribbonWindow e b)).card = e := by
  rw [Finset.card_insert_of_notMem (notMem_ribbonWindow_left e b), card_ribbonWindow]
  omega

/-- `ribbonHeight` counts the beads of `M` inside the window. -/
theorem ribbonHeight_eq_card_inter (M : Finset ℤ) :
    ribbonHeight e M b = (M ∩ ribbonWindow e b).card := by
  unfold ribbonHeight
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_inter, mem_ribbonWindow]

end Window

section Reflect

variable (e : ℕ) (b : ℤ)

/-- Reflection through the midpoint of the window: `x ↦ 2b + e - x`. Conjugating a partition
reflects its Maya diagram, and this is that reflection restricted to the window at `b`. -/
def ribbonReflect (e : ℕ) (b : ℤ) (x : ℤ) : ℤ := 2 * b + (e : ℤ) - x

theorem ribbonReflect_involutive : Function.Involutive (ribbonReflect e b) := by
  intro x
  unfold ribbonReflect
  ring

theorem ribbonReflect_injective : Function.Injective (ribbonReflect e b) :=
  (ribbonReflect_involutive e b).injective

/-- The reflection maps the window onto itself: it is the endpoint-swapping symmetry of
`(b, b+e)`. -/
@[simp]
theorem ribbonReflect_mem_ribbonWindow {x : ℤ} :
    ribbonReflect e b x ∈ ribbonWindow e b ↔ x ∈ ribbonWindow e b := by
  simp only [mem_ribbonWindow, ribbonReflect]
  omega

/-- Reflecting the beads does not change how many of them lie in the window: the reflection
is an injection preserving the window. This is why the *complement*, not the reflection, is
the operative half of conjugation for the height statistic. -/
theorem card_image_ribbonReflect_inter (M : Finset ℤ) :
    ((M.image (ribbonReflect e b)) ∩ ribbonWindow e b).card = (M ∩ ribbonWindow e b).card := by
  have hset : (M.image (ribbonReflect e b)) ∩ ribbonWindow e b
      = (M ∩ ribbonWindow e b).image (ribbonReflect e b) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hw⟩
      exact ⟨y, ⟨hy, (ribbonReflect_mem_ribbonWindow e b).1 hw⟩, rfl⟩
    · rintro ⟨y, ⟨hy, hyw⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, (ribbonReflect_mem_ribbonWindow e b).2 hyw⟩
  rw [hset, Finset.card_image_of_injective _ (ribbonReflect_injective e b)]

end Reflect

section Transpose

variable (e : ℕ) (M : Finset ℤ) (b : ℤ)

/-- The window-local model of the conjugate configuration: inside the window, reflect the
beads through the midpoint and exchange beads with gaps; outside the window, leave `M`
untouched.

Cf. `lem:transpose` of `2026-09-09-Q104-hyperbola-as-fixed-point-set.tex`: on Young diagrams
conjugation exchanges rows with columns, which on the abacus window exchanges the row-changes
(beads) with the column-changes (gaps). -/
def transposeConfig (e : ℕ) (M : Finset ℤ) (b : ℤ) : Finset ℤ :=
  (ribbonWindow e b \ M.image (ribbonReflect e b)) ∪ (M \ ribbonWindow e b)

/-- `transposeConfig` agrees with `M` off the window: the model is local, as advertised. -/
theorem transposeConfig_sdiff_window :
    transposeConfig e M b \ ribbonWindow e b = M \ ribbonWindow e b := by
  ext x
  simp only [transposeConfig, Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- ... and on the window it is the reflected complement. -/
theorem transposeConfig_inter_window :
    transposeConfig e M b ∩ ribbonWindow e b
      = ribbonWindow e b \ M.image (ribbonReflect e b) := by
  ext x
  simp only [transposeConfig, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- The conjugate height counts the **gaps** of the window: the column-changes of the strip. -/
theorem ribbonHeight_transposeConfig_eq_card_sdiff :
    ribbonHeight e (transposeConfig e M b) b
      = (ribbonWindow e b \ M.image (ribbonReflect e b)).card := by
  rw [ribbonHeight_eq_card_inter, transposeConfig_inter_window]

/-- **The target.** Transposition complements occupancy inside the window:

  `hgt(R) + hgt(Rᵀ) = e - 1`.

This is `lem:transpose` of `proofs/2026-09-09-Q104-hyperbola-as-fixed-point-set.tex`, and it
is the reason the anomaly in `ω Rₑ(t) ω = t^(e-1) Rₑ(1/t)` is `t^(e-1)` rather than `t²` or a
root of unity: the exponent is the cardinality of the window that conjugation complements. -/
theorem ribbonHeight_add_ribbonHeight_transposeConfig :
    ribbonHeight e M b + ribbonHeight e (transposeConfig e M b) b = e - 1 := by
  have hsplit :
      (ribbonWindow e b \ M.image (ribbonReflect e b)).card
        + (ribbonWindow e b ∩ M.image (ribbonReflect e b)).card = (ribbonWindow e b).card :=
    Finset.card_sdiff_add_card_inter _ _
  have hcomm : (ribbonWindow e b ∩ M.image (ribbonReflect e b)).card
      = (M.image (ribbonReflect e b) ∩ ribbonWindow e b).card := by
    rw [Finset.inter_comm]
  rw [ribbonHeight_eq_card_inter, ribbonHeight_transposeConfig_eq_card_sdiff]
  rw [hcomm, card_image_ribbonReflect_inter] at hsplit
  rw [card_ribbonWindow] at hsplit
  omega

/-- The conjugate height in closed form. -/
theorem ribbonHeight_transposeConfig :
    ribbonHeight e (transposeConfig e M b) b = e - 1 - ribbonHeight e M b := by
  have := ribbonHeight_add_ribbonHeight_transposeConfig e M b
  omega

/-- `AbacusRibbon.ribbonHeight_le_sub_one`, re-derived as a **corollary** of the equality.
The bound was proved there by containment in the window; here it falls out of the
complementation, which is the point of the exercise — the bound is not an estimate, it is one
side of an exact split. -/
theorem ribbonHeight_le_sub_one_of_transpose : ribbonHeight e M b ≤ e - 1 := by
  have := ribbonHeight_add_ribbonHeight_transposeConfig e M b
  omega

/-- Conjugation is an involution *on the height*: applying `transposeConfig` twice returns the
original height. (Not that it returns the original configuration — it does not, off the
window `transposeConfig` is idempotent but inside it the reflection is applied to a set that
has already been complemented.) -/
theorem ribbonHeight_transposeConfig_transposeConfig :
    ribbonHeight e (transposeConfig e (transposeConfig e M b) b) b = ribbonHeight e M b := by
  have h1 := ribbonHeight_add_ribbonHeight_transposeConfig e M b
  have h2 := ribbonHeight_add_ribbonHeight_transposeConfig e (transposeConfig e M b) b
  omega

end Transpose

section NonVacuity

/-! ### Non-vacuity

The main theorem contains `e - 1` in `ℕ`, which is `0` at `e = 0`, and both heights are `0`
on an empty window. So a witness is required in which the window is genuinely occupied *and*
the two heights differ — otherwise the identity could be read as the fixed-point statement
`h + h = e - 1`, which it is not. The `e = 4` witness below has `hgt = 2` and `hgtᵀ = 1`. -/

/-- The window at `e = 4, b = 0` really is `{1,2,3}`, of cardinality `3 = e - 1`. -/
theorem ribbonWindow_four : ribbonWindow 4 (0 : ℤ) = {1, 2, 3} := by decide

/-- A genuinely occupied window: `M = {0,1,2}` has two interior beads. -/
theorem ribbonHeight_four_nonvacuous : ribbonHeight 4 ({0, 1, 2} : Finset ℤ) 0 = 2 := by decide

/-- The conjugate configuration, computed. -/
theorem transposeConfig_four : transposeConfig 4 ({0, 1, 2} : Finset ℤ) 0 = {1, 0} := by decide

/-- ... and its height is `1 ≠ 2`, so the witness is **not** the self-conjugate fixed point:
the identity is genuinely a complementation and not `h + h = e - 1`. -/
theorem ribbonHeight_transposeConfig_four :
    ribbonHeight 4 (transposeConfig 4 ({0, 1, 2} : Finset ℤ) 0) 0 = 1 := by decide

/-- The two heights differ. -/
theorem ribbonHeight_four_ne :
    ribbonHeight 4 ({0, 1, 2} : Finset ℤ) 0
      ≠ ribbonHeight 4 (transposeConfig 4 ({0, 1, 2} : Finset ℤ) 0) 0 := by decide

/-- The identity, instantiated: `2 + 1 = 3`. -/
theorem ribbonHeight_add_four :
    ribbonHeight 4 ({0, 1, 2} : Finset ℤ) 0
      + ribbonHeight 4 (transposeConfig 4 ({0, 1, 2} : Finset ℤ) 0) 0 = 3 := by decide

/-- The witness is a **legal ribbon**: `b ∈ M` and `b + e ∉ M`, so `addRibbon` applies to it
and `ribbonHeight` is reading the height of an actual ribbon move, not of an arbitrary set. -/
theorem ribbonHeight_four_sideConditions :
    (0 : ℤ) ∈ ({0, 1, 2} : Finset ℤ) ∧ (0 : ℤ) + (4 : ℤ) ∉ ({0, 1, 2} : Finset ℤ) := by decide

/-- The conjugate configuration is a legal ribbon too. -/
theorem transposeConfig_four_sideConditions :
    (0 : ℤ) ∈ transposeConfig 4 ({0, 1, 2} : Finset ℤ) 0 ∧
      (0 : ℤ) + (4 : ℤ) ∉ transposeConfig 4 ({0, 1, 2} : Finset ℤ) 0 := by decide

/-- Both extremes of the split are realised at `e = 4`: `hgtᵀ = 3` when `hgt = 0`. -/
theorem ribbonHeight_four_extreme :
    ribbonHeight 4 ({0} : Finset ℤ) 0 = 0 ∧
      ribbonHeight 4 (transposeConfig 4 ({0} : Finset ℤ) 0) 0 = 3 := by decide

end NonVacuity

section NegativeControl

/-! ### Negative controls

Each control is a *false* variant of the theorem, exhibited as a concrete disequality, so
that the operative hypotheses are shown to be load-bearing rather than decorative. -/

/-- **The complement is load-bearing.** Reflection alone does not conjugate the height:
`ribbonHeight` of the reflected bead set is the *same* as `ribbonHeight` of `M`
(`card_image_ribbonReflect_inter`), so replacing `transposeConfig` by the bare reflection
breaks the identity: `2 + 2 ≠ 3`. -/
theorem ribbonHeight_reflect_not_transpose :
    ribbonHeight 4 ({0, 1, 2} : Finset ℤ) 0
      + ribbonHeight 4 (({0, 1, 2} : Finset ℤ).image (ribbonReflect 4 0)) 0 ≠ 3 := by decide

/-- **The identity is not `h + h`.** Using `M` itself in the second slot fails. -/
theorem ribbonHeight_self_not_complementary :
    ribbonHeight 4 ({0, 1, 2} : Finset ℤ) 0 + ribbonHeight 4 ({0, 1, 2} : Finset ℤ) 0 ≠ 3 := by
  decide

/-- **The window is open, not half-open.** If `ribbonHeight` counted `Ico b (b+e)` the window
would have `e` sites and the sum would be `e`, not `e - 1`. At `e = 4, b = 0` the two
conventions are genuinely distinguishable: `3` sites against `4`, differing by the left
endpoint `0`. So the convention in force is pinned by computation, not assumed. -/
theorem ribbonWindow_ne_Ico :
    (ribbonWindow 4 (0 : ℤ)).card ≠ (Finset.Ico (0 : ℤ) 4).card := by decide

/-- The same control in a form the *compiler* can evaluate, so that `lake test` can shadow it
with a `#guard`. `Finset.Ico` on `ℤ` is noncomputable here (it drags in
`Int.instConditionallyCompleteLinearOrder`), so `#guard` on `ribbonWindow_ne_Ico` fails to
compile even though `decide` kernel-reduces it fine; `Finset.Ioo` and `insert` do not have
that problem. -/
theorem card_insert_ribbonWindow_four :
    (0 : ℤ) ∉ ribbonWindow 4 (0 : ℤ) ∧ (insert (0 : ℤ) (ribbonWindow 4 (0 : ℤ))).card = 4 := by
  decide

/-- **The bound is attained but not always.** `ribbonHeight_le_sub_one_of_transpose` is not
vacuous-by-saturation: there is a configuration strictly below the bound. -/
theorem ribbonHeight_lt_sub_one_witness : ribbonHeight 4 ({0, 1} : Finset ℤ) 0 < 4 - 1 := by
  decide

end NegativeControl

end TworowD4Kernel
