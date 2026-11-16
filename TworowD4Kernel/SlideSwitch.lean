/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Prod.Basic
import TworowD4Kernel.GrowthConfluence

/-!
# Elementary switches on chains of Young diagrams (G4 Lemma D, half (i), tiers A/B)

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D`, the paragraph
"A configuration in either procedure is a word … together with a saturated chain …" and the
italic claim "A forward slide of `F` into the cell of `U_i` is the product of the elementary
switches carrying `U_i` rightward past `F_1, …, F_p` in this order."

## Representation (the documented choice)

A cell is `(r, c) : ℕ × ℕ`. A **diagram** is a `Finset (ℕ × ℕ)` closed under the two immediate
predecessors `(r-1, c)` and `(r, c-1)` (`IsDiag`); this is the lower-set condition stated
locally, so that it is decidable by `Finset` bounded quantification. The outward neighbours of a
cell `h` are `(h.1, h.2+1)` ("east") and `(h.1+1, h.2)` ("north", French convention, as in the
tex where the cells outside the current diagram adjacent to the hole are its east/north ones).

## The switch rule

`switchL a b c` is the tex's "other partition strictly between `η_{t-1}` and `η_{t+1}` if one
exists, else keep `η_t`". It is defined on *all* triples so that it is an involution in its
middle slot **unconditionally** (`switchL_invol`), which is exactly the hypothesis of
`GrowthConfluence.good_unflip`. On a saturated triple it is the tex's rule (`other_unique`).

## Status

* Tier A (A1 `switchL_saturated`, A2 `switchL_invol`, A3 `other_unique`): proved.
* Tier B: `slideCheck N` compares an independently defined jdt forward slide ("smaller of east
  and north") with the switch product on every standard filling of every skew shape with
  `|ν| ≤ N`. It is run by `#guard` in `TworowD4KernelTests.lean`; **`#guard` is evaluation, not
  proof**, and nothing in this file claims the general statement (tier C).
-/

namespace TworowD4Kernel.SlideSwitch

/-- A cell `(row, column)`. -/
abbrev Cell := ℕ × ℕ

/-- Diagram (lower set in `ℕ × ℕ`), stated via the two immediate predecessors. -/
def IsDiag (s : Finset Cell) : Prop :=
  ∀ x ∈ s, (x.1 = 0 ∨ (x.1 - 1, x.2) ∈ s) ∧ (x.2 = 0 ∨ (x.1, x.2 - 1) ∈ s)

instance : DecidablePred IsDiag := fun s => by unfold IsDiag; infer_instance

/-- The candidate "other" middle term: `a ∪ (c \ b)`. -/
def other (a b c : Finset Cell) : Finset Cell := a ∪ (c \ b)

/-- The elementary-switch local rule: replace `b` by the other diagram between `a` and `c`
when that is a diagram (and the triple is a chain), otherwise keep `b`. -/
def switchL (a b c : Finset Cell) : Finset Cell :=
  if a ⊆ b ∧ b ⊆ c ∧ IsDiag b ∧ IsDiag (other a b c) then other a b c else b

lemma other_other {a b c : Finset Cell} (hab : a ⊆ b) (hbc : b ⊆ c) :
    other a (other a b c) c = b := by
  ext x
  have h1 := @hab x
  have h2 := @hbc x
  simp only [other, Finset.mem_union, Finset.mem_sdiff]
  tauto

lemma other_subset_left {a b c : Finset Cell} : a ⊆ other a b c := Finset.subset_union_left

lemma other_subset_right {a b c : Finset Cell} (hab : a ⊆ b) (hbc : b ⊆ c) :
    other a b c ⊆ c := by
  intro x hx
  simp only [other, Finset.mem_union, Finset.mem_sdiff] at hx
  rcases hx with hx | hx
  · exact hbc (hab hx)
  · exact hx.1

/-- **(A2)** The switch rule is an involution in its middle slot, for *every* triple. This is
the hypothesis `hL` of `GrowthConfluence.good_unflip`. -/
theorem switchL_invol (a b c : Finset Cell) : switchL a (switchL a b c) c = b := by
  by_cases h : a ⊆ b ∧ b ⊆ c ∧ IsDiag b ∧ IsDiag (other a b c)
  · obtain ⟨hab, hbc, hb, ho⟩ := h
    have e : switchL a b c = other a b c := if_pos ⟨hab, hbc, hb, ho⟩
    rw [e]
    unfold switchL
    rw [if_pos ⟨other_subset_left, other_subset_right hab hbc, ho, by rwa [other_other hab hbc]⟩,
      other_other hab hbc]
  · have e : switchL a b c = b := if_neg h
    rw [e, e]

/-- Half (ii) applies to the switch rule with backward moves allowed: the instance of
`good_unflip` for `switchL`. -/
theorem good_unflip_switchL (p : ℕ) (g : ℕ → Finset Cell)
    {s s' : List GrowthConfluence.Dir × (ℕ → Finset Cell)}
    (hs : GrowthConfluence.Good switchL p g s) (h : GrowthConfluence.Unflip switchL s s') :
    GrowthConfluence.Good switchL p g s' :=
  GrowthConfluence.good_unflip switchL switchL_invol p g hs h

/-- A saturated step: `a ⊆ b`, exactly one new cell, both diagrams. -/
def SatStep (a b : Finset Cell) : Prop := a ⊆ b ∧ (b \ a).card = 1 ∧ IsDiag a ∧ IsDiag b

lemma other_sdiff_left {a b c : Finset Cell} (hab : a ⊆ b) :
    other a b c \ a = c \ b := by
  ext x
  have h1 := @hab x
  simp only [other, Finset.mem_union, Finset.mem_sdiff]
  tauto

lemma sdiff_other {a b c : Finset Cell} (hab : a ⊆ b) (hbc : b ⊆ c) :
    c \ other a b c = b \ a := by
  ext x
  have h1 := @hab x
  have h2 := @hbc x
  simp only [other, Finset.mem_union, Finset.mem_sdiff]
  tauto

/-- **(A1)** The switch preserves saturation of the triple `a ⊂ b ⊂ c`. -/
theorem switchL_saturated {a b c : Finset Cell} (h1 : SatStep a b) (h2 : SatStep b c) :
    SatStep a (switchL a b c) ∧ SatStep (switchL a b c) c := by
  unfold switchL
  split_ifs with h
  · obtain ⟨hab, hbc, -, ho⟩ := h
    refine ⟨⟨other_subset_left, ?_, h1.2.2.1, ho⟩, ⟨other_subset_right hab hbc, ?_, ho, h2.2.2.2⟩⟩
    · rw [other_sdiff_left hab]; exact h2.2.1
    · rw [sdiff_other hab hbc]; exact h1.2.1
  · exact ⟨h1, h2⟩

/-- **(A1, chain form)** Updating position `t+1` of a chain by the switch rule keeps every
step saturated. `η t ⊂ η (t+1) ⊂ η (t+2)` is the triple the switch reads. -/
theorem switch_chain_saturated (η : ℕ → Finset Cell) (n t : ℕ) (ht : t + 2 ≤ n)
    (hη : ∀ k < n, SatStep (η k) (η (k + 1))) :
    ∀ k < n, SatStep (Function.update η (t + 1) (switchL (η t) (η (t + 1)) (η (t + 2))) k)
      (Function.update η (t + 1) (switchL (η t) (η (t + 1)) (η (t + 2))) (k + 1)) := by
  intro k hk
  have hA := switchL_saturated (hη t (by omega)) (hη (t + 1) (by omega))
  by_cases hk1 : k = t
  · subst hk1
    rw [Function.update_of_ne (by omega), Function.update_self]
    exact hA.1
  by_cases hk2 : k = t + 1
  · subst hk2
    rw [Function.update_self, Function.update_of_ne (by omega)]
    exact hA.2
  rw [Function.update_of_ne hk2, Function.update_of_ne (by omega)]
  exact hη k hk

/-- **(A3)** Uniqueness of "the other partition strictly between": if `a ⊂ b ⊂ c` and
`a ⊂ d ⊂ c` are saturated (one cell per step) and `d ≠ b`, then `d = other a b c`.
(Diagram-ness plays no role.) -/
theorem other_unique {a b c d : Finset Cell} (hab : a ⊆ b) (had : a ⊆ d)
    (hdc : d ⊆ c) (hba : (b \ a).card = 1) (hcb : (c \ b).card = 1) (hda : (d \ a).card = 1)
    (hdb : d ≠ b) : d = other a b c := by
  obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hba
  obtain ⟨y, hy⟩ := Finset.card_eq_one.1 hcb
  obtain ⟨z, hz⟩ := Finset.card_eq_one.1 hda
  have mx : ∀ w, w ∈ b ∧ w ∉ a ↔ w = x := fun w => by
    rw [← Finset.mem_singleton, ← hx, Finset.mem_sdiff]
  have my : ∀ w, w ∈ c ∧ w ∉ b ↔ w = y := fun w => by
    rw [← Finset.mem_singleton, ← hy, Finset.mem_sdiff]
  have mz : ∀ w, w ∈ d ∧ w ∉ a ↔ w = z := fun w => by
    rw [← Finset.mem_singleton, ← hz, Finset.mem_sdiff]
  -- `z ≠ x`, otherwise `d = a ∪ {x} = b`.
  have hzx : z ≠ x := by
    rintro rfl
    apply hdb
    ext w
    constructor
    · intro hw
      by_cases hwa : w ∈ a
      · exact hab hwa
      · exact ((mx w).2 ((mz w).1 ⟨hw, hwa⟩)).1
    · intro hw
      by_cases hwa : w ∈ a
      · exact had hwa
      · exact ((mz w).2 ((mx w).1 ⟨hw, hwa⟩)).1
  -- so `z ∉ b` and `z ∈ c`, hence `z = y`.
  have hzc : z ∈ c := hdc ((mz z).2 rfl).1
  have hzb : z ∉ b := fun hzb => hzx ((mx z).1 ⟨hzb, ((mz z).2 rfl).2⟩)
  have hzy : z = y := (my z).1 ⟨hzc, hzb⟩
  ext w
  simp only [other, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · intro hw
    by_cases hwa : w ∈ a
    · exact Or.inl hwa
    · have := (mz w).1 ⟨hw, hwa⟩
      exact Or.inr ((my w).2 (this.trans hzy))
  · rintro (hw | hw)
    · exact had hw
    · have := (my w).1 hw
      exact ((mz w).2 (this.trans hzy.symm)).1

/-! ## Tier B: the jdt forward slide, defined independently, against the switch product -/

/-- One jdt step with the hole at `h`. `cells[j]` is the cell holding entry `j+1` of the
standard skew tableau. If `smaller`, the hole moves to whichever of the east `(r, c+1)` and
north `(r+1, c)` neighbours carries the smaller entry; `smaller = false` is lesion 1. -/
def jdtStep (smaller : Bool) (cells : List Cell) (h : Cell) : Option (List Cell × Cell) :=
  let e : Cell := (h.1, h.2 + 1)
  let n : Cell := (h.1 + 1, h.2)
  match cells.idxOf? e, cells.idxOf? n with
  | none, none => none
  | some i, none => some (cells.set i h, e)
  | none, some j => some (cells.set j h, n)
  | some i, some j =>
      if decide (i < j) = smaller then some (cells.set i h, e) else some (cells.set j h, n)

/-- The jdt forward slide with fuel (the hole moves at most `cells.length` times). Returns the
new cell list of `F` and the final hole. -/
def jdt (smaller : Bool) : ℕ → List Cell → Cell → List Cell × Cell
  | 0, cells, h => (cells, h)
  | k + 1, cells, h =>
      match jdtStep smaller cells h with
      | none => (cells, h)
      | some (c', h') => jdt smaller k c' h'

/-- The chain `κ₀ ⊂ κ₀ ∪ {w₀} ⊂ κ₀ ∪ {w₀, w₁} ⊂ ⋯` of a cell word starting from `κ₀`. -/
def chainOf (κ₀ : Finset Cell) : List Cell → List (Finset Cell)
  | [] => [κ₀]
  | x :: w => κ₀ :: chainOf (insert x κ₀) w

/-- The cells occupied by the letters of a chain: `η_{t+1} \ η_t`. -/
def lettersOf : List (Finset Cell) → List (Finset Cell)
  | a :: b :: rest => (b \ a) :: lettersOf (b :: rest)
  | _ => []

/-- The elementary switch `s_t` on a list chain: `η_t ← switchL η_{t-1} η_t η_{t+1}`
(1-indexed `t`, the tex's convention; it swaps the letters at positions `t, t+1`). -/
def switchAt (ch : List (Finset Cell)) (t : ℕ) : List (Finset Cell) :=
  ch.set t (switchL (ch.getD (t - 1) ∅) (ch.getD t ∅) (ch.getD (t + 1) ∅))

/-- Carry the letter at position 1 (the hole `U_i`) rightward past `F_1, …, F_p`:
`s_p ∘ ⋯ ∘ s_1`. -/
def carry (p : ℕ) (ch : List (Finset Cell)) : List (Finset Cell) :=
  (List.range p).foldl (fun c t => switchAt c (t + 1)) ch

/-- Switch side: the letter cells after carrying the hole `h` past the filling `F`. -/
def switchSide (κ₀ : Finset Cell) (h : Cell) (F : List Cell) : List (Finset Cell) :=
  lettersOf (carry F.length (chainOf κ₀ (h :: F)))

/-- jdt side: the cells of `F'_1, …, F'_p`, then the final hole, as singletons. -/
def jdtSide (smaller : Bool) (h : Cell) (F : List Cell) : List (Finset Cell) :=
  let r := jdt smaller (F.length + 1) F h
  (r.1 ++ [r.2]).map ({·})

/-! ### Enumeration -/

/-- Candidate cells with both coordinates `≤ N`. -/
def cands (N : ℕ) : List Cell :=
  (List.range (N + 1)).flatMap fun r => (List.range (N + 1)).map (r, ·)

/-- Addable cells of `s` inside the `N`-box. -/
def addable (N : ℕ) (s : Finset Cell) : List Cell :=
  (cands N).filter fun x => x ∉ s ∧ IsDiag (insert x s)

/-- All diagrams of size `k` (inside the `N`-box). -/
def diags (N : ℕ) : ℕ → List (Finset Cell)
  | 0 => [∅]
  | k + 1 => ((diags N k).flatMap fun s => (addable N s).map (insert · s)).dedup

/-- Standard fillings of `ν / μ` as cell words (entry `j+1` in cell `w[j]`), `k = |ν| - |μ|`. -/
def stdFill (N : ℕ) (ν : Finset Cell) : ℕ → Finset Cell → List (List Cell)
  | 0, _ => [[]]
  | k + 1, μ =>
      ((addable N μ).filter (· ∈ ν)).flatMap fun x =>
        (stdFill N ν k (insert x μ)).map (x :: ·)

/-- Arbitrary orderings of the cells of `ν / μ` (lesion 2: standardness dropped). -/
def anyFill (N : ℕ) (ν : Finset Cell) : ℕ → Finset Cell → List (List Cell)
  | 0, _ => [[]]
  | k + 1, μ =>
      ((cands N).filter (· ∈ ν \ μ)).flatMap fun x => (anyFill N ν k (insert x μ)).map (x :: ·)

/-- All instances `(κ₀, h, F)` with `κ = κ₀ ∪ {h}` a diagram, `h` an inner corner, and `F` a
filling of `ν / κ` produced by `fill`, over all diagrams `ν` with `|ν| ≤ N`. -/
def instances (N : ℕ) (fill : Finset Cell → ℕ → Finset Cell → List (List Cell)) :
    List (Finset Cell × Cell × List Cell) :=
  (List.range (N + 1)).flatMap fun n =>
    (diags N n).flatMap fun ν =>
      (List.range (n + 1)).flatMap fun k =>
        ((diags N k).filter (· ⊆ ν)).flatMap fun κ =>
          ((cands N).filter fun h => h ∈ κ ∧ IsDiag (κ.erase h)).flatMap fun h =>
            (fill ν (n - k) κ).map fun F => (κ.erase h, h, F)

/-- Tier B: slide = switch product on every instance. -/
def slideCheck (N : ℕ) (smaller : Bool := true)
    (fill : Finset Cell → ℕ → Finset Cell → List (List Cell) := stdFill N) : Bool :=
  (instances N fill).all fun ⟨κ₀, h, F⟩ => switchSide κ₀ h F = jdtSide smaller h F

/-- First counterexample, if any. -/
def slideCounter (N : ℕ) (smaller : Bool := true)
    (fill : Finset Cell → ℕ → Finset Cell → List (List Cell) := stdFill N) :
    Option (Finset Cell × Cell × List Cell) :=
  (instances N fill).find? fun ⟨κ₀, h, F⟩ => switchSide κ₀ h F ≠ jdtSide smaller h F

end TworowD4Kernel.SlideSwitch

namespace TworowD4Kernel.SlideSwitch

/-! ### Kernel-checked instances -/

/-- Control: on `κ₀ = ∅`, hole `(0,0)`, `F = [(0,1),(1,0)]` (both neighbours present) the
switch product equals the smaller-neighbour slide. -/
theorem control_both_neighbours :
    switchSide ∅ (0, 0) [(0, 1), (1, 0)] = jdtSide true (0, 0) [(0, 1), (1, 0)] := by
  decide

/-- **Lesion 1** ("larger of east/north"): the switch product and the lesioned slide differ. -/
theorem lesion_larger :
    switchSide ∅ (0, 0) [(0, 1), (1, 0)] ≠ jdtSide false (0, 0) [(0, 1), (1, 0)] := by
  decide

/-- **Lesion 2** (standardness of `F` dropped): the row filling `2 1` of `(3)/(1)` breaks it. -/
theorem lesion_nonstandard :
    switchSide ∅ (0, 0) [(0, 2), (0, 1)] ≠ jdtSide true (0, 0) [(0, 2), (0, 1)] := by
  decide

/-- **Tier B, kernel-checked.** On every standard filling `F` of every skew shape `ν / κ` with
`|ν| ≤ 5` and every inner corner `h` of `κ` (162 instances; independently counted in Python
as 54 / 162 / 495 for `|ν| ≤ 4 / 5 / 6`), the jdt forward slide "smaller of east and north"
equals the product `s_p ∘ ⋯ ∘ s_1` of elementary switches carrying the hole past `F_1, …, F_p`.
This is a finite check, not the general statement (tier C, not formalised). `|ν| ≤ 6` is
checked only by `#guard` (evaluation) in `TworowD4KernelTests.lean`: kernel `decide` did not
finish in 580 s. -/
theorem slide_eq_switch_product_le5 : slideCheck 5 = true := by decide +kernel

/-- Lesion 1 at the level of the whole check. -/
theorem slideCheck_larger_fails : slideCheck 3 false = false := by decide +kernel

end TworowD4Kernel.SlideSwitch
