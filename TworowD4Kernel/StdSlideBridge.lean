/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.StdSlide
import TworowD4Kernel.SlideSwitchReverse

/-!
# G4 bridge: cell-word jdt = function-filling slides

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:A` (l.131–147, function fillings,
`StdSlide`) and `lem:D` (l.157–, cell words, `SlideSwitch`/`SlideIteration`). The tex uses both
representations of one standard tableau without comment; this file proves they agree.

* A **forward** cell word `w` (`w[j]` holds entry `j+1`) is the filling `(w.toFinset, valOf w)`,
  `valOf w y = w.idxOf y`. `jdt_bridge`: `jdt true k w h` and `slide fwdRule k` have the same final
  hole, the same final support, and the same values on it (`Nodup w`, `h ∉ w`).
* A **reverse** cell word (`w[i]` holds entry `m - i`) is `(w.toFinset, valDec w)`,
  `valDec w y = w.length - 1 - w.idxOf y`. `jdtRev_bridge` is the mirror for `jdtRev true` and
  `slide revRule` (tie → south on both sides).

`Nodup` is the standardness used: it makes `List.set` a permutation of values (the hole
receives the moved entry's index). No semistandardness enters.

Lesions (kernel `decide`): reading a forward word backwards (`lesion_reverse_order`) and a
reverse word forwards (`lesion_reverse_word_increasing`) each break the one-step bridge.
-/

namespace TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide

/-- The value function of a cell word: entry `j+1` sits at `w[j]`, value `j`. -/
def valOf (w : List Cell) (y : Cell) : ℕ := w.idxOf y

theorem idxOf?_of_mem' (e : ℕ × ℕ) : ∀ w : List Cell, e ∈ w → w.idxOf? e = some (w.idxOf e)
  | [], he => absurd he (List.not_mem_nil)
  | a :: t, he => by
    by_cases hae : a = e
    · subst hae; simp [List.idxOf_cons, List.idxOf?_cons]
    · have ht : e ∈ t := by
        rcases List.mem_cons.1 he with h | h
        · exact absurd h.symm hae
        · exact h
      have := idxOf?_of_mem' e t ht
      simp [List.idxOf_cons, List.idxOf?_cons, hae, this]

lemma idxOf?_of_mem {w : List Cell} {e : Cell} (he : e ∈ w) :
    w.idxOf? e = some (w.idxOf e) := idxOf?_of_mem' e w he

theorem idx_set (h : Cell) : ∀ (w : List Cell) (i : ℕ) (hi : i < w.length), h ∉ w →
    (w.set i h).idxOf h = i ∧ ∀ a, a ≠ w[i] → a ≠ h → (w.set i h).idxOf a = w.idxOf a
  | [], i, hi, _ => absurd hi (by simp)
  | b :: t, 0, _, hh => by
    have hbh : b ≠ h := fun e => hh (e ▸ List.mem_cons_self)
    refine ⟨by simp [List.idxOf_cons], fun a ha hah => ?_⟩
    simp only [List.getElem_cons_zero] at ha
    simp [List.idxOf_cons, beq_iff_eq, Ne.symm ha, Ne.symm hah]
  | b :: t, i + 1, hi, hh => by
    have hbh : b ≠ h := fun e => hh (e ▸ List.mem_cons_self)
    have ht : h ∉ t := fun e => hh (List.mem_cons_of_mem _ e)
    obtain ⟨i1, i2⟩ := idx_set h t i (by simpa using hi) ht
    refine ⟨by simp [List.idxOf_cons, hbh, i1], fun a ha hah => ?_⟩
    simp only [List.getElem_cons_succ] at ha
    by_cases hba : b = a
    · subst hba; simp [List.idxOf_cons]
    · simp [List.idxOf_cons, hba, i2 a ha hah]

theorem mem_set_nodup (h : Cell) : ∀ (w : List Cell) (i : ℕ) (hi : i < w.length), w.Nodup →
    ∀ a, a ∈ w.set i h ↔ a = h ∨ (a ∈ w ∧ a ≠ w[i]) := by
  intro w i hi hw a
  rw [List.mem_iff_getElem, List.mem_iff_getElem]
  simp only [List.length_set, List.getElem_set]
  constructor
  · rintro ⟨j, hj, hja⟩
    split_ifs at hja with hij
    · exact Or.inl hja.symm
    · refine Or.inr ⟨⟨j, hj, hja⟩, fun e => hij ?_⟩
      subst hja
      exact ((List.Nodup.getElem_inj_iff hw).1 e).symm
  · rintro (e | ⟨⟨j, hj, hja⟩, hne⟩)
    · exact ⟨i, hi, by simp [e]⟩
    · refine ⟨j, hj, ?_⟩
      have : i ≠ j := fun e => hne (by subst e; exact hja.symm)
      simp [this, hja]

lemma idxOf?_of_not_mem {w : List Cell} {e : Cell} (he : e ∉ w) : w.idxOf? e = none :=
  List.idxOf?_eq_none_iff.2 he

/-- **Bridge, path part.** The cell-word jdt step (`smaller = true`) moves the hole to the same
cell as the function-filling forward step `fwdChoice` on `(w.toFinset, valOf w)`. -/
theorem jdtStep_hole (w : List Cell) (h : Cell) :
    (jdtStep true w h).map Prod.snd = fwdChoice w.toFinset (valOf w) h := by
  unfold jdtStep fwdChoice
  simp only [List.mem_toFinset, nN, nE, valOf]
  by_cases hE : ((h.1, h.2 + 1) : Cell) ∈ w <;> by_cases hN : ((h.1 + 1, h.2) : Cell) ∈ w
  · rw [idxOf?_of_mem hE, idxOf?_of_mem hN]
    simp only [hE, hN, if_true]
    by_cases hlt : w.idxOf (h.1, h.2 + 1) < w.idxOf (h.1 + 1, h.2)
    · have : ¬ w.idxOf (h.1 + 1, h.2) ≤ w.idxOf (h.1, h.2 + 1) := by omega
      simp [hlt, this]
    · have : w.idxOf (h.1 + 1, h.2) ≤ w.idxOf (h.1, h.2 + 1) := by omega
      simp [hlt, this]
  · rw [idxOf?_of_mem hE, idxOf?_of_not_mem hN]; simp [hE, hN]
  · rw [idxOf?_of_not_mem hE, idxOf?_of_mem hN]; simp [hE, hN]
  · rw [idxOf?_of_not_mem hE, idxOf?_of_not_mem hN]; simp [hE, hN]


/-- The cell-word step replaces the moved cell `y` by the hole. -/
theorem jdtStep_move (w : List Cell) (h : Cell) {w' : List Cell} {y : Cell}
    (hs : jdtStep true w h = some (w', y)) : y ∈ w ∧ w' = w.set (w.idxOf y) h := by
  unfold jdtStep at hs
  simp only at hs
  by_cases hE : ((h.1, h.2 + 1) : Cell) ∈ w <;> by_cases hN : ((h.1 + 1, h.2) : Cell) ∈ w
  · rw [idxOf?_of_mem hE, idxOf?_of_mem hN] at hs
    simp only at hs
    split_ifs at hs <;> (simp only [Option.some.injEq, Prod.mk.injEq] at hs) <;>
      (obtain ⟨rfl, rfl⟩ := hs) <;> simp_all
  · rw [idxOf?_of_mem hE, idxOf?_of_not_mem hN] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; exact ⟨hE, rfl⟩
  · rw [idxOf?_of_not_mem hE, idxOf?_of_mem hN] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; exact ⟨hN, rfl⟩
  · rw [idxOf?_of_not_mem hE, idxOf?_of_not_mem hN] at hs
    simp at hs

/-- **Bridge, one step.** For a standard cell word `w` (no repeated cell) and a hole `h ∉ w`,
the cell-word jdt step and the function-filling forward step agree: same moved cell, and the new
word's support and values are `moveS`/`moveX` of the old. The new word is again standard and
does not contain the new hole. -/
theorem jdtStep_bridge (w : List Cell) (hw : w.Nodup) (h : Cell) (hh : h ∉ w)
    {w' : List Cell} {y : Cell} (hs : jdtStep true w h = some (w', y)) :
    fwdChoice w.toFinset (valOf w) h = some y ∧
    w'.toFinset = moveS w.toFinset h y ∧
    (∀ a ∈ moveS w.toFinset h y, valOf w' a = moveX (valOf w) h y a) ∧
    w'.Nodup ∧ y ∉ w' := by
  have hhole := jdtStep_hole w h
  rw [hs] at hhole
  obtain ⟨hyw, rfl⟩ := jdtStep_move w h hs
  have hi : w.idxOf y < w.length := List.idxOf_lt_length_iff.2 hyw
  have hwi : w[w.idxOf y] = y := List.getElem_idxOf hi
  have hyh : y ≠ h := fun e => hh (e ▸ hyw)
  have hmem := mem_set_nodup h w (w.idxOf y) hi hw
  obtain ⟨i1, i2⟩ := idx_set h w (w.idxOf y) hi hh
  refine ⟨hhole.symm, ?_, ?_, ?_, ?_⟩
  · ext a
    simp only [List.mem_toFinset, hmem, moveS, Finset.mem_insert, Finset.mem_erase, hwi]
    tauto
  · intro a ha
    simp only [moveS, Finset.mem_insert, Finset.mem_erase, List.mem_toFinset] at ha
    unfold valOf moveX
    by_cases hah : a = h
    · subst hah; simp [i1]
    · rw [Function.update_of_ne hah]
      rcases ha with ha | ⟨hay, -⟩
      · exact absurd ha hah
      · exact i2 a (by rw [hwi]; exact hay) hah
  · exact List.Nodup.set hw hh
  · rw [hmem, hwi]; simp [hyh]

/-- **Bridge, iterated.** For a standard cell word `w` and hole `h ∉ w`, the cell-word forward
slide `jdt true k` and the function-filling slide `slide fwdRule k` on `(w.toFinset, valOf w)`
have the same final hole, the same final support, and the same values on it. -/
theorem jdt_bridge : ∀ (k : ℕ) (w : List Cell) (h : Cell), w.Nodup → h ∉ w →
    (jdt true k w h).2 = (slide fwdRule k w.toFinset (valOf w) h).2.2.1 ∧
    (jdt true k w h).1.toFinset = (slide fwdRule k w.toFinset (valOf w) h).1 ∧
    ∀ a ∈ (slide fwdRule k w.toFinset (valOf w) h).1,
      valOf (jdt true k w h).1 a = (slide fwdRule k w.toFinset (valOf w) h).2.1 a := by
  intro k
  induction k with
  | zero => intro w h _ _; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    intro w h hw hh
    simp only [jdt, slide]
    rcases hs : jdtStep true w h with _ | ⟨w', y⟩
    · have hn := jdtStep_hole w h
      rw [hs] at hn
      have : fwdRule.ch w.toFinset (valOf w) h = none := hn.symm
      rw [this]
      exact ⟨rfl, rfl, fun _ _ => rfl⟩
    · obtain ⟨hc, hS, hX, hw', hy'⟩ := jdtStep_bridge w hw h hh hs
      have : fwdRule.ch w.toFinset (valOf w) h = some y := hc
      rw [this]
      simp only
      obtain ⟨j1, j2, j3⟩ := ih w' y hw' hy'
      rw [hS] at j1 j2 j3
      obtain ⟨c1, c2, c3⟩ := slide_congr fwdRule k _ _ _ y (fun a ha => (hX a ha).symm)
      refine ⟨by rw [j1, c2], by rw [j2, c1], fun a ha => ?_⟩
      rw [j3 a (c1 ▸ ha), c3 a (c1 ▸ ha)]

/-! ### Controls and lesions -/

/-- Control: a forward tie configuration from StdSlide, as a word: the hole `(0,0)` has north
`(1,0)` (entry 1) and east `(0,1)` (entry 2); both sides move north. -/
example : (jdtStep true [(1, 0), (0, 1)] (0, 0)).map Prod.snd = some (1, 0) := by decide
example : fwdChoice ([(1, 0), (0, 1)] : List Cell).toFinset (valOf [(1, 0), (0, 1)]) (0, 0)
    = some (1, 0) := by decide

/-- **Lesion (cell order).** Reading the word in the reverse order (value = position from the
end) breaks the bridge at the smallest instance. -/
def valRev (w : List Cell) (y : Cell) : ℕ := w.length - 1 - w.idxOf y

theorem lesion_reverse_order :
    (jdtStep true [(1, 0), (0, 1)] (0, 0)).map Prod.snd ≠
      fwdChoice ([(1, 0), (0, 1)] : List Cell).toFinset (valRev [(1, 0), (0, 1)]) (0, 0) := by
  decide

/-- **Lesion (non-standard word).** With a repeated cell, `idxOf` loses an entry and the
support/value agreement is not available; the `Nodup` hypothesis is used (`List.Nodup.set`). -/
example : ¬ ([(0, 1), (0, 1)] : List Cell).Nodup := by decide

/-! ### The reverse bridge (`jdtRev true` ↔ `slide revRule`) -/

/-- Value function of a reverse cell word: `cells[i]` holds entry `m - i` (decreasing order),
so the value is `length - 1 - index`. -/
def valDec (w : List Cell) (y : Cell) : ℕ := w.length - 1 - w.idxOf y

/-- **Reverse bridge, path part.** -/
theorem jdtStepRev_hole (w : List Cell) (h : Cell) :
    (jdtStepRev true w h).map Prod.snd = revChoice w.toFinset (valDec w) h := by
  unfold jdtStepRev revChoice
  simp only [List.mem_toFinset, nS, nW, valDec]
  by_cases hW : ((h.1, h.2 - 1) : Cell) ∈ w <;> by_cases hS : ((h.1 - 1, h.2) : Cell) ∈ w
  · rw [idxOf?_of_mem hW, idxOf?_of_mem hS]
    simp only [hW, hS, if_true]
    have l1 := List.idxOf_lt_length_iff.2 hW
    have l2 := List.idxOf_lt_length_iff.2 hS
    by_cases hlt : w.idxOf (h.1, h.2 - 1) < w.idxOf (h.1 - 1, h.2)
    · have : ¬ w.length - 1 - w.idxOf (h.1, h.2 - 1) ≤ w.length - 1 - w.idxOf (h.1 - 1, h.2) := by
        omega
      simp [hlt, this]
    · have : w.length - 1 - w.idxOf (h.1, h.2 - 1) ≤ w.length - 1 - w.idxOf (h.1 - 1, h.2) := by
        omega
      simp [hlt, this]
  · rw [idxOf?_of_mem hW, idxOf?_of_not_mem hS]; simp [hW, hS]
  · rw [idxOf?_of_not_mem hW, idxOf?_of_mem hS]; simp [hW, hS]
  · rw [idxOf?_of_not_mem hW, idxOf?_of_not_mem hS]; simp [hW, hS]

theorem jdtStepRev_move (w : List Cell) (h : Cell) {w' : List Cell} {y : Cell}
    (hs : jdtStepRev true w h = some (w', y)) : y ∈ w ∧ w' = w.set (w.idxOf y) h := by
  unfold jdtStepRev at hs
  simp only at hs
  by_cases hW : ((h.1, h.2 - 1) : Cell) ∈ w <;> by_cases hS : ((h.1 - 1, h.2) : Cell) ∈ w
  · rw [idxOf?_of_mem hW, idxOf?_of_mem hS] at hs
    simp only at hs
    split_ifs at hs <;> (simp only [Option.some.injEq, Prod.mk.injEq] at hs) <;>
      (obtain ⟨rfl, rfl⟩ := hs) <;> simp_all
  · rw [idxOf?_of_mem hW, idxOf?_of_not_mem hS] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; exact ⟨hW, rfl⟩
  · rw [idxOf?_of_not_mem hW, idxOf?_of_mem hS] at hs
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs; exact ⟨hS, rfl⟩
  · rw [idxOf?_of_not_mem hW, idxOf?_of_not_mem hS] at hs
    simp at hs

/-- **Reverse bridge, one step.** -/
theorem jdtStepRev_bridge (w : List Cell) (hw : w.Nodup) (h : Cell) (hh : h ∉ w)
    {w' : List Cell} {y : Cell} (hs : jdtStepRev true w h = some (w', y)) :
    revChoice w.toFinset (valDec w) h = some y ∧
    w'.toFinset = moveS w.toFinset h y ∧
    (∀ a ∈ moveS w.toFinset h y, valDec w' a = moveX (valDec w) h y a) ∧
    w'.Nodup ∧ y ∉ w' := by
  have hhole := jdtStepRev_hole w h
  rw [hs] at hhole
  obtain ⟨hyw, rfl⟩ := jdtStepRev_move w h hs
  have hi : w.idxOf y < w.length := List.idxOf_lt_length_iff.2 hyw
  have hwi : w[w.idxOf y] = y := List.getElem_idxOf hi
  have hyh : y ≠ h := fun e => hh (e ▸ hyw)
  have hmem := mem_set_nodup h w (w.idxOf y) hi hw
  obtain ⟨i1, i2⟩ := idx_set h w (w.idxOf y) hi hh
  refine ⟨hhole.symm, ?_, ?_, ?_, ?_⟩
  · ext a
    simp only [List.mem_toFinset, hmem, moveS, Finset.mem_insert, Finset.mem_erase, hwi]
    tauto
  · intro a ha
    simp only [moveS, Finset.mem_insert, Finset.mem_erase, List.mem_toFinset] at ha
    unfold valDec moveX
    rw [List.length_set]
    by_cases hah : a = h
    · subst hah; simp [i1]
    · rw [Function.update_of_ne hah]
      rcases ha with ha | ⟨hay, -⟩
      · exact absurd ha hah
      · rw [i2 a (by rw [hwi]; exact hay) hah]
  · exact List.Nodup.set hw hh
  · rw [hmem, hwi]; simp [hyh]

/-- **Reverse bridge, iterated:** `jdtRev true k` = `slide revRule k` on `(w.toFinset, valDec w)`. -/
theorem jdtRev_bridge : ∀ (k : ℕ) (w : List Cell) (h : Cell), w.Nodup → h ∉ w →
    (jdtRev true k w h).2 = (slide revRule k w.toFinset (valDec w) h).2.2.1 ∧
    (jdtRev true k w h).1.toFinset = (slide revRule k w.toFinset (valDec w) h).1 ∧
    ∀ a ∈ (slide revRule k w.toFinset (valDec w) h).1,
      valDec (jdtRev true k w h).1 a = (slide revRule k w.toFinset (valDec w) h).2.1 a := by
  intro k
  induction k with
  | zero => intro w h _ _; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    intro w h hw hh
    simp only [jdtRev, slide]
    rcases hs : jdtStepRev true w h with _ | ⟨w', y⟩
    · have hn := jdtStepRev_hole w h
      rw [hs] at hn
      have : revRule.ch w.toFinset (valDec w) h = none := hn.symm
      rw [this]
      exact ⟨rfl, rfl, fun _ _ => rfl⟩
    · obtain ⟨hc, hS, hX, hw', hy'⟩ := jdtStepRev_bridge w hw h hh hs
      have : revRule.ch w.toFinset (valDec w) h = some y := hc
      rw [this]
      simp only
      obtain ⟨j1, j2, j3⟩ := ih w' y hw' hy'
      rw [hS] at j1 j2 j3
      obtain ⟨c1, c2, c3⟩ := slide_congr revRule k _ _ _ y (fun a ha => (hX a ha).symm)
      refine ⟨by rw [j1, c2], by rw [j2, c1], fun a ha => ?_⟩
      rw [j3 a (c1 ▸ ha), c3 a (c1 ▸ ha)]

/-- **Lesion (reverse cell order).** Reading a reverse word in increasing order (`valOf`)
breaks the reverse bridge: hole `(1,1)`, word `[(1,0), (0,1)]` (west has the larger entry). -/
theorem lesion_reverse_word_increasing :
    (jdtStepRev true [(1, 0), (0, 1)] (1, 1)).map Prod.snd ≠
      revChoice ([(1, 0), (0, 1)] : List Cell).toFinset (valOf [(1, 0), (0, 1)]) (1, 1) := by
  decide

end TworowD4Kernel.StdSlideBridge
