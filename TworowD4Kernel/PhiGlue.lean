/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.PhiOut
import TworowD4Kernel.SlidesColsBridge

/-!
# G4 Tier A: Φ's own run meets the window-form glue

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `def:phi` (l.98–106) and the proof of
`thm:G4` (l.200–208), the well-typed reading of Purbhoo arXiv:0705.1184 §5.1 Cor. 5.3 (p. 20).

The 2026-11-20 c2 glue (`SlidesColsBridge.V_colsW_of_slidesOK_fuel`) speaks about a run started
from a cell word `U` at fuel `m+1`. `PhiOut.phi` starts from `(S, uVal)` with
`S = skewCells (compl R C A) []` at fuel `R + C`. This file closes the gap between the two:

* **Gap 1, the word `U`.** `U` is `skewCells κ []` itself: its cells come row by row, west to east,
  which is exactly the `(value, column)` order of `uVal = row + 1`. `std_uVal_eq_valOf` proves
  `std S uVal = valOf U` on `S` for *every* list `κ` (no partition hypothesis), via
  `idxOf_eq_card_lt` (in a strictly lex-sorted list, a cell's index = number of smaller cells).
  No `Finset.sort` is involved.
* **Gap 3, fuel of `SlidesOK`.** `slidesOK_fuel_iff`: the named hypothesis is fuel-independent
  under the same conditions as the run (`slides_fuel_eq`), so it may be stated at Φ's fuel.
* **Gap 2 (reading).** The tex asserts in `def:phi`(1) that `f̃` "is a standard tableau on
  `B^∨/A^∨`" and gives no proof; `lem:C` gives `f̃ = std(rr f)`, which would make it standard
  given two unstated facts (`rr` preserves semistandardness; `std` of a semistandard tableau is
  standard). Recorded as a paper gap; here the glue needs only `Nodup` of `U ++ holes`, which is
  stated as a hypothesis (`hnd`), and `StdFrom ∅ (U ++ holes)` is not used in this file.

The capstone `phi_V_colsW`: under the named hypothesis `SlidesOK revRule (R+C)` on Φ's run, the
cells vacated by Φ's run are `take p (colsW m 0 p (U ++ holes))`.
-/

namespace TworowD4Kernel.PhiGlue

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.SlideIteration TworowD4Kernel.SlidesColsBridge TworowD4Kernel.PhiOut
open TworowD4Kernel.PhiOutData

/-! ### Gap 1: the word `U = skewCells κ []` -/

/-- Strict lexicographic order on cells `(row, column)`. -/
def LexLt (a b : Cell) : Prop := a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance (a b : Cell) : Decidable (LexLt a b) := by unfold LexLt; infer_instance

lemma lexLt_irrefl (a : Cell) : ¬ LexLt a a := by unfold LexLt; omega

/-- In a list that is strictly increasing in `LexLt`, the index of a member is the number of
members below it. -/
theorem idxOf_eq_card_lt : ∀ (l : List Cell), l.Pairwise LexLt → ∀ a ∈ l,
    l.idxOf a = (l.toFinset.filter fun b => LexLt b a).card
  | [], _, a, ha => by simp at ha
  | x :: l, hp, a, ha => by
    obtain ⟨hx, hl⟩ := List.pairwise_cons.1 hp
    have hxl : x ∉ l := fun hm => lexLt_irrefl x (hx x hm)
    rcases List.mem_cons.1 ha with rfl | ha'
    · rw [List.idxOf_cons_self]
      symm
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b hb hlt
      simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hb
      rcases hb with rfl | hb
      · exact lexLt_irrefl _ hlt
      · have := hx b hb; unfold LexLt at this hlt; omega
    · have hax : a ≠ x := fun e => hxl (e ▸ ha')
      rw [List.idxOf_cons_ne _ (Ne.symm hax), idxOf_eq_card_lt l hl a ha',
        List.toFinset_cons, Finset.filter_insert, if_pos (hx a ha'),
        Finset.card_insert_of_notMem (by simp [hxl])]

/-- `skewCells κ []` is strictly increasing in the lexicographic order. -/
theorem skewCells_sorted (κ : List ℕ) : (skewCells κ []).Pairwise LexLt := by
  unfold skewCells
  rw [List.pairwise_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact (List.pairwise_lt_range.filter _).imp fun h => Or.inr ⟨rfl, h⟩
  · refine List.pairwise_lt_range.imp fun {r r'} hrr a ha b hb => ?_
    simp only [List.mem_map] at ha hb
    obtain ⟨c, -, rfl⟩ := ha
    obtain ⟨c', -, rfl⟩ := hb
    exact Or.inl hrr

/-- The `(value, column)` key of `uVal` is the lexicographic order of cells. -/
lemma key_uVal_lt_iff (a b : Cell) : key uVal b < key uVal a ↔ LexLt b a := by
  simp only [key, uVal, Prod.Lex.toLex_lt_toLex, LexLt]
  omega

/-- **Gap 1.** For every `κ`, standardising `u_κ` on its own cells gives the position in the
word `skewCells κ []` (rows bottom to top, each west to east). -/
theorem std_uVal_eq_valOf (κ : List ℕ) :
    ∀ a ∈ skewCells κ [], std (skewCells κ []).toFinset uVal a = valOf (skewCells κ []) a := by
  intro a ha
  unfold std valOf
  rw [idxOf_eq_card_lt _ (skewCells_sorted κ) a ha]
  congr 1
  exact Finset.filter_congr fun b _ => key_uVal_lt_iff a b

theorem skewCells_nodup (κ : List ℕ) : (skewCells κ []).Nodup :=
  (skewCells_sorted κ).imp fun {a b} (h : LexLt a b) (e : a = b) => by
    subst e; exact lexLt_irrefl a h

/-! ### Gap 3: `SlidesOK` is fuel-independent like the run -/

lemma ch_none_of_small {S : Finset Cell} {X : Cell → ℕ} {h : Cell} (hh : h ∉ S)
    (hk : mu S h ≤ 0 ∨ dsum h ≤ 0) : revRule.ch S X h = none := by
  rcases hc : revRule.ch S X h with _ | y
  · rfl
  · obtain ⟨hyS, hd⟩ := revChoice_step hh hc
    have := mu_move hyS hd
    omega

/-- **Fuel stability of `SlideOK`** (the analogue of `slide_fuel_succ`). -/
theorem slideOK_fuel_succ : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    (mu S h ≤ k ∨ dsum h ≤ k) → (SlideOK revRule (k + 1) S X h ↔ SlideOK revRule k S X h) := by
  intro k
  induction k with
  | zero =>
    intro S X h hh hk
    simp only [SlideOK, ch_none_of_small (X := X) hh hk, and_true]
  | succ k ih =>
    intro S X h hh hk
    rw [SlideOK]
    conv_rhs => rw [SlideOK]
    rcases hc : revRule.ch S X h with _ | y
    · simp
    · obtain ⟨hyS, hd⟩ := revChoice_step hh hc
      have hyh : y ≠ h := fun e => hh (e ▸ hyS)
      have hy' : y ∉ moveS S h y := by simp [moveS, hyh]
      have := mu_move hyS hd
      simp only
      rw [ih (moveS S h y) (moveX X h y) y hy' (by omega)]

theorem slideOK_fuel_add (b : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hh : h ∉ S)
    (hb : mu S h ≤ b ∨ dsum h ≤ b) :
    ∀ n, (SlideOK revRule (b + n) S X h ↔ SlideOK revRule b S X h) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, slideOK_fuel_succ _ S X h hh (by omega), ih]

theorem slideOK_fuel_iff (k k' : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hh : h ∉ S)
    (hk : S.card ≤ k) (hk' : dsum h ≤ k') :
    SlideOK revRule k S X h ↔ SlideOK revRule k' S X h := by
  have hmu : mu S h ≤ S.card := Finset.card_filter_le _ _
  have e1 := slideOK_fuel_add (mu S h) S X h hh (Or.inl le_rfl) (k - mu S h)
  have e2 := slideOK_fuel_add (dsum h) S X h hh (Or.inr le_rfl) (k' - dsum h)
  have e3 := slideOK_fuel_add (mu S h) S X h hh (Or.inl le_rfl) (max k k' - mu S h)
  have e4 := slideOK_fuel_add (dsum h) S X h hh (Or.inr le_rfl) (max k k' - dsum h)
  rw [show mu S h + (k - mu S h) = k by omega] at e1
  rw [show dsum h + (k' - dsum h) = k' by omega] at e2
  rw [show mu S h + (max k k' - mu S h) = max k k' by omega] at e3
  rw [show dsum h + (max k k' - dsum h) = max k k' by omega] at e4
  rw [e1, e2, ← e3, ← e4]

/-- **Gap 3.** The named hypothesis `SlidesOK revRule` holds at fuel `k ≥ |S|` iff it holds at
any fuel `k'` covering every hole's anti-diagonal (Φ's `R + C`). -/
theorem slidesOK_fuel_iff (k k' : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    hs.Nodup → (∀ h ∈ hs, h ∉ S) → S.card ≤ k → (∀ h ∈ hs, dsum h ≤ k') →
    (SlidesOK revRule k S X hs ↔ SlidesOK revRule k' S X hs) := by
  intro hs
  induction hs with
  | nil => intro S X _ _ _ _; exact Iff.rfl
  | cons h hs ih =>
    intro S X hnd hS hk hk'
    have hh := hS h List.mem_cons_self
    have e := slide_fuel_eq k k' S X h hh hk (hk' h List.mem_cons_self)
    obtain ⟨sub, card⟩ := slide_support revRule k' S X h hh
    have hnd' := List.nodup_cons.1 hnd
    simp only [SlidesOK]
    rw [e, slideOK_fuel_iff k k' S X h hh hk (hk' h List.mem_cons_self),
      ih _ _ hnd'.2 (fun h' hm hm' => ?_) (by rw [card]; exact hk)
        (fun h' hm => hk' h' (List.mem_cons_of_mem _ hm))]
    rcases Finset.mem_insert.1 (sub hm') with rfl | hm''
    · exact hnd'.1 hm
    · exact hS h' (List.mem_cons_of_mem _ hm) hm''

/-! ### The capstone: Φ's run vacates the window-form cells -/

/-- Every hole of Φ is a rotated cell, so its anti-diagonal index is at most `R + C`. -/
theorem holes_dsum_le (t : ℕ → ℕ → Finset Cell → (Cell → ℕ) → Cell → ℕ) (R C : ℕ)
    (A B : List ℕ) (f : Cell → ℕ) : ∀ h ∈ holesWith t R C A B f, dsum h ≤ R + C := by
  intro h hm
  unfold holesWith at hm
  simp only [List.mem_filterMap] at hm
  obtain ⟨j, -, hj⟩ := hm
  have hmem := List.mem_of_find?_eq_some hj
  simp only [List.mem_map] at hmem
  obtain ⟨y, -, rfl⟩ := hmem
  simp only [dsum, rot]
  omega

/-- **Tier A capstone (`thm:G4`, outward half).** Let `κ = A^∨`, `U = skewCells κ []` (the word of
`u_κ` in standard order, gap 1) and `F` Φ's hole list. If `U ++ F` has no repeated cell and the
named hypothesis `SlidesOK revRule (R+C)` holds on Φ's run (column-injectivity along it: the
recalled Fulton fact, gap 3 lets it sit at Φ's own fuel), then the cells vacated by Φ's run are
the first `|F|` cells of the window-form outward procedure `colsW |U| 0 |F| (U ++ F)`. -/
theorem phi_V_colsW (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hnd : (skewCells (compl R C A) [] ++ holesWith tilde R C A B f).Nodup)
    (hok : SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f)) :
    (slides revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
        (holesWith tilde R C A B f)).2.2 =
      (colsW (skewCells (compl R C A) []).length 0 (holesWith tilde R C A B f).length
        (skewCells (compl R C A) [] ++ holesWith tilde R C A B f)).take
        (holesWith tilde R C A B f).length := by
  set U := skewCells (compl R C A) []
  set F := holesWith tilde R C A B f
  have hF : F.Nodup := (List.nodup_append.1 hnd).2.1
  have hdis : ∀ h ∈ F, h ∉ U.toFinset := fun h hm hU =>
    (List.nodup_append.1 hnd).2.2 h (List.mem_toFinset.1 hU) h hm rfl
  have hcard : U.toFinset.card ≤ U.length + 1 := by
    have := List.toFinset_card_le U; omega
  have hbox := holes_dsum_le tilde R C A B f
  have hok' := (slidesOK_fuel_iff (U.length + 1) (R + C) F U.toFinset uVal hF hdis hcard hbox).2 hok
  exact V_colsW_of_slidesOK_fuel U.length (R + C) U F uVal rfl hnd
    (std_uVal_eq_valOf (compl R C A)) hok' hbox

/-! ### Controls and lesions (kernel) -/

instance decSlidesOK (Rl : Rule) (k : ℕ) : ∀ S X hs, Decidable (SlidesOK Rl k S X hs)
  | _, _, [] => isTrue trivial
  | S, X, h :: hs =>
      haveI := decSlidesOK Rl k (slide Rl k S X h).1 (slide Rl k S X h).2.1 hs
      decidable_of_iff (h ∉ S ∧ SlideOK Rl k S X h ∧
        SlidesOK Rl k (slide Rl k S X h).1 (slide Rl k S X h).2.1 hs) (by simp [SlidesOK])

/-- **Control.** On the 310 `phiData33` instances, `U ++ F` is nodup, the named hypothesis
holds, and Φ's vacated cells equal `take p colsW` (so the capstone's hypotheses are met there
and its conclusion is not vacuous). -/
def capCheck (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  let R := d.1; let C := d.2.1; let A := d.2.2.1; let B := d.2.2.2.1
  let f := ofList d.2.2.2.2.1
  let U := skewCells (compl R C A) []
  let F := holesWith tilde R C A B f
  decide (U ++ F).Nodup &&
  decide (SlidesOK revRule (R + C) U.toFinset uVal F) &&
  decide ((slides revRule (R + C) U.toFinset uVal F).2.2 =
    (colsW U.length 0 F.length (U ++ F)).take F.length)

/-- **Lesion (gap 1, U in reverse order).** With `U` reversed, the word no longer standardises
`u_κ`; the window form then disagrees with Φ's run. -/
def capCheckRevU (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  let R := d.1; let C := d.2.1; let A := d.2.2.1; let B := d.2.2.2.1
  let f := ofList d.2.2.2.2.1
  let U := skewCells (compl R C A) []
  let F := holesWith tilde R C A B f
  decide ((slides revRule (R + C) U.toFinset uVal F).2.2 =
    (colsW U.length 0 F.length (U.reverse ++ F)).take F.length)

/-- **Control (kernel).** All 310 instances meet the capstone's hypotheses and conclusion. -/
theorem capstone_control_33 : phiData33.all capCheck = true := by decide +kernel

/-- The lesion instance: `A = (1,1)` in the `2 × 2` box, so `U = [(0,0),(1,0)]` has two cells. -/
def lesionRevU : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ) :=
  (2, 2, [1, 1], [0, 0], [((0, 0), 1), ((1, 0), 2)], [((0, 1), 1), ((1, 1), 2)])

/-- **Lesion (U reversed, kernel).** On `lesionRevU` the true `U` passes and the reversed word
fails; overall the reversed word fails on 98 of the 310 instances. The reversed word is still
nodup, so the lesion fails because `std S uVal = valOf U` breaks, not a precondition. -/
theorem lesion_U_reversed : lesionRevU ∈ phiData33 ∧ capCheck lesionRevU = true ∧
    capCheckRevU lesionRevU = false ∧
    (phiData33.filter fun d => !capCheckRevU d).length = 98 := by
  decide +kernel

end TworowD4Kernel.PhiGlue
