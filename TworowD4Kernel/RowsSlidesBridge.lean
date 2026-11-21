/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SlidesColsBridge
import TworowD4Kernel.PhiOut
import TworowD4Kernel.PhiGlue

/-!
# G4 gap 4: `StdSlide.slides fwdRule` (iterated over holes) = `SlideIteration.rowsW` (window form)

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, definition of `Σ` (`sec:G4`) and
`lem:D`. This file is the forward mirror of `SlidesColsBridge.slides_colsW`, Purbhoo
arXiv:0705.1184 §5.1.

`slides_rowsW` (main): if `U ++ F ++ Z` has no repeated cell, `|F| = p` and `X = valOf F` on `F`,
then, with fuel `p+1` per slide (the fuel of `slideW`),

  `rowsW p |U| (U ++ F ++ Z) = F' ++ V.reverse ++ Z`,

where `V` is the vacated-cell list of `slides fwdRule (p+1) F.toFinset X U.reverse`. The holes are
the letters of `U`, last letter first. `F'` is a cell word whose support and values are the run's
final support and values.
-/

namespace TworowD4Kernel.RowsSlidesBridge
open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.SlideIteration TworowD4Kernel.SlidesColsBridge

/-- Bookkeeping for the forward cell-word slide: length, no repetition, the final hole is not
in the word, and every cell involved comes from `w` or is the start hole. -/
theorem jdt_props : ∀ (k : ℕ) (w : List Cell) (h : Cell), w.Nodup → h ∉ w →
    (jdt true k w h).1.length = w.length ∧ (jdt true k w h).1.Nodup ∧
    (jdt true k w h).2 ∉ (jdt true k w h).1 ∧
    (∀ a ∈ (jdt true k w h).1, a ∈ w ∨ a = h) ∧
    ((jdt true k w h).2 ∈ w ∨ (jdt true k w h).2 = h) := by
  intro k
  induction k with
  | zero => intro w h hw hh; exact ⟨rfl, hw, hh, fun a ha => Or.inl ha, Or.inr rfl⟩
  | succ k ih =>
    intro w h hw hh
    simp only [jdt]
    rcases hs : jdtStep true w h with _ | ⟨w', y⟩
    · exact ⟨rfl, hw, hh, fun a ha => Or.inl ha, Or.inr rfl⟩
    · obtain ⟨-, -, -, hw', hy'⟩ := jdtStep_bridge w hw h hh hs
      obtain ⟨hyw, rfl⟩ := jdtStep_move w h hs
      obtain ⟨l, n, nh, m, mh⟩ := ih _ y hw' hy'
      dsimp only
      have hset : ∀ a ∈ w.set (w.idxOf y) h, a ∈ w ∨ a = h := fun a ha =>
        List.mem_or_eq_of_mem_set ha
      refine ⟨by rw [l, List.length_set], n, nh, fun a ha => ?_, ?_⟩
      · rcases m a ha with ha | rfl
        · exact hset a ha
        · exact Or.inl hyw
      · rcases mh with ha | ha
        · exact hset _ ha
        · rw [ha]; exact Or.inl hyw

/-- **One step.** The forward slide of the hole `h` through the filling `(F, X)` with
`X = valOf F` is the window step of `rowsW`: new word `F1` (the run's final support and values),
then the vacated cell. -/
theorem slide_eq_slideW (F : List Cell) (h : Cell) (hF : F.Nodup) (hh : h ∉ F)
    (X : Cell → ℕ) (hX : ∀ a ∈ F, X a = valOf F a) :
    let r := slide fwdRule (F.length + 1) F.toFinset X h
    slideW h F = (jdt true (F.length + 1) F h).1 ++ [r.2.2.1] ∧
    (jdt true (F.length + 1) F h).1.toFinset = r.1 ∧
    (∀ a ∈ r.1, r.2.1 a = valOf (jdt true (F.length + 1) F h).1 a) := by
  intro r
  obtain ⟨b1, b2, b3⟩ := jdt_bridge (F.length + 1) F h hF hh
  obtain ⟨c1, c2, c3⟩ := slide_congr fwdRule (F.length + 1) F.toFinset X (valOf F) h
    (fun a ha => hX a (List.mem_toFinset.1 ha))
  refine ⟨?_, ?_, ?_⟩
  · unfold slideW; rw [b1, ← c2]
  · rw [b2, ← c1]
  · intro a ha
    rw [c3 a ha, ← b3 a (c1 ▸ ha)]

/-- **Glue lemma (`slides fwdRule` ↔ `rowsW`).** -/
theorem slides_rowsW (p : ℕ) : ∀ (H U F Z : List Cell) (X : Cell → ℕ), U = H.reverse →
    F.length = p → (U ++ (F ++ Z)).Nodup → (∀ a ∈ F, X a = valOf F a) →
    ∃ F' : List Cell,
      rowsW p U.length (U ++ (F ++ Z)) =
        F' ++ ((slides fwdRule (p + 1) F.toFinset X H).2.2.reverse ++ Z) ∧
      F'.toFinset = (slides fwdRule (p + 1) F.toFinset X H).1 ∧
      (∀ a ∈ (slides fwdRule (p + 1) F.toFinset X H).1,
        (slides fwdRule (p + 1) F.toFinset X H).2.1 a = valOf F' a) ∧
      F'.length = p := by
  intro H
  induction H with
  | nil =>
    intro U F Z X hU hp _ hX
    subst hU
    refine ⟨F, by simp [rowsW, slides], by simp [slides], fun a ha => hX a ?_, hp⟩
    simpa [slides] using ha
  | cons h H ih =>
    intro U F Z X hU hp hnd hX
    subst hU hp
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append] at hnd ⊢
    -- hnd : (H.reverse ++ h :: (F ++ Z)).Nodup
    have hn2 := List.nodup_append.1 hnd
    have hhFZ : (h :: (F ++ Z)).Nodup := hn2.2.1
    have hFZ : (F ++ Z).Nodup := (List.nodup_cons.1 hhFZ).2
    have hF : F.Nodup := (List.nodup_append.1 hFZ).1
    have hh : h ∉ F := fun hm => (List.nodup_cons.1 hhFZ).1 (List.mem_append_left _ hm)
    obtain ⟨e1, e2, e3⟩ := slide_eq_slideW F h hF hh X hX
    set r := slide fwdRule (F.length + 1) F.toFinset X h with hr
    set F1 := (jdt true (F.length + 1) F h).1 with hF1
    obtain ⟨l, n, nh, m, mh⟩ := jdt_props (F.length + 1) F h hF hh
    rw [← hF1] at l n nh m
    have hz : r.2.2.1 = (jdt true (F.length + 1) F h).2 := by
      have := e1; unfold slideW at this
      simpa using (List.append_inj' this rfl).2.symm
    -- cells of `F1` and the vacated cell come from `h :: F`
    have hsrc : ∀ a, (a ∈ F1 ∨ a = r.2.2.1) → a ∈ h :: F := by
      rintro a (ha | rfl)
      · rcases m a ha with ha | rfl
        · exact List.mem_cons_of_mem _ ha
        · exact List.mem_cons_self
      · rw [hz]; rcases mh with ha | ha
        · exact List.mem_cons_of_mem _ ha
        · rw [ha]; exact List.mem_cons_self
    have hnd' : (H.reverse ++ (F1 ++ (r.2.2.1 :: Z))).Nodup := by
      have hFZd := List.nodup_append.1 hFZ
      have hhZ : h ∉ Z := fun hm => (List.nodup_cons.1 hhFZ).1 (List.mem_append_right _ hm)
      have hsZ : ∀ a ∈ h :: F, a ∉ Z := by
        intro a ha hZ
        rcases List.mem_cons.1 ha with rfl | ha
        · exact hhZ hZ
        · exact hFZd.2.2 a ha a hZ rfl
      have hall : ∀ a ∈ F1 ++ (r.2.2.1 :: Z), a ∈ h :: (F ++ Z) := by
        intro a ha
        rcases List.mem_append.1 ha with ha | ha
        · rcases List.mem_cons.1 (hsrc a (Or.inl ha)) with rfl | ha
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
        · rcases List.mem_cons.1 ha with rfl | ha
          · rcases List.mem_cons.1 (hsrc _ (Or.inr rfl)) with e | ha
            · rw [e]; exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (List.mem_append_left _ ha)
          · exact List.mem_cons_of_mem _ (List.mem_append_right _ ha)
      have hzZ : r.2.2.1 ∉ Z := hsZ _ (hsrc _ (Or.inr rfl))
      have hzF1 : r.2.2.1 ∉ F1 := by rw [hz]; exact nh
      refine List.nodup_append.2 ⟨hn2.1, ?_, fun a ha b hb => hn2.2.2 a ha b (hall b hb)⟩
      refine List.nodup_append.2 ⟨n, List.nodup_cons.2 ⟨hzZ, hFZd.2.1⟩, fun a ha b hb => ?_⟩
      rcases List.mem_cons.1 hb with rfl | hb
      · rintro rfl; exact hzF1 ha
      · rintro rfl; exact hsZ a (hsrc a (Or.inl ha)) hb
    have hX1 : ∀ a ∈ F1, r.2.1 a = valOf F1 a := by
      intro a ha; exact e3 a (e2 ▸ List.mem_toFinset.2 ha)
    obtain ⟨F', i1, i2, i3, i4⟩ := ih H.reverse F1 (r.2.2.1 :: Z) r.2.1 rfl l hnd' hX1
    rw [e2] at i1 i2 i3
    refine ⟨F', ?_, ?_, ?_, i4⟩
    · have t1 : (H.reverse ++ h :: (F ++ Z)).take H.reverse.length = H.reverse := by simp
      have t3 : (H.reverse ++ h :: (F ++ Z)).getD H.reverse.length (0, 0) = h := by
        simp [List.getD_eq_getElem?_getD]
      have t2 : ((H.reverse ++ h :: (F ++ Z)).drop (H.reverse.length + 1)).take F.length = F := by
        have e : H.reverse ++ h :: (F ++ Z) = (H.reverse ++ [h]) ++ (F ++ Z) := by simp
        rw [e, show H.reverse.length + 1 = (H.reverse ++ [h]).length by simp, List.drop_left,
          List.take_left' rfl]
      have t4 : (H.reverse ++ h :: (F ++ Z)).drop (H.reverse.length + 1 + F.length) = Z := by
        have e : H.reverse ++ h :: (F ++ Z) = (H.reverse ++ h :: F) ++ Z := by simp
        rw [e, show H.reverse.length + 1 + F.length = (H.reverse ++ h :: F).length by simp; omega,
          List.drop_left]
      rw [List.length_append, List.length_singleton, rowsW, t1, t2, t3, t4, e1]
      simp only [List.append_assoc, List.singleton_append] at i1 ⊢
      rw [i1]
      simp [slides, hr]
    · simpa [slides, hr] using i2
    · intro a ha
      simpa [slides, hr] using i3 a (by simpa [slides, hr] using ha)

/-- **Glue, `Z = []` reading.** The vacated cells of `slides fwdRule (p+1) F X U.reverse` are the
last `|U|` cells of `rowsW p |U| (U ++ F)`, read backwards. The first `p` cells form a word with
the final support and values of the run. -/
theorem slides_rowsW_drop (U F : List Cell) (X : Cell → ℕ)
    (hnd : (U ++ F).Nodup) (hX : ∀ a ∈ F, X a = valOf F a) :
    (slides fwdRule (F.length + 1) F.toFinset X U.reverse).2.2 =
      ((rowsW F.length U.length (U ++ F)).drop F.length).reverse ∧
    ((rowsW F.length U.length (U ++ F)).take F.length).toFinset =
      (slides fwdRule (F.length + 1) F.toFinset X U.reverse).1 ∧
    ∀ a ∈ (slides fwdRule (F.length + 1) F.toFinset X U.reverse).1,
      (slides fwdRule (F.length + 1) F.toFinset X U.reverse).2.1 a =
        valOf ((rowsW F.length U.length (U ++ F)).take F.length) a := by
  obtain ⟨F', h1, h2, h3, h4⟩ := slides_rowsW F.length U.reverse U F [] X
    (List.reverse_reverse U).symm rfl (by simpa using hnd) hX
  simp only [List.append_nil] at h1
  rw [h1]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.drop_left' h4, List.reverse_reverse]
  · rw [List.take_left' h4, h2]
  · intro a ha; rw [List.take_left' h4, h3 a ha]

/-- **Glue under `SlidesOK`.** If the forward run on a filling `(F, X)` is column-injective
throughout (`SlidesOK fwdRule`, the named hypothesis: the recalled Fulton fact), and its
standardisation is the word `F` (`std F X = valOf F`), then the cells vacated by `Σ`'s slides
(holes `U` last-first) are `(rowsW p |U| (U ++ F)).drop p`, read backwards. -/
theorem V_rowsW_of_slidesOK (U F : List Cell) (X : Cell → ℕ)
    (hnd : (U ++ F).Nodup) (hstd : ∀ a ∈ F, std F.toFinset X a = valOf F a)
    (hok : SlidesOK fwdRule (F.length + 1) F.toFinset X U.reverse) :
    (slides fwdRule (F.length + 1) F.toFinset X U.reverse).2.2 =
      ((rowsW F.length U.length (U ++ F)).drop F.length).reverse := by
  rw [← (lemmaA_slides fwdRule (F.length + 1) U.reverse F.toFinset X hok).1]
  exact (slides_rowsW_drop U F (std F.toFinset X) hnd hstd).1

/-! ### Forward fuel -/

/-- Support cells strictly above the hole's anti-diagonal. -/
def nu (S : Finset Cell) (h : Cell) : ℕ := (S.filter fun s => dsum h < dsum s).card

lemma fwdChoice_step {S : Finset Cell} {X : Cell → ℕ} {h y : Cell}
    (hc : fwdRule.ch S X h = some y) : y ∈ S ∧ dsum y = dsum h + 1 := by
  have hyS := fwdRule.mem S X h y hc
  refine ⟨hyS, ?_⟩
  have hc' : fwdChoice S X h = some y := hc
  unfold fwdChoice at hc'
  split_ifs at hc' <;> (simp only [Option.some.injEq] at hc') <;> subst hc' <;>
    simp [nN, nE, dsum] <;> omega

lemma nu_move {S : Finset Cell} {h y : Cell} (hyS : y ∈ S) (hd : dsum y = dsum h + 1) :
    nu (moveS S h y) y + 1 ≤ nu S h := by
  unfold nu moveS
  rw [Finset.filter_insert, if_neg (by omega)]
  have hsub : (S.erase y).filter (fun s => dsum y < dsum s) ⊆
      (S.filter fun s => dsum h < dsum s).erase y := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_erase] at hs ⊢
    exact ⟨hs.1.1, hs.1.2, by omega⟩
  have hy : y ∈ S.filter fun s => dsum h < dsum s := Finset.mem_filter.2 ⟨hyS, by omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hy] at this
  have := Finset.card_pos.2 ⟨y, hy⟩
  omega

theorem fwd_slide_fuel_succ : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    nu S h ≤ k → slide fwdRule (k + 1) S X h = slide fwdRule k S X h := by
  intro k
  induction k with
  | zero =>
    intro S X h hh hk
    simp only [slide]
    rcases hc : fwdRule.ch S X h with _ | y
    · rfl
    · obtain ⟨hyS, hd⟩ := fwdChoice_step hc
      have := nu_move hyS hd
      omega
  | succ k ih =>
    intro S X h hh hk
    rw [slide]
    conv_rhs => rw [slide]
    rcases hc : fwdRule.ch S X h with _ | y
    · rfl
    · obtain ⟨hyS, hd⟩ := fwdChoice_step hc
      have hyh : y ≠ h := fun e => hh (e ▸ hyS)
      have hy' : y ∉ moveS S h y := by simp [moveS, hyh]
      have := nu_move hyS hd
      simp only
      rw [ih (moveS S h y) (moveX X h y) y hy' (by omega)]

theorem fwd_slide_fuel_add (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hh : h ∉ S) :
    ∀ n, slide fwdRule (nu S h + n) S X h = slide fwdRule (nu S h) S X h := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, fwd_slide_fuel_succ _ S X h hh (by omega), ih]

/-- **Forward fuel independence, one slide.** Any two fuels `≥ |S|` give the same slide. -/
theorem fwd_slide_fuel_eq (k k' : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hh : h ∉ S)
    (hk : S.card ≤ k) (hk' : S.card ≤ k') :
    slide fwdRule k S X h = slide fwdRule k' S X h := by
  have hnu : nu S h ≤ S.card := Finset.card_filter_le _ _
  have e1 := fwd_slide_fuel_add S X h hh (k - nu S h)
  have e2 := fwd_slide_fuel_add S X h hh (k' - nu S h)
  rw [show nu S h + (k - nu S h) = k by omega] at e1
  rw [show nu S h + (k' - nu S h) = k' by omega] at e2
  rw [e1, e2]

/-- **Forward fuel independence of `Σ`'s run.** Distinct holes avoiding the initial support:
any two fuels `≥ |S|` give the same run. `PhiOut.sigmaWith` runs at `|S| + Σκ + 1`, the window
form at `p + 1` with `p = |S|`. -/
theorem fwd_slides_fuel_eq (k k' : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    hs.Nodup → (∀ h ∈ hs, h ∉ S) → S.card ≤ k → S.card ≤ k' →
    slides fwdRule k S X hs = slides fwdRule k' S X hs := by
  intro hs
  induction hs with
  | nil => intro S X _ _ _ _; rfl
  | cons h hs ih =>
    intro S X hnd hS hk hk'
    have hh := hS h List.mem_cons_self
    have e := fwd_slide_fuel_eq k k' S X h hh hk hk'
    obtain ⟨sub, card⟩ := slide_support fwdRule k' S X h hh
    simp only [slides]
    rw [e]
    have hnd' := (List.nodup_cons.1 hnd)
    rw [ih _ _ hnd'.2 (fun h' hm hm' => ?_) (by rw [card]; exact hk) (by rw [card]; exact hk')]
    rcases Finset.mem_insert.1 (sub hm') with rfl | hm''
    · exact hnd'.1 hm
    · exact hS h' (List.mem_cons_of_mem _ hm) hm''

/-- **Gap 4 at `Σ`'s fuel.** `V_rowsW_of_slidesOK` holds at any fuel `k' ≥ |F|` (`SlidesOK` is
still taken at `|F| + 1`). -/
theorem V_rowsW_of_slidesOK_fuel (k' : ℕ) (U F : List Cell) (X : Cell → ℕ)
    (hnd : (U ++ F).Nodup) (hstd : ∀ a ∈ F, std F.toFinset X a = valOf F a)
    (hok : SlidesOK fwdRule (F.length + 1) F.toFinset X U.reverse) (hk' : F.length ≤ k') :
    (slides fwdRule k' F.toFinset X U.reverse).2.2 =
      ((rowsW F.length U.length (U ++ F)).drop F.length).reverse := by
  have hU : U.reverse.Nodup := List.nodup_reverse.2 (List.nodup_append.1 hnd).1
  have hdis : ∀ h ∈ U.reverse, h ∉ F.toFinset := fun h hm hF =>
    (List.nodup_append.1 hnd).2.2 h (List.mem_reverse.1 hm) h (List.mem_toFinset.1 hF) rfl
  have hcard : F.toFinset.card ≤ F.length := List.toFinset_card_le F
  rw [fwd_slides_fuel_eq k' (F.length + 1) U.reverse F.toFinset X hU hdis (by omega) (by omega)]
  exact V_rowsW_of_slidesOK U F X hnd hstd hok

/-- `Σ`'s hole order is the word `skewCells κ []` read backwards. -/
theorem sigmaHoles_eq (κ : List ℕ) : PhiOut.sigmaHoles κ = (PhiOut.skewCells κ []).reverse := by
  unfold PhiOut.sigmaHoles PhiOut.skewCells
  rw [List.reverse_flatMap]
  congr 1
  funext r
  simp [List.map_reverse]

/-! ### Control and lesion on `Σ`'s own run (kernel; these evaluate finite instances) -/

open TworowD4Kernel.PhiOut TworowD4Kernel.PhiOutData

/-- `Σ ∘ rr` (`PhiOut.sigmaRR`: support `rot(A/B)`, values `rr f`, holes `sigmaHoles κ`, fuel
`|S| + Σκ + 1`) vacates `(rowsW p |U| (Uo U ++ F)).drop p` reversed, where `U = skewCells κ []` and `F`
is Φ's hole list (`f̃`-order). With `Uo = id` this is the true form. -/
def sigCheckWith (Uo : List Cell → List Cell)
    (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  let R := d.1; let C := d.2.1; let A := d.2.2.1; let B := d.2.2.2.1
  let f := ofList d.2.2.2.2.1
  let cs := skewCells A B
  let S := (cs.map (rot R C)).toFinset
  let X := rr R C ((cs.map f).foldr max 0) f
  let κ := compl R C A
  let U := skewCells κ []
  let F := holesWith tilde R C A B f
  decide ((slides fwdRule (S.card + κ.sum + 1) S X (sigmaHoles κ)).2.2 =
    ((rowsW F.length U.length (Uo U ++ F)).drop F.length).reverse)

/-- The hypotheses of `V_rowsW_of_slidesOK_fuel` on the same instance; `F.toFinset = S` says
the word's support is `Σ`'s support. -/
def hypCheck (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  let R := d.1; let C := d.2.1; let A := d.2.2.1; let B := d.2.2.2.1
  let f := ofList d.2.2.2.2.1
  let cs := skewCells A B
  let S := (cs.map (rot R C)).toFinset
  let X := rr R C ((cs.map f).foldr max 0) f
  let κ := compl R C A
  let U := skewCells κ []
  let F := holesWith tilde R C A B f
  decide ((U ++ F).Nodup) && decide (F.toFinset = S) &&
  decide (∀ a ∈ F, std F.toFinset X a = valOf F a) &&
  decide (SlidesOK fwdRule (F.length + 1) F.toFinset X U.reverse)

/-- **Control (kernel).** On all 310 `phiData33` instances, the hypotheses of
`V_rowsW_of_slidesOK_fuel` hold, and `Σ`'s vacated cells equal the window form. -/
theorem sigma_rowsW_control_33 :
    phiData33.all hypCheck = true ∧ phiData33.all (sigCheckWith id) = true := by
  decide +kernel

/-- **Lesion (holes not reversed, kernel).** Feeding the window form `U.reverse` (so that it
processes `U` first-first, unlike `Σ`) fails on 211 instances. That is every instance with
`|U| ≥ 2`, the only ones where the order can matter. -/
theorem lesion_U_not_reversed :
    (phiData33.filter fun d => !sigCheckWith List.reverse d).length = 211 ∧
    (phiData33.filter fun d => 2 ≤ (skewCells (compl d.1 d.2.1 d.2.2.1) []).length).length = 211 ∧
    (phiData33.filter fun d => 2 ≤ (skewCells (compl d.1 d.2.1 d.2.2.1) []).length ∧
      sigCheckWith List.reverse d).length = 0 := by
  decide +kernel

end TworowD4Kernel.RowsSlidesBridge
