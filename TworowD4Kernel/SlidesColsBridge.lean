/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.StdSlideBridge
import TworowD4Kernel.SlideIteration

/-!
# G4 glue: `StdSlide.slides revRule` (iterated over holes) = `SlideIteration.colsW` (window form)

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `def:phi` item 3 (l.98–106) and
`lem:D` (l.172–198). The tex runs the outward procedure in two representations without comment:

* **filling form** (`StdSlide.slides revRule k S X hs`, used by `PhiOut.phi` and `lemmaA_slides`):
  a support `S` with values `X`, the holes `hs = F_1, …, F_p` slid into one after another;
* **window form** (`SlideIteration.colsW m 0 p w`, used by `lemmaD_slides`): the cell word
  `w = U_1 … U_m F_1 … F_p`; step `c` slides `F_{c+1}` (cell `c+m`) backward through the `m`
  cells at positions `c, …, c+m−1` and writes the vacated cell at position `c`.

`slides_colsW` (main): if `U ++ F` has no repeated cell and `X = valOf U` on `U` (entry `i+1` at
`U[i]`), then with fuel `m+1` per slide (the fuel of `revSlideW`)

  `colsW m c p (A ++ U ++ F) = A ++ V ++ U'`,

where `V` is the vacated-cell list of `slides` and `U'` is a cell word whose support and values are
the final support and values of `slides`. `slides_colsW_take` is the `c = 0` reading:
`V = (colsW m 0 p (U ++ F)).take p`.

`V_colsW_of_slidesOK` composes with `lemmaA_slides revRule`: under the named hypothesis
`SlidesOK revRule (m+1) S X F` (column-injectivity along the run, the recalled Fulton fact), a
semistandard `X` whose standardisation is the word `U` vacates the cells `(colsW …).take p`.

Fuel: `PhiOut.phi` runs at fuel `R + C`, `colsW` at `m + 1`. `slides_fuel_eq` shows a reverse
run is fuel-independent once the fuel covers `|S|` or every hole's anti-diagonal index `r + c`
(each reverse move lowers `r + c` by one and the count of support cells below the hole's
anti-diagonal by at least one), giving `V_colsW_of_slidesOK_fuel`.
-/

namespace TworowD4Kernel.SlidesColsBridge
open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.SlideIteration

/-! ### Small facts about `jdtRev` and `slides` -/

theorem jdtRev_length_nodup : ∀ (k : ℕ) (w : List Cell) (h : Cell), w.Nodup → h ∉ w →
    (jdtRev true k w h).1.length = w.length ∧ (jdtRev true k w h).1.Nodup := by
  intro k
  induction k with
  | zero => intro w h hw _; exact ⟨rfl, hw⟩
  | succ k ih =>
    intro w h hw hh
    simp only [jdtRev]
    rcases hs : jdtStepRev true w h with _ | ⟨w', y⟩
    · exact ⟨rfl, hw⟩
    · obtain ⟨-, -, -, hw', hy'⟩ := jdtStepRev_bridge w hw h hh hs
      obtain ⟨-, rfl⟩ := jdtStepRev_move w h hs
      obtain ⟨l, n⟩ := ih _ y hw' hy'
      exact ⟨by rw [l, List.length_set], n⟩

theorem slides_length (R : Rule) (k : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    (slides R k S X hs).2.2.length = hs.length := by
  intro hs
  induction hs with
  | nil => intro S X; rfl
  | cons h hs ih => intro S X; simp [slides, ih]

/-- On a nodup word, the reverse-word value of `U.reverse` is the forward value of `U`. -/
lemma valDec_reverse {U : List Cell} (hU : U.Nodup) {a : Cell} (ha : a ∈ U) :
    valDec U.reverse a = valOf U a := by
  unfold valDec valOf
  rw [List.length_reverse]
  have hi : U.idxOf a < U.length := List.idxOf_lt_length_iff.2 ha
  -- index of `a` in the reverse list
  have hr : U.reverse.idxOf a = U.length - 1 - U.idxOf a := by
    have hlt : U.length - 1 - U.idxOf a < U.reverse.length := by simp; omega
    have hget : U.reverse[U.length - 1 - U.idxOf a] = a := by
      rw [List.getElem_reverse]
      simp only [show U.length - 1 - (U.length - 1 - U.idxOf a) = U.idxOf a by omega]
      exact List.getElem_idxOf hi
    calc U.reverse.idxOf a = U.reverse.idxOf U.reverse[U.length - 1 - U.idxOf a] := by rw [hget]
      _ = U.length - 1 - U.idxOf a := List.Nodup.idxOf_getElem (List.nodup_reverse.2 hU) _ hlt
  rw [hr]; omega

/-! ### One window step -/

/-- **One step.** The reverse slide of the hole `h` into the filling `(U, X)` with `X = valOf U`
on `U` is the window step of `colsW`: vacated cell `z`, new word `U'` with the slide's final
support and values. -/
theorem slide_eq_revSlideW (U : List Cell) (h : Cell) (hU : U.Nodup) (hh : h ∉ U)
    (X : Cell → ℕ) (hX : ∀ a ∈ U, X a = valOf U a) :
    let r := slide revRule (U.length + 1) U.toFinset X h
    revSlideW h U = r.2.2.1 :: (jdtRev true (U.length + 1) U.reverse h).1.reverse ∧
    (jdtRev true (U.length + 1) U.reverse h).1.reverse.toFinset = r.1 ∧
    (∀ a ∈ r.1, r.2.1 a = valOf (jdtRev true (U.length + 1) U.reverse h).1.reverse a) ∧
    (jdtRev true (U.length + 1) U.reverse h).1.reverse.length = U.length ∧
    (jdtRev true (U.length + 1) U.reverse h).1.reverse.Nodup := by
  intro r
  have hUr : U.reverse.Nodup := List.nodup_reverse.2 hU
  have hhr : h ∉ U.reverse := by simpa using hh
  obtain ⟨b1, b2, b3⟩ := jdtRev_bridge (U.length + 1) U.reverse h hUr hhr
  have hfin : U.reverse.toFinset = U.toFinset := by ext; simp
  rw [hfin] at b1 b2 b3
  -- swap the starting values `valDec U.reverse` for `X`
  obtain ⟨c1, c2, c3⟩ := slide_congr revRule (U.length + 1) U.toFinset X (valDec U.reverse) h
    (fun a ha => by rw [hX a (List.mem_toFinset.1 ha), valDec_reverse hU (List.mem_toFinset.1 ha)])
  obtain ⟨l, n⟩ := jdtRev_length_nodup (U.length + 1) U.reverse h hUr hhr
  set W := (jdtRev true (U.length + 1) U.reverse h).1 with hW
  refine ⟨?_, ?_, ?_, by simp [l], List.nodup_reverse.2 n⟩
  · unfold revSlideW; rw [b1, ← c2]
  · rw [List.toFinset_reverse, b2, ← c1]
  · intro a ha
    have ha' : a ∈ (slide revRule (U.length + 1) U.toFinset (valDec U.reverse) h).1 := c1 ▸ ha
    have haW : a ∈ W := by rw [← List.mem_toFinset, b2]; exact ha'
    have e := valDec_reverse (List.nodup_reverse.2 n) (List.mem_reverse.2 haW)
    rw [List.reverse_reverse] at e
    rw [c3 a ha, ← b3 a ha', e]

theorem jdtRev_mem : ∀ (k : ℕ) (w : List Cell) (h : Cell), ∀ a ∈ (jdtRev true k w h).1,
    a ∈ w ∨ a = h := by
  intro k
  induction k with
  | zero => intro w h a ha; exact Or.inl ha
  | succ k ih =>
    intro w h a ha
    simp only [jdtRev] at ha
    rcases hs : jdtStepRev true w h with _ | ⟨w', y⟩
    · rw [hs] at ha; exact Or.inl ha
    · rw [hs] at ha
      obtain ⟨hyw, rfl⟩ := jdtStepRev_move w h hs
      rcases ih _ y a ha with ha | rfl
      · rcases List.mem_or_eq_of_mem_set ha with ha | rfl
        · exact Or.inl ha
        · exact Or.inr rfl
      · exact Or.inl hyw

/-! ### The window form, iterated -/

/-- **Glue lemma (`slides` ↔ `colsW`).** Let `U ++ F` be a cell word without repetitions,
`|U| = m`, and let `X` agree with `valOf U` on `U`. Then for any prefix `A`, the outward
procedure in window form, started at position `|A|`, gives `A ++ V ++ U'`, where `V` is the
list of vacated cells of the filling-form run `slides revRule (m+1) U X F`, and the word `U'`
has that run's final support and final values. -/
theorem slides_colsW (m : ℕ) : ∀ (F A U : List Cell) (X : Cell → ℕ), U.length = m →
    (U ++ F).Nodup → (∀ a ∈ U, X a = valOf U a) →
    ∃ U' : List Cell,
      colsW m A.length F.length (A ++ (U ++ F)) =
        A ++ ((slides revRule (m + 1) U.toFinset X F).2.2 ++ U') ∧
      U'.toFinset = (slides revRule (m + 1) U.toFinset X F).1 ∧
      (∀ a ∈ (slides revRule (m + 1) U.toFinset X F).1,
        (slides revRule (m + 1) U.toFinset X F).2.1 a = valOf U' a) ∧
      U'.length = m := by
  intro F
  induction F with
  | nil =>
    intro A U X hm _ hX
    refine ⟨U, by simp [colsW, slides], by simp [slides], fun a ha => hX a ?_, hm⟩
    simpa [slides] using ha
  | cons h F ih =>
    intro A U X hm hnd hX
    subst hm
    have hU : U.Nodup := (List.nodup_append.1 hnd).1
    have hhF : (h :: F).Nodup := (List.nodup_append.1 hnd).2.1
    have hdisj : ∀ a ∈ U, ∀ b ∈ h :: F, a ≠ b := by
      intro a ha b hb; exact (List.nodup_append.1 hnd).2.2 a ha b hb
    have hh : h ∉ U := fun hm => hdisj h hm h List.mem_cons_self rfl
    obtain ⟨e1, e2, e3, e4, e5⟩ := slide_eq_revSlideW U h hU hh X hX
    set r := slide revRule (U.length + 1) U.toFinset X h with hr
    set U1 := (jdtRev true (U.length + 1) U.reverse h).1.reverse with hU1
    -- cells of `U1` lie in `U ∪ {h}`, so they avoid `F`
    have hU1mem : ∀ a ∈ U1, a ∈ U ∨ a = h := by
      intro a ha
      rcases jdtRev_mem _ U.reverse h a (List.mem_reverse.1 ha) with ha | ha
      · exact Or.inl (List.mem_reverse.1 ha)
      · exact Or.inr ha
    have hF : F.Nodup := (List.nodup_cons.1 hhF).2
    have hnd' : (U1 ++ F).Nodup := by
      refine List.nodup_append.2 ⟨e5, hF, fun a ha b hb => ?_⟩
      rcases hU1mem a ha with ha | rfl
      · exact hdisj a ha b (List.mem_cons_of_mem _ hb)
      · rintro rfl; exact (List.nodup_cons.1 hhF).1 hb
    have hX1 : ∀ a ∈ U1, r.2.1 a = valOf U1 a := by
      intro a ha; exact e3 a (e2 ▸ List.mem_toFinset.2 ha)
    obtain ⟨U', i1, i2, i3, i4⟩ := ih (A ++ [r.2.2.1]) U1 r.2.1 e4 hnd' hX1
    rw [e2] at i1 i2 i3
    refine ⟨U', ?_, ?_, ?_, i4⟩
    · -- unfold one window step of `colsW`
      have t1 : (A ++ (U ++ h :: F)).take A.length = A := by simp
      have t2 : ((A ++ (U ++ h :: F)).drop A.length).take U.length = U := by simp
      have t3 : (A ++ (U ++ h :: F)).getD (A.length + U.length) (0, 0) = h := by
        simp [List.getD_eq_getElem?_getD]
      have t4 : (A ++ (U ++ h :: F)).drop (A.length + U.length + 1) = F := by
        rw [show A.length + U.length + 1 = (A ++ (U ++ [h])).length by simp; omega]
        simp
      rw [List.length_cons, colsW, t1, t2, t3, t4, e1]
      have hw : A ++ (r.2.2.1 :: U1 ++ F) = (A ++ [r.2.2.1]) ++ (U1 ++ F) := by simp
      rw [hw, show A.length + 1 = (A ++ [r.2.2.1]).length by simp, i1]
      simp [slides, hr]
    · simpa [slides, hr] using i2
    · intro a ha
      simpa [slides, hr] using i3 a (by simpa [slides, hr] using ha)

/-- **Glue, `c = 0` reading.** For a nodup word `U ++ F` with `|U| = m`, `|F| = p` and `X = valOf U`
on `U`: the vacated cells of `slides revRule (m+1) U X F` are the first `p` cells of
`colsW m 0 p (U ++ F)`, and the remaining `m` cells form a word with the final support and
values of the run. -/
theorem slides_colsW_take (m : ℕ) (U F : List Cell) (X : Cell → ℕ) (hm : U.length = m)
    (hnd : (U ++ F).Nodup) (hX : ∀ a ∈ U, X a = valOf U a) :
    (slides revRule (m + 1) U.toFinset X F).2.2 = (colsW m 0 F.length (U ++ F)).take F.length ∧
    ((colsW m 0 F.length (U ++ F)).drop F.length).toFinset =
      (slides revRule (m + 1) U.toFinset X F).1 ∧
    ∀ a ∈ (slides revRule (m + 1) U.toFinset X F).1,
      (slides revRule (m + 1) U.toFinset X F).2.1 a =
        valOf ((colsW m 0 F.length (U ++ F)).drop F.length) a := by
  obtain ⟨U', h1, h2, h3, -⟩ := slides_colsW m F [] U X hm hnd hX
  simp only [List.nil_append, List.length_nil] at h1
  have hl := slides_length revRule (m + 1) F U.toFinset X
  rw [h1]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.take_left' hl]
  · rw [List.drop_left' hl, h2]
  · intro a ha; rw [List.drop_left' hl, h3 a ha]

/-- **Glue under `SlidesOK` (the session target).** Let the semistandard filling `(S, X)` be
column-injective along the whole outward run (`SlidesOK revRule (m+1) S X F`, the named
hypothesis: the recalled Fulton fact that jdt preserves column strictness), and let its
standardisation be the cell word `U` (`std S X = valOf U` on `S = U.toFinset`). Then the
cells vacated by the run on `X` are the first `|F|` cells of the window-form outward procedure
`colsW m 0 |F| (U ++ F)`. Proof: `lemmaA_slides revRule` (X ↦ std X), then `slides_colsW_take`. -/
theorem V_colsW_of_slidesOK (m : ℕ) (U F : List Cell) (X : Cell → ℕ) (hm : U.length = m)
    (hnd : (U ++ F).Nodup) (hstd : ∀ a ∈ U, std U.toFinset X a = valOf U a)
    (hok : SlidesOK revRule (m + 1) U.toFinset X F) :
    (slides revRule (m + 1) U.toFinset X F).2.2 = (colsW m 0 F.length (U ++ F)).take F.length := by
  rw [← (lemmaA_slides revRule (m + 1) F U.toFinset X hok).1]
  exact (slides_colsW_take m U F (std U.toFinset X) hm hnd hstd).1

/-! ### Fuel independence (`PhiOut.phi` runs at fuel `R + C`, `colsW` at `m + 1`) -/

/-- Anti-diagonal index of a cell. -/
def dsum (y : Cell) : ℕ := y.1 + y.2

/-- Support cells strictly below the hole's anti-diagonal. -/
def mu (S : Finset Cell) (h : Cell) : ℕ := (S.filter fun s => dsum s < dsum h).card

lemma revChoice_step {S : Finset Cell} {X : Cell → ℕ} {h y : Cell} (hh : h ∉ S)
    (hc : revRule.ch S X h = some y) : y ∈ S ∧ dsum y + 1 = dsum h := by
  have hyS := revRule.mem S X h y hc
  refine ⟨hyS, ?_⟩
  have hc' : revChoice S X h = some y := hc
  unfold revChoice at hc'
  have hyh : y ≠ h := fun e => hh (e ▸ hyS)
  obtain ⟨a, b⟩ := h
  split_ifs at hc' <;> (simp only [Option.some.injEq] at hc') <;> subst hc' <;>
    (simp only [nS, nW, dsum] at hyh ⊢; by_contra hne; apply hyh; ext <;> simp <;> omega)

lemma mu_move {S : Finset Cell} {h y : Cell} (hyS : y ∈ S) (hd : dsum y + 1 = dsum h) :
    mu (moveS S h y) y + 1 ≤ mu S h := by
  unfold mu moveS
  rw [Finset.filter_insert, if_neg (by omega)]
  have hsub : (S.erase y).filter (fun s => dsum s < dsum y) ⊆
      (S.filter fun s => dsum s < dsum h).erase y := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_erase] at hs ⊢
    exact ⟨hs.1.1, hs.1.2, by omega⟩
  have hy : y ∈ S.filter fun s => dsum s < dsum h := Finset.mem_filter.2 ⟨hyS, by omega⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hy] at this
  have := Finset.card_pos.2 ⟨y, hy⟩
  omega

/-- **Fuel stability.** Once the fuel covers either the number of support cells below the hole's
anti-diagonal or the anti-diagonal index itself, one more unit of fuel changes nothing. -/
theorem slide_fuel_succ : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    (mu S h ≤ k ∨ dsum h ≤ k) → slide revRule (k + 1) S X h = slide revRule k S X h := by
  intro k
  induction k with
  | zero =>
    intro S X h hh hk
    simp only [slide]
    rcases hc : revRule.ch S X h with _ | y
    · rfl
    · obtain ⟨hyS, hd⟩ := revChoice_step hh hc
      have := mu_move hyS hd
      omega
  | succ k ih =>
    intro S X h hh hk
    rw [slide]
    conv_rhs => rw [slide]
    rcases hc : revRule.ch S X h with _ | y
    · rfl
    · obtain ⟨hyS, hd⟩ := revChoice_step hh hc
      have hyh : y ≠ h := fun e => hh (e ▸ hyS)
      have hy' : y ∉ moveS S h y := by simp [moveS, hyh]
      have := mu_move hyS hd
      simp only
      rw [ih (moveS S h y) (moveX X h y) y hy' (by omega)]
theorem slide_fuel_add (b : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hh : h ∉ S)
    (hb : mu S h ≤ b ∨ dsum h ≤ b) : ∀ n, slide revRule (b + n) S X h = slide revRule b S X h := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, slide_fuel_succ _ S X h hh (by omega), ih]

/-- **Fuel independence of one reverse slide.** Fuel `≥ |S|` and fuel `≥` the hole's
anti-diagonal index give the same slide. -/
theorem slide_fuel_eq (k k' : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hh : h ∉ S)
    (hk : S.card ≤ k) (hk' : dsum h ≤ k') :
    slide revRule k S X h = slide revRule k' S X h := by
  have hmu : mu S h ≤ S.card := Finset.card_filter_le _ _
  have e1 := slide_fuel_add (mu S h) S X h hh (Or.inl le_rfl) (k - mu S h)
  have e2 := slide_fuel_add (dsum h) S X h hh (Or.inr le_rfl) (k' - dsum h)
  have e3 := slide_fuel_add (mu S h) S X h hh (Or.inl le_rfl) (max k k' - mu S h)
  have e4 := slide_fuel_add (dsum h) S X h hh (Or.inr le_rfl) (max k k' - dsum h)
  rw [show mu S h + (k - mu S h) = k by omega] at e1
  rw [show dsum h + (k' - dsum h) = k' by omega] at e2
  rw [show mu S h + (max k k' - mu S h) = max k k' by omega] at e3
  rw [show dsum h + (max k k' - dsum h) = max k k' by omega] at e4
  rw [e1, e2, ← e3, ← e4]

/-- A slide keeps the support inside `S ∪ {h}` and keeps its size. -/
theorem slide_support (R : Rule) : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    (slide R k S X h).1 ⊆ insert h S ∧ (slide R k S X h).1.card = S.card := by
  intro k
  induction k with
  | zero => intro S X h _; exact ⟨Finset.subset_insert _ _, rfl⟩
  | succ k ih =>
    intro S X h hh
    simp only [slide]
    rcases hc : R.ch S X h with _ | y
    · exact ⟨Finset.subset_insert _ _, rfl⟩
    · have hyS := R.mem S X h y hc
      have hyh : y ≠ h := fun e => hh (e ▸ hyS)
      have hy' : y ∉ moveS S h y := by simp [moveS, hyh]
      obtain ⟨i1, i2⟩ := ih (moveS S h y) (moveX X h y) y hy'
      refine ⟨fun a ha => ?_, ?_⟩
      · have := i1 ha
        simp only [moveS, Finset.mem_insert, Finset.mem_erase] at this ⊢
        rcases this with rfl | rfl | ⟨-, ha⟩
        · exact Or.inr hyS
        · exact Or.inl rfl
        · exact Or.inr ha
      · rw [i2, moveS, Finset.card_insert_of_notMem (by simp [hh]),
          Finset.card_erase_of_mem hyS]
        have := Finset.card_pos.2 ⟨y, hyS⟩
        omega

/-- **Fuel independence of the outward run.** If the holes are distinct and avoid the initial
support, fuel `≥ |S|` and fuel `≥` every hole's anti-diagonal index give the same run. -/
theorem slides_fuel_eq (k k' : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    hs.Nodup → (∀ h ∈ hs, h ∉ S) → S.card ≤ k → (∀ h ∈ hs, dsum h ≤ k') →
    slides revRule k S X hs = slides revRule k' S X hs := by
  intro hs
  induction hs with
  | nil => intro S X _ _ _ _; rfl
  | cons h hs ih =>
    intro S X hnd hS hk hk'
    have hh := hS h List.mem_cons_self
    have e := slide_fuel_eq k k' S X h hh hk (hk' h List.mem_cons_self)
    obtain ⟨sub, card⟩ := slide_support revRule k' S X h hh
    simp only [slides]
    rw [e]
    have hnd' := (List.nodup_cons.1 hnd)
    rw [ih _ _ hnd'.2 (fun h' hm hm' => ?_) (by rw [card]; exact hk)
      (fun h' hm => hk' h' (List.mem_cons_of_mem _ hm))]
    rcases Finset.mem_insert.1 (sub hm') with rfl | hm''
    · exact hnd'.1 hm
    · exact hS h' (List.mem_cons_of_mem _ hm) hm''


/-- **Glue under `SlidesOK`, any fuel covering the anti-diagonals.** The conclusion of
`V_colsW_of_slidesOK` holds for the outward run at any fuel `k'` that is at least every hole's
anti-diagonal index `r + c` (e.g. `PhiOut.phi`'s fuel `R + C` for holes in the `R × C` box).
`SlidesOK` is still taken at fuel `m + 1`. -/
theorem V_colsW_of_slidesOK_fuel (m k' : ℕ) (U F : List Cell) (X : Cell → ℕ) (hm : U.length = m)
    (hnd : (U ++ F).Nodup) (hstd : ∀ a ∈ U, std U.toFinset X a = valOf U a)
    (hok : SlidesOK revRule (m + 1) U.toFinset X F) (hk' : ∀ h ∈ F, dsum h ≤ k') :
    (slides revRule k' U.toFinset X F).2.2 = (colsW m 0 F.length (U ++ F)).take F.length := by
  have hF : F.Nodup := (List.nodup_append.1 hnd).2.1
  have hdis : ∀ h ∈ F, h ∉ U.toFinset := fun h hm hU =>
    (List.nodup_append.1 hnd).2.2 h (List.mem_toFinset.1 hU) h hm rfl
  have hcard : U.toFinset.card ≤ m + 1 := by
    have := List.toFinset_card_le U; omega
  rw [← slides_fuel_eq (m + 1) k' F U.toFinset X hF hdis hcard hk']
  exact V_colsW_of_slidesOK m U F X hm hnd hstd hok

/-! ### Controls and lesions (kernel `decide`) -/

/-- **Control (non-vacuity).** `U = [(0,0)]`, `F = [(0,1),(1,0)]`: the hypotheses hold, the run
makes a genuine move (the first hole slides west into `(0,0)`), and `V` is the first two cells
of `colsW`, as `slides_colsW_take` says. -/
theorem control_take :
    ([(0, 0), (0, 1), (1, 0)] : List Cell).Nodup ∧
    (slides revRule 2 ([(0, 0)] : List Cell).toFinset (valOf [(0, 0)]) [(0, 1), (1, 0)]).2.2 =
      [(0, 0), (1, 0)] ∧
    (colsW 1 0 2 ([(0, 0), (0, 1), (1, 0)] : List Cell)).take 2 = [(0, 0), (1, 0)] := by
  decide +kernel

/-- **Lesion (hole order reversed).** Feeding `slides` the holes `F` in reverse order breaks
the glue on the control instance: it vacates `[(0,0),(0,1)]`, not `colsW`'s `[(0,0),(1,0)]`. -/
theorem lesion_hole_order_reversed :
    (slides revRule 2 ([(0, 0)] : List Cell).toFinset (valOf [(0, 0)]) [(1, 0), (0, 1)]).2.2 ≠
      (colsW 1 0 2 ([(0, 0), (0, 1), (1, 0)] : List Cell)).take 2 := by
  decide +kernel

/-- **Lesion (values read backwards).** The hypothesis `X = valOf U` is used: with the
reverse-word values `valDec U` (entry order flipped) the hole `(1,1)` takes south instead of
west, and the glue fails. -/
theorem lesion_values_reversed :
    (slides revRule 3 ([(0, 1), (1, 0)] : List Cell).toFinset (valOf [(0, 1), (1, 0)])
        [(1, 1)]).2.2 = (colsW 2 0 1 ([(0, 1), (1, 0), (1, 1)] : List Cell)).take 1 ∧
    (slides revRule 3 ([(0, 1), (1, 0)] : List Cell).toFinset (valDec [(0, 1), (1, 0)])
        [(1, 1)]).2.2 ≠ (colsW 2 0 1 ([(0, 1), (1, 0), (1, 1)] : List Cell)).take 1 := by
  decide +kernel

/-- **Lesion (fuel below both bounds).** At fuel `1` the holes `(0,1)`, `(1,0)` have
anti-diagonal index `1`, so `slides_fuel_eq`'s hypothesis `r + c ≤ k'` holds and the run agrees
with `colsW`; at fuel `0` (below every bound) nothing moves and the glue fails. -/
theorem lesion_fuel_zero :
    (slides revRule 1 ([(0, 0)] : List Cell).toFinset (valOf [(0, 0)]) [(0, 1), (1, 0)]).2.2 =
      (colsW 1 0 2 ([(0, 0), (0, 1), (1, 0)] : List Cell)).take 2 ∧
    (slides revRule 0 ([(0, 0)] : List Cell).toFinset (valOf [(0, 0)]) [(0, 1), (1, 0)]).2.2 ≠
      (colsW 1 0 2 ([(0, 0), (0, 1), (1, 0)] : List Cell)).take 2 := by
  decide +kernel

end TworowD4Kernel.SlidesColsBridge
