/-
G4 assembly, links L3 and L4 (LEAN 2026-11-22): the tilde-rank lemma.

`holesWith t R C A B f` lists, for `j = 0, 1, …, |cs|−1`, the first rotated cell `y` with
`t y = j`. It enumerates the rotated support in rank order **iff** the rank is injective there;
for `t = tilde` that is column-strictness of `f` on `A/B` (the paper's standing hypothesis
that `f` is semistandard, `def:phi`(1) in `proofs/2026-11-13c2-Q585-G4-evacuation.tex`).

* `rankList_spec` (generic): for a list `rc` and `r : Cell → ℕ` injective on `rc` with values
  `< n = |rc.toFinset|`, the list `L = (range n).filterMap (j ↦ rc.find? (r · = j))` has
  `L.toFinset = rc.toFinset` and `L.idxOf y = r y` for `y ∈ rc`.
-/
import TworowD4Kernel.PhiOut
import TworowD4Kernel.StdSlideBridge

namespace TworowD4Kernel.RankList

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOut
open TworowD4Kernel.StdSlideBridge

/-- The rank list of `rc` under `r`. -/
def rankList (rc : List Cell) (r : Cell → ℕ) (n : ℕ) : List Cell :=
  (List.range n).filterMap fun j => rc.find? fun y => r y = j

/-- **Tilde-rank lemma, generic form.** -/
theorem rankList_spec (rc : List Cell) (r : Cell → ℕ) (n : ℕ)
    (hn : rc.toFinset.card = n) (hlt : ∀ y ∈ rc, r y < n)
    (hinj : ∀ a ∈ rc, ∀ b ∈ rc, r a = r b → a = b) :
    (rankList rc r n).toFinset = rc.toFinset ∧
      ∀ y ∈ rc, (rankList rc r n).idxOf y = r y := by
  -- surjectivity onto `range n`, by cardinality
  have hsurj : ∀ j < n, ∃ y ∈ rc, r y = j := by
    have hsub : rc.toFinset.image r ⊆ Finset.range n := by
      intro j hj; obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.mem_range.2 (hlt y (List.mem_toFinset.1 hy))
    have hcard : (Finset.range n).card ≤ (rc.toFinset.image r).card := by
      rw [Finset.card_range, Finset.card_image_of_injOn, hn]
      intro a ha b hb e
      exact hinj a (List.mem_toFinset.1 ha) b (List.mem_toFinset.1 hb) e
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    intro j hj
    have : j ∈ rc.toFinset.image r := heq ▸ Finset.mem_range.2 hj
    obtain ⟨y, hy, e⟩ := Finset.mem_image.1 this
    exact ⟨y, List.mem_toFinset.1 hy, e⟩
  -- the found cell
  let g : ℕ → Cell := fun j => (rc.find? fun y => r y = j).getD (0, 0)
  have hfind : ∀ j < n, rc.find? (fun y => r y = j) = some (g j) := by
    intro j hj
    obtain ⟨y, hy, e⟩ := hsurj j hj
    rcases h : rc.find? (fun y => decide (r y = j)) with _ | z
    · exfalso
      have := List.find?_eq_none.1 h y hy
      simp [e] at this
    · simp [g, h]
  have hg : ∀ j < n, g j ∈ rc ∧ r (g j) = j := by
    intro j hj
    have h := hfind j hj
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  have hL : rankList rc r n = (List.range n).map g := by
    unfold rankList
    rw [← List.filterMap_eq_map]
    apply List.filterMap_congr
    intro j hj
    exact hfind j (List.mem_range.1 hj)
  have hgy : ∀ y ∈ rc, g (r y) = y := fun y hy =>
    hinj _ (hg _ (hlt y hy)).1 y hy (hg _ (hlt y hy)).2
  have hnd : ((List.range n).map g).Nodup := by
    refine (List.nodup_range).map_on ?_
    intro a ha b hb e
    rw [← (hg a (List.mem_range.1 ha)).2, ← (hg b (List.mem_range.1 hb)).2, e]
  rw [hL]
  refine ⟨?_, ?_⟩
  · ext y
    simp only [List.mem_toFinset, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact (hg j hj).1
    · intro hy; exact ⟨r y, hlt y hy, hgy y hy⟩
  · intro y hy
    have hj : r y < ((List.range n).map g).length := by simpa using hlt y hy
    have e : ((List.range n).map g)[r y] = y := by simpa using hgy y hy
    have := hnd.idxOf_getElem (r y) hj
    rwa [e] at this

/-! ## Specialisation to `holesWith tilde` -/

lemma map_toFinset (l : List Cell) (φ : Cell → Cell) : (l.map φ).toFinset = l.toFinset.image φ := by
  ext y; simp

theorem skewCells_nodup' (A B : List ℕ) : (skewCells A B).Nodup := by
  unfold skewCells
  rw [List.nodup_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · refine ((List.nodup_range).filter _).map_on ?_
    intro a _ b _ e; simpa using e
  · refine (List.pairwise_lt_range).imp ?_
    intro r s hrs
    simp only [Function.onFun, List.disjoint_left, List.mem_map]
    rintro y ⟨c, _, rfl⟩ ⟨c', _, e⟩
    simp at e; omega

lemma le_foldr_max (l : List ℕ) : ∀ x ∈ l, x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    intro x hx
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_max_left _ _
    · exact (ih x hx).trans (le_max_right _ _)

/-- `ColInj` transports along the rotation (values `≤ ℓ`, cells in the box). -/
lemma colInj_rr (R C ℓ : ℕ) (S : Finset Cell) (f : Cell → ℕ) (hS : InBox R C S)
    (hf : ∀ Y ∈ S, f Y ≤ ℓ) (hcol : ColInj S f) :
    ColInj (S.image (rot R C)) (rr R C ℓ f) := by
  intro a ha b hb hc hv
  obtain ⟨X, hX, rfl⟩ := Finset.mem_image.1 ha
  obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.1 hb
  have hXb := hS X hX; have hYb := hS Y hY
  simp only [rr, rot_rot hXb, rot_rot hYb] at hv
  have h1 := hf X hX; have h2 := hf Y hY
  have hc' : X.2 = Y.2 := by simp only [rot] at hc; omega
  rw [hcol X hX Y hY hc' (by omega)]

/-- `std` is injective on `S` when `X` is column-injective there. -/
lemma std_injOn (S : Finset Cell) (X : Cell → ℕ) (hcol : ColInj S X) :
    ∀ a ∈ S, ∀ b ∈ S, std S X a = std S X b → a = b := by
  intro a ha b hb e
  rcases lt_trichotomy (key X a) (key X b) with h | h | h
  · exact absurd e (ne_of_lt ((std_lt_iff S X ha).2 h))
  · simp only [key, toLex_inj, Prod.mk.injEq] at h
    exact hcol a ha b hb h.2 h.1
  · exact absurd e (ne_of_gt ((std_lt_iff S X hb).2 h))

lemma std_lt_card (S : Finset Cell) (X : Cell → ℕ) {a : Cell} (ha : a ∈ S) :
    std S X a < S.card := by
  unfold std
  refine Finset.card_lt_card ⟨Finset.filter_subset _ _, fun h => ?_⟩
  have := Finset.mem_filter.1 (h ha); exact lt_irrefl _ this.2

/-- `holesWith tilde` is the rank list of the rotated cells under `tilde`. -/
lemma holesWith_eq_rankList (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ) :
    holesWith tilde R C A B f =
      rankList ((skewCells A B).map (rot R C)) (tilde R C (skewCells A B).toFinset f)
        (skewCells A B).length := rfl

/-- **Tilde-rank lemma (L3 + L4 core).** If `A/B` lies in the `R × C` box and `f` is
column-strict on it (tex `def:phi`(1): `f` semistandard), then the hole list of Φ enumerates the
rotated support `rot(A/B)`, and each hole's position in the list is its `tilde`-rank, which equals
`std (rr f)` (Lemma C, `lem:C`). -/
theorem holesWith_spec (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset) (hcol : ColInj (skewCells A B).toFinset f) :
    (holesWith tilde R C A B f).toFinset = ((skewCells A B).map (rot R C)).toFinset ∧
    ∀ y ∈ (skewCells A B).map (rot R C), (holesWith tilde R C A B f).idxOf y =
      std ((skewCells A B).map (rot R C)).toFinset
        (rr R C (((skewCells A B).map f).foldr max 0) f) y := by
  set cs := skewCells A B
  set S := cs.toFinset
  set ℓ := (cs.map f).foldr max 0
  have hf : ∀ Y ∈ S, f Y ≤ ℓ := fun Y hY =>
    le_foldr_max _ _ (List.mem_map.2 ⟨Y, List.mem_toFinset.1 hY, rfl⟩)
  have hT : (cs.map (rot R C)).toFinset = S.image (rot R C) := map_toFinset _ _
  have hC := lemmaC R C ℓ S f hbox hf
  have hinjRot : Set.InjOn (rot R C) S := fun a ha b hb e => by
    rw [← rot_rot (hbox a ha), ← rot_rot (hbox b hb)]; exact congrArg _ e
  have hcard : (S.image (rot R C)).card = cs.length := by
    rw [Finset.card_image_of_injOn hinjRot, List.toFinset_card_of_nodup (skewCells_nodup' A B)]
  have hci := colInj_rr R C ℓ S f hbox hf hcol
  have hmem : ∀ y ∈ cs.map (rot R C), y ∈ S.image (rot R C) := fun y hy => by
    rw [← hT]; exact List.mem_toFinset.2 hy
  have hspec := rankList_spec (cs.map (rot R C)) (tilde R C S f) cs.length (by rw [hT, hcard])
    (fun y hy => by
      rw [← hC y (hmem y hy), ← hcard]; exact std_lt_card _ _ (hmem y hy))
    (fun a ha b hb e => by
      rw [← hC a (hmem a ha), ← hC b (hmem b hb)] at e
      exact std_injOn _ _ hci a (hmem a ha) b (hmem b hb) e)
  rw [holesWith_eq_rankList]
  refine ⟨hspec.1, fun y hy => ?_⟩
  rw [hspec.2 y hy, hT, hC y (hmem y hy)]

/-- **L3.** Φ's hole list enumerates `Σ`'s support `rot(A/B)`. -/
theorem L3_holes_toFinset (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset) (hcol : ColInj (skewCells A B).toFinset f) :
    (holesWith tilde R C A B f).toFinset = ((skewCells A B).map (rot R C)).toFinset :=
  (holesWith_spec R C A B f hbox hcol).1

/-- **L4.** On the hole list `F`, `std (rr f) = valOf F` (position in `F`). -/
theorem L4_std_eq_valOf (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset) (hcol : ColInj (skewCells A B).toFinset f) :
    ∀ a ∈ holesWith tilde R C A B f,
      std (holesWith tilde R C A B f).toFinset
        (rr R C (((skewCells A B).map f).foldr max 0) f) a =
      valOf (holesWith tilde R C A B f) a := by
  obtain ⟨h3, h4⟩ := holesWith_spec R C A B f hbox hcol
  intro a ha
  have ha' : a ∈ (skewCells A B).map (rot R C) := by
    rw [← List.mem_toFinset, ← h3]; exact List.mem_toFinset.2 ha
  rw [h3, valOf, h4 a ha']

/-! ## Lesion: drop column-strictness -/

/-- Without `ColInj`, the hole list loses cells: `A = (1,1)`, `B = ∅` in the `2 × 2` box with
`f ≡ 1` (a column with a repeated value). The box hypothesis holds, both cells get the same
`tilde`-rank, and `holesWith` has length 1 instead of 2, so L3 fails. Kernel-checked. -/
theorem lesion_not_colInj :
    InBox 2 2 (skewCells [1, 1] []).toFinset ∧
    (skewCells [1, 1] []).length = 2 ∧
    (holesWith tilde 2 2 [1, 1] [] (fun _ => 1)).length = 1 ∧
    (holesWith tilde 2 2 [1, 1] [] (fun _ => 1)).toFinset ≠
      ((skewCells [1, 1] []).map (rot 2 2)).toFinset := by
  refine ⟨?_, by decide +kernel, by decide +kernel, by decide +kernel⟩
  intro y hy
  have : y ∈ skewCells [1, 1] [] := List.mem_toFinset.1 hy
  have e : skewCells [1, 1] [] = [(0, 0), (1, 0)] := by decide +kernel
  rw [e] at this
  simp at this
  rcases this with rfl | rfl <;> decide

end TworowD4Kernel.RankList
