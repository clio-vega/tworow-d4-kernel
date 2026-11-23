/-
G4 gap 2 (LEAN 2026-11-23): `lem:rrstd` — the hypothesis `hstd` of `thm_G4_of_slideOK`.

Paper: `proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:rrstd` (l.158; patched at `641b17f`):
for `f` semistandard on `A/B`, `f̃ = std (rr f)` is standard on `B^∨/A^∨`. Purbhoo arXiv:0705.1184
§5.1 Cor. 5.3 step 2 ("the result will have shape ...").

In Lean `hstd` reads `StdFrom ∅ (U ++ F)`, `U = skewCells (compl R C A) []` (`A^∨` row by row),
`F = holesWith tilde R C A B f`. It is **not** implied by `hbox` + `hcol`: it needs
* `A`, `B` partitions (`getD` antitone) with `B ⊆ A` — so that `A^∨` and `B^∨` are diagrams;
* `f` semistandard on `A/B`: weakly increasing along rows (`hrow`), strictly up columns (`hup`).
These are the hypotheses of `lem:rrstd` ("Let X be semistandard on P/Q").

* `stdFrom_of_pairwise` (generic): `κ` a diagram, `L` nodup and disjoint from `κ`, `κ ∪ L` a
  diagram, and no cell of `L` is preceded in `L` by one of its predecessors ⇒ `StdFrom κ L`.
* `mem_compl_cells`, `mem_union_rot`: `A^∨ ∪ rot(A/B) = B^∨` cell by cell.
* `hstd_of_ssyt`: the target.
-/
import TworowD4Kernel.RankList
import TworowD4Kernel.PhiGlue
import TworowD4Kernel.SlideIteration

namespace TworowD4Kernel.RRStd

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOut
open TworowD4Kernel.StdSlideBridge TworowD4Kernel.RankList TworowD4Kernel.PhiGlue
open TworowD4Kernel.SlideIteration

/-- `p` is an immediate predecessor (south or west neighbour) of `y`. -/
def IsPred (p y : Cell) : Prop :=
  (y.1 ≠ 0 ∧ p = (y.1 - 1, y.2)) ∨ (y.2 ≠ 0 ∧ p = (y.1, y.2 - 1))

/-- **Generic.** Adding the cells of `L` in order keeps a diagram if the union is one and no
cell comes after one of its own successors. -/
theorem stdFrom_of_pairwise : ∀ (L : List Cell) (κ : Finset Cell), IsDiag κ → L.Nodup →
    (∀ y ∈ L, y ∉ κ) → IsDiag (κ ∪ L.toFinset) → L.Pairwise (fun a b => ¬ IsPred b a) →
    StdFrom κ L
  | [], _, _, _, _, _, _ => trivial
  | y :: L, κ, hκ, hnd, hdis, hU, hpw => by
    rw [List.pairwise_cons] at hpw
    rw [List.nodup_cons] at hnd
    have hyk : y ∉ κ := hdis y (by simp)
    -- the predecessors of `y` lie in `κ`
    have hpre : ∀ p, IsPred p y → p ∈ κ := by
      intro p hp
      have hpy : p ≠ y := by
        rcases hp with ⟨h0, rfl⟩ | ⟨h0, rfl⟩ <;> intro e <;> simp [Prod.ext_iff] at e <;> omega
      have hyU : y ∈ κ ∪ (y :: L).toFinset := by simp
      have hd := hU y hyU
      have hpU : p ∈ κ ∪ (y :: L).toFinset := by
        rcases hp with ⟨h0, rfl⟩ | ⟨h0, rfl⟩
        · rcases hd.1 with h | h
          · exact absurd h h0
          · exact h
        · rcases hd.2 with h | h
          · exact absurd h h0
          · exact h
      simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at hpU
      rcases hpU with h | h | h
      · exact h
      · exact absurd h hpy
      · exact absurd hp (hpw.1 p h)
    have hdiag : IsDiag (insert y κ) := by
      intro x hx
      rw [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · refine ⟨?_, ?_⟩
        · by_cases h0 : x.1 = 0
          · exact Or.inl h0
          · exact Or.inr (Finset.mem_insert_of_mem (hpre _ (Or.inl ⟨h0, rfl⟩)))
        · by_cases h0 : x.2 = 0
          · exact Or.inl h0
          · exact Or.inr (Finset.mem_insert_of_mem (hpre _ (Or.inr ⟨h0, rfl⟩)))
      · obtain ⟨h1, h2⟩ := hκ x hx
        exact ⟨h1.imp_right (Finset.mem_insert_of_mem), h2.imp_right (Finset.mem_insert_of_mem)⟩
    refine ⟨hyk, hdiag, stdFrom_of_pairwise L _ hdiag hnd.2 ?_ ?_ hpw.2⟩
    · intro z hz hzk
      rw [Finset.mem_insert] at hzk
      rcases hzk with rfl | hzk
      · exact hnd.1 hz
      · exact hdis z (by simp [hz]) hzk
    · have : insert y κ ∪ L.toFinset = κ ∪ (y :: L).toFinset := by
        ext z; simp [or_left_comm]
      rw [this]; exact hU

/-- In a repetition-free list, a pairwise condition follows from an index comparison. -/
lemma pairwise_of_idxOf (L : List Cell) (hnd : L.Nodup)
    (h : ∀ a ∈ L, ∀ b ∈ L, IsPred b a → L.idxOf b < L.idxOf a) :
    L.Pairwise (fun a b => ¬ IsPred b a) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij hp
  have := h _ (List.getElem_mem hi) _ (List.getElem_mem hj) hp
  rw [hnd.idxOf_getElem, hnd.idxOf_getElem] at this
  omega

/-! ### Cells -/

lemma getD_zero_of_le (A : List ℕ) (i : ℕ) (h : A.length ≤ i) : A.getD i 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma mem_skewCells (A B : List ℕ) (y : Cell) :
    y ∈ skewCells A B ↔ y.1 < A.length ∧ B.getD y.1 0 ≤ y.2 ∧ y.2 < A.getD y.1 0 := by
  obtain ⟨r, c⟩ := y
  unfold skewCells
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
    decide_eq_true_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨r', hr', c', ⟨hc', hb⟩, rfl, rfl⟩; exact ⟨hr', hb, hc'⟩
  · rintro ⟨hr, hb, hc⟩; exact ⟨r, hr, c, ⟨hc, hb⟩, rfl, rfl⟩

lemma compl_getD (R C : ℕ) (A : List ℕ) (r : ℕ) (hr : r < R) :
    (compl R C A).getD r 0 = C - A.getD (R - 1 - r) 0 := by
  simp [PhiOut.compl, List.getD_eq_getElem?_getD, hr]

/-- `A^∨` cell by cell. -/
lemma mem_compl_cells (R C : ℕ) (A : List ℕ) (y : Cell) :
    y ∈ skewCells (compl R C A) [] ↔ y.1 < R ∧ y.2 + A.getD (R - 1 - y.1) 0 < C := by
  rw [mem_skewCells]
  have hl : (compl R C A).length = R := by simp [PhiOut.compl]
  rw [hl]
  constructor
  · rintro ⟨h1, -, h3⟩; rw [compl_getD R C A _ h1] at h3; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h3⟩; rw [compl_getD R C A _ h1]
    exact ⟨h1, by simp [List.getD_eq_getElem?_getD], by omega⟩

/-- `A^∨ ∪ rot(A/B) = B^∨`, cell by cell (`B ⊆ A`, `A/B` in the box). -/
lemma mem_union_rot (R C : ℕ) (A B : List ℕ) (hbox : InBox R C (skewCells A B).toFinset)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0) (y : Cell) :
    (y ∈ skewCells (compl R C A) [] ∨ y ∈ (skewCells A B).map (rot R C)) ↔
      y.1 < R ∧ y.2 + B.getD (R - 1 - y.1) 0 < C := by
  rw [mem_compl_cells, List.mem_map]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨Y, hY, rfl⟩)
    · exact ⟨h1, by have := hBA (R - 1 - y.1); omega⟩
    · have hb := hbox Y (List.mem_toFinset.2 hY)
      rw [mem_skewCells] at hY
      simp only [rot]
      have e : R - 1 - (R - 1 - Y.1) = Y.1 := by omega
      rw [e]; omega
  · rintro ⟨h1, h2⟩
    by_cases ha : y.2 + A.getD (R - 1 - y.1) 0 < C
    · exact Or.inl ⟨h1, ha⟩
    · right
      refine ⟨(R - 1 - y.1, C - 1 - y.2), ?_, ?_⟩
      · rw [mem_skewCells]
        refine ⟨?_, by simp only; omega, by simp only; omega⟩
        by_contra hl
        rw [getD_zero_of_le A _ (by omega)] at ha
        omega
      · simp only [rot]; ext <;> simp <;> omega

/-! ### The target -/

/-- **`lem:rrstd` in the form `hstd`.** For `A ⊇ B` partitions and `f` semistandard on `A/B`
(rows weak, columns strict), with `A/B` in the `R × C` box: `u_{A^∨}` (row by row) followed by
Φ's holes (`f̃`-order) is a standard filling from `∅`. Proof as in the tex: `rr` reverses both
orders (a), `std` is strict along rows and columns (b), and `A^∨ ∪ rot(A/B) = B^∨`. -/
theorem hstd_of_ssyt (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset) (hcol : ColInj (skewCells A B).toFinset f)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0)
    (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    StdFrom ∅ (skewCells (compl R C A) [] ++ holesWith tilde R C A B f) := by
  obtain ⟨h3, h4⟩ := holesWith_spec R C A B f hbox hcol
  set U := skewCells (compl R C A) [] with hU
  set F := holesWith tilde R C A B f with hF
  set cs := skewCells A B
  set rc := cs.map (rot R C)
  set ℓ := (cs.map f).foldr max 0
  have hmemF : ∀ y, y ∈ F ↔ y ∈ rc := fun y => by
    rw [← List.mem_toFinset, ← List.mem_toFinset, h3]
  have hf : ∀ Y ∈ cs, f Y ≤ ℓ := fun Y hY => le_foldr_max _ _ (List.mem_map.2 ⟨Y, hY, rfl⟩)
  -- F is repetition-free (the rank list of an injective rank)
  have hFnd : F.Nodup := by
    rw [hF, holesWith_eq_rankList]; unfold rankList
    refine List.Nodup.filterMap ?_ List.nodup_range
    intro j j' y hy hy'
    have e1 := List.find?_some (Option.mem_def.1 hy)
    have e2 := List.find?_some (Option.mem_def.1 hy')
    simp only [decide_eq_true_eq] at e1 e2
    omega
  have hUnd : U.Nodup := skewCells_nodup _
  have hmemU : ∀ y, y ∈ (∅ : Finset Cell) ∪ U.toFinset ↔ y ∈ U := fun y => by simp
  have hUdiag : IsDiag ((∅ : Finset Cell) ∪ U.toFinset) := by
    intro x hx
    rw [hmemU, hU, mem_compl_cells] at hx
    refine ⟨?_, ?_⟩
    · by_cases h0 : x.1 = 0
      · exact Or.inl h0
      · right; rw [hmemU, hU, mem_compl_cells]
        have := hA (R - 1 - x.1) (R - 1 - (x.1 - 1)) (by omega)
        exact ⟨by simp only; omega, by simp only; omega⟩
    · by_cases h0 : x.2 = 0
      · exact Or.inl h0
      · right; rw [hmemU, hU, mem_compl_cells]
        exact ⟨hx.1, by simp only; omega⟩
  apply stdFrom_append_of U F ∅
  · refine stdFrom_of_pairwise U ∅ (by intro x hx; simp at hx) hUnd (by simp) hUdiag ?_
    refine (skewCells_sorted _).imp fun {a b} hab hp => ?_
    unfold LexLt at hab
    rcases hp with ⟨h0, rfl⟩ | ⟨h0, rfl⟩ <;> simp only at hab <;> omega
  · have hdis : ∀ y ∈ F, y ∉ (∅ : Finset Cell) ∪ U.toFinset := by
      intro y hy hyU
      rw [hmemU, hU, mem_compl_cells] at hyU
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 ((hmemF y).1 hy)
      have hb := hbox Y (List.mem_toFinset.2 hY)
      rw [mem_skewCells] at hY
      simp only [rot] at hyU
      have e : R - 1 - (R - 1 - Y.1) = Y.1 := by omega
      rw [e] at hyU; omega
    refine stdFrom_of_pairwise F _ hUdiag hFnd hdis ?_ (pairwise_of_idxOf F hFnd ?_)
    · have hmem2 : ∀ y, y ∈ (∅ : Finset Cell) ∪ U.toFinset ∪ F.toFinset ↔
          y.1 < R ∧ y.2 + B.getD (R - 1 - y.1) 0 < C := fun y => by
        rw [← mem_union_rot R C A B hbox hBA, ← hmemF]; simp [hU]
      intro x hx
      rw [hmem2] at hx
      refine ⟨?_, ?_⟩
      · by_cases h0 : x.1 = 0
        · exact Or.inl h0
        · right; rw [hmem2]
          have := hB (R - 1 - x.1) (R - 1 - (x.1 - 1)) (by omega)
          exact ⟨by simp only; omega, by simp only; omega⟩
      · by_cases h0 : x.2 = 0
        · exact Or.inl h0
        · right; rw [hmem2]
          exact ⟨hx.1, by simp only; omega⟩
    · intro a ha b hb hp
      have ha' := (hmemF a).1 ha
      have hb' := (hmemF b).1 hb
      rw [h4 a ha', h4 b hb']
      have hbS : b ∈ rc.toFinset := List.mem_toFinset.2 hb'
      rw [std_lt_iff _ _ hbS]
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 ha'
      obtain ⟨P, hP, rfl⟩ := List.mem_map.1 hb'
      have hYb := hbox Y (List.mem_toFinset.2 hY)
      have hPb := hbox P (List.mem_toFinset.2 hP)
      have hfY := hf Y hY
      have hfP := hf P hP
      simp only [key, rr, rot_rot hYb, rot_rot hPb, Prod.Lex.toLex_lt_toLex]
      rcases hp with ⟨h0, e⟩ | ⟨h0, e⟩
      · have hPY : P = (Y.1 + 1, Y.2) := by
          simp only [rot, Prod.ext_iff] at e h0 ⊢; omega
        subst hPY
        have := hup Y hY hP
        left; omega
      · have hPY : P = (Y.1, Y.2 + 1) := by
          simp only [rot, Prod.ext_iff] at e h0 ⊢; omega
        subst hPY
        have := hrow Y hY hP
        rcases Nat.lt_or_ge (f Y) (f (Y.1, Y.2 + 1)) with hlt | hge
        · left; omega
        · right; refine ⟨by omega, ?_⟩
          simp only [rot]; omega

end TworowD4Kernel.RRStd
