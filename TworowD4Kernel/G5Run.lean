/-
G4 gap G5 (LEAN 2026-11-24): an SlidesOK-free description of the hokF run, `RunInv`, and the
reduction `RunInv → StartsOK` (hence `SlidesOK fwdRule`, via `FwdInv.slidesOK_of_starts`).

Paper: Fulton, *Young Tableaux* §1.2 (jdt slides of a skew SSYT give a skew SSYT), RECALLED in the
tex `lem:A` proof; no arXiv locator. Bookkeeping only: each piece is around `FwdInv.fwd_step`.
`#eval` control (scratch `proofs/code-1123c2-lean-G4-fulton/FwdInvSweep.lean`, `g5row`): RunInv at
every slide start 310/310; holes in FORWARD order `U`: 156/310.
-/
import TworowD4Kernel.FwdInv

namespace TworowD4Kernel.G5Run

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOut
open TworowD4Kernel.RRStd TworowD4Kernel.PhiGlue TworowD4Kernel.SkewColInj TworowD4Kernel.FwdInv
open TworowD4Kernel.RankList Finset

/-- Weakly north-east (componentwise `≤`). -/
def Le2 (a b : Cell) : Prop := a.1 ≤ b.1 ∧ a.2 ≤ b.2

/-- SlidesOK-free description of the state before a slide: `T` = holes still to fill.
Support and holes disjoint, union convex, no support cell weakly south-west of a remaining hole,
support semistandard. -/
def RunInv (S : Finset Cell) (X : Cell → ℕ) (T : List Cell) : Prop :=
  (∀ t ∈ T, t ∉ S) ∧ Skew (S ∪ T.toFinset) ∧
  (∀ t ∈ T, ∀ z ∈ S, ¬ Le2 z t) ∧ SSOn S X

/-! ### Facts about one slide, any rule -/

lemma ins_move {S : Finset Cell} {h y : Cell} (hy : y ∈ S) :
    insert y (moveS S h y) = insert h S := by
  ext a; simp only [mem_insert, mem_moveS]; by_cases e : a = y <;> simp_all

/-- **G5f.** The support size is constant along a slide. -/
theorem card_slide (Rl : Rule) : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    (slide Rl k S X h).1.card = S.card
  | 0, _, _, _, _ => rfl
  | k + 1, S, X, h, hh => by
    simp only [slide]
    rcases hc : Rl.ch S X h with _ | y
    · rfl
    · have hy := Rl.mem S X h y hc
      have hyh : y ≠ h := fun e => hh (e ▸ hy)
      have hn : y ∉ moveS S h y := by simp [mem_moveS, hyh]
      rw [card_slide Rl k _ _ y hn]
      unfold moveS
      rw [card_insert_of_notMem (by simp [hh]), card_erase_of_mem hy]
      have := card_pos.2 ⟨y, hy⟩; omega

/-- The set `insert hole support` is constant along a slide, any rule. -/
theorem ins_slide (Rl : Rule) : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell),
    insert (slide Rl k S X h).2.2.1 (slide Rl k S X h).1 = insert h S
  | 0, _, _, _ => rfl
  | k + 1, S, X, h => by
    simp only [slide]
    rcases hc : Rl.ch S X h with _ | y
    · rfl
    · simp only []
      rw [ins_slide Rl k _ _ y, ins_move (Rl.mem S X h y hc)]

/-- A forward slide moves the hole weakly north-east. -/
theorem le2_slide : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell),
    Le2 h (slide fwdRule k S X h).2.2.1
  | 0, _, _, _ => ⟨le_rfl, le_rfl⟩
  | k + 1, S, X, h => by
    simp only [slide]
    rcases hc : fwdRule.ch S X h with _ | y
    · exact ⟨le_rfl, le_rfl⟩
    · obtain ⟨h1, h2⟩ := le2_slide k (moveS S h y) (moveX X h y) y
      rcases fwd_cases (S := S) (X := X) hc with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨by simp at h1 ⊢; omega, by simpa using h2⟩
      · exact ⟨by simpa using h1, by simp at h2 ⊢; omega⟩

/-- The fuel measure: support cells strictly above the hole's anti-diagonal. -/
def above (S : Finset Cell) (h : Cell) : ℕ := (S.filter fun z => h.1 + h.2 < z.1 + z.2).card

/-- **G5b.** A forward slide stops once the fuel exceeds `above S h` (each move raises
`h.1 + h.2` by one, and the moved cell leaves the count). No invariant is needed. -/
theorem slide_stops : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), above S h < k →
    fwdChoice (slide fwdRule k S X h).1 (slide fwdRule k S X h).2.1
      (slide fwdRule k S X h).2.2.1 = none
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, S, X, h, hk => by
    simp only [slide]
    rcases hc : fwdRule.ch S X h with _ | y
    · exact hc
    · simp only []
      apply slide_stops k
      have hy : y ∈ S := fwdRule.mem S X h y hc
      have hsum : y.1 + y.2 = h.1 + h.2 + 1 := by
        rcases fwd_cases (S := S) (X := X) hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp <;> omega
      have hsub : (moveS S h y).filter (fun z => y.1 + y.2 < z.1 + z.2) ⊆
          ((S.filter fun z => h.1 + h.2 < z.1 + z.2).erase y) := by
        intro z hz
        simp only [mem_filter, mem_moveS, mem_erase] at hz ⊢
        rcases hz with ⟨rfl | ⟨hzy, hz⟩, hlt⟩
        · omega
        · exact ⟨hzy, hz, by omega⟩
      have := card_le_card hsub
      rw [card_erase_of_mem (by simp [hy]; omega)] at this
      have hpos : 0 < (S.filter fun z => h.1 + h.2 < z.1 + z.2).card :=
        card_pos.2 ⟨y, by simp [hy]; omega⟩
      change ((moveS S h y).filter (fun z => y.1 + y.2 < z.1 + z.2)).card < k
      have hk' : (S.filter fun z => h.1 + h.2 < z.1 + z.2).card < k + 1 := hk
      omega

lemma above_le_card (S : Finset Cell) (h : Cell) : above S h ≤ S.card :=
  card_filter_le _ _

/-! ### G5a, G5c -/

/-- **G5a.** `RunInv` + head hole maximal among the remaining holes ⇒ `FwdInv` at the start
(`HoleOK` is vacuous: the west/south neighbours of `h` would be support cells below `h`). -/
theorem fwdInv_of_runInv (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (T : List Cell)
    (hr : RunInv S X (h :: T)) (hmax : ∀ t ∈ T, ¬ Le2 h t) : FwdInv S X h := by
  obtain ⟨hd, hsk, hsw, hss⟩ := hr
  have hsw0 : ∀ z ∈ S, ¬ Le2 z h := hsw h (List.mem_cons_self ..)
  refine ⟨hd h (List.mem_cons_self ..), ?_, hss, ?_, ?_⟩
  · intro a ha b hb z h1 h2 h3 h4
    have ha' : a ∈ S ∪ (h :: T).toFinset := by
      rcases mem_insert.1 ha with rfl | ha <;> simp_all
    have hb' : b ∈ S ∪ (h :: T).toFinset := by
      rcases mem_insert.1 hb with rfl | hb <;> simp_all
    have hz := hsk a ha' b hb' z h1 h2 h3 h4
    simp only [mem_union, List.mem_toFinset, List.mem_cons] at hz
    rcases hz with hz | rfl | hz
    · exact mem_insert_of_mem hz
    · exact mem_insert_self _ _
    · exfalso
      rcases mem_insert.1 ha with rfl | ha
      · exact hmax z hz ⟨h1, h2⟩
      · exact hsw z (List.mem_cons_of_mem _ hz) a ha ⟨h1, h2⟩
  · rintro w hw rfl -
    exact absurd ⟨le_rfl, Nat.le_succ _⟩ (hsw0 w hw)
  · rintro s hs rfl -
    exact absurd ⟨Nat.le_succ _, le_rfl⟩ (hsw0 s hs)

/-- **G5c.** `RunInv` passes to the next slide: the final hole `h'` is weakly north-east of `h`
(so not below any remaining hole) and has no support cell north-east of it, so it is a maximal
cell of the convex `S ∪ {h} ∪ T`; removing it keeps convexity. -/
theorem runInv_next (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (T : List Cell)
    (hr : RunInv S X (h :: T)) (hmax : ∀ t ∈ T, ¬ Le2 h t) (hk : S.card + 1 ≤ k) :
    RunInv (slide fwdRule k S X h).1 (slide fwdRule k S X h).2.1 T := by
  have hi := fwdInv_of_runInv S X h T hr hmax
  set S' := (slide fwdRule k S X h).1
  set X' := (slide fwdRule k S X h).2.1
  set h' := (slide fwdRule k S X h).2.2.1
  have hi' : FwdInv S' X' h' := fwdInv_slide k S X h hi
  have hstop : fwdChoice S' X' h' = none :=
    slide_stops k S X h (lt_of_le_of_lt (above_le_card S h) (by omega))
  have hins : insert h' S' = insert h S := ins_slide fwdRule k S X h
  have hle : Le2 h h' := le2_slide k S X h
  obtain ⟨hd, hsk, hsw, hss⟩ := hr
  have hN : (h'.1 + 1, h'.2) ∉ S' := by
    intro e; unfold fwdChoice nN nE at hstop; split_ifs at hstop
  have hE : (h'.1, h'.2 + 1) ∉ S' := by
    intro e; unfold fwdChoice nN nE at hstop; split_ifs at hstop
  have hS'sub : ∀ z ∈ S', z = h ∨ z ∈ S := by
    intro z hz
    have : z ∈ insert h' S' := mem_insert_of_mem hz
    rw [hins] at this; simpa using this
  have htne : ∀ t ∈ T, t ≠ h := fun t ht e => hmax t ht (e ▸ ⟨le_rfl, le_rfl⟩)
  have hh'T : ∀ t ∈ T, ¬ Le2 h' t := fun t ht ⟨a, b⟩ => hmax t ht ⟨hle.1.trans a, hle.2.trans b⟩
  -- the big convex set
  have big : ∀ z, z ∈ insert h' (S' ∪ T.toFinset) ↔ z ∈ S ∪ (h :: T).toFinset := by
    intro z
    have hz := congrArg (z ∈ ·) hins
    simp only [mem_insert] at hz
    simp only [mem_insert, mem_union, List.mem_toFinset, List.mem_cons]
    constructor
    · rintro (e | e | e)
      · have : z = h ∨ z ∈ S := hz ▸ Or.inl e
        tauto
      · rcases hS'sub z e with e | e <;> tauto
      · tauto
    · rintro (e | e | e)
      · have hz : z ∈ insert h S := mem_insert_of_mem e
        rw [← hins] at hz; rcases mem_insert.1 hz with e | e <;> tauto
      · have hz : z ∈ insert h S := e ▸ mem_insert_self _ _
        rw [← hins] at hz; rcases mem_insert.1 hz with e | e <;> tauto
      · tauto
  -- `h'` is maximal in the big set
  have hmaxh' : ∀ b ∈ S' ∪ T.toFinset, ¬ Le2 h' b := by
    intro b hb ⟨b1, b2⟩
    simp only [mem_union, List.mem_toFinset] at hb
    rcases hb with hb | hb
    · obtain ⟨hh', hsk', -, -⟩ := hi'
      have hbh : b ≠ h' := fun e => hh' (e ▸ hb)
      by_cases e1 : h'.1 < b.1
      · have := hsk' h' (mem_insert_self _ _) b (mem_insert_of_mem hb) (h'.1 + 1, h'.2)
          (by simp) le_rfl (by simpa using e1) b2
        rcases mem_insert.1 this with e | e
        · simp [Prod.ext_iff] at e
        · exact hN e
      · have e2 : h'.2 < b.2 := by
          by_contra e2; exact hbh (Prod.ext (by omega) (by omega))
        have := hsk' h' (mem_insert_self _ _) b (mem_insert_of_mem hb) (h'.1, h'.2 + 1)
          le_rfl (by simp) b1 (by simpa using e2)
        rcases mem_insert.1 this with e | e
        · simp [Prod.ext_iff] at e
        · exact hE e
    · exact hh'T b hb ⟨b1, b2⟩
  refine ⟨?_, ?_, ?_, (fwd_end hi' hstop).2⟩
  · intro t ht htS
    rcases hS'sub t htS with e | e
    · exact htne t ht e
    · exact hd t (List.mem_cons_of_mem _ ht) e
  · intro a ha b hb z h1 h2 h3 h4
    have ha' := (big a).1 (mem_insert_of_mem ha)
    have hb' := (big b).1 (mem_insert_of_mem hb)
    have hz := (big z).2 (hsk a ha' b hb' z h1 h2 h3 h4)
    rcases mem_insert.1 hz with rfl | hz
    · exact absurd ⟨h3, h4⟩ (hmaxh' b hb)
    · exact hz
  · intro t ht z hz
    rcases hS'sub z hz with rfl | e
    · exact hmax t ht
    · exact hsw t (List.mem_cons_of_mem _ ht) z e

/-! ### G5d and the run induction -/

/-- `skewCells A B` is listed in strict row-major (lexicographic) order. -/
theorem skewCells_pairwise (A B : List ℕ) :
    (skewCells A B).Pairwise (fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)) := by
  unfold skewCells
  rw [List.pairwise_flatMap]
  refine ⟨fun r _ => ?_, ?_⟩
  · rw [List.pairwise_map]
    exact ((List.pairwise_lt_range).sublist List.filter_sublist).imp
      (fun h => Or.inr ⟨rfl, h⟩)
  · refine (List.pairwise_lt_range).imp ?_
    intro r r' hr a ha b hb
    simp only [List.mem_map, List.mem_filter] at ha hb
    obtain ⟨c, -, rfl⟩ := ha; obtain ⟨c', -, rfl⟩ := hb
    exact Or.inl hr

/-- **G5d.** In the start list `U.reverse`, no hole is weakly south-west of a later one: the
head of every suffix is maximal among its tail. Only row-major order is used. -/
theorem rev_heads_maximal (A B : List ℕ) :
    (skewCells A B).reverse.Pairwise (fun a b => ¬ Le2 a b) := by
  rw [List.pairwise_reverse]
  refine (skewCells_pairwise A B).imp ?_
  rintro a b (h | ⟨e, h⟩) ⟨h1, h2⟩ <;> omega

/-- **The run induction.** `RunInv` at the start, holes pairwise "not weakly south-west", and fuel
above the support size give `FwdInv` at every start hole. -/
theorem startsOK_of_runInv (k : ℕ) : ∀ (T : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    RunInv S X T → T.Pairwise (fun a b => ¬ Le2 a b) → S.card + 1 ≤ k → StartsOK k S X T
  | [], _, _, _, _, _ => trivial
  | h :: T, S, X, hr, hp, hk => by
    rw [List.pairwise_cons] at hp
    refine ⟨fwdInv_of_runInv S X h T hr hp.1, ?_⟩
    apply startsOK_of_runInv k T _ _ (runInv_next k S X h T hr hp.1 hk) hp.2
    rw [card_slide fwdRule k S X h (hr.1 h (List.mem_cons_self ..))]; exact hk

/-! ### G5e: the initial `RunInv` -/

/-- **G5e** (= G7: lem:rrstd(a), the SSOn half, plus `F ∪ U = B^∨` from `RRStd.mem_union_rot`).
At the start of the hokF run: support `F = rot(A/B)` with values `rr f`, remaining holes
`U.reverse` (`U` = cells of `A^∨`). -/
theorem runInv_init (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0) (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    RunInv (holesWith tilde R C A B f).toFinset
      (rr R C (((skewCells A B).map f).foldr max 0) f) (skewCells (compl R C A) []).reverse := by
  have hcol := hcol_of_hup A B f hA hB hrow hup
  have hS0 : (holesWith tilde R C A B f).toFinset = ((skewCells A B).map (rot R C)).toFinset :=
    (holesWith_spec R C A B f hbox hcol).1
  rw [hS0]
  have hf : ∀ Y ∈ skewCells A B, f Y ≤ ((skewCells A B).map f).foldr max 0 :=
    fun Y hY => le_foldr_max _ _ (List.mem_map.2 ⟨Y, hY, rfl⟩)
  -- a support cell, numerically: `rot y ∈ A/B`
  have hmem : ∀ y ∈ ((skewCells A B).map (rot R C)).toFinset,
      y.1 < R ∧ y.2 < C ∧ (R - 1 - y.1, C - 1 - y.2) ∈ skewCells A B ∧
      R - 1 - y.1 < A.length ∧ B.getD (R - 1 - y.1) 0 ≤ C - 1 - y.2 ∧
      C - 1 - y.2 < A.getD (R - 1 - y.1) 0 := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map] at hy
    obtain ⟨Y, hY, rfl⟩ := hy
    have hb := hbox Y (List.mem_toFinset.2 hY)
    have hY' := (mem_skewCells A B Y).1 hY
    simp only [rot]
    have e1 : R - 1 - (R - 1 - Y.1) = Y.1 := by omega
    have e2 : C - 1 - (C - 1 - Y.2) = Y.2 := by omega
    rw [e1, e2]
    exact ⟨by omega, by omega, hY, hY'⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- disjoint
    intro t ht hts
    rw [List.mem_reverse, mem_compl_cells] at ht
    obtain ⟨-, -, -, -, -, h3⟩ := hmem t hts
    omega
  · -- convex: membership is `y.1 < R ∧ y.2 + B_{R-1-y.1} < C`
    have hU : ∀ y, y ∈ ((skewCells A B).map (rot R C)).toFinset ∪
        (skewCells (compl R C A) []).reverse.toFinset ↔
          y.1 < R ∧ y.2 + B.getD (R - 1 - y.1) 0 < C := by
      intro y
      rw [← mem_union_rot R C A B hbox hBA y]
      simp only [Finset.mem_union, List.mem_toFinset, List.mem_reverse]; tauto
    intro a ha b hb z h1 h2 h3 h4
    rw [hU] at ha hb ⊢
    have := hB (R - 1 - b.1) (R - 1 - z.1) (by omega)
    omega
  · -- no support cell weakly south-west of a remaining hole
    intro t ht z hz ⟨h1, h2⟩
    rw [List.mem_reverse, mem_compl_cells] at ht
    obtain ⟨-, -, -, -, -, h3⟩ := hmem z hz
    have := hA (R - 1 - t.1) (R - 1 - z.1) (by omega)
    omega
  · -- rows weak
    intro a ha ha'
    obtain ⟨a1, a2, hY, -⟩ := hmem a ha
    obtain ⟨-, b2, hY', -⟩ := hmem _ ha'
    have e : ((R - 1 - a.1, C - 1 - (a.2 + 1)).1, (R - 1 - a.1, C - 1 - (a.2 + 1)).2 + 1) =
        (R - 1 - a.1, C - 1 - a.2) := Prod.ext rfl (by simp only; omega)
    have := hrow _ hY' (by rw [e]; exact hY)
    rw [e] at this
    simp only [rr, rot] at *
    omega
  · -- columns strict
    intro a ha ha'
    obtain ⟨a1, a2, hY, -⟩ := hmem a ha
    obtain ⟨b1, -, hY', -⟩ := hmem _ ha'
    have e : ((R - 1 - (a.1 + 1), C - 1 - a.2).1 + 1, (R - 1 - (a.1 + 1), C - 1 - a.2).2) =
        (R - 1 - a.1, C - 1 - a.2) := Prod.ext (by simp only; omega) rfl
    have := hup _ hY' (by rw [e]; exact hY)
    rw [e] at this
    have := hf _ hY
    simp only [rr, rot] at *
    omega

/-- **`hokF` discharged.** For `A ⊇ B` partitions and `f` semistandard on `A/B` in the box, every
filling met by the forward run (`Σ`'s side) is column-injective. -/
theorem hokF_of_ssyt (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0) (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    SlidesOK fwdRule ((holesWith tilde R C A B f).length + 1)
      (holesWith tilde R C A B f).toFinset
      (rr R C (((skewCells A B).map f).foldr max 0) f)
      (skewCells (compl R C A) []).reverse :=
  slidesOK_of_starts _ _ _ _ <|
    startsOK_of_runInv _ _ _ _ (runInv_init R C A B f hbox hA hB hBA hrow hup)
      (rev_heads_maximal _ _)
      (by have := List.toFinset_card_le (holesWith tilde R C A B f); omega)

/-- `SkewColInj.thm_G4_of_slideOK''` with `hokF` discharged; only `hokR` (the reverse run, G6)
stays a named hypothesis. -/
theorem thm_G4_of_hokR (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0)
    (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2))
    (hokR : SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f)) :
    (phi R C A B f).1 = (sigmaRR R C A B f).1 ∧
    ∀ a ∈ (phi R C A B f).1, (phi R C A B f).2 a = (sigmaRR R C A B f).2 a :=
  thm_G4_of_slideOK'' R C A B f hbox hA hB hBA hrow hup hokR
    (hokF_of_ssyt R C A B f hbox hA hB hBA hrow hup)

/-! ## Lesion: the south-west clause of `RunInv` is load-bearing

Drop "no support cell weakly south-west of a remaining hole". Row 0: support `(0,0) ↦ 2`,
`(0,2) ↦ 1`, one remaining hole `(0,1)` between them. Disjointness, convexity and `SSOn` hold
(no two support cells are adjacent), yet `FwdInv` fails at the start hole: west `2` > east `1`
across the hole (`HoleOK`), so `StartsOK` fails. The full `RunInv` rejects the state on exactly
the dropped clause (`(0,0)` is weakly south-west of `(0,1)`). The `#eval` sweep: holes in forward
order `U` keep this clause false and pass only 156/310. -/

/-- `RunInv` without its south-west clause. -/
def RunInvNoSW (S : Finset Cell) (X : Cell → ℕ) (T : List Cell) : Prop :=
  (∀ t ∈ T, t ∉ S) ∧ Skew (S ∪ T.toFinset) ∧ SSOn S X

def lesS : Finset Cell := {(0, 0), (0, 2)}
def lesX (y : Cell) : ℕ := if y = (0, 0) then 2 else 1

theorem lesion_runInv_sw :
    RunInvNoSW lesS lesX [(0, 1)] ∧ [(0, 1)].Pairwise (fun a b : Cell => ¬ Le2 a b) ∧
    lesS.card + 1 ≤ 3 ∧
    ¬ StartsOK 3 lesS lesX [(0, 1)] ∧
    ¬ RunInv lesS lesX [(0, 1)] ∧ ¬ (∀ t ∈ [((0 : ℕ), (1 : ℕ))], ∀ z ∈ lesS, ¬ Le2 z t) := by
  have hsw : ¬ (∀ t ∈ [((0 : ℕ), (1 : ℕ))], ∀ z ∈ lesS, ¬ Le2 z t) := fun h =>
    h (0, 1) (by simp) (0, 0) (by decide) ⟨le_rfl, by decide⟩
  refine ⟨⟨by decide, ?_, by decide⟩, by simp, by decide, ?_, fun h => hsw h.2.2.1, hsw⟩
  · rintro a ha b hb ⟨i, j⟩ h1 h2 h3 h4
    simp only [lesS, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    have hb' : b.1 = 0 ∧ b.2 ≤ 2 := by
      rcases hb with (rfl | rfl) | rfl <;> simp
    simp only at h3 h4
    obtain rfl : i = 0 := by omega
    have hj : j ≤ 2 := by omega
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide
  · rintro ⟨⟨-, -, -, hW, -⟩, -⟩
    have := hW (0, 0) (by decide) rfl (by decide)
    exact absurd this (by decide)

end TworowD4Kernel.G5Run
