/-
G4 gap G6 (LEAN 2026-11-24 c2): `hokR` discharged. The reverse run of Φ (`revRule`, start
support `u_{A^∨}`, holes `holesWith tilde` = `rot(A/B)` in tilde-rank order) meets only
column-injective fillings. Mirror of `G5Run`, with the invariant of `RevInv` (= `FwdInv`).

Run invariant `RunInvR`: support and holes disjoint, union convex, **no support cell weakly
north-east of a remaining hole**, support semistandard. Fuel: a reverse step lowers `h.1 + h.2`
by one, so fuel `R + C` exceeds it for every hole in the box.

Paper: Fulton, *Young Tableaux* §1.2 (jdt slides preserve semistandardness), RECALLED in the tex
`lem:A` proof; no arXiv locator. `#eval` control (scratch `proofs/code-1124c2-lean-G4-G6/
RevSweep.lean`): RunInvR at every slide start 310/310, `holesWith` heads minimal 310/310.
-/
import TworowD4Kernel.RevInv

namespace TworowD4Kernel.G6Run

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOut
open TworowD4Kernel.RRStd TworowD4Kernel.PhiGlue TworowD4Kernel.SkewColInj TworowD4Kernel.FwdInv
open TworowD4Kernel.RankList TworowD4Kernel.G5Run TworowD4Kernel.RevInv Finset

/-- The reverse run invariant before a slide; `T` = holes still to fill. -/
def RunInvR (S : Finset Cell) (X : Cell → ℕ) (T : List Cell) : Prop :=
  (∀ t ∈ T, t ∉ S) ∧ Skew (S ∪ T.toFinset) ∧
  (∀ t ∈ T, ∀ z ∈ S, ¬ Le2 t z) ∧ SSOn S X

lemma rev_cases' {S : Finset Cell} {X : Cell → ℕ} {h y : Cell} (hh : h ∉ S)
    (hc : revChoice S X h = some y) :
    (y.1 + 1 = h.1 ∧ y.2 = h.2) ∨ (y.1 = h.1 ∧ y.2 + 1 = h.2) := by
  obtain ⟨r, c⟩ := h
  rcases rev_cases hh hc with ⟨i, rfl, rfl, -⟩ | ⟨j, rfl, rfl, -⟩ <;> simp

/-- A reverse slide moves the hole weakly south-west. -/
theorem le2_slideR : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    Le2 (slide revRule k S X h).2.2.1 h
  | 0, _, _, _, _ => ⟨le_rfl, le_rfl⟩
  | k + 1, S, X, h, hh => by
    simp only [slide]
    rcases hc : revRule.ch S X h with _ | y
    · exact ⟨le_rfl, le_rfl⟩
    · dsimp only
      have hyS := revRule.mem S X h y hc
      have hyh : y ≠ h := fun e => hh (e ▸ hyS)
      obtain ⟨h1, h2⟩ := le2_slideR k (moveS S h y) (moveX X h y) y (by simp [mem_moveS, hyh])
      have := rev_cases' (X := X) hh hc
      exact ⟨by omega, by omega⟩

/-- A reverse slide stops once the fuel exceeds `h.1 + h.2`. -/
theorem slide_stopsR : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), h ∉ S →
    h.1 + h.2 < k →
    revChoice (slide revRule k S X h).1 (slide revRule k S X h).2.1
      (slide revRule k S X h).2.2.1 = none
  | 0, _, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | k + 1, S, X, h, hh, hk => by
    simp only [slide]
    rcases hc : revRule.ch S X h with _ | y
    · exact hc
    · simp only []
      have hyS := revRule.mem S X h y hc
      have hyh : y ≠ h := fun e => hh (e ▸ hyS)
      apply slide_stopsR k _ _ y (by simp [mem_moveS, hyh])
      have := rev_cases' (X := X) hh hc
      omega

/-- `RunInvR` + head hole minimal among the remaining holes ⇒ `FwdInv` at the start. -/
theorem fwdInv_of_runInvR (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (T : List Cell)
    (hr : RunInvR S X (h :: T)) (hmin : ∀ t ∈ T, ¬ Le2 t h) : FwdInv S X h := by
  obtain ⟨hd, hsk, hne, hss⟩ := hr
  have hne0 : ∀ z ∈ S, ¬ Le2 h z := hne h (List.mem_cons_self ..)
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
      rcases mem_insert.1 hb with rfl | hb
      · exact hmin z hz ⟨h3, h4⟩
      · exact hne z (List.mem_cons_of_mem _ hz) b hb ⟨h3, h4⟩
  · intro w _ _ hE
    exact absurd ⟨le_rfl, Nat.le_succ _⟩ (hne0 _ hE)
  · intro s _ _ hN
    exact absurd ⟨Nat.le_succ _, le_rfl⟩ (hne0 _ hN)

/-- `RunInvR` passes to the next slide: the final hole is weakly south-west of `h` and has no
south/west support neighbour, so it is a minimal cell of the convex `S ∪ {h} ∪ T`. -/
theorem runInvR_next (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (T : List Cell)
    (hr : RunInvR S X (h :: T)) (hmin : ∀ t ∈ T, ¬ Le2 t h) (hk : h.1 + h.2 < k) :
    RunInvR (slide revRule k S X h).1 (slide revRule k S X h).2.1 T := by
  have hi := fwdInv_of_runInvR S X h T hr hmin
  set S' := (slide revRule k S X h).1
  set X' := (slide revRule k S X h).2.1
  set h' := (slide revRule k S X h).2.2.1
  have hi' : FwdInv S' X' h' := revInv_slide k S X h hi
  have hstop : revChoice S' X' h' = none := slide_stopsR k S X h hi.1 hk
  have hins : insert h' S' = insert h S := ins_slide revRule k S X h
  have hle : Le2 h' h := le2_slideR k S X h hi.1
  obtain ⟨hd, hsk, hne, hss⟩ := hr
  have hSo : (h'.1 - 1, h'.2) ∉ S' := by
    intro e; unfold revChoice nS nW at hstop; split_ifs at hstop
  have hWo : (h'.1, h'.2 - 1) ∉ S' := by
    intro e; unfold revChoice nS nW at hstop; split_ifs at hstop
  have hS'sub : ∀ z ∈ S', z = h ∨ z ∈ S := by
    intro z hz
    have : z ∈ insert h' S' := mem_insert_of_mem hz
    rw [hins] at this; simpa using this
  have htne : ∀ t ∈ T, t ≠ h := fun t ht e => hmin t ht (e ▸ ⟨le_rfl, le_rfl⟩)
  have hTh' : ∀ t ∈ T, ¬ Le2 t h' := fun t ht ⟨a, b⟩ => hmin t ht ⟨a.trans hle.1, b.trans hle.2⟩
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
  have hminh' : ∀ b ∈ S' ∪ T.toFinset, ¬ Le2 b h' := by
    intro b hb ⟨b1, b2⟩
    simp only [mem_union, List.mem_toFinset] at hb
    rcases hb with hb | hb
    · obtain ⟨hh', hsk', -, -⟩ := hi'
      have hbh : b ≠ h' := fun e => hh' (e ▸ hb)
      by_cases e1 : b.1 < h'.1
      · have := hsk' b (mem_insert_of_mem hb) h' (mem_insert_self _ _) (h'.1 - 1, h'.2)
          (by simp only; omega) b2 (by simp) le_rfl
        rcases mem_insert.1 this with e | e
        · simp only [Prod.ext_iff] at e; omega
        · exact hSo e
      · have e2 : b.2 < h'.2 := by
          by_contra e2; exact hbh (Prod.ext (by omega) (by omega))
        have := hsk' b (mem_insert_of_mem hb) h' (mem_insert_self _ _) (h'.1, h'.2 - 1)
          b1 (by simp only; omega) le_rfl (by simp)
        rcases mem_insert.1 this with e | e
        · simp only [Prod.ext_iff] at e; omega
        · exact hWo e
    · exact hTh' b hb ⟨b1, b2⟩
  refine ⟨?_, ?_, ?_, hi'.2.2.1⟩
  · intro t ht htS
    rcases hS'sub t htS with e | e
    · exact htne t ht e
    · exact hd t (List.mem_cons_of_mem _ ht) e
  · intro a ha b hb z h1 h2 h3 h4
    have ha' := (big a).1 (mem_insert_of_mem ha)
    have hb' := (big b).1 (mem_insert_of_mem hb)
    have hz := (big z).2 (hsk a ha' b hb' z h1 h2 h3 h4)
    rcases mem_insert.1 hz with rfl | hz
    · exact absurd ⟨h1, h2⟩ (hminh' a ha)
    · exact hz
  · intro t ht z hz
    rcases hS'sub z hz with rfl | e
    · exact hmin t ht
    · exact hne t (List.mem_cons_of_mem _ ht) z e

/-- **The reverse run induction.** -/
theorem startsOK_of_runInvR (k : ℕ) : ∀ (T : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    RunInvR S X T → T.Pairwise (fun a b => ¬ Le2 b a) → (∀ t ∈ T, t.1 + t.2 < k) →
    StartsOKR k S X T
  | [], _, _, _, _, _ => trivial
  | h :: T, S, X, hr, hp, hk => by
    rw [List.pairwise_cons] at hp
    refine ⟨fwdInv_of_runInvR S X h T hr hp.1, ?_⟩
    exact startsOK_of_runInvR k T _ _
      (runInvR_next k S X h T hr hp.1 (hk h (List.mem_cons_self ..))) hp.2
      (fun t ht => hk t (List.mem_cons_of_mem _ ht))

/-! ### Heads minimal: tilde-rank order is a linear extension of the product order -/

lemma row_le {S : Finset Cell} {X : Cell → ℕ} (hS : Skew S) (hX : SSOn S X) :
    ∀ (d : ℕ) (a : Cell), a ∈ S → (a.1, a.2 + d) ∈ S → X a ≤ X (a.1, a.2 + d) := by
  intro d
  induction d with
  | zero => intro a _ _; exact le_rfl
  | succ d ih =>
    intro a ha ht
    have hb : (a.1, a.2 + d) ∈ S :=
      hS a ha _ ht _ le_rfl (by simp) le_rfl (by simp only; omega)
    exact le_trans (ih a ha hb) (hX.1 _ hb ht)

/-- On a skew shape, a semistandard filling is monotone in the product order. -/
lemma mono_of_SS {S : Finset Cell} {X : Cell → ℕ} (hS : Skew S) (hX : SSOn S X) {a b : Cell}
    (ha : a ∈ S) (hb : b ∈ S) (hab : Le2 a b) : X a ≤ X b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  obtain ⟨h1, h2⟩ := hab
  simp only at h1 h2
  have hm : (b1, a2) ∈ S := hS _ ha _ hb _ h1 le_rfl le_rfl h2
  have e1 : X (a1, a2) ≤ X (b1, a2) := by
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; exact le_rfl
    · obtain ⟨d, rfl⟩ : ∃ d, b1 = a1 + (d + 1) := ⟨b1 - a1 - 1, by omega⟩
      exact (col_lt hS hX d (a1, a2) ha hm).le
  have e2 : X (b1, a2) ≤ X (b1, b2) := by
    obtain ⟨d, rfl⟩ : ∃ d, b2 = a2 + d := ⟨b2 - a2, by omega⟩
    exact row_le hS hX d (b1, a2) hm hb
  exact e1.trans e2

/-- Membership in `rot(A/B)`, numerically. -/
lemma mem_rotImg (R C : ℕ) (A B : List ℕ) (hbox : InBox R C (skewCells A B).toFinset) (y : Cell) :
    y ∈ ((skewCells A B).map (rot R C)).toFinset ↔
      y.1 < R ∧ y.2 < C ∧ R - 1 - y.1 < A.length ∧ B.getD (R - 1 - y.1) 0 ≤ C - 1 - y.2 ∧
      C - 1 - y.2 < A.getD (R - 1 - y.1) 0 := by
  simp only [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨Y, hY, rfl⟩
    have hb := hbox Y (List.mem_toFinset.2 hY)
    have hY' := (mem_skewCells A B Y).1 hY
    simp only [rot]
    have e1 : R - 1 - (R - 1 - Y.1) = Y.1 := by omega
    have e2 : C - 1 - (C - 1 - Y.2) = Y.2 := by omega
    rw [e1, e2]
    exact ⟨by omega, by omega, hY'⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨rot R C y, (mem_skewCells A B _).2 (by simpa [rot] using h3), ?_⟩
    exact rot_rot ⟨h1, h2⟩

theorem skew_rotImg (R C : ℕ) (A B : List ℕ) (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0) (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0) :
    Skew ((skewCells A B).map (rot R C)).toFinset := by
  intro a ha b hb z h1 h2 h3 h4
  rw [mem_rotImg R C A B hbox] at ha hb ⊢
  have := hA (R - 1 - z.1) (R - 1 - a.1) (by omega)
  have := hB (R - 1 - b.1) (R - 1 - z.1) (by omega)
  omega

/-- **Heads minimal.** In `holesWith tilde`, no hole is weakly south-west of an earlier one. -/
theorem holes_heads_minimal (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0) (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hss : SSOn ((skewCells A B).map (rot R C)).toFinset
      (rr R C (((skewCells A B).map f).foldr max 0) f)) :
    (holesWith tilde R C A B f).Pairwise (fun a b => ¬ Le2 b a) := by
  set cs := skewCells A B
  set ℓ := (cs.map f).foldr max 0
  set F := (cs.map (rot R C)).toFinset
  have hf : ∀ Y ∈ cs.toFinset, f Y ≤ ℓ := fun Y hY =>
    le_foldr_max _ _ (List.mem_map.2 ⟨Y, List.mem_toFinset.1 hY, rfl⟩)
  have hT : F = cs.toFinset.image (rot R C) := map_toFinset _ _
  have hC := lemmaC R C ℓ cs.toFinset f hbox hf
  have hsk := skew_rotImg R C A B hbox hA hB
  simp only [holesWith]
  rw [List.pairwise_filterMap]
  refine List.pairwise_lt_range.imp ?_
  intro j j' hjj' a ha b hb hba
  have pa := List.find?_some ha
  have pb := List.find?_some hb
  simp only [decide_eq_true_eq] at pa pb
  have ma : a ∈ F := List.mem_toFinset.2 (List.mem_of_find?_eq_some ha)
  have mb : b ∈ F := List.mem_toFinset.2 (List.mem_of_find?_eq_some hb)
  have sa := hC a (hT ▸ ma)
  have sb := hC b (hT ▸ mb)
  rw [← hT] at sa sb
  have hlt : std F (rr R C ℓ f) a < std F (rr R C ℓ f) b := by rw [sa, sb, pa, pb]; exact hjj'
  have hle : std F (rr R C ℓ f) b ≤ std F (rr R C ℓ f) a := by
    rw [std_le_iff F _ ma]
    have hm := mono_of_SS hsk hss mb ma hba
    simp only [key, Prod.Lex.toLex_le_toLex]
    rcases Nat.lt_or_eq_of_le hm with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e, hba.2⟩
  omega

/-! ### The initial `RunInvR` and `hokR` -/

theorem runInvR_init (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0) (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    RunInvR (skewCells (compl R C A) []).toFinset uVal (holesWith tilde R C A B f) := by
  have hcol := hcol_of_hup A B f hA hB hrow hup
  have hS0 : (holesWith tilde R C A B f).toFinset = ((skewCells A B).map (rot R C)).toFinset :=
    (holesWith_spec R C A B f hbox hcol).1
  have hT : ∀ t ∈ holesWith tilde R C A B f, t ∈ ((skewCells A B).map (rot R C)).toFinset :=
    fun t ht => hS0 ▸ List.mem_toFinset.2 ht
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hts
    rw [List.mem_toFinset, mem_compl_cells] at hts
    have := (mem_rotImg R C A B hbox t).1 (hT t ht)
    omega
  · rw [hS0]
    have hU : ∀ y, y ∈ (skewCells (compl R C A) []).toFinset ∪
        ((skewCells A B).map (rot R C)).toFinset ↔
          y.1 < R ∧ y.2 + B.getD (R - 1 - y.1) 0 < C := by
      intro y
      rw [← mem_union_rot R C A B hbox hBA y]
      simp only [Finset.mem_union, List.mem_toFinset]
    intro a ha b hb z h1 h2 h3 h4
    rw [hU] at ha hb ⊢
    have := hB (R - 1 - b.1) (R - 1 - z.1) (by omega)
    omega
  · intro t ht z hz ⟨h1, h2⟩
    rw [List.mem_toFinset, mem_compl_cells] at hz
    have := (mem_rotImg R C A B hbox t).1 (hT t ht)
    have := hA (R - 1 - z.1) (R - 1 - t.1) (by omega)
    omega
  · intro a _ _; exact le_rfl
  · intro a _ _; simp [uVal]

/-- **`hokR` discharged.** For `A ⊇ B` partitions and `f` semistandard on `A/B` in the box, every
filling met by the reverse run (Φ's side) is column-injective. -/
theorem hokR_of_ssyt (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0) (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f) := by
  have hcol := hcol_of_hup A B f hA hB hrow hup
  have hS0 := (holesWith_spec R C A B f hbox hcol).1
  have hss : SSOn ((skewCells A B).map (rot R C)).toFinset
      (rr R C (((skewCells A B).map f).foldr max 0) f) :=
    hS0 ▸ (runInv_init R C A B f hbox hA hB hBA hrow hup).2.2.2
  refine slidesOK_of_startsR _ _ _ _ <|
    startsOK_of_runInvR _ _ _ _ (runInvR_init R C A B f hbox hA hB hBA hrow hup)
      (holes_heads_minimal R C A B f hbox hA hB hss) ?_
  intro t ht
  have := (mem_rotImg R C A B hbox t).1 (hS0 ▸ List.mem_toFinset.2 ht)
  omega

/-- **Theorem G4, no named hypotheses.** Both Fulton-1.2 hypotheses (`hokR`, `hokF`) are
discharged: for `A ⊇ B` partitions and `f` semistandard on `A/B` inside the `R × C` box,
`Φ(f) = Σ(f)` (same support, same values). -/
theorem thm_G4_ssyt (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0)
    (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    (phi R C A B f).1 = (sigmaRR R C A B f).1 ∧
    ∀ a ∈ (phi R C A B f).1, (phi R C A B f).2 a = (sigmaRR R C A B f).2 a :=
  thm_G4_of_hokR R C A B f hbox hA hB hBA hrow hup
    (hokR_of_ssyt R C A B f hbox hA hB hBA hrow hup)

/-! ## Lesion: the north-east clause of `RunInvR` is load-bearing

Drop "no support cell weakly north-east of a remaining hole". The `G5Run` instance serves again:
row 0, support `(0,0) ↦ 2`, `(0,2) ↦ 1`, one remaining hole `(0,1)`. Disjointness, convexity and
`SSOn` hold, fuel is ample, yet `FwdInv` fails at the start hole (west `2` > east `1` across the
hole), so `StartsOKR` fails. The full `RunInvR` rejects the state on exactly the dropped clause
(`(0,2)` is weakly north-east of `(0,1)`). -/

/-- `RunInvR` without its north-east clause. -/
def RunInvRNoNE (S : Finset Cell) (X : Cell → ℕ) (T : List Cell) : Prop :=
  (∀ t ∈ T, t ∉ S) ∧ Skew (S ∪ T.toFinset) ∧ SSOn S X

theorem lesion_runInvR_ne :
    RunInvRNoNE lesS lesX [(0, 1)] ∧ [(0, 1)].Pairwise (fun a b : Cell => ¬ Le2 b a) ∧
    (∀ t ∈ [((0 : ℕ), (1 : ℕ))], t.1 + t.2 < 3) ∧
    ¬ StartsOKR 3 lesS lesX [(0, 1)] ∧
    ¬ RunInvR lesS lesX [(0, 1)] ∧ ¬ (∀ t ∈ [((0 : ℕ), (1 : ℕ))], ∀ z ∈ lesS, ¬ Le2 t z) := by
  have hne : ¬ (∀ t ∈ [((0 : ℕ), (1 : ℕ))], ∀ z ∈ lesS, ¬ Le2 t z) := fun h =>
    h (0, 1) (by simp) (0, 2) (by decide) ⟨le_rfl, by decide⟩
  refine ⟨⟨by decide, ?_, by decide⟩, by simp, by simp, ?_, fun h => hne h.2.2.1, hne⟩
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

end TworowD4Kernel.G6Run
