/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SlideSwitchGeneral

/-!
# G4 Lemma D, half (i), reverse slide: a reverse jdt slide is a product of elementary switches

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D`, l.183–186, the mirror
claim: "The reverse slide of Definition `def:phi`(3) for the box `F_j` is the product of the
switches carrying `F_j` leftward past `U_m, U_{m-1}, …, U_1`. Here the first adjacent `U_i` met
is the larger of the west and south neighbours." The forward half is `slide_eq_switch_product`
(`SlideSwitchGeneral.lean`).

## Setting

A diagram `D`, a word `U = [U_1, …, U_m]` of cells, and the box `h` of `F_j`, with
`U ++ [h]` a standard filling over `D` (`StdFrom D (U ++ [h])`). The chain is
`chainOf D (U ++ [h])`. The switch product `carryRev m` applies `s_m`, then `s_{m-1}`, …, then
`s_1` (it carries the last letter leftward).

## Route (direct mirror; the 180° rotation route was not taken)

* Switch side: the C1 lemma `switchL_step` applies **unchanged** (the switch is symmetric).
  The induction is from the *left* of `U`: `s_2, …, s_m` act on the tail chain, then `s_1`
  compares `U_1` with wherever the hole ended up. That gives `carryWRev`.
* jdt side: `jdtRev` is defined independently ("larger of west and south") on the list of the
  `U`-cells in **decreasing** order of entry, so "larger entry" = "smaller index". The proof
  mirrors `jdt_eq_carryW`, with the invariant "no placed cell is `≤` the hole"
  (`not_ge_rev_of_not_adj` is where standardness enters), giving `carryV`.
* `carryV_reverse` identifies the two intermediate words.
-/

namespace TworowD4Kernel.SlideSwitch

/-! ### Definitions -/

/-- One reverse jdt step with the hole at `h`. `cells[i]` is the cell holding entry `m - i`
(entries in **decreasing** order). If `larger`, the hole moves to whichever of the west
`(r, c-1)` and south `(r-1, c)` neighbours carries the larger entry (the smaller index);
`larger = false` is the lesion. On the boundary (`c = 0` or `r = 0`) the truncated subtraction
makes the "neighbour" the hole itself, which is never in `cells` (the hole is empty). -/
def jdtStepRev (larger : Bool) (cells : List Cell) (h : Cell) : Option (List Cell × Cell) :=
  let w : Cell := (h.1, h.2 - 1)
  let s : Cell := (h.1 - 1, h.2)
  match cells.idxOf? w, cells.idxOf? s with
  | none, none => none
  | some i, none => some (cells.set i h, w)
  | none, some j => some (cells.set j h, s)
  | some i, some j =>
      if decide (i < j) = larger then some (cells.set i h, w) else some (cells.set j h, s)

/-- The reverse jdt slide with fuel. -/
def jdtRev (larger : Bool) : ℕ → List Cell → Cell → List Cell × Cell
  | 0, cells, h => (cells, h)
  | k + 1, cells, h =>
      match jdtStepRev larger cells h with
      | none => (cells, h)
      | some (c', h') => jdtRev larger k c' h'

/-- jdt side: the final hole (the new cell of `F_j`), then the cells of `U'_1, …, U'_m`, as
singletons, in word order. -/
def jdtSideRev (larger : Bool) (U : List Cell) (h : Cell) : List (Finset Cell) :=
  let r := jdtRev larger (U.length + 1) U.reverse h
  (r.2 :: r.1.reverse).map ({·})

/-- Carry the last letter leftward: `s_1 ∘ s_2 ∘ ⋯ ∘ s_m` (so `s_m` is applied first). -/
def carryRev (m : ℕ) (ch : List (Finset Cell)) : List (Finset Cell) :=
  (List.range m).reverse.foldl (fun c t => switchAt c (t + 1)) ch

/-- Switch side: the letter cells after carrying `F_j` (cell `h`) leftward past `U_m, …, U_1`. -/
def switchSideRev (D : Finset Cell) (U : List Cell) (h : Cell) : List (Finset Cell) :=
  lettersOf (carryRev U.length (chainOf D (U ++ [h])))

/-- Switch-side intermediate: `(cell of F_j, cells of U_1, …, U_m)` after the carry. -/
def carryWRev (h : Cell) : List Cell → Cell × List Cell
  | [] => (h, [])
  | x :: U =>
      if Adj x (carryWRev h U).1 then (x, (carryWRev h U).1 :: (carryWRev h U).2)
      else ((carryWRev h U).1, x :: (carryWRev h U).2)

/-- jdt-side intermediate on the decreasing list `V`: `(new U-cells in V order, final hole)`. -/
def carryV (h : Cell) : List Cell → List Cell × Cell
  | [] => ([], h)
  | y :: V =>
      if Adj y h then (h :: (carryV y V).1, (carryV y V).2)
      else (y :: (carryV h V).1, (carryV h V).2)

/-! ### Switch side -/

lemma carryRev_zero (ch : List (Finset Cell)) : carryRev 0 ch = ch := rfl

lemma carryRev_cons (m : ℕ) (a : Finset Cell) (ch : List (Finset Cell)) :
    carryRev (m + 1) (a :: ch) = switchAt (a :: carryRev m ch) 1 := by
  unfold carryRev
  rw [List.range_succ_eq_map, List.reverse_cons, List.foldl_append, ← List.map_reverse,
    List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  congr 1
  exact foldl_cons_switch a _ ch

/-- **(C2a, reverse)** The leftward carry turns the chain of `U ++ [h]` into the chain of the
word `carryWRev h U`, which is again standard. -/
theorem carryRev_chainOf (h : Cell) (U : List Cell) : ∀ D : Finset Cell, IsDiag D →
    StdFrom D (U ++ [h]) →
      carryRev U.length (chainOf D (U ++ [h])) =
          chainOf D ((carryWRev h U).1 :: (carryWRev h U).2) ∧
        StdFrom D ((carryWRev h U).1 :: (carryWRev h U).2) := by
  induction U with
  | nil => intro D _ hS; exact ⟨rfl, hS⟩
  | cons x U ih =>
    intro D hD hS
    obtain ⟨hxD, hDx, hS'⟩ := hS
    obtain ⟨ihc, ihs⟩ := ih (insert x D) hDx hS'
    set z := (carryWRev h U).1
    set W := (carryWRev h U).2
    obtain ⟨hz, hDxz, hW⟩ := ihs
    have hstep := switchL_step hD hxD hDx hz hDxz
    obtain ⟨rest, hrest⟩ := chainOf_eq_cons (insert z (insert x D)) W
    have e0 : chainOf D ((x :: U) ++ [h]) = D :: chainOf (insert x D) (U ++ [h]) := rfl
    rw [List.length_cons, e0, carryRev_cons, ihc]
    have e1 : chainOf (insert x D) (z :: W) = insert x D :: insert z (insert x D) :: rest := by
      simp only [chainOf]; rw [hrest]
    rw [e1]
    have hsw : switchAt (D :: insert x D :: insert z (insert x D) :: rest) 1 =
        D :: switchL D (insert x D) (insert z (insert x D)) :: insert z (insert x D) :: rest := by
      simp [switchAt]
    rw [hsw, hstep]
    have hxz : x ≠ z := fun e => hz (e ▸ Finset.mem_insert_self _ _)
    have hc : carryWRev h (x :: U) = if Adj x z then (x, z :: W) else (z, x :: W) := rfl
    rw [hc]
    by_cases ha : Adj x z
    · rw [if_pos ha, if_pos ha]
      refine ⟨?_, hxD, hDx, hz, hDxz, hW⟩
      simp only [chainOf]; rw [hrest]
    · rw [if_neg ha, if_neg ha]
      have hzD : z ∉ D := fun e => hz (Finset.mem_insert_of_mem e)
      have hDz : IsDiag (insert z D) := (isDiag_insert_iff_not_adj hD hxD hxz.symm hDxz).2 ha
      have hxzD : x ∉ insert z D := by
        simp only [Finset.mem_insert, not_or]; exact ⟨hxz, hxD⟩
      rw [Finset.insert_comm] at hDxz hW hrest
      refine ⟨?_, hzD, hDz, hxzD, hDxz, hW⟩
      simp only [chainOf]; rw [hrest, Finset.insert_comm]

/-! ### jdt side -/

/-- Standard "from the top": `V` lists cells of `T` that can be removed one at a time, keeping
a diagram (the largest entry first). -/
def StdDown : Finset Cell → List Cell → Prop
  | _, [] => True
  | T, y :: V => y ∈ T ∧ IsDiag (T.erase y) ∧ StdDown (T.erase y) V

lemma jdtStepRev_cons (s : Bool) {x z : Cell} (hx : ¬ Ge x z) (L : List Cell) :
    jdtStepRev s (x :: L) z = (jdtStepRev s L z).map (fun r => (x :: r.1, r.2)) := by
  have he : (x == (z.1, z.2 - 1)) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact hx ⟨le_refl _, by simp⟩
  have hn : (x == (z.1 - 1, z.2)) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact hx ⟨by simp, le_refl _⟩
  unfold jdtStepRev
  simp only [List.idxOf?_cons, he, hn, Bool.false_eq_true, if_false]
  rcases L.idxOf? (z.1, z.2 - 1) with _ | i <;> rcases L.idxOf? (z.1 - 1, z.2) with _ | j <;>
    simp only [Option.map_none, Option.map_some, List.set_cons_succ]
  have : decide (i + 1 < j + 1) = decide (i < j) := by simp
  rw [this]
  split <;> rfl

/-- The hole only moves weakly south-west. -/
lemma jdtStepRev_some {s : Bool} {L c' : List Cell} {z z' : Cell}
    (h : jdtStepRev s L z = some (c', z')) : Ge z' z := by
  unfold jdtStepRev at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨le_refl _, by simp⟩
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by simp, le_refl _⟩
  · split at h
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨le_refl _, by simp⟩
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact ⟨by simp, le_refl _⟩

lemma not_ge_trans_rev {x z z' : Cell} (hx : ¬ Ge x z) (h : Ge z' z) : ¬ Ge x z' := by
  rintro ⟨h1, h2⟩; exact hx ⟨le_trans h1 h.1, le_trans h2 h.2⟩

/-- A cell not `≤` the hole is never looked at again by the reverse slide. -/
theorem jdtRev_cons_irrel (s : Bool) (x : Cell) :
    ∀ (k : ℕ) (L : List Cell) (z : Cell), ¬ Ge x z →
      jdtRev s k (x :: L) z = (x :: (jdtRev s k L z).1, (jdtRev s k L z).2) := by
  intro k
  induction k with
  | zero => intro L z _; rfl
  | succ k ih =>
    intro L z hx
    simp only [jdtRev]
    rw [jdtStepRev_cons s hx L]
    rcases hst : jdtStepRev s L z with _ | ⟨c', z'⟩
    · rfl
    · simp only [Option.map_some]
      exact ih c' z' (not_ge_trans_rev hx (jdtStepRev_some hst))

/-- An adjacent (west or south) head cell carries the largest remaining entry (index `0`). -/
lemma jdtStepRev_adj_head {h y : Cell} (ha : Adj y h) (L : List Cell) :
    jdtStepRev true (y :: L) h = some (h :: L, y) := by
  unfold jdtStepRev
  rcases ha with rfl | rfl
  · have hw : ((y.1, y.2 + 1 - 1) : Cell) = y := by simp
    have hn : (y == (y.1 - 1, y.2 + 1)) = false := by
      rw [beq_eq_false_iff_ne]; intro e; have := congrArg Prod.snd e; simp at this
    simp only [hw, List.idxOf?_cons, beq_self_eq_true, if_true, hn, Bool.false_eq_true, if_false]
    rcases L.idxOf? (y.1 - 1, y.2 + 1) with _ | j <;> simp
  · have hs : ((y.1 + 1 - 1, y.2) : Cell) = y := by simp
    have he : (y == (y.1 + 1, y.2 - 1)) = false := by
      rw [beq_eq_false_iff_ne]; intro e; have := congrArg Prod.fst e; simp at this
    simp only [hs, List.idxOf?_cons, beq_self_eq_true, if_true, he, Bool.false_eq_true, if_false]
    rcases L.idxOf? (y.1 + 1, y.2 - 1) with _ | i <;> simp

/-- The invariant of the reverse jdt side. `T` = `D` plus the not-yet-processed `U`-cells,
`P` = the cells of already processed `U`-letters, `h` = the hole. -/
def JdtInvRev (T P : Finset Cell) (h : Cell) (V : List Cell) : Prop :=
  StdDown T V ∧ IsDiag (insert h (T ∪ P)) ∧ h ∉ T ∧ ∀ c ∈ P, ¬ Ge c h

/-- Standardness at work (mirror of `not_ge_of_not_adj`): the next `U`-cell, if not the
west/south neighbour of the hole, is not `≤` the hole. -/
lemma not_ge_rev_of_not_adj {T P : Finset Cell} {h y : Cell} (hyT : y ∈ T)
    (hTy : IsDiag (T.erase y)) (hN : IsDiag (insert h (T ∪ P))) (hhT : h ∉ T)
    (hP : ∀ c ∈ P, ¬ Ge c h) (hna : ¬ Adj y h) : ¬ Ge y h := by
  intro hge
  have hyh : y ≠ h := fun e => hhT (e ▸ hyT)
  have hhN : h ∈ insert h (T ∪ P) := Finset.mem_insert_self _ _
  -- the successor `s` of `y` towards `h`
  have key : ∀ s : Cell, Ge s h → Ge y s → s ≠ y → s ≠ h → False := by
    intro s hsh hys hsy hsh'
    have hsN := hN.mem_of_ge s _ h hhN rfl hsh
    simp only [Finset.mem_insert, Finset.mem_union] at hsN
    rcases hsN with hs | hs | hs
    · exact hsh' hs
    · have : s ∈ T.erase y := Finset.mem_erase.2 ⟨hsy, hs⟩
      have := hTy.mem_of_ge y _ s this rfl hys
      simp at this
    · exact hP s hs hsh
  by_cases hr : y.1 < h.1
  · refine key (y.1 + 1, y.2) ⟨by simp; omega, by simpa using hge.2⟩ ⟨by simp, by simp⟩ ?_ ?_
    · intro e; have := congrArg Prod.fst e; simp at this
    · intro e; exact hna (Or.inr e.symm)
  · have hr1 : y.1 = h.1 := by have := hge.1; omega
    have hc : y.2 < h.2 := by
      rcases Nat.lt_or_ge y.2 h.2 with h' | h'
      · exact h'
      · exfalso; apply hyh; obtain ⟨a, b⟩ := y; ext <;> simp_all; have := hge.2; omega
    refine key (y.1, y.2 + 1) ⟨by simp [hr1], by simp; omega⟩ ⟨by simp, by simp⟩ ?_ ?_
    · intro e; have := congrArg Prod.snd e; simp at this
    · intro e; apply hna; left; rw [← e]

/-- **(C2b, reverse)** With fuel at least `|V| + 1`, the reverse jdt slide ("larger of west and
south") on the decreasing list `V` returns `carryV h V`. -/
theorem jdtRev_eq_carryV (V : List Cell) : ∀ (T P : Finset Cell) (h : Cell) (k : ℕ),
    JdtInvRev T P h V → V.length + 1 ≤ k → jdtRev true k V h = carryV h V := by
  induction V with
  | nil =>
    intro T P h k _ hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    simp only [jdtRev, jdtStepRev, List.idxOf?_nil, carryV]
  | cons y V ih =>
    intro T P h k hI hk
    obtain ⟨⟨hyT, hTy, hS⟩, hN, hhT, hP⟩ := hI
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hk' : V.length + 1 ≤ k := by simp at hk; omega
    have e1 : insert y (T.erase y ∪ insert h P) = insert h (T ∪ P) := by
      ext c
      by_cases hc : c = y
      · subst hc; simp [hyT]
      · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase, hc, false_or]; tauto
    have e2 : insert h (T.erase y ∪ insert y P) = insert h (T ∪ P) := by
      ext c
      by_cases hc : c = y
      · subst hc; simp [hyT]
      · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_erase, hc, false_or]; tauto
    by_cases ha : Adj y h
    · have hhy : ¬ Ge h y := by
        rintro ⟨h1, h2⟩; rcases ha with rfl | rfl <;> simp at h1 h2 <;> omega
      have hyh : Ge y h := by rcases ha with rfl | rfl <;> exact ⟨by simp, by simp⟩
      have hI' : JdtInvRev (T.erase y) (insert h P) y V := by
        refine ⟨hS, by rw [e1]; exact hN, by simp, ?_⟩
        intro c hc
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact hhy
        · exact not_ge_trans_rev (hP c hc) hyh
      simp only [jdtRev, jdtStepRev_adj_head ha, carryV, if_pos ha]
      rw [jdtRev_cons_irrel true h k V y hhy, ih _ _ y k hI' hk']
    · have hng := not_ge_rev_of_not_adj hyT hTy hN hhT hP ha
      have hI' : JdtInvRev (T.erase y) (insert y P) h V := by
        refine ⟨hS, by rw [e2]; exact hN, fun e => hhT (Finset.mem_of_mem_erase e), ?_⟩
        intro c hc
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact hng
        · exact hP c hc
      rw [jdtRev_cons_irrel true y (k + 1) V h hng]
      simp only [carryV, if_neg ha]
      rw [ih _ _ h (k + 1) hI' (by omega)]

/-! ### Identifying the two intermediate words -/

lemma carryV_append (x : Cell) (V : List Cell) : ∀ h : Cell,
    carryV h (V ++ [x]) =
      if Adj x (carryV h V).2 then ((carryV h V).1 ++ [(carryV h V).2], x)
      else ((carryV h V).1 ++ [x], (carryV h V).2) := by
  induction V with
  | nil => intro h; simp only [List.nil_append, carryV]
  | cons y V ih =>
    intro h
    simp only [List.cons_append, carryV]
    by_cases ha : Adj y h
    · simp only [if_pos ha, ih y]; split_ifs <;> rfl
    · simp only [if_neg ha, ih h]; split_ifs <;> rfl

lemma carryV_reverse (h : Cell) (U : List Cell) :
    (carryV h U.reverse).2 = (carryWRev h U).1 ∧
      (carryV h U.reverse).1 = (carryWRev h U).2.reverse := by
  induction U with
  | nil => exact ⟨rfl, rfl⟩
  | cons x U ih =>
    rw [List.reverse_cons, carryV_append, ih.1, ih.2]
    have hc : carryWRev h (x :: U) =
        if Adj x (carryWRev h U).1 then (x, (carryWRev h U).1 :: (carryWRev h U).2)
        else ((carryWRev h U).1, x :: (carryWRev h U).2) := rfl
    rw [hc]
    split_ifs <;> simp

/-! ### Initial invariant -/

lemma isDiag_union_of_stdFrom (U : List Cell) : ∀ D, IsDiag D → StdFrom D U →
    IsDiag (D ∪ U.toFinset) := by
  induction U with
  | nil => intro D hD _; simpa using hD
  | cons x U ih =>
    intro D _ ⟨_, hDx, hS⟩
    have := ih _ hDx hS
    rwa [List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]

lemma stdFrom_append (U w : List Cell) : ∀ D, StdFrom D (U ++ w) →
    StdFrom D U ∧ StdFrom (D ∪ U.toFinset) w := by
  induction U with
  | nil => intro D hS; exact ⟨trivial, by simpa using hS⟩
  | cons x U ih =>
    intro D ⟨hx, hDx, hS⟩
    obtain ⟨h1, h2⟩ := ih _ hS
    refine ⟨⟨hx, hDx, h1⟩, ?_⟩
    rwa [List.toFinset_cons, Finset.union_insert, ← Finset.insert_union]

lemma stdDown_of_stdFrom (U : List Cell) : ∀ D, IsDiag D → StdFrom D U →
    StdDown (D ∪ U.toFinset) U.reverse := by
  induction U using List.reverseRecOn with
  | nil => intro _ _ _; trivial
  | append_singleton U x ih =>
    intro D hD hS
    obtain ⟨h1, hx, -, -⟩ := stdFrom_append U [x] D hS
    have hE : D ∪ (U ++ [x]).toFinset = insert x (D ∪ U.toFinset) := by
      ext c; simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_singleton,
        Finset.mem_insert]; tauto
    rw [hE, List.reverse_append, List.reverse_singleton, List.singleton_append]
    refine ⟨Finset.mem_insert_self _ _, ?_, ?_⟩ <;> rw [Finset.erase_insert hx]
    · exact isDiag_union_of_stdFrom U D hD h1
    · exact ih D hD h1

lemma fresh_of_stdFrom (w : List Cell) : ∀ D, StdFrom D w → Fresh D w := by
  induction w with
  | nil => intro _ _; trivial
  | cons x w ih => intro D ⟨hx, _, hS⟩; exact ⟨hx, ih _ hS⟩

/-! ### The general theorem -/

/-- **G4 Lemma D, half (i), reverse slide, all shapes.**
`projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D` (l.183–186), mirror of
`slide_eq_switch_product`: for every diagram `D` and every word `U = [U_1, …, U_m]` with
`U ++ [h]` a standard filling over `D` (so `h`, the box of `F_j`, is an outer corner of
`D ∪ U ∪ {h}`), the reverse jdt slide of the `U`-letters into `h` ("larger of west and
south") equals the product `s_1 ∘ ⋯ ∘ s_m` of elementary switches carrying `F_j` leftward
past `U_m, …, U_1`. -/
theorem reverse_slide_eq_switch_product (D : Finset Cell) (U : List Cell) (h : Cell)
    (hD : IsDiag D) (hS : StdFrom D (U ++ [h])) :
    switchSideRev D U h = jdtSideRev true U h := by
  obtain ⟨hc, hstd⟩ := carryRev_chainOf h U D hD hS
  obtain ⟨hU, hh, hDUh, -⟩ := stdFrom_append U [h] D hS
  have hI : JdtInvRev (D ∪ U.toFinset) ∅ h U.reverse :=
    ⟨stdDown_of_stdFrom U D hD hU, by simpa using hDUh, hh, by simp⟩
  have hj := jdtRev_eq_carryV U.reverse _ _ h (U.length + 1) hI (by simp)
  unfold switchSideRev jdtSideRev
  rw [hc, lettersOf_chainOf _ D (fresh_of_stdFrom _ D hstd)]
  dsimp only
  rw [hj, (carryV_reverse h U).1, (carryV_reverse h U).2, List.reverse_reverse]

/-! ### Finite corollary and lesions -/

/-- All instances `(D, U, h)`: `U ++ [h]` a standard filling of `ν / D`, `|ν| ≤ N`,
`|ν / D| ≥ 1`. -/
def instancesRev (N : ℕ) : List (Finset Cell × List Cell × Cell) :=
  (List.range (N + 1)).flatMap fun n =>
    (diags N n).flatMap fun ν =>
      (List.range n).flatMap fun k =>
        ((diags N k).filter (· ⊆ ν)).flatMap fun D =>
          (stdFill N ν (n - k) D).filterMap fun F =>
            match F.reverse with
            | [] => none
            | h :: Ur => some (D, Ur.reverse, h)

/-- Reverse slide = reverse switch product on every instance. -/
def reverseSlideCheck (N : ℕ) (larger : Bool := true) : Bool :=
  (instancesRev N).all fun ⟨D, U, h⟩ => switchSideRev D U h = jdtSideRev larger U h

/-- The hypotheses of `reverse_slide_eq_switch_product` on every enumerated instance. -/
def hypCheckRev (N : ℕ) : Bool :=
  (instancesRev N).all fun ⟨D, U, h⟩ => decide (IsDiag D ∧ StdFrom D (U ++ [h]))

theorem reverseSlideCheck_of_hypCheckRev {N : ℕ} (hN : hypCheckRev N = true) :
    reverseSlideCheck N = true := by
  unfold hypCheckRev at hN
  unfold reverseSlideCheck
  rw [List.all_eq_true] at hN ⊢
  rintro ⟨D, U, h⟩ hm
  have := hN _ hm
  simp only [decide_eq_true_eq] at this
  simpa using reverse_slide_eq_switch_product D U h this.1 this.2

/-- **Corollary**: the reverse finite check at `|ν| ≤ 5`, derived from the general theorem
(the kernel decides only the hypotheses). -/
theorem reverse_slide_eq_switch_product_le5 : reverseSlideCheck 5 = true :=
  reverseSlideCheck_of_hypCheckRev (by decide +kernel)

/-- The `|ν| ≤ 6` reverse check (495 instances), also through the general theorem. -/
theorem reverse_slide_eq_switch_product_le6 : reverseSlideCheck 6 = true :=
  reverseSlideCheck_of_hypCheckRev (by decide +kernel)

/-- Control: hole `(1,1)` with both a west (`U_3` at `(1,0)`) and a south (`U_2` at `(0,1)`)
neighbour. The larger, `U_3`, moves to `(1,1)`. The hole is then at `(1,0)`, and its south
neighbour `U_1` moves to it. The final word is `F` at `(0,0)`, then `U_1, U_2, U_3` at
`(1,0), (0,1), (1,1)`. -/
theorem control_rev_both_neighbours :
    jdtSideRev true [(0, 0), (0, 1), (1, 0)] (1, 1) = [{(0, 0)}, {(1, 0)}, {(0, 1)}, {(1, 1)}] ∧
      switchSideRev ∅ [(0, 0), (0, 1), (1, 0)] (1, 1) =
        jdtSideRev true [(0, 0), (0, 1), (1, 0)] (1, 1) := by
  decide

/-- **Lesion** ("smaller of west and south"): on the control instance the switch product and the
lesioned slide differ. -/
theorem lesion_rev_smaller :
    switchSideRev ∅ [(0, 0), (0, 1), (1, 0)] (1, 1) ≠
      jdtSideRev false [(0, 0), (0, 1), (1, 0)] (1, 1) := by
  decide

/-- **Lesion (general).** The general reverse statement with `larger := false` is false: the
`lesion_rev_smaller` instance satisfies both hypotheses. -/
theorem reverse_slide_eq_switch_product_larger_false :
    ¬ ∀ (D : Finset Cell) (U : List Cell) (h : Cell), IsDiag D → StdFrom D (U ++ [h]) →
      switchSideRev D U h = jdtSideRev false U h :=
  fun H => lesion_rev_smaller (H ∅ _ _ (by decide) (by decide))

/-- Lesion at the level of the whole check (`|ν| ≤ 4`: a hole with both a west and a south
neighbour first occurs at `|ν| = 4`, so `|ν| ≤ 3` would be a vacuous lesion). -/
theorem reverseSlideCheck_larger_fails : reverseSlideCheck 4 false = false := by decide +kernel

end TworowD4Kernel.SlideSwitch
