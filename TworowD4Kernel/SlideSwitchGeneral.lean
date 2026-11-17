/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SlideSwitch

/-!
# G4 Lemma D, half (i), tier C: a forward jdt slide is a product of elementary switches

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D`, l.165–185, the italic
claim "A forward slide of `F` into the cell of `U_i` is the product of the elementary switches
carrying `U_i` rightward past `F_1, F_2, …, F_p` in this order", for **all** shapes.

## Route

Both sides are compared with an intermediate cell word `carryW h F`: process `F` left to right
with a current hole; if the next cell `y` is the east or north neighbour of the hole the hole
moves to `y` (the letters swap cells), otherwise `y` keeps its cell.

* `carry_chainOf` : the switch product on the chain of `h :: F` is the chain of `carryW h F`.
  The single-switch step is `switchL_step` (C1): on a saturated triple
  `D ⊂ D ∪ {h} ⊂ D ∪ {h, y}` the switch keeps the chain iff `y` is adjacent to `h`
  (`isDiag_insert_iff_not_adj`), else replaces the middle by `D ∪ {y}`.
* `jdt_eq_carryW` : the jdt slide "smaller of east and north" produces `carryW h F`.
  Standardness enters exactly as in the tex: a non-adjacent `F_j` is never in the upper
  quadrant of the hole (`not_ge_of_not_adj`), so it is never looked at again
  (`jdt_cons_irrel`), and an adjacent `F_j` met first has the smallest index.
-/

namespace TworowD4Kernel.SlideSwitch

/-- East or north neighbour. -/
def Adj (h y : Cell) : Prop := y = (h.1, h.2 + 1) ∨ y = (h.1 + 1, h.2)

instance (h y : Cell) : Decidable (Adj h y) := by unfold Adj; infer_instance

/-- `F` is a standard filling of a skew shape with inner shape `κ`: each prefix adds one new
cell and stays a diagram. -/
def StdFrom : Finset Cell → List Cell → Prop
  | _, [] => True
  | κ, y :: F => y ∉ κ ∧ IsDiag (insert y κ) ∧ StdFrom (insert y κ) F

instance decStdFrom : ∀ κ F, Decidable (StdFrom κ F)
  | _, [] => isTrue trivial
  | κ, y :: F => by
      unfold StdFrom
      haveI := decStdFrom (insert y κ) F
      infer_instance

/-- The intermediate cell word: carry the hole `h` past `F`. -/
def carryW (h : Cell) : List Cell → List Cell
  | [] => [h]
  | y :: F => if Adj h y then h :: carryW y F else y :: carryW h F

/-! ### C1: the single switch -/

/-- With `D`, `D ∪ {h}`, `D ∪ {h,y}` diagrams (`h, y` new), `D ∪ {y}` is a diagram iff `y` is
not the east/north neighbour of `h`. -/
theorem isDiag_insert_iff_not_adj {D : Finset Cell} {h y : Cell} (hD : IsDiag D)
    (hhD : h ∉ D) (hyh : y ≠ h) (hDhy : IsDiag (insert y (insert h D))) :
    IsDiag (insert y D) ↔ ¬ Adj h y := by
  constructor
  · intro hyD hadj
    obtain ⟨h1, h2⟩ := hyD y (Finset.mem_insert_self _ _)
    rcases hadj with rfl | rfl
    · rcases h2 with h2 | h2
      · simp at h2
      · simp only [Nat.add_sub_cancel, Finset.mem_insert] at h2
        rcases h2 with h2 | h2
        · exact hyh h2.symm
        · exact hhD h2
    · rcases h1 with h1 | h1
      · simp at h1
      · simp only [Nat.add_sub_cancel, Finset.mem_insert] at h1
        rcases h1 with h1 | h1
        · exact hyh h1.symm
        · exact hhD h1
  · intro hna x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · obtain ⟨h1, h2⟩ := hDhy x (Finset.mem_insert_self _ _)
      refine ⟨?_, ?_⟩
      · rcases h1 with h1 | h1
        · exact Or.inl h1
        · rcases Nat.eq_zero_or_pos x.1 with h0 | h0
          · exact Or.inl h0
          right
          simp only [Finset.mem_insert] at h1 ⊢
          rcases h1 with h1 | h1 | h1
          · exfalso; have := congrArg Prod.fst h1; simp at this; omega
          · exfalso; apply hna; right
            rw [← h1]; obtain ⟨a, b⟩ := x
            simp only at h0 ⊢; ext <;> simp <;> omega
          · exact Or.inr h1
      · rcases h2 with h2 | h2
        · exact Or.inl h2
        · rcases Nat.eq_zero_or_pos x.2 with h0 | h0
          · exact Or.inl h0
          right
          simp only [Finset.mem_insert] at h2 ⊢
          rcases h2 with h2 | h2 | h2
          · exfalso; have := congrArg Prod.snd h2; simp at this; omega
          · exfalso; apply hna; left
            rw [← h2]; obtain ⟨a, b⟩ := x
            simp only at h0 ⊢; ext <;> simp <;> omega
          · exact Or.inr h2
    · obtain ⟨h1, h2⟩ := hD x hx
      exact ⟨h1.imp_right (Finset.mem_insert_of_mem), h2.imp_right (Finset.mem_insert_of_mem)⟩

/-- **(C1) The single-step lemma.** One elementary switch at the hole: if `y` is adjacent the
chain is kept (letters swap cells: the hole moves to `y`), otherwise the middle becomes
`D ∪ {y}` (each letter keeps its cell), for every shape. -/
theorem switchL_step {D : Finset Cell} {h y : Cell} (hD : IsDiag D) (hhD : h ∉ D)
    (hDh : IsDiag (insert h D)) (hy : y ∉ insert h D) (hDhy : IsDiag (insert y (insert h D))) :
    switchL D (insert h D) (insert y (insert h D)) =
      if Adj h y then insert h D else insert y D := by
  have hyh : y ≠ h := fun e => hy (e ▸ Finset.mem_insert_self _ _)
  have hyD : y ∉ D := fun e => hy (Finset.mem_insert_of_mem e)
  have ho : other D (insert h D) (insert y (insert h D)) = insert y D := by
    ext x
    simp only [other, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
    constructor
    · rintro (hx | ⟨hx1, hx2⟩)
      · exact Or.inr hx
      · tauto
    · rintro (rfl | hx)
      · right; exact ⟨Or.inl rfl, by tauto⟩
      · exact Or.inl hx
  have hiff := isDiag_insert_iff_not_adj hD hhD hyh hDhy
  unfold switchL
  rw [ho]
  by_cases ha : Adj h y
  · rw [if_pos ha, if_neg]
    rintro ⟨-, -, -, hd⟩
    exact (hiff.1 hd) ha
  · rw [if_neg ha, if_pos]
    exact ⟨Finset.subset_insert _ _, Finset.subset_insert _ _, hDh, hiff.2 ha⟩

/-! ### C2a: the switch product is the chain of `carryW` -/

lemma switchAt_cons_succ (a : Finset Cell) (ch : List (Finset Cell)) {t : ℕ} (ht : 1 ≤ t) :
    switchAt (a :: ch) (t + 1) = a :: switchAt ch t := by
  unfold switchAt
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  simp

lemma foldl_cons_switch (a : Finset Cell) (l : List ℕ)
    (ch : List (Finset Cell)) :
    l.foldl (fun c t => switchAt c (t + 1 + 1)) (a :: ch) =
      a :: l.foldl (fun c t => switchAt c (t + 1)) ch := by
  induction l generalizing ch with
  | nil => rfl
  | cons t l ih =>
    simp only [List.foldl_cons]
    rw [switchAt_cons_succ a ch (by omega)]
    exact ih _

lemma carry_succ (p : ℕ) (a b c : Finset Cell) (rest : List (Finset Cell)) :
    carry (p + 1) (a :: b :: c :: rest) = a :: carry p (switchL a b c :: c :: rest) := by
  unfold carry
  rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
  have h0 : switchAt (a :: b :: c :: rest) (0 + 1) = a :: switchL a b c :: c :: rest := by
    simp [switchAt]
  rw [h0]
  exact foldl_cons_switch a _ _

lemma chainOf_eq_cons (X : Finset Cell) (F : List Cell) : ∃ rest, chainOf X F = X :: rest := by
  cases F <;> exact ⟨_, rfl⟩

/-- The invariant of the switch side. -/
def ChainInv (D : Finset Cell) (h : Cell) (F : List Cell) : Prop :=
  IsDiag D ∧ h ∉ D ∧ IsDiag (insert h D) ∧ StdFrom (insert h D) F

lemma chainInv_next {D : Finset Cell} {h y : Cell} {F : List Cell}
    (hI : ChainInv D h (y :: F)) :
    (Adj h y → ChainInv (insert h D) y F) ∧ (¬ Adj h y → ChainInv (insert y D) h F) := by
  obtain ⟨hD, hhD, hDh, hy, hDhy, hS⟩ := hI
  have hyh : y ≠ h := fun e => hy (e ▸ Finset.mem_insert_self _ _)
  refine ⟨fun _ => ⟨hDh, hy, hDhy, hS⟩, fun ha => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact (isDiag_insert_iff_not_adj hD hhD hyh hDhy).2 ha
  · simp only [Finset.mem_insert, not_or]; exact ⟨hyh.symm, hhD⟩
  · rwa [Finset.insert_comm]
  · rwa [Finset.insert_comm]

/-- **(C2a)** The product `s_p ∘ ⋯ ∘ s_1` carrying the hole past `F` turns the chain of the
word `h :: F` into the chain of the word `carryW h F`. -/
theorem carry_chainOf (F : List Cell) : ∀ (D : Finset Cell) (h : Cell), ChainInv D h F →
    carry F.length (chainOf D (h :: F)) = chainOf D (carryW h F) := by
  induction F with
  | nil => intro D h _; rfl
  | cons y F ih =>
    intro D h hI
    have hnext := chainInv_next hI
    obtain ⟨hD, hhD, hDh, hy, hDhy, -⟩ := hI
    have hstep := switchL_step hD hhD hDh hy hDhy
    obtain ⟨rest, hrest⟩ := chainOf_eq_cons (insert y (insert h D)) F
    have e0 : chainOf D (h :: y :: F) = D :: insert h D :: insert y (insert h D) :: rest := by
      simp only [chainOf]; rw [hrest]
    rw [List.length_cons, e0, carry_succ, hstep, ← hrest]
    by_cases ha : Adj h y
    · rw [if_pos ha]
      have := ih (insert h D) y (hnext.1 ha)
      simp only [carryW, if_pos ha, chainOf]
      rw [← this]; rfl
    · rw [if_neg ha]
      have := ih (insert y D) h (hnext.2 ha)
      simp only [carryW, if_neg ha, chainOf]
      rw [← this, chainOf, Finset.insert_comm]

/-! ### C2b: the jdt slide is `carryW` -/

/-- `x` lies in the (closed) upper quadrant of `z`. -/
def Ge (z x : Cell) : Prop := z.1 ≤ x.1 ∧ z.2 ≤ x.2

lemma jdtStep_cons (s : Bool) {x z : Cell} (hx : ¬ Ge z x) (L : List Cell) :
    jdtStep s (x :: L) z = (jdtStep s L z).map (fun r => (x :: r.1, r.2)) := by
  have he : (x == (z.1, z.2 + 1)) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact hx ⟨le_refl _, by simp⟩
  have hn : (x == (z.1 + 1, z.2)) = false := by
    rw [beq_eq_false_iff_ne]; rintro rfl; exact hx ⟨by simp, le_refl _⟩
  unfold jdtStep
  simp only [List.idxOf?_cons, he, hn, Bool.false_eq_true, if_false]
  rcases L.idxOf? (z.1, z.2 + 1) with _ | i <;> rcases L.idxOf? (z.1 + 1, z.2) with _ | j <;>
    simp only [Option.map_none, Option.map_some, List.set_cons_succ]
  have : decide (i + 1 < j + 1) = decide (i < j) := by simp
  rw [this]
  split <;> rfl

lemma jdtStep_some {s : Bool} {L c' : List Cell} {z z' : Cell}
    (h : jdtStep s L z = some (c', z')) : Adj z z' := by
  unfold jdtStep at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact Or.inl rfl
  · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact Or.inr rfl
  · split at h
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact Or.inl rfl
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact Or.inr rfl

lemma not_ge_of_adj {x z z' : Cell} (hx : ¬ Ge z x) (ha : Adj z z') : ¬ Ge z' x := by
  rintro ⟨h1, h2⟩
  apply hx
  rcases ha with rfl | rfl <;> simp only at h1 h2 <;> exact ⟨by omega, by omega⟩

/-- A cell outside the upper quadrant of the hole is never looked at again. -/
theorem jdt_cons_irrel (s : Bool) (x : Cell) :
    ∀ (k : ℕ) (L : List Cell) (z : Cell), ¬ Ge z x →
      jdt s k (x :: L) z = (x :: (jdt s k L z).1, (jdt s k L z).2) := by
  intro k
  induction k with
  | zero => intro L z _; rfl
  | succ k ih =>
    intro L z hx
    simp only [jdt]
    rw [jdtStep_cons s hx L]
    rcases hst : jdtStep s L z with _ | ⟨c', z'⟩
    · rfl
    · simp only [Option.map_some]
      exact ih c' z' (not_ge_of_adj hx (jdtStep_some hst))

/-- An adjacent head cell is the smaller neighbour (it has index `0`). -/
lemma jdtStep_adj_head {h y : Cell} (ha : Adj h y) (L : List Cell) :
    jdtStep true (y :: L) h = some (h :: L, y) := by
  unfold jdtStep
  rcases ha with rfl | rfl
  · have hn : ((h.1, h.2 + 1) == (h.1 + 1, h.2)) = false := by
      rw [beq_eq_false_iff_ne]; intro e; have := congrArg Prod.fst e; simp at this
    simp only [List.idxOf?_cons, beq_self_eq_true, if_true, hn, Bool.false_eq_true, if_false]
    rcases L.idxOf? (h.1 + 1, h.2) with _ | j <;> simp
  · have he : ((h.1 + 1, h.2) == (h.1, h.2 + 1)) = false := by
      rw [beq_eq_false_iff_ne]; intro e; have := congrArg Prod.fst e; simp at this
    simp only [List.idxOf?_cons, beq_self_eq_true, if_true, he, Bool.false_eq_true, if_false]
    rcases L.idxOf? (h.1, h.2 + 1) with _ | i <;> simp

/-- The invariant of the jdt side: no placed cell is in the upper quadrant of the hole, and the
rest of `F` is standard over the placed cells plus the hole. -/
def JdtInv (D : Finset Cell) (h : Cell) (F : List Cell) : Prop :=
  (∀ c ∈ D, ¬ Ge h c) ∧ StdFrom (insert h D) F

/-- Standardness at work (the tex's "cells that already swapped lie west or south of the hole"):
a next cell that is not adjacent to the hole is outside its upper quadrant. -/
lemma not_ge_of_not_adj {D : Finset Cell} {h y : Cell} (hQ : ∀ c ∈ D, ¬ Ge h c)
    (hy : y ∉ insert h D) (hDhy : IsDiag (insert y (insert h D))) (hna : ¬ Adj h y) :
    ¬ Ge h y := by
  intro hge
  have hyh : y ≠ h := fun e => hy (e ▸ Finset.mem_insert_self _ _)
  obtain ⟨h1, h2⟩ := hDhy y (Finset.mem_insert_self _ _)
  -- the predecessor in a direction where `y` exceeds `h` is in the upper quadrant
  by_cases hr : h.1 < y.1
  · rcases h1 with h1 | h1
    · omega
    · simp only [Finset.mem_insert] at h1
      rcases h1 with h1 | h1 | h1
      · have := congrArg Prod.fst h1; simp at this; omega
      · apply hna; right; rw [← h1]; obtain ⟨a, b⟩ := y; simp only at hr ⊢; ext <;> simp; omega
      · exact hQ _ h1 ⟨by simp; omega, by simpa using hge.2⟩
  · have hr1 : y.1 = h.1 := by have := hge.1; omega
    have hc : h.2 < y.2 := by
      rcases Nat.lt_or_ge h.2 y.2 with h' | h'
      · exact h'
      · exfalso; apply hyh; obtain ⟨a, b⟩ := y; ext <;> simp_all; have := hge.2; omega
    rcases h2 with h2 | h2
    · omega
    · simp only [Finset.mem_insert] at h2
      rcases h2 with h2 | h2 | h2
      · have := congrArg Prod.snd h2; simp at this; omega
      · apply hna; left; rw [← h2]; obtain ⟨a, b⟩ := y; simp only at hc hr1 ⊢; ext <;> simp; omega
      · exact hQ _ h2 ⟨by simpa [hr1] using hge.1, by simp; omega⟩

/-- **(C2b)** With fuel at least `|F| + 1`, the jdt forward slide ("smaller of east and north")
returns the cell word `carryW h F` (the cells of `F'_1, …, F'_p`, then the final hole). -/
theorem jdt_eq_carryW (F : List Cell) : ∀ (D : Finset Cell) (h : Cell) (k : ℕ),
    JdtInv D h F → F.length + 1 ≤ k →
      (jdt true k F h).1 ++ [(jdt true k F h).2] = carryW h F := by
  induction F with
  | nil =>
    intro D h k _ hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    rfl
  | cons y F ih =>
    intro D h k hI hk
    obtain ⟨hQ, hy, hDhy, hS⟩ := hI
    by_cases ha : Adj h y
    · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
      have hyh : ¬ Ge y h := by
        rintro ⟨h1, h2⟩; rcases ha with rfl | rfl <;> simp at h1 h2 <;> omega
      have hQ' : ∀ c ∈ insert h D, ¬ Ge y c := by
        intro c hc
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact hyh
        · intro hge; apply hQ c hc
          rcases ha with rfl | rfl <;> simp only [Ge] at hge ⊢ <;> exact ⟨by omega, by omega⟩
      simp only [jdt, jdtStep_adj_head ha, carryW, if_pos ha]
      rw [jdt_cons_irrel true h k F y hyh]
      simp only [List.cons_append]
      rw [ih (insert h D) y k ⟨hQ', hS⟩ (by simp at hk; omega)]
    · have hng := not_ge_of_not_adj hQ hy hDhy ha
      have hQ' : ∀ c ∈ insert y D, ¬ Ge h c := by
        intro c hc
        rw [Finset.mem_insert] at hc
        rcases hc with rfl | hc
        · exact hng
        · exact hQ c hc
      rw [jdt_cons_irrel true y k F h hng]
      simp only [carryW, if_neg ha, List.cons_append]
      rw [ih (insert y D) h k ⟨hQ', by rwa [Finset.insert_comm]⟩ (by simp at hk; omega)]

/-! ### The general theorem -/

/-- Each cell of the word is new when it is added. -/
def Fresh : Finset Cell → List Cell → Prop
  | _, [] => True
  | D, x :: w => x ∉ D ∧ Fresh (insert x D) w

lemma lettersOf_chainOf (w : List Cell) :
    ∀ D, Fresh D w → lettersOf (chainOf D w) = w.map ({·}) := by
  induction w with
  | nil => intro D _; rfl
  | cons x w ih =>
    intro D ⟨hx, hw⟩
    obtain ⟨rest, hrest⟩ := chainOf_eq_cons (insert x D) w
    have e : chainOf D (x :: w) = D :: insert x D :: rest := by simp only [chainOf]; rw [hrest]
    rw [e, lettersOf, ← hrest, ih _ hw, List.map_cons, Finset.insert_sdiff_cancel hx]

lemma fresh_carryW (F : List Cell) : ∀ D h, ChainInv D h F → Fresh D (carryW h F) := by
  induction F with
  | nil => intro D h hI; exact ⟨hI.2.1, trivial⟩
  | cons y F ih =>
    intro D h hI
    have hnext := chainInv_next hI
    by_cases ha : Adj h y
    · simp only [carryW, if_pos ha]
      exact ⟨hI.2.1, ih _ _ (hnext.1 ha)⟩
    · simp only [carryW, if_neg ha]
      refine ⟨fun e => hI.2.2.2.1 (Finset.mem_insert_of_mem e), ih _ _ (hnext.2 ha)⟩

/-- Diagrams are lower sets. -/
lemma IsDiag.mem_of_ge {S : Finset Cell} (hS : IsDiag S) (h : Cell) :
    ∀ n, ∀ c ∈ S, c.1 + c.2 = n → Ge h c → h ∈ S := by
  intro n
  induction n with
  | zero =>
    intro c hc hn hge
    have : c = h := by obtain ⟨a, b⟩ := c; obtain ⟨hge1, hge2⟩ := hge; ext <;> simp at * <;> omega
    exact this ▸ hc
  | succ n ih =>
    intro c hc hn hge
    obtain ⟨h1, h2⟩ := hS c hc
    by_cases hr : h.1 < c.1
    · rcases h1 with h1 | h1
      · omega
      · exact ih _ h1 (by simp; omega) ⟨by simp; omega, by simpa using hge.2⟩
    by_cases hcol : h.2 < c.2
    · rcases h2 with h2 | h2
      · omega
      · exact ih _ h2 (by simp; omega) ⟨by simpa using hge.1, by simp; omega⟩
    have : c = h := by
      obtain ⟨a, b⟩ := c; obtain ⟨hge1, hge2⟩ := hge; ext <;> simp at * <;> omega
    exact this ▸ hc

/-- **G4 Lemma D, half (i), forward slide, all shapes.**
`projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D` (l.172–183): for every diagram
`κ₀`, every cell `h` with `κ₀ ∪ {h}` a diagram (so `h` is an inner corner of `κ = κ₀ ∪ {h}`),
and every standard filling `F` of a skew shape `ν / κ` (`StdFrom κ F`), the jdt forward slide
into `h` ("smaller of east and north") equals the product `s_p ∘ ⋯ ∘ s_1` of elementary
switches carrying the hole past `F_1, …, F_p`. -/
theorem slide_eq_switch_product (κ₀ : Finset Cell) (h : Cell) (F : List Cell)
    (hκ : IsDiag κ₀) (hh : h ∉ κ₀) (hκh : IsDiag (insert h κ₀))
    (hF : StdFrom (insert h κ₀) F) :
    switchSide κ₀ h F = jdtSide true h F := by
  have hI : ChainInv κ₀ h F := ⟨hκ, hh, hκh, hF⟩
  have hQ : ∀ c ∈ κ₀, ¬ Ge h c := fun c hc hge => hh (hκ.mem_of_ge h _ c hc rfl hge)
  unfold switchSide jdtSide
  rw [carry_chainOf F κ₀ h hI, lettersOf_chainOf _ κ₀ (fresh_carryW F κ₀ h hI)]
  dsimp only
  rw [jdt_eq_carryW F κ₀ h _ ⟨hQ, hF⟩ le_rfl]

/-- The hypotheses of `slide_eq_switch_product`, checked on every enumerated instance. -/
def hypCheck (N : ℕ) : Bool :=
  (instances N (stdFill N)).all fun ⟨κ₀, h, F⟩ =>
    decide (IsDiag κ₀ ∧ h ∉ κ₀ ∧ IsDiag (insert h κ₀) ∧ StdFrom (insert h κ₀) F)

/-- The finite check follows from the general theorem once the enumeration is seen to produce
only instances satisfying its hypotheses. -/
theorem slideCheck_of_hypCheck {N : ℕ} (hN : hypCheck N = true) : slideCheck N = true := by
  unfold hypCheck at hN
  unfold slideCheck
  rw [List.all_eq_true] at hN ⊢
  rintro ⟨κ₀, h, F⟩ hm
  have := hN _ hm
  simp only [decide_eq_true_eq] at this
  obtain ⟨h1, h2, h3, h4⟩ := this
  simpa using slide_eq_switch_product κ₀ h F h1 h2 h3 h4

/-- **Sanity corollary** (the tier-B theorem, re-derived from the general one): here the kernel
only checks the hypotheses of the 162 instances; the equality comes from
`slide_eq_switch_product`. -/
theorem slide_eq_switch_product_le5' : slideCheck 5 = true :=
  slideCheck_of_hypCheck (by decide +kernel)

/-- The `|ν| ≤ 6` check (495 instances), previously `#guard`-only (kernel `decide` on the switch
product timed out at 580 s), now a theorem: the kernel decides only the hypotheses. -/
theorem slide_eq_switch_product_le6 : slideCheck 6 = true :=
  slideCheck_of_hypCheck (by decide +kernel)

/-- **Lesion (C2).** The general statement with "larger of east and north" is false: the tier-B
instance `lesion_larger` satisfies every hypothesis. -/
theorem slide_eq_switch_product_larger_false :
    ¬ ∀ (κ₀ : Finset Cell) (h : Cell) (F : List Cell), IsDiag κ₀ → h ∉ κ₀ →
      IsDiag (insert h κ₀) → StdFrom (insert h κ₀) F → switchSide κ₀ h F = jdtSide false h F :=
  fun H => lesion_larger (H ∅ (0, 0) [(0, 1), (1, 0)] (by decide) (by decide) (by decide)
    (by decide))

/-- **Lesion (standardness).** Dropping `StdFrom` is not harmless: `lesion_nonstandard`
satisfies the other three hypotheses. -/
theorem slide_eq_switch_product_nonstd_false :
    ¬ ∀ (κ₀ : Finset Cell) (h : Cell) (F : List Cell), IsDiag κ₀ → h ∉ κ₀ →
      IsDiag (insert h κ₀) → switchSide κ₀ h F = jdtSide true h F :=
  fun H => lesion_nonstandard (H ∅ (0, 0) [(0, 2), (0, 1)] (by decide) (by decide) (by decide))

end TworowD4Kernel.SlideSwitch
