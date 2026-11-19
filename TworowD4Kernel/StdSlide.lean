/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Prod.Lex
import TworowD4Kernel.SlideSwitch

/-!
# G4 Lemma A: standardisation commutes with jdt slides

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:A`, l.131–147.

> For semistandard `X` and any forward slide `s`, the hole follows the same path in `X` and in
> `std X`, and `std(sX) = s(std X)`. … The mirror statement also holds: for reverse slides with
> the tie rule "south", and the standardisation (value, column), the same conclusion holds.

## Representation

A cell is `(r, c)` (`SlideSwitch.Cell`; column = `.2`). A *filling* is a support
`S : Finset Cell` with a value function `X : Cell → ℕ` (values off `S` are junk). The hole `h`
is a cell not in `S`.

* Forward step: neighbours `n = (r+1, c)` (north) and `e = (r, c+1)` (east). If both are in `S`
  the hole takes `n` iff `X n ≤ X e` (tie → north), i.e. the smaller.
* Reverse step: neighbours `s = (r-1, c)` (south) and `w = (r, c-1)` (west). If both are in
  `S` the hole takes `s` iff `X w ≤ X s` (tie → south), i.e. the larger.
* `key X y = toLex (X y, y.2)` (value, then column) and `std S X y` = the number of cells of `S`
  with strictly smaller key: the tex's "numbers the cells in the order (value, then column)".

## What the tex's proof uses, and how it enters here

The path claim needs nothing (`fwdChoice_std`, `revChoice_std`): `≤` on `X` at `n` vs `e` is
`≤` on keys because `n` is west of `e`; `std` is strictly monotone in the key unconditionally.

`std(sX) = s(std X)` needs column-injectivity (`ColInj`: no two cells of one column carry the same
value) of **both** `X` and `sX`; this is the tex's "Column `c+1` is impossible because `X` is
column strict. Column `c` is impossible because `sX` is column strict." The second is the
classical fact that jdt preserves semistandardness (Fulton §1.2), **recalled** in the tex; it is a
hypothesis here (`ColInj` of each intermediate filling, `SlideOK`), not proved.
-/

namespace TworowD4Kernel.StdSlide

open TworowD4Kernel.SlideSwitch Finset

/-- The (value, column) key. -/
def key (X : Cell → ℕ) (y : Cell) : ℕ ×ₗ ℕ := toLex (X y, y.2)

/-- Standardisation: rank of the key among the cells of `S`. -/
def std (S : Finset Cell) (X : Cell → ℕ) (y : Cell) : ℕ :=
  (S.filter fun b => key X b < key X y).card

/-- Column-injectivity on `S` (what "column strict" is used for in the tex). -/
def ColInj (S : Finset Cell) (X : Cell → ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → X a = X b → a = b

/-! ### `std` is strictly monotone in the key (no hypotheses) -/

lemma std_lt_iff (S : Finset Cell) (X : Cell → ℕ) {a b : Cell} (ha : a ∈ S) :
    std S X a < std S X b ↔ key X a < key X b := by
  unfold std
  constructor
  · intro h
    by_contra hk
    rw [not_lt] at hk
    have : (S.filter fun c => key X c < key X b) ⊆ (S.filter fun c => key X c < key X a) := by
      intro c hc
      simp only [mem_filter] at hc ⊢
      exact ⟨hc.1, lt_of_lt_of_le hc.2 hk⟩
    exact absurd (card_le_card this) (not_le.2 h)
  · intro h
    apply card_lt_card
    refine ⟨fun c hc => ?_, fun hsub => ?_⟩
    · simp only [mem_filter] at hc ⊢
      exact ⟨hc.1, lt_trans hc.2 h⟩
    · have := hsub (mem_filter.2 ⟨ha, h⟩)
      simp at this

lemma std_le_iff (S : Finset Cell) (X : Cell → ℕ) {a b : Cell} (hb : b ∈ S) :
    std S X a ≤ std S X b ↔ key X a ≤ key X b := by
  rw [← not_lt, ← not_lt, std_lt_iff S X hb]

/-! ### The single forward step -/

/-- North and east neighbours. -/
def nN (h : Cell) : Cell := (h.1 + 1, h.2)
def nE (h : Cell) : Cell := (h.1, h.2 + 1)

/-- The cell the hole takes in a forward step (tie → north), for any value type. -/
def fwdChoice {α : Type*} [LinearOrder α] (S : Finset Cell) (X : Cell → α) (h : Cell) :
    Option Cell :=
  if nN h ∈ S then
    if nE h ∈ S then (if X (nN h) ≤ X (nE h) then some (nN h) else some (nE h))
    else some (nN h)
  else if nE h ∈ S then some (nE h) else none

/-- The tie rule is exactly the key order: `n` is west of `e`. -/
lemma le_iff_key_le_NE (X : Cell → ℕ) (h : Cell) :
    X (nN h) ≤ X (nE h) ↔ key X (nN h) ≤ key X (nE h) := by
  simp only [key, nN, nE, Prod.Lex.toLex_le_toLex]
  omega

/-- **Lemma A, path part, one forward step.** The hole takes the same cell in `X` and in
`std X`. No semistandardness is needed. -/
theorem fwdChoice_std (S : Finset Cell) (X : Cell → ℕ) (h : Cell) :
    fwdChoice S (std S X) h = fwdChoice S X h := by
  unfold fwdChoice
  split_ifs with h1 h2 h3 h3 <;> try rfl
  · exact absurd ((le_iff_key_le_NE X h).2 ((std_le_iff S X (a := nN h) h2).1 ‹_›)) ‹_›
  · exact absurd ((std_le_iff S X (a := nN h) h2).2 ((le_iff_key_le_NE X h).1 ‹_›)) ‹_›

/-! ### Applying a move -/

/-- Move the entry at `y` into the hole `h`: new support and new values. -/
def moveS (S : Finset Cell) (h y : Cell) : Finset Cell := insert h (S.erase y)
def moveX {α : Type*} (X : Cell → α) (h y : Cell) : Cell → α := Function.update X h (X y)

/-- Where the entry now at `a` came from. -/
def src (h y a : Cell) : Cell := if a = h then y else a

lemma moveX_eq_src {α : Type*} (X : Cell → α) (h y a : Cell) :
    moveX X h y a = X (src h y a) := by
  unfold moveX src
  by_cases ha : a = h
  · subst ha; simp
  · simp [ha]

/-- The key comparison is transported by `src`, provided the moved entry keeps its relative
order with every equal entry. `hcol` says: the only way the key of the moved entry changes is its
column, from `y.2` to `h.2`, and no other cell between those columns (inclusive) carries its value.
-/
lemma key_move_lt_iff (S : Finset Cell) (X : Cell → ℕ) {h y : Cell}
    (hcol : ∀ b ∈ S, b ≠ y → X b = X y → b.2 ≠ y.2 ∧ b.2 ≠ h.2)
    (hhy : h.2 = y.2 ∨ h.2 + 1 = y.2 ∨ y.2 + 1 = h.2)
    {a b : Cell} (ha : a ∈ moveS S h y) (hb : b ∈ moveS S h y) :
    key (moveX X h y) a < key (moveX X h y) b ↔ key X (src h y a) < key X (src h y b) := by
  have hmem : ∀ c ∈ moveS S h y, c ≠ h → c ∈ S ∧ c ≠ y := by
    intro c hc hch
    simp only [moveS, mem_insert, mem_erase] at hc
    rcases hc with hc | ⟨h1, h2⟩
    · exact absurd hc hch
    · exact ⟨h2, h1⟩
  -- the comparison of the moved entry with a fixed entry `b`
  have side : ∀ b ∈ moveS S h y, b ≠ h →
      ((X y < X b ∨ X y = X b ∧ h.2 < b.2) ↔ (X y < X b ∨ X y = X b ∧ y.2 < b.2)) ∧
      ((X b < X y ∨ X b = X y ∧ b.2 < h.2) ↔ (X b < X y ∨ X b = X y ∧ b.2 < y.2)) := by
    intro b hb hbh
    obtain ⟨hbS, hby⟩ := hmem b hb hbh
    by_cases hv : X b = X y
    · have := hcol b hbS hby hv
      constructor <;> constructor <;> rintro (h1 | ⟨h1, h2⟩) <;> first
        | exact Or.inl h1 | (right; exact ⟨h1, by omega⟩)
    · constructor <;> constructor <;> rintro (h1 | ⟨h1, h2⟩) <;> first
        | exact Or.inl h1 | exact absurd h1.symm hv | exact absurd h1 hv
  simp only [key, moveX, src, Prod.Lex.toLex_lt_toLex]
  by_cases hah : a = h <;> by_cases hbh : b = h
  · rw [if_pos hah, if_pos hbh, hah, hbh]; simp
  · rw [if_pos hah, if_neg hbh, hah, Function.update_self, Function.update_of_ne hbh]
    exact (side b hb hbh).1
  · rw [if_neg hah, if_pos hbh, hbh, Function.update_self, Function.update_of_ne hah]
    exact (side a ha hah).2
  · rw [if_neg hah, if_neg hbh, Function.update_of_ne hah, Function.update_of_ne hbh]

/-- **Lemma A, `std` part, one move.** Under `key_move_lt_iff`'s hypothesis, `std` of the moved
filling is the moved `std`: `std(sX) = s(std X)` on the new support. -/
theorem std_move (S : Finset Cell) (X : Cell → ℕ) {h y : Cell} (hhS : h ∉ S) (hyS : y ∈ S)
    (hcol : ∀ b ∈ S, b ≠ y → X b = X y → b.2 ≠ y.2 ∧ b.2 ≠ h.2)
    (hhy : h.2 = y.2 ∨ h.2 + 1 = y.2 ∨ y.2 + 1 = h.2) :
    ∀ a ∈ moveS S h y, std (moveS S h y) (moveX X h y) a = moveX (std S X) h y a := by
  intro a ha
  rw [moveX_eq_src]
  unfold std
  -- `src` is a bijection `moveS S h y → S` transporting the key order.
  apply card_nbij (src h y)
  · intro b hb
    simp only [coe_filter, Set.mem_setOf_eq] at hb ⊢
    refine ⟨?_, (key_move_lt_iff S X hcol hhy hb.1 ha).1 hb.2⟩
    by_cases hbh : b = h
    · simp [src, hbh, hyS]
    · have := hb.1
      simp only [moveS, mem_insert, mem_erase] at this
      rcases this with rfl | ⟨-, h2⟩
      · exact absurd rfl hbh
      · simpa [src, hbh] using h2
  · intro b₁ hb₁ b₂ hb₂ he
    simp only [coe_filter, Set.mem_setOf_eq] at hb₁ hb₂
    have m1 := hb₁.1; have m2 := hb₂.1
    simp only [moveS, mem_insert, mem_erase] at m1 m2
    unfold src at he
    split_ifs at he with e1 e2 e2
    · rw [e1, e2]
    · rcases m2 with m2 | ⟨m2, -⟩
      · exact absurd m2 e2
      · exact absurd he.symm m2
    · rcases m1 with m1 | ⟨m1, -⟩
      · exact absurd m1 e1
      · exact absurd he m1
    · exact he
  · intro c hc
    simp only [coe_filter, Set.mem_setOf_eq] at hc
    by_cases hcy : c = y
    · subst hcy
      refine ⟨h, ?_, by simp [src]⟩
      simp only [coe_filter, Set.mem_setOf_eq]
      have hm : h ∈ moveS S h c := mem_insert_self _ _
      refine ⟨hm, (key_move_lt_iff S X hcol hhy hm ha).2 (by simpa [src] using hc.2)⟩
    · have hch : c ≠ h := fun e => hhS (e ▸ hc.1)
      have hm : c ∈ moveS S h y := mem_insert_of_mem (mem_erase.2 ⟨hcy, hc.1⟩)
      refine ⟨c, ?_, by simp [src, hch]⟩
      simp only [coe_filter, Set.mem_setOf_eq]
      refine ⟨hm, (key_move_lt_iff S X hcol hhy hm ha).2 (by simpa [src, hch] using hc.2)⟩

/-! ### `ColInj` of `X` and of the moved filling gives the hypothesis of `std_move` -/

lemma hcol_of_colInj {S : Finset Cell} {X : Cell → ℕ} {h y : Cell} (hhS : h ∉ S)
    (h0 : ColInj S X) (h1 : ColInj (moveS S h y) (moveX X h y)) (hyS : y ∈ S) :
    ∀ b ∈ S, b ≠ y → X b = X y → b.2 ≠ y.2 ∧ b.2 ≠ h.2 := by
  intro b hb hby hv
  have hbh : b ≠ h := fun e => hhS (e ▸ hb)
  refine ⟨fun hc => hby (h0 b hb y hyS hc hv), fun hc => hbh ?_⟩
  refine h1 b (mem_insert_of_mem (mem_erase.2 ⟨hby, hb⟩)) h (mem_insert_self _ _) hc ?_
  simp [moveX, Function.update_of_ne hbh, hv]

/-! ### The reverse step (tie → south) -/

/-- South and west neighbours (`ℕ`-subtraction: at the border the "neighbour" is `h` itself,
which is never in the support since `h` is the hole). -/
def nS (h : Cell) : Cell := (h.1 - 1, h.2)
def nW (h : Cell) : Cell := (h.1, h.2 - 1)

/-- The cell the hole takes in a reverse step: the larger of west and south, tie → south. -/
def revChoice {α : Type*} [LinearOrder α] (S : Finset Cell) (X : Cell → α) (h : Cell) :
    Option Cell :=
  if nS h ∈ S then
    if nW h ∈ S then (if X (nW h) ≤ X (nS h) then some (nS h) else some (nW h))
    else some (nS h)
  else if nW h ∈ S then some (nW h) else none

lemma le_iff_key_le_of_col (X : Cell → ℕ) {a b : Cell} (hab : a.2 ≤ b.2) :
    X a ≤ X b ↔ key X a ≤ key X b := by
  simp only [key, Prod.Lex.toLex_le_toLex]
  omega

/-- **Lemma A, path part, one reverse step** (tie rule "south"). -/
theorem revChoice_std (S : Finset Cell) (X : Cell → ℕ) (h : Cell) :
    revChoice S (std S X) h = revChoice S X h := by
  have hc : (nW h).2 ≤ (nS h).2 := by simp [nW, nS]
  unfold revChoice
  split_ifs with h1 h2 h3 h3 <;> try rfl
  · exact absurd ((le_iff_key_le_of_col X hc).2 ((std_le_iff S X (a := nW h) h1).1 ‹_›)) ‹_›
  · exact absurd ((std_le_iff S X (a := nW h) h1).2 ((le_iff_key_le_of_col X hc).1 ‹_›)) ‹_›

/-! ### Rules and iterated slides -/

/-- A slide rule: which neighbour the hole takes. The four fields are what Lemma A uses. -/
structure Rule where
  ch : Finset Cell → (Cell → ℕ) → Cell → Option Cell
  std_inv : ∀ S X h, ch S (std S X) h = ch S X h
  congr : ∀ S X Y h, (∀ a ∈ S, X a = Y a) → ch S X h = ch S Y h
  mem : ∀ S X h y, ch S X h = some y → y ∈ S
  col : ∀ S X h y, ch S X h = some y → h.2 = y.2 ∨ h.2 + 1 = y.2 ∨ y.2 + 1 = h.2

/-- An iterated slide with fuel: final support, final values, final hole, hole path. -/
def slide (R : Rule) : ℕ → Finset Cell → (Cell → ℕ) → Cell →
    Finset Cell × (Cell → ℕ) × Cell × List Cell
  | 0, S, X, h => (S, X, h, [])
  | k + 1, S, X, h =>
      match R.ch S X h with
      | none => (S, X, h, [])
      | some y =>
          let r := slide R k (moveS S h y) (moveX X h y) y
          (r.1, r.2.1, r.2.2.1, y :: r.2.2.2)

/-- Every filling met along the slide is column-injective (the recalled Fulton fact, as a
hypothesis). -/
def SlideOK (R : Rule) : ℕ → Finset Cell → (Cell → ℕ) → Cell → Prop
  | 0, S, X, _ => ColInj S X
  | k + 1, S, X, h =>
      ColInj S X ∧
      match R.ch S X h with
      | none => True
      | some y => SlideOK R k (moveS S h y) (moveX X h y) y

instance decColInj (S : Finset Cell) (X : Cell → ℕ) : Decidable (ColInj S X) := by
  unfold ColInj; infer_instance

instance decSlideOK (R : Rule) : ∀ k S X h, Decidable (SlideOK R k S X h)
  | 0, S, X, _ => decColInj S X
  | k + 1, S, X, h =>
      match hc : R.ch S X h with
      | none => decidable_of_iff (ColInj S X) (by simp [SlideOK, hc])
      | some y =>
          haveI := decSlideOK R k (moveS S h y) (moveX X h y) y
          decidable_of_iff (ColInj S X ∧ SlideOK R k (moveS S h y) (moveX X h y) y)
            (by simp [SlideOK, hc])

lemma SlideOK.colInj {R : Rule} : ∀ {k S X h}, SlideOK R k S X h → ColInj S X
  | 0, _, _, _, hk => hk
  | _ + 1, _, _, _, hk => hk.1

/-- The slide only reads values on the support. -/
theorem slide_congr (R : Rule) : ∀ (k : ℕ) (S : Finset Cell) (X Y : Cell → ℕ) (h : Cell),
    (∀ a ∈ S, X a = Y a) →
    (slide R k S X h).1 = (slide R k S Y h).1 ∧
    (slide R k S X h).2.2 = (slide R k S Y h).2.2 ∧
    ∀ a ∈ (slide R k S X h).1, (slide R k S X h).2.1 a = (slide R k S Y h).2.1 a := by
  intro k
  induction k with
  | zero => intro S X Y h hXY; exact ⟨rfl, rfl, hXY⟩
  | succ k ih =>
    intro S X Y h hXY
    simp only [slide]
    rw [R.congr S X Y h hXY]
    rcases hc : R.ch S Y h with _ | y
    · exact ⟨rfl, rfl, hXY⟩
    · have hyS := R.mem S Y h y hc
      have hm : ∀ a ∈ moveS S h y, moveX X h y a = moveX Y h y a := by
        intro a ha
        rw [moveX_eq_src, moveX_eq_src]
        apply hXY
        by_cases hah : a = h
        · simp [src, hah, hyS]
        · simp only [moveS, mem_insert, mem_erase] at ha
          rcases ha with ha | ⟨-, ha⟩
          · exact absurd ha hah
          · simpa [src, hah] using ha
      obtain ⟨e1, e2, e3⟩ := ih _ _ _ y hm
      exact ⟨e1, by simp [e2], e3⟩

/-- **Lemma A (iterated, any rule).** If every filling along the slide of `X` is
column-injective, then the slide of `std X` has the same hole path, the same final support and
final hole, and its final values are `std` of the final values of the slide of `X`:
`s(std X) = std(sX)`. -/
theorem lemmaA_slide (R : Rule) : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell),
    h ∉ S → SlideOK R k S X h →
    (slide R k S (std S X) h).2.2 = (slide R k S X h).2.2 ∧
    (slide R k S (std S X) h).1 = (slide R k S X h).1 ∧
    ∀ a ∈ (slide R k S X h).1,
      (slide R k S (std S X) h).2.1 a = std (slide R k S X h).1 (slide R k S X h).2.1 a := by
  intro k
  induction k with
  | zero => intro S X h _ _; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | succ k ih =>
    intro S X h hhS hok
    simp only [slide]
    rw [R.std_inv S X h]
    obtain ⟨h0, hrest⟩ := hok
    rcases hc : R.ch S X h with _ | y
    · exact ⟨rfl, rfl, fun _ _ => rfl⟩
    · rw [hc] at hrest
      have hyS := R.mem S X h y hc
      have hyh : y ≠ h := fun e => hhS (e ▸ hyS)
      have hy' : y ∉ moveS S h y := by simp [moveS, hyh]
      have h1 := hrest.colInj
      have hcol := hcol_of_colInj hhS h0 h1 hyS
      have hsm := std_move S X hhS hyS hcol (R.col S X h y hc)
      -- the slide of `moveX (std X)` agrees with the slide of `std (moveX X)`
      obtain ⟨c1, c2, c3⟩ := slide_congr R k _ _ _ y (fun a ha => (hsm a ha).symm)
      obtain ⟨i1, i2, i3⟩ := ih _ _ y hy' hrest
      refine ⟨by simp [c2, i1], by simp [c1, i2], fun a ha => ?_⟩
      simp only at ha ⊢
      rw [c3 a (c1 ▸ i2 ▸ ha), i3 a ha]

/-! ### The two rules of the tex -/

/-- Forward jdt rule: smaller of north/east, tie → north. -/
def fwdRule : Rule where
  ch := fwdChoice
  std_inv := fwdChoice_std
  congr := by
    intro S X Y h hXY
    unfold fwdChoice
    split_ifs with h1 h2 h3 h4 h4 <;> first | rfl | (rw [hXY _ h1, hXY _ h2] at h3; contradiction)
  mem := by
    intro S X h y hy
    unfold fwdChoice at hy
    split_ifs at hy <;> simp_all
  col := by
    intro S X h y hy
    unfold fwdChoice at hy
    split_ifs at hy <;> (simp only [Option.some.injEq] at hy) <;> subst hy <;>
      simp [nN, nE]

/-- Reverse jdt rule: larger of south/west, tie → south. -/
def revRule : Rule where
  ch := revChoice
  std_inv := revChoice_std
  congr := by
    intro S X Y h hXY
    unfold revChoice
    split_ifs with h1 h2 h3 h4 h4 <;> first | rfl | (rw [hXY _ h1, hXY _ h2] at h3; contradiction)
  mem := by
    intro S X h y hy
    unfold revChoice at hy
    split_ifs at hy <;> simp_all
  col := by
    intro S X h y hy
    unfold revChoice at hy
    split_ifs at hy <;> (simp only [Option.some.injEq] at hy) <;> subst hy <;>
      simp [nS, nW] <;> omega

/-- **Lemma A, forward** (tex `lem:A`, first sentence). -/
theorem lemmaA_forward (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hhS : h ∉ S)
    (hok : SlideOK fwdRule k S X h) :
    (slide fwdRule k S (std S X) h).2.2 = (slide fwdRule k S X h).2.2 ∧
    (slide fwdRule k S (std S X) h).1 = (slide fwdRule k S X h).1 ∧
    ∀ a ∈ (slide fwdRule k S X h).1,
      (slide fwdRule k S (std S X) h).2.1 a =
        std (slide fwdRule k S X h).1 (slide fwdRule k S X h).2.1 a :=
  lemmaA_slide fwdRule k S X h hhS hok

/-- **Lemma A, mirror** (tex `lem:A`, last sentence): reverse slides, tie "south". -/
theorem lemmaA_reverse (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell) (hhS : h ∉ S)
    (hok : SlideOK revRule k S X h) :
    (slide revRule k S (std S X) h).2.2 = (slide revRule k S X h).2.2 ∧
    (slide revRule k S (std S X) h).1 = (slide revRule k S X h).1 ∧
    ∀ a ∈ (slide revRule k S X h).1,
      (slide revRule k S (std S X) h).2.1 a =
        std (slide revRule k S X h).1 (slide revRule k S X h).2.1 a :=
  lemmaA_slide revRule k S X h hhS hok

/-! ### Iterating over a list of holes: `V(X) = V(std X)` and `Σ(X) = Σ(std X)` -/

/-- Perform slides into the holes `hs` in order (fuel `k` per slide). Returns the final support,
the final values and the list of vacated cells `V = (z_1, …)`. -/
def slides (R : Rule) (k : ℕ) : Finset Cell → (Cell → ℕ) → List Cell →
    Finset Cell × (Cell → ℕ) × List Cell
  | S, X, [] => (S, X, [])
  | S, X, h :: hs =>
      let r := slide R k S X h
      let q := slides R k r.1 r.2.1 hs
      (q.1, q.2.1, r.2.2.1 :: q.2.2)

/-- Each start hole is outside the current support, and every filling met is column-injective. -/
def SlidesOK (R : Rule) (k : ℕ) : Finset Cell → (Cell → ℕ) → List Cell → Prop
  | _, _, [] => True
  | S, X, h :: hs =>
      h ∉ S ∧ SlideOK R k S X h ∧
      SlidesOK R k (slide R k S X h).1 (slide R k S X h).2.1 hs

theorem slides_congr (R : Rule) (k : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X Y : Cell → ℕ),
    (∀ a ∈ S, X a = Y a) →
    (slides R k S X hs).1 = (slides R k S Y hs).1 ∧
    (slides R k S X hs).2.2 = (slides R k S Y hs).2.2 ∧
    ∀ a ∈ (slides R k S X hs).1, (slides R k S X hs).2.1 a = (slides R k S Y hs).2.1 a := by
  intro hs
  induction hs with
  | nil => intro S X Y hXY; exact ⟨rfl, rfl, hXY⟩
  | cons h hs ih =>
    intro S X Y hXY
    obtain ⟨c1, c2, c3⟩ := slide_congr R k S X Y h hXY
    simp only [slides]
    obtain ⟨d1, d2, d3⟩ := ih _ _ (slide R k S Y h).2.1 c3
    rw [← c1]
    refine ⟨d1, by rw [c2, d2], d3⟩

/-- **Lemma A, iterated over all slides (tex: "Hence `V(X) = V(std X)` and `Σ(X) = Σ(std X)`").**
Running the same holes on `std X` vacates the same cells (`V`), ends on the same support, and
ends with `std` of the final filling of `X`. Since `Σ` labels the vacated cell `z_k` by the row of
the `k`-th processed hole, `Σ` is a function of `(holes, V)`, so equality of `V` is
`Σ(X) = Σ(std X)`. -/
theorem lemmaA_slides (R : Rule) (k : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    SlidesOK R k S X hs →
    (slides R k S (std S X) hs).2.2 = (slides R k S X hs).2.2 ∧
    (slides R k S (std S X) hs).1 = (slides R k S X hs).1 ∧
    ∀ a ∈ (slides R k S X hs).1,
      (slides R k S (std S X) hs).2.1 a = std (slides R k S X hs).1 (slides R k S X hs).2.1 a := by
  intro hs
  induction hs with
  | nil => intro S X _; exact ⟨rfl, rfl, fun _ _ => rfl⟩
  | cons h hs ih =>
    intro S X ⟨hhS, hok, hrest⟩
    obtain ⟨a1, a2, a3⟩ := lemmaA_slide R k S X h hhS hok
    simp only [slides]
    -- the std-side state after the first slide agrees on its support with `std` of the X-side
    obtain ⟨c1, c2, c3⟩ := slides_congr R k hs _ _
      (std (slide R k S X h).1 (slide R k S X h).2.1) a3
    obtain ⟨i1, i2, i3⟩ := ih _ _ hrest
    rw [a2]
    refine ⟨by rw [a1, c2, i1], by rw [c1, i2], fun a ha => ?_⟩
    rw [c3 a (c1 ▸ i2 ▸ ha), i3 a ha]

/-- The vacated-cell sequence `V` of a forward `Σ`-run is the same for `X` and `std X`. -/
theorem V_std_forward (k : ℕ) (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ)
    (hok : SlidesOK fwdRule k S X hs) :
    (slides fwdRule k S (std S X) hs).2.2 = (slides fwdRule k S X hs).2.2 :=
  (lemmaA_slides fwdRule k hs S X hok).1

/-- The mirror: the outward procedure's reverse slides, tie "south". -/
theorem V_std_reverse (k : ℕ) (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ)
    (hok : SlidesOK revRule k S X hs) :
    (slides revRule k S (std S X) hs).2.2 = (slides revRule k S X hs).2.2 :=
  (lemmaA_slides revRule k hs S X hok).1

/-! ### Lemma C: `std ∘ revrot = ~` -/

/-- Rotation by 180° in the `R × C` box (rows `< R`, columns `< C`). -/
def rot (R C : ℕ) (y : Cell) : Cell := (R - 1 - y.1, C - 1 - y.2)

/-- `revrot f` on the rotated support: `(rr f)(rot Y) = ℓ + 1 - f Y`. -/
def rr (R C ℓ : ℕ) (f : Cell → ℕ) (y : Cell) : ℕ := ℓ + 1 - f (rot R C y)

/-- `f̃(rot X)` = position (0-based, like `std`) of `X` in the **reverse** standard order of `f`,
where the standard order is: `f X < f Y`, or `f X = f Y` and `X` west of `Y`
(Purbhoo 0705.1184 §2.2 p.7–8, with the "east to west" typo corrected as in the tex). -/
def tilde (R C : ℕ) (S : Finset Cell) (f : Cell → ℕ) (y : Cell) : ℕ :=
  (S.filter fun Y => f (rot R C y) < f Y ∨ (f Y = f (rot R C y) ∧ (rot R C y).2 < Y.2)).card

def InBox (R C : ℕ) (S : Finset Cell) : Prop := ∀ y ∈ S, y.1 < R ∧ y.2 < C

lemma rot_rot {R C : ℕ} {y : Cell} (hy : y.1 < R ∧ y.2 < C) : rot R C (rot R C y) = y := by
  obtain ⟨a, b⟩ := y
  simp only [rot] at hy ⊢
  ext <;> simp <;> omega

/-- **Lemma C** (tex `lem:C`, l.149): for any filling `f` of a box-contained support with values
`≤ ℓ`, `std (rr f) = f̃` on the rotated support. Semistandardness is not used. -/
theorem lemmaC (R C ℓ : ℕ) (S : Finset Cell) (f : Cell → ℕ) (hS : InBox R C S)
    (hf : ∀ Y ∈ S, f Y ≤ ℓ) :
    ∀ y ∈ S.image (rot R C), std (S.image (rot R C)) (rr R C ℓ f) y = tilde R C S f y := by
  intro y hy
  obtain ⟨X, hX, rfl⟩ := mem_image.1 hy
  have hXb := hS X hX
  unfold std tilde
  rw [filter_image, card_image_of_injOn]
  · congr 1
    apply filter_congr
    intro Y hY
    have hYb := hS Y hY
    simp only [key, rr, rot_rot hYb, rot_rot hXb, Prod.Lex.toLex_lt_toLex]
    have h1 := hf X hX; have h2 := hf Y hY
    simp only [rot]
    omega
  · intro a ha b hb he
    simp only [coe_filter] at ha hb
    rw [← rot_rot (hS a ha.1), he, rot_rot (hS b hb.1)]

/-! ### Control and lesions (kernel-evaluated at small instances) -/

/-- Control instance: a forward tie. `h = (0,0)`, north `(1,0)` and east `(0,1)` both carry `1`. -/
def tieS : Finset Cell := {(1, 0), (0, 1)}
def oneX : Cell → ℕ := fun _ => 1

/-- Control: the tie is met, the hole goes north, and the standardised filling agrees
(the statement of `lemmaA_forward` evaluated, not assumed). The instance satisfies `SlideOK`, so
`lemmaA_forward` applies to it non-vacuously. -/
theorem control_forward_tie :
    (slide fwdRule 2 tieS oneX (0, 0)).2.2.2 = [(1, 0)] ∧
    (slide fwdRule 2 tieS (std tieS oneX) (0, 0)).2.2.2 = [(1, 0)] ∧
    SlideOK fwdRule 2 tieS oneX (0, 0) := by
  decide

/-- Wrong standardisation: equal values numbered **east first**. -/
def stdBad (S : Finset Cell) (X : Cell → ℕ) (y : Cell) : ℕ :=
  (S.filter fun b => X b < X y ∨ (X b = X y ∧ y.2 < b.2)).card

/-- Lesion 1 (tie broken the wrong way in `std`): the path claim fails on the control tie. -/
theorem lesion_std_east_first :
    fwdChoice tieS (stdBad tieS oneX) (0, 0) ≠ fwdChoice tieS oneX (0, 0) := by decide

/-- The reverse rule with the wrong tie (→ west). -/
def revChoiceW (S : Finset Cell) (X : Cell → ℕ) (h : Cell) : Option Cell :=
  if nS h ∈ S then
    if nW h ∈ S then (if X (nW h) < X (nS h) then some (nS h) else some (nW h))
    else some (nS h)
  else if nW h ∈ S then some (nW h) else none

/-- Reverse tie: hole `(1,1)`, south `(0,1)` and west `(1,0)` both carry `1`. -/
def revTieS : Finset Cell := {(0, 1), (1, 0)}

/-- Lesion 2 (reverse slide with tie → west): the hole path in `X` and in `std X` differ.
The correct rule (`revChoice`, tie → south) agrees there. -/
theorem lesion_reverse_tie_west :
    revChoiceW revTieS (std revTieS oneX) (1, 1) ≠ revChoiceW revTieS oneX (1, 1) ∧
    revChoice revTieS (std revTieS oneX) (1, 1) = revChoice revTieS oneX (1, 1) := by decide

/-- Lesion 3a (column-injectivity of `X` dropped): two `1`s in column 1; the slide moves the east
one, and `std` no longer commutes. -/
def badS1 : Finset Cell := {(0, 1), (1, 1)}

theorem lesion_not_colInj_before :
    ¬ ColInj badS1 oneX ∧
    (slide fwdRule 2 badS1 (std badS1 oneX) (0, 0)).2.1 (1, 1) ≠
      std (slide fwdRule 2 badS1 oneX (0, 0)).1 (slide fwdRule 2 badS1 oneX (0, 0)).2.1 (1, 1) := by
  decide

/-- Lesion 3b (column-injectivity of the **slid** filling dropped, `X` itself column-injective):
the moved `1` lands in column 0 under another `1`. So in this abstract model the recalled fact
"jdt preserves semistandardness" is a real input, not a consequence of `ColInj X`. -/
def badS2 : Finset Cell := {(0, 1), (2, 0)}

theorem lesion_not_colInj_after :
    ColInj badS2 oneX ∧
    ¬ ColInj (moveS badS2 (0, 0) (0, 1)) (moveX oneX (0, 0) (0, 1)) ∧
    (slide fwdRule 2 badS2 (std badS2 oneX) (0, 0)).2.1 (0, 0) ≠
      std (slide fwdRule 2 badS2 oneX (0, 0)).1 (slide fwdRule 2 badS2 oneX (0, 0)).2.1 (0, 0) := by
  decide

/-- Lemma C control: a row of two equal entries (`R = 1`, `C = 2`, `ℓ = 1`). The reverse
standard order puts the east cell first, so `f̃(rot (0,1)) = f̃((0,0)) = 0` and
`f̃(rot (0,0)) = f̃((0,1)) = 1`; `std ∘ rr` gives the same numbers. -/
def rowS : Finset Cell := {(0, 0), (0, 1)}

theorem control_lemmaC :
    tilde 1 2 rowS oneX (0, 0) = 0 ∧ tilde 1 2 rowS oneX (0, 1) = 1 ∧
    std (rowS.image (rot 1 2)) (rr 1 2 1 oneX) (0, 0) = 0 ∧
    std (rowS.image (rot 1 2)) (rr 1 2 1 oneX) (0, 1) = 1 := by decide

/-- Lemma C lesion: with Purbhoo's printed "east to west" clause (ties: east cell first in the
standard order), `std ∘ rr` is **not** `f̃` on the control. -/
def tildeTypo (R C : ℕ) (S : Finset Cell) (f : Cell → ℕ) (y : Cell) : ℕ :=
  (S.filter fun Y => f (rot R C y) < f Y ∨ (f Y = f (rot R C y) ∧ Y.2 < (rot R C y).2)).card

theorem lesion_lemmaC_typo :
    std (rowS.image (rot 1 2)) (rr 1 2 1 oneX) (0, 0) ≠ tildeTypo 1 2 rowS oneX (0, 0) := by
  decide

end TworowD4Kernel.StdSlide
