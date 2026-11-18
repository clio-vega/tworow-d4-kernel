/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.LemmaD
import TworowD4Kernel.SlideSwitchReverse

/-!
# G4 Lemma D in slide form: iterated slides are the rows / columns switch products

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D`, l.172–198.
`Σ` slides `U_m, U_{m−1}, …, U_1` in turn forward through the `F`-letters (a row of the grid
`[m] × [p]` each), and the outward procedure slides `F_1, F_2, …, F_p` in turn backward through
the `U`-letters (a column each). `LemmaD.lemmaD_rows_eq_columns` proves the two **switch**
products agree. This file supplies the glue named in the 2026-11-18 c1 note:

* (a) **window lemmas** `window_forward`, `window_reverse`: the switches at positions
  `i, …, i+p−1` act on the *full* configuration `(word, η)` exactly as the one-letter carry on
  the window, i.e. replace the cells `h :: F` of the window by the slid word, and leave every
  cell outside the window where it was (`window_forward_outside`);
* (b) **propagation** `stdFrom_carryW`, and the second component of `carryRev_chainOf`:
  the full cell word stays a standard filling, so the next row's (column's) slide theorem
  applies.

Iterating gives `sigma_eq_rows_product` (iterated forward jdt slides = rows switch product) and
`outward_eq_columns_product` (iterated reverse jdt slides = columns switch product), and with
`lemmaD_rows_eq_columns`, `lemmaD_slides`: **Σ and the outward procedure produce the same
standard filling**, so in particular the same `U`-part — Lemma D in the tex's own terms.

Chains are recorded by their cell words: `lab D₀ w t = D₀ ∪ {w₀, …, w_{t−1}}`
(`phi_chainOf`: this is `phi (chainOf D₀ w)`).
-/

namespace TworowD4Kernel.SlideIteration

open GrowthConfluence SlideSwitch LemmaD Dir

/-! ## Chains of cell words -/

/-- The label function of the chain of the cell word `w` over `D₀`. -/
def lab (D₀ : Finset Cell) (w : List Cell) (t : ℕ) : Finset Cell :=
  if t ≤ w.length then D₀ ∪ (w.take t).toFinset else ∅

lemma getD_chainOf (w : List Cell) : ∀ (D₀ : Finset Cell) (t : ℕ),
    (chainOf D₀ w).getD t ∅ = lab D₀ w t := by
  induction w with
  | nil => intro D₀ t; cases t <;> simp [chainOf, lab]
  | cons x w ih =>
    intro D₀ t
    cases t with
    | zero => simp [chainOf, lab]
    | succ t =>
      simp only [chainOf, List.getD_cons_succ, ih, lab, List.length_cons, List.take_succ_cons,
        List.toFinset_cons, Nat.add_le_add_iff_right]
      split_ifs <;> simp [Finset.insert_union, Finset.union_insert]

/-- The `phi` of `LemmaD` applied to a `chainOf` is `lab`. -/
theorem phi_chainOf (D₀ : Finset Cell) (w : List Cell) : phi (chainOf D₀ w) = lab D₀ w := by
  funext t; exact getD_chainOf w D₀ t

lemma lab_append (D₀ : Finset Cell) (A C : List Cell) (j : ℕ) (hj : j ≤ C.length) :
    lab D₀ (A ++ C) (A.length + j) = D₀ ∪ A.toFinset ∪ (C.take j).toFinset := by
  unfold lab
  rw [if_pos (by simp; omega), List.take_append, List.take_of_length_le (by omega),
    show A.length + j - A.length = j by omega, List.toFinset_append, Finset.union_assoc]

lemma union_append_singleton (D₀ : Finset Cell) (A : List Cell) (x : Cell) :
    D₀ ∪ (A ++ [x]).toFinset = insert x (D₀ ∪ A.toFinset) := by
  ext c; simp only [Finset.mem_union, List.mem_toFinset, List.mem_append, List.mem_singleton,
    Finset.mem_insert]; tauto

/-- Swapping two adjacent cells of the word changes exactly one label. -/
lemma lab_swap (D₀ : Finset Cell) (A C : List Cell) (x y : Cell) :
    Function.update (lab D₀ (A ++ x :: y :: C)) (A.length + 1) (insert y (D₀ ∪ A.toFinset)) =
      lab D₀ (A ++ y :: x :: C) := by
  funext t
  by_cases ht : t = A.length + 1
  · subst ht
    rw [Function.update_self, lab_append _ _ _ _ (by simp)]
    ext c; simp
  · rw [Function.update_of_ne ht]
    unfold lab
    simp only [List.length_append, List.length_cons]
    split_ifs with hle
    · congr 1
      rw [List.take_append, List.take_append]
      rcases Nat.lt_or_ge t (A.length + 1) with hlt | hge
      · rw [show t - A.length = 0 by omega]; simp
      · obtain ⟨k, hk⟩ : ∃ k, t - A.length = k + 2 := ⟨t - A.length - 2, by omega⟩
        rw [hk]
        ext c; simp only [List.toFinset_append, Finset.mem_union, List.mem_toFinset,
          List.take_succ_cons, List.mem_cons]; tauto
    · rfl

/-! ## (a) The window lemma, forward -/

/-- **Window lemma (forward).** Let the word be `a ++ U :: F^p ++ b` and the chain the chain of
the cell word `A ++ (h :: F) ++ B` over `D₀`, with `|a| = |A|`, and let `h :: F` be standard
over `D₀ ∪ A` (`ChainInv`). The switches at positions `|A|, …, |A|+p−1` carry the `U` past the
`p` letters `F` and turn the chain into the chain of `A ++ carryW h F ++ B`: the window
`h :: F` is replaced by the one-letter carry, and nothing outside it moves. -/
theorem window_forward (D₀ : Finset Cell) (F : List Cell) : ∀ (a b : List Dir) (A B : List Cell)
    (h : Cell), a.length = A.length → ChainInv (D₀ ∪ A.toFinset) h F →
    swSeq ((List.range F.length).map (A.length + ·))
        (a ++ D :: (List.replicate F.length R ++ b), lab D₀ (A ++ (h :: F ++ B))) =
      (a ++ List.replicate F.length R ++ D :: b, lab D₀ (A ++ (carryW h F ++ B))) := by
  induction F with
  | nil => intro a b A B h _ _; simp [carryW]
  | cons y F ih =>
    intro a b A B h hlen hI
    have hnext := chainInv_next hI
    obtain ⟨hS, hhS, hSh, hy, hShy, -⟩ := hI
    have hstep := switchL_step hS hhS hSh hy hShy
    set S := D₀ ∪ A.toFinset with hSdef
    -- the three labels at the window's first switch
    have l0 : lab D₀ (A ++ (h :: y :: F ++ B)) A.length = S := by
      have := lab_append D₀ A (h :: y :: F ++ B) 0 (by simp)
      simpa using this
    have l1 : lab D₀ (A ++ (h :: y :: F ++ B)) (A.length + 1) = insert h S := by
      rw [lab_append _ _ _ _ (by simp), hSdef]; ext c; simp
    have l2 : lab D₀ (A ++ (h :: y :: F ++ B)) (A.length + 2) = insert y (insert h S) := by
      rw [lab_append _ _ _ _ (by simp), hSdef]; ext c; simp; tauto
    have hw : a ++ D :: (List.replicate (F.length + 1) R ++ b) =
        a ++ D :: R :: (List.replicate F.length R ++ b) := by simp [List.replicate_succ]
    have hpos : (List.range (F.length + 1)).map (A.length + ·) =
        A.length :: (List.range F.length).map ((A.length + 1) + ·) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
      congr 1; apply List.map_congr_left; intro i _; simp; omega
    have he : (a ++ [R]) ++ List.replicate F.length R ++ D :: b =
        a ++ List.replicate (F.length + 1) R ++ D :: b := by simp [List.replicate_succ]
    have hw' : (a ++ [R]) ++ D :: (List.replicate F.length R ++ b) =
        a ++ R :: D :: (List.replicate F.length R ++ b) := by simp
    rw [List.length_cons, hpos, swSeq_cons, hw, ← hlen, sw_eq, hlen, l0, l1, l2, hstep]
    by_cases ha : Adj h y
    · rw [if_pos ha, ← l1, Function.update_eq_self]
      have hA : D₀ ∪ (A ++ [h]).toFinset = insert h S := union_append_singleton _ _ _
      have := ih (a ++ [R]) b (A ++ [h]) B y (by simp [hlen]) (hA ▸ hnext.1 ha)
      rw [hw', List.length_append, List.length_singleton] at this
      have e1 : (A ++ [h]) ++ (y :: F ++ B) = A ++ (h :: y :: F ++ B) := by simp
      have e2 : (A ++ [h]) ++ (carryW y F ++ B) = A ++ (carryW h (y :: F) ++ B) := by
        simp [carryW, if_pos ha]
      rw [e1, e2, he] at this
      exact this
    · rw [if_neg ha, show A.length + 1 = A.length + 1 from rfl]
      have hsw := lab_swap D₀ A (F ++ B) h y
      simp only [List.cons_append] at hsw ⊢
      rw [hsw]
      have hA : D₀ ∪ (A ++ [y]).toFinset = insert y S := union_append_singleton _ _ _
      have := ih (a ++ [R]) b (A ++ [y]) B h (by simp [hlen]) (hA ▸ hnext.2 ha)
      rw [hw', List.length_append, List.length_singleton] at this
      have e1 : (A ++ [y]) ++ (h :: (F ++ B)) = A ++ (y :: h :: (F ++ B)) := by simp
      have e2 : (A ++ [y]) ++ (carryW h F ++ B) = A ++ (carryW h (y :: F) ++ B) := by
        simp [carryW, if_neg ha]
      simp only [List.cons_append] at this
      rw [e1, e2, he] at this
      exact this

/-! ## (b) Propagation, forward -/

lemma stdFrom_append_of (U w : List Cell) : ∀ D, StdFrom D U →
    StdFrom (D ∪ U.toFinset) w → StdFrom D (U ++ w) := by
  induction U with
  | nil => intro D _ hw; simpa using hw
  | cons x U ih =>
    intro D ⟨hx, hDx, hS⟩ hw
    refine ⟨hx, hDx, ih _ hS ?_⟩
    rwa [List.toFinset_cons, Finset.union_insert, ← Finset.insert_union] at hw

/-- **Propagation.** Carrying the hole keeps the whole word standard. -/
theorem stdFrom_carryW (B : List Cell) (F : List Cell) : ∀ (S : Finset Cell) (h : Cell),
    IsDiag S → StdFrom S (h :: (F ++ B)) → StdFrom S (carryW h F ++ B) := by
  induction F with
  | nil => intro S h _ hS; simpa [carryW] using hS
  | cons y F ih =>
    intro S h hD hS
    obtain ⟨hhS, hSh, hy, hShy, hrest⟩ := hS
    have hyh : y ≠ h := fun e => hy (e ▸ Finset.mem_insert_self _ _)
    by_cases ha : Adj h y
    · simp only [carryW, if_pos ha, List.cons_append]
      exact ⟨hhS, hSh, ih _ y hSh ⟨hy, hShy, hrest⟩⟩
    · simp only [carryW, if_neg ha, List.cons_append]
      have hSy : IsDiag (insert y S) := (isDiag_insert_iff_not_adj hD hhS hyh hShy).2 ha
      refine ⟨fun e => hy (Finset.mem_insert_of_mem e), hSy, ih _ h hSy ⟨?_, ?_, ?_⟩⟩
      · simp only [Finset.mem_insert, not_or]; exact ⟨hyh.symm, hhS⟩
      · rwa [Finset.insert_comm]
      · rwa [Finset.insert_comm]

lemma length_carryW (h : Cell) (F : List Cell) : (carryW h F).length = F.length + 1 := by
  induction F generalizing h with
  | nil => rfl
  | cons y F ih => simp only [carryW]; split_ifs <;> simp [ih]

/-! ## (a) The window lemma, reverse -/

lemma carryWRev_toFinset (h : Cell) (U : List Cell) :
    insert (carryWRev h U).1 (carryWRev h U).2.toFinset = insert h U.toFinset ∧
      (carryWRev h U).2.length = U.length := by
  induction U with
  | nil => simp [carryWRev]
  | cons x U ih =>
    have hc : carryWRev h (x :: U) =
        if Adj x (carryWRev h U).1 then (x, (carryWRev h U).1 :: (carryWRev h U).2)
        else ((carryWRev h U).1, x :: (carryWRev h U).2) := rfl
    obtain ⟨ih1, ih2⟩ := ih
    rw [hc]
    split_ifs
    · refine ⟨?_, by simp [ih2]⟩
      rw [List.toFinset_cons, ih1, List.toFinset_cons, Finset.insert_comm]
    · refine ⟨?_, by simp [ih2]⟩
      rw [List.toFinset_cons, Finset.insert_comm, ih1, List.toFinset_cons, Finset.insert_comm]

/-- **Window lemma (reverse).** Let the word be `a ++ U^k ++ F :: b` and the chain the chain of
`A ++ (U ++ h :: B)` over `D₀`, with `|a| = |A|`, `|U| = k`, and `U ++ [h]` standard over the
diagram `D₀ ∪ A`. The switches at positions `|A|+k−1, …, |A|` carry the `F` leftward past the
`k` letters `U` and turn the chain into the chain of `A ++ (carryWRev h U ++ B)`. -/
theorem window_reverse (D₀ : Finset Cell) (h : Cell) (U : List Cell) :
    ∀ (a b : List Dir) (A B : List Cell), a.length = A.length →
    IsDiag (D₀ ∪ A.toFinset) → StdFrom (D₀ ∪ A.toFinset) (U ++ [h]) →
    swSeq ((List.range U.length).reverse.map (A.length + ·))
        (a ++ (List.replicate U.length D ++ R :: b), lab D₀ (A ++ (U ++ h :: B))) =
      (a ++ R :: (List.replicate U.length D ++ b),
        lab D₀ (A ++ ((carryWRev h U).1 :: (carryWRev h U).2 ++ B))) := by
  induction U with
  | nil => intro a b A B _ _ _; simp [carryWRev]
  | cons x U ih =>
    intro a b A B hlen hS hstd
    set S := D₀ ∪ A.toFinset with hSdef
    obtain ⟨hxS, hSx, hstd'⟩ := hstd
    have hA : D₀ ∪ (A ++ [x]).toFinset = insert x S := union_append_singleton _ _ _
    have hin := ih (a ++ [D]) b (A ++ [x]) B (by simp [hlen]) (hA ▸ hSx) (hA ▸ hstd')
    obtain ⟨-, hz, hSxz, -⟩ := carryRev_chainOf h U (insert x S) hSx hstd'
    set z := (carryWRev h U).1
    set W := (carryWRev h U).2
    have hstep := switchL_step hS hxS hSx hz hSxz
    have hpos : (List.range (U.length + 1)).reverse.map (A.length + ·) =
        (List.range U.length).reverse.map ((A ++ [x]).length + ·) ++ [A.length] := by
      rw [List.range_succ_eq_map, List.reverse_cons, List.map_append, List.map_reverse,
        List.map_reverse, List.map_map]
      simp only [List.map_cons, List.map_nil, Nat.add_zero, List.length_append,
        List.length_singleton]
      congr 2; apply List.map_congr_left; intro i _; simp; omega
    have ew : a ++ (List.replicate (U.length + 1) D ++ R :: b) =
        (a ++ [D]) ++ (List.replicate U.length D ++ R :: b) := by simp [List.replicate_succ]
    have ec : A ++ ((x :: U) ++ h :: B) = (A ++ [x]) ++ (U ++ h :: B) := by simp
    have ew2 : (a ++ [D]) ++ R :: (List.replicate U.length D ++ b) =
        a ++ D :: R :: (List.replicate U.length D ++ b) := by simp
    have ec2 : (A ++ [x]) ++ (z :: W ++ B) = A ++ (x :: z :: (W ++ B)) := by simp
    rw [List.length_cons, hpos, swSeq_append, ew, ec, hin, ew2, ec2, swSeq_cons, swSeq_nil,
      ← hlen, sw_eq, hlen]
    have l0 : lab D₀ (A ++ (x :: z :: (W ++ B))) A.length = S := by
      have := lab_append D₀ A (x :: z :: (W ++ B)) 0 (by simp)
      simpa using this
    have l1 : lab D₀ (A ++ (x :: z :: (W ++ B))) (A.length + 1) = insert x S := by
      rw [lab_append _ _ _ _ (by simp), hSdef]; ext c; simp
    have l2 : lab D₀ (A ++ (x :: z :: (W ++ B))) (A.length + 2) = insert z (insert x S) := by
      rw [lab_append _ _ _ _ (by simp), hSdef]; ext c; simp; tauto
    have ew3 : a ++ R :: D :: (List.replicate U.length D ++ b) =
        a ++ R :: (List.replicate (U.length + 1) D ++ b) := by simp [List.replicate_succ]
    rw [l0, l1, l2, hstep, ew3]
    have hc : carryWRev h (x :: U) = if Adj x z then (x, z :: W) else (z, x :: W) := rfl
    rw [hc]
    by_cases ha : Adj x z
    · rw [if_pos ha, if_pos ha, ← l1, Function.update_eq_self]; simp
    · rw [if_neg ha, if_neg ha, lab_swap]; simp

/-! ## Slides as cell words -/

/-- The forward jdt slide ("smaller of east and north") of the hole `h` through `F`, as a cell
word: the new cells of `F_1, …, F_p`, then the final hole. -/
def slideW (h : Cell) (F : List Cell) : List Cell :=
  (jdt true (F.length + 1) F h).1 ++ [(jdt true (F.length + 1) F h).2]

/-- The reverse jdt slide ("larger of west and south") of the `U`-letters into `h`, as a cell
word: the new cell of `F_j`, then the new cells of `U_1, …, U_m`. -/
def revSlideW (h : Cell) (U : List Cell) : List Cell :=
  (jdtRev true (U.length + 1) U.reverse h).2 :: (jdtRev true (U.length + 1) U.reverse h).1.reverse

lemma slideW_eq_carryW {S : Finset Cell} {h : Cell} {F : List Cell} (hS : IsDiag S)
    (hstd : StdFrom S (h :: F)) : slideW h F = carryW h F := by
  obtain ⟨hh, -, hF⟩ := hstd
  have hQ : ∀ c ∈ S, ¬ Ge h c := fun c hc hge => hh (hS.mem_of_ge h _ c hc rfl hge)
  exact jdt_eq_carryW F S h _ ⟨hQ, hF⟩ le_rfl

lemma revSlideW_eq_carryWRev {S : Finset Cell} {h : Cell} {U : List Cell} (hS : IsDiag S)
    (hstd : StdFrom S (U ++ [h])) :
    revSlideW h U = (carryWRev h U).1 :: (carryWRev h U).2 := by
  obtain ⟨hU, hh, hDUh, -⟩ := stdFrom_append U [h] S hstd
  have hI : JdtInvRev (S ∪ U.toFinset) ∅ h U.reverse :=
    ⟨stdDown_of_stdFrom U S hS hU, by simpa using hDUh, hh, by simp⟩
  have hj := jdtRev_eq_carryV U.reverse _ _ h (U.length + 1) hI (by simp)
  unfold revSlideW
  rw [hj, (carryV_reverse h U).1, (carryV_reverse h U).2, List.reverse_reverse]

/-! ## Σ: iterated forward slides -/

/-- `Σ` on cell words: slide the hole `U_i` (cell `i−1`) forward through the next `p` cells,
for `i = m, m−1, …, 1`. -/
def rowsW (p : ℕ) : ℕ → List Cell → List Cell
  | 0, w => w
  | i + 1, w => rowsW p i
      (w.take i ++ (slideW (w.getD i (0, 0)) ((w.drop (i + 1)).take p) ++ w.drop (i + 1 + p)))

lemma getD_eq {w : List Cell} {i : ℕ} (hi : i < w.length) : w.getD i (0, 0) = w[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]

lemma decomp_fwd (w : List Cell) (i p : ℕ) (hl : i + p < w.length) :
    w = w.take i ++ (w.getD i (0, 0) :: (w.drop (i + 1)).take p ++ w.drop (i + 1 + p)) := by
  conv_lhs => rw [← List.take_append_drop i w]
  congr 1
  rw [List.drop_eq_getElem_cons (by omega), getD_eq (by omega), List.cons_append]
  congr 1
  conv_lhs => rw [← List.take_append_drop p (w.drop (i + 1)), List.drop_drop]


theorem rows_aux' (D₀ : Finset Cell) (hD₀ : IsDiag D₀) (p : ℕ) (i : ℕ) :
    ∀ (c : ℕ) (w : List Cell), w.length = i + p + c → StdFrom D₀ w →
    swSeq (rowsOrder p i)
        (List.replicate i D ++ List.replicate p R ++ List.replicate c D, lab D₀ w) =
      (List.replicate p R ++ List.replicate (i + c) D, lab D₀ (rowsW p i w)) := by
  induction i with
  | zero => intro c w _ _; simp [rowsOrder, rowsW]
  | succ i ih =>
    intro c w hl hstd
    have hdec := decomp_fwd w i p (by omega)
    set A := w.take i
    set h := w.getD i (0, 0)
    set F := (w.drop (i + 1)).take p
    set B := w.drop (i + 1 + p)
    have hAl : A.length = i := by simp [A]; omega
    have hFl : F.length = p := by simp [F]; omega
    have hBl : B.length = c := by simp [B]; omega
    rw [hdec] at hstd
    obtain ⟨h1, h2⟩ := stdFrom_append A _ D₀ hstd
    have hS := isDiag_union_of_stdFrom A D₀ hD₀ h1
    have h3 := (stdFrom_append (h :: F) B _ (by simpa using h2)).1
    have hI : ChainInv (D₀ ∪ A.toFinset) h F := ⟨hS, h3.1, h3.2.1, h3.2.2⟩
    have hwin := window_forward D₀ F (List.replicate i D) (List.replicate c D) A B h
      (by simp [hAl]) hI
    rw [hFl, hAl] at hwin
    have ew : List.replicate (i + 1) D ++ List.replicate p R ++ List.replicate c D =
        List.replicate i D ++ D :: (List.replicate p R ++ List.replicate c D) := by
      simp [List.replicate_succ']
    have ew2 : List.replicate i D ++ List.replicate p R ++ D :: List.replicate c D =
        List.replicate i D ++ List.replicate p R ++ List.replicate (c + 1) D := by
      simp [List.replicate_succ]
    have hsl : slideW h F = carryW h F := slideW_eq_carryW hS h3
    have hstd' : StdFrom D₀ (A ++ (carryW h F ++ B)) :=
      stdFrom_append_of A _ D₀ h1 (stdFrom_carryW B F _ h hS (by simpa using h2))
    have hl' : (A ++ (carryW h F ++ B)).length = i + p + (c + 1) := by
      simp [length_carryW, hAl, hFl, hBl]; omega
    rw [rowsOrder, swSeq_append, ew, hdec, hwin, ew2, ih (c + 1) _ hl' hstd',
      show i + (c + 1) = i + 1 + c by omega]
    congr 2
    rw [rowsW, ← hdec, ← hsl]

/-- **Σ = the rows switch product.** For every standard filling `w` (a cell word with
`StdFrom ∅ w`) of length `m + p`, the by-rows switch product on `(U^m F^p, chain of w)` gives
`F^p U^m` and the chain of `rowsW p m w`, the cell word obtained by the iterated forward jdt
slides of `Σ` (`U_m` through `F_1 … F_p`, then `U_{m−1}`, …). -/
theorem sigma_eq_rows_product (m p : ℕ) (w : List Cell) (hl : w.length = m + p)
    (hstd : StdFrom ∅ w) :
    swSeq (rowsOrder p m) (initWord p m, phi (chainOf ∅ w)) =
      (finalWord p m, phi (chainOf ∅ (rowsW p m w))) := by
  have := rows_aux' ∅ (by simp [IsDiag]) p m 0 w (by omega) hstd
  simpa [initWord, finalWord, phi_chainOf] using this

/-! ## The outward procedure: iterated reverse slides -/

/-- The outward procedure on cell words: slide `F_{c+1}` (cell `c+m`) backward through the `m`
cells before it, for `c = 0, 1, …, p−1`. -/
def colsW (m : ℕ) : ℕ → ℕ → List Cell → List Cell
  | _, 0, w => w
  | c, j + 1, w => colsW m (c + 1) j
      (w.take c ++ (revSlideW (w.getD (c + m) (0, 0)) ((w.drop c).take m) ++ w.drop (c + m + 1)))

lemma decomp_rev (w : List Cell) (c m : ℕ) (hl : c + m < w.length) :
    w = w.take c ++ ((w.drop c).take m ++ w.getD (c + m) (0, 0) :: w.drop (c + m + 1)) := by
  conv_lhs => rw [← List.take_append_drop c w]
  congr 1
  conv_lhs => rw [← List.take_append_drop m (w.drop c)]
  congr 1
  rw [List.drop_drop, List.drop_eq_getElem_cons (by omega), getD_eq (by omega)]

theorem cols_aux' (D₀ : Finset Cell) (hD₀ : IsDiag D₀) (m : ℕ) (j : ℕ) :
    ∀ (c : ℕ) (w : List Cell), w.length = c + m + j → StdFrom D₀ w →
    swSeq (colsFrom m c j)
        (List.replicate c R ++ List.replicate m D ++ List.replicate j R, lab D₀ w) =
      (List.replicate (c + j) R ++ List.replicate m D, lab D₀ (colsW m c j w)) := by
  induction j with
  | zero => intro c w _ _; simp [colsFrom, colsW]
  | succ j ih =>
    intro c w hl hstd
    have hdec := decomp_rev w c m (by omega)
    set A := w.take c
    set U := (w.drop c).take m
    set h := w.getD (c + m) (0, 0)
    set B := w.drop (c + m + 1)
    have hAl : A.length = c := by simp [A]; omega
    have hUl : U.length = m := by simp [U]; omega
    have hBl : B.length = j := by simp [B]; omega
    rw [hdec] at hstd
    obtain ⟨h1, h2⟩ := stdFrom_append A _ D₀ hstd
    have hS := isDiag_union_of_stdFrom A D₀ hD₀ h1
    obtain ⟨h3, h4⟩ := stdFrom_append (U ++ [h]) B _ (by simpa using h2)
    have hwin := window_reverse D₀ h U (List.replicate c R) (List.replicate j R) A B
      (by simp [hAl]) hS h3
    rw [hUl, hAl] at hwin
    have ew : List.replicate c R ++ List.replicate m D ++ List.replicate (j + 1) R =
        List.replicate c R ++ (List.replicate m D ++ R :: List.replicate j R) := by
      simp [List.replicate_succ]
    have ew2 : List.replicate c R ++ R :: (List.replicate m D ++ List.replicate j R) =
        List.replicate (c + 1) R ++ List.replicate m D ++ List.replicate j R := by
      simp [List.replicate_succ']
    obtain ⟨-, hstdZ⟩ := carryRev_chainOf h U _ hS h3
    obtain ⟨hfin, hlenW⟩ := carryWRev_toFinset h U
    have hsl : revSlideW h U = (carryWRev h U).1 :: (carryWRev h U).2 :=
      revSlideW_eq_carryWRev hS h3
    have hB' : StdFrom (D₀ ∪ A.toFinset ∪ ((carryWRev h U).1 :: (carryWRev h U).2).toFinset) B := by
      have e : ((carryWRev h U).1 :: (carryWRev h U).2).toFinset = (U ++ [h]).toFinset := by
        rw [List.toFinset_cons, hfin]; ext x; simp
      rwa [e]
    have hstd' : StdFrom D₀ (A ++ ((carryWRev h U).1 :: (carryWRev h U).2 ++ B)) :=
      stdFrom_append_of A _ D₀ h1 (stdFrom_append_of _ B _ hstdZ hB')
    have hl' : (A ++ ((carryWRev h U).1 :: (carryWRev h U).2 ++ B)).length = c + 1 + m + j := by
      simp [hlenW, hAl, hUl, hBl]; omega
    rw [colsFrom, swSeq_append, ew, hdec, hwin, ew2, ih (c + 1) _ hl' hstd',
      show c + 1 + j = c + (j + 1) by omega]
    congr 2
    rw [colsW, ← hdec, ← hsl]

/-- **The outward procedure = the columns switch product.** For every standard filling `w`
of length `m + p`, the by-columns switch product on `(U^m F^p, chain of w)` gives `F^p U^m`
and the chain of `colsW m 0 p w`, the cell word obtained by the iterated reverse jdt slides
(`F_1` backward through `U_m … U_1`, then `F_2`, …). -/
theorem outward_eq_columns_product (m p : ℕ) (w : List Cell) (hl : w.length = m + p)
    (hstd : StdFrom ∅ w) :
    swSeq (colsOrder m p) (initWord p m, phi (chainOf ∅ w)) =
      (finalWord p m, phi (chainOf ∅ (colsW m 0 p w))) := by
  have := cols_aux' ∅ (by simp [IsDiag]) m p 0 w (by omega) hstd
  simpa [initWord, finalWord, colsOrder, phi_chainOf] using this

/-! ## Lemma D in slide form -/

/-- **G4 Lemma D (`lem:D`, l.172–198), slide form.** For every standard filling `w` of length
`m + p` (letters `U_1 … U_m` in cells `w₀ … w_{m−1}`, letters `F_1 … F_p` after them), the
iterated forward slides of `Σ` (`rowsW`) and the iterated reverse slides of the outward
procedure (`colsW`) produce the same chain, hence the same cells for every letter, in
particular the same `U`-part. Proof: `sigma_eq_rows_product`, `outward_eq_columns_product`
and `lemmaD_rows_eq_columns` (Benkart–Sottile–Stroomer growth-diagram confluence, abstract form
`GrowthConfluence.confluence_final`). -/
theorem lemmaD_slides (m p : ℕ) (w : List Cell) (hl : w.length = m + p) (hstd : StdFrom ∅ w) :
    phi (chainOf ∅ (rowsW p m w)) = phi (chainOf ∅ (colsW m 0 p w)) := by
  have h := lemmaD_rows_eq_columns m p (phi (chainOf ∅ w))
  rw [sigma_eq_rows_product m p w hl hstd, outward_eq_columns_product m p w hl hstd] at h
  exact (Prod.mk.inj h).2

/-! ## Labels outside the window do not move -/

lemma carryW_toFinset (h : Cell) (F : List Cell) : (carryW h F).toFinset = (h :: F).toFinset := by
  induction F generalizing h with
  | nil => rfl
  | cons y F ih =>
    simp only [carryW]
    split_ifs
    · rw [List.toFinset_cons, ih]; simp
    · rw [List.toFinset_cons, ih]; ext c; simp; tauto

lemma lab_outside (D₀ : Finset Cell) (A X Y B : List Cell) (hl : X.length = Y.length)
    (hs : X.toFinset = Y.toFinset) (t : ℕ) (ht : t ≤ A.length ∨ A.length + X.length ≤ t) :
    lab D₀ (A ++ (X ++ B)) t = lab D₀ (A ++ (Y ++ B)) t := by
  unfold lab
  simp only [List.length_append, hl]
  split_ifs
  · congr 1
    rcases ht with ht | ht
    · rw [List.take_append_of_le_length ht, List.take_append_of_le_length ht]
    · obtain ⟨k, rfl⟩ : ∃ k, t = A.length + (X.length + k) := ⟨t - A.length - X.length, by omega⟩
      rw [List.take_length_add_append, List.take_length_add_append, List.take_length_add_append,
        hl, List.take_length_add_append]
      simp only [List.toFinset_append, hs]
  · rfl

/-- **Window lemma, outside part.** The switches of the window `|A|, …, |A|+p−1` leave
`η_t` unchanged for every `t ≤ |A|` and every `t ≥ |A| + p + 1`. -/
theorem window_forward_outside (D₀ : Finset Cell) (F : List Cell) (a b : List Dir)
    (A B : List Cell) (h : Cell) (hlen : a.length = A.length)
    (hI : ChainInv (D₀ ∪ A.toFinset) h F) (t : ℕ)
    (ht : t ≤ A.length ∨ A.length + F.length + 1 ≤ t) :
    (swSeq ((List.range F.length).map (A.length + ·))
        (a ++ D :: (List.replicate F.length R ++ b), lab D₀ (A ++ (h :: F ++ B)))).2 t =
      lab D₀ (A ++ (h :: F ++ B)) t := by
  rw [window_forward D₀ F a b A B h hlen hI]
  exact lab_outside D₀ A (carryW h F) (h :: F) B (by simp [length_carryW])
    (carryW_toFinset h F) t (by rw [length_carryW]; omega)

/-! ## Control and lesion -/

/-- The example window: `A = [(0,0)]`, hole `h = (1,0)`, `F = [(0,1)]` (not adjacent to `h`,
so the switch genuinely changes `η_2`). -/
def exCells : List Cell := [(0, 0), (1, 0), (0, 1)]

/-- **Control.** The window `[1]` on `D D R` gives `D R D` and the chain of
`A ++ carryW h F = [(0,0),(0,1),(1,0)]`, which differs from the starting chain. -/
theorem control_window :
    snapL 3 (swSeq [1] ([D, D, R], phi (chainOf ∅ exCells))) =
      snapL 3 ([D, R, D], phi (chainOf ∅ [(0, 0), (0, 1), (1, 0)])) ∧
    snapL 3 ([D, R, D], phi (chainOf ∅ [(0, 0), (0, 1), (1, 0)])) ≠
      snapL 3 ([D, R, D], phi (chainOf ∅ exCells)) := by
  decide +kernel

/-- **Lesion (window shifted by one).** The window shifted right (`[2]`) or left (`[0]`) does
not produce the window lemma's output on the example. -/
theorem lesion_window_shift :
    snapL 3 (swSeq [2] ([D, D, R], phi (chainOf ∅ exCells))) ≠
      snapL 3 ([D, R, D], phi (chainOf ∅ [(0, 0), (0, 1), (1, 0)])) ∧
    snapL 3 (swSeq [0] ([D, D, R], phi (chainOf ∅ exCells))) ≠
      snapL 3 ([D, R, D], phi (chainOf ∅ [(0, 0), (0, 1), (1, 0)])) := by
  decide +kernel

/-- The general window lemma specialised to the example agrees with the kernel computation. -/
example : swSeq [1] ([D, D, R], lab ∅ exCells) = ([D, R, D], lab ∅ [(0, 0), (0, 1), (1, 0)]) := by
  have := window_forward ∅ [(0, 1)] [D] [] [(0, 0)] [] (1, 0) rfl
    (by refine ⟨?_, ?_, ?_, ?_⟩ <;> decide)
  simpa [carryW, Adj, exCells] using this

end TworowD4Kernel.SlideIteration
