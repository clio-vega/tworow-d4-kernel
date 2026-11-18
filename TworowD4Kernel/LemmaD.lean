/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SlideSwitchGeneral

/-!
# G4 Lemma D: switching by rows = switching by columns

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D`, l.187–198:
"`Σ` applies the switches at the grid squares `(i,j)` of `[m] × [p]` in the order
`(m,1),…,(m,p),(m−1,1),…` (by rows), and the outward procedure applies them in the order
`(m,1),(m−1,1),…,(1,1),(m,2),…` (by columns) … So they produce the same final chain."
The growth-diagram argument is Benkart–Sottile–Stroomer 1996 (recalled, not consulted, as in
the paper); its abstract form is `GrowthConfluence.confluence_final`.

## Encoding (the documented choice)

A configuration is a word in the letters `U_1 … U_m F_1 … F_p` and a saturated chain
`η_0 ⊂ ⋯ ⊂ η_{m+p}`. We encode it as a `GrowthConfluence` state `(w, f)`:

* letter `U ↦ Dir.D`, letter `F ↦ Dir.R`;
* the chain is the label function, `f t = η_t`.

**Why this orientation.** `GrowthConfluence.Flip` rewrites `D R ↦ R D` and is the only
monotone move. Both orders of the lemma move `U`-letters rightward past `F`-letters
(`U F ↦ F U`), so `U ↦ D` is forced. With `U ↦ R` every switch would be an `Unflip`.
Consequently the paper's grid `[m] × [p]` (`m` letters `U`, `p` letters `F`) is the
`GrowthConfluence` grid with its two parameters **swapped**: initial word
`U^m F^p = initWord p m = D^m R^p`, final word `F^p U^m = finalWord p m = R^p D^m`.

The elementary switch `s_{t+1}` (paper indexing: it swaps the letters at positions `t+1, t+2`,
i.e. 0-indexed word positions `t, t+1`, and rewrites `η_{t+1}`) is `sw t`. It is applied only
to a `U F` pair. At any other position it is the identity, so an illegal order is visible as a
wrong final word.

## Main results

* `switch_is_flip` : one switch is one `Flip switchL` step.
* `rows_reach`, `cols_reach` : the by-rows and by-columns products are `ReflTransGen (Flip switchL)`
  sequences from `(U^m F^p, g)` to `(F^p U^m, ·)`, for **all** `m, p` and every chain `g`.
* `lemmaD_rows_eq_columns` : the two products agree (word and chain), from `confluence_final`.

## Not covered (recorded in the 2026-11-18 note)

The theorem is the switch form of `lem:D`. Identifying the iterated slides of `Σ` (rows: `U_i`
carried past `F_1 … F_p`, a forward slide by `slide_eq_switch_product`) and of the outward
procedure (columns: `F_j` carried past `U_m … U_1`, a reverse slide by
`reverse_slide_eq_switch_product`) with these products needs two mechanical lemmas that are not
here: the window lemma (switches at positions `i … i+p−1` act as `carry p` on `η_i ⊂ ⋯`)
and the
propagation of the slide hypotheses (`IsDiag`, `StdFrom`) from one row/column to the next.
-/

namespace TworowD4Kernel.LemmaD

open GrowthConfluence SlideSwitch Dir

/-- A configuration: word (`U ↦ D`, `F ↦ R`) and chain `t ↦ η_t`. -/
abbrev St := List Dir × (ℕ → Finset Cell)

/-- The elementary switch at 0-indexed word position `t` (the paper's `s_{t+1}`), on a `U F` pair:
swap the letters and replace `η_{t+1}` by `switchL η_t η_{t+1} η_{t+2}`. Identity elsewhere. -/
def sw (t : ℕ) (s : St) : St :=
  if (s.1.drop t).take 2 = [D, R] then
    (s.1.take t ++ R :: D :: s.1.drop (t + 2),
      Function.update s.2 (t + 1) (switchL (s.2 t) (s.2 (t + 1)) (s.2 (t + 2))))
  else s

/-- Apply the switches of a list of positions, first to last. -/
def swSeq (l : List ℕ) (s : St) : St := l.foldl (fun s t => sw t s) s

@[simp] lemma swSeq_nil (s : St) : swSeq [] s = s := rfl
@[simp] lemma swSeq_cons (t : ℕ) (l : List ℕ) (s : St) :
    swSeq (t :: l) s = swSeq l (sw t s) := rfl
lemma swSeq_append (l₁ l₂ : List ℕ) (s : St) :
    swSeq (l₁ ++ l₂) s = swSeq l₂ (swSeq l₁ s) := by
  simp [swSeq, List.foldl_append]

/-- The switch on a decomposed word. -/
lemma sw_eq (a b : List Dir) (f : ℕ → Finset Cell) :
    sw a.length (a ++ D :: R :: b, f) =
      (a ++ R :: D :: b,
        Function.update f (a.length + 1)
          (switchL (f a.length) (f (a.length + 1)) (f (a.length + 2)))) := by
  have h2 : (a ++ D :: R :: b).drop (a.length + 2) = b := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      show a.length + 2 - a.length = 2 by omega]
    rfl
  simp [sw, h2]

/-- **Tier A: one switch is one flip.** On a `U F` pair the elementary switch is a `Flip switchL`
step of the growth diagram. -/
theorem switch_is_flip (a b : List Dir) (f : ℕ → Finset Cell) :
    Flip switchL (a ++ D :: R :: b, f) (sw a.length (a ++ D :: R :: b, f)) := by
  rw [sw_eq]; exact Flip.mk a b f

/-- The same, with the position given as a number. -/
theorem switch_is_flip' (w : List Dir) (f : ℕ → Finset Cell) (t : ℕ)
    (h : (w.drop t).take 2 = [D, R]) : Flip switchL (w, f) (sw t (w, f)) := by
  have hw : w = w.take t ++ D :: R :: w.drop (t + 2) := by
    conv_lhs => rw [← List.take_append_drop t w]
    congr 1
    rw [← List.take_append_drop 2 (w.drop t), h, List.drop_drop, Nat.add_comm]
    rfl
  have hlen : (w.take t).length = t := by
    have := congrArg List.length h
    simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at this
    simp only [List.length_take]
    omega
  have := switch_is_flip (w.take t) (w.drop (t + 2)) f
  rw [← hw, hlen] at this
  exact this

/-- A switch whose letters are not a `U F` pair does nothing. -/
lemma sw_illegal (w : List Dir) (f : ℕ → Finset Cell) (t : ℕ)
    (h : (w.drop t).take 2 ≠ [D, R]) : sw t (w, f) = (w, f) := by
  simp [sw, h]

/-! ## Carrying one letter -/

/-- Carry the `U` at position `a.length` rightward past `k` letters `F` (positions
`a.length, …, a.length + k − 1`). -/
theorem carry_right (b : List Dir) (k : ℕ) : ∀ (a : List Dir) (f : ℕ → Finset Cell),
    ∃ f', swSeq ((List.range k).map (a.length + ·)) (a ++ D :: (List.replicate k R ++ b), f) =
        (a ++ List.replicate k R ++ D :: b, f') ∧
      Relation.ReflTransGen (Flip switchL) (a ++ D :: (List.replicate k R ++ b), f)
        (a ++ List.replicate k R ++ D :: b, f') := by
  induction k with
  | zero => intro a f; exact ⟨f, by simp, by simpa using Relation.ReflTransGen.refl⟩
  | succ k ih =>
    intro a f
    have hw : a ++ D :: (List.replicate (k + 1) R ++ b) =
        a ++ D :: R :: (List.replicate k R ++ b) := by simp [List.replicate_succ]
    have hstep := switch_is_flip a (List.replicate k R ++ b) f
    rw [sw_eq] at hstep
    obtain ⟨f', h1, h2⟩ := ih (a ++ [R]) (Function.update f (a.length + 1)
      (switchL (f a.length) (f (a.length + 1)) (f (a.length + 2))))
    have hw' : (a ++ [R]) ++ D :: (List.replicate k R ++ b) =
        a ++ R :: D :: (List.replicate k R ++ b) := by
      simp
    have he : (a ++ [R]) ++ List.replicate k R ++ D :: b =
        a ++ List.replicate (k + 1) R ++ D :: b := by
      simp [List.replicate_succ]
    refine ⟨f', ?_, ?_⟩
    · rw [hw, List.range_succ_eq_map, List.map_cons, swSeq_cons, Nat.add_zero, sw_eq,
        List.map_map, ← hw', ← he]
      convert h1 using 3
      funext i; simp [Function.comp]; omega
    · rw [hw, ← he]
      rw [hw'] at h2
      exact Relation.ReflTransGen.head hstep h2

/-- Carry the `F` at position `a.length + k` leftward past `k` letters `U` (positions
`a.length + k − 1, …, a.length`). -/
theorem carry_left (a : List Dir) (k : ℕ) : ∀ (b : List Dir) (f : ℕ → Finset Cell),
    ∃ f', swSeq ((List.range k).reverse.map (a.length + ·))
        (a ++ List.replicate k D ++ R :: b, f) =
        (a ++ R :: (List.replicate k D ++ b), f') ∧
      Relation.ReflTransGen (Flip switchL) (a ++ List.replicate k D ++ R :: b, f)
        (a ++ R :: (List.replicate k D ++ b), f') := by
  induction k with
  | zero => intro b f; exact ⟨f, by simp, by simpa using Relation.ReflTransGen.refl⟩
  | succ k ih =>
    intro b f
    have hw : a ++ List.replicate (k + 1) D ++ R :: b =
        (a ++ List.replicate k D) ++ D :: R :: b := by
      simp [List.replicate_succ']
    have hl : (a ++ List.replicate k D).length = a.length + k := by simp
    have hstep := switch_is_flip (a ++ List.replicate k D) b f
    rw [sw_eq] at hstep
    obtain ⟨f', h1, h2⟩ := ih (D :: b) (Function.update f ((a ++ List.replicate k D).length + 1)
      (switchL (f (a ++ List.replicate k D).length) (f ((a ++ List.replicate k D).length + 1))
        (f ((a ++ List.replicate k D).length + 2))))
    have hw' : (a ++ List.replicate k D) ++ R :: D :: b =
        a ++ List.replicate k D ++ R :: (D :: b) := by
      simp
    have he : a ++ R :: (List.replicate k D ++ D :: b) =
        a ++ R :: (List.replicate (k + 1) D ++ b) := by
      simp [List.replicate_succ']
    refine ⟨f', ?_, ?_⟩
    · rw [hw, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append,
        List.map_cons, swSeq_cons, ← hl, sw_eq, hw', ← he]
      exact h1
    · rw [hw, ← he]
      rw [hw'] at hstep
      exact Relation.ReflTransGen.head hstep h2

/-! ## The two orders -/

/-- By rows: `U_m` past `F_1 … F_p`, then `U_{m−1}` past `F_1 … F_p`, … (the paper's
`(m,1),…,(m,p),(m−1,1),…`). `U_{i+1}` sits at position `i`. -/
def rowsOrder (p : ℕ) : ℕ → List ℕ
  | 0 => []
  | i + 1 => (List.range p).map (i + ·) ++ rowsOrder p i

/-- By columns, starting at column offset `c`: `F_{c+1}` past `U_m … U_1`, then `F_{c+2}`, ….
`F_{c+1}` sits at position `c + m`. -/
def colsFrom (m : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | c, j + 1 => (List.range m).reverse.map (c + ·) ++ colsFrom m (c + 1) j

/-- The paper's by-columns order `(m,1),(m−1,1),…,(1,1),(m,2),…`. -/
def colsOrder (m p : ℕ) : List ℕ := colsFrom m 0 p

/-- On the `2 × 2` grid these are `GrowthConfluence.ordB` (rows) and `ordA` (columns). -/
example : rowsOrder 2 2 = [1, 2, 0, 1] ∧ colsOrder 2 2 = [1, 0, 2, 1] := by decide

theorem rows_aux (p : ℕ) (m : ℕ) : ∀ (c : ℕ) (f : ℕ → Finset Cell),
    ∃ f', swSeq (rowsOrder p m)
        (List.replicate m D ++ List.replicate p R ++ List.replicate c D, f) =
        (List.replicate p R ++ List.replicate (m + c) D, f') ∧
      Relation.ReflTransGen (Flip switchL)
        (List.replicate m D ++ List.replicate p R ++ List.replicate c D, f)
        (List.replicate p R ++ List.replicate (m + c) D, f') := by
  induction m with
  | zero => intro c f; exact ⟨f, by simp [rowsOrder], by simpa using Relation.ReflTransGen.refl⟩
  | succ m ih =>
    intro c f
    have hw : List.replicate (m + 1) D ++ List.replicate p R ++ List.replicate c D =
        List.replicate m D ++ D :: (List.replicate p R ++ List.replicate c D) := by
      simp [List.replicate_succ']
    obtain ⟨f₁, h1, r1⟩ := carry_right (List.replicate c D) p (List.replicate m D) f
    have he : List.replicate m D ++ List.replicate p R ++ D :: List.replicate c D =
        List.replicate m D ++ List.replicate p R ++ List.replicate (c + 1) D := by
      simp [List.replicate_succ]
    obtain ⟨f₂, h2, r2⟩ := ih (c + 1) f₁
    have he2 : m + (c + 1) = m + 1 + c := by omega
    refine ⟨f₂, ?_, ?_⟩
    · rw [rowsOrder, swSeq_append, hw]
      simp only [List.length_replicate] at h1
      rw [h1, he, h2, he2]
    · rw [hw]
      rw [he] at r1
      rw [← he2]
      exact r1.trans r2

theorem cols_aux (m : ℕ) (j : ℕ) : ∀ (c : ℕ) (f : ℕ → Finset Cell),
    ∃ f', swSeq (colsFrom m c j)
        (List.replicate c R ++ List.replicate m D ++ List.replicate j R, f) =
        (List.replicate (c + j) R ++ List.replicate m D, f') ∧
      Relation.ReflTransGen (Flip switchL)
        (List.replicate c R ++ List.replicate m D ++ List.replicate j R, f)
        (List.replicate (c + j) R ++ List.replicate m D, f') := by
  induction j with
  | zero => intro c f; exact ⟨f, by simp [colsFrom], by simpa using Relation.ReflTransGen.refl⟩
  | succ j ih =>
    intro c f
    have hw : List.replicate c R ++ List.replicate m D ++ List.replicate (j + 1) R =
        List.replicate c R ++ List.replicate m D ++ R :: List.replicate j R := by
      simp [List.replicate_succ]
    obtain ⟨f₁, h1, r1⟩ := carry_left (List.replicate c R) m (List.replicate j R) f
    have he : List.replicate c R ++ R :: (List.replicate m D ++ List.replicate j R) =
        List.replicate (c + 1) R ++ List.replicate m D ++ List.replicate j R := by
      simp [List.replicate_succ']
    obtain ⟨f₂, h2, r2⟩ := ih (c + 1) f₁
    have he2 : c + 1 + j = c + (j + 1) := by omega
    refine ⟨f₂, ?_, ?_⟩
    · rw [colsFrom, swSeq_append, hw]
      simp only [List.length_replicate] at h1
      rw [h1, he, h2, he2]
    · rw [hw]
      rw [he] at r1
      rw [← he2]
      exact r1.trans r2

/-- **Tier B (rows).** The by-rows product is a monotone flip sequence from `U^m F^p` to
`F^p U^m`, for every chain. -/
theorem rows_reach (m p : ℕ) (g : ℕ → Finset Cell) :
    (swSeq (rowsOrder p m) (initWord p m, g)).1 = finalWord p m ∧
      Relation.ReflTransGen (Flip switchL) (initWord p m, g)
        (swSeq (rowsOrder p m) (initWord p m, g)) := by
  obtain ⟨f', h1, r1⟩ := rows_aux p m 0 g
  simp only [List.replicate_zero, List.append_nil, Nat.add_zero] at h1 r1
  rw [initWord, h1]
  exact ⟨rfl, r1⟩

/-- **Tier B (columns).** The by-columns product is a monotone flip sequence from `U^m F^p` to
`F^p U^m`, for every chain. -/
theorem cols_reach (m p : ℕ) (g : ℕ → Finset Cell) :
    (swSeq (colsOrder m p) (initWord p m, g)).1 = finalWord p m ∧
      Relation.ReflTransGen (Flip switchL) (initWord p m, g)
        (swSeq (colsOrder m p) (initWord p m, g)) := by
  obtain ⟨f', h1, r1⟩ := cols_aux m p 0 g
  simp only [List.replicate_zero, List.nil_append, Nat.zero_add] at h1 r1
  rw [initWord, colsOrder, h1]
  exact ⟨rfl, r1⟩

/-- **G4 Lemma D (`lem:D`, l.187–198), switch form.** Applying the elementary switches by rows
and by columns to the configuration `(U_1 ⋯ U_m F_1 ⋯ F_p, η)` gives the same word `F^p U^m`
and the same chain; in particular the same `U`-part. Holds for every chain `η` (saturation and
the switch rule play no role here; they enter through `slide_eq_switch_product` and
`reverse_slide_eq_switch_product`, which identify the rows/columns with slides). -/
theorem lemmaD_rows_eq_columns (m p : ℕ) (g : ℕ → Finset Cell) :
    swSeq (rowsOrder p m) (initWord p m, g) = swSeq (colsOrder m p) (initWord p m, g) := by
  obtain ⟨w1, r1⟩ := rows_reach m p g
  obtain ⟨w2, r2⟩ := cols_reach m p g
  generalize swSeq (rowsOrder p m) (initWord p m, g) = s1 at w1 r1 ⊢
  generalize swSeq (colsOrder m p) (initWord p m, g) = s2 at w2 r2 ⊢
  obtain ⟨x1, f1⟩ := s1
  obtain ⟨x2, f2⟩ := s2
  simp only at w1 w2
  subst w1 w2
  rw [confluence_final switchL p m g r1 r2]

/-! ## Finite corollary, nontriviality, lesions -/

/-- A list chain as a label function (positions past the end get `∅`). -/
def phi (ch : List (Finset Cell)) : ℕ → Finset Cell := fun k => ch.getD k ∅

/-- Observe a configuration: the word and `η_0, …, η_n`. -/
def snapL (n : ℕ) (s : St) : List Dir × List (Finset Cell) := (s.1, (List.range (n + 1)).map s.2)

/-- Instances `(m, p, w)`: every standard tableau `w` (as a cell word) of every diagram `ν` with
`|ν| ≤ N`, split as `m` letters `U` then `p = |ν| − m` letters `F`. -/
def ldInst (N : ℕ) : List (ℕ × ℕ × List Cell) :=
  (List.range (N + 1)).flatMap fun n => (diags N n).flatMap fun ν =>
    (stdFill N ν n ∅).flatMap fun w => (List.range (n + 1)).map fun m => (m, n - m, w)

/-- The finite check: rows product = columns product on every instance. -/
def lemmaDCheck (N : ℕ) : Bool :=
  (ldInst N).all fun ⟨m, p, w⟩ =>
    decide (snapL (m + p) (swSeq (rowsOrder p m) (initWord p m, phi (chainOf ∅ w))) =
      snapL (m + p) (swSeq (colsOrder m p) (initWord p m, phi (chainOf ∅ w))))

/-- The finite check holds at **every** `N`, as a corollary of `lemmaD_rows_eq_columns`
(nothing is decided by the kernel). -/
theorem lemmaDCheck_true (N : ℕ) : lemmaDCheck N = true := by
  unfold lemmaDCheck
  rw [List.all_eq_true]
  rintro ⟨m, p, w⟩ -
  simp only [lemmaD_rows_eq_columns, decide_true]

/-- The `|ν| ≤ 5` instance of the corollary (231 instances). -/
theorem lemmaDCheck_le5 : lemmaDCheck 5 = true := lemmaDCheck_true 5

/-- Number of instances on which the rows product changes the chain (the check is not vacuous). -/
def nontrivCount (N : ℕ) : ℕ :=
  ((ldInst N).filter fun ⟨m, p, w⟩ =>
    snapL (m + p) (swSeq (rowsOrder p m) (initWord p m, phi (chainOf ∅ w))) ≠
      snapL (m + p) (finalWord p m, phi (chainOf ∅ w))).length

/-- The example chain: standard tableau of `(3,1)` with `1,2` in the first column (`U`-part)
and `3,4` in the first row (`F`-part). -/
def exW : List Cell := [(0, 0), (1, 0), (0, 1), (0, 2)]

/-- **Control.** On `exW` both orders give word `F F U U` and move the second cell of the chain
from `(1,0)` to `(0,1)`: the switches are not all trivial. -/
theorem control_exW :
    snapL 4 (swSeq (rowsOrder 2 2) (initWord 2 2, phi (chainOf ∅ exW))) =
      snapL 4 (swSeq (colsOrder 2 2) (initWord 2 2, phi (chainOf ∅ exW))) ∧
    snapL 4 (swSeq (rowsOrder 2 2) (initWord 2 2, phi (chainOf ∅ exW))) ≠
      snapL 4 (initWord 2 2, phi (chainOf ∅ exW)) := by
  decide +kernel

/-- **Lesion (order).** Perturbing the last position of the rows order (`[1,2,0,0]`) gives a
sequence that is not a monotone flip sequence to `F^p U^m`: its last switch is illegal (a no-op),
and the result differs from the columns product. (With `switchL` the *chain* cannot be what
breaks: `switchL` is involutive (`switchL_invol`), so by `good_unflip` any switch sequence that
reaches `F^p U^m` gives the same chain; only the word can witness the lesion.) -/
theorem lesion_order :
    (swSeq [1, 2, 0, 0] (initWord 2 2, phi (chainOf ∅ exW))).1 ≠ finalWord 2 2 ∧
    snapL 4 (swSeq [1, 2, 0, 0] (initWord 2 2, phi (chainOf ∅ exW))) ≠
      snapL 4 (swSeq (colsOrder 2 2) (initWord 2 2, phi (chainOf ∅ exW))) := by
  decide +kernel

/-- **Lesion (encoding).** With the other orientation `U ↦ R`, `U^2 F^2 = R R D D` and every
switch of the rows order is illegal: the product never leaves the initial word. This is why
`U ↦ D`. -/
theorem lesion_encoding :
    (swSeq (rowsOrder 2 2) ([R, R, D, D], phi (chainOf ∅ exW))).1 = [R, R, D, D] := by
  decide +kernel

end TworowD4Kernel.LemmaD
