/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Count

/-!
# Growth-diagram confluence (the abstract half of G4's Lemma D)

This file formalises half (ii) of the proof of Lemma `lem:D` ("inward = outward switching") in
`projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex` (Clio, 2026-11-13), the paragraph that
begins "Index a word by the lattice path …". It is the standard growth-diagram argument that
tableau switching does not depend on the order of the elementary switches
(Benkart–Sottile–Stroomer 1996; recalled, not consulted, as in the paper). Half (i), that a jdt
slide *is* a product of elementary switches, is tableau-specific and is **not** formalised here.

## Convention

The grid is `[0,m] × [0,p]`, vertices `(i,j)`. A labelled path runs from `(0,p)` to `(m,0)` and is
encoded as a **word** `w : List Dir` (`R` : `i ↦ i+1`, `D` : `j ↦ j−1`) together with a
**label function** `f : ℕ → V`, where `f t` is the value at the `t`-th vertex of the path
(`vtx p w t`). Positions `t > w.length` are not vertices; their labels are carried
along unchanged. This is literally the paper's (word, chain) pair: position `t` ↔ `η_t`.

* initial path `D^p R^m`: down the left side, then along the bottom;
* final path `R^m D^p`: along the top, then down the right side;
* a **flip** at position `t` rewrites the letters `D R` at `t, t+1` to `R D`. The path stops
  passing through the lower-left corner `(i−1,j−1)` of a unit square and passes through its
  upper-right corner `(i,j)` instead. The new value at position `t+1` is
  `L (f t) (f (t+1)) (f (t+2))`, the local rule applied to the other three corners `(i−1,j)`,
  `(i−1,j−1)`, `(i,j−1)`.

`eta L p g` is the recursion-defined labelling of the whole grid. The boundary values are read
off the initial labelling `g`, and the interior is `η(i,j) = L η(i−1,j) η(i−1,j−1) η(i,j−1)`.

## Main results

* `GrowthConfluence.reachable_label_eq_eta`: along **any** flip sequence from `(D^p R^m, g)`,
  every vertex of the current path carries `eta` of that vertex, and non-vertex positions still
  carry `g`. The invariant is about the current path only. "Each vertex is created exactly once"
  is never needed.
* `GrowthConfluence.confluence`: two flip sequences that reach the same word give the same label
  function. In particular they agree on the final path `R^m D^p`.

## Lesions (each refuted by `decide` on a small instance)

1. `lesion_step_indexed`: a rule `L s a b c` that also reads the step number `s` gives
   different final labellings for the two orders on the `2 × 2` grid (rows-first vs columns-first).
2. `lesion_unflip`: allowing a backward move (`R D ↦ D R`, rule applied to the three other
   corners) with the non-involutive rule `L a b c = b + 1` breaks confluence on the `1 × 1` grid.
   `unflip_harmless_of_involutive` shows that it *is* harmless when `L a (L a b c) c = b`.
3. `lesion_initial`: different initial labellings give different final labellings (control).
-/

namespace TworowD4Kernel.GrowthConfluence

/-- A step of a lattice path from `(0,p)` to `(m,0)`: `R` = east, `D` = south. -/
inductive Dir
  | R
  | D
  deriving DecidableEq, Repr

open Dir

variable {V : Type*}

/-- The `t`-th vertex of the path `w` starting at `(0,p)`. -/
def vtx (p : ℕ) (w : List Dir) (t : ℕ) : ℕ × ℕ :=
  ((w.take t).count R, p - (w.take t).count D)

/-- The recursion-defined labelling of the grid from the initial labelling `g` of the path
`D^p R^m`: `η(0,j) = g(p−j)`, `η(i,0) = g(p+i)`, and `η(i,j) = L η(i−1,j) η(i−1,j−1) η(i,j−1)`. -/
def eta (L : V → V → V → V) (p : ℕ) (g : ℕ → V) : ℕ → ℕ → V
  | 0, j => g (p - j)
  | i + 1, 0 => g (p + (i + 1))
  | i + 1, j + 1 => L (eta L p g i (j + 1)) (eta L p g i j) (eta L p g (i + 1) j)
termination_by i j => i + j

/-- The initial path `D^p R^m` (left side, then bottom). -/
def initWord (m p : ℕ) : List Dir := List.replicate p D ++ List.replicate m R

/-- The final path `R^m D^p` (top, then right side). -/
def finalWord (m p : ℕ) : List Dir := List.replicate m R ++ List.replicate p D

/-- One monotone flip at position `a.length`: `D R ↦ R D`, the vertex at `a.length + 1` gets
`L` of the three other corners of the unit square. -/
inductive Flip (L : V → V → V → V) : List Dir × (ℕ → V) → List Dir × (ℕ → V) → Prop
  | mk (a b : List Dir) (f : ℕ → V) :
      Flip L (a ++ D :: R :: b, f)
        (a ++ R :: D :: b,
          Function.update f (a.length + 1) (L (f a.length) (f (a.length + 1)) (f (a.length + 2))))

/-- The invariant: `w` has `p` south steps, every vertex carries `eta`, non-vertices carry `g`. -/
def Good (L : V → V → V → V) (p : ℕ) (g : ℕ → V) (s : List Dir × (ℕ → V)) : Prop :=
  s.1.count D = p ∧ (∀ t ≤ s.1.length, s.2 t = eta L p g (vtx p s.1 t).1 (vtx p s.1 t).2) ∧
    ∀ t, s.1.length < t → s.2 t = g t

/-! ## Bookkeeping on prefixes -/

/-- Away from the flipped vertex, the prefix counts of the two words agree. -/
lemma count_take_swap (a b : List Dir) (x y c : Dir) (t : ℕ) (ht : t ≠ a.length + 1) :
    ((a ++ x :: y :: b).take t).count c = ((a ++ y :: x :: b).take t).count c := by
  rcases Nat.lt_or_ge a.length t with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, t = a.length + 2 + k := ⟨t - a.length - 2, by omega⟩
    rw [show a.length + 2 + k = a.length + (k + 2) by omega, List.take_length_add_append,
      List.take_length_add_append]
    simp only [List.take_succ_cons, List.count_append, List.count_cons]
    omega
  · rw [List.take_append_of_le_length h, List.take_append_of_le_length h]

lemma vtx_swap (p : ℕ) (a b : List Dir) (x y : Dir) (t : ℕ) (ht : t ≠ a.length + 1) :
    vtx p (a ++ x :: y :: b) t = vtx p (a ++ y :: x :: b) t := by
  simp only [vtx, count_take_swap a b x y _ t ht]

lemma take_len_succ (a b : List Dir) (x : Dir) :
    (a ++ x :: b).take (a.length + 1) = a ++ [x] := by
  rw [List.take_length_add_append]; simp

lemma take_len_two (a b : List Dir) (x y : Dir) :
    (a ++ x :: y :: b).take (a.length + 2) = a ++ [x, y] := by
  rw [List.take_length_add_append]; simp

/-! ## The invariant -/

theorem good_init (L : V → V → V → V) (m p : ℕ) (g : ℕ → V) :
    Good L p g (initWord m p, g) := by
  refine ⟨by simp [initWord, List.count_replicate], ?_, fun _ _ => rfl⟩
  intro t ht
  simp only [initWord, List.length_append, List.length_replicate] at ht
  rcases Nat.lt_or_ge p t with h | h
  swap
  · have : (initWord m p).take t = List.replicate t D := by
      rw [initWord, List.take_append_of_le_length (by simpa using h), List.take_replicate,
        Nat.min_eq_left h]
    simp only [vtx, this, List.count_replicate]
    simp [eta, Nat.sub_sub_self h]
  · obtain ⟨i, rfl⟩ : ∃ i, t = p + (i + 1) := ⟨t - p - 1, by omega⟩
    have : (initWord m p).take (p + (i + 1)) = List.replicate p D ++ List.replicate (i + 1) R := by
      rw [initWord, List.take_append]
      simp [List.take_replicate]
      omega
    simp only [vtx, this, List.count_append, List.count_replicate]
    simp [eta]

theorem good_flip (L : V → V → V → V) (p : ℕ) (g : ℕ → V) {s s' : List Dir × (ℕ → V)}
    (hs : Good L p g s) (h : Flip L s s') : Good L p g s' := by
  obtain ⟨a, b, f⟩ := h
  obtain ⟨hc, hv, hg⟩ := hs
  simp only at hc hv hg
  have hlen : (a ++ R :: D :: b).length = (a ++ D :: R :: b).length := by simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.count_append, List.count_cons] at hc ⊢; omega
  · intro t ht
    simp only
    by_cases htn : t = a.length + 1
    · subst htn
      rw [Function.update_self]
      -- the three corners
      have hd : (a.count D) + 1 ≤ p := by
        rw [← hc]; simp [List.count_append]
      have h0 := hv a.length (by simp)
      have h1 := hv (a.length + 1) (by simp)
      have h2 := hv (a.length + 2) (by simp)
      rw [h0, h1, h2]
      have hR1 : (a ++ [D]).count R = a.count R := by simp
      have hD1 : (a ++ [D]).count D = a.count D + 1 := by simp
      have hR1' : (a ++ [R]).count R = a.count R + 1 := by simp
      have hD1' : (a ++ [R]).count D = a.count D := by simp
      have hR2 : (a ++ [D, R]).count R = a.count R + 1 := by simp
      have hD2 : (a ++ [D, R]).count D = a.count D + 1 := by simp
      simp only [vtx, List.take_left' rfl, take_len_succ, take_len_two, hR1, hD1, hR1', hD1',
        hR2, hD2]
      obtain ⟨j, hj⟩ : ∃ j, p - a.count D = j + 1 := ⟨p - a.count D - 1, by omega⟩
      have hj' : p - (a.count D + 1) = j := by omega
      rw [hj, hj', eta.eq_3]
    · rw [Function.update_of_ne htn, hv t (hlen ▸ ht), vtx_swap p a b D R t htn]
  · intro t ht
    simp only
    rw [Function.update_of_ne (by simp at ht; omega)]
    exact hg t (by rw [← hlen]; exact ht)

/-- **The invariant along any flip sequence.** Every vertex of a reachable labelled path carries
the recursion-defined value `eta` of that vertex. -/
theorem good_of_reachable (L : V → V → V → V) (m p : ℕ) (g : ℕ → V) {s : List Dir × (ℕ → V)}
    (h : Relation.ReflTransGen (Flip L) (initWord m p, g) s) : Good L p g s := by
  induction h with
  | refl => exact good_init L m p g
  | tail _ hstep ih => exact good_flip L p g ih hstep

theorem reachable_label_eq_eta (L : V → V → V → V) (m p : ℕ) (g : ℕ → V) {w : List Dir}
    {f : ℕ → V} (h : Relation.ReflTransGen (Flip L) (initWord m p, g) (w, f)) :
    ∀ t ≤ w.length, f t = eta L p g (vtx p w t).1 (vtx p w t).2 :=
  (good_of_reachable L m p g h).2.1

/-- **Confluence.** Two flip sequences from the same initial labelled path that end on the same
path produce the same labels. -/
theorem confluence (L : V → V → V → V) (m p : ℕ) (g : ℕ → V) {w : List Dir} {f₁ f₂ : ℕ → V}
    (h₁ : Relation.ReflTransGen (Flip L) (initWord m p, g) (w, f₁))
    (h₂ : Relation.ReflTransGen (Flip L) (initWord m p, g) (w, f₂)) : f₁ = f₂ := by
  obtain ⟨-, hv₁, hg₁⟩ := good_of_reachable L m p g h₁
  obtain ⟨-, hv₂, hg₂⟩ := good_of_reachable L m p g h₂
  funext t
  rcases Nat.lt_or_ge w.length t with ht | ht
  · exact (hg₁ t ht).trans (hg₂ t ht).symm
  · exact (hv₁ t ht).trans (hv₂ t ht).symm

/-- The form used in Lemma D: two flip sequences from `D^p R^m` to `R^m D^p` agree. -/
theorem confluence_final (L : V → V → V → V) (m p : ℕ) (g : ℕ → V) {f₁ f₂ : ℕ → V}
    (h₁ : Relation.ReflTransGen (Flip L) (initWord m p, g) (finalWord m p, f₁))
    (h₂ : Relation.ReflTransGen (Flip L) (initWord m p, g) (finalWord m p, f₂)) : f₁ = f₂ :=
  confluence L m p g h₁ h₂

/-! ## Backward moves: harmless exactly when the rule is an involution in its middle slot -/

/-- One backward move at position `a.length`: `R D ↦ D R`, and the vertex at `a.length + 1` gets
`L` of the three other corners. This relation is *not* part of the theorem. It exists for
lesion 2. -/
inductive Unflip (L : V → V → V → V) : List Dir × (ℕ → V) → List Dir × (ℕ → V) → Prop
  | mk (a b : List Dir) (f : ℕ → V) :
      Unflip L (a ++ R :: D :: b, f)
        (a ++ D :: R :: b,
          Function.update f (a.length + 1) (L (f a.length) (f (a.length + 1)) (f (a.length + 2))))

/-- If `L a (L a b c) c = b`, a backward move also preserves the invariant. Then mixed
forward/backward sequences are confluent too. -/
theorem good_unflip (L : V → V → V → V) (hL : ∀ a b c, L a (L a b c) c = b) (p : ℕ)
    (g : ℕ → V) {s s' : List Dir × (ℕ → V)} (hs : Good L p g s) (h : Unflip L s s') :
    Good L p g s' := by
  obtain ⟨a, b, f⟩ := h
  obtain ⟨hc, hv, hg⟩ := hs
  simp only at hc hv hg
  have hlen : (a ++ D :: R :: b).length = (a ++ R :: D :: b).length := by simp
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.count_append, List.count_cons] at hc ⊢; omega
  · intro t ht
    simp only
    by_cases htn : t = a.length + 1
    · subst htn
      rw [Function.update_self]
      have hd : (a.count D) + 1 ≤ p := by
        rw [← hc]; simp [List.count_append]
      rw [hv a.length (by simp), hv (a.length + 1) (by simp), hv (a.length + 2) (by simp)]
      have hR1 : (a ++ [D]).count R = a.count R := by simp
      have hD1 : (a ++ [D]).count D = a.count D + 1 := by simp
      have hR1' : (a ++ [R]).count R = a.count R + 1 := by simp
      have hD1' : (a ++ [R]).count D = a.count D := by simp
      have hR2 : (a ++ [R, D]).count R = a.count R + 1 := by simp
      have hD2 : (a ++ [R, D]).count D = a.count D + 1 := by simp
      simp only [vtx, List.take_left' rfl, take_len_succ, take_len_two, hR1, hD1, hR1', hD1',
        hR2, hD2]
      obtain ⟨j, hj⟩ : ∃ j, p - a.count D = j + 1 := ⟨p - a.count D - 1, by omega⟩
      have hj' : p - (a.count D + 1) = j := by omega
      rw [hj, hj', eta.eq_3, hL]
    · rw [Function.update_of_ne htn, hv t (hlen ▸ ht), vtx_swap p a b R D t htn]
  · intro t ht
    simp only
    rw [Function.update_of_ne (by simp at ht; omega)]
    exact hg t (by rw [← hlen]; exact ht)

/-! ## Executable flips (for the lesions) -/

/-- Flip at position `t` with a rule that may also read the step number `s`; `none` if the
letters at `t, t+1` are not `D R`. With `rev = true` it is the backward move `R D ↦ D R`. -/
def flipAt (L : ℕ → V → V → V → V) (rev : Bool) (s : ℕ) (w : List Dir) (f : ℕ → V) (t : ℕ) :
    Option (List Dir × (ℕ → V)) :=
  let x := if rev then R else D
  let y := if rev then D else R
  if (w.drop t).take 2 = [x, y] then
    some (w.take t ++ y :: x :: w.drop (t + 2),
      Function.update f (t + 1) (L s (f t) (f (t + 1)) (f (t + 2))))
  else none

/-- Run a list of moves `(rev, t)`; the `k`-th move uses step number `k`. -/
def run (L : ℕ → V → V → V → V) : ℕ → List (Bool × ℕ) → List Dir × (ℕ → V) →
    Option (List Dir × (ℕ → V))
  | _, [], st => some st
  | k, (rev, t) :: ms, (w, f) => (flipAt L rev k w f t).bind (run L (k + 1) ms)

/-- Observe a state: the word and the labels at positions `0 … n`. -/
def snap (n : ℕ) (o : Option (List Dir × (ℕ → V))) : Option (List Dir × List V) :=
  o.map fun st => (st.1, (List.range (n + 1)).map st.2)

/-- Soundness of the executable forward flip with a step-blind rule: it *is* a `Flip`. -/
theorem flipAt_sound (L : V → V → V → V) (s : ℕ) (w : List Dir) (f : ℕ → V) (t : ℕ)
    (st : List Dir × (ℕ → V)) (h : flipAt (fun _ => L) false s w f t = some st) :
    Flip L (w, f) st := by
  simp only [flipAt, Bool.false_eq_true, if_false] at h
  split_ifs at h with hc
  cases h
  have hw : w = w.take t ++ D :: R :: w.drop (t + 2) := by
    conv_lhs => rw [← List.take_append_drop t w]
    congr 1
    rw [← List.take_append_drop 2 (w.drop t), hc, List.drop_drop, Nat.add_comm]
    rfl
  have hlen : (w.take t).length = t := by
    have := congrArg List.length hc
    simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil] at this
    simp only [List.length_take]
    omega
  have := Flip.mk (L := L) (w.take t) (w.drop (t + 2)) f
  rw [← hw, hlen] at this
  exact this

/-- The two orders on the `2 × 2` grid. Word positions: `DDRR`. Rows-first:
`1,0,2,1`; columns-first: `1,2,0,1`. Both end at `RRDD`. -/
def ordA : List (Bool × ℕ) := [(false, 1), (false, 0), (false, 2), (false, 1)]
def ordB : List (Bool × ℕ) := [(false, 1), (false, 2), (false, 0), (false, 1)]

/-- Positive control: with a step-blind rule both orders are legal, reach `RRDD`, and agree.
The rule is `a + 2b + 3c + 1`, chosen so that it is not symmetric in its arguments. -/
theorem control_two_orders_agree :
    snap 4 (run (fun _ a b c => a + 2 * b + 3 * c + 1 : ℕ → ℕ → ℕ → ℕ → ℕ) 0 ordA
        (initWord 2 2, fun t => t)) =
      snap 4 (run (fun _ a b c => a + 2 * b + 3 * c + 1) 0 ordB (initWord 2 2, fun t => t)) ∧
    (snap 4 (run (fun _ a b c => a + 2 * b + 3 * c + 1 : ℕ → ℕ → ℕ → ℕ → ℕ) 0 ordA
        (initWord 2 2, fun t => t))).map Prod.fst = some (finalWord 2 2) := by
  decide

/-- **Lesion 1 (load-bearing).** A rule that also reads the step number (`L s a b c = s`) gives
different final labellings for the two orders on the `2 × 2` grid. Both runs are legal and
both end at `RRDD`. -/
theorem lesion_step_indexed :
    (snap 4 (run (fun s _ _ _ => s : ℕ → ℕ → ℕ → ℕ → ℕ) 0 ordA (initWord 2 2, fun _ => 0))) =
      some (finalWord 2 2, [0, 1, 3, 2, 0]) ∧
    (snap 4 (run (fun s _ _ _ => s : ℕ → ℕ → ℕ → ℕ → ℕ) 0 ordB (initWord 2 2, fun _ => 0))) =
      some (finalWord 2 2, [0, 2, 3, 1, 0]) := by
  decide

/-- **Lesion 2.** With a backward move and the non-involutive rule `L a b c = b + 1` on the
`1 × 1` grid, "flip" and "flip, unflip, flip" reach the same path `RD` with different labels.
(`good_unflip` shows that an involutive rule makes backward moves harmless.) -/
theorem lesion_unflip :
    snap 2 (run (fun _ _ b _ => b + 1 : ℕ → ℕ → ℕ → ℕ → ℕ) 0 [(false, 0)]
        (initWord 1 1, fun _ => 0)) = some ([R, D], [0, 1, 0]) ∧
    snap 2 (run (fun _ _ b _ => b + 1 : ℕ → ℕ → ℕ → ℕ → ℕ) 0 [(false, 0), (true, 0), (false, 0)]
        (initWord 1 1, fun _ => 0)) = some ([R, D], [0, 3, 0]) := by
  decide

/-- **Lesion 3 (control).** Different initial labellings give different final labellings. -/
theorem lesion_initial :
    snap 2 (run (fun _ a b c => a + b + c : ℕ → ℕ → ℕ → ℕ → ℕ) 0 [(false, 0)]
        (initWord 1 1, fun _ => 0)) ≠
    snap 2 (run (fun _ a b c => a + b + c : ℕ → ℕ → ℕ → ℕ → ℕ) 0 [(false, 0)]
        (initWord 1 1, fun t => if t = 0 then 1 else 0)) := by
  decide

end TworowD4Kernel.GrowthConfluence
