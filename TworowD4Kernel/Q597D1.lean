/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.Q597G1Lift

/-!
# Q597 Lemma D(1): every KT puzzle has a 0-lift; Theorem G1 for every KT puzzle

Paper proof: `projects/proofs/2026-11-24c2-Q597-D.tex`, Lemma `lem:chir` and Lemma `lem:D`(1)
(Knutson–Tao, as stated in Purbhoo arXiv:0705.1184 §2.4).

`Q597G1.G1_puzzle` proved Theorem G1 for a labelling *with* a 0-lift `f` (`PuzzleLift`). This file
constructs `f` for every KT puzzle, so G1 holds with no hypothesis beyond KT-ness.

Only the `Λ₀`-part `f₀ = π₀ ∘ L` of the tex's `ℤ⁴`-lift is built, since that is all `G1_puzzle`
consumes. The tex's cochain, projected to `Λ₀`, is: an oriented `0`-edge gets its own vector,
a `1`-edge gets `0`, and a `10`-edge gets minus the `0`-part of the other two edges of a
`(10,0,1)`-triangle containing it.

* `coch lab`: the cochain, with the `10`-value read from the **up**-triangle containing the edge
  (every edge `⟨a,b,k⟩` is an edge of the up-triangle `(a,b)`), so closure on up-triangles holds by
  construction.
* `rhombus_rule` (tex Lemma chir (b) / the well-definedness step of D(1)): the value the
  down-triangle across a `10`-edge would assign agrees with the up-triangle's value.  This is a
  finite check over pairs of KT pieces, and **this is where chirality enters**:
  `rhombus_rule_mirror_fails` is a kernel-checked counterexample for mirror pieces.
* `integ_exact` (tex "Exactness": the triangulated disk): a cochain on the unit edges of `T_n`
  that is closed on every unit triangle is the coboundary of its row-path integral `integ c`
  (up the left side, then along the row). Proved by induction along rows, with no topology.
  `annulus_control`: drop closure on a single down-triangle and a closed-elsewhere cochain is
  not exact, so the hypothesis of `integ_exact` is what carries the disk.
* `G1_KT`: Theorem G1 for every KT puzzle.
-/

namespace Q597G1

open Ori Cls Lbl Finset

/-! ## The cochain -/

/-- The `0`-part of a `0`/`1`-edge of class `k` with label `x`. -/
def locv (k : Cls) (x : Lbl) : V :=
  if x = l0 then (match k with | c0 => (1, 0) | c1 => (0, 1) | c2 => (-1, 1)) else 0

/-- The cochain value on the class-`k` edge of a unit triangle whose class-0,1,2 edges carry
labels `x0 x1 x2`, all in the reference orientations. The relation to be kept is
`c(class 0) + c(class 2) = c(class 1)` — the same for up- and down-triangles. A `10`-edge gets
the value forced by this relation from the other two (tex: `(-d_0,-d_1)`, projected to `Λ₀`). -/
def triVal (k : Cls) (x0 x1 x2 : Lbl) : V :=
  match k with
  | c0 => if x0 = l10 then locv c1 x1 - locv c2 x2 else locv c0 x0
  | c1 => if x1 = l10 then locv c0 x0 + locv c2 x2 else locv c1 x1
  | c2 => if x2 = l10 then locv c1 x1 - locv c0 x0 else locv c2 x2

/-- The `Λ₀`-cochain of a labelling: read off the up-triangle `(a,b)` containing `⟨a,b,k⟩`. -/
def coch (lab : Edge → Lbl) (e : Edge) : V :=
  triVal e.k (lab ⟨e.a, e.b, c0⟩) (lab ⟨e.a, e.b, c1⟩) (lab ⟨e.a, e.b, c2⟩)

/-! ## KT pieces (Purbhoo's chirality) -/

/-- A KT piece read counterclockwise: a rotation of `(0,0,0)`, `(1,1,1)` or `(10,0,1)`. -/
def KTPiece : Lbl → Lbl → Lbl → Bool
  | l0, l0, l0 | l1, l1, l1 | l10, l0, l1 | l0, l1, l10 | l1, l10, l0 => true
  | _, _, _ => false

/-- The mirror pieces: rotations of `(0,0,0)`, `(1,1,1)` or `(10,1,0)` (lesion only). -/
def MirPiece : Lbl → Lbl → Lbl → Bool
  | l0, l0, l0 | l1, l1, l1 | l10, l1, l0 | l1, l0, l10 | l0, l10, l1 => true
  | _, _, _ => false

/-- The counterclockwise labels of a unit triangle (the order of `triEdges`). Up `(a,b)`:
classes `0, 2, 1`; down `(a,b)`: classes `1, 0, 2` (tex Lemma chir (a)). -/
def KTTri (lab : Edge → Lbl) (t : Tri) : Prop :=
  match t.o with
  | up => KTPiece (lab ⟨t.a, t.b, c0⟩) (lab ⟨t.a, t.b, c2⟩) (lab ⟨t.a, t.b, c1⟩) = true
  | down => KTPiece (lab ⟨t.a + 1, t.b, c1⟩) (lab ⟨t.a, t.b + 1, c0⟩) (lab ⟨t.a, t.b, c2⟩) = true

instance : Fintype Lbl where
  elems := {l0, l1, l10}
  complete x := by cases x <;> decide

instance : Fintype Cls where
  elems := {c0, c1, c2}
  complete x := by cases x <;> decide

/-! ## Lemma chir, finite form -/

/-- Up-triangle closure: on a KT piece, `c(0) + c(2) = c(1)` (it holds for any piece with at
most one `10`). -/
theorem triVal_closed : ∀ x0 x1 x2 : Lbl, KTPiece x0 x2 x1 = true →
    triVal c0 x0 x1 x2 + triVal c2 x0 x1 x2 = triVal c1 x0 x1 x2 := by decide

/-- Down-triangle closure, local form: on a KT piece read as a down-triangle
(counterclockwise classes `1, 0, 2`), `c(0) + c(2) = c(1)`. -/
theorem triVal_closed_down : ∀ y0 y1 y2 : Lbl, KTPiece y1 y0 y2 = true →
    triVal c0 y0 y1 y2 + triVal c2 y0 y1 y2 = triVal c1 y0 y1 y2 := by decide

/-- **The rhombus rule** (tex Lemma chir (b), and the well-definedness of the `10`-value in
Lemma D(1)): if an up-triangle (ccw classes `0,2,1`) and a down-triangle (ccw classes `1,0,2`)
are KT pieces sharing their class-`k` edge, they assign it the same value. Both triangles read
the classes in the same cyclic order (Lemma chir (a)), which is the half-turn argument. -/
theorem rhombus_rule_c0 : ∀ x0 x1 x2 y1 y2 : Lbl, KTPiece x0 x2 x1 = true →
    KTPiece y1 x0 y2 = true → triVal c0 x0 x1 x2 = triVal c0 x0 y1 y2 := by decide

theorem rhombus_rule_c1 : ∀ x0 x1 x2 y0 y2 : Lbl, KTPiece x0 x2 x1 = true →
    KTPiece x1 y0 y2 = true → triVal c1 x0 x1 x2 = triVal c1 y0 x1 y2 := by decide

theorem rhombus_rule_c2 : ∀ x0 x1 x2 y0 y1 : Lbl, KTPiece x0 x2 x1 = true →
    KTPiece y1 y0 x2 = true → triVal c2 x0 x1 x2 = triVal c2 y0 y1 x2 := by decide

/-- **Control: the rule needs consistent chirality, not KT's chirality.** For mirror pieces
throughout, the rhombus rule *also* holds (the half-turn argument does not distinguish the two
chiralities). This matches the census: on all mirror labellings with `n ≤ 3` (2, 5, 14 of them)
the row-path integral is a lift (`scratch/q597_d1_check.py`). -/
theorem rhombus_rule_mirror : ∀ (k : Cls) (x0 x1 x2 y0 y1 y2 : Lbl),
    MirPiece x0 x2 x1 = true → MirPiece y1 y0 y2 = true →
    ((k = c0 ∧ x0 = y0) ∨ (k = c1 ∧ x1 = y1) ∨ (k = c2 ∧ x2 = y2)) →
    triVal k x0 x1 x2 = triVal k y0 y1 y2 := by decide

/-- **Mixed-chirality lesion** (kernel): a KT up-triangle `(1,10,0)` glued along its class-2
`10`-edge to a mirror down-triangle `(1,0,10)` gives the edge two different values, `(0,1)` and
`(-1,0)`. Census: with up-triangles KT and down-triangles mirror, the integral is a lift on only
2 of 5 (`n=2`) and 2 of 16 (`n=3`) labellings. -/
theorem rhombus_rule_mixed_fails :
    KTPiece l1 l10 l0 = true ∧ MirPiece l1 l0 l10 = true ∧
      triVal c2 l1 l0 l10 = (0, 1) ∧ triVal c2 l0 l1 l10 = (-1, 0) := by decide

/-! ## Closed ⇒ exact on the triangle -/

/-- Closure of a cochain on every unit triangle of `T_n`, in reference orientations
(up `(a,b)`: `c⟨a,b,0⟩ + c⟨a,b,2⟩ = c⟨a,b,1⟩`; down `(a,b)`:
`c⟨a,b+1,0⟩ + c⟨a,b,2⟩ = c⟨a+1,b,1⟩`, i.e. `bdTri` pairs to `0`). -/
def Closed (c : Edge → V) (n : ℕ) : Prop :=
  (∀ a b : ℕ, a + b + 1 ≤ n → c ⟨a, b, c0⟩ + c ⟨a, b, c2⟩ = c ⟨a, b, c1⟩) ∧
  (∀ a b : ℕ, a + b + 2 ≤ n →
    c ⟨(a : ℤ), (b : ℤ) + 1, c0⟩ + c ⟨a, b, c2⟩ = c ⟨(a : ℤ) + 1, b, c1⟩)

/-- The row-path integral: up the left side to `(0,b)`, then along row `b` to `(a,b)`. -/
def integ (c : Edge → V) (p : V) : V :=
  (∑ j ∈ range p.2.toNat, c ⟨0, j, c1⟩) + ∑ i ∈ range p.1.toNat, c ⟨i, p.2, c0⟩

theorem integ_nat (c : Edge → V) (i j : ℕ) :
    integ c ((i : ℤ), (j : ℤ)) =
      (∑ j' ∈ range j, c ⟨0, j', c1⟩) + ∑ i' ∈ range i, c ⟨i', j, c0⟩ := by
  simp [integ]

theorem integ_c0 (c : Edge → V) (i j : ℕ) :
    integ c ((i : ℤ) + 1, (j : ℤ)) = integ c (i, j) + c ⟨i, j, c0⟩ := by
  have := integ_nat c (i + 1) j
  push_cast at this
  rw [this, integ_nat, sum_range_succ, add_assoc]

theorem integ_c1 (c : Edge → V) (n : ℕ) (h : Closed c n) :
    ∀ i j : ℕ, i + j + 1 ≤ n → integ c (i, (j : ℤ) + 1) = integ c (i, j) + c ⟨i, j, c1⟩ := by
  intro i
  induction i with
  | zero =>
    intro j _
    have := integ_nat c 0 (j + 1)
    have h0 := integ_nat c 0 j
    push_cast at this h0 ⊢
    rw [this, h0, sum_range_succ]; simp
  | succ i ih =>
    intro j hij
    have hu1 := h.1 i j (by omega)
    have hd := h.2 i j (by omega)
    have hu2 := h.1 i (j + 1) (by omega)
    have e1 := integ_c0 c i (j + 1)
    have e2 := integ_c0 c i j
    push_cast at e1 e2 hu2 ⊢
    rw [e1, e2, ih j (by omega), ← hd, ← hu1]
    abel

theorem integ_c2 (c : Edge → V) (n : ℕ) (h : Closed c n) (i j : ℕ) (hij : i + j + 1 ≤ n) :
    integ c (i, (j : ℤ) + 1) = integ c ((i : ℤ) + 1, j) + c ⟨i, j, c2⟩ := by
  rw [integ_c1 c n h i j hij, integ_c0, ← h.1 i j hij]; abel

/-- **Closed ⇒ exact on `T_n`** (tex Lemma D(1), "Exactness"): every edge of every up-triangle of
`T_n` — hence every unit edge of `T_n` — has `c e = integ c (head) - integ c (tail)`. -/
theorem integ_exact (c : Edge → V) (n : ℕ) (h : Closed c n) (e : Edge)
    (ha : 0 ≤ e.a) (hb : 0 ≤ e.b) (hn : e.a + e.b + 1 ≤ n) :
    integ c e.head = integ c e.tail + c e := by
  rcases e with ⟨a, b, k⟩
  lift a to ℕ using ha
  lift b to ℕ using hb
  have hn' : a + b + 1 ≤ n := by simp at hn; omega
  rcases k with _ | _ | _ <;> simp only [Edge.head, Edge.tail]
  · exact integ_c0 c a b
  · exact integ_c1 c n h a b hn'
  · exact integ_c2 c n h a b hn'

/-! ## KT puzzle ⇒ closed ⇒ lift -/

/-- KT on every unit triangle of `T_n`. -/
def AllKT (lab : Edge → Lbl) (n : ℕ) : Prop := ∀ t, inDelta (0, 0) n t → KTTri lab t

theorem closed_of_KT (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) : Closed (coch lab) n := by
  constructor
  · intro a b hab
    have := hK ⟨a, b, up⟩ (by simp [inDelta]; omega)
    exact triVal_closed _ _ _ this
  · intro a b hab
    have hd := hK ⟨a, b, down⟩ (by simp [inDelta]; omega)
    have hu0 := hK ⟨a, (b : ℤ) + 1, up⟩ (by simp [inDelta]; omega)
    have hu1 := hK ⟨(a : ℤ) + 1, b, up⟩ (by simp [inDelta]; omega)
    have hu2 := hK ⟨a, b, up⟩ (by simp [inDelta]; omega)
    simp only [KTTri] at hd hu0 hu1 hu2
    -- the down-triangle's own values (classes 0,1,2 at `⟨a,b+1,0⟩, ⟨a+1,b,1⟩, ⟨a,b,2⟩`)
    set y0 := lab ⟨a, (b : ℤ) + 1, c0⟩
    set y1 := lab ⟨(a : ℤ) + 1, b, c1⟩
    set y2 := lab ⟨a, b, c2⟩
    have r0 : coch lab ⟨a, (b : ℤ) + 1, c0⟩ = triVal c0 y0 y1 y2 :=
      rhombus_rule_c0 _ _ _ y1 y2 hu0 hd
    have r1 : coch lab ⟨(a : ℤ) + 1, b, c1⟩ = triVal c1 y0 y1 y2 :=
      rhombus_rule_c1 _ _ _ y0 y2 hu1 hd
    have r2 : coch lab ⟨a, b, c2⟩ = triVal c2 y0 y1 y2 :=
      rhombus_rule_c2 _ _ _ y0 y1 hu2 hd
    rw [r0, r1, r2]
    exact triVal_closed_down _ _ _ hd

/-- On a `0`-edge the cochain is the edge vector, on a `1`-edge it is `0`. -/
theorem coch_l0 (lab : Edge → Lbl) (e : Edge) (h : lab e = l0) : coch lab e = e.vec := by
  rcases e with ⟨a, b, _ | _ | _⟩ <;> simp [coch, triVal, locv, Edge.vec, h]

theorem coch_l1 (lab : Edge → Lbl) (e : Edge) (h : lab e = l1) : coch lab e = 0 := by
  rcases e with ⟨a, b, _ | _ | _⟩ <;> simp [coch, triVal, locv, h]

theorem piece_000_or_has1 : ∀ x y z : Lbl, KTPiece x y z = true →
    (x = l0 ∧ y = l0 ∧ z = l0) ∨ (x = l1 ∨ y = l1 ∨ z = l1) := by decide

theorem is000_or_has1_of_piece (lab : Edge → Lbl) (t : Tri) (p q r : Edge)
    (ht : triEdges t = [p, q, r]) (hk : KTPiece (lab p) (lab q) (lab r) = true) :
    Is000 lab t ∨ Has1 lab t := by
  unfold Is000 Has1; rw [ht]
  rcases piece_000_or_has1 _ _ _ hk with ⟨h1, h2, h3⟩ | h | h | h
  · left; simp [h1, h2, h3]
  · exact Or.inr ⟨p, by simp, h⟩
  · exact Or.inr ⟨q, by simp, h⟩
  · exact Or.inr ⟨r, by simp, h⟩

/-- **Lemma D(1), `Λ₀`-part** (tex Lemma D(1), Knutson–Tao as stated in Purbhoo
arXiv:0705.1184 §2.4): every labelling all of whose unit triangles are KT pieces has a 0-lift,
namely `integ (coch lab)`. -/
theorem puzzleLift_of_KT (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) :
    PuzzleLift lab (integ (coch lab)) n := by
  have hC := closed_of_KT lab n hK
  have hE : ∀ e : Edge, 0 ≤ e.a → 0 ≤ e.b → e.a + e.b + 1 ≤ n → LiftOK lab (integ (coch lab)) e :=
    fun e ha hb hn => by
      have := integ_exact _ n hC e ha hb hn
      exact ⟨fun h => by rw [this, coch_l0 lab e h], fun h => by rw [this, coch_l1 lab e h,
        add_zero]⟩
  intro t ht
  refine ⟨fun e he => ?_, ?_⟩
  · rcases t with ⟨a, b, _ | _⟩ <;> simp only [inDelta, sub_zero] at ht <;>
      simp only [triEdges, List.mem_cons, List.not_mem_nil, or_false] at he <;>
      rcases he with rfl | rfl | rfl <;> exact hE _ (by simp; omega) (by simp; omega)
        (by simp; omega)
  · have hk := hK t ht
    rcases t with ⟨a, b, _ | _⟩ <;> simp only [KTTri] at hk <;>
      exact is000_or_has1_of_piece lab _ _ _ _ rfl hk

/-- **Theorem G1 for every KT puzzle** (tex Thm G1 with Lemma D(1)–(4)): if every unit
triangle of `T_n` is a KT piece and the boundary carries only `0`s and `1`s, the 0-lift
`f = integ (coch lab)` exists, and for `m` = the number of `0`s on the bottom side,
`N₀(t) = 1` exactly for the unit triangles of `Δ₀ = f(0,0) + m·T₁`. -/
theorem G1_KT (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    ∃ f : V → V, PuzzleLift lab f n ∧ ∃ m : ℕ, f ((n : ℤ), 0) = f (0, 0) + ((m : ℤ), 0) ∧
      ∀ t, Nchain lab f n t = if inDelta (f (0, 0)) m t then 1 else 0 := by
  have hT := puzzleLift_of_KT lab n hK
  obtain ⟨k, hk, -⟩ := fstar_bd_Tn lab _ n hT hB
  have hk' : integ (coch lab) ((n : ℤ), 0) = integ (coch lab) (0, 0) + ((k : ℤ), 0) := by
    rw [hk]; simp
  exact ⟨_, hT, k, hk', G1_puzzle lab _ n k hT hB hk'⟩

/-! ## Control: closed ≠ exact on an annulus -/

/-- The annulus `T_3 ∖ down(0,0)`: the cochain `c = (1,0)` on `⟨0,0,2⟩`, `-(1,0)` on `⟨0,0,0⟩`,
`0` elsewhere (a cut from the hole to the outside) is closed on every unit triangle of `T_3`
except `down(0,0)`, and no vertex map integrates it on the edges of `T_3`. So the full closure
hypothesis of `integ_exact` (the disk) is what is used. -/
def annulusCoch (e : Edge) : V :=
  if e = ⟨0, 0, c2⟩ then (1, 0) else if e = ⟨0, 0, c0⟩ then (-1, 0) else 0

theorem annulus_control :
    (∀ a b : ℕ, a + b + 1 ≤ 3 →
      annulusCoch ⟨a, b, c0⟩ + annulusCoch ⟨a, b, c2⟩ = annulusCoch ⟨a, b, c1⟩) ∧
    (∀ a b : ℕ, a + b + 2 ≤ 3 → (a, b) ≠ (0, 0) →
      annulusCoch ⟨(a : ℤ), (b : ℤ) + 1, c0⟩ + annulusCoch ⟨a, b, c2⟩ =
        annulusCoch ⟨(a : ℤ) + 1, b, c1⟩) ∧
    ¬ ∃ f : V → V, ∀ e : Edge, 0 ≤ e.a → 0 ≤ e.b → e.a + e.b + 1 ≤ 3 →
      f e.head = f e.tail + annulusCoch e := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have : a ≤ 2 := by omega
    have : b ≤ 2 := by omega
    interval_cases a <;> interval_cases b <;> simp [annulusCoch]
  · intro a b hab hne
    have : a ≤ 1 := by omega
    have : b ≤ 1 := by omega
    interval_cases a <;> interval_cases b <;> simp_all [annulusCoch]
  · rintro ⟨f, hf⟩
    have h1 := hf ⟨1, 0, c1⟩ (by simp) (by simp) (by simp)
    have h2 := hf ⟨0, 1, c0⟩ (by simp) (by simp) (by simp)
    have h3 := hf ⟨0, 0, c2⟩ (by simp) (by simp) (by simp)
    simp only [Edge.head, Edge.tail, annulusCoch] at h1 h2 h3
    norm_num at h1 h2 h3
    rw [h2, h3] at h1
    have := congrArg Prod.fst h1
    simp at this

end Q597G1
