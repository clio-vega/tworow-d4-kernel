/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.Q597G1
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Q597 Theorem G1: the signed edge count from a puzzle lift

Paper proof: `projects/proofs/2026-11-24c2-Q597-D.tex`, Theorem `thm:G1` (the "by edges /
by tiles" count), resting on Lemma D (3),(4) (Knutson–Tao, as stated in Purbhoo
arXiv:0705.1184 §2.4).

`Q597G1.G1_of_signedEdgeCount` concluded `N = [Δ]` from the named hypothesis
`hSEC : ∂N = ∂[Δ]`. This file derives `∂N` from a *puzzle with a 0-lift*:

* a labelling `lab` of unit edges by `0`, `1`, `10`;
* a vertex map `f : ℤ² → ℤ²` (the 0-lift `f₀ = π₀ ∘ L`) such that on every edge of `T_n`
  labelled `0`, `f` moves by the edge vector, and on every edge labelled `1` it stays put
  (`LiftOK`; this is the defining property of `L` in Lemma D(1), not its existence);
* every unit triangle of `T_n` is `000` or has a `1`-edge (`PieceOK`; true for KT pieces and
  for their mirror images — *no chirality is used*).

The tile-by-tile count is the identity `∂N = f_*(∂[T_n])` (`bd_N_eq`), proved by linearity:
`f_*(∂ t) = ∂[f t]` on a `000`-triangle (translation) and `f_*(∂ t) = 0` on a triangle with a
`1`-edge (two of its vertices have the same image; this covers the KT rhombi *and* the
`111`-triangles, so no rhombus pairing is needed), and interior edges cancel because
`∂` and `f_*` are linear.  The boundary statement Lemma D(4) enters only as
`f_*(∂[T_n]) = ∂[Δ]` (`hBdry`), which is the named hypothesis that replaces `hSEC`.
-/

namespace Q597G1

open Ori Cls Finsupp

/-- Lattice points `(a,b) ↔ a + bω`. -/
abbrev V := ℤ × ℤ

/-- Reference tail of an edge (module docstring of `Q597G1`). -/
def Edge.tail (e : Edge) : V :=
  match e.k with
  | c0 => (e.a, e.b) | c1 => (e.a, e.b) | c2 => (e.a + 1, e.b)

/-- Reference head of an edge. -/
def Edge.head (e : Edge) : V :=
  match e.k with
  | c0 => (e.a + 1, e.b) | c1 => (e.a, e.b + 1) | c2 => (e.a, e.b + 1)

/-- Edge vector `head - tail`: class 0 is `(1,0)`, class 1 `(0,1)`, class 2 `(-1,1)`. -/
def Edge.vec (e : Edge) : V :=
  match e.k with
  | c0 => (1, 0) | c1 => (0, 1) | c2 => (-1, 1)

/-! ## 1-chains -/

/-- The boundary of a single triangle, as a finitely supported 1-chain (cf. `inc`). -/
noncomputable def bdTri (t : Tri) : Edge →₀ ℤ :=
  match t.o with
  | up => single ⟨t.a, t.b, c0⟩ 1 + single ⟨t.a, t.b, c2⟩ 1 - single ⟨t.a, t.b, c1⟩ 1
  | down => single ⟨t.a + 1, t.b, c1⟩ 1 - single ⟨t.a, t.b + 1, c0⟩ 1 - single ⟨t.a, t.b, c2⟩ 1

theorem bdTri_apply (t : Tri) (e : Edge) : bdTri t e = inc t e := by
  rcases t with ⟨a, b, _ | _⟩ <;> rcases e with ⟨a', b', _ | _ | _⟩ <;>
    simp only [bdTri, inc, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.single_apply,
      Edge.mk.injEq, reduceCtorEq, and_true, and_false] <;>
    split_ifs <;> first | contradiction | omega

/-- The boundary map `C₂ → C₁`. -/
noncomputable def bd : (Tri →₀ ℤ) →ₗ[ℤ] (Edge →₀ ℤ) := linearCombination ℤ bdTri

theorem bd_apply (c : Tri →₀ ℤ) (e : Edge) : bd c e = bdry c e := by
  unfold bd bdry
  rw [linearCombination_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  simp [bdTri_apply]

/-- The unit lattice edge from `x` to `y`, as a signed 1-chain; `0` if `x,y` are not
adjacent (in particular if `x = y`). -/
noncomputable def seg (x y : V) : Edge →₀ ℤ :=
  if y = x + (1, 0) then single ⟨x.1, x.2, c0⟩ 1
  else if y = x + (0, 1) then single ⟨x.1, x.2, c1⟩ 1
  else if y = x + (-1, 1) then single ⟨x.1 - 1, x.2, c2⟩ 1
  else if x = y + (1, 0) then -single ⟨y.1, y.2, c0⟩ 1
  else if x = y + (0, 1) then -single ⟨y.1, y.2, c1⟩ 1
  else if x = y + (-1, 1) then -single ⟨y.1 - 1, y.2, c2⟩ 1
  else 0

theorem seg_self (x : V) : seg x x = 0 := by
  obtain ⟨a, b⟩ := x
  simp [seg, Prod.ext_iff]

theorem seg_swap (x y : V) : seg y x = -seg x y := by
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  unfold seg
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add]
  split_ifs <;> first | simp | (exfalso; omega)

/-- `seg` of an edge's reference endpoints is that edge. -/
theorem seg_edge (e : Edge) : seg e.tail e.head = single e 1 := by
  rcases e with ⟨a, b, _ | _ | _⟩ <;>
    simp [seg, Edge.tail, Edge.head, Prod.ext_iff]

theorem seg_c0 (x : V) : seg x (x + (1, 0)) = single ⟨x.1, x.2, c0⟩ 1 := by
  simp [seg]

theorem seg_c1 (x : V) : seg x (x + (0, 1)) = single ⟨x.1, x.2, c1⟩ 1 := by
  obtain ⟨a, b⟩ := x; simp [seg, Prod.ext_iff]

theorem seg_c2 (x : V) : seg x (x + (-1, 1)) = single ⟨x.1 - 1, x.2, c2⟩ 1 := by
  obtain ⟨a, b⟩ := x; simp [seg, Prod.ext_iff]

/-- Translation invariance of `seg` on reference edges. -/
theorem seg_translate (e : Edge) (v : V) :
    seg (e.tail + v) (e.head + v) = single ⟨e.a + v.1, e.b + v.2, e.k⟩ 1 := by
  rcases e with ⟨a, b, _ | _ | _⟩ <;> obtain ⟨v1, v2⟩ := v
  · have : ((a + 1, b) : V) + (v1, v2) = ((a, b) + (v1, v2)) + (1, 0) := by
      ext <;> simp <;> ring
    simp only [Edge.tail, Edge.head]; rw [this, seg_c0]; simp
  · have : ((a, b + 1) : V) + (v1, v2) = ((a, b) + (v1, v2)) + (0, 1) := by
      ext <;> simp <;> ring
    simp only [Edge.tail, Edge.head]; rw [this, seg_c1]; simp
  · have : ((a, b + 1) : V) + (v1, v2) = ((a + 1, b) + (v1, v2)) + (-1, 1) := by
      ext <;> simp <;> ring
    simp only [Edge.tail, Edge.head]; rw [this, seg_c2]; simp; ring_nf

/-! ## Pushforward along a vertex map, and the two local cases -/

/-- `f_*` on 1-chains: the edge `pq` goes to the unit segment `f p → f q` (or to `0`). -/
noncomputable def fstar (f : V → V) : (Edge →₀ ℤ) →ₗ[ℤ] (Edge →₀ ℤ) :=
  linearCombination ℤ fun e => seg (f e.tail) (f e.head)

/-- Edge labels of a puzzle: `0`, `1`, and the composite `10`. -/
inductive Lbl | l0 | l1 | l10
  deriving DecidableEq, Repr

open Lbl

/-- The three edges of a unit triangle (in the order of `bdTri`). -/
def triEdges (t : Tri) : List Edge :=
  match t.o with
  | up => [⟨t.a, t.b, c0⟩, ⟨t.a, t.b, c2⟩, ⟨t.a, t.b, c1⟩]
  | down => [⟨t.a + 1, t.b, c1⟩, ⟨t.a, t.b + 1, c0⟩, ⟨t.a, t.b, c2⟩]

/-- The lift condition at one edge (the defining property of `f₀ = π₀ ∘ L`, Lemma D(1)):
a `0`-edge is moved by its own vector, a `1`-edge is collapsed. `10`-edges are unconstrained. -/
def LiftOK (lab : Edge → Lbl) (f : V → V) (e : Edge) : Prop :=
  (lab e = l0 → f e.head = f e.tail + e.vec) ∧ (lab e = l1 → f e.head = f e.tail)

/-- A `000`-triangle. -/
def Is000 (lab : Edge → Lbl) (t : Tri) : Prop := ∀ e ∈ triEdges t, lab e = l0

instance (lab : Edge → Lbl) (t : Tri) : Decidable (Is000 lab t) := by
  unfold Is000; infer_instance

/-- A triangle with a `1`-edge (`111`-triangles, and both halves of every KT rhombus,
of either chirality). -/
def Has1 (lab : Edge → Lbl) (t : Tri) : Prop := ∃ e ∈ triEdges t, lab e = l1

/-- The image triangle of a `000`-triangle under `f` (a translate of `t`). -/
def imgTri (f : V → V) (t : Tri) : Tri :=
  match t.o with
  | up => ⟨(f (t.a, t.b)).1, (f (t.a, t.b)).2, up⟩
  | down => ⟨(f (t.a + 1, t.b)).1 - 1, (f (t.a + 1, t.b)).2, down⟩

theorem fstar_single (f : V → V) (e : Edge) :
    fstar f (single e 1) = seg (f e.tail) (f e.head) := by
  simp [fstar]

/-- A cyclic sum of three `seg`s vanishes when two of the three points coincide. -/
theorem seg_cycle_eq_zero (u v w : V) (h : u = v ∨ v = w ∨ u = w) :
    seg u v + seg v w - seg u w = 0 := by
  rcases h with rfl | rfl | rfl
  · simp [seg_self]
  · simp [seg_self]
  · rw [seg_self, seg_swap u v]; abel

theorem fstar_bdTri_up (f : V → V) (a b : ℤ) :
    fstar f (bdTri ⟨a, b, up⟩) =
      seg (f (a, b)) (f (a + 1, b)) + seg (f (a + 1, b)) (f (a, b + 1)) -
        seg (f (a, b)) (f (a, b + 1)) := by
  simp [bdTri, map_add, map_sub, fstar_single, Edge.tail, Edge.head]

theorem fstar_bdTri_down (f : V → V) (a b : ℤ) :
    fstar f (bdTri ⟨a, b, down⟩) =
      seg (f (a + 1, b)) (f (a + 1, b + 1)) + seg (f (a + 1, b + 1)) (f (a, b + 1)) -
        seg (f (a + 1, b)) (f (a, b + 1)) := by
  simp only [bdTri, map_sub, fstar_single, Edge.tail, Edge.head]
  rw [seg_swap (f (a + 1, b + 1)) (f (a, b + 1))]; abel

/-- **Degenerate case** (tex: KT rhombus halves and `111`-triangles): a triangle with a
`1`-edge has `f_*(∂t) = 0`. -/
theorem fstar_bdTri_has1 (lab : Edge → Lbl) (f : V → V) (t : Tri)
    (hL : ∀ e ∈ triEdges t, LiftOK lab f e) (h1 : Has1 lab t) : fstar f (bdTri t) = 0 := by
  obtain ⟨e, he, hl⟩ := h1
  have hfe := (hL e he).2 hl
  rcases t with ⟨a, b, _ | _⟩
  · rw [fstar_bdTri_up]; apply seg_cycle_eq_zero
    simp only [triEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp only [Edge.tail, Edge.head] at hfe
    · exact Or.inl hfe.symm
    · exact Or.inr (Or.inl hfe.symm)
    · exact Or.inr (Or.inr hfe.symm)
  · rw [fstar_bdTri_down]; apply seg_cycle_eq_zero
    simp only [triEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;> simp only [Edge.tail, Edge.head] at hfe
    · exact Or.inl hfe.symm
    · exact Or.inr (Or.inl hfe)
    · exact Or.inr (Or.inr hfe.symm)

/-- **Translation case** (tex: "f₀ is a translation on a `000`-triangle"):
`f_*(∂t) = ∂(f t)`. -/
theorem fstar_bdTri_000 (lab : Edge → Lbl) (f : V → V) (t : Tri)
    (hL : ∀ e ∈ triEdges t, LiftOK lab f e) (h0 : Is000 lab t) :
    fstar f (bdTri t) = bdTri (imgTri f t) := by
  have H := fun e (he : e ∈ triEdges t) => (hL e he).1 (h0 e he)
  rcases t with ⟨a, b, _ | _⟩
  · have hq := H ⟨a, b, c0⟩ (by simp [triEdges])
    have hr := H ⟨a, b, c1⟩ (by simp [triEdges])
    simp only [Edge.tail, Edge.head, Edge.vec] at hq hr
    rw [fstar_bdTri_up, hq, hr]
    set x := f (a, b)
    have : x + (0, 1) = (x + (1, 0)) + (-1, 1) := by ext <;> simp
    rw [seg_c0, this, seg_c2, ← this, seg_c1]
    simp [bdTri, imgTri, x]
  · have hq := H ⟨a + 1, b, c1⟩ (by simp [triEdges])
    have hr := H ⟨a, b, c2⟩ (by simp [triEdges])
    simp only [Edge.tail, Edge.head, Edge.vec] at hq hr
    rw [fstar_bdTri_down, hq, hr]
    set x := f (a + 1, b)
    have h1 : x + (-1, 1) = ((x.1 - 1, x.2) : V) + (0, 1) := by ext <;> simp <;> ring
    have h2 : x + (0, 1) = (x + (-1, 1)) + (1, 0) := by ext <;> simp
    rw [seg_c1, h2, seg_swap, seg_c0, seg_c2, h1]
    simp [bdTri, imgTri, x]
    abel

/-! ## Assembly: the tile-by-tile count -/

/-- The puzzle region `T_n` (corners `(0,0),(n,0),(0,n)`) as a 2-chain. -/
noncomputable def Tn (n : ℕ) : Tri →₀ ℤ := deltaChain (0, 0) n

/-- The lift-count chain `N₀ = Σ_{000-triangles τ of T_n} [f τ]`: `N₀ t` is the number of
`000`-triangles whose `f`-image is `t` (tex: the number of `Λ₀`-triangles of `M₀` over `t`). -/
noncomputable def Nchain (lab : Edge → Lbl) (f : V → V) (n : ℕ) : Tri →₀ ℤ :=
  ∑ t ∈ (Tn n).support.filter (Is000 lab), single (imgTri f t) 1

theorem mem_support_Tn {n : ℕ} {t : Tri} : t ∈ (Tn n).support ↔ inDelta (0, 0) n t := by
  simp [Tn, deltaChain_apply, Finsupp.mem_support_iff]

theorem bd_Tn (n : ℕ) : bd (Tn n) = ∑ t ∈ (Tn n).support, bdTri t := by
  unfold bd; rw [linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [mem_support_Tn] at ht
  simp [Tn, deltaChain_apply, ht]

/-- The local hypotheses on a puzzle with a 0-lift: on every unit triangle of `T_n`, the lift
condition holds at its three edges, and the triangle is `000` or has a `1`-edge. -/
def PuzzleLift (lab : Edge → Lbl) (f : V → V) (n : ℕ) : Prop :=
  ∀ t, inDelta (0, 0) n t → (∀ e ∈ triEdges t, LiftOK lab f e) ∧ (Is000 lab t ∨ Has1 lab t)

/-- **The "by tiles" count** (tex Thm G1, `S` evaluated tile by tile, then by edges):
`∂N₀ = f_*(∂[T_n])`. Interior edges of `T_n` cancel inside `∂[T_n]`; `000`-triangles
contribute `∂[f τ]`; every other triangle contributes `0`. -/
theorem bd_N_eq (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hT : PuzzleLift lab f n) :
    bd (Nchain lab f n) = fstar f (bd (Tn n)) := by
  rw [bd_Tn, map_sum, ← Finset.sum_filter_add_sum_filter_not _ (Is000 lab)]
  have h2 : ∑ t ∈ (Tn n).support.filter (fun t => ¬ Is000 lab t), fstar f (bdTri t) = 0 := by
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [Finset.mem_filter, mem_support_Tn] at ht
    exact fstar_bdTri_has1 lab f t (hT t ht.1).1 ((hT t ht.1).2.resolve_left ht.2)
  rw [h2, add_zero, Nchain, map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.mem_filter, mem_support_Tn] at ht
  rw [fstar_bdTri_000 lab f t (hT t ht.1).1 ht.2]
  simp [bd]

/-- **Theorem G1 from a puzzle lift**, with Lemma D(4) as the one named hypothesis
`hBdry : f_*(∂[T_n]) = ∂[Δ(p,m)]` ("the boundary of `T_n` maps onto `∂Δ₀`, each unit edge
once, interiors on matching sides"). This replaces `hSEC` of `G1_of_signedEdgeCount`. -/
theorem G1_of_lift (lab : Edge → Lbl) (f : V → V) (n : ℕ) (p : ℤ × ℤ) (m : ℕ)
    (hT : PuzzleLift lab f n) (hBdry : fstar f (bd (Tn n)) = bd (deltaChain p m)) (t : Tri) :
    Nchain lab f n t = if inDelta p m t then 1 else 0 :=
  G1_of_signedEdgeCount _ p m
    (fun e => by rw [← bd_apply, ← bd_apply, bd_N_eq lab f n hT, hBdry]) t

/-! ## Lemma D(4): the boundary of `T_n` maps onto `∂Δ` -/

/-- Indicator sums over `range n` with a unique solution. -/
theorem sum_range_ind (n : ℕ) (P : ℕ → Prop) [DecidablePred P] (c : ℤ) (Q : Prop) [Decidable Q]
    (h : ∀ i : ℕ, P i ↔ ((i : ℤ) = c ∧ Q)) :
    (∑ i ∈ Finset.range n, if P i then (1 : ℤ) else 0) =
      if 0 ≤ c ∧ c < n ∧ Q then 1 else 0 := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; split_ifs <;> omega
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hn := h n
    push_cast
    by_cases hP : P n <;> by_cases hQ : Q <;> simp [hP, hQ] at hn ⊢ <;> split_ifs <;> omega

/-- `∂[T_n]`: the bottom side (class 0, `+`), the hypotenuse (class 2, `+`), the left
side (class 1, `-`). -/
theorem bd_Tn_explicit (n : ℕ) :
    bd (Tn n) = (∑ i ∈ Finset.range n, single ⟨(i : ℤ), 0, c0⟩ 1) +
      (∑ j ∈ Finset.range n, single ⟨(n : ℤ) - 1 - j, j, c2⟩ 1) -
      (∑ j ∈ Finset.range n, single ⟨0, (j : ℤ), c1⟩ 1) := by
  ext ⟨a, b, k⟩
  rw [bd_apply, bdry_eq_bdryFun]
  rcases k with _ | _ | _ <;>
  simp only [Finsupp.add_apply, Finsupp.sub_apply, Finsupp.finsetSum_apply, Finsupp.single_apply,
    Edge.mk.injEq, bdryFun, Tn, deltaChain_apply, reduceCtorEq, and_true, and_false]
  all_goals simp only [and_false, if_false, Finset.sum_const_zero, add_zero, zero_add,
    sub_zero]
  · rw [sum_range_ind n _ a (b = 0) (fun i => by constructor <;> intro h <;> omega)]
    simp only [posTri, negTri, inDelta]; split_ifs <;> omega
  · rw [sum_range_ind n _ b (a = 0) (fun i => by constructor <;> intro h <;> omega)]
    simp only [posTri, negTri, inDelta]; split_ifs <;> omega
  · rw [sum_range_ind n _ b (a + b + 1 = n) (fun i => by constructor <;> intro h <;> omega)]
    simp only [posTri, negTri, inDelta]; split_ifs <;> omega

/-- **Walk lemma** (tex Lemma D(4), one side): a lattice walk whose every step is `D` or `0`
pushes forward to the straight run of its `k` nonzero steps. -/
theorem walk (x : ℕ → V) (D : V) (L : ℕ) (h : ∀ i < L, x (i + 1) = x i + D ∨ x (i + 1) = x i) :
    ∃ k : ℕ, x L = x 0 + (k : ℤ) • D ∧
      ∑ i ∈ Finset.range L, seg (x i) (x (i + 1)) =
        ∑ j ∈ Finset.range k, seg (x 0 + (j : ℤ) • D) (x 0 + (j : ℤ) • D + D) := by
  induction L with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ L ih =>
    obtain ⟨k, hk, hs⟩ := ih fun i hi => h i (by omega)
    rw [Finset.sum_range_succ, hs]
    rcases h L (by omega) with h1 | h1
    · refine ⟨k + 1, ?_, ?_⟩
      · rw [h1, hk]; push_cast; rw [add_smul, one_smul, add_assoc]
      · rw [Finset.sum_range_succ, h1, hk]
    · exact ⟨k, by rw [h1, hk], by rw [h1, seg_self, add_zero]⟩

/-- The KT boundary condition: every boundary edge of `T_n` is labelled `0` or `1`. -/
def BdryOK (lab : Edge → Lbl) (n : ℕ) : Prop :=
  ∀ i < n, (lab ⟨(i : ℤ), 0, c0⟩ = l0 ∨ lab ⟨(i : ℤ), 0, c0⟩ = l1) ∧
    (lab ⟨(n : ℤ) - 1 - i, i, c2⟩ = l0 ∨ lab ⟨(n : ℤ) - 1 - i, i, c2⟩ = l1) ∧
    (lab ⟨0, (i : ℤ), c1⟩ = l0 ∨ lab ⟨0, (i : ℤ), c1⟩ = l1)

/-- The canonical image of `∂[T_n]`: the boundary of the triangle `p + k·T₁`, written as
three straight runs (bottom, hypotenuse from `p + k(1,0)`, left side). -/
noncomputable def runs (p : V) (k : ℕ) : Edge →₀ ℤ :=
  (∑ j ∈ Finset.range k, seg (p + (j : ℤ) • (1, 0)) (p + (j : ℤ) • (1, 0) + (1, 0))) +
    (∑ j ∈ Finset.range k, seg (p + (k : ℤ) • (1, 0) + (j : ℤ) • (-1, 1))
      (p + (k : ℤ) • (1, 0) + (j : ℤ) • (-1, 1) + (-1, 1))) -
    (∑ j ∈ Finset.range k, seg (p + (j : ℤ) • (0, 1)) (p + (j : ℤ) • (0, 1) + (0, 1)))

/-- One walk step from the lift condition at an edge labelled `0` or `1`. -/
theorem step_of_lift (lab : Edge → Lbl) (f : V → V) (e : Edge) (hL : LiftOK lab f e)
    (hb : lab e = l0 ∨ lab e = l1) : f e.head = f e.tail + e.vec ∨ f e.head = f e.tail :=
  hb.imp hL.1 hL.2

/-- **Lemma D(2),(4)** for a puzzle with a 0-lift: the three sides of `T_n` carry the same
number `k` of `0`s (here: `f` advances by `k` along each side), and `f_*(∂[T_n])` is the
boundary of `f(0,0) + k·T₁`, run by run. -/
theorem fstar_bd_Tn (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hT : PuzzleLift lab f n)
    (hB : BdryOK lab n) :
    ∃ k : ℕ, f ((n : ℤ), 0) = f (0, 0) + (k : ℤ) • (1, 0) ∧
      fstar f (bd (Tn n)) = runs (f (0, 0)) k := by
  have lift : ∀ t e, inDelta (0, 0) n t → e ∈ triEdges t → LiftOK lab f e :=
    fun t e ht he => (hT t ht).1 e he
  -- bottom
  obtain ⟨kb, hkb, hsb⟩ := walk (fun i : ℕ => f ((i : ℤ), 0)) (1, 0) n fun i hi => by
    have := step_of_lift lab f ⟨i, 0, c0⟩
      (lift ⟨i, 0, up⟩ _ (by simp [inDelta]; omega) (by simp [triEdges])) (hB i hi).1
    simpa [Edge.tail, Edge.head, Edge.vec] using this
  -- hypotenuse, from `(n,0)` to `(0,n)`
  obtain ⟨kh, hkh, hsh⟩ := walk (fun j : ℕ => f ((n : ℤ) - j, j)) (-1, 1) n fun j hj => by
    have := step_of_lift lab f ⟨(n : ℤ) - 1 - j, j, c2⟩
      (lift ⟨(n : ℤ) - 1 - j, j, up⟩ _ (by simp [inDelta]; omega) (by simp [triEdges]))
      (hB j hj).2.1
    have e1 : (n : ℤ) - 1 - j + 1 = n - j := by ring
    have e2 : (n : ℤ) - 1 - j = n - (j + 1) := by ring
    simp only [Edge.tail, Edge.head, Edge.vec] at this
    rw [e1, e2] at this; push_cast; exact this
  -- left side, from `(0,0)` to `(0,n)`
  obtain ⟨kl, hkl, hsl⟩ := walk (fun j : ℕ => f (0, (j : ℤ))) (0, 1) n fun j hj => by
    have := step_of_lift lab f ⟨0, j, c1⟩
      (lift ⟨0, j, up⟩ _ (by simp [inDelta]; omega) (by simp [triEdges])) (hB j hj).2.2
    simpa [Edge.tail, Edge.head, Edge.vec] using this
  simp only [sub_zero, CharP.cast_eq_zero] at hkb hkh hkl hsb hsh hsl
  -- D(2): the three counts agree
  have hcorner : f (0, (n : ℤ)) = f (0, 0) + (kb : ℤ) • (1, 0) + (kh : ℤ) • (-1, 1) := by
    rw [← hkb]; simpa using hkh
  have hh : kh = kb ∧ kl = kb := by
    have := hcorner.symm.trans hkl
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at this
    omega
  obtain ⟨rfl, rfl⟩ := hh
  refine ⟨_, hkb, ?_⟩
  rw [bd_Tn_explicit, map_sub, map_add, map_sum, map_sum, map_sum]
  simp only [fstar_single, Edge.tail, Edge.head]
  unfold runs
  -- `congr` closes the bottom and left runs by `hsb`, `hsl`; the hypotenuse needs reindexing.
  congr 1; congr 1
  rw [← hkb, ← hsh]; refine Finset.sum_congr rfl fun j _ => ?_
  congr 2 <;> ext <;> push_cast <;> ring

/-! ## `∂[Δ]` from the all-`0` puzzle, and Theorem G1 with no named hypothesis -/

/-- The all-`0` "puzzle" of size `m` translated by `p` is a puzzle lift. -/
theorem puzzleLift_trans (p : V) (m : ℕ) : PuzzleLift (fun _ => l0) (fun v => v + p) m := by
  intro t _
  refine ⟨fun e _ => ⟨fun _ => ?_, fun h => absurd h Lbl.noConfusion⟩, Or.inl fun _ _ => rfl⟩
  rcases e with ⟨a, b, _ | _ | _⟩ <;>
    ext <;> simp [Edge.tail, Edge.head, Edge.vec] <;> ring

/-- Its lift-count chain is `[Δ(p,m)]`. -/
theorem nchain_trans (p : V) (m : ℕ) :
    Nchain (fun _ => l0) (fun v => v + p) m = deltaChain p m := by
  ext t
  have hf : (Tn m).support.filter (Is000 fun _ => l0) = (Tn m).support :=
    Finset.filter_true_of_mem fun _ _ _ _ => rfl
  rw [Nchain, hf, Finsupp.finsetSum_apply, deltaChain_apply]
  have key : ∀ t', imgTri (fun v => v + p) t' = t ↔ t' = ⟨t.a - p.1, t.b - p.2, t.o⟩ := by
    intro t'
    rcases t with ⟨a, b, _ | _⟩ <;> rcases t' with ⟨a', b', _ | _⟩ <;>
      simp only [imgTri, Tri.mk.injEq, Prod.fst_add, Prod.snd_add, reduceCtorEq, and_false,
        and_true] <;> omega
  simp_rw [Finsupp.single_apply, key, Finset.sum_ite_eq', mem_support_Tn]
  rcases t with ⟨a, b, _ | _⟩ <;> simp only [inDelta] <;> split_ifs <;> omega

theorem bdryOK_zero (m : ℕ) : BdryOK (fun _ => l0) m := fun _ _ => ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

/-- `∂[Δ(p,m)]` is `runs p m`. -/
theorem bd_delta (p : V) (m : ℕ) : bd (deltaChain p m) = runs p m := by
  obtain ⟨k, hk, h⟩ := fstar_bd_Tn _ _ m (puzzleLift_trans p m) (bdryOK_zero m)
  have hkm : k = m := by
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at hk
    omega
  rw [← nchain_trans, bd_N_eq _ _ _ (puzzleLift_trans p m), h, ← hkm]
  congr 1; simp

/-- **Theorem G1, from a puzzle with a 0-lift, with no named hypothesis.**
`lab` labels the unit edges of `T_n` by `0,1,10`; `f` is the 0-lift (`LiftOK` on every edge of
every unit triangle); every triangle is `000` or has a `1`-edge (all KT pieces and their mirror
images); the boundary carries only `0`s and `1`s. Let `m` be the advance of `f` along the
bottom side (= the number of `0`s there). Then `N₀(t) = 1` for `t ⊆ Δ₀ = f(0,0) + m·T₁` and
`0` otherwise.

Paper: `proofs/2026-11-24c2-Q597-D.tex` Thm G1 with Lemma D(2)–(4) (Knutson–Tao, as stated in
Purbhoo arXiv:0705.1184 §2.4). The *existence* of the lift `f` (Lemma D(1)) is an input, not
proved here: it is where chirality enters. -/
theorem G1_puzzle (lab : Edge → Lbl) (f : V → V) (n m : ℕ) (hT : PuzzleLift lab f n)
    (hB : BdryOK lab n) (hm : f ((n : ℤ), 0) = f (0, 0) + ((m : ℤ), 0)) (t : Tri) :
    Nchain lab f n t = if inDelta (f (0, 0)) m t then 1 else 0 := by
  obtain ⟨k, hk, h⟩ := fstar_bd_Tn lab f n hT hB
  have hkm : k = m := by
    rw [hm] at hk
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at hk
    omega
  refine G1_of_lift lab f n (f (0, 0)) m hT ?_ t
  rw [h, bd_delta, hkm]

end Q597G1
