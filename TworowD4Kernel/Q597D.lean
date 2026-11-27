/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.Q597G1k1

/-!
# Q597 Lemma D: uniqueness of the lift, the joint `ℤ⁴` lift, and D(3)'s rhombus clause

Paper proof: `projects/proofs/2026-11-24c2-Q597-D.tex`, Lemma `lem:D` (1),(3) and Lemma
`lem:chir` (b) (Knutson–Tao, as stated in Purbhoo arXiv:0705.1184 §2.4, printed pp. 10–11).

Earlier files built the two halves of the lift separately: `f₀ = integ (coch ℓ)` (`Q597D1`) and
`f₁ = integ (coch (swapLab ℓ))` (`Q597G1k1`). This file adds what Lemma D states beyond
existence of the halves.

* **D(1), joint lift** (`jointLift_of_KT`): `L = (f₀, f₁) : ℤ² → ℤ² × ℤ² = Λ₀ × Λ₁` moves by
  `(d,0)` along every `0`-edge and by `(0,d)` along every `1`-edge, and by the tex cochain value
  `(coch ℓ e, coch (swapLab ℓ) e)` along *every* edge. This is pairing the two existing lifts —
  no new argument. `tenVal_up_fidelity` / `tenVal_down_fidelity` check (kernel, 27 label
  triples each) that this value on a `10`-edge is the tex's `(-d₀,-d₁)` read in either of its
  two triangles.
* **D(1), uniqueness up to translation, from the `0/1`-edges alone** (`jointLift_unique`,
  `lift0_unique`, `lift1_unique`): two maps with the lift property on the `0`- and `1`-edges of
  a KT puzzle differ by a constant on all vertices of `T_n`. The tex's argument: every `10`-edge
  of a KT triangle has its endpoints joined by the other two edges, which are `0`/`1`
  (`KT_at_most_one_10`), so the `0/1`-graph is connected; then `const_of_edges` (rows, as in
  `integ_exact`).
* **D(3), rhombus clause** (`rhombus_clause_k0`, `rhombus_clause_k1`): on a KT rhombus, the two
  `k`-edges have the same class and the same `f_k`-image unit segment (same orientation), and each
  `(1-k)`-edge goes to a point. `k = 1` comes from the mirror instance via the swap.

Lesions: `uniq_lesion_drop1` (constrain only the `0`-edges: a second lift exists),
`mixed_rhombus_lesion` (KT up-triangle glued to a mirror down-triangle: the two `0`-edges have
different classes, and no local `0`-lift exists).
-/

namespace Q597G1

open Ori Cls Lbl Finset

/-! ## Edges of `T_n` -/

/-- A property of every unit edge of `T_n` (every such edge is an edge of the up-triangle at
its reference coordinates). -/
def OnEdges (n : ℕ) (Q : Edge → Prop) : Prop :=
  ∀ e : Edge, 0 ≤ e.a → 0 ≤ e.b → e.a + e.b + 1 ≤ n → Q e

theorem onEdges_of_tri (n : ℕ) (Q : Edge → Prop)
    (h : ∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t, Q e) : OnEdges n Q := by
  intro ⟨a, b, k⟩ ha hb hn
  have ht : inDelta (0, 0) n ⟨a, b, up⟩ := by simp only [inDelta] at *; simp at hn ⊢; omega
  exact h _ ht _ (by rcases k <;> simp [triEdges])

/-- **Connectivity** (tex D(1) "the graph is connected"): a map constant along every unit edge
of `T_n` is constant on its vertices. Up the left side, then along each row. -/
theorem const_of_edges {W : Type*} (D : V → W) (n : ℕ)
    (h : OnEdges n fun e => D e.head = D e.tail) :
    ∀ i j : ℕ, i + j ≤ n → D ((i : ℤ), (j : ℤ)) = D (0, 0) := by
  have left : ∀ j : ℕ, j ≤ n → D (0, (j : ℤ)) = D (0, 0) := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have := h ⟨0, j, c1⟩ (le_refl _) (by simp) (by simp; omega)
      simp only [Edge.head, Edge.tail] at this
      push_cast; rw [this, ih (by omega)]
  intro i
  induction i with
  | zero => intro j hj; simpa using left j (by omega)
  | succ i ih =>
    intro j hij
    have := h ⟨i, j, c0⟩ (by simp) (by simp) (by simp; omega)
    simp only [Edge.head, Edge.tail] at this
    push_cast; rw [this, ih j (by omega)]

/-! ## The `0/1`-subgraph spans: at most one `10` per KT triangle -/

theorem KT_at_most_one_10 : ∀ x0 x1 x2 : Lbl, KTPiece x0 x2 x1 = true →
    (x0 = l10 → x1 ≠ l10 ∧ x2 ≠ l10) ∧ (x1 = l10 → x0 ≠ l10 ∧ x2 ≠ l10) ∧
      (x2 = l10 → x0 ≠ l10 ∧ x1 ≠ l10) := by decide

/-- **The `0/1`-edges suffice** (tex D(1), last sentence): on a KT puzzle, a map constant along
every `0`- and `1`-edge of `T_n` is constant along every edge, `10`-edges included. -/
theorem edges_of_nonten (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) {W : Type*} (D : V → W)
    (h : OnEdges n fun e => lab e ≠ l10 → D e.head = D e.tail) :
    OnEdges n fun e => D e.head = D e.tail := by
  intro ⟨a, b, k⟩ ha hb hn
  have ht : inDelta (0, 0) n ⟨a, b, up⟩ := by simp only [inDelta] at *; simp at hn ⊢; omega
  have hk := hK _ ht
  simp only [KTTri] at hk
  have h10 := KT_at_most_one_10 _ _ _ hk
  have e0 := h ⟨a, b, c0⟩ ha hb (by simpa using hn)
  have e1 := h ⟨a, b, c1⟩ ha hb (by simpa using hn)
  have e2 := h ⟨a, b, c2⟩ ha hb (by simpa using hn)
  rcases k <;> simp only [Edge.head, Edge.tail] at e0 e1 e2 ⊢
  · by_cases h0 : lab ⟨a, b, c0⟩ = l10
    · rw [← e2 (h10.1 h0).2, e1 (h10.1 h0).1]
    · exact e0 h0
  · by_cases h1 : lab ⟨a, b, c1⟩ = l10
    · rw [e2 (h10.2.1 h1).2, e0 (h10.2.1 h1).1]
    · exact e1 h1
  · by_cases h2 : lab ⟨a, b, c2⟩ = l10
    · rw [e1 (h10.2.2 h2).2, e0 (h10.2.2 h2).1]
    · exact e2 h2

/-! ## D(1): uniqueness up to translation -/

/-- The joint lift condition at an edge: `L = (f₀,f₁)` moves by `(d,0)` on a `0`-edge and by
`(0,d)` on a `1`-edge (tex D(1)'s cochain on `0/1`-edges). `10`-edges are unconstrained. -/
def JointOK (lab : Edge → Lbl) (L : V → V × V) (e : Edge) : Prop :=
  (lab e = l0 → L e.head = L e.tail + (e.vec, 0)) ∧ (lab e = l1 → L e.head = L e.tail + (0, e.vec))

/-- Generic uniqueness: two maps whose difference is constant along every `0/1`-edge differ by
a constant on `T_n`. -/
theorem unique_of_nonten (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) {W : Type*}
    [AddCommGroup W] (F G : V → W)
    (h : OnEdges n fun e => lab e ≠ l10 → F e.head - G e.head = F e.tail - G e.tail) :
    ∀ i j : ℕ, i + j ≤ n →
      F ((i : ℤ), (j : ℤ)) = G ((i : ℤ), (j : ℤ)) + (F (0, 0) - G (0, 0)) := by
  intro i j hij
  have := const_of_edges (fun p => F p - G p) n (edges_of_nonten lab n hK (fun p => F p - G p) h) i j hij
  simp only at this
  rw [← this]; abel

/-- **Lemma D(1), uniqueness of the joint lift** (tex: "unique up to translation … determined by
the `0`- and `1`-edges alone"): two maps `L, L' : ℤ² → Λ₀ × Λ₁` with the lift property on every
`0`- and `1`-edge of a KT puzzle differ by the constant `L(0,0) - L'(0,0)` on every vertex of
`T_n`. -/
theorem jointLift_unique (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (L L' : V → V × V)
    (hL : OnEdges n (JointOK lab L)) (hL' : OnEdges n (JointOK lab L')) :
    ∀ i j : ℕ, i + j ≤ n →
      L ((i : ℤ), (j : ℤ)) = L' ((i : ℤ), (j : ℤ)) + (L (0, 0) - L' (0, 0)) := by
  refine unique_of_nonten lab n hK L L' fun e ha hb hn hne => ?_
  have h1 := hL e ha hb hn
  have h2 := hL' e ha hb hn
  cases hl : lab e with
  | l0 => rw [h1.1 hl, h2.1 hl]; abel
  | l1 => rw [h1.2 hl, h2.2 hl]; abel
  | l10 => exact absurd hl hne

/-- Uniqueness of the `Λ₀`-part alone: every `0`-lift (`LiftOK`) is `f₀` up to translation. -/
theorem lift0_unique (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (f g : V → V)
    (hf : OnEdges n (LiftOK lab f)) (hg : OnEdges n (LiftOK lab g)) :
    ∀ i j : ℕ, i + j ≤ n →
      f ((i : ℤ), (j : ℤ)) = g ((i : ℤ), (j : ℤ)) + (f (0, 0) - g (0, 0)) := by
  refine unique_of_nonten lab n hK f g fun e ha hb hn hne => ?_
  have h1 := hf e ha hb hn
  have h2 := hg e ha hb hn
  cases hl : lab e with
  | l0 => rw [h1.1 hl, h2.1 hl]; abel
  | l1 => rw [h1.2 hl, h2.2 hl]
  | l10 => exact absurd hl hne

/-- Uniqueness of the `Λ₁`-part alone (`LiftOK1`, stated on `ℓ` itself). -/
theorem lift1_unique (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (f g : V → V)
    (hf : OnEdges n (LiftOK1 lab f)) (hg : OnEdges n (LiftOK1 lab g)) :
    ∀ i j : ℕ, i + j ≤ n →
      f ((i : ℤ), (j : ℤ)) = g ((i : ℤ), (j : ℤ)) + (f (0, 0) - g (0, 0)) := by
  refine unique_of_nonten lab n hK f g fun e ha hb hn hne => ?_
  have h1 := hf e ha hb hn
  have h2 := hg e ha hb hn
  cases hl : lab e with
  | l1 => rw [h1.1 hl, h2.1 hl]; abel
  | l0 => rw [h1.2 hl, h2.2 hl]
  | l10 => exact absurd hl hne

/-! ## D(1): the joint lift exists -/

/-- The joint lift `L = (f₀, f₁)`: the two row-path integrals of c1 and c2, paired. -/
def jointL (lab : Edge → Lbl) (p : V) : V × V :=
  (integ (coch lab) p, integ (coch (swapLab lab)) p)

/-- **Lemma D(1), existence of the `ℤ⁴`-lift** (tex Lemma D(1); Knutson–Tao as stated in Purbhoo
arXiv:0705.1184 §2.4): for a KT puzzle, `L = jointL ℓ` satisfies `L(q) - L(p) = c(pq)` on every
unit edge of `T_n`, where `c = (coch ℓ, coch (swapLab ℓ))` is the tex cochain: `(d,0)` on
`0`-edges, `(0,d)` on `1`-edges, and on `10`-edges the value fixed by closure (see the fidelity
lemmas below). In particular `L` has the joint lift property. This is the pairing of
`puzzleLift_of_KT` and `puzzleLift_of_mirror ∘ swap`; nothing new is proved about either half. -/
theorem jointLift_of_KT (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) :
    OnEdges n (fun e => jointL lab e.head = jointL lab e.tail + (coch lab e, coch (swapLab lab) e))
      ∧ OnEdges n (JointOK lab (jointL lab)) := by
  have hC0 := closed_of_KT lab n hK
  have hC1 := closed_of_pieces MirPiece goodPieces_Mir (swapLab lab) n (allMir_swap lab n hK)
  have hex : OnEdges n
      (fun e => jointL lab e.head = jointL lab e.tail + (coch lab e, coch (swapLab lab) e)) :=
    fun e ha hb hn => by
      simp only [jointL, Prod.mk_add_mk, integ_exact _ n hC0 e ha hb hn,
        integ_exact _ n hC1 e ha hb hn]
  refine ⟨hex, fun e ha hb hn => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hex e ha hb hn, coch_l0 lab e h, coch_swap_l0 lab e h]
  · rw [hex e ha hb hn, coch_l1 lab e h, coch_swap_l1 lab e h]

/-! ## Fidelity of the `10`-value to the tex's `(-d₀,-d₁)` -/

/-- Counterclockwise edge vectors of an up-triangle, by class (tex Lemma chir (a)). -/
def ccwUp : Cls → V | c0 => (1, 0) | c1 => (0, -1) | c2 => (-1, 1)
/-- Reference orientation = `sUp k` × counterclockwise orientation, on an up-triangle. -/
def sUp : Cls → ℤ | c0 => 1 | c1 => -1 | c2 => 1
/-- Counterclockwise edge vectors of a down-triangle, by class. -/
def ccwDown : Cls → V | c0 => (-1, 0) | c1 => (0, 1) | c2 => (1, -1)
def sDown : Cls → ℤ | c0 => -1 | c1 => 1 | c2 => -1

/-- Labels by class. -/
def byCls (x0 x1 x2 : Lbl) : Cls → Lbl | c0 => x0 | c1 => x1 | c2 => x2

/-- `d_x` of the tex: the counterclockwise vector of the edge labelled `x`. -/
def dOf (ccw : Cls → V) (x0 x1 x2 : Lbl) (x : Lbl) : V :=
  (if byCls x0 x1 x2 c0 = x then ccw c0 else 0) + (if byCls x0 x1 x2 c1 = x then ccw c1 else 0) +
    (if byCls x0 x1 x2 c2 = x then ccw c2 else 0)

/-- **Fidelity, up-triangle** (kernel, 27 triples × 3 classes): on a KT up-triangle, the
`10`-edge's cochain value, in reference orientation, is `s · (-d₀, -d₁)` with `d₀, d₁` the
counterclockwise vectors of its `0`- and `1`-edge — the tex's definition. -/
theorem tenVal_up_fidelity : ∀ (k : Cls) (x0 x1 x2 : Lbl), KTPiece x0 x2 x1 = true →
    byCls x0 x1 x2 k = l10 →
    triVal k x0 x1 x2 = sUp k • (-dOf ccwUp x0 x1 x2 l0) ∧
      triVal k (swap01 x0) (swap01 x1) (swap01 x2) = sUp k • (-dOf ccwUp x0 x1 x2 l1) := by
  decide

/-- **Fidelity, down-triangle**: the same value is the tex's `(-d₀,-d₁)` read in the other
triangle of the rhombus (tex D(1) "well-defined on `10`-edges"). -/
theorem tenVal_down_fidelity : ∀ (k : Cls) (y0 y1 y2 : Lbl), KTPiece y1 y0 y2 = true →
    byCls y0 y1 y2 k = l10 →
    triVal k y0 y1 y2 = sDown k • (-dOf ccwDown y0 y1 y2 l0) ∧
      triVal k (swap01 y0) (swap01 y1) (swap01 y2) = sDown k • (-dOf ccwDown y0 y1 y2 l1) := by
  decide

/-! ## D(3): translation on `k`-triangles, constant on `(1-k)`-triangles -/

/-- The three vertices of a unit triangle. -/
def triVerts (t : Tri) : List V :=
  match t.o with
  | up => [(t.a, t.b), (t.a + 1, t.b), (t.a, t.b + 1)]
  | down => [(t.a + 1, t.b), (t.a + 1, t.b + 1), (t.a, t.b + 1)]

/-- **Lemma D(3), triangle clauses, `k = 0`**: a `0`-lift is the restriction of a translation on
every `000`-triangle, and constant on every `111`-triangle. -/
theorem D3_tri_k0 (lab : Edge → Lbl) (f : V → V) (t : Tri)
    (hL : ∀ e ∈ triEdges t, LiftOK lab f e) :
    (Is000 lab t → ∃ v : V, ∀ p ∈ triVerts t, f p = p + v) ∧
      (Is111 lab t → ∀ p ∈ triVerts t, f p = f (triVerts t).head!) := by
  have E : ∀ e ∈ triEdges t, (lab e = l0 → f e.head = f e.tail + e.vec) ∧
      (lab e = l1 → f e.head = f e.tail) := hL
  rcases t with ⟨a, b, _ | _⟩
  · have L1 := E ⟨a, b, c0⟩ (by simp [triEdges])
    have L2 := E ⟨a, b, c1⟩ (by simp [triEdges])
    simp only [Edge.head, Edge.tail, Edge.vec] at L1 L2
    refine ⟨fun h0 => ⟨f (a, b) - (a, b), fun p hp => ?_⟩, fun h1 p hp => ?_⟩ <;>
      simp only [triVerts, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl <;> try simp only [triVerts, List.head!_cons]
    · abel
    · rw [L1.1 (h0 _ (by simp [triEdges]))]; ext <;> simp <;> ring
    · rw [L2.1 (h0 _ (by simp [triEdges]))]; ext <;> simp <;> ring
    · rw [L1.2 (h1 _ (by simp [triEdges]))]
    · rw [L2.2 (h1 _ (by simp [triEdges]))]
  · have L1 := E ⟨a + 1, b, c1⟩ (by simp [triEdges])
    have L2 := E ⟨a, b, c2⟩ (by simp [triEdges])
    simp only [Edge.head, Edge.tail, Edge.vec] at L1 L2
    refine ⟨fun h0 => ⟨f (a + 1, b) - (a + 1, b), fun p hp => ?_⟩, fun h1 p hp => ?_⟩ <;>
      simp only [triVerts, List.mem_cons, List.not_mem_nil, or_false] at hp <;>
      rcases hp with rfl | rfl | rfl <;> try simp only [triVerts, List.head!_cons]
    · abel
    · rw [L1.1 (h0 _ (by simp [triEdges]))]; ext <;> simp <;> ring
    · rw [L2.1 (h0 _ (by simp [triEdges]))]; ext <;> simp <;> ring
    · rw [L1.2 (h1 _ (by simp [triEdges]))]
    · rw [L2.2 (h1 _ (by simp [triEdges]))]

/-- **Lemma D(3), triangle clauses, `k = 1`** (stated on `ℓ`): a `k = 1` lift is a translation on
every `111`-triangle and constant on every `000`-triangle. -/
theorem D3_tri_k1 (lab : Edge → Lbl) (f : V → V) (t : Tri)
    (hL : ∀ e ∈ triEdges t, LiftOK1 lab f e) :
    (Is111 lab t → ∃ v : V, ∀ p ∈ triVerts t, f p = p + v) ∧
      (Is000 lab t → ∀ p ∈ triVerts t, f p = f (triVerts t).head!) := by
  have h := D3_tri_k0 (swapLab lab) f t fun e he => (liftOK1_iff lab f e).1 (hL e he)
  rw [← is111_iff] at h
  have h0 : Is111 (swapLab lab) t ↔ Is000 lab t := by simp [Is111, Is000, swapLab]
  rw [h0] at h
  exact h

/-! ## D(3): the rhombus clause -/

/-- The down-triangle across the class-`k` edge `⟨a,b,k⟩` of the up-triangle `(a,b)`. -/
def rhDown (a b : ℤ) : Cls → Tri
  | c0 => ⟨a, b - 1, down⟩ | c1 => ⟨a - 1, b, down⟩ | c2 => ⟨a, b, down⟩

/-- The four outer edges of the rhombus `up(a,b) ∪ rhDown a b k` (all edges but the shared
`⟨a,b,k⟩`). -/
def rhOuter (a b : ℤ) : Cls → List Edge
  | c0 => [⟨a, b, c1⟩, ⟨a, b, c2⟩, ⟨a + 1, b - 1, c1⟩, ⟨a, b - 1, c2⟩]
  | c1 => [⟨a, b, c0⟩, ⟨a, b, c2⟩, ⟨a - 1, b + 1, c0⟩, ⟨a - 1, b, c2⟩]
  | c2 => [⟨a, b, c0⟩, ⟨a, b, c1⟩, ⟨a + 1, b, c1⟩, ⟨a, b + 1, c0⟩]

/-- The rhombus clause for the "moving" label `x` and the "collapsed" label `y`: the two
`x`-edges have the same class and the same `f`-image unit segment (same orientation), every
`x`-edge is moved by its vector, every `y`-edge goes to a point, and there are exactly two of
each. -/
def RhClause (lab : Edge → Lbl) (f : V → V) (a b : ℤ) (k : Cls) (x y : Lbl) : Prop :=
  (∀ e ∈ rhOuter a b k, ∀ e' ∈ rhOuter a b k, lab e = x → lab e' = x →
      e.k = e'.k ∧ f e.tail = f e'.tail ∧ f e.head = f e'.head) ∧
    (∀ e ∈ rhOuter a b k, lab e = x → f e.head = f e.tail + e.vec) ∧
    (∀ e ∈ rhOuter a b k, lab e = y → f e.head = f e.tail) ∧
    (rhOuter a b k).countP (fun e => lab e = x) = 2 ∧
    (rhOuter a b k).countP (fun e => lab e = y) = 2

theorem KT_10_1 : ∀ y z : Lbl, KTPiece l10 y z = true → y = l0 ∧ z = l1 := by decide
theorem KT_10_2 : ∀ y z : Lbl, KTPiece y l10 z = true → y = l1 ∧ z = l0 := by decide
theorem KT_10_3 : ∀ y z : Lbl, KTPiece y z l10 = true → y = l0 ∧ z = l1 := by decide
theorem Mir_10_1 : ∀ y z : Lbl, MirPiece l10 y z = true → y = l1 ∧ z = l0 := by decide
theorem Mir_10_2 : ∀ y z : Lbl, MirPiece y l10 z = true → y = l0 ∧ z = l1 := by decide
theorem Mir_10_3 : ∀ y z : Lbl, MirPiece y z l10 = true → y = l1 ∧ z = l0 := by decide

/-- **D(3) rhombus clause, for a consistent chirality** (tex Lemma D(3) last sentence, with
Lemma chir (b)): KT pieces or mirror pieces on both triangles of a rhombus, a `0`-lift on its
four outer edges ⇒ `RhClause … l0 l1`. The finite part (which outer edges are `0`, which `1`)
is the six `*_10_*` lemmas; the rest is the lift condition on the four edges. -/
theorem rhombus_clause_P (P : Lbl → Lbl → Lbl → Bool) (hP : P = KTPiece ∨ P = MirPiece)
    (lab : Edge → Lbl) (f : V → V) (a b : ℤ) (k : Cls) (h10 : lab ⟨a, b, k⟩ = l10)
    (hu : PTri P lab ⟨a, b, up⟩) (hd : PTri P lab (rhDown a b k))
    (hL : ∀ e ∈ rhOuter a b k, LiftOK lab f e) : RhClause lab f a b k l0 l1 := by
  unfold RhClause
  rcases hP with rfl | rfl <;> rcases k <;>
    simp only [PTri, rhDown, rhOuter, List.forall_mem_cons,
      and_true] at hu hd hL h10 ⊢ <;>
    simp only [sub_add_cancel, h10] at hu hd <;>
    obtain ⟨L1, L2, L3, L4⟩ := hL
  · obtain ⟨h1, h2⟩ := KT_10_1 _ _ hu
    obtain ⟨h3, h4⟩ := KT_10_2 _ _ hd
    simp only [LiftOK, h1, h2, h3, h4, Edge.head, Edge.tail, Edge.vec, 
      reduceCtorEq, false_implies, true_implies, and_true, true_and] at L1 L2 L3 L4 ⊢
    have e1 : b - 1 + 1 = b := by omega
    have e2 : a - 1 + 1 = a := by omega
    try simp only [e1, e2] at L1 L2 L3 L4 ⊢
    simp_all
  · obtain ⟨h1, h2⟩ := KT_10_3 _ _ hu
    obtain ⟨h3, h4⟩ := KT_10_1 _ _ hd
    simp only [LiftOK, h1, h2, h3, h4, Edge.head, Edge.tail, Edge.vec, 
      reduceCtorEq, false_implies, true_implies, and_true, true_and] at L1 L2 L3 L4 ⊢
    have e1 : b - 1 + 1 = b := by omega
    have e2 : a - 1 + 1 = a := by omega
    try simp only [e1, e2] at L1 L2 L3 L4 ⊢
    simp_all
  · obtain ⟨h1, h2⟩ := KT_10_2 _ _ hu
    obtain ⟨h3, h4⟩ := KT_10_3 _ _ hd
    simp only [LiftOK, h1, h2, h3, h4, Edge.head, Edge.tail, Edge.vec, 
      reduceCtorEq, false_implies, true_implies, and_true, true_and] at L1 L2 L3 L4 ⊢
    have e1 : b - 1 + 1 = b := by omega
    have e2 : a - 1 + 1 = a := by omega
    try simp only [e1, e2] at L1 L2 L3 L4 ⊢
    simp_all
  · obtain ⟨h1, h2⟩ := Mir_10_1 _ _ hu
    obtain ⟨h3, h4⟩ := Mir_10_2 _ _ hd
    simp only [LiftOK, h1, h2, h3, h4, Edge.head, Edge.tail, Edge.vec, 
      reduceCtorEq, false_implies, true_implies, and_true, true_and] at L1 L2 L3 L4 ⊢
    have e1 : b - 1 + 1 = b := by omega
    have e2 : a - 1 + 1 = a := by omega
    try simp only [e1, e2] at L1 L2 L3 L4 ⊢
    simp_all
  · obtain ⟨h1, h2⟩ := Mir_10_3 _ _ hu
    obtain ⟨h3, h4⟩ := Mir_10_1 _ _ hd
    simp only [LiftOK, h1, h2, h3, h4, Edge.head, Edge.tail, Edge.vec, 
      reduceCtorEq, false_implies, true_implies, and_true, true_and] at L1 L2 L3 L4 ⊢
    have e1 : b - 1 + 1 = b := by omega
    have e2 : a - 1 + 1 = a := by omega
    try simp only [e1, e2] at L1 L2 L3 L4 ⊢
    simp_all
  · obtain ⟨h1, h2⟩ := Mir_10_2 _ _ hu
    obtain ⟨h3, h4⟩ := Mir_10_3 _ _ hd
    simp only [LiftOK, h1, h2, h3, h4, Edge.head, Edge.tail, Edge.vec, 
      reduceCtorEq, false_implies, true_implies, and_true, true_and] at L1 L2 L3 L4 ⊢
    have e1 : b - 1 + 1 = b := by omega
    have e2 : a - 1 + 1 = a := by omega
    try simp only [e1, e2] at L1 L2 L3 L4 ⊢
    simp_all

/-- Every outer edge of the rhombus is an edge of one of its two triangles. -/
theorem rhOuter_sub (a b : ℤ) (k : Cls) :
    ∀ e ∈ rhOuter a b k, e ∈ triEdges ⟨a, b, up⟩ ∨ e ∈ triEdges (rhDown a b k) := by
  rcases k <;> simp [rhOuter, triEdges, rhDown]

/-- **Lemma D(3), rhombus clause, `k = 0`** (tex `lem:D`(3); Knutson–Tao as stated in Purbhoo
arXiv:0705.1184 §2.4): on a KT rhombus of a KT puzzle (the up-triangle `(a,b)` and the
down-triangle across its `10`-edge `⟨a,b,k⟩`, both in `T_n`), every `0`-lift `f` — in particular
`f₀ = π₀ ∘ L` — takes the two `0`-edges (same class) to one and the same unit segment and each
`1`-edge to a point. -/
theorem rhombus_clause_k0 (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hK : AllKT lab n)
    (hL : ∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t, LiftOK lab f e) (a b : ℤ) (k : Cls)
    (hu : inDelta (0, 0) n ⟨a, b, up⟩) (hd : inDelta (0, 0) n (rhDown a b k))
    (h10 : lab ⟨a, b, k⟩ = l10) : RhClause lab f a b k l0 l1 :=
  rhombus_clause_P KTPiece (Or.inl rfl) lab f a b k h10 (hK _ hu) (hK _ hd) fun e he =>
    (rhOuter_sub a b k e he).elim (hL _ hu e) (hL _ hd e)

/-- **Lemma D(3), rhombus clause, `k = 1`**: every `k = 1` lift `f` (`LiftOK1`, e.g.
`f₁ = π₁ ∘ L`) takes the two `1`-edges of a KT rhombus to one unit segment and each `0`-edge to
a point. From the mirror instance of `rhombus_clause_P` via the swap (`allMir_swap`). -/
theorem rhombus_clause_k1 (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hK : AllKT lab n)
    (hL : ∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t, LiftOK1 lab f e) (a b : ℤ) (k : Cls)
    (hu : inDelta (0, 0) n ⟨a, b, up⟩) (hd : inDelta (0, 0) n (rhDown a b k))
    (h10 : lab ⟨a, b, k⟩ = l10) : RhClause lab f a b k l1 l0 := by
  have hM := allMir_swap lab n hK
  have h := rhombus_clause_P MirPiece (Or.inr rfl) (swapLab lab) f a b k
    (by simp [swapLab, h10, swap01]) (hM _ hu) (hM _ hd) fun e he =>
    (liftOK1_iff lab f e).1 ((rhOuter_sub a b k e he).elim (hL _ hu e) (hL _ hd e))
  simpa [RhClause, swapLab] using h

/-- **Lemma D(3) for the joint lift**: for a KT puzzle, `jointL ℓ = (f₀,f₁)` satisfies both
rhombus clauses on every KT rhombus in `T_n`. -/
theorem rhombus_clause_joint (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (a b : ℤ) (k : Cls)
    (hu : inDelta (0, 0) n ⟨a, b, up⟩) (hd : inDelta (0, 0) n (rhDown a b k))
    (h10 : lab ⟨a, b, k⟩ = l10) :
    RhClause lab (fun p => (jointL lab p).1) a b k l0 l1 ∧
      RhClause lab (fun p => (jointL lab p).2) a b k l1 l0 := by
  have hT0 := puzzleLift_of_KT lab n hK
  have hT1 := puzzleLift_of_mirror (swapLab lab) n (allMir_swap lab n hK)
  exact ⟨rhombus_clause_k0 lab _ n hK (fun t ht => (hT0 t ht).1) a b k hu hd h10,
    rhombus_clause_k1 lab _ n hK (fun t ht e he => (liftOK1_iff lab _ e).2 ((hT1 t ht).1 e he))
      a b k hu hd h10⟩

/-! ## D(2): the three sides carry the same number of `0`s, and `m` is that number -/

/-- The number of edges labelled `x` on the bottom, hypotenuse and left side of `T_n`. -/
def cntBot (lab : Edge → Lbl) (n : ℕ) (x : Lbl) : ℤ :=
  ∑ i ∈ range n, if lab ⟨(i : ℤ), 0, c0⟩ = x then 1 else 0
def cntHyp (lab : Edge → Lbl) (n : ℕ) (x : Lbl) : ℤ :=
  ∑ j ∈ range n, if lab ⟨(n : ℤ) - 1 - j, j, c2⟩ = x then 1 else 0
def cntLeft (lab : Edge → Lbl) (n : ℕ) (x : Lbl) : ℤ :=
  ∑ j ∈ range n, if lab ⟨0, (j : ℤ), c1⟩ = x then 1 else 0

/-- A walk that moves by `D` at each `0`-letter and stays at each `1`-letter advances by
(number of `0`-letters) · `D`. -/
theorem walk_count (x : ℕ → V) (D : V) (w : ℕ → Lbl) (L : ℕ)
    (h : ∀ i < L, (w i = l0 → x (i + 1) = x i + D) ∧ (w i = l1 → x (i + 1) = x i))
    (hb : ∀ i < L, w i = l0 ∨ w i = l1) :
    x L = x 0 + (∑ i ∈ range L, if w i = l0 then (1 : ℤ) else 0) • D := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [sum_range_succ, add_smul, ← add_assoc, ← ih (fun i hi => h i (by omega))
      (fun i hi => hb i (by omega))]
    rcases hb L (by omega) with hl | hl
    · rw [(h L (by omega)).1 hl, if_pos hl, one_smul]
    · rw [(h L (by omega)).2 hl, if_neg (by rw [hl]; decide), zero_smul, add_zero]

/-- **Lemma D(2)** for any `0`-lift `f` with `0/1` boundary: `f` advances along each side by
the number of `0`s on that side, and the three numbers agree. -/
theorem D2_of_lift (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hL : OnEdges n (LiftOK lab f))
    (hB : BdryOK lab n) :
    f ((n : ℤ), 0) = f (0, 0) + (cntBot lab n l0, 0) ∧
      cntBot lab n l0 = cntHyp lab n l0 ∧ cntBot lab n l0 = cntLeft lab n l0 := by
  have hb := walk_count (fun i : ℕ => f ((i : ℤ), 0)) (1, 0) (fun i => lab ⟨i, 0, c0⟩) n
    (fun i hi => by
      have := hL ⟨i, 0, c0⟩ (by simp) le_rfl (by push_cast; omega)
      simp only [LiftOK, Edge.head, Edge.tail, Edge.vec] at this
      push_cast; exact this) (fun i hi => (hB i hi).1)
  have hh := walk_count (fun j : ℕ => f ((n : ℤ) - j, j)) (-1, 1)
    (fun j => lab ⟨(n : ℤ) - 1 - j, j, c2⟩) n
    (fun j hj => by
      have := hL ⟨(n : ℤ) - 1 - j, j, c2⟩ (by simp; omega) (by simp) (by simp)
      have e1 : (n : ℤ) - 1 - j + 1 = n - j := by ring
      have e2 : (n : ℤ) - ((j : ℤ) + 1) = n - 1 - j := by ring
      simp only [LiftOK, Edge.head, Edge.tail, Edge.vec] at this
      rw [e1] at this; push_cast; rw [e2]; exact this) (fun j hj => (hB j hj).2.1)
  have hl := walk_count (fun j : ℕ => f (0, (j : ℤ))) (0, 1) (fun j => lab ⟨0, j, c1⟩) n
    (fun j hj => by
      have := hL ⟨0, j, c1⟩ le_rfl (by simp) (by simp; omega)
      simp only [LiftOK, Edge.head, Edge.tail, Edge.vec] at this
      push_cast; exact this) (fun j hj => (hB j hj).2.2)
  simp only [CharP.cast_eq_zero, sub_zero, sub_self] at hb hh hl
  rw [hb] at hh
  rw [hh] at hl
  simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at hb hl
  refine ⟨?_, ?_, ?_⟩
  · exact Prod.ext (by rw [hb.1]; simp [cntBot]) (by rw [hb.2]; simp)
  · simp only [cntBot, cntHyp]; linarith [hl.1, hl.2]
  · simp only [cntBot, cntLeft]; linarith [hl.1, hl.2]

/-- `#1 = n - #0` on a side whose letters are all `0` or `1`. -/
theorem cnt_compl (n : ℕ) (w : ℕ → Lbl) (hb : ∀ i < n, w i = l0 ∨ w i = l1) :
    (∑ i ∈ range n, if w i = l1 then (1 : ℤ) else 0) =
      n - ∑ i ∈ range n, if w i = l0 then (1 : ℤ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, sum_range_succ, ih fun i hi => hb i (by omega)]
    push_cast
    rcases hb n (by omega) with h | h <;> simp [h]; ring

/-- **Lemma D(2)** (tex `lem:D`(2)): the three sides of a KT puzzle carry the same number `m₀`
of `0`s, and the same number `m₁ = n - m₀` of `1`s. -/
theorem lemmaD2 (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    cntBot lab n l0 = cntHyp lab n l0 ∧ cntBot lab n l0 = cntLeft lab n l0 ∧
      cntBot lab n l1 = n - cntBot lab n l0 ∧ cntHyp lab n l1 = n - cntHyp lab n l0 ∧
      cntLeft lab n l1 = n - cntLeft lab n l0 := by
  have hT := puzzleLift_of_KT lab n hK
  obtain ⟨-, h1, h2⟩ := D2_of_lift lab _ n (onEdges_of_tri n _ fun t ht => (hT t ht).1) hB
  exact ⟨h1, h2, cnt_compl n _ fun i hi => (hB i hi).1, cnt_compl n _ fun i hi => (hB i hi).2.1,
    cnt_compl n _ fun i hi => (hB i hi).2.2⟩

/-- **Theorem G1, `k = 0`, with `m₀` = the number of `0`s on the bottom side** (replaces the
`#eval` identification of the advance `m` in `G1_KT`). -/
theorem G1_KT_count (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    ∀ t, Nchain lab (integ (coch lab)) n t =
      if inDelta (integ (coch lab) (0, 0)) (cntBot lab n l0).toNat t then 1 else 0 := by
  have hT := puzzleLift_of_KT lab n hK
  obtain ⟨h, -, -⟩ := D2_of_lift lab _ n (onEdges_of_tri n _ fun t ht => (hT t ht).1) hB
  have hpos : 0 ≤ cntBot lab n l0 := sum_nonneg fun _ _ => by split_ifs <;> norm_num
  refine G1_puzzle lab _ n _ hT hB ?_
  rw [h, Int.toNat_of_nonneg hpos]

/-- **Theorem G1, `k = 1`, with `m₁` = the number of `1`s on the bottom side.** -/
theorem G1_KT_k1_count (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    ∀ t, Nchain1 lab (integ (coch (swapLab lab))) n t =
      if inDelta (integ (coch (swapLab lab)) (0, 0)) (cntBot lab n l1).toNat t then 1 else 0 := by
  have hT := puzzleLift_of_mirror (swapLab lab) n (allMir_swap lab n hK)
  have hB' := bdryOK_swap lab n hB
  obtain ⟨h, -, -⟩ := D2_of_lift (swapLab lab) _ n
    (onEdges_of_tri n _ fun t ht => (hT t ht).1) hB'
  have hc : cntBot (swapLab lab) n l0 = cntBot lab n l1 := by simp [cntBot, swapLab]
  have hpos : 0 ≤ cntBot lab n l1 := sum_nonneg fun _ _ => by split_ifs <;> norm_num
  intro t
  rw [nchain1_eq]
  refine G1_puzzle (swapLab lab) _ n _ hT hB' ?_ t
  rw [h, hc, Int.toNat_of_nonneg hpos]

/-- **Lemma D(4), the boundary walk** (tex: "walking a side, `f_k` advances by one unit along
the parallel side of `Δ_k` at each `k`-letter and stays put at each `(1-k)`-letter"): after the
first `L` letters of each side, `f` has moved by (number of `0`s among them) · (side direction).
-/
theorem D4_walk (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hL : OnEdges n (LiftOK lab f))
    (hB : BdryOK lab n) (L : ℕ) (hLn : L ≤ n) :
    f ((L : ℤ), 0) = f (0, 0) +
        (∑ i ∈ range L, if lab ⟨(i : ℤ), 0, c0⟩ = l0 then (1 : ℤ) else 0) • ((1, 0) : V) ∧
    f ((n : ℤ) - L, L) = f ((n : ℤ), 0) +
        (∑ j ∈ range L, if lab ⟨(n : ℤ) - 1 - j, j, c2⟩ = l0 then (1 : ℤ) else 0) • ((-1, 1) : V) ∧
    f (0, (L : ℤ)) = f (0, 0) +
        (∑ j ∈ range L, if lab ⟨0, (j : ℤ), c1⟩ = l0 then (1 : ℤ) else 0) • ((0, 1) : V) := by
  refine ⟨?_, ?_, ?_⟩
  · have := walk_count (fun i : ℕ => f ((i : ℤ), 0)) (1, 0) (fun i => lab ⟨i, 0, c0⟩) L
      (fun i hi => by
        have := hL ⟨i, 0, c0⟩ (by simp) le_rfl (by push_cast; omega)
        simp only [LiftOK, Edge.head, Edge.tail, Edge.vec] at this
        push_cast; exact this) (fun i hi => (hB i (by omega)).1)
    simpa using this
  · have := walk_count (fun j : ℕ => f ((n : ℤ) - j, j)) (-1, 1)
      (fun j => lab ⟨(n : ℤ) - 1 - j, j, c2⟩) L
      (fun j hj => by
        have := hL ⟨(n : ℤ) - 1 - j, j, c2⟩ (by simp; omega) (by simp) (by simp)
        have e1 : (n : ℤ) - 1 - j + 1 = n - j := by ring
        have e2 : (n : ℤ) - ((j : ℤ) + 1) = n - 1 - j := by ring
        simp only [LiftOK, Edge.head, Edge.tail, Edge.vec] at this
        rw [e1] at this; push_cast; rw [e2]; exact this) (fun j hj => (hB j (by omega)).2.1)
    simpa using this
  · have := walk_count (fun j : ℕ => f (0, (j : ℤ))) (0, 1) (fun j => lab ⟨0, j, c1⟩) L
      (fun j hj => by
        have := hL ⟨0, j, c1⟩ le_rfl (by simp) (by simp; omega)
        simp only [LiftOK, Edge.head, Edge.tail, Edge.vec] at this
        push_cast; exact this) (fun j hj => (hB j (by omega)).2.2)
    simpa using this

/-! ## Lemma D, assembled -/

/-- D(4) with `m` = the letter count: `f_*(∂[T_n]) = ∂[f(0,0) + m₀·T₁]`, `m₀` = #`0`s on the
bottom. -/
theorem D4_count (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hT : PuzzleLift lab f n)
    (hB : BdryOK lab n) :
    fstar f (bd (Tn n)) = bd (deltaChain (f (0, 0)) (cntBot lab n l0).toNat) := by
  obtain ⟨k, hk, h⟩ := fstar_bd_Tn lab f n hT hB
  obtain ⟨hc, -, -⟩ := D2_of_lift lab f n (onEdges_of_tri n _ fun t ht => (hT t ht).1) hB
  have hkc : (k : ℤ) = cntBot lab n l0 := by
    rw [hc] at hk
    simp only [Prod.ext_iff, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul] at hk
    linarith [hk.1]
  rw [h, bd_delta, ← hkc, Int.toNat_natCast]

/-- **Lemma D** (tex `lem:D`(1)–(4); Knutson–Tao, as stated in Purbhoo arXiv:0705.1184 §2.4) for
every KT puzzle `ℓ` of size `n` (KT pieces on every unit triangle, `0/1` on the boundary), with
`L = jointL ℓ = (f₀, f₁)`:
1. `L` integrates the tex cochain on every unit edge; it has the `(d,0)/(0,d)` property on
   `0/1`-edges; every map with that property on the `0/1`-edges alone is `L` plus a constant on
   all vertices of `T_n`;
2. the three sides carry the same number of `0`s, and `#1 = n - #0` on each side;
3. `f₀` (resp. `f₁`) is a translation on `000` (resp. `111`) triangles and constant on `111`
   (resp. `000`) triangles; on every KT rhombus in `T_n`, both rhombus clauses hold;
4. walking each side, `f_k` advances by one unit (in the side's direction) at each `k`-letter
   and stays put at each `(1-k)`-letter; and `f_{k*}(∂[T_n]) = ∂[f_k(0,0) + m_k·T₁]` with
   `m_k` = the number of `k`s on the bottom side. -/
theorem lemmaD (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    -- D(1)
    (OnEdges n fun e =>
        jointL lab e.head = jointL lab e.tail + (coch lab e, coch (swapLab lab) e)) ∧
    OnEdges n (JointOK lab (jointL lab)) ∧
    (∀ L' : V → V × V, OnEdges n (JointOK lab L') → ∀ i j : ℕ, i + j ≤ n →
      L' ((i : ℤ), (j : ℤ)) = jointL lab ((i : ℤ), (j : ℤ)) + (L' (0, 0) - jointL lab (0, 0))) ∧
    -- D(2)
    (cntBot lab n l0 = cntHyp lab n l0 ∧ cntBot lab n l0 = cntLeft lab n l0 ∧
      cntBot lab n l1 = n - cntBot lab n l0 ∧ cntHyp lab n l1 = n - cntHyp lab n l0 ∧
      cntLeft lab n l1 = n - cntLeft lab n l0) ∧
    -- D(3)
    (∀ t, inDelta (0, 0) n t →
      ((Is000 lab t → ∃ v : V, ∀ p ∈ triVerts t, (jointL lab p).1 = p + v) ∧
        (Is111 lab t → ∀ p ∈ triVerts t, (jointL lab p).1 = (jointL lab (triVerts t).head!).1)) ∧
      ((Is111 lab t → ∃ v : V, ∀ p ∈ triVerts t, (jointL lab p).2 = p + v) ∧
        (Is000 lab t → ∀ p ∈ triVerts t, (jointL lab p).2 = (jointL lab (triVerts t).head!).2))) ∧
    (∀ (a b : ℤ) (k : Cls), inDelta (0, 0) n ⟨a, b, up⟩ → inDelta (0, 0) n (rhDown a b k) →
      lab ⟨a, b, k⟩ = l10 →
      RhClause lab (fun p => (jointL lab p).1) a b k l0 l1 ∧
        RhClause lab (fun p => (jointL lab p).2) a b k l1 l0) ∧
    -- D(4)
    (∀ L : ℕ, L ≤ n →
      (fun p => (jointL lab p).1) ((L : ℤ), 0) = (fun p => (jointL lab p).1) (0, 0) +
          (∑ i ∈ range L, if lab ⟨(i : ℤ), 0, c0⟩ = l0 then (1 : ℤ) else 0) • ((1, 0) : V) ∧
      (fun p => (jointL lab p).1) ((n : ℤ) - L, L) = (fun p => (jointL lab p).1) ((n : ℤ), 0) +
          (∑ j ∈ range L, if lab ⟨(n : ℤ) - 1 - j, j, c2⟩ = l0 then (1 : ℤ) else 0) •
            ((-1, 1) : V) ∧
      (fun p => (jointL lab p).1) (0, (L : ℤ)) = (fun p => (jointL lab p).1) (0, 0) +
          (∑ j ∈ range L, if lab ⟨0, (j : ℤ), c1⟩ = l0 then (1 : ℤ) else 0) • ((0, 1) : V)) ∧
    (∀ L : ℕ, L ≤ n →
      (fun p => (jointL lab p).2) ((L : ℤ), 0) = (fun p => (jointL lab p).2) (0, 0) +
          (∑ i ∈ range L, if lab ⟨(i : ℤ), 0, c0⟩ = l1 then (1 : ℤ) else 0) • ((1, 0) : V) ∧
      (fun p => (jointL lab p).2) ((n : ℤ) - L, L) = (fun p => (jointL lab p).2) ((n : ℤ), 0) +
          (∑ j ∈ range L, if lab ⟨(n : ℤ) - 1 - j, j, c2⟩ = l1 then (1 : ℤ) else 0) •
            ((-1, 1) : V) ∧
      (fun p => (jointL lab p).2) (0, (L : ℤ)) = (fun p => (jointL lab p).2) (0, 0) +
          (∑ j ∈ range L, if lab ⟨0, (j : ℤ), c1⟩ = l1 then (1 : ℤ) else 0) • ((0, 1) : V)) ∧
    fstar (fun p => (jointL lab p).1) (bd (Tn n)) =
      bd (deltaChain (jointL lab (0, 0)).1 (cntBot lab n l0).toNat) ∧
    fstar (fun p => (jointL lab p).2) (bd (Tn n)) =
      bd (deltaChain (jointL lab (0, 0)).2 (cntBot lab n l1).toNat) := by
  have hT0 := puzzleLift_of_KT lab n hK
  have hT1 := puzzleLift_of_mirror (swapLab lab) n (allMir_swap lab n hK)
  obtain ⟨hex, hJ⟩ := jointLift_of_KT lab n hK
  have hc : cntBot (swapLab lab) n l0 = cntBot lab n l1 := by simp [cntBot, swapLab]
  refine ⟨hex, hJ, fun L' hL' => jointLift_unique lab n hK L' _ hL' hJ, lemmaD2 lab n hK hB,
    fun t ht => ⟨D3_tri_k0 lab _ t (hT0 t ht).1, D3_tri_k1 lab _ t fun e he =>
      (liftOK1_iff lab _ e).2 ((hT1 t ht).1 e he)⟩,
    fun a b k hu hd h10 => rhombus_clause_joint lab n hK a b k hu hd h10,
    fun L hL => D4_walk lab _ n (onEdges_of_tri n _ fun t ht => (hT0 t ht).1) hB L hL,
    fun L hL => by
      simpa [swapLab] using D4_walk (swapLab lab) _ n
        (onEdges_of_tri n _ fun t ht => (hT1 t ht).1) (bdryOK_swap lab n hB) L hL,
    D4_count lab _ n hT0 hB, ?_⟩
  rw [← hc]
  exact D4_count (swapLab lab) _ n hT1 (bdryOK_swap lab n hB)

/-! ## Lesions -/

/-- **Mixed-rhombus lesion** (kernel). The up-triangle `(0,0)` is KT with its class-2 edge `10`;
the down-triangle `(0,0)` across that edge is a *mirror* piece, not KT. Then the two `0`-edges
of the rhombus have *different* classes (1 and 0: adjacent, not opposite), so the first part of
`RhClause` fails, and no `0`-lift exists on the four outer edges at all. Predicted in advance
(note `2026-11-27-lean-Q597-D.md`). The consistent mirror rhombus satisfies the clause
(`rhombus_clause_P` with `MirPiece`), as also predicted. -/
def mixedLab (e : Edge) : Lbl :=
  if e = ⟨0, 0, c2⟩ then l10 else if e = ⟨0, 0, c1⟩ ∨ e = ⟨0, 1, c0⟩ then l0 else l1

theorem mixed_rhombus_lesion :
    KTTri mixedLab ⟨0, 0, up⟩ ∧ PTri MirPiece mixedLab ⟨0, 0, down⟩ ∧
      ¬ KTTri mixedLab ⟨0, 0, down⟩ ∧
      mixedLab ⟨0, 0, c1⟩ = l0 ∧ mixedLab ⟨0, 1, c0⟩ = l0 ∧
      ¬ ∃ f : V → V, ∀ e ∈ rhOuter 0 0 c2, LiftOK mixedLab f e := by
  refine ⟨by simp only [KTTri]; decide, by simp only [PTri]; decide, by simp only [KTTri]; decide,
    by decide, by decide, ?_⟩
  rintro ⟨f, hf⟩
  simp only [rhOuter, List.forall_mem_cons] at hf
  obtain ⟨h1, h2, h3, h4, -⟩ := hf
  have a1 := h1.2 (by decide)
  have a2 := h2.1 (by decide)
  have a3 := h3.2 (by decide)
  have a4 := h4.1 (by decide)
  simp only [Edge.head, Edge.tail, Edge.vec] at a1 a2 a3 a4
  norm_num at a1 a2 a3 a4
  rw [a4, a2, ← a1] at a3
  have := congrArg Prod.fst a3
  simp at this

/-- **Uniqueness lesion** (kernel): the `1`-edges are needed. On the all-`1` puzzle of size 1
(a single KT `111`-triangle), the identity and the zero map both satisfy the `0`-edge half of
the lift condition (vacuously), yet do not differ by a constant. So `lift0_unique` with only
the `0`-edges constrained is false. -/
theorem uniq_lesion_drop1 :
    AllKT (fun _ => l1) 1 ∧
    (OnEdges 1 fun e => (fun _ : Edge => l1) e = l0 → id e.head = id e.tail + e.vec) ∧
    (OnEdges 1 fun e => (fun _ : Edge => l1) e = l0 → (0 : V) = 0 + e.vec) ∧
    id ((1 : ℤ), (0 : ℤ)) ≠ (0 : V) + (id ((0 : ℤ), (0 : ℤ)) - 0) := by
  refine ⟨?_, fun _ _ _ _ h => by simp at h, fun _ _ _ _ h => by simp at h, by decide⟩
  intro t ht
  rcases t with ⟨a, b, _ | _⟩ <;> simp [KTTri, KTPiece]

/-- **Uniqueness lesion, spanning pair** (kernel): in a KT `(10,0,1)` up-triangle, drop its
`0`-edge from the constrained family; the indicator of the vertex `(1,0)` is then constant along
every remaining `0/1`-edge but not constant. -/
theorem uniq_lesion_drop_spanning :
    KTPiece l10 l0 l1 = true ∧
    let D : V → ℤ := fun p => if p = (1, 0) then 1 else 0
    D (Edge.head ⟨0, 0, c1⟩) = D (Edge.tail ⟨0, 0, c1⟩) ∧ D (1, 0) ≠ D (0, 0) := by
  decide

end Q597G1
