/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finsupp.Basic

/-!
# Q597 Theorem G1, core: a finitely supported 2-chain on the triangular lattice with zero
boundary is zero

Paper proof: `projects/proofs/2026-11-24c2-Q597-D.tex`, §(G1) "the signed edge count",
Theorem `thm:G1`. Its last paragraph shows `N_0(t⁺) - N_0(t⁻)` equals the corresponding
difference for the indicator `[Δ_0]` across every unit edge `E`, and concludes
`N_0 = [Δ_0]` because "M_0 is finite, so N_0 = 0 far away" and the unit triangles are
connected through edges. This file formalises that concluding step:

* `bdry c e = c (posTri e) - c (negTri e)` is the boundary of a 2-chain at an edge
  (the two triangles on either side, with the counterclockwise orientation);
* `eq_zero_of_bdry_eq_zero`: finitely supported `c` with `∂c = 0` is `0`;
* `eq_of_bdry_eq`: equal boundaries ⇒ equal chains;
* `G1_of_signedEdgeCount`: Theorem G1's conclusion `N = [Δ]`, from the named hypothesis
  `hSEC : ∂N = ∂[Δ]` (the "by edges / by tiles" count, which uses Lemma D — not formalised
  here) and finiteness of `N` (it is a `Finsupp`).

The Knutson–Tao lift (Lemma D, after Purbhoo arXiv:0705.1184 §2.4) is *not* formalised; it is
only the source of the hypothesis `hSEC`.

Coordinates: lattice points `(a,b) ↔ a + bω`, `ω = e^{iπ/3}`. The up-triangle `(a,b)` has
corners `(a,b),(a+1,b),(a,b+1)`; the down-triangle `(a,b)` has corners
`(a+1,b),(a+1,b+1),(a,b+1)`. Edge `(a,b,k)` is `(a,b)→(a+1,b)` (`k=0`), `(a,b)→(a,b+1)`
(`k=1`), `(a+1,b)→(a,b+1)` (`k=2`), matching the tex's classes 0, 1, 2.
-/

namespace Q597G1

/-- Orientation of a unit triangle. -/
inductive Ori | up | down
  deriving DecidableEq, Repr

/-- A unit triangle of the triangular lattice. -/
structure Tri where
  a : ℤ
  b : ℤ
  o : Ori
  deriving DecidableEq, Repr

/-- Edge class (tex: class 0 is `±(1,0)`, class 1 is `±(0,1)`, class 2 is `±(-1,1)`). -/
inductive Cls | c0 | c1 | c2
  deriving DecidableEq, Repr

/-- A unit edge, with the reference orientation described in the module docstring. -/
structure Edge where
  a : ℤ
  b : ℤ
  k : Cls
  deriving DecidableEq, Repr

open Ori Cls

/-- Incidence number: the coefficient of edge `e` in the boundary of triangle `t`, the
triangle traversed counterclockwise.
Up `(a,b)`: `(a,b)→(a+1,b)` is `+e(a,b,0)`, `(a+1,b)→(a,b+1)` is `+e(a,b,2)`,
`(a,b+1)→(a,b)` is `-e(a,b,1)`.
Down `(a,b)`: `(a+1,b)→(a+1,b+1)` is `+e(a+1,b,1)`, `(a+1,b+1)→(a,b+1)` is `-e(a,b+1,0)`,
`(a,b+1)→(a+1,b)` is `-e(a,b,2)`. -/
def inc (t : Tri) (e : Edge) : ℤ :=
  match t.o with
  | up =>
      if e = ⟨t.a, t.b, c0⟩ then 1
      else if e = ⟨t.a, t.b, c2⟩ then 1
      else if e = ⟨t.a, t.b, c1⟩ then -1 else 0
  | down =>
      if e = ⟨t.a + 1, t.b, c1⟩ then 1
      else if e = ⟨t.a, t.b + 1, c0⟩ then -1
      else if e = ⟨t.a, t.b, c2⟩ then -1 else 0

/-- The triangle inducing `e` positively. -/
def posTri (e : Edge) : Tri :=
  match e.k with
  | c0 => ⟨e.a, e.b, up⟩
  | c1 => ⟨e.a - 1, e.b, down⟩
  | c2 => ⟨e.a, e.b, up⟩

/-- The triangle inducing `e` negatively. -/
def negTri (e : Edge) : Tri :=
  match e.k with
  | c0 => ⟨e.a, e.b - 1, down⟩
  | c1 => ⟨e.a, e.b, up⟩
  | c2 => ⟨e.a, e.b, down⟩

/-- Every edge has exactly two triangles, one inducing it with each sign. -/
theorem inc_eq (t : Tri) (e : Edge) :
    inc t e = (if t = posTri e then 1 else 0) - (if t = negTri e then 1 else 0) := by
  rcases t with ⟨a, b, _ | _⟩ <;> rcases e with ⟨a', b', _ | _ | _⟩ <;>
    simp only [inc, posTri, negTri] <;>
    split_ifs <;> simp_all

/-- Boundary of a finitely supported 2-chain: `∂c(e) = Σ_t c(t) · inc(t,e)`. -/
noncomputable def bdry (c : Tri →₀ ℤ) (e : Edge) : ℤ :=
  ∑ t ∈ c.support, c t * inc t e

/-- The two-term formula for the boundary, as a function on *arbitrary* (not necessarily
finitely supported) chains. Used for `#eval` and for the lesion. -/
def bdryFun (c : Tri → ℤ) (e : Edge) : ℤ := c (posTri e) - c (negTri e)

theorem bdry_eq_bdryFun (c : Tri →₀ ℤ) (e : Edge) : bdry c e = bdryFun c e := by
  classical
  unfold bdry bdryFun
  simp_rw [inc_eq, mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs <;> simp_all

/-- Linearity of the boundary. -/
theorem bdry_sub (c d : Tri →₀ ℤ) (e : Edge) : bdry (c - d) e = bdry c e - bdry d e := by
  simp only [bdry_eq_bdryFun, bdryFun, Finsupp.sub_apply]; ring

/-- A function on `ℤ × ℤ` invariant under both unit shifts is constant. -/
theorem const_of_shift (f : ℤ → ℤ → ℤ) (h1 : ∀ a b, f a b = f (a - 1) b)
    (h2 : ∀ a b, f a b = f a (b - 1)) : ∀ a b, f a b = f 0 0 := by
  have hA : ∀ a b, f a b = f 0 b := by
    intro a b
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [h1]; simpa using ih
    | pred n ih => rw [← ih, h1 (-(n : ℤ)) b]
  have hB : ∀ b, f 0 b = f 0 0 := by
    intro b
    induction b using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [h2]; simpa using ih
    | pred n ih => rw [← ih, h2 0 (-(n : ℤ))]
  intro a b; rw [hA, hB]

/-- Zero boundary (for an arbitrary function) means: constant on up-triangles, and each
down-triangle has the value of the up-triangle sharing its class-2 edge. -/
theorem const_of_bdryFun_eq_zero (c : Tri → ℤ) (h : ∀ e, bdryFun c e = 0) (t : Tri) :
    c t = c ⟨0, 0, up⟩ := by
  have h0 : ∀ a b, c ⟨a, b, up⟩ = c ⟨a, b - 1, down⟩ := fun a b => by
    have := h ⟨a, b, c0⟩; simp only [bdryFun, posTri, negTri] at this; omega
  have h1 : ∀ a b, c ⟨a, b, up⟩ = c ⟨a - 1, b, down⟩ := fun a b => by
    have := h ⟨a, b, c1⟩; simp only [bdryFun, posTri, negTri] at this; omega
  have h2 : ∀ a b, c ⟨a, b, up⟩ = c ⟨a, b, down⟩ := fun a b => by
    have := h ⟨a, b, c2⟩; simp only [bdryFun, posTri, negTri] at this; omega
  have hc := const_of_shift (fun a b => c ⟨a, b, up⟩)
    (fun a b => by simp only; rw [h1, ← h2]) (fun a b => by simp only; rw [h0, ← h2])
  rcases t with ⟨a, b, _ | _⟩
  · exact hc a b
  · rw [← h2]; exact hc a b

/-- **Core lemma.** A finitely supported 2-chain with zero boundary is zero. -/
theorem eq_zero_of_bdry_eq_zero (c : Tri →₀ ℤ) (h : ∀ e, bdry c e = 0) : c = 0 := by
  classical
  have hconst := const_of_bdryFun_eq_zero c (fun e => by rw [← bdry_eq_bdryFun]; exact h e)
  -- finiteness: some up-triangle lies outside the support
  obtain ⟨p, hp⟩ := Infinite.exists_notMem_finset
    (c.support.image fun t : Tri => (t.a, t.b))
  have hz : c ⟨p.1, p.2, up⟩ = 0 := by
    by_contra hne
    exact hp (Finset.mem_image.2 ⟨_, Finsupp.mem_support_iff.2 hne, rfl⟩)
  ext t
  rw [hconst t, Finsupp.coe_zero, Pi.zero_apply, ← hconst ⟨p.1, p.2, up⟩, hz]

/-- **Corollary.** Two finitely supported 2-chains with the same boundary are equal. -/
theorem eq_of_bdry_eq (c d : Tri →₀ ℤ) (h : ∀ e, bdry c e = bdry d e) : c = d :=
  sub_eq_zero.1 <| eq_zero_of_bdry_eq_zero _ fun e => by rw [bdry_sub, h, sub_self]

/-! ## The triangle `Δ = p + m·T₁` and Theorem G1's conclusion -/

/-- Membership of a unit triangle in `Δ(p, m) = p + m·T₁`, `T₁` with corners
`(0,0),(1,0),(0,1)`. Up `(a,b)` ⊆ Δ iff `a,b ≥ 0` and `a+b ≤ m-1` (relative to `p`);
down `(a,b)` ⊆ Δ iff `a,b ≥ 0` and `a+b ≤ m-2`. -/
def inDelta (p : ℤ × ℤ) (m : ℕ) (t : Tri) : Prop :=
  0 ≤ t.a - p.1 ∧ 0 ≤ t.b - p.2 ∧
    match t.o with
    | up => (t.a - p.1) + (t.b - p.2) + 1 ≤ m
    | down => (t.a - p.1) + (t.b - p.2) + 2 ≤ m

instance (p : ℤ × ℤ) (m : ℕ) (t : Tri) : Decidable (inDelta p m t) := by
  unfold inDelta; rcases t with ⟨a, b, _ | _⟩ <;> exact inferInstance

/-- The indicator `[Δ(p,m)]` as a finitely supported chain (support ⊆ a finite box). -/
noncomputable def deltaChain (p : ℤ × ℤ) (m : ℕ) : Tri →₀ ℤ :=
  Finsupp.ofSupportFinite (fun t => if inDelta p m t then 1 else 0) <| by
    classical
    let box : Finset Tri :=
      ((Finset.Icc p.1 (p.1 + m) ×ˢ Finset.Icc p.2 (p.2 + m)) ×ˢ
          ({up, down} : Finset Ori)).image fun q => ⟨q.1.1, q.1.2, q.2⟩
    refine box.finite_toSet.subset ?_
    intro t ht
    rcases t with ⟨a, b, o⟩
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not, inDelta] at ht
    obtain ⟨ha, hb, hs⟩ := ht
    simp only [box, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_product,
      Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨((a, b), o), ?_, rfl⟩
    cases o <;> simp at hs ⊢ <;> omega

theorem deltaChain_apply (p : ℤ × ℤ) (m : ℕ) (t : Tri) :
    deltaChain p m t = if inDelta p m t then 1 else 0 := rfl

/-- **Theorem G1 (conclusion), from the signed edge count.**
`N` is the lift-count chain `t ↦ N_k(t)` (finitely supported because `M_0` is finite).
`hSEC` is the output of the tex's "by edges / by tiles" count:
`N(t⁺) - N(t⁻) = [Δ](t⁺) - [Δ](t⁻)` across every unit edge, i.e. `∂N = ∂[Δ]`. It rests on
Lemma D (Knutson–Tao, as stated in Purbhoo arXiv:0705.1184 §2.4), which is not formalised.
Conclusion: `N_k(t) = 1` on `Δ_k` and `0` off it. -/
theorem G1_of_signedEdgeCount (N : Tri →₀ ℤ) (p : ℤ × ℤ) (m : ℕ)
    (hSEC : ∀ e, bdry N e = bdry (deltaChain p m) e) (t : Tri) :
    N t = if inDelta p m t then 1 else 0 := by
  rw [eq_of_bdry_eq N (deltaChain p m) hSEC, deltaChain_apply]

/-! ## Lesion: finite support is load-bearing -/

/-- The all-ones chain (infinite support) has zero boundary and is nonzero. So
`eq_zero_of_bdry_eq_zero` fails for functions that are not finitely supported. -/
theorem lesion_allOnes : (∀ e, bdryFun (fun _ => (1 : ℤ)) e = 0) ∧
    (fun _ : Tri => (1 : ℤ)) ≠ 0 := by
  refine ⟨fun e => by simp [bdryFun], fun h => ?_⟩
  have := congrFun h ⟨0, 0, up⟩
  simp at this

end Q597G1
