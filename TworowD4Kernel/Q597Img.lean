/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.Q597D

/-!
# Q597 Corollary img: every vertex image lies in `Δ_k`

Paper proof: `projects/proofs/2026-11-24c2-Q597-D.tex`, Corollary `cor:img` (l.90–95), resting on
Theorem G1 (`G1_KT_count`, `G1_KT_k1_count`) and Lemma D (Knutson–Tao, as stated in Purbhoo
arXiv:0705.1184 §2.4; `Q597G1.lemmaD`).

The tex's walk ("leave the rhombus by its other `0`-edge; the `ν`-coordinate increases strictly,
so the edges never repeat, contradicting finiteness") is formalised as a measure: among the
`0`-edges of `T_n` whose image is not in `Δ₀`, the walk step (`walk_step`) produces another one of
the same class, the same image, and a strictly larger value of the class functional `νfun`,
which is bounded by `n` on `T_n`. Strong induction on `n - νfun` closes it (`edge_img_core`).
-/

namespace Q597G1

open Ori Cls Lbl Finset

/-- A lattice point of the triangle `Δ(c, m) = c + m·T₁`. -/
def PtIn (c : V) (m : ℕ) (x : V) : Prop :=
  0 ≤ x.1 - c.1 ∧ 0 ≤ x.2 - c.2 ∧ (x.1 - c.1) + (x.2 - c.2) ≤ m

/-- The image of an edge under `f` lies in `Δ(c,m)` (both endpoints; `Δ` is convex). -/
def EdgeIn (f : V → V) (c : V) (m : ℕ) (e : Edge) : Prop :=
  PtIn c m (f e.tail) ∧ PtIn c m (f e.head)

/-- Coordinates of a unit edge of `T_n` (the domain of `OnEdges`). -/
def InTn (n : ℕ) (e : Edge) : Prop := 0 ≤ e.a ∧ 0 ≤ e.b ∧ e.a + e.b + 1 ≤ n

/-- Boundary edges of `T_n`: bottom, left side, hypotenuse. -/
def IsBdry (n : ℕ) (e : Edge) : Prop :=
  (e.k = c0 ∧ e.b = 0) ∨ (e.k = c1 ∧ e.a = 0) ∨ (e.k = c2 ∧ e.a + e.b + 1 = n)

/-- The tex's `ν`-coordinate for an edge of each class: `ν` is the normal of the edge pointing
into `posTri e` (class 0: up, `b`; class 1: left, `-a`; class 2: down-left, `-(a+b)`). -/
def νfun (e : Edge) : ℤ :=
  match e.k with
  | c0 => e.b | c1 => -e.a | c2 => -(e.a + e.b)

theorem νfun_le (n : ℕ) (e : Edge) (h : InTn n e) : νfun e ≤ n := by
  obtain ⟨a, b, k⟩ := e; simp only [InTn] at h; cases k <;> simp [νfun] <;> omega

/-- An edge of a triangle of `T_n` has `T_n` coordinates. -/
theorem inTn_of_tri (n : ℕ) (t : Tri) (ht : inDelta (0, 0) n t) (e : Edge) (he : e ∈ triEdges t) :
    InTn n e := by
  obtain ⟨a, b, o⟩ := t
  cases o <;> simp only [inDelta, triEdges, List.mem_cons, List.not_mem_nil, or_false] at ht he <;>
    simp at ht <;> rcases he with rfl | rfl | rfl <;> simp [InTn] <;> omega

/-- A boundary edge of a puzzle with `0/1` boundary is not a `10`-edge. -/
theorem bdry_not10 (lab : Edge → Lbl) (n : ℕ) (hB : BdryOK lab n) (e : Edge) (he : InTn n e)
    (hb : IsBdry n e) : lab e ≠ l10 := by
  obtain ⟨a, b, k⟩ := e
  simp only [InTn, IsBdry] at he hb
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hab⟩
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = i := ⟨a.toNat, by omega⟩
    rcases (hB i (by omega)).1 with h | h <;> rw [h] <;> decide
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, b = i := ⟨b.toNat, by omega⟩
    rcases (hB i (by omega)).2.2 with h | h <;> rw [h] <;> decide
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, b = i := ⟨b.toNat, by omega⟩
    have : a = (n : ℤ) - 1 - i := by omega
    subst this
    rcases (hB i (by omega)).2.1 with h | h <;> rw [h] <;> decide

/-- An interior edge of `T_n` has both of its triangles in `T_n`. -/
theorem tris_of_interior (n : ℕ) (e : Edge) (he : InTn n e) (hb : ¬ IsBdry n e) :
    inDelta (0, 0) n (posTri e) ∧ inDelta (0, 0) n (negTri e) := by
  obtain ⟨a, b, k⟩ := e
  simp only [InTn, IsBdry] at he hb
  cases k <;> simp [posTri, negTri, inDelta] at hb ⊢ <;> omega

/-- `N₀(f τ) ≥ 1` for every `000`-triangle `τ` of `T_n`. -/
theorem nchain_pos (lab : Edge → Lbl) (f : V → V) (n : ℕ) (t : Tri) (ht : inDelta (0, 0) n t)
    (h0 : Is000 lab t) : 1 ≤ Nchain lab f n (imgTri f t) := by
  classical
  unfold Nchain
  rw [Finsupp.finsetSum_apply]
  have hmem : t ∈ (Tn n).support.filter (Is000 lab) := by
    rw [Finset.mem_filter, mem_support_Tn]; exact ⟨ht, h0⟩
  calc (1 : ℤ) = Finsupp.single (imgTri f t) 1 (imgTri f t) := by simp
    _ ≤ _ := Finset.single_le_sum (f := fun s => Finsupp.single (imgTri f s) (1 : ℤ) (imgTri f t))
        (fun s _ => by simp only [Finsupp.single_apply]; split_ifs <;> norm_num) hmem

/-- A `000`-triangle whose image triangle lies in `Δ(c,m)` has all its edges mapped into it. -/
theorem tri_good (lab : Edge → Lbl) (f : V → V) (c : V) (m : ℕ) (t : Tri)
    (hL : ∀ e ∈ triEdges t, LiftOK lab f e) (h0 : Is000 lab t) (hD : inDelta c m (imgTri f t)) :
    ∀ e ∈ triEdges t, EdgeIn f c m e := by
  obtain ⟨a, b, o⟩ := t
  cases o
  · have L1 := (hL ⟨a, b, c0⟩ (by simp [triEdges])).1 (h0 _ (by simp [triEdges]))
    have L2 := (hL ⟨a, b, c1⟩ (by simp [triEdges])).1 (h0 _ (by simp [triEdges]))
    simp only [Edge.head, Edge.tail, Edge.vec] at L1 L2
    simp only [imgTri, inDelta] at hD
    intro e he
    simp only [triEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [EdgeIn, PtIn, Edge.head, Edge.tail, L1, L2, Prod.fst_add, Prod.snd_add] <;>
      omega
  · have L1 := (hL ⟨a + 1, b, c1⟩ (by simp [triEdges])).1 (h0 _ (by simp [triEdges]))
    have L2 := (hL ⟨a, b, c2⟩ (by simp [triEdges])).1 (h0 _ (by simp [triEdges]))
    simp only [Edge.head, Edge.tail, Edge.vec] at L1 L2
    simp only [imgTri, inDelta] at hD
    intro e he
    simp only [triEdges, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl <;>
      simp only [EdgeIn, PtIn, Edge.head, Edge.tail, L1, L2, Prod.fst_add, Prod.snd_add] at hD ⊢ <;>
      omega

/-- A `KT` or mirror piece with a `0`-edge that is not `000` has a `10`-edge. -/
theorem piece_has10 (P : Lbl → Lbl → Lbl → Bool) (hP : P = KTPiece ∨ P = MirPiece) :
    ∀ x y z : Lbl, P x y z = true → (x = l0 ∨ y = l0 ∨ z = l0) → ¬ (x = l0 ∧ y = l0 ∧ z = l0) →
      (x = l10 ∨ y = l10 ∨ z = l10) := by
  rcases hP with rfl | rfl <;> decide

/-- In a duplicate-free list with exactly two `p`-elements, each one has a partner. -/
theorem pick_other {α : Type*} [DecidableEq α] (L : List α) (hL : L.Nodup) (p : α → Prop)
    [DecidablePred p] (hc : L.countP (fun x => decide (p x)) = 2) (e : α) (he : e ∈ L) (_hp : p e) :
    ∃ e' ∈ L, e' ≠ e ∧ p e' := by
  by_contra h
  push Not at h
  have h1 : L.countP (fun x => decide (p x)) ≤ L.countP (fun x => decide (x = e)) :=
    List.countP_mono_left fun x hx hpx => by
      by_contra hne
      exact h x hx (by simpa using hne) (by simpa using hpx)
  have h2 : L.countP (fun x => decide (x = e)) = L.count e := by
    rw [List.count_eq_countP]; congr 1
  rw [h2, List.count_eq_one_of_mem hL he] at h1
  omega

theorem mem_posTri (e : Edge) : e ∈ triEdges (posTri e) := by
  obtain ⟨a, b, k⟩ := e; cases k <;> simp [posTri, triEdges]

theorem rhOuter_nodup (a b : ℤ) (k : Cls) : (rhOuter a b k).Nodup := by
  cases k <;> simp [rhOuter] <;> omega

/-- The rhombus half of the walk step: on a rhombus of `T_n`, a `0`-edge `e` has a partner
`0`-edge `e'` (same class, same image), and the finite geometric fact `hgeo` says the partner is
further along `ν`. -/
theorem rh_partner (P : Lbl → Lbl → Lbl → Bool) (hP : P = KTPiece ∨ P = MirPiece)
    (lab : Edge → Lbl) (f : V → V) (n : ℕ) (c : V) (m : ℕ) (hA : AllP P lab n)
    (hT : PuzzleLift lab f n) (a b : ℤ) (k : Cls) (hu : inDelta (0, 0) n ⟨a, b, up⟩)
    (hd : inDelta (0, 0) n (rhDown a b k)) (h10 : lab ⟨a, b, k⟩ = l10) (e : Edge)
    (he : e ∈ rhOuter a b k) (h0 : lab e = l0)
    (hgeo : ∀ e' ∈ rhOuter a b k, e'.k = e.k → e' ≠ e → νfun e < νfun e') :
    ∃ e', InTn n e' ∧ lab e' = l0 ∧ (EdgeIn f c m e' ↔ EdgeIn f c m e) ∧ νfun e < νfun e' := by
  have hR := rhombus_clause_P P hP lab f a b k h10 (hA _ hu) (hA _ hd) fun x hx =>
    (rhOuter_sub a b k x hx).elim (fun h => (hT _ hu).1 x h) (fun h => (hT _ hd).1 x h)
  obtain ⟨hsame, -, -, hcnt, -⟩ := hR
  obtain ⟨e', he', hne, h0'⟩ := pick_other _ (rhOuter_nodup a b k) (fun x => lab x = l0) hcnt e he h0
  obtain ⟨hk, ht, hh⟩ := hsame e' he' e he h0' h0
  refine ⟨e', ?_, h0', by simp [EdgeIn, ht, hh], hgeo e' he' hk hne⟩
  rcases rhOuter_sub a b k e' he' with h | h
  · exact inTn_of_tri n _ hu e' h
  · exact inTn_of_tri n _ hd e' h

/-- A `10`-edge with `T_n` coordinates is interior, so both its triangles are in `T_n`. -/
theorem tris_of_10 (lab : Edge → Lbl) (n : ℕ) (hB : BdryOK lab n) (g : Edge) (hg : InTn n g)
    (h10 : lab g = l10) : inDelta (0, 0) n (posTri g) ∧ inDelta (0, 0) n (negTri g) :=
  tris_of_interior n g hg fun hb => bdry_not10 lab n hB g hg hb h10

/-- **The walk step** (tex Cor img, proof, sentences 3–6). A `0`-edge `e` of `T_n` whose image is
not in `Δ(c,m)` is interior (boundary `0`-edges map into `∂Δ`, hypothesis `hBd`); the tile on
its `ν`-side is not `000` (its image triangle would be in `Δ` by G1, `hN`), so it is half of a
rhombus, which is in `T_n`; leaving by the other `0`-edge `e'` gives a `0`-edge of the same
class with the same image and a larger `ν`-coordinate. -/
theorem walk_step (P : Lbl → Lbl → Lbl → Bool) (hP : P = KTPiece ∨ P = MirPiece)
    (lab : Edge → Lbl) (f : V → V) (n : ℕ) (c : V) (m : ℕ) (hA : AllP P lab n)
    (hT : PuzzleLift lab f n) (hB : BdryOK lab n)
    (hN : ∀ t, Nchain lab f n t = if inDelta c m t then 1 else 0)
    (hBd : ∀ e, InTn n e → IsBdry n e → lab e = l0 → EdgeIn f c m e)
    (e : Edge) (he : InTn n e) (h0 : lab e = l0) (hbad : ¬ EdgeIn f c m e) :
    ∃ e', InTn n e' ∧ lab e' = l0 ∧ (EdgeIn f c m e' ↔ EdgeIn f c m e) ∧ νfun e < νfun e' := by
  have hnb : ¬ IsBdry n e := fun hb => hbad (hBd e he hb h0)
  have hp := (tris_of_interior n e he hnb).1
  by_cases h000 : Is000 lab (posTri e)
  · exfalso
    have h1 := nchain_pos lab f n _ hp h000
    rw [hN] at h1
    have hD : inDelta c m (imgTri f (posTri e)) := by
      by_contra hc; rw [if_neg hc] at h1; omega
    exact hbad (tri_good lab f c m _ (hT _ hp).1 h000 hD e (mem_posTri e))
  have hpc := hA _ hp
  obtain ⟨a, b, k⟩ := e
  simp only [InTn] at he
  cases k
  · -- class 0: posTri = up(a,b), edges c0 (= e), c2, c1
    simp only [posTri, PTri, Is000, triEdges, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpc h000 h0 hp
    rcases piece_has10 P hP _ _ _ hpc (Or.inl h0) (by tauto) with h | h | h
    · rw [h0] at h; cases h
    · have hd := (tris_of_10 lab n hB ⟨a, b, c2⟩ (by simp [InTn]; omega) h).2
      exact rh_partner P hP lab f n c m hA hT a b c2 hp hd h _ (by simp [rhOuter]) h0
        (fun e' he' hk hne => by
          simp only [rhOuter, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl | rfl | rfl <;> simp_all [νfun])
    · have hd := (tris_of_10 lab n hB ⟨a, b, c1⟩ (by simp [InTn]; omega) h).1
      exact rh_partner P hP lab f n c m hA hT a b c1 hp hd h _ (by simp [rhOuter]) h0
        (fun e' he' hk hne => by
          simp only [rhOuter, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl | rfl | rfl <;> simp_all [νfun])
  · -- class 1: posTri = down(a-1,b), edges c1 (= e), ⟨a-1,b+1,c0⟩, ⟨a-1,b,c2⟩
    simp only [posTri, PTri, Is000, triEdges, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq, sub_add_cancel] at hpc h000 h0 hp
    rcases piece_has10 P hP _ _ _ hpc (Or.inl h0) (by tauto) with h | h | h
    · rw [h0] at h; cases h
    · have hu := (tris_of_10 lab n hB ⟨a - 1, b + 1, c0⟩ (by simp [InTn, inDelta] at hp ⊢; omega) h).1
      have hd : inDelta (0, 0) n (rhDown (a - 1) (b + 1) c0) := by
        simpa [rhDown] using hp
      exact rh_partner P hP lab f n c m hA hT (a - 1) (b + 1) c0 hu hd h _
        (by simp [rhOuter]) h0
        (fun e' he' hk hne => by
          simp only [rhOuter, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl | rfl | rfl <;> simp_all [νfun])
    · have hu := (tris_of_10 lab n hB ⟨a - 1, b, c2⟩ (by simp [InTn, inDelta] at hp ⊢; omega) h).1
      exact rh_partner P hP lab f n c m hA hT (a - 1) b c2 hu hp h _
        (by simp [rhOuter]) h0
        (fun e' he' hk hne => by
          simp only [rhOuter, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl | rfl | rfl <;> simp_all [νfun])
  · -- class 2: posTri = up(a,b), edges c0, c2 (= e), c1
    simp only [posTri, PTri, Is000, triEdges, List.mem_cons, List.not_mem_nil, or_false,
      forall_eq_or_imp, forall_eq] at hpc h000 h0 hp
    rcases piece_has10 P hP _ _ _ hpc (Or.inr (Or.inl h0)) (by tauto) with h | h | h
    · have hd := (tris_of_10 lab n hB ⟨a, b, c0⟩ (by simp [InTn]; omega) h).2
      exact rh_partner P hP lab f n c m hA hT a b c0 hp hd h _ (by simp [rhOuter]) h0
        (fun e' he' hk hne => by
          simp only [rhOuter, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl | rfl | rfl <;> simp_all [νfun])
    · rw [h0] at h; cases h
    · have hd := (tris_of_10 lab n hB ⟨a, b, c1⟩ (by simp [InTn]; omega) h).1
      exact rh_partner P hP lab f n c m hA hT a b c1 hp hd h _ (by simp [rhOuter]) h0
        (fun e' he' hk hne => by
          simp only [rhOuter, List.mem_cons, List.not_mem_nil, or_false] at he'
          rcases he' with rfl | rfl | rfl | rfl <;> simp_all [νfun])

/-! ## The measure: the walk cannot go on for ever -/

/-- **Every `0`-edge of `T_n` maps into `Δ(c,m)`** (tex Cor img, first sentence, from the
walk). Strong induction on `n - νfun e`, which the walk step strictly decreases (`νfun_le`). -/
theorem edge_img_core (P : Lbl → Lbl → Lbl → Bool) (hP : P = KTPiece ∨ P = MirPiece)
    (lab : Edge → Lbl) (f : V → V) (n : ℕ) (c : V) (m : ℕ) (hA : AllP P lab n)
    (hT : PuzzleLift lab f n) (hB : BdryOK lab n)
    (hN : ∀ t, Nchain lab f n t = if inDelta c m t then 1 else 0)
    (hBd : ∀ e, InTn n e → IsBdry n e → lab e = l0 → EdgeIn f c m e) :
    ∀ e, InTn n e → lab e = l0 → EdgeIn f c m e := by
  suffices H : ∀ d : ℕ, ∀ e, ((n : ℤ) - νfun e).toNat = d → InTn n e → lab e = l0 →
      EdgeIn f c m e from fun e => H _ e rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro e hd he h0
    by_contra hbad
    obtain ⟨e', he', h0', hiff, hlt⟩ := walk_step P hP lab f n c m hA hT hB hN hBd e he h0 hbad
    have h1 := νfun_le n e he
    have h2 := νfun_le n e' he'
    exact hbad (hiff.1 (ih _ (by omega) e' rfl he' h0'))

/-! ## The boundary: Lemma D(4) puts boundary `0`-edges on `∂Δ` -/

theorem psum_bounds (w : ℕ → Prop) [DecidablePred w] (L n : ℕ) (h : L ≤ n) :
    0 ≤ (∑ i ∈ range L, if w i then (1 : ℤ) else 0) ∧
      (∑ i ∈ range L, if w i then (1 : ℤ) else 0) ≤ ∑ i ∈ range n, if w i then (1 : ℤ) else 0 :=
  ⟨sum_nonneg fun _ _ => by split_ifs <;> norm_num,
    sum_le_sum_of_subset_of_nonneg (range_subset_range.2 h) fun _ _ _ => by
      split_ifs <;> norm_num⟩

/-- **Boundary `0`-edges map into `Δ₀ = f(0,0) + m₀T₁`** (tex Lemma D(4), via `D4_walk` and
`D2_of_lift`): `m₀` = the number of `0`s on the bottom. -/
theorem bdry_img (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hL : OnEdges n (LiftOK lab f))
    (hB : BdryOK lab n) :
    ∀ e, InTn n e → IsBdry n e → EdgeIn f (f (0, 0)) (cntBot lab n l0).toNat e := by
  obtain ⟨hn, hh, hl⟩ := D2_of_lift lab f n hL hB
  have hpos : 0 ≤ cntBot lab n l0 := sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hm : ((cntBot lab n l0).toNat : ℤ) = cntBot lab n l0 := Int.toNat_of_nonneg hpos
  intro ⟨a, b, k⟩ he hb
  simp only [InTn, IsBdry] at he hb
  rcases hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hab⟩
  · obtain ⟨i, rfl⟩ : ∃ i : ℕ, a = i := ⟨a.toNat, by omega⟩
    have w0 := (D4_walk lab f n hL hB i (by omega)).1
    have w1 := (D4_walk lab f n hL hB (i + 1) (by omega)).1
    have b0 := psum_bounds (fun i => lab ⟨(i : ℤ), 0, c0⟩ = l0) i n (by omega)
    have b1 := psum_bounds (fun i => lab ⟨(i : ℤ), 0, c0⟩ = l0) (i + 1) n (by omega)
    beta_reduce at b0 b1
    simp only [EdgeIn, PtIn, Edge.head, Edge.tail]
    push_cast at w1
    rw [w0, w1]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
    rw [hm]
    simp only [cntBot, cntHyp, cntLeft] at hh hl ⊢
    omega
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, b = j := ⟨b.toNat, by omega⟩
    have w0 := (D4_walk lab f n hL hB j (by omega)).2.2
    have w1 := (D4_walk lab f n hL hB (j + 1) (by omega)).2.2
    have b0 := psum_bounds (fun j => lab ⟨0, (j : ℤ), c1⟩ = l0) j n (by omega)
    have b1 := psum_bounds (fun j => lab ⟨0, (j : ℤ), c1⟩ = l0) (j + 1) n (by omega)
    beta_reduce at b0 b1
    simp only [EdgeIn, PtIn, Edge.head, Edge.tail]
    push_cast at w1
    rw [w0, w1]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
    rw [hm]
    simp only [cntBot, cntHyp, cntLeft] at hh hl ⊢
    omega
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, b = j := ⟨b.toNat, by omega⟩
    have w0 := (D4_walk lab f n hL hB j (by omega)).2.1
    have w1 := (D4_walk lab f n hL hB (j + 1) (by omega)).2.1
    have b0 := psum_bounds (fun j => lab ⟨(n : ℤ) - 1 - j, j, c2⟩ = l0) j n (by omega)
    have b1 := psum_bounds (fun j => lab ⟨(n : ℤ) - 1 - j, j, c2⟩ = l0) (j + 1) n (by omega)
    beta_reduce at b0 b1
    have et : (a + 1, (j : ℤ)) = ((n : ℤ) - j, (j : ℤ)) := by ext <;> simp <;> omega
    have eh : (a, (j : ℤ) + 1) = ((n : ℤ) - ((j + 1 : ℕ) : ℤ), ((j + 1 : ℕ) : ℤ)) := by
      ext <;> simp <;> omega
    simp only [EdgeIn, PtIn, Edge.head, Edge.tail]
    rw [et, eh, w0, w1, hn]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul]
    rw [hm]
    simp only [cntBot, cntHyp, cntLeft] at hh hl ⊢
    omega

/-! ## From edges to vertices: the `0/1`-graph is connected -/

/-- If membership in `Δ` is unchanged along every `0/1`-edge of a KT puzzle, every vertex of
`T_n` has the status of `(0,0)` (Lemma D(1): the `0/1`-graph is connected). -/
theorem vert_img (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (f : V → V) (c : V) (m : ℕ)
    (h00 : PtIn c m (f (0, 0)))
    (hE : OnEdges n fun e => lab e ≠ l10 → (PtIn c m (f e.head) ↔ PtIn c m (f e.tail))) :
    ∀ i j : ℕ, i + j ≤ n → PtIn c m (f ((i : ℤ), (j : ℤ))) := by
  intro i j hij
  have := const_of_edges (fun p => PtIn c m (f p)) n
    (edges_of_nonten lab n hK (fun p => PtIn c m (f p))
      fun e ha hb hn h => propext (hE e ha hb hn h)) i j hij
  simp only at this
  rw [this]; exact h00

theorem ptIn_self (c : V) (m : ℕ) : PtIn c m c := by simp [PtIn]

/-! ## The nest-rhombus clause -/

/-- **The three sides of `Δ₀`** (tex Cor img, last sentence; Lemma D(4)): from each corner
`f(p_s)` of `Δ₀ = f(0,0) + m₀T₁`, the points `f(p_s) + a·D_s`, `0 ≤ a ≤ m₀`, are in `Δ₀`, for the
three sides `(p_s, D_s) = ((0,0),(1,0)), ((n,0),(-1,1)), ((0,n),(0,-1))` of `T_n`. -/
theorem nest_img (lab : Edge → Lbl) (f : V → V) (n : ℕ) (hL : OnEdges n (LiftOK lab f))
    (hB : BdryOK lab n) (a : ℕ) (ha : a ≤ (cntBot lab n l0).toNat) :
    PtIn (f (0, 0)) (cntBot lab n l0).toNat (f (0, 0) + (a : ℤ) • ((1, 0) : V)) ∧
    PtIn (f (0, 0)) (cntBot lab n l0).toNat (f ((n : ℤ), 0) + (a : ℤ) • ((-1, 1) : V)) ∧
    PtIn (f (0, 0)) (cntBot lab n l0).toNat (f (0, (n : ℤ)) + (a : ℤ) • ((0, -1) : V)) := by
  obtain ⟨hn, -, hl⟩ := D2_of_lift lab f n hL hB
  have hpos : 0 ≤ cntBot lab n l0 := sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hm : ((cntBot lab n l0).toNat : ℤ) = cntBot lab n l0 := Int.toNat_of_nonneg hpos
  have h0n := (D4_walk lab f n hL hB n le_rfl).2.2
  have hl' : (∑ j ∈ range n, if lab ⟨0, (j : ℤ), c1⟩ = l0 then (1 : ℤ) else 0) =
      cntBot lab n l0 := by rw [hl]; rfl
  rw [hl'] at h0n
  have ha' : (a : ℤ) ≤ cntBot lab n l0 := by omega
  simp only [PtIn, hn, h0n, Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_eq_mul, hm]
  omega

/-! ## Corollary img -/

theorem swap_eq_l0 (lab : Edge → Lbl) (e : Edge) : swapLab lab e = l0 ↔ lab e = l1 := by
  simp only [swapLab]; cases lab e <;> decide

theorem swap_eq_l1 (lab : Edge → Lbl) (e : Edge) : swapLab lab e = l1 ↔ lab e = l0 := by
  simp only [swapLab]; cases lab e <;> decide

/-- **Corollary img, `k = 0`** (tex `cor:img`; Knutson–Tao as stated in Purbhoo arXiv:0705.1184
§2.4 for Lemma D): for a KT puzzle with `f₀ = π₀ ∘ L` and `Δ₀ = f₀(0,0) + m₀T₁`
(`m₀` = number of `0`s on the bottom), every `0`-edge of `T_n` maps onto a unit edge in `Δ₀`,
and `f₀(p) ∈ Δ₀` for every vertex `p` of `T_n`. -/
theorem corImg_k0 (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    (∀ e, InTn n e → lab e = l0 →
      EdgeIn (fun p => (jointL lab p).1) (jointL lab (0, 0)).1 (cntBot lab n l0).toNat e) ∧
    (∀ i j : ℕ, i + j ≤ n →
      PtIn (jointL lab (0, 0)).1 (cntBot lab n l0).toNat (jointL lab ((i : ℤ), (j : ℤ))).1) := by
  have hT0 := puzzleLift_of_KT lab n hK
  have hL := onEdges_of_tri n _ fun t ht => (hT0 t ht).1
  have hE := edge_img_core KTPiece (Or.inl rfl) lab (integ (coch lab)) n _ _ hK hT0 hB
    (G1_KT_count lab n hK hB) fun e he hb _ => bdry_img lab _ n hL hB e he hb
  refine ⟨hE, vert_img lab n hK (integ (coch lab)) _ _ (ptIn_self _ _) ?_⟩
  intro e ha hb hn h10
  have hLe := hL e ha hb hn
  cases hlab : lab e
  · obtain ⟨h1, h2⟩ := hE e ⟨ha, hb, hn⟩ hlab
    exact iff_of_true h2 h1
  · rw [hLe.2 hlab]
  · exact absurd hlab h10

/-- **Corollary img, `k = 1`**: with `f₁ = π₁ ∘ L` and `Δ₁ = f₁(0,0) + m₁T₁` (`m₁` = number of
`1`s on the bottom), every `1`-edge maps onto a unit edge in `Δ₁` and `f₁(p) ∈ Δ₁` for every
vertex. The edge half is `edge_img_core` for mirror pieces on `swapLab ℓ`. -/
theorem corImg_k1 (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    (∀ e, InTn n e → lab e = l1 →
      EdgeIn (fun p => (jointL lab p).2) (jointL lab (0, 0)).2 (cntBot lab n l1).toNat e) ∧
    (∀ i j : ℕ, i + j ≤ n →
      PtIn (jointL lab (0, 0)).2 (cntBot lab n l1).toNat (jointL lab ((i : ℤ), (j : ℤ))).2) := by
  have hT1 := puzzleLift_of_mirror (swapLab lab) n (allMir_swap lab n hK)
  have hL := onEdges_of_tri n _ fun t ht => (hT1 t ht).1
  have hB' := bdryOK_swap lab n hB
  have hc : cntBot (swapLab lab) n l0 = cntBot lab n l1 := by simp [cntBot, swapLab]
  have hN : ∀ t, Nchain (swapLab lab) (integ (coch (swapLab lab))) n t =
      if inDelta (integ (coch (swapLab lab)) (0, 0)) (cntBot lab n l1).toNat t then 1 else 0 :=
    fun t => by rw [← nchain1_eq]; exact G1_KT_k1_count lab n hK hB t
  have hBd : ∀ e, InTn n e → IsBdry n e → swapLab lab e = l0 →
      EdgeIn (integ (coch (swapLab lab))) (integ (coch (swapLab lab)) (0, 0))
        (cntBot lab n l1).toNat e := fun e he hb _ => by
    rw [← hc]; exact bdry_img (swapLab lab) _ n hL hB' e he hb
  have hE := edge_img_core MirPiece (Or.inr rfl) (swapLab lab) (integ (coch (swapLab lab))) n _ _
    (allMir_swap lab n hK) hT1 hB' hN hBd
  refine ⟨fun e he h1 => hE e he ((swap_eq_l0 lab e).2 h1),
    vert_img lab n hK (integ (coch (swapLab lab))) _ _ (ptIn_self _ _) ?_⟩
  intro e ha hb hn h10
  have hLe := hL e ha hb hn
  cases hlab : lab e
  · rw [hLe.2 ((swap_eq_l1 lab e).2 hlab)]
  · obtain ⟨h1, h2⟩ := hE e ⟨ha, hb, hn⟩ ((swap_eq_l0 lab e).2 hlab)
    exact iff_of_true h2 h1
  · exact absurd hlab h10

/-- The three sides of `T_n` as (start vertex `p_s`, direction `D`), counterclockwise. -/
def sides (n : ℕ) : List (V × V) :=
  [((0, 0), (1, 0)), (((n : ℤ), 0), (-1, 1)), ((0, (n : ℤ)), (0, -1))]

/-- **Corollary img** (tex `cor:img`, l.90–95, all three clauses; Lemma D and Theorem G1 from
Knutson–Tao as stated in Purbhoo arXiv:0705.1184 §2.4). For a KT puzzle `ℓ` of size `n` with
`L = jointL ℓ = (f₀, f₁)`, `Δ_k = f_k(0,0) + m_k·T₁`, `m_k` = number of `k`s on the bottom side:
1. every `0`-edge of `T_n` maps under `f₀` onto a unit edge in `Δ₀`, and `f₀(p) ∈ Δ₀` for every
   vertex `p`;
2. the same for `k = 1`;
3. every vertex of a lifted tile (`L(p)`, `p` a vertex of `T_n`) and every nest-rhombus vertex
   `L(p_s) + a(D,0) + b(0,D)`, `0 ≤ a ≤ m₀`, `0 ≤ b ≤ m₁`, for every side `(p_s, D)` of `T_n`, has
   `π₀ ∈ Δ₀` and `π₁ ∈ Δ₁`.
The identification of the nest-rhombus vertices with this family is the tex's Definition
`def:M0` (`M₀` itself is not defined in Lean). -/
theorem corImg (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    -- (1)
    ((∀ e, InTn n e → lab e = l0 →
      EdgeIn (fun p => (jointL lab p).1) (jointL lab (0, 0)).1 (cntBot lab n l0).toNat e) ∧
    (∀ i j : ℕ, i + j ≤ n →
      PtIn (jointL lab (0, 0)).1 (cntBot lab n l0).toNat (jointL lab ((i : ℤ), (j : ℤ))).1)) ∧
    -- (2)
    ((∀ e, InTn n e → lab e = l1 →
      EdgeIn (fun p => (jointL lab p).2) (jointL lab (0, 0)).2 (cntBot lab n l1).toNat e) ∧
    (∀ i j : ℕ, i + j ≤ n →
      PtIn (jointL lab (0, 0)).2 (cntBot lab n l1).toNat (jointL lab ((i : ℤ), (j : ℤ))).2)) ∧
    -- (3)
    (∀ s ∈ sides n, ∀ a b : ℕ, a ≤ (cntBot lab n l0).toNat → b ≤ (cntBot lab n l1).toNat →
      PtIn (jointL lab (0, 0)).1 (cntBot lab n l0).toNat
          (jointL lab s.1 + ((a : ℤ) • s.2, (b : ℤ) • s.2)).1 ∧
        PtIn (jointL lab (0, 0)).2 (cntBot lab n l1).toNat
          (jointL lab s.1 + ((a : ℤ) • s.2, (b : ℤ) • s.2)).2) := by
  refine ⟨corImg_k0 lab n hK hB, corImg_k1 lab n hK hB, ?_⟩
  have hT0 := puzzleLift_of_KT lab n hK
  have hL0 := onEdges_of_tri n _ fun t ht => (hT0 t ht).1
  have hT1 := puzzleLift_of_mirror (swapLab lab) n (allMir_swap lab n hK)
  have hL1 := onEdges_of_tri n _ fun t ht => (hT1 t ht).1
  have hc : cntBot (swapLab lab) n l0 = cntBot lab n l1 := by simp [cntBot, swapLab]
  intro s hs a b ha hb
  have N0 := nest_img lab _ n hL0 hB a ha
  have N1 := nest_img (swapLab lab) _ n hL1 (bdryOK_swap lab n hB) b (by rw [hc]; exact hb)
  rw [hc] at N1
  simp only [sides, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl <;>
    simp only [Prod.fst_add, Prod.snd_add, jointL] <;>
    exact ⟨by tauto, by tauto⟩

/-! ## Lesion: the `0/1` boundary hypothesis is load-bearing -/

/-- One up-triangle with the KT piece `(10, 0, 1)` read counterclockwise from the bottom, so the
bottom edge is `10`. -/
def bLab (e : Edge) : Lbl :=
  if e = ⟨0, 0, c0⟩ then l10 else if e = ⟨0, 0, c2⟩ then l0 else l1

/-- **Boundary lesion** (predicted before running, note `2026-11-27c2-lean-Q597-img.md`): the
triangle is KT, `BdryOK` fails (bottom is `10`), `m₀ = 0`, and the vertex `(1,0)` maps to
`f₀(0,0) + (1,-1)`, outside `Δ₀ = {f₀(0,0)}`. So the vertex clause of `corImg` fails once the
`0/1` boundary hypothesis is dropped. -/
theorem bdry10_lesion :
    KTTri bLab ⟨0, 0, up⟩ ∧ ¬ BdryOK bLab 1 ∧ cntBot bLab 1 l0 = 0 ∧
      (jointL bLab (1, 0)).1 = (jointL bLab (0, 0)).1 + (1, -1) ∧
      ¬ PtIn (jointL bLab (0, 0)).1 (cntBot bLab 1 l0).toNat (jointL bLab (1, 0)).1 := by
  have h1 : cntBot bLab 1 l0 = 0 := by simp [cntBot, bLab]
  have h2 : (jointL bLab (1, 0)).1 = (1, -1) := by
    simp [jointL, integ, coch, bLab, triVal, locv]
  have h3 : (jointL bLab (0, 0)).1 = (0, 0) := by simp [jointL, integ]; rfl
  refine ⟨by simp [KTTri, bLab, KTPiece], fun h => ?_, h1, by rw [h2, h3]; rfl, ?_⟩
  · have := (h 0 (by norm_num)).1; simp [bLab] at this
  · rw [h1, h2, h3]; simp [PtIn]

end Q597G1
