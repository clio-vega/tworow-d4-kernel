/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.Q597D1

/-!
# Q597 Theorem G1 for `k = 1` (and so for `k ∈ {0,1}`), for every KT puzzle

Paper proof: `projects/proofs/2026-11-24c2-Q597-D.tex`, Theorem `thm:G1` ("Take `k=0`; the case
`k=1` is the same with `0` and `1` exchanged"), with Lemma `lem:D`(1)–(4) (Knutson–Tao, as stated
in Purbhoo arXiv:0705.1184 §2.4) and Lemma `lem:chir`.

`Q597G1.G1_KT` (`Q597D1.lean`) is the case `k = 0`. The tex's "exchange `0` and `1`" is **not** a
symmetry of KT pieces: the swap of `(10,0,1)` is `(10,1,0)`, a *mirror* piece
(`swap_not_KT`). What survives is that the swap carries KT pieces onto mirror pieces
(`KTPiece_iff_swap`), and the lift construction of `Q597D1` needs only *consistent* chirality.

* `puzzleLift_of_pieces`: the c1 construction (`integ (coch lab)`) for any piece predicate `P`
  satisfying five finite local facts (up/down closure, the three rhombus rules) and
  "`000` or has a `1`". `puzzleLift_of_KT'` re-derives c1's `puzzleLift_of_KT` from it, and
  `puzzleLift_of_mirror` is the mirror instance.
* The `k = 1` objects are stated **on `ℓ` itself**, as in the tex: `LiftOK1` (`f₁` moves by the
  edge vector on `1`-edges and is constant on `0`-edges, tex Lemma D(1),(3) for `π₁ ∘ L`),
  `Is111`, and `Nchain1` (the number of `111`-triangles of `ℓ` over `t`, i.e. of
  `Λ₁`-triangles of `M₀`). The bridge lemmas `liftOK1_iff`, `is111_iff`, `nchain1_eq` identify
  them with the `k = 0` objects of `swapLab ℓ`; they are definitional unfoldings, not
  hypotheses.
* `coch_swap_l1`, `coch_swap_l0`: the cochain `coch (swapLab ℓ)` gives a `1`-edge of `ℓ` its own
  vector and a `0`-edge `0` — it is the `Λ₁`-part of the tex's cochain. Its value on a `10`-edge
  is fixed by closure, which is how the tex defines it too (`-d₁`).
* `G1_k1_of_lift`: G1 for `k = 1` for **every** `f` with the `k = 1` lift property (so for the
  tex's `f₁ = π₁ ∘ L`, whatever normalisation of `L` is chosen).
* `G1_KT_k1`: for every KT puzzle such an `f₁` exists, and `N₁ = [f₁(0,0) + m·T₁]`.
* `G1_KT_both`: Theorem G1 as the tex states it, for `k = 0` and `k = 1`.

Lesion: `mixed_violates_rhombus` — the piece predicate "KT or mirror" (mixed chirality) fails
the class-2 rhombus rule hypothesis of `puzzleLift_of_pieces`.
-/

namespace Q597G1

open Ori Cls Lbl Finset

/-! ## The swap `0 ↔ 1` -/

/-- Exchange the labels `0` and `1`; `10` is fixed. -/
def swap01 : Lbl → Lbl
  | l0 => l1 | l1 => l0 | l10 => l10

/-- The swapped labelling. -/
def swapLab (lab : Edge → Lbl) : Edge → Lbl := fun e => swap01 (lab e)

@[simp] theorem swap01_swap01 (x : Lbl) : swap01 (swap01 x) = x := by cases x <;> rfl

@[simp] theorem swap01_eq_l0 (x : Lbl) : swap01 x = l0 ↔ x = l1 := by cases x <;> decide
@[simp] theorem swap01_eq_l1 (x : Lbl) : swap01 x = l1 ↔ x = l0 := by cases x <;> decide

/-- **The swap is not a KT symmetry**: `(10,0,1)` is KT, its swap `(10,1,0)` is not. -/
theorem swap_not_KT :
    KTPiece l10 l0 l1 = true ∧ KTPiece (swap01 l10) (swap01 l0) (swap01 l1) = false := by
  decide

/-- The swap carries KT pieces exactly onto mirror pieces. -/
theorem KTPiece_iff_swap :
    ∀ x y z : Lbl, KTPiece x y z = MirPiece (swap01 x) (swap01 y) (swap01 z) := by
  decide

/-! ## The lift construction for any consistent piece predicate -/

/-- A unit triangle whose counterclockwise labels satisfy `P` (cf. `KTTri`). -/
def PTri (P : Lbl → Lbl → Lbl → Bool) (lab : Edge → Lbl) (t : Tri) : Prop :=
  match t.o with
  | up => P (lab ⟨t.a, t.b, c0⟩) (lab ⟨t.a, t.b, c2⟩) (lab ⟨t.a, t.b, c1⟩) = true
  | down => P (lab ⟨t.a + 1, t.b, c1⟩) (lab ⟨t.a, t.b + 1, c0⟩) (lab ⟨t.a, t.b, c2⟩) = true

/-- Every unit triangle of `T_n` satisfies `P`. -/
def AllP (P : Lbl → Lbl → Lbl → Bool) (lab : Edge → Lbl) (n : ℕ) : Prop :=
  ∀ t, inDelta (0, 0) n t → PTri P lab t

/-- The five finite local facts that the c1 construction uses (tex Lemma chir and the
well-definedness/closure step of Lemma D(1)), plus "`000` or has a `1`-edge". -/
structure GoodPieces (P : Lbl → Lbl → Lbl → Bool) : Prop where
  up : ∀ x0 x1 x2 : Lbl, P x0 x2 x1 = true →
    triVal c0 x0 x1 x2 + triVal c2 x0 x1 x2 = triVal c1 x0 x1 x2
  down : ∀ y0 y1 y2 : Lbl, P y1 y0 y2 = true →
    triVal c0 y0 y1 y2 + triVal c2 y0 y1 y2 = triVal c1 y0 y1 y2
  r0 : ∀ x0 x1 x2 y1 y2 : Lbl, P x0 x2 x1 = true → P y1 x0 y2 = true →
    triVal c0 x0 x1 x2 = triVal c0 x0 y1 y2
  r1 : ∀ x0 x1 x2 y0 y2 : Lbl, P x0 x2 x1 = true → P x1 y0 y2 = true →
    triVal c1 x0 x1 x2 = triVal c1 y0 x1 y2
  r2 : ∀ x0 x1 x2 y0 y1 : Lbl, P x0 x2 x1 = true → P y1 y0 x2 = true →
    triVal c2 x0 x1 x2 = triVal c2 y0 y1 x2
  has1 : ∀ x y z : Lbl, P x y z = true → (x = l0 ∧ y = l0 ∧ z = l0) ∨ (x = l1 ∨ y = l1 ∨ z = l1)

theorem goodPieces_KT : GoodPieces KTPiece :=
  ⟨triVal_closed, triVal_closed_down, rhombus_rule_c0, rhombus_rule_c1, rhombus_rule_c2,
    piece_000_or_has1⟩

/-- The mirror pieces satisfy the same five facts (tex D(1)'s half-turn argument does not see
chirality); cf. c1's `rhombus_rule_mirror`. -/
theorem goodPieces_Mir : GoodPieces MirPiece := by
  refine ⟨by decide, by decide, ?_, ?_, ?_, by decide⟩
  · intro x0 x1 x2 y1 y2 h1 h2
    exact rhombus_rule_mirror c0 x0 x1 x2 x0 y1 y2 h1 h2 (Or.inl ⟨rfl, rfl⟩)
  · intro x0 x1 x2 y0 y2 h1 h2
    exact rhombus_rule_mirror c1 x0 x1 x2 y0 x1 y2 h1 h2 (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · intro x0 x1 x2 y0 y1 h1 h2
    exact rhombus_rule_mirror c2 x0 x1 x2 y0 y1 x2 h1 h2 (Or.inr (Or.inr ⟨rfl, rfl⟩))

theorem closed_of_pieces (P : Lbl → Lbl → Lbl → Bool) (hP : GoodPieces P) (lab : Edge → Lbl)
    (n : ℕ) (hK : AllP P lab n) : Closed (coch lab) n := by
  constructor
  · intro a b hab
    have := hK ⟨a, b, up⟩ (by simp [inDelta]; omega)
    exact hP.up _ _ _ this
  · intro a b hab
    have hd := hK ⟨a, b, down⟩ (by simp [inDelta]; omega)
    have hu0 := hK ⟨a, (b : ℤ) + 1, up⟩ (by simp [inDelta]; omega)
    have hu1 := hK ⟨(a : ℤ) + 1, b, up⟩ (by simp [inDelta]; omega)
    have hu2 := hK ⟨a, b, up⟩ (by simp [inDelta]; omega)
    simp only [PTri] at hd hu0 hu1 hu2
    set y0 := lab ⟨a, (b : ℤ) + 1, c0⟩
    set y1 := lab ⟨(a : ℤ) + 1, b, c1⟩
    set y2 := lab ⟨a, b, c2⟩
    have r0 : coch lab ⟨a, (b : ℤ) + 1, c0⟩ = triVal c0 y0 y1 y2 := hP.r0 _ _ _ y1 y2 hu0 hd
    have r1 : coch lab ⟨(a : ℤ) + 1, b, c1⟩ = triVal c1 y0 y1 y2 := hP.r1 _ _ _ y0 y2 hu1 hd
    have r2 : coch lab ⟨a, b, c2⟩ = triVal c2 y0 y1 y2 := hP.r2 _ _ _ y0 y1 hu2 hd
    rw [r0, r1, r2]
    exact hP.down _ _ _ hd

/-- **Lemma D(1), `Λ₀`-part, for any consistent chirality** (generalises c1's
`puzzleLift_of_KT`). -/
theorem puzzleLift_of_pieces (P : Lbl → Lbl → Lbl → Bool) (hP : GoodPieces P)
    (lab : Edge → Lbl) (n : ℕ) (hK : AllP P lab n) : PuzzleLift lab (integ (coch lab)) n := by
  have hC := closed_of_pieces P hP lab n hK
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
    have key : ∀ (p q r : Edge), P (lab p) (lab q) (lab r) = true → triEdges t = [p, q, r] →
        Is000 lab t ∨ Has1 lab t := fun p q r hk ht' => by
      unfold Is000 Has1; rw [ht']
      rcases hP.has1 _ _ _ hk with ⟨h1, h2, h3⟩ | h | h | h
      · left; simp [h1, h2, h3]
      · exact Or.inr ⟨p, by simp, h⟩
      · exact Or.inr ⟨q, by simp, h⟩
      · exact Or.inr ⟨r, by simp, h⟩
    rcases t with ⟨a, b, _ | _⟩ <;> simp only [PTri] at hk <;> exact key _ _ _ hk rfl

/-- Consistency check: c1's `puzzleLift_of_KT` is the `KTPiece` instance. -/
theorem puzzleLift_of_KT' (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) :
    PuzzleLift lab (integ (coch lab)) n :=
  puzzleLift_of_pieces KTPiece goodPieces_KT lab n hK

theorem puzzleLift_of_mirror (lab : Edge → Lbl) (n : ℕ) (hM : AllP MirPiece lab n) :
    PuzzleLift lab (integ (coch lab)) n :=
  puzzleLift_of_pieces MirPiece goodPieces_Mir lab n hM

/-- Step 1 of the route: the swap of a KT puzzle is a consistent-mirror labelling. -/
theorem allMir_swap (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) :
    AllP MirPiece (swapLab lab) n := by
  intro t ht
  have := hK t ht
  rcases t with ⟨a, b, _ | _⟩ <;> simp only [KTTri, PTri, swapLab] at this ⊢ <;>
    rwa [← KTPiece_iff_swap]

/-! ## The `k = 1` objects, stated on `ℓ` -/

/-- The `k = 1` lift condition (tex Lemma D(1),(3) for `f₁ = π₁ ∘ L`): on a `1`-edge `f`
moves by the edge vector, on a `0`-edge it is constant. -/
def LiftOK1 (lab : Edge → Lbl) (f : V → V) (e : Edge) : Prop :=
  (lab e = l1 → f e.head = f e.tail + e.vec) ∧ (lab e = l0 → f e.head = f e.tail)

/-- A `111`-triangle. -/
def Is111 (lab : Edge → Lbl) (t : Tri) : Prop := ∀ e ∈ triEdges t, lab e = l1

instance (lab : Edge → Lbl) (t : Tri) : Decidable (Is111 lab t) := by
  unfold Is111; infer_instance

/-- `N₁(t)`: the number of `111`-triangles `τ` of `T_n` with `f(τ) = t` (tex: the number of
`Λ₁`-triangles of `M₀` whose `π₁`-image is `t`). -/
noncomputable def Nchain1 (lab : Edge → Lbl) (f : V → V) (n : ℕ) : Tri →₀ ℤ :=
  ∑ t ∈ (Tn n).support.filter (Is111 lab), Finsupp.single (imgTri f t) 1

theorem liftOK1_iff (lab : Edge → Lbl) (f : V → V) (e : Edge) :
    LiftOK1 lab f e ↔ LiftOK (swapLab lab) f e := by
  simp [LiftOK1, LiftOK, swapLab]

theorem is111_iff (lab : Edge → Lbl) (t : Tri) : Is111 lab t ↔ Is000 (swapLab lab) t := by
  simp [Is111, Is000, swapLab]

theorem nchain1_eq (lab : Edge → Lbl) (f : V → V) (n : ℕ) :
    Nchain1 lab f n = Nchain (swapLab lab) f n := by
  unfold Nchain1 Nchain
  congr 1
  exact Finset.filter_congr fun t _ => is111_iff lab t

theorem bdryOK_swap (lab : Edge → Lbl) (n : ℕ) (hB : BdryOK lab n) : BdryOK (swapLab lab) n := by
  intro i hi
  obtain ⟨h1, h2, h3⟩ := hB i hi
  simp only [swapLab, swap01_eq_l0, swap01_eq_l1]
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- On a KT piece every triangle is `111` or has a `0`-edge (`(0,0,0)`, `(10,0,1)` have one). -/
theorem piece_111_or_has0 : ∀ x y z : Lbl, KTPiece x y z = true →
    (x = l1 ∧ y = l1 ∧ z = l1) ∨ (x = l0 ∨ y = l0 ∨ z = l0) := by decide

/-- **Fidelity**: `coch (swapLab ℓ)` is the `Λ₁`-part of the tex cochain of `ℓ` — an oriented
`1`-edge of `ℓ` gets its own vector, a `0`-edge gets `0`. -/
theorem coch_swap_l1 (lab : Edge → Lbl) (e : Edge) (h : lab e = l1) :
    coch (swapLab lab) e = e.vec := coch_l0 _ e (by simp [swapLab, h])

theorem coch_swap_l0 (lab : Edge → Lbl) (e : Edge) (h : lab e = l0) :
    coch (swapLab lab) e = 0 := coch_l1 _ e (by simp [swapLab, h])

/-! ## Theorem G1 for `k = 1` -/

/-- **Theorem G1, `k = 1`, for every `k = 1` lift.** Let `ℓ` be a KT puzzle with `0/1`
boundary and `f` any vertex map with the `k = 1` lift property on every edge of `T_n`
(for example `f₁ = π₁ ∘ L`, tex Lemma D(3)). Let `m` be the advance of `f` along the bottom side
(= the number of `1`s there, tex `m₁`). Then `N₁(t) = 1` for `t ⊆ Δ₁ = f(0,0) + m·T₁`, and `0`
otherwise. -/
theorem G1_k1_of_lift (lab : Edge → Lbl) (f : V → V) (n m : ℕ) (hK : AllKT lab n)
    (hB : BdryOK lab n)
    (hL : ∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t, LiftOK1 lab f e)
    (hm : f ((n : ℤ), 0) = f (0, 0) + ((m : ℤ), 0)) (t : Tri) :
    Nchain1 lab f n t = if inDelta (f (0, 0)) m t then 1 else 0 := by
  have hT : PuzzleLift (swapLab lab) f n := by
    intro t ht
    refine ⟨fun e he => (liftOK1_iff lab f e).1 (hL t ht e he), ?_⟩
    have hk := hK t ht
    have key : ∀ (p q r : Edge), KTPiece (lab p) (lab q) (lab r) = true →
        triEdges t = [p, q, r] → Is000 (swapLab lab) t ∨ Has1 (swapLab lab) t :=
      fun p q r hk ht' => by
        unfold Is000 Has1; rw [ht']
        rcases piece_111_or_has0 _ _ _ hk with ⟨h1, h2, h3⟩ | h | h | h
        · left; simp [swapLab, h1, h2, h3]
        · exact Or.inr ⟨p, by simp, by simp [swapLab, h]⟩
        · exact Or.inr ⟨q, by simp, by simp [swapLab, h]⟩
        · exact Or.inr ⟨r, by simp, by simp [swapLab, h]⟩
    rcases t with ⟨a, b, _ | _⟩ <;> simp only [KTTri] at hk <;> exact key _ _ _ hk rfl
  rw [nchain1_eq]
  exact G1_puzzle (swapLab lab) f n m hT (bdryOK_swap lab n hB) hm t

/-- **Theorem G1 for `k = 1`, for every KT puzzle** (tex Thm G1, with Lemma D(1)–(4)):
the `k = 1` lift `f₁ = integ (coch (swapLab ℓ))` exists, and `N₁ = [f₁(0,0) + m·T₁]`. -/
theorem G1_KT_k1 (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    ∃ f : V → V, (∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t, LiftOK1 lab f e) ∧
      ∃ m : ℕ, f ((n : ℤ), 0) = f (0, 0) + ((m : ℤ), 0) ∧
        ∀ t, Nchain1 lab f n t = if inDelta (f (0, 0)) m t then 1 else 0 := by
  have hT := puzzleLift_of_mirror (swapLab lab) n (allMir_swap lab n hK)
  have hL : ∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t,
      LiftOK1 lab (integ (coch (swapLab lab))) e :=
    fun t ht e he => (liftOK1_iff lab _ e).2 ((hT t ht).1 e he)
  obtain ⟨k, hk, -⟩ := fstar_bd_Tn (swapLab lab) _ n hT (bdryOK_swap lab n hB)
  have hk' : integ (coch (swapLab lab)) ((n : ℤ), 0) =
      integ (coch (swapLab lab)) (0, 0) + ((k : ℤ), 0) := by rw [hk]; simp
  exact ⟨_, hL, k, hk', G1_k1_of_lift lab _ n k hK hB hL hk'⟩

/-- **Theorem G1 for `k ∈ {0,1}`, for every KT puzzle** — the statement of tex Thm G1. -/
theorem G1_KT_both (lab : Edge → Lbl) (n : ℕ) (hK : AllKT lab n) (hB : BdryOK lab n) :
    (∃ f : V → V, PuzzleLift lab f n ∧ ∃ m : ℕ, f ((n : ℤ), 0) = f (0, 0) + ((m : ℤ), 0) ∧
      ∀ t, Nchain lab f n t = if inDelta (f (0, 0)) m t then 1 else 0) ∧
    (∃ f : V → V, (∀ t, inDelta (0, 0) n t → ∀ e ∈ triEdges t, LiftOK1 lab f e) ∧
      ∃ m : ℕ, f ((n : ℤ), 0) = f (0, 0) + ((m : ℤ), 0) ∧
        ∀ t, Nchain1 lab f n t = if inDelta (f (0, 0)) m t then 1 else 0) :=
  ⟨G1_KT lab n hK hB, G1_KT_k1 lab n hK hB⟩

/-! ## Lesion -/

/-- **Mixed-chirality lesion** (kernel): the predicate "KT or mirror" fails the class-2
rhombus-rule field of `GoodPieces`, so `puzzleLift_of_pieces` does not apply to mixed
labellings (c1 census: 2/5 and 2/16 lift). -/
theorem mixed_violates_rhombus :
    ¬ ∀ x0 x1 x2 y0 y1 : Lbl, (KTPiece x0 x2 x1 || MirPiece x0 x2 x1) = true →
      (KTPiece y1 y0 x2 || MirPiece y1 y0 x2) = true →
      triVal c2 x0 x1 x2 = triVal c2 y0 y1 x2 := by decide

theorem mixed_not_good : ¬ GoodPieces (fun x y z => KTPiece x y z || MirPiece x y z) :=
  fun h => mixed_violates_rhombus h.r2

end Q597G1
