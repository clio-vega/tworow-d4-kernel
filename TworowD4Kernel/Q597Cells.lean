/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.Q597D1
import Mathlib.NumberTheory.Real.Irrational

/-!
# Q597 Lemma 36: the 36 cells `(e,0) × (0,f)` under the engine's embedding `φ`, in exact arithmetic

Paper proof: `projects/proofs/2026-11-27c2-Q597-MC.tex`, Lemma `lem:36` (l.125–131). The Python
check `proofs/code-1127c2-Q597/chir36.py` decides the shape by `round(degrees(phase))` and the
orientation by a float `det` with a `1e-9` tolerance. This file replaces both float steps with
exact arithmetic in `ℤ[√3]`. Purbhoo's chirality is as in arXiv:0705.1184 §2.4 (pp. 10–11): this
file reuses `KTPiece` from `Q597D1`, so Lemma 36 talks about the same pieces as Lemma D.

## The embedding, exactly

The engine (`code-1112c2-Q585/mosaic.py`, `Geo(-1)`) uses
`φ(a₀,b₀,a₁,b₁) = z₀·tri(a₀,b₀) + z₁·tri(a₁,b₁)` with `tri(a,b) = a + b·ω₆`, `ω₆ = e^{iπ/3}`,
`z₀ = e^{iπ/12}` and `z₁ = e^{-iπ/12}`. These entries need `√2`. Shape, angle and orientation
are invariant under a rotation followed by a positive scaling, so we work with
`Φ = 4·e^{-iπ/12}·φ = (2z₀')·(2 tri) + (2z₁')·(2 tri)`, where `2z₀' = 2` and `2z₁' = √3 − i`.
`2·tri(a,b) = (2a+b) + i·b√3`. Every coordinate of `Φ` lies in `ℤ[√3]`.
`Φ_fidelity` (below, an `#eval`) prints `Φ` on the four basis vectors. The cross-check against the
Python floats, `e^{iπ/12}·Φ/4 = G.phi`, is in the session note (max error 2.2e-16).

`Z3.sgn` and the `ℤ[√3]` equalities are proved to be the real ones (`Z3.sgn_sound`,
`Z3.val_inj`, using that `√3` is irrational; `isSquareZ_real`, `isRh30Z_real`,
`lemma36_orient_real`), so every kernel `decide` here is a statement about the real plane.

The puzzle plane uses the same `2·tri` (a positive scaling of the engine's `cz`).
-/

namespace Q597Cells

open Q597G1 Lbl

/-! ## `ℤ[√3]` with an exact sign -/

/-- `re + ir·√3`. -/
structure Z3 where
  re : ℤ
  ir : ℤ
  deriving DecidableEq, Repr

namespace Z3

instance : Add Z3 := ⟨fun x y => ⟨x.re + y.re, x.ir + y.ir⟩⟩
instance : Neg Z3 := ⟨fun x => ⟨-x.re, -x.ir⟩⟩
instance : Sub Z3 := ⟨fun x y => ⟨x.re - y.re, x.ir - y.ir⟩⟩
instance : Mul Z3 := ⟨fun x y => ⟨x.re * y.re + 3 * x.ir * y.ir, x.re * y.ir + x.ir * y.re⟩⟩
instance : Zero Z3 := ⟨⟨0, 0⟩⟩

/-- Exact sign of `a + b√3` (`√3` irrational, so `a + b√3 = 0 ⟺ a = b = 0`).
Positive iff both parts are `≥ 0` (not both zero), or the parts have opposite signs and the
positive part dominates in square: `a² > 3b²` or `3b² > a²`. -/
def sgn (x : Z3) : ℤ :=
  if x.re = 0 ∧ x.ir = 0 then 0
  else if 0 ≤ x.re ∧ 0 ≤ x.ir then 1
  else if x.re ≤ 0 ∧ x.ir ≤ 0 then -1
  else if 0 < x.re then (if 3 * x.ir * x.ir < x.re * x.re then 1 else -1)
  else (if x.re * x.re < 3 * x.ir * x.ir then 1 else -1)

/-- Sanity: `sgn` agrees with the real number on a grid of 2601 values (`√3 ≈ 1.7320508`
bounds: `173/100 < √3 < 174/100`, enough to separate every grid point that is nonzero). -/
theorem sgn_grid : ∀ a b : Fin 51,
    let x : Z3 := ⟨(a : ℤ) - 25, (b : ℤ) - 25⟩
    (sgn x = 1 → 0 < 100 * x.re + 174 * x.ir) ∧ (sgn x = -1 → 100 * x.re + 173 * x.ir < 0) := by
  decide

end Z3

/-- A point of the plane, coordinates in `ℤ[√3]`. -/
abbrev Pt := Z3 × Z3

def det (p q : Pt) : Z3 := p.1 * q.2 - p.2 * q.1
def inner (p q : Pt) : Z3 := p.1 * q.1 + p.2 * q.2
/-- Complex multiplication. -/
def cmul (z w : Pt) : Pt := (z.1 * w.1 - z.2 * w.2, z.1 * w.2 + z.2 * w.1)

/-- `2·tri(a,b) = (2a+b) + i·b√3`. -/
def tri2 (v : V) : Pt := (⟨2 * v.1 + v.2, 0⟩, ⟨0, v.2⟩)

/-- `2z₀' = 2`. -/
def Z0 : Pt := (⟨2, 0⟩, ⟨0, 0⟩)
/-- `2z₁' = √3 − i`: `z₁/z₀ = e^{-iπ/6}` (engine `Geo(-1)`). -/
def Z1 : Pt := (⟨0, 1⟩, ⟨-1, 0⟩)
/-- The mirror engine `Geo(+1)`: `z₁/z₀ = e^{+iπ/6}` (lesion only). -/
def Z1mir : Pt := (⟨0, 1⟩, ⟨1, 0⟩)

/-- `Φ = 4·e^{-iπ/12}·φ`, with second constant `z` (`Z1` for the engine). -/
def PhiZ (z : Pt) (P : V × V) : Pt := cmul Z0 (tri2 P.1) + cmul z (tri2 P.2)

def Phi : V × V → Pt := PhiZ Z1

/-- Fidelity printout: `Φ` on the four basis vectors of `ℤ⁴`. -/
def Phi_fidelity : List Pt :=
  [Phi ((1, 0), (0, 0)), Phi ((0, 1), (0, 0)), Phi ((0, 0), (1, 0)), Phi ((0, 0), (0, 1))]

#eval Phi_fidelity

/-! ## The six puzzle unit vectors and the KT chirality of a parallelogram -/

/-- The six unit vectors, in the order of `chir36.py`'s `U`. -/
def U : Fin 6 → V
  | 0 => (1, 0) | 1 => (0, 1) | 2 => (-1, 1) | 3 => (-1, 0) | 4 => (0, -1) | 5 => (1, -1)

def isUnit (d : V) : Bool := (List.finRange 6).any fun i => U i = d

def parallel (e f : V) : Bool := f = e || f = -e

/-- Puzzle-plane determinant of `e, f` (scaled by `4`). -/
def psiDet (e f : V) : Z3 := det (tri2 e) (tri2 f)

/-- The label of the parallelogram edge `p → q`: the short diagonal is `10`, edges parallel to
`e` are `0`, edges parallel to `f` are `1` (`chir36.py`'s `lab`). `none` marks an edge that is
none of these. -/
def labEdge (e f : V) (diag : V × V) (p q : V) : Option Lbl :=
  if (p, q) = diag ∨ (q, p) = diag then some l10
  else if parallel e (q - p) then some l0
  else if parallel f (q - p) then some l1
  else none

/-- A triangle is a KT piece when its labels read counterclockwise are `KTPiece`. The
counterclockwise order is decided by the exact sign of the puzzle-plane determinant. -/
def triOK (e f : V) (diag : V × V) (t : V × V × V) : Bool :=
  let (a, b, c) := t
  let (b, c) := if Z3.sgn (det (tri2 (b - a)) (tri2 (c - a))) < 0 then (c, b) else (b, c)
  match labEdge e f diag a b, labEdge e f diag b c, labEdge e f diag c a with
  | some x, some y, some z => KTPiece x y z
  | _, _, _ => false

/-- The puzzle parallelogram on `e, f` is a KT rhombus of Purbhoo's chirality: split it along its
short diagonal, and both triangles are KT pieces (`chir36.py`'s `good`). -/
def ktOK (e f : V) : Bool :=
  if isUnit (e - f) then
    triOK e f (e, f) ((0, 0), e, f) && triOK e f (e, f) (e, e + f, f)
  else
    triOK e f ((0, 0), e + f) ((0, 0), e, e + f) && triOK e f ((0, 0), e + f) ((0, 0), e + f, f)

/-! ## Shapes, exactly -/

/-- `φ`-image of the cell `(e,0) × (0,f)` is a square: the edge vectors are orthogonal. -/
def isSquareZ (z : Pt) (e f : V) : Bool := inner (PhiZ z (e, 0)) (PhiZ z (0, f)) = 0

/-- A `30°/150°` rhombus: `4⟨u,v⟩² = 3|u|²|v|²`, i.e. `|cos ∠(u,v)| = √3/2`. -/
def isRh30Z (z : Pt) (e f : V) : Bool :=
  let u := PhiZ z (e, 0); let v := PhiZ z (0, f)
  (⟨4, 0⟩ : Z3) * inner u v * inner u v = (⟨3, 0⟩ : Z3) * inner u u * inner v v

/-- `ψ ∘ φ⁻¹` preserves orientation on the cell: `det(Φ(e,0), Φ(0,f))` and `det(e,f)` have the
same nonzero sign. -/
def orientPresZ (z : Pt) (e f : V) : Bool :=
  Z3.sgn (det (PhiZ z (e, 0)) (PhiZ z (0, f))) = Z3.sgn (psiDet e f)

/-- All four edges of the cell have the same `Φ`-length (`|Φ(e,0)|² = |Φ(0,f)|² = 16`), so the
cell is a rhombus in the strict sense. -/
theorem cell_sides_unit : ∀ i j : Fin 6,
    inner (Phi (U i, 0)) (Phi (U i, 0)) = ⟨16, 0⟩ ∧
      inner (Phi (0, U j)) (Phi (0, U j)) = ⟨16, 0⟩ := by
  decide

/-! ## Lemma 36 -/

/-- **Lemma 36 (the 36 cells)**, `2026-11-27c2-Q597-MC.tex` l.125. For puzzle unit vectors
`e = U i`, `f = U j`, the `φ`-image of `(e,0) × (0,f)`:

* is exactly one of a square and a `30°/150°` rhombus;
* (a) is a square iff the puzzle parallelogram is non-degenerate and a KT rhombus of Purbhoo's
  chirality;
* (b) is a `30°/150°` rhombus with `ψ` degenerate iff `e ∥ f`;
* (c) otherwise (not a square, `e ∦ f`) is a `30°/150°` rhombus with `ψ` non-degenerate and the
  wrong chirality;
* `ψ ∘ φ⁻¹` preserves orientation on every non-degenerate cell. -/
theorem lemma36 : ∀ i j : Fin 6,
    let e := U i; let f := U j
    (isSquareZ Z1 e f ≠ isRh30Z Z1 e f) ∧
    (isSquareZ Z1 e f = true ↔ (Z3.sgn (psiDet e f) ≠ 0 ∧ ktOK e f = true)) ∧
    ((isRh30Z Z1 e f = true ∧ psiDet e f = 0) ↔ parallel e f = true) ∧
    ((isSquareZ Z1 e f = false ∧ parallel e f = false) →
      isRh30Z Z1 e f = true ∧ Z3.sgn (psiDet e f) ≠ 0 ∧ ktOK e f = false) ∧
    (Z3.sgn (psiDet e f) ≠ 0 → orientPresZ Z1 e f = true) := by
  decide

/-- The census of `chir36.py`: 12 square / KT / preserved, 12 rhombus / degenerate,
12 rhombus / wrong chirality / preserved. -/
def cells : List (Fin 6 × Fin 6) := (List.finRange 6).flatMap fun i => (List.finRange 6).map (i, ·)

theorem census36 :
    (cells.filter fun c => isSquareZ Z1 (U c.1) (U c.2) && ktOK (U c.1) (U c.2) &&
        orientPresZ Z1 (U c.1) (U c.2)).length = 12 ∧
    (cells.filter fun c => isRh30Z Z1 (U c.1) (U c.2) && psiDet (U c.1) (U c.2) = 0).length = 12 ∧
    (cells.filter fun c => isRh30Z Z1 (U c.1) (U c.2) && Z3.sgn (psiDet (U c.1) (U c.2)) ≠ 0 &&
        !ktOK (U c.1) (U c.2) && orientPresZ Z1 (U c.1) (U c.2)).length = 12 := by
  decide

/-! ## The triangles `τ × {w}` and `{v} × σ` -/

/-- **Lemma 36, triangle clause.** The unit triangle with edge vectors `U i`, `U (i+1)`
(counterclockwise, 6 per lattice), placed in `Λ₀` (`τ × {w}`, `k = 0`) or in `Λ₁` (`{v} × σ`,
`k = 1`): `Φ` and `ψ` give it the same nonzero orientation. `ψ` is the identity on each factor,
so the puzzle side is `det(U i, U (i+1))`. 12 cases. -/
def embK (k : Fin 2) (v : V) : V × V := if k = 0 then (v, 0) else (0, v)

theorem lemma36_triangles : ∀ (k : Fin 2) (i : Fin 6),
    let a := U i; let b := U (i + 1)
    Z3.sgn (psiDet a b) = 1 ∧
    Z3.sgn (det (Phi (embK k a)) (Phi (embK k b))) = Z3.sgn (psiDet a b) := by
  decide

/-! ## Lesions -/

/-- **Lesion (mirror embedding, `Geo(+1)`)**. Predicted before running: angle `θ − 30°` becomes
`θ + 30°`, so the squares are now the cells with `θ ∈ {60°, 240°}`, which are the wrong-chirality
cells. Clause (a) fails on every non-degenerate cell: square ⟺ *wrong* chirality. Clause (b) and
orientation are unchanged (`sign sin(θ ± 30°) = sign sin θ` off `180°ℤ`). -/
theorem mirror_lesion_a : ∀ i j : Fin 6,
    let e := U i; let f := U j
    (isSquareZ Z1mir e f = true ↔ (Z3.sgn (psiDet e f) ≠ 0 ∧ ktOK e f = false)) ∧
    ((isRh30Z Z1mir e f = true ∧ psiDet e f = 0) ↔ parallel e f = true) ∧
    (Z3.sgn (psiDet e f) ≠ 0 → orientPresZ Z1mir e f = true) := by
  decide

/-- Therefore the lemma's clause (a) is false for the mirror embedding (not vacuous). -/
theorem mirror_lesion_breaks : ¬ ∀ i j : Fin 6,
    (isSquareZ Z1mir (U i) (U j) = true ↔
      (Z3.sgn (psiDet (U i) (U j)) ≠ 0 ∧ ktOK (U i) (U j) = true)) := by
  decide

/-- **Lesion (orientation clause)**: conjugating the `Λ₁` factor (`Φ'(P) = Z0·tri P₁ +
Z1·conj(tri P₂)`) is a reflection on `{v} × σ`. Predicted: the triangle clause fails for `k = 1`
on all 6 triangles, and holds for `k = 0`. -/
def conj (p : Pt) : Pt := (p.1, -p.2)
def PhiConj (P : V × V) : Pt := cmul Z0 (tri2 P.1) + cmul Z1 (conj (tri2 P.2))

theorem conj_lesion : ∀ i : Fin 6,
    Z3.sgn (det (PhiConj (embK 1 (U i))) (PhiConj (embK 1 (U (i + 1))))) = -1 ∧
    Z3.sgn (det (PhiConj (embK 0 (U i))) (PhiConj (embK 0 (U (i + 1))))) = 1 := by
  decide

end Q597Cells

/-! ## Soundness: the `ℤ[√3]` computation is the real computation -/

namespace Q597Cells.Z3

/-- The real number `re + ir·√3`. -/
noncomputable def val (x : Z3) : ℝ := x.re + x.ir * Real.sqrt 3

theorem irr3 : Irrational (Real.sqrt 3) := by
  have := (irrational_sqrt_ofNat_iff (n := 3)).2 (by
    rintro ⟨r, hr⟩
    have : r ≤ 2 := by nlinarith
    interval_cases r <;> norm_num at hr)
  simpa using this

theorem val_ne_zero (x : Z3) (hx : ¬ (x.re = 0 ∧ x.ir = 0)) : val x ≠ 0 := by
  intro h
  unfold val at h
  by_cases hb : x.ir = 0
  · apply hx; refine ⟨?_, hb⟩; simp [hb] at h; exact_mod_cast h
  · apply irr3
    refine ⟨(-(x.re : ℚ) / x.ir), ?_⟩
    have hb' : (x.ir : ℝ) ≠ 0 := by exact_mod_cast hb
    push_cast; field_simp; linarith

theorem sgn_sound (x : Z3) :
    (sgn x = 1 → 0 < val x) ∧ (sgn x = -1 → val x < 0) ∧ (sgn x = 0 ↔ val x = 0) := by
  have s0 : (0:ℝ) < Real.sqrt 3 := by positivity
  have s2 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hne := val_ne_zero x
  obtain ⟨a, b⟩ := x
  simp only [sgn, val] at *
  by_cases h0 : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := h0; simp
  have hv := hne h0
  rw [if_neg h0]
  have hb : ¬ (0:ℤ) = 1 ∧ ¬ (0:ℤ) = -1 := by omega
  by_cases h1 : 0 ≤ a ∧ 0 ≤ b
  · rw [if_pos h1]
    have : (0:ℝ) ≤ a := by exact_mod_cast h1.1
    have : (0:ℝ) ≤ b := by exact_mod_cast h1.2
    have : 0 ≤ (a:ℝ) + b * Real.sqrt 3 := by positivity
    refine ⟨fun _ => lt_of_le_of_ne this (Ne.symm hv), by omega, by simp [hv]⟩
  rw [if_neg h1]
  by_cases h2 : a ≤ 0 ∧ b ≤ 0
  · rw [if_pos h2]
    have : (a:ℝ) ≤ 0 := by exact_mod_cast h2.1
    have : (b:ℝ) ≤ 0 := by exact_mod_cast h2.2
    have : (a:ℝ) + b * Real.sqrt 3 ≤ 0 := by nlinarith
    refine ⟨by omega, fun _ => lt_of_le_of_ne this hv, by simp [hv]⟩
  rw [if_neg h2]
  by_cases h3 : 0 < a
  · rw [if_pos h3]
    have hb0 : b < 0 := by omega
    have ha : (0:ℝ) < a := by exact_mod_cast h3
    have hbr : (b:ℝ) < 0 := by exact_mod_cast hb0
    by_cases h4 : 3 * b * b < a * a
    · rw [if_pos h4]
      have h4' : (3:ℝ) * b * b < a * a := by exact_mod_cast h4
      refine ⟨fun _ => ?_, by omega, by simp [hv]⟩
      nlinarith [mul_pos ha s0]
    · rw [if_neg h4]
      have h4' : (a:ℝ) * a ≤ 3 * b * b := by push Not at h4; exact_mod_cast h4
      have hp : 0 < (a:ℝ) - b * Real.sqrt 3 := by nlinarith [mul_pos ha s0]
      have hq : ((a:ℝ) + b * Real.sqrt 3) * (a - b * Real.sqrt 3) = a * a - 3 * b * b := by
        linear_combination (-(b:ℝ) * b) * s2
      have : (a:ℝ) + b * Real.sqrt 3 ≤ 0 := by nlinarith
      refine ⟨by omega, fun _ => lt_of_le_of_ne this hv, by simp [hv]⟩
  · rw [if_neg h3]
    have ha0 : a < 0 := by omega
    have hb0 : 0 < b := by omega
    have ha : (a:ℝ) < 0 := by exact_mod_cast ha0
    have hbr : (0:ℝ) < b := by exact_mod_cast hb0
    by_cases h4 : a * a < 3 * b * b
    · rw [if_pos h4]
      have h4' : (a:ℝ) * a < 3 * b * b := by exact_mod_cast h4
      refine ⟨fun _ => ?_, by omega, by simp [hv]⟩
      nlinarith [mul_pos hbr s0]
    · rw [if_neg h4]
      have h4' : 3 * (b:ℝ) * b ≤ a * a := by push Not at h4; exact_mod_cast h4
      have : (a:ℝ) + b * Real.sqrt 3 ≤ 0 := by nlinarith [mul_pos hbr s0]
      refine ⟨by omega, fun _ => lt_of_le_of_ne this hv, by simp [hv]⟩

@[simp] theorem add_re (x y : Z3) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_ir (x y : Z3) : (x + y).ir = x.ir + y.ir := rfl
@[simp] theorem sub_re (x y : Z3) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_ir (x y : Z3) : (x - y).ir = x.ir - y.ir := rfl
@[simp] theorem mul_re (x y : Z3) : (x * y).re = x.re * y.re + 3 * x.ir * y.ir := rfl
@[simp] theorem mul_ir (x y : Z3) : (x * y).ir = x.re * y.ir + x.ir * y.re := rfl
@[simp] theorem zero_re : (0 : Z3).re = 0 := rfl
@[simp] theorem zero_ir : (0 : Z3).ir = 0 := rfl

theorem val_add (x y : Z3) : val (x + y) = val x + val y := by
  simp only [val, add_re, add_ir]; push_cast; ring
theorem val_sub (x y : Z3) : val (x - y) = val x - val y := by
  simp only [val, sub_re, sub_ir]; push_cast; ring
theorem val_mul (x y : Z3) : val (x * y) = val x * val y := by
  have s2 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  simp only [val, mul_re, mul_ir]; push_cast; linear_combination (↑x.ir * ↑y.ir : ℝ) * (-s2)
theorem val_zero : val 0 = 0 := by simp [val]

/-- `val` is injective (`√3` irrational): an equality in `ℤ[√3]` is the real equality. -/
theorem val_inj (x y : Z3) : val x = val y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h0 : val (x - y) = 0 := by rw [val_sub, h, sub_self]
  by_contra hxy
  apply val_ne_zero (x - y) _ h0
  rintro ⟨h1, h2⟩
  apply hxy
  simp only [sub_re, sub_ir] at h1 h2
  obtain ⟨a, b⟩ := x; obtain ⟨c, d⟩ := y
  simp only at h1 h2
  simp only [Z3.mk.injEq]; omega

end Q597Cells.Z3

namespace Q597Cells
open Q597G1 Z3

/-- The real point. -/
noncomputable def rpt (p : Pt) : ℝ × ℝ := (val p.1, val p.2)

/-- **Soundness of the exact orientation**: `sgn (det p q)` is the sign of the real determinant
of the real points. -/
theorem det_real (p q : Pt) :
    val (det p q) = (rpt p).1 * (rpt q).2 - (rpt p).2 * (rpt q).1 := by
  simp only [det, rpt, val_sub, val_mul]

theorem inner_real (p q : Pt) :
    val (inner p q) = (rpt p).1 * (rpt q).1 + (rpt p).2 * (rpt q).2 := by
  simp only [inner, rpt, val_add, val_mul]

/-- `isSquareZ` is the real orthogonality of the two `Φ`-edge vectors. -/
theorem isSquareZ_real (z : Pt) (e f : V) :
    isSquareZ z e f = true ↔
      (rpt (PhiZ z (e, 0))).1 * (rpt (PhiZ z (0, f))).1 +
        (rpt (PhiZ z (e, 0))).2 * (rpt (PhiZ z (0, f))).2 = 0 := by
  rw [← inner_real, ← val_zero, val_inj]
  simp [isSquareZ]

/-- `isRh30Z` is the real identity `4⟨u,v⟩² = 3|u|²|v|²`. -/
theorem isRh30Z_real (z : Pt) (e f : V) :
    isRh30Z z e f = true ↔
      (let u := rpt (PhiZ z (e, 0)); let v := rpt (PhiZ z (0, f))
       4 * (u.1 * v.1 + u.2 * v.2) ^ 2 =
         3 * (u.1 * u.1 + u.2 * u.2) * (v.1 * v.1 + v.2 * v.2)) := by
  simp only [isRh30Z, decide_eq_true_eq]
  rw [← val_inj, val_mul, val_mul, val_mul, val_mul, inner_real, inner_real, inner_real]
  simp only [val]; push_cast; constructor <;> intro h <;> linear_combination h

/-- **Orientation clause over ℝ.** On every non-degenerate cell, the real determinants of the
`Φ`-edge vectors and of the `ψ`-edge vectors are nonzero with the same sign. -/
theorem lemma36_orient_real : ∀ i j : Fin 6, sgn (psiDet (U i) (U j)) ≠ 0 →
    0 < val (det (Phi (U i, 0)) (Phi (0, U j))) * val (psiDet (U i) (U j)) := by
  intro i j hd
  have ho := (lemma36 i j).2.2.2.2 hd
  simp only [orientPresZ, decide_eq_true_eq] at ho
  have h1 := sgn_sound (det (Phi (U i, 0)) (Phi (0, U j)))
  have h2 := sgn_sound (psiDet (U i) (U j))
  have hr : sgn (psiDet (U i) (U j)) = 1 ∨ sgn (psiDet (U i) (U j)) = -1 := by
    revert hd; generalize psiDet (U i) (U j) = x; intro hd
    simp only [sgn] at hd ⊢; split_ifs at hd ⊢ <;> simp_all
  rcases hr with h | h
  · exact mul_pos (h1.1 (ho.trans h)) (h2.1 h)
  · exact mul_pos_of_neg_of_neg (h1.2.1 (ho.trans h)) (h2.2.1 h)

end Q597Cells
