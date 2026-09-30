/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The metric criterion for a nonnegative symmetric `3 × 3` matrix

Formalises two results of `proofs/2026-09-29-c1-cylindric-lorentzian-ell3.tex`
(registry `cylindric-lorentzian`):

* `l3_det_reduction`  — Proposition `prop:reduction` of that file, registry node
  `l3-det-reduction`: a symmetric `3 × 3` matrix with nonnegative entries has at most one
  positive eigenvalue **iff** `e₂ ≤ 0` and `det ≥ 0`.
* `metric_criterion`  — Lemma `lem:metric` of that file, registry node `metric-criterion`:
  conditions (A) and (B) imply `e₂ ≤ 0`, `det ≥ 0`, and hence at most one positive eigenvalue.

Nothing here is transported or assumed: the matrix is a `Matrix (Fin 3) (Fin 3) ℝ` and its
eigenvalues are `Matrix.IsHermitian.eigenvalues`, i.e. Mathlib's, obtained from the spectral
theorem.  The bridge from the entries to the eigenvalues is `charpoly_eq_cubic` together with
`Matrix.IsHermitian.charpoly_eq`, so the elementary symmetric functions are *derived*, not
posited.

## Deviation from the paper proof

The paper closes Step 2 with "`g(ξ,η,ζ) = ξηζ - ξ - η - ζ + 2` is affine in each variable, hence
attains its minimum on `[0,1]³` at a vertex", and then evaluates at the vertices.  That is a real
lemma about multilinear functions on a box.  It is not needed: `cube_certificate` below gives the
explicit positivity certificate

`xyz + 2t³ - t²(x+y+z) = x(t-y)(t-z) + t(t-x)(t-y) + t(t-x)(t-z)`,

a `ring` identity whose three summands are products of nonnegatives.  This is strictly stronger
evidence than the vertex argument, since it exhibits the witness rather than quantifying over
extreme points.
-/

namespace TworowD4Kernel.MetricCriterion

open Matrix Polynomial

variable {M : Matrix (Fin 3) (Fin 3) ℝ}

/-- Second elementary symmetric function of a `3 × 3` matrix, as the sum of its three `2 × 2`
principal minors.  This is the paper's definition (Step 3 of `lem:metric`). -/
def e2 (M : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  (M 0 0 * M 1 1 - M 0 1 * M 1 0) + (M 0 0 * M 2 2 - M 0 2 * M 2 0)
    + (M 1 1 * M 2 2 - M 1 2 * M 2 1)

/-- Condition (A) of `def:AB`: `M i j ^ 2 ≥ M i i * M j j` off the diagonal. -/
def CondA (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j, i ≠ j → M i i * M j j ≤ M i j ^ 2

/-- Condition (B) of `def:AB`: `M i k * M k j ≥ M i j * M k k` for distinct `i, j, k`. -/
def CondB (M : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k → M i j * M k k ≤ M i k * M k j

/-- `M` has at most one positive eigenvalue.  Stated pairwise; `atMostOnePos_iff_card` proves
this is literally a cardinality bound, so the name carries no hidden content. -/
def AtMostOnePos (hM : M.IsHermitian) : Prop :=
  ∀ i j : Fin 3, 0 < hM.eigenvalues i → 0 < hM.eigenvalues j → i = j

theorem atMostOnePos_iff_card (hM : M.IsHermitian) :
    AtMostOnePos hM ↔ (Finset.univ.filter fun i => 0 < hM.eigenvalues i).card ≤ 1 := by
  rw [Finset.card_le_one]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, AtMostOnePos]
  tauto

/-! ### From the entries to the eigenvalues -/

theorem prod_three_eq_cubic (u v w : ℝ) :
    (X - C u) * (X - C v) * (X - C w)
      = X ^ 3 - C (u + v + w) * X ^ 2 + C (u * v + u * w + v * w) * X - C (u * v * w) := by
  simp only [map_add, map_mul]
  ring

/-- The characteristic polynomial of a `3 × 3` real matrix, coefficient by coefficient. -/
theorem charpoly_eq_cubic (M : Matrix (Fin 3) (Fin 3) ℝ) :
    M.charpoly = X ^ 3 - C M.trace * X ^ 2 + C (e2 M) * X - C M.det := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp only [charmatrix_apply_eq, charmatrix_apply_ne, ne_eq, show ¬(0 : Fin 3) = 1 by decide,
    show ¬(0 : Fin 3) = 2 by decide, show ¬(1 : Fin 3) = 0 by decide,
    show ¬(1 : Fin 3) = 2 by decide, show ¬(2 : Fin 3) = 0 by decide,
    show ¬(2 : Fin 3) = 1 by decide, not_false_eq_true]
  rw [Matrix.trace_fin_three, Matrix.det_fin_three]
  simp only [e2, map_add, map_sub, map_mul, map_neg]
  ring

/-- The three coefficients of a monic real cubic written in `e`-form. -/
theorem coeff_cubic (A B D : ℝ) :
    (X ^ 3 - C A * X ^ 2 + C B * X - C D).coeff 2 = -A ∧
    (X ^ 3 - C A * X ^ 2 + C B * X - C D).coeff 1 = B ∧
    (X ^ 3 - C A * X ^ 2 + C B * X - C D).coeff 0 = -D := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [coeff_one, coeff_C, coeff_X, coeff_X_pow]

/-- The three elementary symmetric functions of the entries agree with those of Mathlib's
eigenvalues.  This is the whole bridge, and it is derived from
`Matrix.IsHermitian.charpoly_eq` (the spectral theorem), not assumed. -/
theorem trace_e2_det_eq_eigen (hM : M.IsHermitian) :
    M.trace = hM.eigenvalues 0 + hM.eigenvalues 1 + hM.eigenvalues 2 ∧
    e2 M = hM.eigenvalues 0 * hM.eigenvalues 1 + hM.eigenvalues 0 * hM.eigenvalues 2
             + hM.eigenvalues 1 * hM.eigenvalues 2 ∧
    M.det = hM.eigenvalues 0 * hM.eigenvalues 1 * hM.eigenvalues 2 := by
  have h := hM.charpoly_eq
  rw [Fin.prod_univ_three, charpoly_eq_cubic] at h
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h
  rw [prod_three_eq_cubic] at h
  obtain ⟨l2, l1, l0⟩ := coeff_cubic M.trace (e2 M) M.det
  obtain ⟨r2, r1, r0⟩ := coeff_cubic (hM.eigenvalues 0 + hM.eigenvalues 1 + hM.eigenvalues 2)
    (hM.eigenvalues 0 * hM.eigenvalues 1 + hM.eigenvalues 0 * hM.eigenvalues 2
      + hM.eigenvalues 1 * hM.eigenvalues 2)
    (hM.eigenvalues 0 * hM.eigenvalues 1 * hM.eigenvalues 2)
  refine ⟨?_, ?_, ?_⟩
  · have e := l2.symm.trans (h ▸ r2); linarith
  · have e := l1.symm.trans (h ▸ r1); linarith
  · have e := l0.symm.trans (h ▸ r0); linarith

/-! ### `l3-det-reduction` -/

/-- Step 4 converse (Proposition `prop:reduction`, `⇒`), as pure algebra.  If at least two of
`u, v, w` are nonpositive and `u + v + w ≥ 0`, then `e₂ ≤ 0` and the product is `≥ 0`.
This is the paper's `e₂ ≤ -(v² + vw + w²) ≤ 0` computation. -/
theorem e2_nonpos_det_nonneg {u v w : ℝ} (htr : 0 ≤ u + v + w) (hv : v ≤ 0) (hw : w ≤ 0) :
    u * v + u * w + v * w ≤ 0 ∧ 0 ≤ u * v * w := by
  have hu : 0 ≤ u := by linarith
  have hvw : 0 ≤ v * w := by
    nlinarith [mul_nonneg (neg_nonneg.mpr hv) (neg_nonneg.mpr hw)]
  refine ⟨?_, by rw [mul_assoc]; exact mul_nonneg hu hvw⟩
  nlinarith [mul_nonneg htr (by linarith : (0:ℝ) ≤ -(v + w)), hvw, sq_nonneg v, sq_nonneg w]

/-- Step 4 of `lem:metric`, as pure algebra: `e₂ ≤ 0` and `det ≥ 0` forbid two positive
eigenvalues.  All three variables explicit, so that each of the six orderings of a pair of
positive eigenvalues can be discharged by it. -/
theorem no_two_pos (u v w : ℝ) (he : u * v + u * w + v * w ≤ 0) (hd : 0 ≤ u * v * w)
    (hu : 0 < u) (hv : 0 < v) : False := by
  have hw : 0 ≤ w := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos hu hv]
  nlinarith [mul_pos hu hv, mul_nonneg hw hu.le, mul_nonneg hw hv.le]

/-- **Proposition `prop:reduction`** (registry node `l3-det-reduction`).  A symmetric `3 × 3`
real matrix with nonnegative entries has at most one positive eigenvalue if and only if
`e₂ M ≤ 0` and `det M ≥ 0`.

Nonnegativity of the entries is used **only** through `0 ≤ M.trace`, which is what the
hypothesis is weakened to here; see `l3_det_reduction` for the stated form. -/
theorem l3_det_reduction_trace (hM : M.IsHermitian) (htr : 0 ≤ M.trace) :
    AtMostOnePos hM ↔ (e2 M ≤ 0 ∧ 0 ≤ M.det) := by
  obtain ⟨htr', he2, hdet⟩ := trace_e2_det_eq_eigen hM
  rw [htr'] at htr
  set u := hM.eigenvalues 0
  set v := hM.eigenvalues 1
  set w := hM.eigenvalues 2
  rw [he2, hdet]
  constructor
  · intro h
    -- (⇒) at most one positive, plus `tr ≥ 0`: at least two eigenvalues are `≤ 0`.
    have h01 : ¬(0 < u ∧ 0 < v) := fun ⟨a, b⟩ => by simpa using h 0 1 a b
    have h02 : ¬(0 < u ∧ 0 < w) := fun ⟨a, b⟩ => by simpa using h 0 2 a b
    have h12 : ¬(0 < v ∧ 0 < w) := fun ⟨a, b⟩ => by simpa using h 1 2 a b
    rcases le_or_gt u 0 with hu | hu
    · rcases le_or_gt v 0 with hv | hv
      · obtain ⟨A, B⟩ := e2_nonpos_det_nonneg (u := w) (v := u) (w := v) (by linarith) hu hv
        exact ⟨by linarith, by linarith⟩
      · have hw : w ≤ 0 := by by_contra hc; exact h12 ⟨hv, lt_of_not_ge hc⟩
        obtain ⟨A, B⟩ := e2_nonpos_det_nonneg (u := v) (v := u) (w := w) (by linarith) hu hw
        exact ⟨by linarith, by linarith⟩
    · have hv : v ≤ 0 := by by_contra hc; exact h01 ⟨hu, lt_of_not_ge hc⟩
      have hw : w ≤ 0 := by by_contra hc; exact h02 ⟨hu, lt_of_not_ge hc⟩
      exact e2_nonpos_det_nonneg (u := u) (v := v) (w := w) (by linarith) hv hw
  · -- (⇐) Step 4 of `lem:metric`.
    rintro ⟨he, hd⟩ i j hi hj
    by_contra hij
    -- two distinct positive eigenvalues; the third is forced `≥ 0` by `det ≥ 0`, so `e₂ > 0`.
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, ne_eq, not_true_eq_false] at hi hj hij ⊢ <;>
      first
        | exact hij rfl
        | exact no_two_pos u v w he hd hi hj
        | exact no_two_pos u w v (by linarith) (by linarith) hi hj
        | exact no_two_pos v u w (by linarith) (by linarith) hi hj
        | exact no_two_pos v w u (by linarith) (by linarith) hi hj
        | exact no_two_pos w u v (by linarith) (by linarith) hi hj
        | exact no_two_pos w v u (by linarith) (by linarith) hi hj

/-- `l3-det-reduction` in the stated form: nonnegative entries. -/
theorem l3_det_reduction (hM : M.IsHermitian) (hnn : ∀ i j, 0 ≤ M i j) :
    AtMostOnePos hM ↔ (e2 M ≤ 0 ∧ 0 ≤ M.det) := by
  refine l3_det_reduction_trace hM ?_
  rw [Matrix.trace_fin_three]
  have := hnn 0 0; have := hnn 1 1; have := hnn 2 2
  linarith

/-! ### `metric-criterion` -/

/-- The algebraic core of Step 2, replacing the paper's "affine in each variable, hence minimised
at a vertex of `[0,1]³`" by an explicit positivity certificate. -/
theorem cube_certificate {x y z t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hxt : x ≤ t) (hyt : y ≤ t) (hzt : z ≤ t) :
    0 ≤ x * y * z + 2 * t ^ 3 - t ^ 2 * (x + y + z) := by
  have ht : 0 ≤ t := hx.trans hxt
  have key : x * y * z + 2 * t ^ 3 - t ^ 2 * (x + y + z)
      = x * ((t - y) * (t - z)) + t * ((t - x) * (t - y)) + t * ((t - x) * (t - z)) := by ring
  rw [key]
  have h1 : 0 ≤ x * ((t - y) * (t - z)) :=
    mul_nonneg hx (mul_nonneg (by linarith) (by linarith))
  have h2 : 0 ≤ t * ((t - x) * (t - y)) :=
    mul_nonneg ht (mul_nonneg (by linarith) (by linarith))
  have h3 : 0 ≤ t * ((t - x) * (t - z)) :=
    mul_nonneg ht (mul_nonneg (by linarith) (by linarith))
  linarith

/-- Steps 1 and 2 of `lem:metric`, as pure algebra in the six independent entries
`a = M₁₁, b = M₂₂, c = M₃₃, p = M₂₃, q = M₁₃, r = M₁₂`.  The conclusion is
`det M = P + 2t - x - y - z ≥ 0`.  Condition (A) enters **only** in the degenerate branch
`t = 0`, exactly as the paper's remark after the proof claims. -/
theorem det_nonneg_alg {a b c p q r : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hA1 : a * b ≤ r ^ 2) (hA2 : a * c ≤ q ^ 2) (hA3 : b * c ≤ p ^ 2)
    (hB1 : p * a ≤ r * q) (hB2 : q * b ≤ r * p) (hB3 : r * c ≤ q * p) :
    0 ≤ a * b * c + 2 * (p * q * r) - a * p ^ 2 - b * q ^ 2 - c * r ^ 2 := by
  have ht : 0 ≤ p * q * r := by positivity
  -- Step 1: (B) multiplied through by a nonnegative off-diagonal entry gives `x, y, z ≤ t`.
  have hx : a * p ^ 2 ≤ p * q * r := by nlinarith [mul_le_mul_of_nonneg_left hB1 hp]
  have hy : b * q ^ 2 ≤ p * q * r := by nlinarith [mul_le_mul_of_nonneg_left hB2 hq]
  have hz : c * r ^ 2 ≤ p * q * r := by nlinarith [mul_le_mul_of_nonneg_left hB3 hr]
  rcases ht.eq_or_lt with ht0 | ht0
  · -- `t = 0`: (B1)–(B3) force `x = y = z = 0`, and (A) multiplied out forces `P = 0`.
    have hx0 : a * p ^ 2 ≤ 0 := by linarith
    have hy0 : b * q ^ 2 ≤ 0 := by linarith
    have hz0 : c * r ^ 2 ≤ 0 := by linarith
    have hprod : a * b * (a * c * (b * c)) ≤ r ^ 2 * (q ^ 2 * p ^ 2) :=
      mul_le_mul hA1 (mul_le_mul hA2 hA3 (by positivity) (by positivity)) (by positivity)
        (by positivity)
    have htsq : r ^ 2 * (q ^ 2 * p ^ 2) = 0 := by linear_combination (-(p * q * r)) * ht0
    have h2 : (a * b * c) ^ 2 ≤ 0 := by nlinarith [hprod, htsq]
    have habc : a * b * c = 0 := by
      have h3 : (a * b * c) ^ 2 = 0 := le_antisymm h2 (sq_nonneg _)
      exact sq_eq_zero_iff.mp h3
    nlinarith [mul_nonneg (mul_nonneg ha hp) hp, mul_nonneg (mul_nonneg hb hq) hq,
      mul_nonneg (mul_nonneg hc hr) hr]
  · -- `t > 0`: the certificate, after multiplying by `t² > 0`.
    have hcert := cube_certificate (x := a * p ^ 2) (y := b * q ^ 2) (z := c * r ^ 2)
      (t := p * q * r) (by positivity) (by positivity) (by positivity) hx hy hz
    nlinarith [hcert, mul_pos ht0 ht0]

/-- **Lemma `lem:metric`** (registry node `metric-criterion`).  A symmetric `3 × 3` real matrix
with nonnegative entries satisfying (A) and (B) has `e₂ ≤ 0`, `det ≥ 0`, and therefore at most
one positive eigenvalue. -/
theorem metric_criterion (hM : M.IsHermitian) (hnn : ∀ i j, 0 ≤ M i j)
    (hA : CondA M) (hB : CondB M) :
    e2 M ≤ 0 ∧ 0 ≤ M.det ∧ AtMostOnePos hM := by
  have hsym : ∀ i j, M j i = M i j := fun i j => hM.apply i j
  -- Step 3: (A) makes each `2 × 2` principal minor nonpositive.
  have he2 : e2 M ≤ 0 := by
    have h01 := hA 0 1 (by decide)
    have h02 := hA 0 2 (by decide)
    have h12 := hA 1 2 (by decide)
    simp only [e2]
    rw [hsym 0 1, hsym 0 2, hsym 1 2]
    nlinarith [h01, h02, h12]
  -- Steps 1–2 via `det_nonneg_alg`.
  have hdet : 0 ≤ M.det := by
    rw [Matrix.det_fin_three, hsym 0 1, hsym 0 2, hsym 1 2]
    have := det_nonneg_alg (a := M 0 0) (b := M 1 1) (c := M 2 2) (p := M 1 2) (q := M 0 2)
      (r := M 0 1) (hnn 0 0) (hnn 1 1) (hnn 2 2) (hnn 1 2) (hnn 0 2) (hnn 0 1)
      (hA 0 1 (by decide)) (hA 0 2 (by decide)) (hA 1 2 (by decide))
      (by have := hB 1 2 0 (by decide) (by decide) (by decide)
          rw [hsym 0 1] at this; linarith [this])
      (by have := hB 0 2 1 (by decide) (by decide) (by decide)
          linarith [this])
      (by have := hB 0 1 2 (by decide) (by decide) (by decide)
          rw [hsym 1 2] at this; linarith [this])
    linarith [this]
  exact ⟨he2, hdet, (l3_det_reduction hM hnn).mpr ⟨he2, hdet⟩⟩

/-! ### Negative controls

These exist because an implication is passed identically by a vacuous hypothesis set.  Each
witness below is re-derived here rather than copied: the arithmetic is `norm_num`, not a
transcription of the numbers recorded in the registry. -/

/-- The witness of the `rlc-implies-l3` dead end (registry `cylindric-lorentzian`). -/
def W : Matrix (Fin 3) (Fin 3) ℝ := !![4, 6, 4; 6, 1, 4; 4, 4, 4]

theorem W_isHermitian : W.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [W]

theorem W_nonneg : ∀ i j, 0 ≤ W i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [W]

theorem W_condA : CondA W := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | norm_num [W]

theorem W_det : W.det = -16 := by
  rw [Matrix.det_fin_three]; norm_num [W, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const]

/-- **(A) alone does not suffice.**  `W` is symmetric with nonnegative entries and satisfies (A),
yet has more than one positive eigenvalue.  Note the route: this is derived from the `⇒`
direction of `l3_det_reduction` together with `det W < 0`, so it needs no eigenvalue
computation — and it is therefore also a live test of that direction of the iff. -/
theorem condA_not_sufficient : ¬ AtMostOnePos W_isHermitian := by
  intro h
  have hd := ((l3_det_reduction W_isHermitian W_nonneg).mp h).2
  rw [W_det] at hd
  norm_num at hd

/-- `W` fails (B) at `(i, j, k) = (0, 1, 2)`: `W 0 2 * W 2 1 = 16 < 24 = W 0 1 * W 2 2`.
So (B) is exactly the hypothesis whose absence produced the recorded counterexample. -/
theorem W_not_condB : ¬ CondB W := by
  intro h
  have := h 0 1 2 (by decide) (by decide) (by decide)
  norm_num [W, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const] at this

/-! **Not formalised, recorded as owed.**  Two controls the brief asks for are *not* Lean
theorems here, and neither is asserted anywhere in this file:

1. *Nonnegativity of the entries is load-bearing.*  It enters only through `0 ≤ M.trace`
   (`l3_det_reduction_trace` isolates exactly that), and `M = -(1 : Matrix (Fin 3) (Fin 3) ℝ)`
   shows the `⇒` direction fails without it: no positive eigenvalue, yet `e₂ = 3 > 0` and
   `det = -1 < 0`.  The `e₂` and `det` values are arithmetic; the step "`-1` has no positive
   eigenvalue" was not formalised (it needs the eigenvalues of a diagonal matrix, which this
   file never computes).  Checked numerically only.

2. *The `3 × 3`-ness is load-bearing.*  `metric_criterion` is false at `ℓ = 4`:
   `!![3,6,2,6; 6,0,1,4; 2,1,0,4; 6,4,4,1]` satisfies (A) and (B) with nonnegative entries and
   has two positive eigenvalues (spectrum `≈ {13.493, 0.081, -4.574, -5}`).  Verified in Python
   only.  Formalising it needs "a `2`-dimensional positive subspace forces two positive
   eigenvalues" — Cauchy interlacing / min-max — which is not in reach of this file, and the
   `det`/`e₂` criterion cannot substitute because that criterion is itself `3 × 3`-only.
   So the *statement* `metric-criterion-general-ell` remains refuted by computation, not by Lean.
-/

end TworowD4Kernel.MetricCriterion
