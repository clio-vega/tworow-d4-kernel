/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# The collapse multiplier and its level set

Formalisation of the algebraic core of Proposition `prop:rhoXminus1` and
Theorem `thm:dict` of
`projects/proofs/2026-10-17-typeB-multiplier-and-boundary-entry.tex`
(commit `e347ed3`, L410--L455).

## The object

In both type `B` and type `C`, the multiplier by which the restriction to the
hyperplane `H_ab = {w_a w_b = 1}` fails to be a *coboundary* is

    ρ^X = (1-q)^2 / ((1 - q w_a^h) (1 - q w_b^h)),

with `h = 1` in type `B` (short roots) and `h = 2` in type `C` (long roots);
on `H` one has `w_b = w_a^{-1}`, so `w_b^h = (w_a^h)^{-1}`.  Writing
`t := w_a^h` for the single relevant variable, the object formalised here is

    rho q t = (1-q)^2 / ((1 - q*t) * (1 - q*t⁻¹)).

The paper's `ρ^X` is `rho q (w^h)` with `h` the root-length parameter; the
type dependence of the locus is therefore **entirely** the `h`-dependence of
`{w : w^h = 1}`, which is the content of `rho_eq_one_iff_pow` below.

## Main results

* `rho_sub_one` — Proposition `prop:rhoXminus1`: `ρ - 1 = q t (1 - t⁻¹)^2 / D`,
  i.e. the numerator of `ρ - 1` is `q (t + t⁻¹ - 2) = q t⁻¹ (t-1)^2`.
* `rho_eq_one_iff` — the level set: `ρ = 1 ↔ q = 0 ∨ t = 1`.
* `rho_eq_one_iff_pow`, `rho_eq_one_iff_mem_rootsOfUnity` — the same with
  `t = w ^ h`, the second phrased via Mathlib's `rootsOfUnity`.
* `rho_eq_one_iff_typeB` (`h = 1`) and `rho_eq_one_iff_typeC` (`h = 2`) — the
  paper's table.  The type-`C` statement needs `(2 : K) ≠ 0`: in
  characteristic `2` the two loci coincide and the paper's discriminating
  measurement at `w_a = -1` collapses.

## Note on the hypotheses

`t ≠ 0` is *not* removable, even though Lean's `t⁻¹` is total: at `t = 0` the
Lean expression `rho q 0` is `(1-q)^2`, which equals `1` also at `q = 2`.
See `rho_eq_one_iff_lesion_t_ne_zero` for that counterexample, recorded as a
theorem.
-/

namespace TworowD4Kernel
namespace CollapseMultiplier

variable {K : Type*} [Field K]

/-- The collapse multiplier `ρ = (1-q)^2 / ((1 - q t)(1 - q t⁻¹))`, with
`t = w_a^h` the root-length power of the boundary spectral parameter.  Paper
`eq:rhoX` / `eq:rhoB`. -/
noncomputable def rho (q t : K) : K := (1 - q) ^ 2 / ((1 - q * t) * (1 - q * t⁻¹))

/-- **Proposition `prop:rhoXminus1`.**  The obstruction `ρ - 1`, with its
numerator in factored form.  The paper's proof is the one-line identity
`(1-q)^2 - (1-qt)(1-qt⁻¹) = q(t + t⁻¹ - 2) = q t⁻¹ (t-1)^2`; the form below
clears `t⁻¹` from the front so that the square is visible. -/
theorem rho_sub_one (q t : K) (ht : t ≠ 0) (hd1 : 1 - q * t ≠ 0)
    (hd2 : 1 - q * t⁻¹ ≠ 0) :
    rho q t - 1 = q * t * (1 - t⁻¹) ^ 2 / ((1 - q * t) * (1 - q * t⁻¹)) := by
  have hqt : t - q ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hd2 (by rw [← h, mul_inv_cancel₀ ht, sub_self])
  unfold rho
  field_simp
  ring

/-- **The level set.**  `ρ = 1` exactly on `{q = 0} ∪ {t = 1}`.  This is the
"in particular" of Theorem `thm:dict`: the zero locus of the obstruction. -/
theorem rho_eq_one_iff (q t : K) (ht : t ≠ 0) (hd1 : 1 - q * t ≠ 0)
    (hd2 : 1 - q * t⁻¹ ≠ 0) :
    rho q t = 1 ↔ q = 0 ∨ t = 1 := by
  rw [← sub_eq_zero, rho_sub_one q t ht hd1 hd2,
    div_eq_zero_iff, mul_eq_zero, mul_eq_zero, pow_eq_zero_iff (n := 2) (by norm_num),
    sub_eq_zero]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact absurd h ht
    · exact Or.inr (by rw [eq_comm, inv_eq_one] at h; exact h)
    · exact absurd h (mul_ne_zero hd1 hd2)
  · rintro (h | h)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inr (by rw [h, inv_one]))

/-! ### The boundary entry: `thm:dict` proper -/

/-- The charge-violating entry `[K^X(u)]_0^{\,1}` of Motegi's `K`-matrix,
`eq:Kentries` of the paper (L431--L455), quoting Motegi arXiv:2610.15344:

    [K^C(u)]_0^1 = 1 - u^{-2}   (long roots,  h = 2),
    [K^B(u)]_0^1 = 1 - u^{-1}   (short roots, h = 1),

uniformly `1 - u^{-h}`.  The identification of this expression with the
`K`-matrix entry is external input (Motegi), not formalised here; what is
formalised is that this expression is exactly the square root of the
obstruction's numerator. -/
noncomputable def Kentry (h : ℕ) (u : K) : K := 1 - (u ^ h) ⁻¹

/-- **Theorem `thm:dict`** (paper L431--L442): the obstruction `ρ^X - 1` is
`q w_a^h` times the *square of the charge-violating boundary entry*, over the
same denominator.

Note what the proof is: this is `rho_sub_one` at `t = w ^ h`, with no further
work — once `Kentry` is written out, the two statements are the same
expression.  That is the honest content of the dictionary.  The mathematical
claim being certified is the *coincidence*, and the coincidence is visible only
because `Kentry` was defined from Motegi's source and not reverse-engineered
from the numerator. -/
theorem rho_sub_one_eq_Kentry_sq (q w : K) (h : ℕ) (hw : w ≠ 0)
    (hd1 : 1 - q * w ^ h ≠ 0) (hd2 : 1 - q * (w ^ h)⁻¹ ≠ 0) :
    rho q (w ^ h) - 1 =
      q * w ^ h * Kentry h w ^ 2 / ((1 - q * w ^ h) * (1 - q * (w ^ h)⁻¹)) :=
  rho_sub_one q (w ^ h) (pow_ne_zero h hw) hd1 hd2

/-- Paper `prop:rhoXminus1`, the explicit type-`C` numerator: `q(w - w⁻¹)^2`. -/
theorem numerator_typeC (q w : K) (hw : w ≠ 0) :
    q * w ^ 2 * Kentry 2 w ^ 2 = q * (w - w⁻¹) ^ 2 := by
  rw [Kentry]
  field_simp

/-- Paper `prop:rhoXminus1`, the explicit type-`B` numerator: `q(w + w⁻¹ - 2)`.
This is `q w⁻¹ (w-1)^2`, so it vanishes **only** at `w = 1` — whereas the
type-`C` numerator `q(w - w⁻¹)^2` vanishes at `w = ±1`.  That asymmetry is the
whole discriminating content of the paper. -/
theorem numerator_typeB (q w : K) (hw : w ≠ 0) :
    q * w ^ 1 * Kentry 1 w ^ 2 = q * (w + w⁻¹ - 2) := by
  rw [Kentry]
  field_simp
  ring

/-! ### The level set in `w`, where the type dependence lives -/

/-- **Theorem `thm:dict`, the locus.**  Substituting `t = w ^ h` (`h = 1` in
type `B`, `h = 2` in type `C`): the collapse locus of `ρ` is
`{q = 0} ∪ μ_h`, the `h`-th roots of unity in `w`.

No hypothesis `h ≠ 0` is needed: at `h = 0` both sides are unconditionally
true (`w ^ 0 = 1` forces `t = 1`, hence `ρ = 1`).  The brief listed `h ≠ 0`
as a hypothesis to lesion; it is not present, so the stronger statement is
recorded directly. -/
theorem rho_eq_one_iff_pow (q w : K) (h : ℕ) (hw : w ≠ 0)
    (hd1 : 1 - q * w ^ h ≠ 0) (hd2 : 1 - q * (w ^ h)⁻¹ ≠ 0) :
    rho q (w ^ h) = 1 ↔ q = 0 ∨ w ^ h = 1 :=
  rho_eq_one_iff q (w ^ h) (pow_ne_zero h hw) hd1 hd2

/-- The same statement with `μ_h` named as Mathlib's `rootsOfUnity h K`, for a
unit `w : Kˣ`.  Membership is `mem_rootsOfUnity'`. -/
theorem rho_eq_one_iff_mem_rootsOfUnity (q : K) (w : Kˣ) (h : ℕ)
    (hd1 : 1 - q * (w : K) ^ h ≠ 0) (hd2 : 1 - q * ((w : K) ^ h)⁻¹ ≠ 0) :
    rho q ((w : K) ^ h) = 1 ↔ q = 0 ∨ w ∈ rootsOfUnity h K := by
  rw [rho_eq_one_iff_pow q (w : K) h w.ne_zero hd1 hd2, mem_rootsOfUnity']

/-! ### The paper's table -/

/-- **Type `B`, `h = 1`** (short roots): the locus is `{q = 0} ∪ {w = 1}`. -/
theorem rho_eq_one_iff_typeB (q w : K) (hw : w ≠ 0) (hd1 : 1 - q * w ≠ 0)
    (hd2 : 1 - q * w⁻¹ ≠ 0) :
    rho q w = 1 ↔ q = 0 ∨ w = 1 :=
  rho_eq_one_iff q w hw hd1 hd2

/-- **Type `C`, `h = 2`** (long roots): the locus is `{q = 0} ∪ {w = ±1}`.

This statement needs **no** characteristic hypothesis: in characteristic `2`
the disjunct `w = -1` is simply the same as `w = 1`, and the equivalence stays
true.  The characteristic enters only when the two types' loci are *separated*
— see `typeC_collapses_typeB_does_not_at_neg_one`. -/
theorem rho_eq_one_iff_typeC (q w : K) (hw : w ≠ 0) (hd1 : 1 - q * w ^ 2 ≠ 0)
    (hd2 : 1 - q * (w ^ 2)⁻¹ ≠ 0) :
    rho q (w ^ 2) = 1 ↔ q = 0 ∨ w = 1 ∨ w = -1 := by
  rw [rho_eq_one_iff_pow q w 2 hw hd1 hd2, pow_two, mul_self_eq_one_iff]

/-- **The discriminating measurement.**  At `w_a = -1` the type-`C` multiplier
collapses to `1` and the type-`B` multiplier does not.  This is the
disagreement set of the two readings (paper L91--L92), and it is exactly where
`(2 : K) ≠ 0` is real content: in characteristic `2` one has `-1 = 1`, the two
loci coincide, and the measurement carries no information. -/
theorem typeC_collapses_typeB_does_not_at_neg_one (q : K) (h2 : (2 : K) ≠ 0)
    (hq : q ≠ 0) (hd : 1 - q * (-1 : K) ≠ 0) (hd' : 1 - q ≠ 0) :
    rho q ((-1 : K) ^ 2) = 1 ∧ rho q (-1 : K) ≠ 1 := by
  have hne : (-1 : K) ≠ 1 := fun h => h2 (by rw [show (2 : K) = 1 - (-1) by ring, h, sub_self])
  refine ⟨?_, ?_⟩
  · rw [rho_eq_one_iff_typeC q (-1) (neg_ne_zero.mpr one_ne_zero) ?_ ?_]
    · exact Or.inr (Or.inr rfl)
    · simpa using hd'
    · simpa using hd'
  · intro hc
    rw [rho_eq_one_iff q (-1) (neg_ne_zero.mpr one_ne_zero) hd
      (by simpa using hd)] at hc
    exact hc.elim hq hne

/-! ### Two evaluations of `rho`

Both are used below to show that hypotheses are not removable. -/

/-- `ρ = 1` identically at `q = 0`: the first disjunct of the level set, as a
value and not just as a membership. -/
@[simp] theorem rho_zero (t : K) : rho 0 t = 1 := by
  simp [rho]

/-- `ρ = 1` at `t = 1`: the second disjunct.  Needs `1 - q ≠ 0`, since
otherwise Lean's `0 / 0 = 0`. -/
theorem rho_one (q : K) (hq : 1 - q ≠ 0) : rho q 1 = 1 := by
  rw [rho]
  rw [inv_one, mul_one, ← pow_two]
  exact div_self (pow_ne_zero 2 hq)

/-! ### Lesions

The brief requires each hypothesis to be deleted once.  A deleted binder makes
the stored proof fail with `Unknown identifier`, which grades the *script*, not
the statement, so every lesion below is instead settled by a **compiled
counterexample** (for the irremovable ones) or by a **re-proof without the
hypothesis** (for the removable one).  Four hypotheses are irremovable, one is
free. -/

/-- Lesion of `ht : t ≠ 0` in `rho_sub_one`: **irremovable**.  At `t = 0`
Lean's `t⁻¹` is `0`, the right-hand side collapses to `0`, and the left-hand
side is `(1-q)^2 - 1`, nonzero at `q = 3`.  Both denominator hypotheses hold
at this point, so the lesion is isolated. -/
theorem rho_sub_one_needs_ht :
    (1 - (3 : ℚ) * 0 ≠ 0) ∧ (1 - (3 : ℚ) * (0 : ℚ)⁻¹ ≠ 0) ∧
      rho (3 : ℚ) 0 - 1 ≠ 3 * 0 * (1 - (0 : ℚ)⁻¹) ^ 2 / ((1 - 3 * 0) * (1 - 3 * (0 : ℚ)⁻¹)) := by
  refine ⟨by norm_num, by norm_num, by norm_num [rho]⟩

/-- Lesion of `hd1 : 1 - q * t ≠ 0` in `rho_sub_one`: **irremovable**.  At
`q = 1/2`, `t = 2` the first denominator factor vanishes, so the right-hand
side is `0` while `ρ - 1 = -1`.  `ht` and `hd2` both hold here. -/
theorem rho_sub_one_needs_hd1 :
    ((2 : ℚ) ≠ 0) ∧ (1 - (2⁻¹ : ℚ) * (2 : ℚ)⁻¹ ≠ 0) ∧
      rho (2⁻¹ : ℚ) 2 - 1 ≠
        2⁻¹ * 2 * (1 - (2 : ℚ)⁻¹) ^ 2 / ((1 - 2⁻¹ * 2) * (1 - 2⁻¹ * (2 : ℚ)⁻¹)) := by
  refine ⟨by norm_num, by norm_num, by norm_num [rho]⟩

/-- Lesion of `hd2 : 1 - q * t⁻¹ ≠ 0` in `rho_sub_one`: **irremovable**.  The
second factor vanishes exactly when `q = t`; at `q = t = 2` the right-hand side
is `0` and `ρ - 1 = -1`.  `ht` and `hd1` both hold here. -/
theorem rho_sub_one_needs_hd2 :
    ((2 : ℚ) ≠ 0) ∧ (1 - (2 : ℚ) * 2 ≠ 0) ∧
      rho (2 : ℚ) 2 - 1 ≠
        2 * 2 * (1 - (2 : ℚ)⁻¹) ^ 2 / ((1 - 2 * 2) * (1 - (2 : ℚ) * (2 : ℚ)⁻¹)) := by
  refine ⟨by norm_num, by norm_num, by norm_num [rho]⟩

/-- Lesion of `ht : t ≠ 0` in `rho_eq_one_iff`: **irremovable**.  `rho q 0` is
`(1-q)^2`, which is `1` at `q = 2` while neither `q = 0` nor `t = 1`.  Both
denominator hypotheses hold at this point. -/
theorem rho_eq_one_iff_needs_ht :
    (1 - (2 : ℚ) * 0 ≠ 0) ∧ (1 - (2 : ℚ) * (0 : ℚ)⁻¹ ≠ 0) ∧
      (rho (2 : ℚ) 0 = 1 ∧ ¬((2 : ℚ) = 0 ∨ (0 : ℚ) = 1)) := by
  refine ⟨by norm_num, by norm_num, by norm_num [rho], by norm_num⟩

/-- Lesion of `hd1 : 1 - q * t ≠ 0` in `rho_eq_one_iff`: **irremovable**.  At
`q = t = 1` the denominator vanishes, Lean's division makes `ρ = 0 ≠ 1`, while
`t = 1` makes the right-hand side true: the equivalence fails rightward.  Note
`hd2` also vanishes here — and it has to, by
`rho_eq_one_iff_of_hd1`, which shows `hd2` alone is removable. -/
theorem rho_eq_one_iff_needs_hd1 :
    ((1 : ℚ) ≠ 0) ∧ (rho (1 : ℚ) 1 ≠ 1 ∧ ((1 : ℚ) = 0 ∨ (1 : ℚ) = 1)) := by
  refine ⟨by norm_num, by norm_num [rho], by norm_num⟩

/-- Lesion of `hd2 : 1 - q * t⁻¹ ≠ 0` in `rho_eq_one_iff`: **removable**, a
stronger theorem for free.

Given `ht` and `hd1`, the hypothesis `hd2` follows from either side of the
equivalence being inhabited: if the second denominator factor vanishes then
`ρ = 0 ≠ 1` *and* the right-hand side is false (`q = 0` would give
`1 - q t⁻¹ = 1`, and `t = 1` would give `1 - q t⁻¹ = 1 - q t`, contradicting
`hd1`), so the equivalence holds for the trivial reason.  Hence `hd2` was never
spent. -/
theorem rho_eq_one_iff_of_hd1 (q t : K) (ht : t ≠ 0) (hd1 : 1 - q * t ≠ 0) :
    rho q t = 1 ↔ q = 0 ∨ t = 1 := by
  by_cases hd2 : 1 - q * t⁻¹ = 0
  · have hrho : rho q t = 0 := by rw [rho, hd2, mul_zero, div_zero]
    constructor
    · rw [hrho]; exact fun h => absurd h.symm one_ne_zero
    · rintro (h | h)
      · rw [h] at hd2; simp at hd2
      · rw [h, inv_one, mul_one] at hd2
        rw [h, mul_one] at hd1
        exact absurd hd2 hd1
  · exact rho_eq_one_iff q t ht hd1 hd2

/-- Lesion of `h2 : (2 : K) ≠ 0` in
`typeC_collapses_typeB_does_not_at_neg_one`: **irremovable**, and the reason is
mathematical rather than incidental.  In characteristic `2`, `-1 = 1`, so the
type-`B` multiplier *also* collapses at `w_a = -1`: the two types' loci
coincide and the paper's discriminating measurement carries no information.

Stated in generality rather than by exhibiting a concrete characteristic-`2`
field, because in `𝔽₂` the hypotheses `q ≠ 0` and `1 - q ≠ 0` are jointly
unsatisfiable and the counterexample would need `𝔽₄`. -/
theorem typeB_also_collapses_at_neg_one_of_char_two (q : K) (h2 : (2 : K) = 0)
    (hq : 1 - q ≠ 0) : rho q (-1 : K) = 1 := by
  have hne : (-1 : K) = 1 := by
    rw [show (-1 : K) = 1 - 2 by ring, h2, sub_zero]
  rw [hne]
  exact rho_one q hq

/-- Lesion of `hq : q ≠ 0` in `typeC_collapses_typeB_does_not_at_neg_one`:
**irremovable**.  At `q = 0` the multiplier is identically `1` by `rho_zero`,
so the type-`B` factor does not fail to collapse either.  `q = 0` is the other
component of the level set. -/
theorem typeB_also_collapses_at_neg_one_of_q_zero :
    rho (0 : K) (-1 : K) = 1 := rho_zero _

end CollapseMultiplier
end TworowD4Kernel
