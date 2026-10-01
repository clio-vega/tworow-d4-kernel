/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Finprod
import TworowD4Kernel.DiscreteConcavity

/-!
# Convolution on `ℤ` and the trapezoid formula

Closes the first gap listed in the "What is NOT formalised" section of
`TworowD4Kernel/DiscreteConcavity.lean`.

`prop:regII` of `proofs/2026-09-30-c1-cylindric-kostka-logconcavity.tex` (l.376) is a claim
about the function

  `G(s) = ∑_{t ∈ T} (1_[a_t,b_t] * 1_[c_t,d_t]) (s)`           (eq:G, l.263)

and it *derives* the trapezoid formula

  `(1_[a,b] * 1_[c,d]) (s) = min (s-ℓ+1, h-s+1, n_t, m_t)_+`    (l.394)

from the convolution.  In `DiscreteConcavity.lean` the function `GR` is *defined* by that
right-hand side, so `GR_PFtwo` there is a theorem about a formula, not about a convolution.
This file defines the convolution, proves the formula, and re-derives `GR` from it, so that
`sum_conv_PFtwo` below is a statement about the paper's `eq:G`.
-/

namespace TworowD4Kernel.Convolution

open TworowD4Kernel.DiscreteConcavity

/-- The indicator of the integer interval `[a,b]`, the paper's `1_[a,b]`. -/
def ind (a b : ℤ) : ℤ → ℤ := fun x => if a ≤ x ∧ x ≤ b then 1 else 0

/-- Convolution on `ℤ`: `(f * g) s = ∑_{x ∈ ℤ} f x * g (s - x)`.

Written as a `finsum` (`∑ᶠ`) rather than as a sum over an explicitly chosen window, so that no
window appears in the statement of the trapezoid formula and there is nothing to check about the
window's adequacy.  `finsum` of a function with infinite support is `0`; every use here is of a
compactly supported summand, bridged by `conv_eq_sum_of_vanishing`. -/
noncomputable def conv (f g : ℤ → ℤ) (s : ℤ) : ℤ := ∑ᶠ x : ℤ, f x * g (s - x)

/-- `f` vanishes off `[p,q]`. -/
def VanishesOff (f : ℤ → ℤ) (p q : ℤ) : Prop := ∀ x, x < p ∨ q < x → f x = 0

/-- The convolution is computed by a sum over any window carrying the support of `f`. -/
theorem conv_eq_sum_of_vanishing {f : ℤ → ℤ} {p q : ℤ} (hf : VanishesOff f p q) (g : ℤ → ℤ)
    (s : ℤ) : conv f g s = ∑ x ∈ Finset.Icc p q, f x * g (s - x) := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro x hx
  simp only [Function.mem_support, ne_eq] at hx
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hcon
  exact hx (by rw [hf x (by omega)]; ring)

theorem ind_vanishesOff (a b : ℤ) : VanishesOff (ind a b) a b := by
  intro x hx; simp only [ind]; rw [if_neg]; omega

theorem ind_eq_one_of_mem {a b x : ℤ} (h₁ : a ≤ x) (h₂ : x ≤ b) : ind a b x = 1 := by
  simp only [ind]; rw [if_pos ⟨h₁, h₂⟩]

/-- `ind a b` vanishes off any window containing `[a,b]`. -/
theorem ind_vanishesOff_wide {p q a b : ℤ} (hp : p ≤ a) (hq : b ≤ q) :
    VanishesOff (ind a b) p q := by
  intro x hx; simp only [ind]; rw [if_neg]; omega

/-- The two-point set `{0,3}` vanishes off `[-5,10]`; used by `conv_sees_the_summand`. -/
theorem twoPoint_vanishesOff :
    VanishesOff (fun x : ℤ => if x = 0 ∨ x = 3 then 1 else 0) (-5) 10 := by
  intro x hx
  show (if x = 0 ∨ x = 3 then (1 : ℤ) else 0) = 0
  rw [if_neg]; omega

/-- **The trapezoid formula** (`prop:regII`, l.394).  The convolution of the indicators of
`[a,b]` and `[c,d]` is the positive part of a minimum of four affine functions: the two rising
and falling edges `s - ℓ + 1` and `h - s + 1` with `ℓ = a + c`, `h = b + d`, and the two widths
`n = b - a + 1`, `m = d - c + 1`. -/
theorem conv_ind_ind (a b c d s : ℤ) :
    conv (ind a b) (ind c d) s
      = max (min (min (s - (a + c) + 1) (b + d - s + 1)) (min (b - a + 1) (d - c + 1))) 0 := by
  rw [conv_eq_sum_of_vanishing (ind_vanishesOff a b) _ s]
  have hstep : ∀ x ∈ Finset.Icc a b,
      ind a b x * ind c d (s - x) = if x ∈ Finset.Icc (s - d) (s - c) then (1 : ℤ) else 0 := by
    intro x hx
    simp only [Finset.mem_Icc] at hx
    rw [ind_eq_one_of_mem hx.1 hx.2, one_mul]
    simp only [ind, Finset.mem_Icc]
    by_cases h : c ≤ s - x ∧ s - x ≤ d
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_mem]
  have hinter : Finset.Icc a b ∩ Finset.Icc (s - d) (s - c)
      = Finset.Icc (max a (s - d)) (min b (s - c)) := by
    ext x; simp only [Finset.mem_inter, Finset.mem_Icc]; omega
  rw [hinter, Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Icc]
  omega

/-! ### Controls on the convolution

The trapezoid formula is the statement this file exists to supply, so it gets a control that
can fail.  `conv` is a `finsum` and therefore noncomputable; the control evaluates it over a
**different, wider** window than the one `conv_ind_ind`'s proof uses, so it tests the
window-independence of `conv` as well as the formula. -/

/-- Positive control: `1_[0,2] * 1_[0,1]` evaluated over the window `[-5,10]` by `decide`,
against the trapezoid formula.  The profile is `(1,2,2,1)` on `[0,3]`, of total mass
`3 · 2 = 6`. -/
theorem conv_control_values :
    conv (ind 0 2) (ind 0 1) 0 = 1 ∧ conv (ind 0 2) (ind 0 1) 1 = 2 ∧
      conv (ind 0 2) (ind 0 1) 2 = 2 ∧ conv (ind 0 2) (ind 0 1) 3 = 1 ∧
      conv (ind 0 2) (ind 0 1) 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    rw [conv_eq_sum_of_vanishing (ind_vanishesOff_wide (p := -5) (q := 10)
      (by omega) (by omega))] <;> decide

/-- and the same five values from the formula: the two agree, so the formula is not vacuous. -/
theorem conv_control_formula :
    max (min (min (0 - (0 + 0) + 1) (2 + 1 - 0 + 1)) (min (2 - 0 + 1) (1 - 0 + 1))) 0 = (1 : ℤ) ∧
      max (min (min (1 - (0 + 0) + 1) (2 + 1 - 1 + 1)) (min (2 - 0 + 1) (1 - 0 + 1))) 0 = (2 : ℤ) ∧
      max (min (min (4 - (0 + 0) + 1) (2 + 1 - 4 + 1)) (min (2 - 0 + 1) (1 - 0 + 1))) 0 = (0 : ℤ) := by
  refine ⟨by omega, by omega, by omega⟩

/-- Negative control: the positive part in the trapezoid formula is load-bearing.  Off `[ℓ,h]`
the bare minimum of the four affine functions is **negative**, while the convolution is `0`;
dropping `(·)_+` would make the formula false at `s = 5`. -/
theorem trapezoid_posPart_needed :
    conv (ind 0 2) (ind 0 1) 5 = 0 ∧
      min (min (5 - (0 + 0) + 1) (2 + 1 - 5 + 1)) (min (2 - 0 + 1) (1 - 0 + 1)) < (0 : ℤ) := by
  constructor
  · rw [conv_eq_sum_of_vanishing (ind_vanishesOff_wide (p := -5) (q := 10)
      (by omega) (by omega))]
    decide
  · omega

/-- Negative control: `conv` is a genuine convolution and not the trapezoid formula in disguise.
A **non**-interval first factor gives a value the trapezoid formula cannot produce: `1_{{0,3}}`
convolved with `1_[0,1]` has the non-unimodal profile `(1,1,0,1,1)` on `[0,4]`, and in particular its value at `2` is
`0` while the trapezoid formula for the hull `[0,3] × [0,1]` returns
`min (2-0+1, 4-2+1, 4, 2)_+ = 2` there. -/
theorem conv_sees_the_summand :
    conv (fun x => if x = 0 ∨ x = 3 then 1 else 0) (ind 0 1) 2 = 0 := by
  rw [conv_eq_sum_of_vanishing twoPoint_vanishesOff]
  decide

/-! ### Re-deriving `GR` from the convolution

This is the point of the file: `GR` in `DiscreteConcavity.lean` is a *definition*, and the
paper's `G` (eq:G, l.263) is a sum of convolutions.  The next theorem identifies them under the
region II / IV hypothesis that `a_t + c_t` and `b_t + d_t` are constant on `T` (`prop:regII`,
l.377), and the one after it transports `GR_PFtwo` across. -/

variable {ι : Type*}

/-- The widths `n_t = b_t - a_t + 1`, `m_t = d_t - c_t + 1` enter only through `min (n_t) (m_t)`,
which is the `k` of `rho`. -/
def width (a b c d : ι → ℤ) : ι → ℤ := fun t => min (b t - a t + 1) (d t - c t + 1)

/-- **The paper's `G` is the paper's `ρ_R ∘ H`.**  Under the region II / IV hypothesis of
`prop:regII` (all the trapezoids share the support `[ℓ,h]`), the sum of convolutions `eq:G`
equals `GR`, which `DiscreteConcavity.lean` had taken as a definition. -/
theorem sum_conv_eq_GR (T : Finset ι) (a b c d : ι → ℤ) (l h : ℤ)
    (hl : ∀ t ∈ T, a t + c t = l) (hh : ∀ t ∈ T, b t + d t = h) (s : ℤ) :
    ∑ t ∈ T, conv (ind (a t) (b t)) (ind (c t) (d t)) s = GR T (width a b c d) l h s := by
  simp only [GR, width]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [conv_ind_ind, ← hl t ht, ← hh t ht]
  simp only [H]

/-- **`prop:regII` as a statement about the paper's object.**  `GR_PFtwo` of
`DiscreteConcavity.lean` proved `PF₂` for the trapezoid *formula*; composed with
`sum_conv_eq_GR` it now holds for the sum of convolutions `eq:G` itself.

The nondegeneracy hypothesis is that *one* index `t₀ ∈ T` has both intervals nonempty — exactly
`k t₀ ≥ 1` in `GR_PFtwo`. -/
theorem sum_conv_PFtwo (T : Finset ι) (a b c d : ι → ℤ) (l h : ℤ)
    (hl : ∀ t ∈ T, a t + c t = l) (hh : ∀ t ∈ T, b t + d t = h)
    {t₀ : ι} (ht₀ : t₀ ∈ T) (hab : a t₀ ≤ b t₀) (hcd : c t₀ ≤ d t₀) :
    PFtwo (fun s => ∑ t ∈ T, conv (ind (a t) (b t)) (ind (c t) (d t)) s) := by
  have hfun : (fun s => ∑ t ∈ T, conv (ind (a t) (b t)) (ind (c t) (d t)) s)
      = GR T (width a b c d) l h := funext fun s => sum_conv_eq_GR T a b c d l h hl hh s
  rw [hfun]
  exact GR_PFtwo T (width a b c d) l h ht₀ (by simp only [width]; omega)

/-! ### The sliding-window reduction, for `prop:regI`

`prop:regI` is the remaining unformalised proposition of the paper.  It invokes **(P3)**,
closure of `PF₂` under convolution, in full generality.  (P3) is *not* an uncited import: the
paper proves it from scratch, via `T(f*g) = T(f) T(g)` on bi-infinite Toeplitz matrices plus
Cauchy–Binet — registry node `pf2-convolution` of `cylindric-lorentzian.json`, trust `proved`,
`proofs/2026-09-26-c1-cylindric-lorentzian.tex`, with Hoggar's classical statement at
arXiv:1906.09633.  So the scope point below is about what a *formalisation* owes, not about a
gap in the paper.

What `prop:regI` actually convolves is an *interval indicator* against a `PF₂` sequence, and the
next theorem says what that operation is: a **sliding window sum** of fixed width.  So the
statement a Lean `prop:regI` needs is only

  *a sliding window sum of a `PF₂` sequence is `PF₂`*,

strictly weaker than (P3), and reachable without Toeplitz matrices or Cauchy–Binet.  The
reduction is proved here; the implication itself is **not** proved in this file — see the scope
note at the end. -/

/-- Convolution against an interval indicator is a sliding window sum of fixed width
`B - A + 1`: `(1_[A,B] * w) (s) = ∑_{x = s-B}^{s-A} w x`.  No hypothesis on `w`. -/
theorem conv_ind_left (A B : ℤ) (w : ℤ → ℤ) (s : ℤ) :
    conv (ind A B) w s = ∑ x ∈ Finset.Icc (s - B) (s - A), w x := by
  rw [conv_eq_sum_of_vanishing (ind_vanishesOff A B) w s]
  rw [Finset.sum_congr rfl (fun x hx => by
    rw [ind_eq_one_of_mem (Finset.mem_Icc.1 hx).1 (Finset.mem_Icc.1 hx).2, one_mul])]
  have himg : (Finset.Icc A B).image (fun x => s - x) = Finset.Icc (s - B) (s - A) := by
    ext y
    simp only [Finset.mem_image, Finset.mem_Icc]
    constructor
    · rintro ⟨x, hx, rfl⟩; omega
    · intro hy; exact ⟨s - y, by omega, by omega⟩
  rw [← himg, Finset.sum_image (fun x _ y _ h => by omega)]

/-- The window has constant width, which is what makes the sliding-window form a *reduction*
and not a reparametrisation. -/
theorem conv_ind_left_window_card (A B : ℤ) (hAB : A ≤ B) (s : ℤ) :
    (Finset.Icc (s - B) (s - A)).card = (B - A + 1).toNat := by
  rw [Int.card_Icc]; congr 1; omega

/-! ### What is NOT formalised in this file

Stated here, in the section a copier reads.  Both items are propositions in the paper that are
carried by a remark or a citation rather than by a proof.

* **(P3) is invoked more strongly than it is used; the weaker statement is not proved here.**
  `conv_ind_left` reduces `prop:regI`'s convolution to a sliding window sum, so what is needed
  is only *window sum of `PF₂` is `PF₂`*, not the full closure of `PF₂` under convolution.
  That reduction is a theorem above.  The implication is **not** proved.  (P3) itself *is*
  proved in the paper by Toeplitz/Cauchy–Binet, so this is a statement about the cheapest route
  to a formalised `prop:regI`, not a defect in the paper.  What a
  later session has to supply is the log-concavity of
  `W (s) = ∑_{x = s-B}^{s-A} w x`; the algebra of the obstruction, with
  `α = w (s-1-B)`, `β = w (s-B)`, `γ = w (s-A)`, `δ = w (s-A+1)` (so `β, γ` are the two ends of
  the window at `s`, and `α, δ` the two sites just outside it), is
  `W (s) ^ 2 - W (s-1) * W (s+1) = W (s) * (β + γ - α - δ) + (α - γ) * (β - δ)`,
  using `W (s±1) = W (s) + (α - γ)` resp. `W (s) + (δ - β)`.  This is **not** a consequence of
  `omega` plus log-concavity of `w` termwise: it needs the monotone-ratio form of `PF₂`
  (`β * γ ≥ α * δ`, from the ratios `β/α ≥ δ/γ` at the two window ends) together with
  `W (s) ≥ β + γ`.  For a window of width `1` the identity degenerates to `γ ^ 2 - α * δ ≥ 0`,
  i.e. exactly log-concavity of `w`, which is a sanity check on the identity and *not* a proof
  of the general case.
* **The `-∞`-extended `lem:trunc`.**  The paper writes "`c` may be a concave function with
  interval domain extended by `-∞`; the same proof applies".  "The same proof applies" is a
  proposition, not a remark.  `DiscreteConcavity.PFtwo_posPart` proves only the finite version
  (`c : ℤ → ℤ`, concave everywhere).  The extended version is the statement that
  `fun s => if p ≤ s ∧ s ≤ q then max (c s) 0 else 0` is `PF₂` whenever `c` is concave on the
  **interior** `p < s < q`, and it is a genuinely separate statement: `IntConcave.min_le`, which
  carries the interval-support conjunct in the finite proof, is stated for `c` concave on all of
  `ℤ` and its induction (`slope_antitone`) walks outside `[p,q]`.  Not proved here.
-/

end TworowD4Kernel.Convolution

/-! ### Axiom audit -/

section Audit
open TworowD4Kernel.Convolution
#print axioms conv_eq_sum_of_vanishing
#print axioms conv_ind_ind
#print axioms sum_conv_eq_GR
#print axioms sum_conv_PFtwo
#print axioms conv_ind_left
#print axioms conv_control_values
#print axioms trapezoid_posPart_needed
#print axioms conv_sees_the_summand
end Audit
