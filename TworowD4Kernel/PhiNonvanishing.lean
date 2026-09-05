/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

/-!
# Nonvanishing of the witness polynomial `Φ_{\vec e}`

This file formalises the single load-bearing sentence in the proof of the main theorem of
`~/projects/proofs/2026-09-05-Q83-sharpness-all-k.tex` (Theorem "main", the sharpness of the
`(1+t)`-adic valuation for all `k`):

> "If `e_{k-1} ≠ e_k` then `x^{e_{k-1}} - x^{e_k} ≠ 0` and each `1 - x^{e_i} ≠ 0` in the
> integral domain `ℤ[x]`, so `Φ_{\vec e} ≠ 0`."

Everything in the equivalence (i) `e_{k-1} ≠ e_k` ⟺ (iii) the valuation is exactly `1` rests on
that sentence and on nothing else, so it is worth checking by machine.

## The statement

The paper writes `Φ` with a division,
`Φ_{\vec e}(x) = (x^{e_{k-1}} - x^{e_k})/(1-x) · ∏_{i ≤ k-2} (1 - x^{e_i})`.
We do **not** formalise a quotient. For `a < b` the first factor *is* the geometric sum
`x^a + x^{a+1} + ⋯ + x^{b-1}`, which is what the paper's own derivation produces (the window
`j - e_max < Σ_T ≤ j - e_min`) before it is contracted into a fraction; so `Phi` below takes
that sum as its definition. Here `a = min(e_{k-1}, e_k)` and `b = max(e_{k-1}, e_k)`, and the
list `e` is `e_1, …, e_{k-2}`.

## The trick

The two factors need *different* evaluation points, and there is no single point at which both
are visibly nonzero:

* `1 - X^m ≠ 0` is seen at `x = 0`, where it is `1`. At `x = 1` it is `0`.
* `∑_{i < b-a} X^{a+i} ≠ 0` is seen at `x = 1`, where it is `b - a`. At `x = 0` it is `0`
  unless `a = 0`.

Nonvanishing of the product then comes from `IsDomain (Polynomial ℤ)`.

## A finding: the paper's `e_i ≥ 2` is not load-bearing here

The paper hypothesises `e_1, …, e_k ≥ 2` throughout. For *this* step only `e_i ≥ 1` is needed —
`1 ≥ 1` is exactly what makes `eval 0 (1 - X^m) = 1`. The lemma is therefore stated at `1 ≤ m`.
The `≥ 2` is genuinely used elsewhere in the paper (it is what makes `e_min ≥ 2`, hence the
degree window in the very next sentence), but it does not enter the nonvanishing argument.

## Main results

* `TworowD4Kernel.PhiNonvanishing.Phi_ne_zero` — the target: `a < b` and `∀ m ∈ e, 1 ≤ m`
  imply `Phi a b e ≠ 0`.
* `TworowD4Kernel.PhiNonvanishing.Phi_natDegree` — the degree identity
  `(Phi a b e).natDegree = (b - 1) + e.sum`, which is what pins the witness `j₀` inside
  `0 ≤ j₀ ≤ E - 1` and so guarantees `(E - j₀, 1^{j₀})` is a genuine partition of `E`.

## Coverage note

`Polynomial ℤ` is `noncomputable`, so **none of this file can be exercised by `#guard` in
`TworowD4KernelTests`**. Its only validation is `lake build` plus the `#print axioms` check
recorded in the session write-up. No reader should infer test-driver coverage here.
-/

namespace TworowD4Kernel.PhiNonvanishing

open Polynomial

/-- The witness polynomial of `2026-09-05-Q83-sharpness-all-k.tex`, Theorem "main".

`a = min(e_{k-1}, e_k)`, `b = max(e_{k-1}, e_k)`, and `e = [e_1, …, e_{k-2}]`.
The first factor is the geometric sum `x^a + ⋯ + x^{b-1}`, which for `a < b` equals the
paper's `(x^a - x^b)/(1-x)` without introducing a quotient. -/
noncomputable def Phi (a b : ℕ) (e : List ℕ) : Polynomial ℤ :=
  (∑ i ∈ Finset.range (b - a), Polynomial.X ^ (a + i)) *
    (e.map fun m => 1 - Polynomial.X ^ m).prod

/-- A polynomial with a nonzero value somewhere is nonzero. -/
theorem ne_zero_of_eval_ne_zero {p : Polynomial ℤ} {x : ℤ} (h : p.eval x ≠ 0) : p ≠ 0 := by
  intro hp
  exact h (by rw [hp, Polynomial.eval_zero])

/-- The geometric-sum factor evaluated at `1` is the window width `b - a`. -/
theorem eval_one_window (a b : ℕ) :
    (∑ i ∈ Finset.range (b - a), Polynomial.X ^ (a + i)).eval (1 : ℤ) = (b - a : ℕ) := by
  rw [Polynomial.eval_finsetSum]
  simp

/-- The geometric-sum factor is nonzero as soon as the window is nonempty. -/
theorem window_ne_zero {a b : ℕ} (hab : a < b) :
    (∑ i ∈ Finset.range (b - a), Polynomial.X ^ (a + i)) ≠ (0 : Polynomial ℤ) := by
  refine ne_zero_of_eval_ne_zero (x := 1) ?_
  rw [eval_one_window]
  exact_mod_cast Nat.sub_ne_zero_of_lt hab

/-- Each factor `1 - X^m` evaluated at `0` is `1`, provided `m ≥ 1`. -/
theorem eval_zero_factor {m : ℕ} (hm : 1 ≤ m) :
    ((1 : Polynomial ℤ) - Polynomial.X ^ m).eval 0 = 1 := by
  simp [_root_.zero_pow (Nat.one_le_iff_ne_zero.mp hm)]

/-- The product `∏ (1 - X^{e_i})` is nonzero when every `e_i ≥ 1`: it evaluates to `1` at `0`. -/
theorem prod_factors_ne_zero {e : List ℕ} (he : ∀ m ∈ e, 1 ≤ m) :
    (e.map fun m => 1 - Polynomial.X ^ m).prod ≠ (0 : Polynomial ℤ) := by
  refine ne_zero_of_eval_ne_zero (x := 0) ?_
  have : ((e.map fun m => (1 : Polynomial ℤ) - Polynomial.X ^ m).prod).eval 0 = 1 := by
    induction e with
    | nil => simp
    | cons m t ih =>
      have hm : 1 ≤ m := he m (List.mem_cons_self ..)
      have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => he x (List.mem_cons_of_mem _ hx)
      rw [List.map_cons, List.prod_cons, Polynomial.eval_mul, eval_zero_factor hm, ih ht,
        one_mul]
  rw [this]
  exact one_ne_zero

/-- **The target.** `Φ_{\vec e} ≠ 0` when `e_{k-1} ≠ e_k` (here `a < b`) and every
`e_i ≥ 1`. This is the load-bearing sentence of `2026-09-05-Q83-sharpness-all-k.tex`,
Theorem "main": *"each `1 - x^{e_i} ≠ 0` in the integral domain `ℤ[x]`, so `Φ_{\vec e} ≠ 0`."*

Note the hypothesis is `1 ≤ m`, not the paper's `2 ≤ m`; see the module docstring. -/
theorem Phi_ne_zero {a b : ℕ} {e : List ℕ} (hab : a < b) (he : ∀ m ∈ e, 1 ≤ m) :
    Phi a b e ≠ 0 :=
  mul_ne_zero (window_ne_zero hab) (prod_factors_ne_zero he)

/-! ## The degree identity

The paper's next sentence — the one that guarantees the witness index `j₀` really does give a
partition — reads:

> "Every nonzero coefficient of `Φ_{\vec e}` lies in degrees between `e_min ≥ 2` and
> `deg Φ_{\vec e} = e_max - 1 + ∑_{i ≤ k-2} e_i = E - e_min - 1`, so `0 ≤ j₀ ≤ E - 1`."

In the notation of `Phi`, `e_max = b` and `∑_{i ≤ k-2} e_i = e.sum`, so the claim is
`natDegree (Phi a b e) = (b - 1) + e.sum`. That is `Phi_natDegree` below. -/

/-- The single factor `1 - X^m` has degree `m` when `m ≥ 1`. -/
theorem natDegree_factor {m : ℕ} (hm : 1 ≤ m) :
    ((1 : Polynomial ℤ) - Polynomial.X ^ m).natDegree = m := by
  have h : ((1 : Polynomial ℤ)).natDegree < ((Polynomial.X : Polynomial ℤ) ^ m).natDegree := by
    simpa [Polynomial.natDegree_X_pow] using hm
  rw [Polynomial.natDegree_sub_eq_right_of_natDegree_lt h, Polynomial.natDegree_X_pow]

/-- The product `∏ (1 - X^{e_i})` has degree `∑ e_i`. Uses `IsDomain (Polynomial ℤ)` through
`natDegree_mul`, which needs both factors nonzero — supplied by `prod_factors_ne_zero`. -/
theorem natDegree_prod_factors {e : List ℕ} (he : ∀ m ∈ e, 1 ≤ m) :
    ((e.map fun m => (1 : Polynomial ℤ) - Polynomial.X ^ m).prod).natDegree = e.sum := by
  induction e with
  | nil => simp
  | cons m t ih =>
    have hm : 1 ≤ m := he m (List.mem_cons_self ..)
    have ht : ∀ x ∈ t, 1 ≤ x := fun x hx => he x (List.mem_cons_of_mem _ hx)
    have hfac : ((1 : Polynomial ℤ) - Polynomial.X ^ m) ≠ 0 := by
      have := prod_factors_ne_zero (e := [m]) (by simpa using hm)
      simpa using this
    rw [List.map_cons, List.prod_cons,
      Polynomial.natDegree_mul hfac (prod_factors_ne_zero ht),
      natDegree_factor hm, ih ht, List.sum_cons]

/-- The geometric-sum factor `X^a + ⋯ + X^{b-1}` has degree `b - 1`. -/
theorem natDegree_window {a b : ℕ} (hab : a < b) :
    (∑ i ∈ Finset.range (b - a), (Polynomial.X : Polynomial ℤ) ^ (a + i)).natDegree = b - 1 := by
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine Polynomial.natDegree_sum_le_of_forall_le (Finset.range (b - a))
      (fun i => (Polynomial.X : Polynomial ℤ) ^ (a + i)) fun i hi => ?_
    rw [Polynomial.natDegree_X_pow]
    have : i < b - a := Finset.mem_range.mp hi
    omega
  · have hmem : b - 1 - a ∈ Finset.range (b - a) := by
      rw [Finset.mem_range]; omega
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single (b - 1 - a)]
    · rw [Polynomial.coeff_X_pow]
      simp only [if_pos (by omega : b - 1 = a + (b - 1 - a))]
      exact one_ne_zero
    · intro i _ hne
      rw [Polynomial.coeff_X_pow, if_neg]
      omega
    · intro h; exact absurd hmem h

/-- **The degree identity.** `deg Φ_{\vec e} = (b - 1) + ∑ e_i`, i.e. in the paper's notation
`e_max - 1 + ∑_{i ≤ k-2} e_i`. This is the step of `2026-09-05-Q83-sharpness-all-k.tex`,
Theorem "main", that places the witness index `j₀` inside `0 ≤ j₀ ≤ E - 1` and so makes
`(E - j₀, 1^{j₀})` a genuine partition of `E`. -/
theorem Phi_natDegree {a b : ℕ} {e : List ℕ} (hab : a < b) (he : ∀ m ∈ e, 1 ≤ m) :
    (Phi a b e).natDegree = (b - 1) + e.sum := by
  rw [Phi, Polynomial.natDegree_mul (window_ne_zero hab) (prod_factors_ne_zero he),
    natDegree_window hab, natDegree_prod_factors he]

/-! ## Cross-check against the paper's worked example

`2026-09-05-Q83-sharpness-all-k.tex`, the example headed *"the excluded case of
Theorem (wit-cited) is not an obstruction"*, takes `(e₁, e₂, e₃) = (4, 2, 3)` and computes by
hand

> `Φ_{\vec e}(x) = (x² - x³)/(1 - x) · (1 - x⁴) = x²(1 - x⁴) = x² - x⁶`.

In the notation of `Phi` that is `a = e₂ = 2`, `b = e₃ = 3`, `e = [4]`. Neither number below was
tuned: the polynomial is computed from the definition, and the degree `6` is read off
`Phi_natDegree` and independently equals the paper's `E - e_min - 1 = 9 - 2 - 1`. -/

example : Phi 2 3 [4] = Polynomial.X ^ 2 - Polynomial.X ^ 6 := by
  simp only [Phi, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  norm_num [Finset.sum_range_succ]
  ring

example : (Phi 2 3 [4]).natDegree = 6 := by
  rw [Phi_natDegree (by norm_num) (by simp)]
  norm_num

example : Phi 2 3 [4] ≠ 0 := Phi_ne_zero (by norm_num) (by simp)

end TworowD4Kernel.PhiNonvanishing
