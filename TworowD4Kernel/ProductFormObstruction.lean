/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.NonCyclotomicRoot
import Mathlib.Algebra.BigOperators.Ring.Multiset
import Mathlib.Tactic

/-!
# No product form: a root in `(-1,0)` obstructs `t^c ∏ (1 - t^{d_i})`

This file closes the step that `TworowD4Kernel/NonCyclotomicRoot.lean` deliberately left open.
That file proved the analytic input to Theorem D of
`projects/proofs/2026-10-07-two-part-green-polynomials.tex`:

> for every odd `b ≥ 3`, `D_b(t) = t^b - t^{b-1} + 1` has a real root in `(-1,0)`

and recorded that the *consequence* — that such a root rules out a product form — was not
formalised, naming `Polynomial.isRoot_cyclotomic_iff` / `IsPrimitiveRoot` as the route.

**That route is not needed.** Cyclotomic theory is a detour: against the *specific* product shape
`t^c ∏_i (1 - t^{d_i})` the obstruction is an elementary sign argument on `(-1,0)`, with no roots
of unity anywhere in it.

> For `t ∈ (-1,0)` we have `|t| < 1`, so `|t^k| = |t|^k < 1` for every `k ≥ 1`, hence `t^k < 1`
> and `1 - t^k > 0`. Also `t ≠ 0`, so `t^c ≠ 0`. A finite product of nonzero reals is nonzero.
> But `D_b` *does* vanish somewhere on `(-1,0)`. So `D_b` is not of that shape.

## What is formalised, and what is not

**Formalised:** `prod_one_sub_pow_ne_zero` (the elementary lemma) and `not_product_form` (its
composition with `exists_root_Ioo`), the latter stated for the bare real function
`t ↦ t^b - t^{b-1} + 1`.

**NOT formalised:** Theorem D itself. `Y^λ_ρ`, Hall–Littlewood `P_λ`, Kostka–Foulkes polynomials
and the charge statistic have **no Lean definitions in this project**, and the identification
`D_{a,b} = Y^{(a,b)}_{(a,b)} = t^b - t^{b-1} + 1` is paper-side (Theorem C at `m = b`). Here
`t^b - t^{b-1} + 1` is simply *written down*. `unproved ≠ unformalised`: nothing here should be
read as formalising Theorem D's quantification over all `ℓ(λ) ≤ 2` and all two-part `ρ`. What is
proved is the obstruction mechanism at the single polynomial, for the exponent `±1 = +1` shape.

**Scope of the product shape.** Theorem D's display allows exponents `±1`, i.e. factors in the
denominator too. What is proved *here* is the numerator-only form `t^c ∏ (1 - t^{d_i})`, and
`not_product_form` below should not be read as covering the signed case.

**That gap is now closed, in `TworowD4Kernel/SignedProductFormObstruction.lean`** (2026-10-08 c2):
`not_signed_product_form` allows arbitrary `e_i ∈ ℤ`, `not_product_form_pm_one` is the literal `±1`
display, and `not_product_form_ratio` is the quotient form. No denominator clearing was needed —
each factor `1 - t^{d_i}` is strictly *positive* at the root by `one_sub_pow_pos` (reused from this
file), and positivity survives every integer power, so the ratio is nonzero there for the same
reason the product is. The remark that previously stood here — that clearing denominators reduces
it to "the same argument, since the left side still vanishes at the root" — was a correct
*conclusion* reached by an unnecessary route; see that file's `cleared_lhs_eq_zero_at_one` for why
the related `t = 1` route does not work at all.

## Multiset, and the `List` precedent in this repo

The exponents `d_i` carry no order, so `Multiset ℕ` is the honest index type and is what is used.
Note that `TworowD4Kernel/PhiNonvanishing.lean` already has a close cousin over `List`:

```
prod_factors_ne_zero {e : List ℕ} (he : ∀ m ∈ e, 1 ≤ m) :
    (e.map fun m => 1 - Polynomial.X ^ m).prod ≠ (0 : Polynomial ℤ)
```

That is **a different statement**, and it does not imply this one: it says the *polynomial*
`∏ (1 - X^{e_i})` is nonzero in `ℤ[X]` (seen by evaluating at `0`), whereas what is needed here is
nonvanishing *at one particular real point* `t`, and a nonzero polynomial may certainly vanish at a
point. The implication runs the other way. The hypothesis `∀ k ∈ d, 1 ≤ k` is shared, and for the
same reason in both files: `k = 0` makes the factor `1 - t^0 = 0`.
-/

namespace TworowD4Kernel.ProductForm

open Set

/-- For `t ∈ (-1,0)` and `k ≥ 1`, the factor `1 - t^k` is **strictly positive**.

`|t| < 1` gives `|t^k| = |t|^k < 1`, hence `t^k ≤ |t^k| < 1`. The hypothesis `k ≥ 1` is needed:
`k = 0` gives `1 - t^0 = 0`. -/
theorem one_sub_pow_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {k : ℕ} (hk : 1 ≤ k) :
    0 < 1 - t ^ k := by
  obtain ⟨h1, h2⟩ := ht
  have habs : |t| < 1 := abs_lt.mpr ⟨h1, by linarith⟩
  have hpow : |t ^ k| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg t) habs (by omega)
  have : t ^ k < 1 := lt_of_abs_lt hpow
  linarith

/-- Each factor `1 - t^k` is nonzero on `(-1,0)` when `k ≥ 1`. -/
theorem one_sub_pow_ne_zero {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {k : ℕ} (hk : 1 ≤ k) :
    1 - t ^ k ≠ 0 :=
  ne_of_gt (one_sub_pow_pos ht hk)

/-- **The elementary obstruction.** For `t ∈ (-1,0)` and every exponent `d_i ≥ 1`, the product
form `t^c ∏_i (1 - t^{d_i})` is nonzero.

`t ≠ 0` kills the monomial; each factor is positive by `one_sub_pow_pos`; `Multiset.prod_ne_zero`
then needs only that `0` is not among the mapped factors. -/
theorem prod_one_sub_pow_ne_zero (c : ℕ) (d : Multiset ℕ) (hd : ∀ k ∈ d, 1 ≤ k)
    {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 0) :
    t ^ c * (d.map (fun k => 1 - t ^ k)).prod ≠ 0 := by
  have htne : t ≠ 0 := ne_of_lt ht.2
  refine mul_ne_zero (pow_ne_zero c htne) (Multiset.prod_ne_zero ?_)
  intro hmem
  obtain ⟨k, hk, hkeq⟩ := Multiset.mem_map.mp hmem
  exact one_sub_pow_ne_zero ht (hd k hk) hkeq

/-- **The deliverable.** For odd `b ≥ 3` the function `t ↦ t^b - t^{b-1} + 1` admits **no**
product form `t^c ∏_i (1 - t^{d_i})` with all `d_i ≥ 1`.

The two halves meet at the root: `exists_root_Ioo` (`NonCyclotomicRoot.lean`) produces
`t₀ ∈ (-1,0)` with `D_b(t₀) = 0`, while `prod_one_sub_pow_ne_zero` says the right-hand side is
nonzero there.

Reference: Theorem D, `projects/proofs/2026-10-07-two-part-green-polynomials.tex`. -/
theorem not_product_form (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (d : Multiset ℕ), (∀ k ∈ d, 1 ≤ k) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1 = t ^ c * (d.map (fun k => 1 - t ^ k)).prod := by
  rintro ⟨c, d, hd, hid⟩
  obtain ⟨t₀, ht₀, hroot⟩ := TworowD4Kernel.exists_root_Ioo b hb hodd
  have hne := prod_one_sub_pow_ne_zero c d hd ht₀
  rw [← hid t₀, hroot] at hne
  exact hne rfl

/-! ## The hypothesis `∀ k ∈ d, 1 ≤ k` is load-bearing — as a counterexample, not a build failure

Dropping `hd` does not merely break the proof above; it makes the **conclusion false**. At
`d = {0}` the factor is `1 - t^0 = 1 - 1 = 0`, so the product vanishes for *every* `c` and *every*
`t` whatsoever — no interval hypothesis is even consulted. This is the companion to
`not_exists_root_Ioo_four` in `NonCyclotomicRoot.lean`: a fact about the statement, where a failed
`lake build` would only have been a fact about my proof. -/

theorem prod_eq_zero_of_exponent_zero (c : ℕ) (t : ℝ) :
    t ^ c * ((({0} : Multiset ℕ)).map (fun k => 1 - t ^ k)).prod = 0 := by
  simp

/-- **The ablation, as a theorem.** `prod_one_sub_pow_ne_zero` with `hd` deleted is false:
`d = {0}` satisfies nothing and makes the product zero at every point of `(-1,0)`. -/
theorem not_prod_ne_zero_without_hd :
    ¬ ∀ (c : ℕ) (d : Multiset ℕ) (t : ℝ), t ∈ Set.Ioo (-1 : ℝ) 0 →
      t ^ c * (d.map (fun k => 1 - t ^ k)).prod ≠ 0 := by
  intro h
  have hmem : (-(1/2) : ℝ) ∈ Set.Ioo (-1 : ℝ) 0 := by constructor <;> norm_num
  exact h 0 {0} (-(1/2)) hmem (prod_eq_zero_of_exponent_zero 0 (-(1/2)))

end TworowD4Kernel.ProductForm
