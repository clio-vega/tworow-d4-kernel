/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ProductFormObstruction
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Signed exponents: the obstruction survives denominators

`TworowD4Kernel/ProductFormObstruction.lean` proved that for odd `b ≥ 3` the polynomial
`D_b(t) = t^b - t^{b-1} + 1` is not of the shape `t^c ∏_i (1 - t^{d_i})`, and its own docstring
flagged the scope limit: Theorem D of `projects/proofs/2026-10-07-two-part-green-polynomials.tex`
allows exponents `±1`, i.e. factors in the **denominator** too. This file closes that gap.

## The route named for this step was not needed, and its premise is false

The plan recorded for this session was: *clear the denominators first*, turning the claim into the
polynomial identity `D_b · ∏_{e_i = -1}(1 - t^{d_i}) = t^c ∏_{e_i = +1}(1 - t^{d_i})`, and then
separate the two sides by their order of vanishing at `t = 1` — the suggestion being that the left
side is nonzero at `t = 1` (`1 - 1 + 1 = 1`) while the right side vanishes.

**Neither step is needed, and the `t = 1` premise is false.** `D_b(1) = 1`, but the cleared left
side is `D_b(1) · ∏(1 - 1^{d_i}) = 1 · 0 = 0` as soon as the denominator set is nonempty — which is
exactly the case the extension exists to handle. That is recorded as
`cleared_lhs_eq_zero_at_one` below, so the dead route is a theorem and not a memory.

What actually closes it is the *same* root in `(-1,0)`, used once more:

> At `t₀ ∈ (-1,0)` every factor `1 - t₀^{d_i}` is **strictly positive** (`one_sub_pow_pos`), and a
> positive real raised to **any** integer power is positive. So each `(1 - t₀^{d_i})^{e_i} > 0`, the
> product is positive, and `t₀^c ≠ 0`. The right side is nonzero at `t₀`; the left side is `0`.

Nonvanishing is preserved under inversion, so the `-1` exponents cost nothing — no denominator
clearing, no evaluation at `t = 1`, no cyclotomic theory. This is the second time on this file that
the route a gap note named was not the route the step needed.

## What is proved, and in what generality

`not_signed_product_form` allows **arbitrary** `e_i ∈ ℤ`, not just `±1`: positivity of the base is
what the argument consumes, and it is indifferent to the exponent. `not_product_form_pm_one` is the
literal Theorem-D-shaped corollary, and its hypothesis `e_i ∈ {+1,-1}` is therefore **unused** — it
is stated only so that a reader matching the paper display finds the paper's statement, and the
`hpm`-is-discharged-by-nothing fact is noted at that declaration.

`not_product_form_ratio` is the same obstruction written as a quotient of two unsigned products,
which is how the paper display is actually typeset.

## Scope — unchanged from the numerator-only file

Theorem D itself is still **not** formalised: `Y^λ_ρ`, Hall-Littlewood `P_λ`, Kostka-Foulkes
polynomials and charge have no Lean definitions in this project, and the identification
`D_{a,b} = Y^{(a,b)}_{(a,b)} = t^b - t^{b-1} + 1` is paper-side (Theorem C at `m = b`). Here
`t^b - t^{b-1} + 1` is simply written down. What this file adds is exponent generality in the
obstruction mechanism, nothing else.

## Division by zero is Lean's, not the paper's

In `ℝ`, `(0 : ℝ) ^ (-1 : ℤ) = 0` and `x / 0 = 0`. So a careless reading of the statements below
could be satisfied by making a factor vanish rather than by a genuine identity. That is precisely
what the hypothesis `1 ≤ d_i` excludes, and `not_signed_prod_ne_zero_without_hd` shows the
hypothesis is load-bearing **as a counterexample** — at `d = {(0,-1)}` the conclusion is false, not
merely unproved.
-/

namespace TworowD4Kernel.ProductForm

open Set

/-- For `t ∈ (-1,0)`, `k ≥ 1` and **any** integer `e`, the signed factor `(1 - t^k)^e` is strictly
positive.

The whole extension to denominators is this one line: `one_sub_pow_pos` gives a positive base, and
`zpow_pos` carries positivity to every integer power, `e < 0` included. -/
theorem one_sub_zpow_pos {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) {k : ℕ} (hk : 1 ≤ k) (e : ℤ) :
    0 < (1 - t ^ k) ^ e :=
  zpow_pos (one_sub_pow_pos ht hk) e

/-- A finite product of signed factors `(1 - t^{d_i})^{e_i}` is strictly positive on `(-1,0)`,
given `d_i ≥ 1`. Exponents are indexed by a `Multiset (ℕ × ℤ)`: the pairs carry no order, and the
same `(d, e)` may repeat. -/
theorem prod_signed_pos (d : Multiset (ℕ × ℤ)) (hd : ∀ p ∈ d, 1 ≤ p.1)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    0 < (d.map (fun p => (1 - t ^ p.1) ^ p.2)).prod := by
  refine Multiset.prod_pos ?_
  intro a ha
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp ha
  exact one_sub_zpow_pos ht (hd p hp) p.2

/-- **The elementary obstruction, signed.** On `(-1,0)` the ratio `t^c ∏_i (1 - t^{d_i})^{e_i}` is
nonzero for every `c`, every multiset of `(d_i, e_i)` with `d_i ≥ 1`, and every sign pattern.

Companion to `prod_one_sub_pow_ne_zero`, which is the `e_i = +1` case. -/
theorem prod_signed_ne_zero (c : ℕ) (d : Multiset (ℕ × ℤ)) (hd : ∀ p ∈ d, 1 ≤ p.1)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 0) :
    t ^ c * (d.map (fun p => (1 - t ^ p.1) ^ p.2)).prod ≠ 0 :=
  mul_ne_zero (pow_ne_zero c (ne_of_lt ht.2)) (ne_of_gt (prod_signed_pos d hd ht))

/-- **The deliverable.** For odd `b ≥ 3` the function `t ↦ t^b - t^{b-1} + 1` admits no
representation `t^c ∏_i (1 - t^{d_i})^{e_i}` with `d_i ≥ 1` and `e_i ∈ ℤ` arbitrary.

`exists_root_Ioo` (`NonCyclotomicRoot.lean`) supplies `t₀ ∈ (-1,0)` with `D_b(t₀) = 0`;
`prod_signed_ne_zero` says the right side is nonzero there.

Reference: Theorem D, `projects/proofs/2026-10-07-two-part-green-polynomials.tex`. -/
theorem not_signed_product_form (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (d : Multiset (ℕ × ℤ)), (∀ p ∈ d, 1 ≤ p.1) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (d.map (fun p => (1 - t ^ p.1) ^ p.2)).prod := by
  rintro ⟨c, d, hd, hid⟩
  obtain ⟨t₀, ht₀, hroot⟩ := TworowD4Kernel.exists_root_Ioo b hb hodd
  have hne := prod_signed_ne_zero c d hd ht₀
  rw [← hid t₀, hroot] at hne
  exact hne rfl

/-- **Theorem D's literal display**, exponents restricted to `±1`.

The hypothesis `hpm : ∀ p ∈ d, p.2 = 1 ∨ p.2 = -1` is **not used**: this statement is a weakening
of `not_signed_product_form`, which already allows every integer exponent. It is recorded because
the paper writes `±1`, and a reader checking the formalisation against the display should find the
display. Do not read `hpm` as load-bearing — deleting it yields a theorem that is still true (it is
`not_signed_product_form` verbatim). -/
theorem not_product_form_pm_one (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (d : Multiset (ℕ × ℤ)), (∀ p ∈ d, 1 ≤ p.1) ∧ (∀ p ∈ d, p.2 = 1 ∨ p.2 = -1) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (d.map (fun p => (1 - t ^ p.1) ^ p.2)).prod := by
  rintro ⟨c, d, hd, _hpm, hid⟩
  exact not_signed_product_form b hb hodd ⟨c, d, hd, hid⟩

/-- **The paper's typesetting: a quotient of two unsigned products.** No identity
`D_b(t) = t^c ∏_{i}(1 - t^{n_i}) / ∏_{j}(1 - t^{m_j})` holds, for odd `b ≥ 3`, all `n_i, m_j ≥ 1`.

Proved directly rather than by transport along `not_signed_product_form`: both products are
positive at the root, so the quotient is nonzero there without any `zpow`/division bookkeeping. -/
theorem not_product_form_ratio (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (num den : Multiset ℕ), (∀ k ∈ num, 1 ≤ k) ∧ (∀ k ∈ den, 1 ≤ k) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (num.map (fun k => 1 - t ^ k)).prod
            / (den.map (fun k => 1 - t ^ k)).prod := by
  rintro ⟨c, num, den, hnum, hden, hid⟩
  obtain ⟨t₀, ht₀, hroot⟩ := TworowD4Kernel.exists_root_Ioo b hb hodd
  have hpn : 0 < (num.map (fun k => 1 - t₀ ^ k)).prod := by
    refine Multiset.prod_pos ?_
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp ha
    exact one_sub_pow_pos ht₀ (hnum k hk)
  have hpd : 0 < (den.map (fun k => 1 - t₀ ^ k)).prod := by
    refine Multiset.prod_pos ?_
    intro a ha
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp ha
    exact one_sub_pow_pos ht₀ (hden k hk)
  have hne : t₀ ^ c * (num.map (fun k => 1 - t₀ ^ k)).prod
      / (den.map (fun k => 1 - t₀ ^ k)).prod ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero c (ne_of_lt ht₀.2)) (ne_of_gt hpn)) (ne_of_gt hpd)
  rw [← hid t₀, hroot] at hne
  exact hne rfl

/-! ## Two controls

The first kills the route this session was told to take; the second shows which hypothesis is
actually carrying the statement. -/

/-- **The named route's premise, refuted.** After clearing denominators the left side is
`D_b(t) · ∏_{k ∈ den}(1 - t^k)`. At `t = 1` this is **zero**, not `D_b(1) = 1`, whenever `den` is
nonempty — because every factor `1 - 1^k` is `0`. So the proposed separation of the two sides by
their value at `t = 1` has no content in exactly the case the denominators were introduced for.

Note the statement is for *any* `b` and any nonempty `den`: no oddness, no `b ≥ 3`. -/
theorem cleared_lhs_eq_zero_at_one (b : ℕ) (den : Multiset ℕ) (hden : den ≠ 0) :
    ((1 : ℝ) ^ b - (1 : ℝ) ^ (b - 1) + 1) * (den.map (fun k => 1 - (1 : ℝ) ^ k)).prod = 0 := by
  obtain ⟨k, hk⟩ := Multiset.exists_mem_of_ne_zero hden
  have : (0 : ℝ) ∈ den.map (fun k => 1 - (1 : ℝ) ^ k) :=
    Multiset.mem_map.mpr ⟨k, hk, by simp⟩
  rw [Multiset.prod_eq_zero this, mul_zero]

/-- With `d = {(0, -1)}` the single factor is `(1 - t^0)^{-1} = 0^{-1} = 0` in `ℝ`, so the product
vanishes at every `t`. This is the `e = -1` analogue of `prod_eq_zero_of_exponent_zero`, and it is
the reason the signed statements need `1 ≤ d_i`: Lean's `0^{-1} = 0` makes a `0` exponent satisfy
the identity trivially, from the denominator side as well as the numerator side. -/
theorem signed_prod_eq_zero_of_exponent_zero (c : ℕ) (t : ℝ) :
    t ^ c * ((({(0, -1)} : Multiset (ℕ × ℤ))).map
      (fun p => (1 - t ^ p.1) ^ p.2)).prod = 0 := by
  simp

/-- **The ablation, as a theorem.** `prod_signed_ne_zero` with `hd` deleted is false. A failed
`lake build` would be a fact about my proof; this is a fact about the statement. -/
theorem not_signed_prod_ne_zero_without_hd :
    ¬ ∀ (c : ℕ) (d : Multiset (ℕ × ℤ)) (t : ℝ), t ∈ Ioo (-1 : ℝ) 0 →
      t ^ c * (d.map (fun p => (1 - t ^ p.1) ^ p.2)).prod ≠ 0 := by
  intro h
  have hmem : (-(1/2) : ℝ) ∈ Ioo (-1 : ℝ) 0 := by constructor <;> norm_num
  exact h 0 {(0, -1)} (-(1/2)) hmem (signed_prod_eq_zero_of_exponent_zero 0 (-(1/2)))

end TworowD4Kernel.ProductForm
