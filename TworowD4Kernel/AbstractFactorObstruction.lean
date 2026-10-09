/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SignedProductFormObstruction

/-!
# The factor class as a hypothesis: `D_b` has no product form over *any* admissible factors

`TworowD4Kernel/ProductFormObstruction.lean` and
`TworowD4Kernel/SignedProductFormObstruction.lean` prove that for odd `b >= 3` the function
`D_b(t) = t^b - t^(b-1) + 1` is not of the shape `t^c * prod_i (1 - t^(d_i))^(e_i)`. Each of those
files widened the **exponents** (`e_i = +1`, then `e_i` over all of `Z`). Neither widened the
**factors**: the shape `1 - t^d` is hard-coded into every statement.

This file makes the factor class a hypothesis. The factors become an arbitrary finite family of
real functions `f_i : R -> R`, and the single thing assumed about them is that they do not vanish
at a root of `D_b` in `(-1,0)`.

Reference: Theorem D, `projects/proofs/2026-10-07-two-part-green-polynomials.tex`. The analytic
input is `TworowD4Kernel.exists_root_Ioo` (`NonCyclotomicRoot.lean`).

## What the argument actually consumes: nonvanishing, not positivity

The gap note for this file predicted that *positivity at the root* is the load-bearing hypothesis,
on the evidence that `not_product_form_pm_one`'s sign hypothesis `hpm` turned out to be unused.
Formalising it shows the prediction was one notch too strong. The chain is

* `f_i t != 0`  =>  `(f_i t)^(e_i) != 0`   (`zpow_ne_zero`; works for `e_i < 0` too),
* a finite product of nonzero reals is nonzero (`Multiset.prod_ne_zero`),
* `t != 0` kills the monomial `t^c`,

and **no step of it mentions an order**. Positivity is merely how the instances
`f_i t = 1 - t^(d_i)` happen to achieve nonvanishing on `(-1,0)`; it is not what the
mechanism uses. So the hypothesis here is `p.1 t != 0`, and
`factor_class_strictly_wider` below records that this is a *strictly* larger admissible class
than the positive one -- `f t = t` is admissible for the theorems in this
file and inadmissible for a positivity-hypothesis version, at every point of `(-1,0)`.

That matters for the intended application: among the cyclotomic polynomials, `Phi_1(t) = t - 1` is
**negative** on `(-1,0)` while `Phi_n` for `n >= 2` is positive there. A positivity hypothesis
cannot see `Phi_1`; a nonvanishing hypothesis can. See `not_product_form_cyclotomic_low` for the
`Phi_1, Phi_2` instance, and the scope note below for what is *not* claimed about general `Phi_n`.

## Mathlib already has the packaging (overlap guard, 2026-10-09 c2)

The abstraction needed no new mechanism: `Multiset.prod_ne_zero`
(`Mathlib/Algebra/BigOperators/Ring/Multiset.lean`) and `Multiset.prod_pos`
(`Mathlib/Algebra/Order/BigOperators/GroupWithZero/Multiset.lean:64`) are exactly the
"product of nonzeros / positives at a point" statements, and they are already the engines of the
two earlier files. The core lemma below is a two-line instance of the first. A statement-shape
search over this repo found **no** function-valued factor family (`grep "R -> R"` in
`TworowD4Kernel/`: no hits), so nothing here duplicates an existing declaration.

## Scope -- unchanged, and one new boundary

`Y^lambda_rho`, Hall-Littlewood `P_lambda`, Kostka-Foulkes polynomials and charge have **no Lean
definitions in this project**; the identification `D_{a,b} = Y^{(a,b)}_{(a,b)} = t^b - t^(b-1) + 1`
is paper-side (Theorem C at `m = b`). Here `t^b - t^(b-1) + 1` is simply written down, and
Theorem D itself is **not** formalised. `unproved != unformalised`.

New boundary: `Odd b` is **not** removable *from this file*, and that is a fact about the
mathematics. For even `b`, `D_b` has no real root at all (`not_exists_root_Ioo_four` records
`b = 4` as a theorem), and every statement here is proved by evaluating at a real root in
`(-1,0)`. Widening the factor class does nothing for even `b`.

Correction to this session's gap note, which predicted the even case "needs a coefficient argument
with no root location in it": it is **closed on paper**, same day, and *not* by a coefficient
argument. `D_b(alpha) = 0` is `alpha^(b-1)(alpha - 1) = -1`, so `|alpha| = 1` forces
`|alpha - 1| = 1` too, and the unit circles about `0` and `1` meet in exactly two points; since
`deg D_b = b > 2` some root is off the circle. That is a root-location argument on the unit circle
rather than on `(-1,0)` -- see `projects/proofs/2026-10-09-c2-product-form-invariance.tex`. It is
**not formalised**, here or anywhere, and nothing in this file should be read as covering even `b`.

Also not claimed here: that `D_b` is not a product of **general** cyclotomic polynomials. The
instance by the present mechanism would need "`Phi_n` has no root in `(-1,0)` for every `n`"; only
`n = 1, 2` are proved below, by hand. On paper the stronger statement is already available --
`Phi_6` is the *only* cyclotomic that can divide `D_b`, and it does iff `b = 2 mod 6`, same
reference -- so this is an unformalised known result and a concrete next Lean target, not an open
question.
-/

namespace TworowD4Kernel.ProductForm

open Set

/-! ## The mechanism, with the factor class as a hypothesis -/

/-- **The core lemma, abstracted over the factors.** At any point `t != 0` at which every factor
`f_i` is nonzero, the signed product form `t^c * prod_i (f_i t)^(e_i)` is nonzero.

The factor family is a `Multiset ((R -> R) x Z)`: the pairs `(f_i, e_i)` carry no order and may
repeat, matching the index type used for `(d_i, e_i)` in `SignedProductFormObstruction.lean`.

Note what is *absent*: no interval, no order, no positivity, no hypothesis on `e_i`. This is a
two-line instance of `Multiset.prod_ne_zero`. -/
theorem prod_abstract_ne_zero (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ))
    {t : ℝ} (ht : t ≠ 0) (hf : ∀ p ∈ f, p.1 t ≠ 0) :
    t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero c ht) (Multiset.prod_ne_zero ?_)
  intro hmem
  obtain ⟨p, hp, hpeq⟩ := Multiset.mem_map.mp hmem
  exact zpow_ne_zero p.2 (hf p hp) hpeq

/-- **The deliverable, in its weakest form.** For odd `b >= 3`, and any `c` and any factor family
`f` whose members are nonzero *at every root of `D_b` in `(-1,0)`*, the identity
`D_b(t) = t^c * prod_i (f_i t)^(e_i)` fails at some real `t`.

The hypothesis `hf` is as weak as the proof allows: it is consulted only at a root, and only for
nonvanishing. Everything else -- the shape of the `f_i`, the signs of the `e_i`, the behaviour of
`f_i` away from the root -- is unconstrained. -/
theorem not_abstract_product_form (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b)
    (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ))
    (hf : ∀ t ∈ Ioo (-1 : ℝ) 0, t ^ b - t ^ (b - 1) + 1 = 0 → ∀ p ∈ f, p.1 t ≠ 0) :
    ¬ ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1 = t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod := by
  intro hid
  obtain ⟨t₀, ht₀, hroot⟩ := TworowD4Kernel.exists_root_Ioo b hb hodd
  have hne := prod_abstract_ne_zero c f (ne_of_lt ht₀.2) (hf t₀ ht₀ hroot)
  rw [← hid t₀, hroot] at hne
  exact hne rfl

/-- **The deliverable in the brief's shape**: admissibility of the factor class as a conjunct
inside the existential, with the simpler hypothesis "nonvanishing on all of `(-1,0)`" (which is
what every instance below actually verifies, root location being irrelevant to them). -/
theorem not_exists_abstract_product_form (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ)),
      (∀ p ∈ f, ∀ t ∈ Ioo (-1 : ℝ) 0, p.1 t ≠ 0) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod := by
  rintro ⟨c, f, hf, hid⟩
  exact not_abstract_product_form b hb hodd c f
    (fun t ht _ p hp => hf p hp t ht) hid

/-- The positivity-hypothesis version, for the record: it is a *corollary* of the nonvanishing one,
by `ne_of_gt`. Keeping both makes the comparison in `factor_class_strictly_wider` precise. -/
theorem not_exists_abstract_product_form_of_pos (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ)),
      (∀ p ∈ f, ∀ t ∈ Ioo (-1 : ℝ) 0, 0 < p.1 t) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod := by
  rintro ⟨c, f, hf, hid⟩
  exact not_exists_abstract_product_form b hb hodd
    ⟨c, f, fun p hp t ht => ne_of_gt (hf p hp t ht), hid⟩

/-! ## The three existing theorems, re-derived as instances

Each is obtained by instantiating the factor family at `f_i t = 1 - t^(d_i)`; the admissibility
hypothesis is discharged by `one_sub_pow_ne_zero` from `ProductFormObstruction.lean`, which is the
only place the shape `1 - t^d` appears in this file. The primed names are new declarations: the
originals are **left standing** in their own files, proved directly, not replaced by transport. -/

/-- `not_signed_product_form` as an instance of the abstract theorem. -/
theorem not_signed_product_form' (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (d : Multiset (ℕ × ℤ)), (∀ p ∈ d, 1 ≤ p.1) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (d.map (fun p => (1 - t ^ p.1) ^ p.2)).prod := by
  rintro ⟨c, d, hd, hid⟩
  refine not_exists_abstract_product_form b hb hodd
    ⟨c, d.map (fun p => ((fun t : ℝ => 1 - t ^ p.1), p.2)), ?_, ?_⟩
  · intro q hq t ht
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
    exact one_sub_pow_ne_zero ht (hd p hp)
  · intro t
    rw [hid t, Multiset.map_map]
    rfl

/-- `not_product_form` (the unsigned, `e_i = +1` shape) as an instance of the abstract theorem. -/
theorem not_product_form' (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (d : Multiset ℕ), (∀ k ∈ d, 1 ≤ k) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1 = t ^ c * (d.map (fun k => 1 - t ^ k)).prod := by
  rintro ⟨c, d, hd, hid⟩
  refine not_exists_abstract_product_form b hb hodd
    ⟨c, d.map (fun k => ((fun t : ℝ => 1 - t ^ k), (1 : ℤ))), ?_, ?_⟩
  · intro q hq t ht
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
    exact one_sub_pow_ne_zero ht (hd p hp)
  · intro t
    rw [hid t, Multiset.map_map]
    simp

/-- `not_product_form_ratio` (the paper's typesetting, a quotient of two unsigned products) as an
instance of the abstract theorem: the numerator factors enter with exponent `+1`, the denominator
factors with exponent `-1`, and the two families are combined by multiset addition. -/
theorem not_product_form_ratio' (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (num den : Multiset ℕ), (∀ k ∈ num, 1 ≤ k) ∧ (∀ k ∈ den, 1 ≤ k) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1
        = t ^ c * (num.map (fun k => 1 - t ^ k)).prod
            / (den.map (fun k => 1 - t ^ k)).prod := by
  rintro ⟨c, num, den, hnum, hden, hid⟩
  refine not_exists_abstract_product_form b hb hodd
    ⟨c, num.map (fun k => ((fun t : ℝ => 1 - t ^ k), (1 : ℤ)))
        + den.map (fun k => ((fun t : ℝ => 1 - t ^ k), (-1 : ℤ))), ?_, ?_⟩
  · intro q hq t ht
    rw [Multiset.mem_add] at hq
    rcases hq with hq | hq
    · obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp hq
      exact one_sub_pow_ne_zero ht (hnum k hk)
    · obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.mp hq
      exact one_sub_pow_ne_zero ht (hden k hk)
  · intro t
    rw [hid t, Multiset.map_add, Multiset.prod_add, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, zpow_one, zpow_neg, zpow_one, Multiset.prod_map_inv]
    rw [div_eq_mul_inv, mul_assoc]

/-! ## The generalisation has content: the admissible class is strictly wider

The gap note predicted *positivity* at the root. The mechanism consumes only *nonvanishing*, and
the gap between the two is not empty: `f t = t` is nonvanishing on all of `(-1,0)` and positive
nowhere on it. So `not_exists_abstract_product_form` reaches factor families that
`not_exists_abstract_product_form_of_pos` cannot, and the widening is a theorem rather than a
remark.

Memory note (2026-10-09 c2): *test the hypothesis on the admissible class, not only on the target.*
A proposed hypothesis that the class's own generators fail is worthless; here the witness is
exhibited explicitly. -/

/-- **The two hypotheses are not equivalent.** The identity function is admissible for the
nonvanishing theorem at every point of `(-1,0)` and admissible for the positivity theorem at no
point of it. -/
theorem factor_class_strictly_wider :
    (∀ t ∈ Ioo (-1 : ℝ) 0, (fun s : ℝ => s) t ≠ 0) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 0, ¬ (0 < (fun s : ℝ => s) t)) := by
  refine ⟨fun t ht => ne_of_lt ht.2, fun t ht => not_lt.mpr (le_of_lt ht.2)⟩

/-- **A factor class no earlier theorem in this repo covers.** For odd `b >= 3` there is no
representation `D_b(t) = t^c * (t - 1)^(e_1) * (t + 1)^(e_2)` with `e_1, e_2 : Z`.

These are the cyclotomic polynomials `Phi_1(t) = t - 1` and `Phi_2(t) = t + 1`. On `(-1,0)` the
first is **negative** and the second positive, so this instance is out of reach of a positivity
hypothesis and of both `1 - t^d` statements, while the nonvanishing hypothesis handles it in one
line each.

Not claimed: the general cyclotomic statement. That needs `Phi_n` root-free on `(-1,0)` for all
`n`, which is not proved in this project. -/
theorem not_product_form_cyclotomic_low (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ¬ ∃ (c : ℕ) (e₁ e₂ : ℤ),
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1 = t ^ c * ((t - 1) ^ e₁ * (t + 1) ^ e₂) := by
  rintro ⟨c, e₁, e₂, hid⟩
  refine not_exists_abstract_product_form b hb hodd
    ⟨c, {((fun t : ℝ => t - 1), e₁), ((fun t : ℝ => t + 1), e₂)}, ?_, ?_⟩
  · intro q hq t ht
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact ne_of_lt (by linarith [ht.2] : t - 1 < 0)
    · exact ne_of_gt (by linarith [ht.1] : (0 : ℝ) < t + 1)
  · intro t
    rw [hid t]
    simp

/-! ## Both hypotheses of the core lemma are load-bearing, as counterexamples

A failed `lake build` is a fact about my proof; a counterexample is a fact about the statement.
Note that abstracting the factor class makes the first ablation *sharper* than its concrete
ancestor `prod_eq_zero_of_exponent_zero`: there one had to reach for the exponent `d = 0` to make
`1 - t^d` vanish, whereas here the constant function `0` is a perfectly good factor shape, so
without `hf` the conclusion fails for a reason that has nothing to do with `t` at all. -/

/-- The zero function as a factor: the product vanishes at every `t`, for every `c`. -/
theorem abstract_prod_eq_zero_of_zero_factor (c : ℕ) (t : ℝ) :
    t ^ c * (({((fun _ : ℝ => (0 : ℝ)), (1 : ℤ))} : Multiset ((ℝ → ℝ) × ℤ)).map
      (fun p => (p.1 t) ^ p.2)).prod = 0 := by
  simp

/-- **Ablation 1.** `prod_abstract_ne_zero` with the admissibility hypothesis `hf` deleted is
false, witnessed by the constant factor `0` at `t = -1/2`. -/
theorem not_prod_abstract_ne_zero_without_hf :
    ¬ ∀ (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ)) (t : ℝ), t ≠ 0 →
      t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod ≠ 0 := by
  intro h
  exact h 0 {((fun _ : ℝ => (0 : ℝ)), (1 : ℤ))} (-(1/2)) (by norm_num)
    (abstract_prod_eq_zero_of_zero_factor 0 (-(1/2)))

/-- **Ablation 2.** `prod_abstract_ne_zero` with `ht : t ≠ 0` deleted is false: at `t = 0`, `c = 1`
and the *empty* factor family the monomial alone kills the product, with `hf` vacuously true. This
is why the obstruction theorems evaluate at a root in the **open** interval `(-1,0)`. -/
theorem not_prod_abstract_ne_zero_without_ht :
    ¬ ∀ (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ)) (t : ℝ), (∀ p ∈ f, p.1 t ≠ 0) →
      t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod ≠ 0 := by
  intro h
  exact h 1 0 0 (by simp) (by simp)

end TworowD4Kernel.ProductForm
