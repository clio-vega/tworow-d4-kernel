/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# `t^b - t^{b-1} + 1` has a real root in `(-1, 0)` for odd `b ≥ 3`

Formalisation of the **load-bearing arithmetic step** of Theorem D of
`proofs/2026-10-07-two-part-green-polynomials.tex`:

> Let `a > b ≥ 1`, `ρ = (a,b)`. Then `D_{a,b}(t) = Y^{(a,b)}_{(a,b)}(t) = t^b - t^{b-1} + 1`,
> and for every odd `b ≥ 3` this polynomial has a real root in `(-1,0)`; consequently it is not
> a product of cyclotomic polynomials and monomials, and no identity
> `Y^λ_ρ(t) = t^c ∏ (1 - t^{d_i})^{±1}` holds for all `ℓ(λ) ≤ 2` and all two-part `ρ`.

## What is formalised, and what is not

**Formalised here:** exactly the real-analytic statement `exists_root_Ioo` — the existence of the
root. This is the only step of Theorem D with analytic content, and the only one whose failure
would cost the theorem.

**NOT formalised here:** the rest of Theorem D. Its remaining clauses quantify over
`Y^λ_ρ`, Hall–Littlewood `P_λ`, Kostka–Foulkes polynomials and the charge statistic, **none of
which exist as Lean definitions in this project**. The closed form `D_{a,b} = t^b - t^{b-1} + 1`
is the `m = b` case of Theorem C on paper; here `t^b - t^{b-1} + 1` is simply *written down*.
A paper↔Lean dictionary is not a Lean definition: `unproved ≠ unformalised`, and nothing in this
file should be read as formalising the product-form null itself.

## The proof

Two evaluations and the intermediate value theorem.

* `b` odd ⇒ `b - 1` even ⇒ `D_b(-1) = (-1) - (+1) + 1 = -1 < 0`  (`Odd.neg_one_pow`,
  `Nat.Odd.sub_odd`).
* `b ≥ 3` ⇒ `b ≥ 1` and `b - 1 ≥ 1` ⇒ `D_b(0) = 0 - 0 + 1 = 1 > 0`  (`zero_pow`).
* `D_b` is continuous, so `intermediate_value_Ioo` applied on `Icc (-1) 0` puts
  `Ioo (D_b (-1)) (D_b 0) = Ioo (-1) 1 ∋ 0` in the image of `Ioo (-1) 0`.

**The `Odd b` hypothesis enters in exactly one place** — the sign of `(-1)^{b-1}` in
`eval_neg_one`. It is load-bearing: dropping it makes the statement false, since `b = 4` gives
`D_4(-1) = 1 - (-1) + 1 = 3 > 0`, and in fact `t^4 - t^3 + 1 > 0` on all of `[-1,0]`. See
`TworowD4KernelTests` for that evaluation as an executable check.

## The consequence, which is *not* proved here

Theorem D concludes non-cyclotomicity from this root. That step needs "every root of a cyclotomic
polynomial has modulus 1", so that a root with `|r| ∈ (0,1)` is neither a root of unity nor `0`.
It is a Mathlib-search question (`Polynomial.isRoot_cyclotomic_iff`, `IsPrimitiveRoot`) and is
deliberately left out of this file; `exists_root_Ioo` is the input it would consume.

Note, carried forward from the paper unchanged: **Theorem D's conclusion needs only one
non-cyclotomic witness**, and the odd-`b` family supplies infinitely many. The separate even-`b`
observation (`gap:evenb`, non-cyclotomic for `3 ≤ b ≤ 15`, *computed* and not proved) is therefore
not needed for, and does not weaken, the statement proved here.
-/

namespace TworowD4Kernel

open Set

/-- `D b t = t^b - t^{b-1} + 1`, the diagonal two-part Green polynomial `Y^{(a,b)}_{(a,b)}` for
`a > b` (Theorem D of `proofs/2026-10-07-two-part-green-polynomials.tex`). Here it is a bare
real function: the identification with `Y` is paper-side and is *not* formalised. -/
noncomputable def D (b : ℕ) (t : ℝ) : ℝ := t ^ b - t ^ (b - 1) + 1

theorem continuous_D (b : ℕ) : Continuous (D b) := by
  unfold D; fun_prop

/-- `D b (-1) = -1` **when `b` is odd**: `(-1)^b = -1` and `(-1)^{b-1} = 1` because `b - 1` is
even. This is the single place the parity hypothesis is used. -/
theorem D_eval_neg_one {b : ℕ} (hodd : Odd b) : D b (-1) = -1 := by
  have h1 : ((-1 : ℝ)) ^ b = -1 := hodd.neg_one_pow
  have h2 : ((-1 : ℝ)) ^ (b - 1) = 1 := (Nat.Odd.sub_odd hodd odd_one).neg_one_pow
  rw [D, h1, h2]
  ring

/-- `D b 0 = 1` for `b ≥ 2`: both `0^b` and `0^{b-1}` vanish. -/
theorem D_eval_zero {b : ℕ} (hb : 2 ≤ b) : D b 0 = 1 := by
  have h1 : ((0 : ℝ)) ^ b = 0 := zero_pow (by omega)
  have h2 : ((0 : ℝ)) ^ (b - 1) = 0 := zero_pow (by omega)
  rw [D, h1, h2]
  ring

/-- **The load-bearing step of Theorem D.** For every odd `b ≥ 3` the polynomial
`D_b(t) = t^b - t^{b-1} + 1` has a real root strictly between `-1` and `0`.

Proof: `D_b(-1) = -1 < 0 < 1 = D_b(0)` and `D_b` is continuous, so `intermediate_value_Ioo`
produces the root. The hypothesis `Odd b` is used only for `D_b(-1) = -1` and is load-bearing:
at `b = 4`, `D_4(-1) = 3 > 0`.

Reference: Theorem D, `proofs/2026-10-07-two-part-green-polynomials.tex`. -/
theorem exists_root_Ioo (b : ℕ) (hb : 3 ≤ b) (hodd : Odd b) :
    ∃ t ∈ Ioo (-1 : ℝ) 0, t ^ b - t ^ (b - 1) + 1 = 0 := by
  have hcont : ContinuousOn (D b) (Icc (-1 : ℝ) 0) := (continuous_D b).continuousOn
  have hmem : (0 : ℝ) ∈ Ioo (D b (-1)) (D b 0) := by
    rw [D_eval_neg_one hodd, D_eval_zero (by omega)]
    constructor <;> norm_num
  obtain ⟨t, ht, hft⟩ := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ 0) hcont hmem
  exact ⟨t, ht, hft⟩

/-! ## The `Odd b` hypothesis is load-bearing

Not merely "the proof uses it": with `Odd b` dropped the **statement is false**. At `b = 4` the
sign at `-1` reverses (`D 4 (-1) = 3 > 0`) and `D 4` is in fact strictly positive on all of
`[-1,0]`, so there is no sign change for the intermediate value theorem to exploit and no root in
`Ioo (-1) 0` at all. -/

theorem D_four_eval_neg_one : D 4 (-1) = 3 := by
  rw [D]; norm_num

theorem D_four_pos_of_mem_Icc {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 0) : 0 < D 4 t := by
  obtain ⟨h1, h2⟩ := ht
  rw [D]
  norm_num
  nlinarith [sq_nonneg t, sq_nonneg (t * t), sq_nonneg (t + 1)]

/-- **The ablation, as a theorem.** `exists_root_Ioo` with `Odd b` deleted is false: `b = 4`
satisfies `3 ≤ b` and has no root of `t^4 - t^3 + 1` in `(-1, 0)`. -/
theorem not_exists_root_Ioo_four :
    ¬ ∃ t ∈ Ioo (-1 : ℝ) 0, t ^ 4 - t ^ (4 - 1) + 1 = 0 := by
  rintro ⟨t, ht, hroot⟩
  have hmem : t ∈ Icc (-1 : ℝ) 0 := Ioo_subset_Icc_self ht
  have hpos := D_four_pos_of_mem_Icc hmem
  rw [D] at hpos
  exact absurd hroot (ne_of_gt hpos)

end TworowD4Kernel
