/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Tactic.ComputeDegree

/-!
# `D_b` has a root off the unit circle, for **every** `b ≥ 3`

`TworowD4Kernel/AbstractFactorObstruction.lean` proves that for **odd** `b ≥ 3` the function
`D_b(t) = t^b - t^(b-1) + 1` is not of the shape `t^c * prod_i (f_i t)^(e_i)` for any family of
real functions `f_i` nonvanishing on `(-1,0)`. Every statement there is proved by evaluating at a
real root of `D_b` in `(-1,0)`, and that root is what `Odd b` buys
(`TworowD4Kernel.exists_root_Ioo`). This file removes the parity hypothesis.

Reference: Theorem D, `projects/proofs/2026-10-09-c2-product-form-invariance.tex` (13 pp), which
closes even `b` on paper. The paper's phrasing -- *"the unit circles about `0` and `1` meet in
exactly two points"* -- sounds like plane geometry; it is four lines of `normSq` algebra, and that
is how it is formalised here (`re_eq_half_of_normSq`).

## The route

1. `D_b(α) = 0` is `α^(b-1) * (α - 1) = -1` (`re_eq_half_of_root`; rearrangement, no analysis).
2. If `‖α‖ = 1`, taking `normSq` in (1) gives `normSq (α - 1) = 1`.
3. `normSq α = 1` and `normSq (α - 1) = 1` together give **`re α = 1/2`** -- expand
   `normSq (α - 1) = normSq α - 2 re α + 1` and the two ones cancel (`re_eq_half_of_normSq`).
   No circle-intersection argument, and `α` is never pinned down to `exp(±iπ/3)`: `re α = 1/2`
   plus `normSq α = 1` is all the rest of the proof consumes.
4. Hence **`normSq (-1 - α) = normSq α + 2 re α + 1 = 3`** for every root on the circle.
5. So if *all* `b` roots were on the circle, evaluating the monic factorisation
   `D_b = prod (X - α)` at `t = -1` and taking `normSq` would give `3 ^ b`. But
   `D_b(-1) = (-1)^b - (-1)^(b-1) + 1` is `3` (even `b`) or `-1` (odd `b`), so
   `normSq (D_b(-1)) ≤ 9`, and `3 ^ b ≥ 27` for `b ≥ 3`. Contradiction.

**`3 ≤ b` is consumed exactly once, in step 5, as `3 ^ b > 9`.** The hypothesis is not a degree
bound in disguise; it is this one inequality.

### Where this differs from the brief's route

The brief closed step 4 differently: `α - 1 = α²` for a primitive 6th root of unity, so
`α^(b+1) = -1` and `b ≡ 2 (mod 6)`, followed by a degree count. That works but needs the two
roots named, a parity/conjugacy argument to rule out multiplicities, and a case split. Evaluating
at `-1` replaces all of it with one `Multiset.prod_replicate`, and -- a bonus -- needs **no case
split on the parity of `b` at all**, since both values of `D_b(-1)` have `normSq ≤ 9`. The
`b ≡ 2 (mod 6)` statement is a genuine theorem but is *not* needed for the obstruction, so it is
left unformalised rather than proved and unused.

## The factor class had to change, and that is a theorem, not a preference

The brief named the target as the existing statement *with `Odd b` deleted*, keeping the factor
class `Multiset ((ℝ → ℝ) × ℤ)` admissible when nonvanishing on `(-1,0)`.

**That statement is false for even `b`.** `exists_abstract_product_form_real_of_even` below
exhibits the counterexample: for even `b`, `D_b` has no real root at all, so `D_b` is *itself* an
admissible factor, with `c = 0` and one factor at exponent `+1`. Widening the *factors* cannot
repair the loss of the *evaluation point*. So the generalisation here moves to `ℂ` and replaces
"nonvanishing on `(-1,0)`" by **"nonvanishing off the unit circle"**, which is the condition the
concrete factors `1 - t^(d_i)` actually satisfy -- their zeros are roots of unity
(`one_sub_pow_ne_zero_of_norm_ne_one`). `exists_root_Ioo` is traded for
`exists_root_normSq_ne_one`.

A failed `lake build` is a fact about my proof; the counterexample is a fact about the statement.

## Scope -- unchanged from `AbstractFactorObstruction.lean`

`Y^lambda_rho`, Hall-Littlewood `P_lambda`, Kostka-Foulkes polynomials and charge have **no Lean
definitions in this project**; the identification `D_{a,b} = Y^{(a,b)}_{(a,b)} = t^b - t^(b-1) + 1`
is paper-side (Theorem C at `m = b`). Here `t^b - t^(b-1) + 1` is simply written down, and
Theorem D itself is **not** formalised. `unproved != unformalised`. What is formalised is the
polynomial obstruction and nothing else; the parent registry node `thm-D` keeps its `proved`
grade independently of this file.

Also not formalised: `Phi_6` is the only cyclotomic that can divide `D_b`, and does so iff
`b ≡ 2 (mod 6)` (same reference). Step 4 of the brief's route contains it; the proof above does
not go through it, so it remains a known-but-unformalised result and a concrete next target.
-/

namespace TworowD4Kernel.UnitCircle

open Complex Polynomial

/-! ## Step 1: the purely algebraic heart -/

/-- If `α` and `α - 1` both have modulus one then `re α = 1/2`. -/
theorem re_eq_half_of_normSq {α : ℂ} (h1 : normSq α = 1) (h2 : normSq (α - 1) = 1) :
    α.re = 1 / 2 := by
  rw [normSq_apply] at h1
  rw [normSq_apply, sub_re, sub_im] at h2
  simp only [one_re, one_im, sub_zero] at h2
  nlinarith [h1, h2]

/-- A root of `D_b` on the unit circle has real part `1/2`. -/
theorem re_eq_half_of_root {b : ℕ} (hb : 1 ≤ b) {α : ℂ}
    (hroot : α ^ b - α ^ (b - 1) + 1 = 0) (hnorm : normSq α = 1) :
    α.re = 1 / 2 := by
  have hb' : b - 1 + 1 = b := Nat.succ_pred_eq_of_pos hb
  have key : α ^ (b - 1) * (α - 1) = -1 := by
    have : α ^ b = α ^ (b - 1) * α := by rw [← pow_succ, hb']
    rw [this] at hroot; linear_combination hroot
  have hns : normSq (α ^ (b - 1)) * normSq (α - 1) = 1 := by
    rw [← map_mul, key]; simp [normSq_apply]
  rw [map_pow, hnorm, one_pow, one_mul] at hns
  exact re_eq_half_of_normSq hnorm hns

/-! ## Step 2: the polynomial, its degree, and its roots -/

/-- `D_{n+2}(X) = X^(n+2) - X^(n+1) + 1` as a polynomial over `ℂ`.

Parametrised by `n` rather than `b` so that `natDegree` is a literal successor and truncated
subtraction never appears inside the polynomial. `b = n + 2`. -/
noncomputable def Dpoly (n : ℕ) : ℂ[X] := X ^ (n + 2) - X ^ (n + 1) + 1

theorem Dpoly_monic (n : ℕ) : (Dpoly n).Monic := by
  unfold Dpoly; monicity!

theorem Dpoly_natDegree (n : ℕ) : (Dpoly n).natDegree = n + 2 := by
  unfold Dpoly; compute_degree!

theorem Dpoly_eval (n : ℕ) (z : ℂ) : (Dpoly n).eval z = z ^ (n + 2) - z ^ (n + 1) + 1 := by
  simp [Dpoly]

theorem Dpoly_splits (n : ℕ) : (Dpoly n).Splits := IsAlgClosed.splits (Dpoly n)

theorem Dpoly_card_roots (n : ℕ) : Multiset.card (Dpoly n).roots = n + 2 := by
  rw [(Dpoly_splits n).natDegree_eq_card_roots.symm, Dpoly_natDegree]

/-! ## Step 3: the contradiction -/

/-- **The content.** For every `b ≥ 3` the polynomial `D_b(t) = t^b - t^(b-1) + 1` has a complex
root off the unit circle. -/
theorem exists_root_normSq_ne_one (b : ℕ) (hb : 3 ≤ b) :
    ∃ α : ℂ, α ^ b - α ^ (b - 1) + 1 = 0 ∧ normSq α ≠ 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, b = n + 2 := ⟨b - 2, by omega⟩
  have hn : 1 ≤ n := by omega
  by_contra hcon
  push Not at hcon
  -- every root of `Dpoly n` lies on the unit circle, hence has `re = 1/2`
  have hroots : ∀ α ∈ (Dpoly n).roots, normSq (-1 - α) = 3 := by
    intro α hα
    have heval : α ^ (n + 2) - α ^ (n + 2 - 1) + 1 = 0 := by
      have := (mem_roots'.mp hα).2
      rw [IsRoot, Dpoly_eval] at this
      simpa using this
    have h1 : normSq α = 1 := hcon α heval
    have hre : α.re = 1 / 2 := re_eq_half_of_root (by omega) heval h1
    rw [normSq_apply] at h1 ⊢
    simp only [sub_re, sub_im, neg_re, neg_im, one_re, one_im, neg_zero]
    nlinarith [h1, hre]
  -- evaluate the root factorisation at `-1`
  have hprod : (Dpoly n).eval (-1) = (((Dpoly n).roots).map (fun a => (-1 : ℂ) - a)).prod :=
    (Dpoly_splits n).eval_eq_prod_roots_of_monic (Dpoly_monic n) (-1)
  have hns : normSq ((Dpoly n).eval (-1)) = 3 ^ (n + 2) := by
    have hrep : (((Dpoly n).roots.map (fun a => (-1 : ℂ) - a)).map normSq)
        = Multiset.replicate (n + 2) (3 : ℝ) := by
      rw [Multiset.map_map, Multiset.eq_replicate]
      refine ⟨by rw [Multiset.card_map, Dpoly_card_roots], ?_⟩
      intro x hx
      obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hx
      simpa using hroots a ha
    rw [hprod, map_multiset_prod, hrep, Multiset.prod_replicate]
  -- but `|D_b(-1)| <= 3`, so `3 ^ (n+2) <= 9`
  have hval : normSq ((Dpoly n).eval (-1)) ≤ 9 := by
    rw [Dpoly_eval]
    rcases Nat.even_or_odd n with he | ho
    · have h1 : ((-1 : ℂ)) ^ (n + 2) = 1 := by
        simpa using (he.add (by decide : Even 2)).neg_one_pow
      have h2 : ((-1 : ℂ)) ^ (n + 1) = -1 := by
        simpa using (he.add_one).neg_one_pow
      rw [h1, h2]; norm_num [normSq_apply]
    · have h1 : ((-1 : ℂ)) ^ (n + 2) = -1 := by
        simpa using (ho.add_even (by decide : Even 2)).neg_one_pow
      have h2 : ((-1 : ℂ)) ^ (n + 1) = 1 := by
        simpa using (ho.add_one).neg_one_pow
      rw [h1, h2]; norm_num [normSq_apply]
  rw [hns] at hval
  have : (27 : ℝ) ≤ 3 ^ (n + 2) := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ (n + 2) := by
        apply pow_le_pow_right₀ (by norm_num) (by omega)
  linarith

/-! ## Step 4: the obstruction, over the unit-circle factor class -/

/-- `normSq` and `‖·‖` detect the unit circle equally well. -/
theorem normSq_ne_one_iff {z : ℂ} : normSq z ≠ 1 ↔ ‖z‖ ≠ 1 := by
  rw [normSq_eq_norm_sq]
  constructor
  · intro h hn; exact h (by rw [hn]; norm_num)
  · intro h hn
    exact h (by nlinarith [norm_nonneg z, hn])

/-- **The core lemma, over `ℂ`.** At any `z ≠ 0` where every factor is nonzero, the signed
product form `z^c * prod_i (f_i z)^(e_i)` is nonzero. Verbatim the mechanism of
`TworowD4Kernel.ProductForm.prod_abstract_ne_zero`, with `ℝ` replaced by `ℂ`; no order is used
there either, which is exactly why the transfer is free. -/
theorem prod_abstract_ne_zero (c : ℕ) (f : Multiset ((ℂ → ℂ) × ℤ))
    {z : ℂ} (hz : z ≠ 0) (hf : ∀ p ∈ f, p.1 z ≠ 0) :
    z ^ c * (f.map (fun p => (p.1 z) ^ p.2)).prod ≠ 0 := by
  refine mul_ne_zero (pow_ne_zero c hz) (Multiset.prod_ne_zero ?_)
  intro hmem
  obtain ⟨p, hp, hpeq⟩ := Multiset.mem_map.mp hmem
  exact zpow_ne_zero p.2 (hf p hp) hpeq

/-- **The deliverable: no parity hypothesis.** For every `b ≥ 3` -- even `b` included -- there is
no representation `D_b(z) = z^c * prod_i (f_i z)^(e_i)` by complex factors `f_i` that are
nonvanishing off the unit circle.

`3 ≤ b` is consumed exactly once, in `exists_root_normSq_ne_one`, as `3 ^ b > 9`. -/
theorem not_exists_abstract_product_form_all_b (b : ℕ) (hb : 3 ≤ b) :
    ¬ ∃ (c : ℕ) (f : Multiset ((ℂ → ℂ) × ℤ)),
      (∀ p ∈ f, ∀ z : ℂ, ‖z‖ ≠ 1 → p.1 z ≠ 0) ∧
      ∀ z : ℂ, z ^ b - z ^ (b - 1) + 1 = z ^ c * (f.map (fun p => (p.1 z) ^ p.2)).prod := by
  rintro ⟨c, f, hf, hid⟩
  obtain ⟨α, hroot, hns⟩ := exists_root_normSq_ne_one b hb
  have hα0 : α ≠ 0 := by
    intro h
    rw [h, zero_pow (by omega : b ≠ 0), zero_pow (by omega : b - 1 ≠ 0)] at hroot
    norm_num at hroot
  have hne := prod_abstract_ne_zero c f hα0 (fun p hp => hf p hp α (normSq_ne_one_iff.mp hns))
  rw [← hid α, hroot] at hne
  exact hne rfl

/-! ## The class is the right one: it contains the factors of the paper's product form -/

/-- `1 - z^d` is admissible for `d >= 1`: all its zeros are roots of unity. This is what makes
the unit-circle class the correct generalisation of the `1 - t^d` shape -- the whole point of a
product form `prod (1 - t^(d_i))^(e_i)` is that its zeros and poles sit on the unit circle. -/
theorem one_sub_pow_ne_zero_of_norm_ne_one {d : ℕ} (hd : 1 ≤ d) {z : ℂ} (hz : ‖z‖ ≠ 1) :
    1 - z ^ d ≠ 0 := by
  intro h
  have hzd : z ^ d = 1 := by linear_combination -h
  have hn : ‖z‖ ^ d = 1 := by rw [← norm_pow, hzd, norm_one]
  rcases lt_trichotomy ‖z‖ 1 with h1 | h1 | h1
  · have := pow_lt_one₀ (norm_nonneg z) h1 (by omega : d ≠ 0); linarith
  · exact hz h1
  · have := one_lt_pow₀ h1 (by omega : d ≠ 0); linarith

/-- **The transported statement.** For every `b >= 3`, `D_b` is not a signed product of factors
`1 - z^(d_i)` over `ℂ`. For odd `b` this is
`TworowD4Kernel.ProductForm.not_signed_product_form'` read over `ℂ`; the content here is that
`Odd b` is gone. -/
theorem not_signed_product_form_all_b (b : ℕ) (hb : 3 ≤ b) :
    ¬ ∃ (c : ℕ) (d : Multiset (ℕ × ℤ)), (∀ p ∈ d, 1 ≤ p.1) ∧
      ∀ z : ℂ, z ^ b - z ^ (b - 1) + 1
        = z ^ c * (d.map (fun p => (1 - z ^ p.1) ^ p.2)).prod := by
  rintro ⟨c, d, hd, hid⟩
  refine not_exists_abstract_product_form_all_b b hb
    ⟨c, d.map (fun p => ((fun z : ℂ => 1 - z ^ p.1), p.2)), ?_, ?_⟩
  · intro q hq z hz
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp hq
    exact one_sub_pow_ne_zero_of_norm_ne_one (hd p hp) hz
  · intro z
    rw [hid z, Multiset.map_map]
    rfl

/-! ## Scope: the `(-1,0)` factor class does **not** extend to even `b`, and that is a theorem

The brief for this session named the target as "the existing statement with the parity hypothesis
dropped", i.e. `TworowD4Kernel.ProductForm.not_exists_abstract_product_form` minus `Odd b`, with
its factor class `f : Multiset ((ℝ → ℝ) × ℤ)` admissible when nonvanishing on `(-1,0)`.

**That statement is false for even `b`, and the witness is `D_b` itself.** For even `b`, `D_b` has
no real root at all, so `D_b` is its own admissible factor, `c = 0`, one factor, exponent `+1`.
The real-interval class is simply too wide once there is no real root to evaluate at: widening the
*factors* cannot repair the loss of the *evaluation point*. This is why the generalisation above
moves to `ℂ` and replaces "nonvanishing on `(-1,0)`" by "nonvanishing off the unit circle" --
`exists_root_Ioo` is traded for `exists_root_normSq_ne_one`.

A failed `lake build` would have been a fact about my proof; the theorem below is a fact about
the statement. -/

/-- **The brief's literal target is false for even `b`.** `D_b` itself is an admissible factor. -/
theorem exists_abstract_product_form_real_of_even (b : ℕ) (hb : 2 ≤ b) (heven : Even b) :
    ∃ (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ)),
      (∀ p ∈ f, ∀ t ∈ Set.Ioo (-1 : ℝ) 0, p.1 t ≠ 0) ∧
      ∀ t : ℝ, t ^ b - t ^ (b - 1) + 1 = t ^ c * (f.map (fun p => (p.1 t) ^ p.2)).prod := by
  have hodd : Odd (b - 1) := Nat.Even.sub_odd (by omega : 1 ≤ b) heven odd_one
  refine ⟨0, {((fun t : ℝ => t ^ b - t ^ (b - 1) + 1), (1 : ℤ))}, ?_, ?_⟩
  · intro p hp t ht
    simp only [Multiset.mem_singleton] at hp
    subst hp
    have h1 : (0 : ℝ) < t ^ b := heven.pow_pos (ne_of_lt ht.2)
    have h2 : t ^ (b - 1) < 0 := hodd.pow_neg ht.2
    intro hzero
    dsimp only at hzero
    linarith
  · intro t
    simp

end UnitCircle

end TworowD4Kernel
