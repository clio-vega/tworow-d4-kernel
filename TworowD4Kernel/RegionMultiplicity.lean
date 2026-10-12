/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.RootMultiplicityProduct

/-!
# The region condition forces the Korff multiplicities to be positive on `J`

Formalisation of **Lemma `lem:wd`** ("gap 3") of
`proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`:

> If `i ∈ J(θ^{(a)})` then `m_i(x^{(a-1)}) ≥ 1`, so `(eq:Psi)` is a product of factors
> `(1 - t^m)` with `m ≥ 1`.

The objects are HKKO's lattice-path region (`arXiv:2301.13117`, Prop. 2.7 — cited at line 199
of the `.tex` above),
`R = {x ∈ ℤ^h : x_1 ≥ x_2 ≥ ⋯ ≥ x_h ≥ x_1 - w}`,
and Korff's multiplicity vector and ascent set (`arXiv:1110.6356`, (5.13) — cited at line 190
of the `.tex` above), transported to `R` by Prop. `prop:dict` of the same file:

* `(eq:mvec)`  `m_i(x) = x_i - x_{i+1}` for `1 ≤ i < h`,  `m_h(x) = w - (x_1 - x_h)`;
* `(eq:Psi)`   `J(θ) = {i ∈ ℤ/hℤ : θ_i = 0, θ_{i+1} = 1}`, with `θ_{h+1} := θ_1`.

## Indexing

Indices are **1-based `ℕ`**, matching the paper's `1 ≤ i ≤ h` verbatim; values are in `ℤ`
(`m_h` is a difference `w - (x_1 - x_h)` that is only nonnegative *because* of the region
condition, so truncated `ℕ` subtraction would smuggle the conclusion into the definition).
The cyclic wrap `θ_{h+1} = θ_1` is carried by `succIdx`, not by `ZMod h`, because the region
condition `x_1 ≥ ⋯ ≥ x_h` is **not** cyclic — only `m` and `J` are.

## Scope audit: what the paper's proof actually uses

The printed proof uses the region condition **only at the endpoint `y = x + θ`**, never at `x`.
That is recorded in the hypothesis of `one_le_mult_of_mem_J`: it takes `Mem h w (x + θ)` and
no assumption on `x` at all. This is strictly stronger than the paper's statement, which reads
as if both endpoints of the step are in `R`.

## Non-vacuity

`Mem h w x → 0 ≤ mult h w x i` (`mult_nonneg`) is the region condition alone, with no
reference to `J`. So `J`-membership is exactly what upgrades `≥ 0` to `≥ 1`; the main theorem
is not a restatement of the region condition. (This is the paper's own step (ii) of
`prop:dict`.)
-/

namespace TworowD4Kernel.Region

open Polynomial

variable {h : ℕ} {w : ℤ} {x : ℕ → ℤ} {θ : ℕ → Bool}

/-- The `ℤ`-value of a `0/1` step vector `θ ∈ {0,1}^h` at index `i`. -/
def stepVal (θ : ℕ → Bool) (i : ℕ) : ℤ := if θ i then 1 else 0

/-- Translation of a point of `ℤ^h` by a `0/1` step vector: the path step `x ↦ x + θ`. -/
def shift (x : ℕ → ℤ) (θ : ℕ → Bool) : ℕ → ℤ := fun i => x i + stepVal θ i

/-- HKKO's region `R = {x : x_1 ≥ x_2 ≥ ⋯ ≥ x_h ≥ x_1 - w}` (`arXiv:2301.13117`, Prop. 2.7).
`mono` is the weak decrease along `1 ≤ i < h`; `wrap` is the cylindric closing condition. -/
structure Mem (h : ℕ) (w : ℤ) (x : ℕ → ℤ) : Prop where
  mono : ∀ i, 1 ≤ i → i < h → x (i + 1) ≤ x i
  wrap : x 1 - w ≤ x h

/-- Korff's multiplicity vector `(eq:mvec)`: `m_i(x) = x_i - x_{i+1}` for `i < h`, and the
wrapped value `m_h(x) = w - (x_1 - x_h)` at the last site. -/
def mult (h : ℕ) (w : ℤ) (x : ℕ → ℤ) (i : ℕ) : ℤ :=
  if i < h then x i - x (i + 1) else w - (x 1 - x h)

/-- The cyclic successor of a site index: `h + 1` is identified with `1`. This is the paper's
convention `θ_{h+1} := θ_1` in `(eq:Psi)`. -/
def succIdx (h i : ℕ) : ℕ := if i = h then 1 else i + 1

/-- Korff's ascent set `J(θ) = {i : θ_i = 0, θ_{i+1} = 1}`, cyclic of period `h`. -/
def inJ (h : ℕ) (θ : ℕ → Bool) (i : ℕ) : Prop :=
  θ i = false ∧ θ (succIdx h i) = true

@[simp] theorem succIdx_self (h : ℕ) : succIdx h h = 1 := by simp [succIdx]

theorem succIdx_of_lt {i : ℕ} (hi : i < h) : succIdx h i = i + 1 := by
  simp [succIdx, Nat.ne_of_lt hi]

@[simp] theorem stepVal_false (hθ : θ i = false) : stepVal θ i = 0 := by simp [stepVal, hθ]

@[simp] theorem stepVal_true (hθ : θ i = true) : stepVal θ i = 1 := by simp [stepVal, hθ]

/-- **Non-vacuity control**, and step (ii) of `prop:dict`: the region condition *by itself*
gives `m_i(x) ≥ 0` for every site `1 ≤ i ≤ h`, with no reference to `J`. -/
theorem mult_nonneg (hx : Mem h w x) {i : ℕ} (hi1 : 1 ≤ i) (hih : i ≤ h) :
    0 ≤ mult h w x i := by
  rcases Nat.lt_or_ge i h with hlt | hge
  · have := hx.mono i hi1 hlt
    simp only [mult, if_pos hlt]
    omega
  · have hih' : i = h := le_antisymm hih hge
    subst hih'
    have := hx.wrap
    simp only [mult, if_neg (Nat.lt_irrefl i)]
    omega

/-- **Gap 3, Lemma `lem:wd`.** If `i ∈ J(θ)` then `m_i(x) ≥ 1`.

The hypothesis is that the **endpoint** `x + θ` of the step lies in the region; the paper's
proof uses nothing about `x` itself. Two cases, exactly as printed: for `i < h` the pair
`θ_i = 0, θ_{i+1} = 1` makes the endpoint's `mono` inequality at `i` read
`x_{i+1} + 1 ≤ x_i`; for `i = h` the pair `θ_h = 0, θ_1 = 1` makes the endpoint's `wrap`
inequality read `x_1 + 1 - w ≤ x_h`. -/
theorem one_le_mult_of_mem_J (hy : Mem h w (shift x θ)) {i : ℕ}
    (hi1 : 1 ≤ i) (hih : i ≤ h) (hJ : inJ h θ i) :
    1 ≤ mult h w x i := by
  obtain ⟨hzero, hone⟩ := hJ
  rcases Nat.lt_or_ge i h with hlt | hge
  · rw [succIdx_of_lt hlt] at hone
    have hstep := hy.mono i hi1 hlt
    simp only [shift, stepVal_false hzero, stepVal_true hone] at hstep
    simp only [mult, if_pos hlt]
    omega
  · have hih' : i = h := le_antisymm hih hge
    subst hih'
    rw [succIdx_self] at hone
    have hstep := hy.wrap
    simp only [shift, stepVal_false hzero, stepVal_true hone] at hstep
    simp only [mult, if_neg (Nat.lt_irrefl i)]
    omega

/-- The `ℕ`-valued multiplicity, for feeding gap 1 (whose `m : ι → ℕ`). -/
def multNat (h : ℕ) (w : ℤ) (x : ℕ → ℤ) (i : ℕ) : ℕ := (mult h w x i).toNat

/-- Gap 3 in the `ℕ`-valued form that gap 1's hypothesis `∀ i ∈ J, 1 ≤ m i` wants. -/
theorem one_le_multNat_of_mem_J (hy : Mem h w (shift x θ)) {i : ℕ}
    (hi1 : 1 ≤ i) (hih : i ≤ h) (hJ : inJ h θ i) :
    1 ≤ multNat h w x i := by
  have := one_le_mult_of_mem_J hy hi1 hih hJ
  simp only [multNat]
  omega

/-- **Gap 1 ∘ Gap 3, with the conditionality discharged.** For a step `x ↦ x + θ` whose
endpoint lies in the region, and any finset `J` of sites contained in `J(θ)`, the order of
vanishing at `t = 1` of `∏_{i ∈ J} (1 - t^{m_i(x)})` is exactly `|J|` — with **no** hypothesis
on the multiplicities, because the region condition supplies it.

This is the composite of `Polynomial.rootMultiplicity_prod_one_sub_X_pow_of_one_le`
(gap 1, `RootMultiplicityProduct.lean`) with `one_le_multNat_of_mem_J` (gap 3, above). -/
theorem rootMultiplicity_prod_mult_eq_card {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (hy : Mem h w (shift x θ)) (J : Finset ℕ)
    (hJ : ∀ i ∈ J, 1 ≤ i ∧ i ≤ h ∧ inJ h θ i) :
    rootMultiplicity (1 : R) (∏ i ∈ J, (1 - X ^ (multNat h w x i))) = J.card :=
  rootMultiplicity_prod_one_sub_X_pow_of_one_le J (multNat h w x) fun i hi => by
    obtain ⟨h1, h2, h3⟩ := hJ i hi
    exact one_le_multNat_of_mem_J hy h1 h2 h3

end TworowD4Kernel.Region
