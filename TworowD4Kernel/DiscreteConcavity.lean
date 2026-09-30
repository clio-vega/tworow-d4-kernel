/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The discrete-concavity toolkit under the `m = 2` theorem

Formalises the three small results that everything in
`proofs/2026-09-30-c1-cylindric-kostka-logconcavity.tex` stands on.  Each of them is proved
there by prose case analysis with because-clauses, which is exactly what Lean is for.

* `PFtwo` — the paper's `PF₂` (l.103): nonnegative, support an interval of `ℤ`, and
  `g s ^ 2 ≥ g (s-1) * g (s+1)`.  Stated as a three-field structure with the conjuncts kept
  separate, *not* transported through a Mathlib log-concavity predicate, so that the strength
  of each hypothesis is Lean-visible.
* `PFtwo_of_concave_on_interval_support` — Lemma `lem:conc` (l.106).
* `PFtwo_posPart` — Lemma `lem:trunc` (l.119).
* `GR_PFtwo` — the `PF₂` conclusion of Proposition `prop:regII` (l.347) for regions II and IV.

## Negative controls

A control that cannot fail is not a control.  Four live ones:

* `gapTwo_not_PFtwo` — the interval-support conjunct of `PFtwo` is **not** implied by the other
  two: `(1,0,0,1)` is nonnegative and log-concave with non-interval support.
* `gapOne_not_logConcave` — and a gap of width one already breaks log-concavity: `(1,0,1)`.
* `Gsharp_not_logConcave` — the `1`-Lipschitz hypothesis of `conj:T` (Lemma T) is load-bearing.
  This is `rem:sharp` (l.272), first bullet: the profiles `Φ = (-1,0,1)`, `Ψ = (-3,0,4)` on
  `{0,1,2}` are concave resp. convex but not `1`-Lipschitz, and the resulting `G` is not
  log-concave.  The values of `G` are *computed* here by `decide`, not copied from the paper.
* `bump_PFtwo` together with `bump_not_concave` — `lem:conc` is a strictly one-way implication:
  `(1,3,6,7,6,3,1)` is `PF₂` and is not concave.  This is why the route of `prop:regII`
  (concavity on the support) cannot be expected to extend past `m = 2`.

## Deviation from the paper proof

`prop:regII` closes with "a nondecreasing concave function composed with a concave function is
concave, so `G_R = ρ_R ∘ H` is concave on `[ℓ,h]`".  That is a real lemma, and it is not needed
here.  `GR_concave_interior` below is a termwise explicit certificate: on `ℓ < s < h` all three
of `H (s-1), H s, H (s+1)` are `≥ 1`, so the positive part is inactive on every summand, and the
summand inequality
`min (H (s-1)) k + min (H (s+1)) k ≤ 2 * min (H s) k`
is a linear-arithmetic fact about `min` of affine functions, discharged by `omega` per summand.
The factorisation the paper names is still recorded, as `GR_eq_rho_comp_H`, so nothing is lost.

## What is NOT formalised in this file

Stated here, in the section a copier reads:

* **The trapezoid formula itself.**  `prop:regII` derives
  `(1_[a,b] * 1_[c,d]) s = min (s-ℓ+1, h-s+1, n_t, m_t)_+` from the convolution of two interval
  indicators.  Convolution on `ℤ` is not defined here; `GR` is *defined* by the right-hand side.
  What is formalised is everything the paper deduces *from* that formula.  The one identity the
  derivation leans on in passing, `min(α,β)_+ = min(α_+,β_+)`, is `posPart_min`.
* **The `∓∞`-extended version of `lem:trunc`.**  The paper writes "`c` may be a concave function
  with interval domain extended by `-∞`; the same proof applies".  "The same proof applies" is a
  proposition, not a remark, and only the finite version (`PFtwo_posPart`, `c : ℤ → ℤ`) is
  formalised.  The extended version is a *separate* statement and is not proved here.
* **Lemma T** (`conj:T`) itself is a conjecture in the paper and is not formalised; only the
  sharpness witness `Gsharp` of `rem:sharp` is.
* `prop:regI` (the region I/III factorisation through `(P3)`, closure of `PF₂` under
  convolution) is not formalised; it needs convolution.  Its *concavity* input is
  `PFtwo_posPart`, which is.

## A citation in the paper whose object is undefined

`lem:trunc`'s proof says "at the two ends of the support the argument of Lemma `lem:conc` applies
verbatim".  `lem:conc` is stated for support a **bounded** interval `J = [j₀,j₁]`, and
`max (c, 0)` need not have bounded support: `posPart_support_unbounded` exhibits a concave `c`
(namely `c ≡ 1`) for which no `(j₀,j₁)` describes the support of `max (c,0)`, so `lem:conc` has
no "two ends" to offer.  The conclusion of `lem:trunc` is nevertheless true, and
`PFtwo_posPart` proves it — but it does so *without* invoking `lem:conc`, via
`IntConcave.pos_support_interval`.  The paper's citation is to a lemma that is not applicable in
the generality claimed, not to a false one.
-/

namespace TworowD4Kernel.DiscreteConcavity

/-- Discrete concavity of an integer sequence, exactly as the paper writes it in `lem:trunc`
(l.119): `2 c s ≥ c (s-1) + c (s+1)` for all `s`. -/
def IntConcave (c : ℤ → ℤ) : Prop := ∀ s, c (s - 1) + c (s + 1) ≤ 2 * c s

/-- The paper's `PF₂` (l.103): "nonnegative, support an interval of `ℤ`, and
`g(s)^2 ≥ g(s-1) g(s+1)` for all `s`".

The three conjuncts are kept as separate fields on purpose, so that each can be shown
independent of the others (see `gapTwo_not_PFtwo`) and so that the name `PFtwo` is never
load-bearing.  `logConcave` is written `g s * g s` rather than `g s ^ 2` to keep it inside
`omega`'s language; `PFtwo.logConcave_sq` is the paper's form. -/
structure PFtwo (g : ℤ → ℤ) : Prop where
  /-- `g` is nonnegative. -/
  nonneg : ∀ s, 0 ≤ g s
  /-- The support of `g` is an interval: it is closed under betweenness. -/
  suppInterval : ∀ r s t : ℤ, r ≤ s → s ≤ t → g r ≠ 0 → g t ≠ 0 → g s ≠ 0
  /-- `g` is log-concave. -/
  logConcave : ∀ s, g (s - 1) * g (s + 1) ≤ g s * g s

/-- The log-concavity field in the paper's notation. -/
theorem PFtwo.logConcave_sq {g : ℤ → ℤ} (hg : PFtwo g) (s : ℤ) :
    g (s - 1) * g (s + 1) ≤ g s ^ 2 := by
  have := hg.logConcave s; rw [sq]; exact this

/-- AM–GM over `ℤ`: this is the one-line interior step of `lem:conc`. -/
theorem mul_le_sq_of_add_le_two_mul {a b d : ℤ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (h : a + d ≤ 2 * b) : a * d ≤ b * b := by
  have hb : 0 ≤ b := by linarith
  have h1 : (a + d) * (a + d) ≤ (2 * b) * (2 * b) :=
    mul_le_mul h h (by linarith) (by linarith)
  nlinarith [sq_nonneg (a - d)]

/-! ### (1) `lem:conc`: concave + nonnegative + interval support ⟹ `PF₂` -/

/-- **Lemma `lem:conc`** (l.106 of `2026-09-30-c1-cylindric-kostka-logconcavity.tex`).
`g : ℤ → ℤ≥0` with support exactly `J = [j₀,j₁]`, satisfying `2 g s ≥ g (s-1) + g (s+1)` for
`j₀ < s < j₁` only, is `PF₂`.

The hypothesis is assumed on the *strict* interior while the conclusion is asserted for **all**
`s`; in the paper the boundary and exterior are carried by a single English sentence containing
an `or`, an `unless` and a `which forces`.  Here the case split is explicit and three-way:
`s ≤ j₀` (then `g (s-1) = 0`), `j₁ ≤ s` (then `g (s+1) = 0`), and the interior.  Note that this
trichotomy is exhaustive *including* when `J` is empty (`j₁ < j₀`), a case the paper's
enumeration of "`s = j₀`, `s = j₁`, `s ∉ J`, `j₀ < s < j₁`" does not name. -/
theorem PFtwo_of_concave_on_interval_support (g : ℤ → ℤ) (j₀ j₁ : ℤ)
    (hnn : ∀ s, 0 ≤ g s)
    (hsupp : ∀ s, g s ≠ 0 ↔ (j₀ ≤ s ∧ s ≤ j₁))
    (hconc : ∀ s, j₀ < s → s < j₁ → g (s - 1) + g (s + 1) ≤ 2 * g s) :
    PFtwo g := by
  have hzero : ∀ s : ℤ, (s < j₀ ∨ j₁ < s) → g s = 0 := by
    intro s hs
    by_contra hne
    obtain ⟨h1, h2⟩ := (hsupp s).1 hne
    omega
  refine ⟨hnn, ?_, ?_⟩
  · -- the support is an interval, by hypothesis
    intro r s t hrs hst hr ht
    obtain ⟨hr0, -⟩ := (hsupp r).1 hr
    obtain ⟨-, ht1⟩ := (hsupp t).1 ht
    exact (hsupp s).2 ⟨by omega, by omega⟩
  · intro s
    rcases le_or_gt s j₀ with hlo | hlo
    · -- `s ≤ j₀`, so `s - 1 < j₀` lies outside `J` and the left factor vanishes
      have h0 : g (s - 1) = 0 := hzero _ (Or.inl (by omega))
      rw [h0, zero_mul]
      exact mul_nonneg (hnn s) (hnn s)
    · rcases le_or_gt j₁ s with hhi | hhi
      · -- `j₁ ≤ s`, so `s + 1 > j₁` lies outside `J` and the right factor vanishes
        have h0 : g (s + 1) = 0 := hzero _ (Or.inr (by omega))
        rw [h0, mul_zero]
        exact mul_nonneg (hnn s) (hnn s)
      · -- interior: AM–GM
        exact mul_le_sq_of_add_le_two_mul (hnn _) (hnn _) (hconc s hlo hhi)

/-! ### (2) `lem:trunc`: the positive part of a concave function -/

variable {c : ℤ → ℤ}

/-- The increment `s ↦ c (s+1) - c s` of a concave integer sequence is nonincreasing.  This is
the only induction in the file. -/
theorem slope_antitone (hc : IntConcave c) {a b : ℤ} (hab : a ≤ b) :
    c (b + 1) - c b ≤ c (a + 1) - c a := by
  induction b, hab using Int.leInduction with
  | base => exact le_rfl
  | succ b _ ih =>
      have h := hc (b + 1)
      have e1 : b + 1 - 1 = b := by ring
      rw [e1] at h
      linarith

/-- Auxiliary strong induction for `IntConcave.min_le`, on the span `t - r`. -/
private theorem min_le_aux (hc : IntConcave c) :
    ∀ (n : ℕ) (r s t : ℤ), t - r ≤ (n : ℤ) → r ≤ s → s ≤ t → min (c r) (c t) ≤ c s := by
  intro n
  induction n with
  | zero =>
      intro r s t hn hrs hst
      have : r = s := by omega
      subst this
      exact min_le_left _ _
  | succ n ih =>
      intro r s t hn hrs hst
      rcases eq_or_lt_of_le hrs with h | hrs'
      · subst h; exact min_le_left _ _
      rcases eq_or_lt_of_le hst with h | hst'
      · subst h; exact min_le_right _ _
      -- `r < s < t`: shrink from the right and from the left, and compare the two slopes
      have h1 := ih r s (t - 1) (by omega) (by omega) (by omega)
      have h2 := ih (r + 1) s t (by omega) (by omega) (by omega)
      have h3 := slope_antitone hc (a := r) (b := t - 1) (by omega)
      have e : t - 1 + 1 = t := by ring
      rw [e] at h3
      omega

/-- A concave integer sequence is quasiconcave: `c s ≥ min (c r) (c t)` for `r ≤ s ≤ t`.
This is the content of `lem:trunc`'s "`{c > 0}` is an interval **because** `c` is concave" — the
clause the paper leaves ungraded. -/
theorem IntConcave.min_le (hc : IntConcave c) {r s t : ℤ} (hrs : r ≤ s) (hst : s ≤ t) :
    min (c r) (c t) ≤ c s :=
  min_le_aux hc (t - r).toNat r s t (by omega) hrs hst

/-- `{c > 0}` is an interval, for `c` concave. -/
theorem IntConcave.pos_support_interval (hc : IntConcave c) {r s t : ℤ}
    (hrs : r ≤ s) (hst : s ≤ t) (hr : 0 < c r) (ht : 0 < c t) : 0 < c s := by
  have := hc.min_le hrs hst
  omega

/-- The positive part `max (c ·) 0`. -/
def posPart (c : ℤ → ℤ) : ℤ → ℤ := fun s => max (c s) 0

@[simp] theorem posPart_apply (c : ℤ → ℤ) (s : ℤ) : posPart c s = max (c s) 0 := rfl

theorem posPart_ne_zero_iff (c : ℤ → ℤ) (s : ℤ) : posPart c s ≠ 0 ↔ 0 < c s := by
  simp only [posPart_apply]; omega

/-- **Lemma `lem:trunc`** (l.119).  The positive part of a concave integer sequence has interval
support and is `PF₂`.

Proved *directly*, not by citing `lem:conc`: see the module docstring — `lem:conc` needs a
bounded support and `posPart c` need not have one. -/
theorem PFtwo_posPart (hc : IntConcave c) : PFtwo (posPart c) := by
  refine ⟨fun s => le_max_right _ _, ?_, ?_⟩
  · intro r s t hrs hst hr ht
    rw [posPart_ne_zero_iff] at hr ht ⊢
    exact hc.pos_support_interval hrs hst hr ht
  · intro s
    by_cases h1 : 0 < c (s - 1)
    · by_cases h2 : 0 < c (s + 1)
      · have h3 : 0 < c s :=
          hc.pos_support_interval (by omega : s - 1 ≤ s) (by omega : s ≤ s + 1) h1 h2
        simp only [posPart_apply, max_eq_left h1.le, max_eq_left h2.le, max_eq_left h3.le]
        exact mul_le_sq_of_add_le_two_mul h1.le h2.le (hc s)
      · have h0 : posPart c (s + 1) = 0 := by
          rw [← posPart_ne_zero_iff c (s + 1)] at h2; omega
        rw [h0, mul_zero]
        exact mul_nonneg (le_max_right _ _) (le_max_right _ _)
    · have h0 : posPart c (s - 1) = 0 := by
        rw [← posPart_ne_zero_iff c (s - 1)] at h1; omega
      rw [h0, zero_mul]
      exact mul_nonneg (le_max_right _ _) (le_max_right _ _)

/-- `lem:trunc` cannot cite `lem:conc` in the generality it is stated: `c ≡ 1` is concave and
the support of `max (c, 0)` is all of `ℤ`, so there is no `J = [j₀,j₁]`. -/
theorem posPart_support_unbounded :
    IntConcave (fun _ : ℤ => (1 : ℤ)) ∧
      ∀ j₀ j₁ : ℤ, ¬ ∀ s : ℤ, posPart (fun _ : ℤ => (1 : ℤ)) s ≠ 0 ↔ (j₀ ≤ s ∧ s ≤ j₁) := by
  refine ⟨fun s => by norm_num, fun j₀ j₁ hj => ?_⟩
  have := (hj (j₁ + 1)).1 (by simp)
  omega

/-! ### (3) `prop:regII`: regions II and IV

The small identity the trapezoid formula leans on, then the pieces of the composition chain,
then the conclusion. -/

/-- `min(α,β)_+ = min(α_+, β_+)`, the identity used in `prop:regII` to justify the trapezoid
formula. -/
theorem posPart_min (α β : ℤ) : max (min α β) 0 = min (max α 0) (max β 0) := by omega

/-- `v ↦ min(v,k)_+` is nondecreasing. -/
theorem cap_mono (k : ℤ) {v w : ℤ} (h : v ≤ w) : max (min v k) 0 ≤ max (min w k) 0 := by omega

/-- `v ↦ min(v,k)_+` is concave on `v ≥ 1`.  Not on `v ≥ 0`: at `v = 0` the positive part bites,
which is exactly why `prop:regII` needs `H s ≥ 1` on `[ℓ,h]`. -/
theorem cap_concave (k : ℤ) {v : ℤ} (hv : 1 ≤ v) :
    max (min (v - 1) k) 0 + max (min (v + 1) k) 0 ≤ 2 * max (min v k) 0 := by omega

/-- and it vanishes at `0`. -/
theorem cap_zero (k : ℤ) : max (min (0 : ℤ) k) 0 = 0 := by omega

/-- Concavity of `v ↦ min(v,k)_+` genuinely fails at `v = 0` when `k ≥ 1`. -/
theorem cap_not_concave_at_zero :
    ¬ ∀ k v : ℤ, 0 ≤ v →
      max (min (v - 1) k) 0 + max (min (v + 1) k) 0 ≤ 2 * max (min v k) 0 := by
  intro h
  have := h 1 0 le_rfl
  omega

variable {ι : Type*}

/-- `ρ_R (v) = ∑_{t ∈ T} min(v, k t)_+`, where `k t = min (n t) (m t)`. -/
def rho (T : Finset ι) (k : ι → ℤ) (v : ℤ) : ℤ := ∑ t ∈ T, max (min v (k t)) 0

/-- `min(v, n_t, m_t)_+ = min(v, min n_t m_t)_+`, so the single cap `k = min n m` loses nothing. -/
theorem rho_eq_two_caps (T : Finset ι) (n m : ι → ℤ) (v : ℤ) :
    rho T (fun t => min (n t) (m t)) v = ∑ t ∈ T, max (min (min v (n t)) (m t)) 0 := by
  simp only [rho]
  refine Finset.sum_congr rfl fun t _ => ?_
  show max (min v (min (n t) (m t))) 0 = max (min (min v (n t)) (m t)) 0
  omega

theorem rho_zero (T : Finset ι) (k : ι → ℤ) : rho T k 0 = 0 :=
  Finset.sum_eq_zero fun t _ => cap_zero (k t)

theorem rho_mono (T : Finset ι) (k : ι → ℤ) {v w : ℤ} (h : v ≤ w) : rho T k v ≤ rho T k w :=
  Finset.sum_le_sum fun t _ => cap_mono (k t) h

theorem rho_concave (T : Finset ι) (k : ι → ℤ) {v : ℤ} (hv : 1 ≤ v) :
    rho T k (v - 1) + rho T k (v + 1) ≤ 2 * rho T k v := by
  rw [rho, rho, rho, ← Finset.sum_add_distrib, Finset.mul_sum]
  exact Finset.sum_le_sum fun t _ => cap_concave (k t) hv

/-- The common trapezoid profile `H s = min (s - ℓ + 1, h - s + 1)` of `prop:regII`. -/
def H (l h s : ℤ) : ℤ := min (s - l + 1) (h - s + 1)

theorem H_pos {l h s : ℤ} (h1 : l ≤ s) (h2 : s ≤ h) : 1 ≤ H l h s := by
  simp only [H]; omega

theorem H_nonpos {l h s : ℤ} (hs : s < l ∨ h < s) : H l h s ≤ 0 := by
  simp only [H]; omega

theorem H_concave (l h : ℤ) : IntConcave (H l h) := by
  intro s; simp only [H]; omega

/-- `G_R` as `prop:regII` computes it: a sum of trapezoids of common support `[ℓ,h]`. -/
def GR (T : Finset ι) (k : ι → ℤ) (l h : ℤ) (s : ℤ) : ℤ :=
  ∑ t ∈ T, max (min (H l h s) (k t)) 0

/-- The factorisation `G_R = ρ_R ∘ H` that `prop:regII` asserts. -/
theorem GR_eq_rho_comp_H (T : Finset ι) (k : ι → ℤ) (l h s : ℤ) :
    GR T k l h s = rho T k (H l h s) := rfl

theorem GR_nonneg (T : Finset ι) (k : ι → ℤ) (l h s : ℤ) : 0 ≤ GR T k l h s :=
  Finset.sum_nonneg fun _t _ => le_max_right _ _

/-- `G_R` vanishes off `[ℓ,h]`: every summand does. -/
theorem GR_eq_zero_of_outside (T : Finset ι) (k : ι → ℤ) {l h s : ℤ} (hs : s < l ∨ h < s) :
    GR T k l h s = 0 :=
  Finset.sum_eq_zero fun _t _ => by have := H_nonpos (l := l) (h := h) hs; omega

/-- **The explicit certificate replacing the composition lemma.**  On the interior of `[ℓ,h]`,
`G_R` is concave — proved summand by summand, because all three of `H (s-1), H s, H (s+1)` are
`≥ 1` there, so the positive part is inactive and what remains is linear arithmetic on `min`s of
affine functions.  No "nondecreasing concave ∘ concave" lemma is used. -/
theorem GR_concave_interior (T : Finset ι) (k : ι → ℤ) {l h s : ℤ} (hl : l < s) (hh : s < h) :
    GR T k l h (s - 1) + GR T k l h (s + 1) ≤ 2 * GR T k l h s := by
  rw [GR, GR, GR, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  simp only [H]
  omega

/-- **Proposition `prop:regII`** (l.347), the `PF₂` conclusion for regions II and IV.  Given one
index `t₀` whose trapezoid is nondegenerate (`k t₀ ≥ 1`), the support of `G_R` is exactly
`[ℓ,h]` and `G_R ∈ PF₂`. -/
theorem GR_PFtwo (T : Finset ι) (k : ι → ℤ) (l h : ℤ) {t₀ : ι} (ht₀ : t₀ ∈ T)
    (hk : 1 ≤ k t₀) : PFtwo (GR T k l h) := by
  have hsupp : ∀ s : ℤ, GR T k l h s ≠ 0 ↔ (l ≤ s ∧ s ≤ h) := by
    intro s
    constructor
    · intro hne
      by_contra hcon
      exact hne (GR_eq_zero_of_outside T k (by omega))
    · rintro ⟨h1, h2⟩
      have hterm : 1 ≤ max (min (H l h s) (k t₀)) 0 := by
        have := H_pos h1 h2; omega
      have hle : max (min (H l h s) (k t₀)) 0 ≤ GR T k l h s :=
        Finset.single_le_sum (f := fun t => max (min (H l h s) (k t)) 0)
          (fun i _ => le_max_right _ _) ht₀
      omega
  exact PFtwo_of_concave_on_interval_support _ l h (GR_nonneg T k l h) hsupp
    (fun s hs1 hs2 => GR_concave_interior T k hs1 hs2)

/-! ### Negative controls -/

/-- `(1,0,0,1)`. -/
def gapTwo : ℤ → ℤ := fun s => if s = 0 ∨ s = 3 then 1 else 0

/-- The interval-support conjunct of `PFtwo` is **not** implied by the other two: `gapTwo` is
nonnegative and log-concave, and its support `{0,3}` is not an interval. -/
theorem gapTwo_not_PFtwo :
    (∀ s, 0 ≤ gapTwo s) ∧ (∀ s, gapTwo (s - 1) * gapTwo (s + 1) ≤ gapTwo s * gapTwo s) ∧
      ¬ PFtwo gapTwo := by
  refine ⟨fun s => by simp only [gapTwo]; split_ifs <;> omega,
          fun s => by simp only [gapTwo]; split_ifs <;> omega, fun hg => ?_⟩
  have h1 : gapTwo 0 ≠ 0 := by simp [gapTwo]
  have h2 : gapTwo 3 ≠ 0 := by simp [gapTwo]
  have := hg.suppInterval 0 1 3 (by omega) (by omega) h1 h2
  simp [gapTwo] at this

/-- `(1,0,1)`: a gap of width one already breaks log-concavity, at the gap. -/
def gapOne : ℤ → ℤ := fun s => if s = 0 ∨ s = 2 then 1 else 0

theorem gapOne_not_logConcave :
    ¬ ∀ s : ℤ, gapOne (s - 1) * gapOne (s + 1) ≤ gapOne s * gapOne s := by
  intro h
  have := h 1
  simp [gapOne] at this

/-! #### `rem:sharp`: the `1`-Lipschitz hypothesis of Lemma T is load-bearing

`Φ = (-1,0,1)` is concave and `Ψ = (-3,0,4)` is convex on `{0,1,2}`, but `Ψ` is not
`1`-Lipschitz.  `G s = ∑_{i+j=s} (Φ i - Ψ j + 1)_+` is then not log-concave.  The values of `G`
are computed by the kernel below, not asserted. -/

/-- `Φ = (-1,0,1)` on `{0,1,2}`. -/
def Phi : ℤ → ℤ := fun i => if i = 0 then -1 else if i = 1 then 0 else 1

/-- `Ψ = (-3,0,4)` on `{0,1,2}`. -/
def Psi : ℤ → ℤ := fun j => if j = 0 then -3 else if j = 1 then 0 else 4

theorem Phi_concave_on : ∀ i : ℤ, i = 1 → Phi (i - 1) + Phi (i + 1) ≤ 2 * Phi i := by
  intro i hi; subst hi; norm_num [Phi]

theorem Psi_convex_on : ∀ j : ℤ, j = 1 → 2 * Psi j ≤ Psi (j - 1) + Psi (j + 1) := by
  intro j hj; subst hj; norm_num [Psi]

/-- `Ψ` is not `1`-Lipschitz: the step from `1` to `2` is `4`. -/
theorem Psi_not_one_lipschitz : ¬ ∀ j : ℤ, |Psi (j + 1) - Psi j| ≤ 1 := by
  intro h
  have := h 1
  norm_num [Psi] at this

/-- `G s = ∑_{i+j=s} (Φ i - Ψ j + 1)_+`, both indices ranging over `{0,1,2}`. -/
def Gsharp (s : ℤ) : ℤ :=
  ∑ i ∈ ({0, 1, 2} : Finset ℤ),
    if 0 ≤ s - i ∧ s - i ≤ 2 then max (Phi i - Psi (s - i) + 1) 0 else 0

/-- `Φ` *is* `1`-Lipschitz, so the failure below is attributable to `Ψ` alone. -/
theorem Phi_one_lipschitz : ∀ i : ℤ, 0 ≤ i → i ≤ 1 → |Phi (i + 1) - Phi i| ≤ 1 := by
  intro i h1 h2
  interval_cases i <;> norm_num [Phi]

/-- The values of `G`, computed by the kernel. -/
theorem Gsharp_values : Gsharp 0 = 3 ∧ Gsharp 1 = 4 ∧ Gsharp 2 = 6 ∧ Gsharp 3 = 2 ∧
    Gsharp 4 = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [Gsharp, Phi, Psi]

/-- The failing instance, printed: `4 * 4 = 16 < 18 = 3 * 6`. -/
theorem Gsharp_failure : Gsharp 1 * Gsharp 1 < Gsharp 0 * Gsharp 2 := by
  norm_num [Gsharp, Phi, Psi]

/-- The `rem:sharp` witness, first bullet: `G` is not log-concave at `s = 1`. -/
theorem Gsharp_not_logConcave :
    ¬ ∀ s : ℤ, Gsharp (s - 1) * Gsharp (s + 1) ≤ Gsharp s * Gsharp s := by
  intro h
  have := h 1
  norm_num [Gsharp, Phi, Psi] at this

/-! #### `lem:conc` is one-way: `PF₂` does not imply concavity -/

/-- `(1,3,6,7,6,3,1)`. -/
def bump : ℤ → ℤ := fun s =>
  if s = 0 ∨ s = 6 then 1 else
  if s = 1 ∨ s = 5 then 3 else
  if s = 2 ∨ s = 4 then 6 else
  if s = 3 then 7 else 0

theorem bump_PFtwo : PFtwo bump := by
  refine ⟨fun s => ?_, fun r s t hrs hst hr ht => ?_, fun s => ?_⟩
  · simp only [bump]; split_ifs <;> omega
  · simp only [bump] at hr ht ⊢; split_ifs at hr ht ⊢ <;> omega
  · simp only [bump]; split_ifs <;> omega

/-- The failing concavity instance, printed: `2 * 3 = 6 < 7 = 1 + 6`. -/
theorem bump_concavity_failure : 2 * bump 1 < bump 0 + bump 2 := by norm_num [bump]

/-- `bump` is `PF₂` but not concave, so `lem:conc` is a strictly one-way implication. -/
theorem bump_not_concave : ¬ IntConcave bump := by
  intro h
  have := h 1
  norm_num [bump] at this

end TworowD4Kernel.DiscreteConcavity

/-! ### Axiom audit -/

section Audit

#print axioms TworowD4Kernel.DiscreteConcavity.PFtwo_of_concave_on_interval_support
#print axioms TworowD4Kernel.DiscreteConcavity.PFtwo_posPart
#print axioms TworowD4Kernel.DiscreteConcavity.IntConcave.min_le
#print axioms TworowD4Kernel.DiscreteConcavity.IntConcave.pos_support_interval
#print axioms TworowD4Kernel.DiscreteConcavity.slope_antitone
#print axioms TworowD4Kernel.DiscreteConcavity.posPart_support_unbounded
#print axioms TworowD4Kernel.DiscreteConcavity.posPart_min
#print axioms TworowD4Kernel.DiscreteConcavity.rho_zero
#print axioms TworowD4Kernel.DiscreteConcavity.rho_mono
#print axioms TworowD4Kernel.DiscreteConcavity.rho_concave
#print axioms TworowD4Kernel.DiscreteConcavity.rho_eq_two_caps
#print axioms TworowD4Kernel.DiscreteConcavity.H_concave
#print axioms TworowD4Kernel.DiscreteConcavity.GR_eq_rho_comp_H
#print axioms TworowD4Kernel.DiscreteConcavity.GR_concave_interior
#print axioms TworowD4Kernel.DiscreteConcavity.GR_PFtwo
#print axioms TworowD4Kernel.DiscreteConcavity.gapTwo_not_PFtwo
#print axioms TworowD4Kernel.DiscreteConcavity.gapOne_not_logConcave
#print axioms TworowD4Kernel.DiscreteConcavity.Psi_not_one_lipschitz
#print axioms TworowD4Kernel.DiscreteConcavity.Gsharp_not_logConcave
#print axioms TworowD4Kernel.DiscreteConcavity.bump_PFtwo
#print axioms TworowD4Kernel.DiscreteConcavity.bump_not_concave
#print axioms TworowD4Kernel.DiscreteConcavity.cap_not_concave_at_zero
#print axioms TworowD4Kernel.DiscreteConcavity.Gsharp_values
#print axioms TworowD4Kernel.DiscreteConcavity.Gsharp_failure
#print axioms TworowD4Kernel.DiscreteConcavity.Phi_one_lipschitz
#print axioms TworowD4Kernel.DiscreteConcavity.bump_concavity_failure

end Audit
