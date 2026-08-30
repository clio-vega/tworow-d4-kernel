/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.HookKummerLemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Lemma F — the factor-in-product principle (uniform boundary engine, `d = 4`)

This file formalises **Lemma F**, the one elementary 2-adic fact that drives every closed boundary
case of the three-row tie families for `c = 1` and `c = 2` (and the `c = 3` top), as stated in §1.3
of `~/projects/proofs/2026-06-15-boundary-lemma-threerow.md`.

Informally:

> Among the `Q ≥ 4` consecutive integers `R+1, …, R+Q`, any single distinguished factor `R+t₀`
> (`1 ≤ t₀ ≤ Q`) satisfies `v₂(∏_{t=1}^{Q} (R+t)) − v₂(R+t₀) ≥ 1`.

The mechanism: `R + t₀` is one factor of the product, so the product's valuation is at least
`v₂(R+t₀)` plus the valuation of *the rest*; and among `≥ 4` consecutive integers there are at
least **two** even ones, so the rest still contains an even factor and contributes `v₂ ≥ 1`.

A two-factor strengthening — **Lemma F2** — is the keystone of the harder `c = 3` `a`-odd top, where
two deficits must be absorbed. The honest hypothesis is `Q ≥ 6` (sharp), giving surplus `≥ 1`:

> Among the `Q ≥ 6` consecutive integers `R+1, …, R+Q`, any two distinct distinguished factors
> `R+t₁, R+t₂` satisfy `v₂(∏) − v₂(R+t₁) − v₂(R+t₂) ≥ 1`.

(The `Q ≥ 5`, surplus `≥ 0` form stated in the LEAN brief is *true but vacuous*: dropping two
factors of a product never decreases its valuation below the sum of the two factors' valuations,
for any `Q ≥ 2`. The content — that an even factor *survives* the two deletions — needs `Q ≥ 6`,
which is sharp: at `Q = 5` with `R` even the only two even factors can both be deleted.)

## Main results

* `TworowD4Kernel.lemma_F` — the factor-in-product principle: `Q ≥ 4`, single deleted factor,
  surplus `≥ 1`.
* `TworowD4Kernel.lemma_F2` — the two-factor strengthening: `Q ≥ 6`, two distinct deleted factors,
  surplus `≥ 1`.

## References

`2026-06-15-boundary-lemma-threerow.md`, §1.3; `2026-06-16-c3-boundary-complete.md` (Lemma F2,
`Q ≥ 6` sharp).
-/

namespace TworowD4Kernel

open Nat Finset

/-- **Lemma F (factor-in-product principle).** For `Q ≥ 4` and any distinguished index
`t₀ ∈ [1, Q]`, the product of the `Q` consecutive integers `R+1, …, R+Q` carries a spare factor of
`2` beyond its single factor `R + t₀`:
`v₂(R + t₀) + 1 ≤ v₂(∏_{t=1}^{Q} (R + t))`.

*Proof.* Split off the distinguished factor: `∏ = (R+t₀) · rest`, where `rest` runs over the erased
index set. Among `R+1, …, R+4` (the first four, present since `Q ≥ 4`) two are even, so the erased
set still contains an index `t₁ ≠ t₀` with `R + t₁` even. Hence `2 ∣ rest`, i.e. `v₂(rest) ≥ 1`, and
`v₂(∏) = v₂(R+t₀) + v₂(rest) ≥ v₂(R+t₀) + 1`. -/
theorem lemma_F {R Q t₀ : ℕ} (hQ : 4 ≤ Q) (ht₀ : t₀ ∈ Finset.Icc 1 Q) :
    padicValNat 2 (R + t₀) + 1 ≤ padicValNat 2 (∏ t ∈ Finset.Icc 1 Q, (R + t)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht₀1, ht₀Q⟩ := Finset.mem_Icc.mp ht₀
  -- split the product into the distinguished factor and the rest
  have hsplit : (∏ t ∈ Finset.Icc 1 Q, (R + t))
      = (R + t₀) * ∏ t ∈ (Finset.Icc 1 Q).erase t₀, (R + t) :=
    (Finset.mul_prod_erase (Finset.Icc 1 Q) (fun t => R + t) ht₀).symm
  -- among the first four indices there are two even factors; one differs from `t₀`
  obtain ⟨t₁, ht₁mem, ht₁ne, ht₁even⟩ :
      ∃ t₁, t₁ ∈ Finset.Icc 1 Q ∧ t₁ ≠ t₀ ∧ 2 ∣ (R + t₁) := by
    rcases Nat.even_or_odd R with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- `R` even: `R+2` and `R+4` are even
      rcases eq_or_ne t₀ 2 with h | h
      · exact ⟨4, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ⟨k + 2, by omega⟩⟩
      · exact ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ⟨k + 1, by omega⟩⟩
    · -- `R` odd: `R+1` and `R+3` are even
      rcases eq_or_ne t₀ 1 with h | h
      · exact ⟨3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ⟨k + 2, by omega⟩⟩
      · exact ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega, ⟨k + 1, by omega⟩⟩
  -- the rest is divisible by `2`
  have hrest_mem : t₁ ∈ (Finset.Icc 1 Q).erase t₀ := Finset.mem_erase.mpr ⟨ht₁ne, ht₁mem⟩
  have h2dvd : 2 ∣ ∏ t ∈ (Finset.Icc 1 Q).erase t₀, (R + t) :=
    dvd_trans ht₁even (Finset.dvd_prod_of_mem (fun t => R + t) hrest_mem)
  have hrest_ne : (∏ t ∈ (Finset.Icc 1 Q).erase t₀, (R + t)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    have h1 : 1 ≤ t := (Finset.mem_Icc.mp (Finset.mem_of_mem_erase ht)).1
    omega
  have hfac_ne : R + t₀ ≠ 0 := by omega
  have hge1 : 1 ≤ padicValNat 2 (∏ t ∈ (Finset.Icc 1 Q).erase t₀, (R + t)) :=
    (padicValNat_dvd_iff_le hrest_ne).mp (by rw [pow_one]; exact h2dvd)
  calc padicValNat 2 (R + t₀) + 1
      ≤ padicValNat 2 (R + t₀)
        + padicValNat 2 (∏ t ∈ (Finset.Icc 1 Q).erase t₀, (R + t)) := by omega
    _ = padicValNat 2 (∏ t ∈ Finset.Icc 1 Q, (R + t)) := by
        rw [hsplit, padicValNat.mul hfac_ne hrest_ne]

/-- **Lemma F2 (two-factor strengthening).** For `Q ≥ 6` and any two *distinct* distinguished
indices `t₁, t₂ ∈ [1, Q]`, the product of the `Q` consecutive integers `R+1, …, R+Q` still carries
a spare factor of `2` beyond its two factors `R + t₁` and `R + t₂`:
`v₂(R + t₁) + v₂(R + t₂) + 1 ≤ v₂(∏_{t=1}^{Q} (R + t))`.

*Proof.* Split off both distinguished factors: `∏ = (R+t₁) · (R+t₂) · rest`, where `rest` runs over
the doubly-erased index set. Among `R+1, …, R+6` (present since `Q ≥ 6`) there are **three** even
integers, so at least one — at an index `t₃ ∉ {t₁, t₂}` — survives both deletions; hence `2 ∣ rest`,
i.e. `v₂(rest) ≥ 1`.

The hypothesis `Q ≥ 6` is sharp: at `Q = 5` with `R` even the only two even factors are `R+2, R+4`,
and deleting both leaves an odd product (surplus `0`). -/
theorem lemma_F2 {R Q t₁ t₂ : ℕ} (hQ : 6 ≤ Q) (ht₁ : t₁ ∈ Finset.Icc 1 Q)
    (ht₂ : t₂ ∈ Finset.Icc 1 Q) (hne : t₁ ≠ t₂) :
    padicValNat 2 (R + t₁) + padicValNat 2 (R + t₂) + 1
      ≤ padicValNat 2 (∏ t ∈ Finset.Icc 1 Q, (R + t)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ht₁1, ht₁Q⟩ := Finset.mem_Icc.mp ht₁
  obtain ⟨ht₂1, ht₂Q⟩ := Finset.mem_Icc.mp ht₂
  -- split off both distinguished factors
  have ht₂mem' : t₂ ∈ (Finset.Icc 1 Q).erase t₁ := Finset.mem_erase.mpr ⟨hne.symm, ht₂⟩
  have hsplit1 : (∏ t ∈ Finset.Icc 1 Q, (R + t))
      = (R + t₁) * ∏ t ∈ (Finset.Icc 1 Q).erase t₁, (R + t) :=
    (Finset.mul_prod_erase (Finset.Icc 1 Q) (fun t => R + t) ht₁).symm
  have hsplit2 : (∏ t ∈ (Finset.Icc 1 Q).erase t₁, (R + t))
      = (R + t₂) * ∏ t ∈ ((Finset.Icc 1 Q).erase t₁).erase t₂, (R + t) :=
    (Finset.mul_prod_erase ((Finset.Icc 1 Q).erase t₁) (fun t => R + t) ht₂mem').symm
  -- among the first six indices there are three even factors; one avoids `t₁` and `t₂`
  obtain ⟨t₃, ht₃mem, ht₃1, ht₃2, ht₃even⟩ :
      ∃ t₃, t₃ ∈ Finset.Icc 1 Q ∧ t₃ ≠ t₁ ∧ t₃ ≠ t₂ ∧ 2 ∣ (R + t₃) := by
    rcases Nat.even_or_odd R with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- `R` even: `R+2, R+4, R+6` are even
      rcases (show (2 ≠ t₁ ∧ 2 ≠ t₂) ∨ (4 ≠ t₁ ∧ 4 ≠ t₂) ∨ (6 ≠ t₁ ∧ 6 ≠ t₂) by omega)
        with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨2, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, a, b, ⟨k + 1, by omega⟩⟩
      · exact ⟨4, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, a, b, ⟨k + 2, by omega⟩⟩
      · exact ⟨6, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, a, b, ⟨k + 3, by omega⟩⟩
    · -- `R` odd: `R+1, R+3, R+5` are even
      rcases (show (1 ≠ t₁ ∧ 1 ≠ t₂) ∨ (3 ≠ t₁ ∧ 3 ≠ t₂) ∨ (5 ≠ t₁ ∧ 5 ≠ t₂) by omega)
        with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨1, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, a, b, ⟨k + 1, by omega⟩⟩
      · exact ⟨3, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, a, b, ⟨k + 2, by omega⟩⟩
      · exact ⟨5, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, a, b, ⟨k + 3, by omega⟩⟩
  -- the doubly-erased rest is divisible by `2`
  have ht₃mem2 : t₃ ∈ ((Finset.Icc 1 Q).erase t₁).erase t₂ :=
    Finset.mem_erase.mpr ⟨ht₃2, Finset.mem_erase.mpr ⟨ht₃1, ht₃mem⟩⟩
  have h2dvd : 2 ∣ ∏ t ∈ ((Finset.Icc 1 Q).erase t₁).erase t₂, (R + t) :=
    dvd_trans ht₃even (Finset.dvd_prod_of_mem (fun t => R + t) ht₃mem2)
  have hrest_ne : (∏ t ∈ ((Finset.Icc 1 Q).erase t₁).erase t₂, (R + t)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    have h1 : 1 ≤ t :=
      (Finset.mem_Icc.mp (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))).1
    omega
  have hf1 : R + t₁ ≠ 0 := by omega
  have hf2 : R + t₂ ≠ 0 := by omega
  have hge1 : 1 ≤ padicValNat 2 (∏ t ∈ ((Finset.Icc 1 Q).erase t₁).erase t₂, (R + t)) :=
    (padicValNat_dvd_iff_le hrest_ne).mp (by rw [pow_one]; exact h2dvd)
  have hval : padicValNat 2 (∏ t ∈ Finset.Icc 1 Q, (R + t))
      = padicValNat 2 (R + t₁) + padicValNat 2 (R + t₂)
        + padicValNat 2 (∏ t ∈ ((Finset.Icc 1 Q).erase t₁).erase t₂, (R + t)) := by
    rw [hsplit1, hsplit2, padicValNat.mul hf1 (mul_ne_zero hf2 hrest_ne),
      padicValNat.mul hf2 hrest_ne, Nat.add_assoc]
  omega

end TworowD4Kernel
