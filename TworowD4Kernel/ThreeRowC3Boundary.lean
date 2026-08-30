/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ThreeRowC2Boundary
import TworowD4Kernel.LemmaF
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The three-row `c = 3` boundary lemma, end-to-end (`d = 4`)

This file assembles the **boundary lemma** for the three-row tie family `λ = (a, b, 3)` into a
single `sorry`-free declaration, closing the last residual of the `c = 3` interior theorem
(`~/projects/proofs/2026-06-14-threerow-c3-Jstar-even.md`,
`~/projects/proofs/2026-06-15-compensation-lemma-B-proved.md`) via
`~/projects/proofs/2026-06-16-c3-boundary-complete.md` (`c = 3`, COMPLETE). It joins the already
machine-checked `c = 1` (`ThreeRowC1Boundary`) and `c = 2` (`ThreeRowC2Boundary`) families.

## What is proved here, and what is assumed

For `λ = (a, b, 3) ⊢ 2m` (so `a + b = 2m − 3`, hence `a, b` opposite parity) the graded valuations
are `val(j) = j + 2 v₂(G_j)`, `G_j = ⟨s_λ, e₂^j h₁^{2(m−j)}⟩ = C(m,j) M_j`. The interior theorem
pins the minimiser set `J*` to the interior 2-adic box `j₀ + {0,2,4,6}` (`j₀ ∈ {0,3}`) and leaves
**one** residual: that none of the three boundary indices `j ∈ {b+1, b+2, b+3}` is an extra
minimiser, i.e. `val(b+i) > V` for `i = 1, 2, 3`, where the threshold is `V = val(0) − θ`,
`θ ∈ {0, 3}` (`θ = 0` when `a` is even, `θ = 3` when `a` is odd — the forced descent
`val(3) = val(0) − 3`).

We work in the box-interior / Lemma-D regime `a = 2P + b + 3` with `P ≥ 0` (so `a ≥ b + 3`); this is
exactly the regime in which the `Δ` closed forms are derived and Murnaghan–Nakayama-verified (the
finitely many smaller-`b` shapes are the per-family boundary-tie casework of the interior note). The
box-interior thresholds `b ≥ 7` (`a` even, so `b` odd) and `b ≥ 10` (`a` odd, so `b` even) keep the
2-adic box inside `[0, b]`.

Writing `Δ(b+i) := val(b+i) − val(0)` and `s₂ n = (Nat.digits 2 n).sum`, the expanded Lemma D closed
forms (each Murnaghan–Nakayama-verified over the box-interior range `m ≤ 30`, `0` mismatch) are

> `Δ(b+3) = (b+5) + 2 s₂(P) − 2 s₂(a+2) − 2 v₂(a−1) − 2 v₂(P+2)`,
> `Δ(b+2) = (b+2) + 2 s₂(P+1) − 2 s₂(a+2) + 2 v₂(N₂) − 2 v₂(a−1) − 2 v₂(P+2)`,
> `Δ(b+1) = (b−1) + 2 s₂(P+2) − 2 s₂(a+2) + 2 v₂(N₁) − 2 v₂(a−1)`,

where `N₂ = a(b+3) − (b²+2b+3)` and `N₁ = ab² + 5ab + 6a − (b³+b²+4b+6)` are the polynomial factors
of `M_{b+2}, M_{b+1}`. These rest on the Murnaghan–Nakayama closed forms for `M_0` (hook), `M_{b+3}`
(Lemma T) and `M_{b+1}, M_{b+2}` — symmetric-function facts out of Mathlib's reach. Consistent with
every prior session, they are therefore taken as the **hypotheses** `hΔ3, hΔ2, hΔ1`, together with
the definitions of `N₁, N₂`. Everything downstream — the genuine 2-adic number theory, including the
*evenness* of `N₁, N₂` derived from their definitions — is proved here from scratch.

## The number-theoretic content (proved, not assumed)

The keystone is the two-factor engine `TworowD4Kernel.lemma_F2` (`Q ≥ 6`, two distinct deleted
factors, surplus `≥ 1`), which dissolves the two simultaneous deficits `v₂(a−1), v₂(a−b+1)` of the
`a`-odd cases; the `a`-even cases use the single-factor `TworowD4Kernel.lemma_F` and divisibility.
Both rest on the bridge `TworowD4Kernel.vz_prod_Icc`.

* `TworowD4Kernel.threerow_c3_boundary_top_aeven` / `_aodd` — the top index `j = b+3`.
* `TworowD4Kernel.threerow_c3_boundary_sub2_aeven` / `_aodd` — the subtop index `j = b+2`.
* `TworowD4Kernel.threerow_c3_boundary_sub1_aeven` / `_aodd` — the subtop index `j = b+1`.
* `TworowD4Kernel.threerow_c3_boundary` — the assembled end-to-end statement: `V < valb1`,
  `V < valb2`, `V < valb3`.

## References

`2026-06-16-c3-boundary-complete.md` (`c = 3`, COMPLETE); the `c = 1, 2` companions
`TworowD4Kernel.threerow_c1_boundary`, `TworowD4Kernel.threerow_c2_boundary`; the factor-in-product
engines `TworowD4Kernel.lemma_F`, `TworowD4Kernel.lemma_F2`.
-/

namespace TworowD4Kernel

open Nat Finset

/-- `v₂(N₂) ≥ 1`: from `N₂ = a(b+3) − (b²+2b+3)` and `a = 2P+b+3` one has the exact even
decomposition `N₂ = 2·(Pb + 3P + 2b + 3)`, so `N₂` is even (and positive). -/
theorem vz_N2_ge_one {a b P N₂ : ℕ} (hP : a = 2 * P + b + 3)
    (hN2 : N₂ = a * (b + 3) - (b * b + 2 * b + 3)) : 1 ≤ vz N₂ := by
  have key : a * (b + 3) = 2 * (P * b + 3 * P + 2 * b + 3) + (b * b + 2 * b + 3) := by
    rw [hP]; ring
  have hN2eq : N₂ = 2 * (P * b + 3 * P + 2 * b + 3) := by rw [hN2, key, Nat.add_sub_cancel]
  have hne : P * b + 3 * P + 2 * b + 3 ≠ 0 := by positivity
  have hvN2 : vz N₂ = 1 + vz (P * b + 3 * P + 2 * b + 3) := by
    rw [hN2eq, vz_mul (by norm_num) hne, vz]
    norm_num [padicValNat.self (show 1 < 2 by norm_num)]
  have hnn : 0 ≤ vz (P * b + 3 * P + 2 * b + 3) := by simp only [vz]; exact Int.natCast_nonneg _
  omega

/-- **`c = 3` boundary, top index `j = b+3`, `a` even.** Box-interior regime `a = 2P+b+3`, `b ≥ 7`
(so `b` is odd). The MN-verified closed form forces `Δ(b+3) ≥ 2`, hence `val(b+3) > val(0) = V`.

*Proof (§3 top).* `a` even ⟹ `a−1` odd ⟹ `v₂(a−1) = 0`. With `b = 2β+1`, set `Q := β+3 ≥ 4`; then
`a = 2(P+β+2)`, `a+2 = 2(P+β+3)`, and the bridge collapses `Δ(b+3) = 2[v₂(∏_{t=1}^{Q}(P+t)) −
v₂(P+2)]`, where `P+2` is the `t = 2` factor, so `lemma_F` gives `Δ ≥ 2`. -/
theorem threerow_c3_boundary_top_aeven {a b P : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 3) (ha : Even a)
    (hb : 7 ≤ b)
    (hΔ : Δ = (b : ℤ) + 5 + 2 * ((Nat.digits 2 P).sum : ℤ) - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ)
      - 2 * vz (a - 1) - 2 * vz (P + 2)) :
    2 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ka, hka⟩ := ha
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · omega   -- `b` even contradicts `a` even via `a = 2P+b+3`
  · -- `b = 2β + 1`, `β ≥ 3`.
    have hb2 : b = 2 * β + 1 := by omega
    have hβ3 : 3 ≤ β := by omega
    have haeq : a = 2 * (P + β + 2) := by omega
    have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
      rw [ha2eq, sum_digits_two_mul]
    have hva1 : vz (a - 1) = 0 := by
      have hodd : ¬ (2 ∣ (a - 1)) := by omega
      simp [vz, padicValNat.eq_zero_of_not_dvd hodd]
    -- bridge at `Q = β + 3`, and `lemma_F` deleting the `t = 2` factor `P + 2`.
    have hbridge := vz_prod_Icc P (β + 3)
    rw [show P + (β + 3) = P + β + 3 by omega] at hbridge
    have hmem : (2 : ℕ) ∈ Finset.Icc 1 (β + 3) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hF := lemma_F (R := P) (Q := β + 3) (t₀ := 2) (by omega) hmem
    have hFz : vz (P + 2) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 3), (P + t)) := by
      simp only [vz]; exact_mod_cast hF
    have hb2z : (b : ℤ) = 2 * (β : ℤ) + 1 := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva1]
    push_cast
    linarith

/-- **`c = 3` boundary, top index `j = b+3`, `a` odd.** Box-interior regime `a = 2P+b+3`, `b ≥ 10`
(so `b` is even). The MN-verified closed form forces `Δ(b+3) ≥ −1`, hence
`val(b+3) > val(0) − 3 = V`.

*Proof (§4 top).* `b = 2β`, `β ≥ 5`. Here `a−1 = 2(P+β+1)` and `a−b+1 = 2(P+2)` give two deficits
`v₂(a−1) = 1 + v₂(P+β+1)` and `v₂(P+2)`. Set `Q := β+2 ≥ 6`; the bridge collapses `Δ(b+3) =
2[v₂(∏_{t=1}^{Q}(P+t)) − v₂(P+β+1) − v₂(P+2)] − 3`. The two distinct factors `P+2` (`t = 2`) and
`P+β+1` (`t = β+1`) are dissolved by `lemma_F2`, giving `Δ ≥ 2·1 − 3 = −1`. -/
theorem threerow_c3_boundary_top_aodd {a b P : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 3) (ha : Odd a)
    (hb : 10 ≤ b)
    (hΔ : Δ = (b : ℤ) + 5 + 2 * ((Nat.digits 2 P).sum : ℤ) - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ)
      - 2 * vz (a - 1) - 2 * vz (P + 2)) :
    -1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ka, hka⟩ := ha
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · -- `b = 2β`, `β ≥ 5`.
    have hb2 : b = 2 * β := by omega
    have hβ5 : 5 ≤ β := by omega
    have ha1eq : a - 1 = 2 * (P + β + 1) := by omega
    have ha2eq : a + 2 = 2 * (P + β + 2) + 1 := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 2)).sum + 1 := by
      rw [ha2eq, sum_digits_two_mul_add_one]
    have hva1 : vz (a - 1) = 1 + vz (P + β + 1) := by
      rw [ha1eq, vz_mul (by norm_num) (by omega), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    -- bridge at `Q = β + 2`, and `lemma_F2` deleting `t = 2` (`P+2`) and `t = β+1` (`P+β+1`).
    have hbridge := vz_prod_Icc P (β + 2)
    rw [show P + (β + 2) = P + β + 2 by omega] at hbridge
    have hm1 : (2 : ℕ) ∈ Finset.Icc 1 (β + 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hm2 : (β + 1) ∈ Finset.Icc 1 (β + 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hF := lemma_F2 (R := P) (Q := β + 2) (t₁ := 2) (t₂ := β + 1) (by omega) hm1 hm2 (by omega)
    have hFz : vz (P + 2) + vz (P + β + 1) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 2), (P + t)) := by
      rw [show P + β + 1 = P + (β + 1) by omega]
      simp only [vz]; exact_mod_cast hF
    have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva1]
    push_cast
    linarith
  · omega   -- `b` odd contradicts `a` odd via `a = 2P+b+3`

/-- **`c = 3` boundary, subtop index `j = b+2`, `a` even.** Box-interior regime, `b ≥ 7`. The
MN-verified closed form forces `Δ(b+2) ≥ 1`, hence `val(b+2) > val(0) = V`.

*Proof (§3 subtop).* `v₂(a−1) = 0` and `v₂(N₂) ≥ 1`. With `b = 2β+1`, set `Q := β+2`; the bridge
collapses `Δ(b+2) = 2[v₂(∏_{t=1}^{Q}(P+1+t)) − v₂(P+2)] + 2 v₂(N₂) − 1`, and `P+2` is the `t = 1`
factor of the product, so the bracket is `≥ 0` (divisibility) and `Δ ≥ 2·0 + 2·1 − 1 = 1`. -/
theorem threerow_c3_boundary_sub2_aeven {a b P N₂ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 3)
    (ha : Even a) (hb : 7 ≤ b) (hN2 : N₂ = a * (b + 3) - (b * b + 2 * b + 3))
    (hΔ : Δ = (b : ℤ) + 2 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₂ - 2 * vz (a - 1) - 2 * vz (P + 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvN2 := vz_N2_ge_one hP hN2
  obtain ⟨ka, hka⟩ := ha
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · omega
  · have hb2 : b = 2 * β + 1 := by omega
    have hβ3 : 3 ≤ β := by omega
    have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
      rw [ha2eq, sum_digits_two_mul]
    have hva1 : vz (a - 1) = 0 := by
      have hodd : ¬ (2 ∣ (a - 1)) := by omega
      simp [vz, padicValNat.eq_zero_of_not_dvd hodd]
    -- bridge at `Q = β + 1`, `R = P + 1`; `P + 2` is the `t = 1` factor of the product.
    have hbridge := vz_prod_Icc (P + 1) (β + 2)
    rw [show (P + 1) + (β + 2) = P + β + 3 by omega] at hbridge
    have hprodne : (∏ t ∈ Finset.Icc 1 (β + 2), ((P + 1) + t)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro t ht; omega
    have hdvd : ((P + 1) + 1) ∣ ∏ t ∈ Finset.Icc 1 (β + 2), ((P + 1) + t) :=
      Finset.dvd_prod_of_mem (fun t => (P + 1) + t) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hdvdle := vz_dvd_le hprodne hdvd
    rw [show (P + 1) + 1 = P + 2 by omega] at hdvdle
    have hb2z : (b : ℤ) = 2 * (β : ℤ) + 1 := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva1]
    push_cast
    linarith

/-- **`c = 3` boundary, subtop index `j = b+2`, `a` odd.** Box-interior regime, `b ≥ 10`. The
MN-verified closed form forces `Δ(b+2) ≥ 0`, hence `val(b+2) > val(0) − 3 = V`.

*Proof (§4 subtop).* `b = 2β`, `β ≥ 5`, `v₂(a−1) = 1 + v₂(P+β+1)`, `v₂(N₂) ≥ 1`. Set `Q := β+1 ≥ 6`,
`R := P+1`; the bridge collapses `Δ(b+2) = 2[v₂(∏) − 1 + v₂(N₂) − v₂(a−1) − v₂(P+2)]`. The two
distinct factors `P+2` (`t = 1`) and `P+β+1` (`t = β`) are dissolved by `lemma_F2`, giving
`Δ ≥ 2[1 − 2 + v₂(N₂)] = 2(v₂(N₂) − 1) ≥ 0`. -/
theorem threerow_c3_boundary_sub2_aodd {a b P N₂ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 3)
    (ha : Odd a) (hb : 10 ≤ b) (hN2 : N₂ = a * (b + 3) - (b * b + 2 * b + 3))
    (hΔ : Δ = (b : ℤ) + 2 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₂ - 2 * vz (a - 1) - 2 * vz (P + 2)) :
    0 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvN2 := vz_N2_ge_one hP hN2
  obtain ⟨ka, hka⟩ := ha
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · have hb2 : b = 2 * β := by omega
    have hβ5 : 5 ≤ β := by omega
    have ha1eq : a - 1 = 2 * (P + β + 1) := by omega
    have ha2eq : a + 2 = 2 * (P + β + 2) + 1 := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 2)).sum + 1 := by
      rw [ha2eq, sum_digits_two_mul_add_one]
    have hva1 : vz (a - 1) = 1 + vz (P + β + 1) := by
      rw [ha1eq, vz_mul (by norm_num) (by omega), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    -- bridge at `Q = β + 1`, `R = P + 1`; `lemma_F2` on `t = 1` (`P+2`), `t = β` (`P+β+1`).
    have hbridge := vz_prod_Icc (P + 1) (β + 1)
    rw [show (P + 1) + (β + 1) = P + β + 2 by omega] at hbridge
    have hm1 : (1 : ℕ) ∈ Finset.Icc 1 (β + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hm2 : β ∈ Finset.Icc 1 (β + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hF := lemma_F2 (R := P + 1) (Q := β + 1) (t₁ := 1) (t₂ := β) (by omega) hm1 hm2 (by omega)
    have hFz : vz (P + 2) + vz (P + β + 1) + 1
        ≤ vz (∏ t ∈ Finset.Icc 1 (β + 1), ((P + 1) + t)) := by
      rw [show P + 2 = (P + 1) + 1 by omega, show P + β + 1 = (P + 1) + β by omega]
      simp only [vz]; exact_mod_cast hF
    have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva1]
    push_cast
    linarith
  · omega

/-- **`c = 3` boundary, subtop index `j = b+1`, `a` even.** Box-interior regime, `b ≥ 7`. The
MN-verified closed form forces `Δ(b+1) ≥ 2`, hence `val(b+1) > val(0) = V`.

*Proof (§3 subtop).* `v₂(a−1) = 0`, `v₂(N₁) ≥ 1`. With `b = 2β+1`, set `Q := β+1 ≥ 4`, `R := P+2`;
the bridge collapses `Δ(b+1) = 2[v₂(∏_{t=1}^{Q}(P+2+t)) + v₂(N₁) − 1]`. The product of `Q ≥ 4`
consecutive integers has `v₂ ≥ 1` (an even factor survives, via `lemma_F`); with `v₂(N₁) ≥ 1` the
bracket is `≥ 1` and `Δ ≥ 2`. -/
theorem threerow_c3_boundary_sub1_aeven {a b P N₁ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 3)
    (ha : Even a) (hb : 7 ≤ b)
    (hN1 : N₁ = a * b * b + 5 * a * b + 6 * a - (b * b * b + b * b + 4 * b + 6))
    (hΔ : Δ = (b : ℤ) - 1 + 2 * ((Nat.digits 2 (P + 2)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₁ - 2 * vz (a - 1)) :
    2 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ka, hka⟩ := ha
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · omega
  · have hb2 : b = 2 * β + 1 := by omega
    have hβ3 : 3 ≤ β := by omega
    have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
      rw [ha2eq, sum_digits_two_mul]
    have hva1 : vz (a - 1) = 0 := by
      have hodd : ¬ (2 ∣ (a - 1)) := by omega
      simp [vz, padicValNat.eq_zero_of_not_dvd hodd]
    -- `v₂(N₁) ≥ 1`: even decomposition `N₁ = 2·(4Pβ²+14Pβ+12P+14β²+31β+18)` (`b = 2β+1`).
    have key : a * b * b + 5 * a * b + 6 * a
        = 2 * (4 * P * β ^ 2 + 14 * P * β + 12 * P + 14 * β ^ 2 + 31 * β + 18)
          + (b * b * b + b * b + 4 * b + 6) := by rw [hP, hb2]; ring
    have hN1eq : N₁ = 2 * (4 * P * β ^ 2 + 14 * P * β + 12 * P + 14 * β ^ 2 + 31 * β + 18) := by
      rw [hN1, key, Nat.add_sub_cancel]
    have hvN1 : vz N₁
        = 1 + vz (4 * P * β ^ 2 + 14 * P * β + 12 * P + 14 * β ^ 2 + 31 * β + 18) := by
      rw [hN1eq, vz_mul (by norm_num) (by positivity), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    have hvN1nn : 0 ≤ vz (4 * P * β ^ 2 + 14 * P * β + 12 * P + 14 * β ^ 2 + 31 * β + 18) := by
      simp only [vz]; exact Int.natCast_nonneg _
    -- bridge at `Q = β + 1`, `R = P + 2`; `lemma_F` gives `v₂(∏) ≥ 1` (delete the `t = 1` factor).
    have hbridge := vz_prod_Icc (P + 2) (β + 1)
    rw [show (P + 2) + (β + 1) = P + β + 3 by omega] at hbridge
    have hmem : (1 : ℕ) ∈ Finset.Icc 1 (β + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hF := lemma_F (R := P + 2) (Q := β + 1) (t₀ := 1) (by omega) hmem
    have hFz : 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 1), ((P + 2) + t)) := by
      have hnn : (0 : ℤ) ≤ vz ((P + 2) + 1) := by simp only [vz]; exact Int.natCast_nonneg _
      have : vz ((P + 2) + 1) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 1), ((P + 2) + t)) := by
        simp only [vz]; exact_mod_cast hF
      linarith
    have hb2z : (b : ℤ) = 2 * (β : ℤ) + 1 := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva1, hvN1]
    push_cast
    linarith

/-- **`c = 3` boundary, subtop index `j = b+1`, `a` odd.** Box-interior regime, `b ≥ 10`. The
MN-verified closed form forces `Δ(b+1) ≥ −1`, hence `val(b+1) > val(0) − 3 = V`.

*Proof (§4 subtop).* `b = 2β`, `β ≥ 5`, `v₂(a−1) = 1 + v₂(P+β+1)`, `v₂(N₁) ≥ 1`. Set `Q := β ≥ 4`,
`R := P+2`; the bridge collapses `Δ(b+1) = 2[v₂(∏) + v₂(N₁) − v₂(a−1)] − 3`. The single factor
`P+β+1` (`t = β−1`) is dissolved by `lemma_F`, giving `Δ ≥ 2[1 + 1 − 1] − 3 = −1`. -/
theorem threerow_c3_boundary_sub1_aodd {a b P N₁ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 3)
    (ha : Odd a) (hb : 10 ≤ b)
    (hN1 : N₁ = a * b * b + 5 * a * b + 6 * a - (b * b * b + b * b + 4 * b + 6))
    (hΔ : Δ = (b : ℤ) - 1 + 2 * ((Nat.digits 2 (P + 2)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₁ - 2 * vz (a - 1)) :
    -1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ka, hka⟩ := ha
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · have hb2 : b = 2 * β := by omega
    have hβ5 : 5 ≤ β := by omega
    have ha1eq : a - 1 = 2 * (P + β + 1) := by omega
    have ha2eq : a + 2 = 2 * (P + β + 2) + 1 := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 2)).sum + 1 := by
      rw [ha2eq, sum_digits_two_mul_add_one]
    have hva1 : vz (a - 1) = 1 + vz (P + β + 1) := by
      rw [ha1eq, vz_mul (by norm_num) (by omega), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    -- `v₂(N₁) ≥ 1`: even decomposition `N₁ = 2·(4Pβ²+10Pβ+6P+14β²+17β+6)` (`b = 2β`).
    have key : a * b * b + 5 * a * b + 6 * a
        = 2 * (4 * P * β ^ 2 + 10 * P * β + 6 * P + 14 * β ^ 2 + 17 * β + 6)
          + (b * b * b + b * b + 4 * b + 6) := by rw [hP, hb2]; ring
    have hN1eq : N₁ = 2 * (4 * P * β ^ 2 + 10 * P * β + 6 * P + 14 * β ^ 2 + 17 * β + 6) := by
      rw [hN1, key, Nat.add_sub_cancel]
    have hvN1 : vz N₁ = 1 + vz (4 * P * β ^ 2 + 10 * P * β + 6 * P + 14 * β ^ 2 + 17 * β + 6) := by
      rw [hN1eq, vz_mul (by norm_num) (by positivity), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    have hvN1nn : 0 ≤ vz (4 * P * β ^ 2 + 10 * P * β + 6 * P + 14 * β ^ 2 + 17 * β + 6) := by
      simp only [vz]; exact Int.natCast_nonneg _
    -- bridge at `Q = β`, `R = P + 2`; `lemma_F` deleting the `t = β−1` factor `P+β+1`.
    have hbridge := vz_prod_Icc (P + 2) β
    rw [show (P + 2) + β = P + β + 2 by omega] at hbridge
    have hmem : (β - 1) ∈ Finset.Icc 1 β := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hF := lemma_F (R := P + 2) (Q := β) (t₀ := β - 1) (by omega) hmem
    have hFz : vz (P + β + 1) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 β, ((P + 2) + t)) := by
      rw [show P + β + 1 = (P + 2) + (β - 1) by omega]
      simp only [vz]; exact_mod_cast hF
    have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva1, hvN1]
    push_cast
    linarith
  · omega

/-- **The three-row `c = 3` boundary lemma (assembled, end-to-end).**

Let `λ = (a, b, 3)` in the box-interior regime `a = 2P + b + 3`, and let `val0, valb1, valb2, valb3`
be the graded valuations `val(0), val(b+1), val(b+2), val(b+3)` with the MN-verified Lemma D
differences. With the threshold `V = val0 − θ` (`θ = 0` for `a` even on `b ≥ 7`; `θ = 3` for `a` odd
on `b ≥ 10`), all three boundary values strictly exceed the threshold:

> `V < valb1`,  `V < valb2`,  `V < valb3`.

This closes the boundary residual of the three-row `c = 3` even-`|J*|` theorem: no boundary index is
an extra minimiser, so `J*` is exactly the interior 2-adic box `j₀ + {0,2,4,6}` and `|J*| ∈ {1,2,4}`
is even on every tie — matching `c = 1, c = 2`. The only inputs beyond pure 2-adic number theory are
the closed forms `hΔ3, hΔ2, hΔ1` and the definitions `hN1, hN2`, all MN-verified facts about the
symmetric-function object `G_λ`. -/
theorem threerow_c3_boundary {a b P N₁ N₂ : ℕ} (val0 valb1 valb2 valb3 V : ℤ)
    (hP : a = 2 * P + b + 3)
    (hN2 : N₂ = a * (b + 3) - (b * b + 2 * b + 3))
    (hN1 : N₁ = a * b * b + 5 * a * b + 6 * a - (b * b * b + b * b + 4 * b + 6))
    (hΔ3 : valb3 - val0 = (b : ℤ) + 5 + 2 * ((Nat.digits 2 P).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) - 2 * vz (a - 1) - 2 * vz (P + 2))
    (hΔ2 : valb2 - val0 = (b : ℤ) + 2 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₂ - 2 * vz (a - 1) - 2 * vz (P + 2))
    (hΔ1 : valb1 - val0 = (b : ℤ) - 1 + 2 * ((Nat.digits 2 (P + 2)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₁ - 2 * vz (a - 1))
    (hcase : (Even a ∧ 7 ≤ b ∧ V = val0) ∨ (Odd a ∧ 10 ≤ b ∧ V = val0 - 3)) :
    V < valb1 ∧ V < valb2 ∧ V < valb3 := by
  rcases hcase with ⟨ha, hb, hV⟩ | ⟨ha, hb, hV⟩
  · have h3 := threerow_c3_boundary_top_aeven (valb3 - val0) hP ha hb hΔ3
    have h2 := threerow_c3_boundary_sub2_aeven (valb2 - val0) hP ha hb hN2 hΔ2
    have h1 := threerow_c3_boundary_sub1_aeven (valb1 - val0) hP ha hb hN1 hΔ1
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · have h3 := threerow_c3_boundary_top_aodd (valb3 - val0) hP ha hb hΔ3
    have h2 := threerow_c3_boundary_sub2_aodd (valb2 - val0) hP ha hb hN2 hΔ2
    have h1 := threerow_c3_boundary_sub1_aodd (valb1 - val0) hP ha hb hN1 hΔ1
    refine ⟨?_, ?_, ?_⟩ <;> omega

end TworowD4Kernel
