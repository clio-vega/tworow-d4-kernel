/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ThreeRowC3Boundary

/-!
# The three-row `c = 4` boundary lemma, end-to-end (`d = 4`)

This file assembles the **boundary lemma** for the three-row tie family `λ = (a, b, 4)` into a
single `sorry`-free declaration, closing the last residual of the `c = 4` interior theorem
(`~/projects/proofs/2026-06-18-c4-interior-Jstar-even.md`) via
`~/projects/proofs/2026-06-16-c4-boundary-complete.md` (`c = 4`, COMPLETE). It joins the already
machine-checked `c = 1, 2, 3` families (`ThreeRowC1Boundary`, `ThreeRowC2Boundary`,
`ThreeRowC3Boundary`).

## What is proved here, and what is assumed

For `λ = (a, b, 4) ⊢ 2m` (so `a + b = 2m − 4`, hence `a, b` have the **same** parity) the graded
valuations are `val(j) = j + 2 v₂(G_j)`, `G_j = ⟨s_λ, (p₂ + π e₂)^m⟩_{[π^j]} = C(m, j) M_j`. Because
`c = 4` is **even**, the interior theorem pins `j₀ = min J* = 0` and the offset `θ = 0` for *both*
parities of `a` (contrast `c = 3`, where `a` odd forced `θ = 3`). So the threshold is `V = val(0)`
and the boundary lemma is the strict statement: each of the four boundary indices
`j ∈ {b+1, b+2, b+3, b+4}` satisfies `val(j) > V`, i.e. `Δ(b+i) > 0` for `i = 1, 2, 3, 4`.

We work in the **box-interior regime** `a = 2P + b + 4` with `P ≥ 0` (so `a ≥ b + 4`), `b ≥ 6`. The
finitely many smaller shapes `b ∈ {4, 5}` are the per-family boundary-tie casework of the interior
note.

Writing `Δ(b+i) := val(b+i) − val(0)` and `s₂ n = (Nat.digits 2 n).sum`, the §1/§2 master valuation
(`R_i := G_{b+i}/G_0` exact ratio, MN-verified `m ≤ 41`; here re-expressed in digit-sum form via the
bridge `TworowD4Kernel.vz_prod_Icc` — a purely 2-adic restatement verified algebraically) reads

> `Δ(b+4) = (b+8) + 2 s₂(P)   − 2 s₂(a+2)          − 2 v₂(a−2)`,
> `Δ(b+3) = (b+5) + 2 s₂(P+1) − 2 s₂(a+2) + 2 v₂(N₃) − 2 v₂(a−2)`,
> `Δ(b+2) = b     + 2 s₂(P+2) − 2 s₂(a+2) + 2 v₂(N₂) − 2 v₂(a−2)`,
> `Δ(b+1) = (b−3) + 2 s₂(P+3) − 2 s₂(a+2) + 2 v₂(N₁) − 2 v₂(a−2)`,

where, with the standing relation `a = 2P + b + 4` giving `a − 2 = 2P + b + 2` (`= a − c + 2`),

> `N₃ = a(b+4) − (b²+3b+8)`,
> `N₂ = a²b² + 7a²b + 12a² + b⁴ + 2b³ + 13b² + 16b − (2ab³ + 9ab² + 21ab + 20a + 8)`,
> `N₁ = a²b³ + 9a²b² + 26a²b + 24a² + b⁵ + 17b³`
>      `   − (2ab⁴ + 7ab³ + 13ab² + 14ab + 2b⁴ + 4b² + 84b + 96)`

are the polynomial factors of `M_{b+3}, M_{b+2}, M_{b+1}` (`N₄ := 1`). These rest on the
Murnaghan–Nakayama closed forms for `M_0` (hook), `M_{b+4}` (Lemma T) and
`M_{b+1}, M_{b+2}, M_{b+3}` — symmetric-function facts out of Mathlib's reach. Consistent with
every prior session, they are taken as the **hypotheses** `hΔ4, …, hΔ1`, together with the
definitions of `N₁, N₂, N₃`.
Everything downstream — the genuine 2-adic number theory, including the **2-adic content** of
`N₁, N₂, N₃` derived from their definitions — is proved here from scratch.

## The number-theoretic content (proved, not assumed)

`c = 4` is **even**, so `a − b + 1 = 2P + 5` is **odd** (no smooth deficit) and **no `lemma_F2` is
needed** (unlike `c = 3`'s `a`-odd keystone). The discharge is the `c = 2` template lifted to four
indices:

* **`b` odd** (`v₂(a−2) = 0`): subadditivity `s₂(a+2) ≤ s₂(P+4−i) + s₂(b+2i−2)` and Lemma A
  (`TworowD4Kernel.two_mul_sum_digits_le`) plus the **content bounds** `v₂(N₂) ≥ 2`, `v₂(N₁) ≥ 2`.
* **`b` even** (`v₂(a−2) = 1 + v₂(P+b/2+1)`): the bridge `vz_prod_Icc` plus the factor-in-product
  `TworowD4Kernel.lemma_F` (indices `i = 4, 2`) or plain divisibility (`i = 3, 1`), plus the content
  bounds `v₂(N₃) ≥ 1`, `v₂(N₂) ≥ 2`, `v₂(N₁) ≥ 3`. The lone `v₂(a−2)` deficit is absorbed by the
  factor `P + b/2 + 1` inside the consecutive-product run.

The content bounds come from the explicit even decompositions after `a = 2P + b + 4` and the parity
split `b = 2β` / `b = 2β + 1`; **none factors `N_i`** (the `c ≥ 4` irreducibility wall is
irrelevant).

## References

`2026-06-16-c4-boundary-complete.md` (`c = 4`, COMPLETE); the `c = 1, 2, 3` companions; the
factor-in-product engine `TworowD4Kernel.lemma_F`; the bridge `TworowD4Kernel.vz_prod_Icc`.
-/

namespace TworowD4Kernel

open Nat Finset

/-- `v₂(N₃) ≥ 1` for `b` even. With `b = 2β`, `a = 2P+b+4`, the explicit even decomposition
`N₃ = 2·(2βP + 5β + 4P + 4)` holds. -/
theorem vz_N3_ge_one_beven {a b P β N₃ : ℕ} (hP : a = 2 * P + b + 4) (hb2 : b = 2 * β)
    (hN3 : N₃ = a * b + 4 * a - (b * b + 3 * b + 8)) : 1 ≤ vz N₃ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : a * b + 4 * a
      = 2 * (2 * β * P + 5 * β + 4 * P + 4) + (b * b + 3 * b + 8) := by rw [hP, hb2]; ring
  have hN3eq : N₃ = 2 ^ 1 * (2 * β * P + 5 * β + 4 * P + 4) := by
    rw [hN3, key, Nat.add_sub_cancel]; ring
  have hne : N₃ ≠ 0 := by rw [hN3eq]; positivity
  have hdvd : (2 : ℕ) ^ 1 ∣ N₃ := by rw [hN3eq]; exact dvd_mul_right _ _
  have := (padicValNat_dvd_iff_le hne).mp hdvd
  simp only [vz]; exact_mod_cast this

/-- `v₂(N₂) ≥ 2` (both parities). After `a = 2P+b+4`, `N₂ = 4·Q` with `Q` an integer polynomial in
`P, β` (the inner polynomial differs by parity of `b`); the `c = 4` Number-Lemma content floor. -/
theorem vz_N2_ge_two {a b P β N₂ : ℕ} (hP : a = 2 * P + b + 4)
    (hb : b = 2 * β ∨ b = 2 * β + 1)
    (hN2 : N₂ = a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
      + 13 * (b * b) + 16 * b
      - (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8)) :
    2 ≤ vz N₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hb with hb2 | hb2
  · -- `b = 2β`
    have key : a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
        + 13 * (b * b) + 16 * b
        = 4 * (4 * β ^ 2 * P ^ 2 + 26 * β ^ 2 * P + 40 * β ^ 2 + 14 * β * P ^ 2 + 59 * β * P
            + 60 * β + 12 * P ^ 2 + 38 * P + 26)
          + (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8) := by
      rw [hP, hb2]; ring
    have hN2eq : N₂ = 2 ^ 2 * (4 * β ^ 2 * P ^ 2 + 26 * β ^ 2 * P + 40 * β ^ 2 + 14 * β * P ^ 2
        + 59 * β * P + 60 * β + 12 * P ^ 2 + 38 * P + 26) := by
      rw [hN2, key, Nat.add_sub_cancel]; ring
    have hne : N₂ ≠ 0 := by rw [hN2eq]; positivity
    have hdvd : (2 : ℕ) ^ 2 ∣ N₂ := by rw [hN2eq]; exact dvd_mul_right _ _
    have := (padicValNat_dvd_iff_le hne).mp hdvd
    simp only [vz]; exact_mod_cast this
  · -- `b = 2β + 1`
    have key : a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
        + 13 * (b * b) + 16 * b
        = 4 * (4 * β ^ 2 * P ^ 2 + 26 * β ^ 2 * P + 40 * β ^ 2 + 18 * β * P ^ 2 + 85 * β * P
            + 100 * β + 20 * P ^ 2 + 74 * P + 66)
          + (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8) := by
      rw [hP, hb2]; ring
    have hN2eq : N₂ = 2 ^ 2 * (4 * β ^ 2 * P ^ 2 + 26 * β ^ 2 * P + 40 * β ^ 2 + 18 * β * P ^ 2
        + 85 * β * P + 100 * β + 20 * P ^ 2 + 74 * P + 66) := by
      rw [hN2, key, Nat.add_sub_cancel]; ring
    have hne : N₂ ≠ 0 := by rw [hN2eq]; positivity
    have hdvd : (2 : ℕ) ^ 2 ∣ N₂ := by rw [hN2eq]; exact dvd_mul_right _ _
    have := (padicValNat_dvd_iff_le hne).mp hdvd
    simp only [vz]; exact_mod_cast this

/-- `v₂(N₁) ≥ 3` for `b` even. With `b = 2β`, `a = 2P+b+4`, `N₁ = 8·Q` with `Q` integer. -/
theorem vz_N1_ge_three_beven {a b P β N₁ : ℕ} (hP : a = 2 * P + b + 4) (hb2 : b = 2 * β)
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96)) :
    3 ≤ vz N₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      = 8 * (4 * β ^ 3 * P ^ 2 + 38 * β ^ 3 * P + 90 * β ^ 3 + 18 * β ^ 2 * P ^ 2 + 111 * β ^ 2 * P
          + 153 * β ^ 2 + 26 * β * P ^ 2 + 121 * β * P + 117 * β + 12 * P ^ 2 + 48 * P + 36)
        + (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
            + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96) := by rw [hP, hb2]; ring
  have hN1eq : N₁ = 2 ^ 3 * (4 * β ^ 3 * P ^ 2 + 38 * β ^ 3 * P + 90 * β ^ 3 + 18 * β ^ 2 * P ^ 2
      + 111 * β ^ 2 * P + 153 * β ^ 2 + 26 * β * P ^ 2 + 121 * β * P + 117 * β + 12 * P ^ 2
      + 48 * P + 36) := by rw [hN1, key, Nat.add_sub_cancel]; ring
  have hne : N₁ ≠ 0 := by rw [hN1eq]; positivity
  have hdvd : (2 : ℕ) ^ 3 ∣ N₁ := by rw [hN1eq]; exact dvd_mul_right _ _
  have := (padicValNat_dvd_iff_le hne).mp hdvd
  simp only [vz]; exact_mod_cast this

/-- `v₂(N₁) ≥ 2` for `b` odd. With `b = 2β+1`, `a = 2P+b+4`, `N₁ = 4·Q` with `Q` integer. -/
theorem vz_N1_ge_two_bodd {a b P β N₁ : ℕ} (hP : a = 2 * P + b + 4) (hb2 : b = 2 * β + 1)
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96)) :
    2 ≤ vz N₁ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      = 4 * (8 * β ^ 3 * P ^ 2 + 76 * β ^ 3 * P + 180 * β ^ 3 + 48 * β ^ 2 * P ^ 2 + 336 * β ^ 2 * P
          + 576 * β ^ 2 + 94 * β * P ^ 2 + 521 * β * P + 675 * β + 60 * P ^ 2 + 282 * P + 288)
        + (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
            + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96) := by rw [hP, hb2]; ring
  have hN1eq : N₁ = 2 ^ 2 * (8 * β ^ 3 * P ^ 2 + 76 * β ^ 3 * P + 180 * β ^ 3 + 48 * β ^ 2 * P ^ 2
      + 336 * β ^ 2 * P + 576 * β ^ 2 + 94 * β * P ^ 2 + 521 * β * P + 675 * β + 60 * P ^ 2
      + 282 * P + 288) := by rw [hN1, key, Nat.add_sub_cancel]; ring
  have hne : N₁ ≠ 0 := by rw [hN1eq]; positivity
  have hdvd : (2 : ℕ) ^ 2 ∣ N₁ := by rw [hN1eq]; exact dvd_mul_right _ _
  have := (padicValNat_dvd_iff_le hne).mp hdvd
  simp only [vz]; exact_mod_cast this

/-! ### The multiplicative-redundancy content, packaged (for the joint FREE/RIGID note).

Rick's additive side ships a single named axiom-free witness `additive_redundancy_at_eS`. These two
lemmas are the **multiplicative-side counterpart**: one citable statement per parity of `b` that
bundles the fixed 2-adic floors of the redundancy factors `N₁, N₂, N₃`, each derived above from the
explicit even decomposition `N_i = 2^{k_i} · (integer)` (no `N_i` is factored). -/

/-- **Multiplicative-redundancy content floor, `c = 4`, `b` even** (`a` even). The redundancy
factors carry the fixed 2-adic floors `v₂(N₃) ≥ 1`, `v₂(N₂) ≥ 2`, `v₂(N₁) ≥ 3`. Axiom-free witness
of the multiplicative-side redundancy move; counterpart to Rick's additive
`additive_redundancy_at_eS`. -/
theorem multiplicative_redundancy_c4_beven {a b P β N₁ N₂ N₃ : ℕ}
    (hP : a = 2 * P + b + 4) (hb2 : b = 2 * β)
    (hN3 : N₃ = a * b + 4 * a - (b * b + 3 * b + 8))
    (hN2 : N₂ = a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
      + 13 * (b * b) + 16 * b
      - (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8))
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96)) :
    1 ≤ vz N₃ ∧ 2 ≤ vz N₂ ∧ 3 ≤ vz N₁ :=
  ⟨vz_N3_ge_one_beven hP hb2 hN3, vz_N2_ge_two hP (Or.inl hb2) hN2,
   vz_N1_ge_three_beven hP hb2 hN1⟩

/-- **Multiplicative-redundancy content floor, `c = 4`, `b` odd** (`a` odd). The redundancy factors
carry the fixed 2-adic floors `v₂(N₂) ≥ 2`, `v₂(N₁) ≥ 2` (`N₃` needs no floor when `v₂(a−2) = 0`).
Axiom-free witness of the multiplicative-side redundancy move; counterpart to Rick's additive
`additive_redundancy_at_eS`. -/
theorem multiplicative_redundancy_c4_bodd {a b P β N₁ N₂ : ℕ}
    (hP : a = 2 * P + b + 4) (hb2 : b = 2 * β + 1)
    (hN2 : N₂ = a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
      + 13 * (b * b) + 16 * b
      - (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8))
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96)) :
    2 ≤ vz N₂ ∧ 2 ≤ vz N₁ :=
  ⟨vz_N2_ge_two hP (Or.inr hb2) hN2, vz_N1_ge_two_bodd hP hb2 hN1⟩

/-! ### The four boundary indices, `b` even (`a` even). Bridge + `lemma_F` / divisibility. -/

/-- **`c = 4` boundary, top index `j = b+4`, `b` even.** Forces `Δ(b+4) ≥ 2 > 0`.

*Proof.* `b = 2β` (`β ≥ 3`), `a+2 = 2(P+β+3)`, `a−2 = 2(P+β+1)`. The bridge at `R = P`, `Q = β+3`
gives `s₂(P) − s₂(a+2) = v₂(∏_{t=1}^{β+3}(P+t)) − (β+3)`; `P+β+1` is the `t = β+1` factor, dissolved
by `lemma_F` (`Q ≥ 4`), absorbing the lone `v₂(a−2) = 1 + v₂(P+β+1)` deficit. -/
theorem threerow_c4_boundary_top_beven {a b P : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4) (hb : 6 ≤ b)
    (hbe : Even b)
    (hΔ : Δ = (b : ℤ) + 8 + 2 * ((Nat.digits 2 P).sum : ℤ) - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ)
      - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := hbe
  have hb2 : b = 2 * β := by omega
  have hβ3 : 3 ≤ β := by omega
  have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
  have ham2eq : a - 2 = 2 * (P + β + 1) := by omega
  have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
    rw [ha2eq, sum_digits_two_mul]
  have hvm2 : vz (a - 2) = 1 + vz (P + β + 1) := by
    rw [ham2eq, vz_mul (by norm_num) (by omega), vz]
    norm_num [padicValNat.self (show 1 < 2 by norm_num)]
  have hbridge := vz_prod_Icc P (β + 3)
  rw [show P + (β + 3) = P + β + 3 by omega] at hbridge
  have hmem : (β + 1) ∈ Finset.Icc 1 (β + 3) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hF := lemma_F (R := P) (Q := β + 3) (t₀ := β + 1) (by omega) hmem
  have hFz : vz (P + β + 1) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 3), (P + t)) := by
    rw [show P + β + 1 = P + (β + 1) by omega]; simp only [vz]; exact_mod_cast hF
  have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
  push_cast at hbridge
  rw [hΔ, hsa2, hvm2]
  push_cast
  linarith

/-- **`c = 4` boundary, index `j = b+3`, `b` even.** Forces `Δ(b+3) ≥ 1 > 0`.

*Proof.* Bridge at `R = P+1`, `Q = β+2`; `P+β+1` is the `t = β` factor, so divisibility gives
`v₂(∏) ≥ v₂(P+β+1)`, absorbing `v₂(a−2)`. With `v₂(N₃) ≥ 1` (Lemma C(ii)) the margin is `≥ 1`. -/
theorem threerow_c4_boundary_sub3_beven {a b P N₃ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4) (hb : 6 ≤ b)
    (hbe : Even b) (hN3 : N₃ = a * b + 4 * a - (b * b + 3 * b + 8))
    (hΔ : Δ = (b : ℤ) + 5 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₃ - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := hbe
  have hb2 : b = 2 * β := by omega
  have hβ3 : 3 ≤ β := by omega
  have hvN3 := vz_N3_ge_one_beven hP hb2 hN3
  have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
  have ham2eq : a - 2 = 2 * (P + β + 1) := by omega
  have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
    rw [ha2eq, sum_digits_two_mul]
  have hvm2 : vz (a - 2) = 1 + vz (P + β + 1) := by
    rw [ham2eq, vz_mul (by norm_num) (by omega), vz]
    norm_num [padicValNat.self (show 1 < 2 by norm_num)]
  have hbridge := vz_prod_Icc (P + 1) (β + 2)
  rw [show (P + 1) + (β + 2) = P + β + 3 by omega] at hbridge
  have hprodne : (∏ t ∈ Finset.Icc 1 (β + 2), ((P + 1) + t)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_; intro t ht; omega
  have hdvd : ((P + 1) + β) ∣ ∏ t ∈ Finset.Icc 1 (β + 2), ((P + 1) + t) :=
    Finset.dvd_prod_of_mem (fun t => (P + 1) + t) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hdvdle := vz_dvd_le hprodne hdvd
  rw [show (P + 1) + β = P + β + 1 by omega] at hdvdle
  have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
  push_cast at hbridge
  rw [hΔ, hsa2, hvm2]
  push_cast
  linarith

/-- **`c = 4` boundary, index `j = b+2`, `b` even.** Forces `Δ(b+2) ≥ 2 > 0`.

*Proof.* Bridge at `R = P+2`, `Q = β+1`; `P+β+1` is the `t = β−1` factor, dissolved by `lemma_F`
(`Q = β+1 ≥ 4`). With `v₂(N₂) ≥ 2` (Lemma C(i)) the margin is `≥ 2`. -/
theorem threerow_c4_boundary_sub2_beven {a b P β N₂ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4)
    (hb : 6 ≤ b) (hb2 : b = 2 * β)
    (hN2 : N₂ = a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
      + 13 * (b * b) + 16 * b
      - (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8))
    (hΔ : Δ = (b : ℤ) + 2 * ((Nat.digits 2 (P + 2)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₂ - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ3 : 3 ≤ β := by omega
  have hvN2 := vz_N2_ge_two hP (Or.inl hb2) hN2
  have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
  have ham2eq : a - 2 = 2 * (P + β + 1) := by omega
  have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
    rw [ha2eq, sum_digits_two_mul]
  have hvm2 : vz (a - 2) = 1 + vz (P + β + 1) := by
    rw [ham2eq, vz_mul (by norm_num) (by omega), vz]
    norm_num [padicValNat.self (show 1 < 2 by norm_num)]
  have hbridge := vz_prod_Icc (P + 2) (β + 1)
  rw [show (P + 2) + (β + 1) = P + β + 3 by omega] at hbridge
  have hmem : (β - 1) ∈ Finset.Icc 1 (β + 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hF := lemma_F (R := P + 2) (Q := β + 1) (t₀ := β - 1) (by omega) hmem
  have hFz : vz (P + β + 1) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 1), ((P + 2) + t)) := by
    rw [show P + β + 1 = (P + 2) + (β - 1) by omega]; simp only [vz]; exact_mod_cast hF
  have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
  push_cast at hbridge
  rw [hΔ, hsa2, hvm2]
  push_cast
  linarith

/-- **`c = 4` boundary, index `j = b+1`, `b` even.** Forces `Δ(b+1) ≥ 1 > 0`.

*Proof.* Bridge at `R = P+3`, `Q = β`; `P+β+1` is the `t = β−2` factor, so divisibility gives
`v₂(∏) ≥ v₂(P+β+1)`. With `v₂(N₁) ≥ 3` (Lemma C(iii)) the margin is `≥ 1`. -/
theorem threerow_c4_boundary_sub1_beven {a b P β N₁ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4)
    (hb : 6 ≤ b) (hb2 : b = 2 * β)
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96))
    (hΔ : Δ = (b : ℤ) - 3 + 2 * ((Nat.digits 2 (P + 3)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₁ - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hβ3 : 3 ≤ β := by omega
  have hvN1 := vz_N1_ge_three_beven hP hb2 hN1
  have ha2eq : a + 2 = 2 * (P + β + 3) := by omega
  have ham2eq : a - 2 = 2 * (P + β + 1) := by omega
  have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 3)).sum := by
    rw [ha2eq, sum_digits_two_mul]
  have hvm2 : vz (a - 2) = 1 + vz (P + β + 1) := by
    rw [ham2eq, vz_mul (by norm_num) (by omega), vz]
    norm_num [padicValNat.self (show 1 < 2 by norm_num)]
  have hbridge := vz_prod_Icc (P + 3) β
  rw [show (P + 3) + β = P + β + 3 by omega] at hbridge
  have hprodne : (∏ t ∈ Finset.Icc 1 β, ((P + 3) + t)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_; intro t ht; omega
  have hdvd : ((P + 3) + (β - 2)) ∣ ∏ t ∈ Finset.Icc 1 β, ((P + 3) + t) :=
    Finset.dvd_prod_of_mem (fun t => (P + 3) + t) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  have hdvdle := vz_dvd_le hprodne hdvd
  rw [show (P + 3) + (β - 2) = P + β + 1 by omega] at hdvdle
  have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
  push_cast at hbridge
  rw [hΔ, hsa2, hvm2]
  push_cast
  linarith

/-! ### The four boundary indices, `b` odd (`a` odd). Subadditivity + Lemma A. -/

/-- **`c = 4` boundary, top index `j = b+4`, `b` odd.** Forces `Δ(b+4) ≥ 3 > 0`.

*Proof.* `b` odd ⟹ `a−2` odd ⟹ `v₂(a−2) = 0`. Subadditivity `s₂(a+2) ≤ s₂(P) + s₂(b+6)`
(`a+2 = 2P + (b+6)`) and Lemma A `2 s₂(b+6) ≤ b+5` give `Δ ≥ (b+8) − (b+5) = 3`. -/
theorem threerow_c4_boundary_top_bodd {a b P : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4) (hb : 6 ≤ b)
    (hbo : Odd b)
    (hΔ : Δ = (b : ℤ) + 8 + 2 * ((Nat.digits 2 P).sum : ℤ) - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ)
      - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := hbo
  have hvm2 : vz (a - 2) = 0 := by
    have : ¬ (2 ∣ (a - 2)) := by omega
    simp [vz, padicValNat.eq_zero_of_not_dvd this]
  have hsub : (Nat.digits 2 (a + 2)).sum ≤ (Nat.digits 2 P).sum + (Nat.digits 2 (b + 6)).sum := by
    have h := sum_digits_two_add_le (2 * P + (b + 6)) (2 * P) (b + 6) rfl
    rw [sum_digits_two_mul, show 2 * P + (b + 6) = a + 2 by omega] at h
    exact h
  have hLemA : 2 * (Nat.digits 2 (b + 6)).sum ≤ b + 5 := by
    have := two_mul_sum_digits_le (b + 6) (by omega); omega
  rw [hΔ, hvm2]
  have hsubz : ((Nat.digits 2 (a + 2)).sum : ℤ)
      ≤ ((Nat.digits 2 P).sum : ℤ) + ((Nat.digits 2 (b + 6)).sum : ℤ) := by exact_mod_cast hsub
  have hLemAz : 2 * ((Nat.digits 2 (b + 6)).sum : ℤ) ≤ (b : ℤ) + 5 := by exact_mod_cast hLemA
  linarith

/-- **`c = 4` boundary, index `j = b+3`, `b` odd.** Forces `Δ(b+3) ≥ 2 > 0`.

*Proof.* `v₂(a−2) = 0`, `v₂(N₃) ≥ 0`. Subadditivity `s₂(a+2) ≤ s₂(P+1) + s₂(b+4)`
(`a+2 = 2(P+1) + (b+4)`) and Lemma A `2 s₂(b+4) ≤ b+3` give `Δ ≥ (b+5) − (b+3) = 2`. -/
theorem threerow_c4_boundary_sub3_bodd {a b P N₃ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4) (hb : 6 ≤ b)
    (hbo : Odd b)
    (hΔ : Δ = (b : ℤ) + 5 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₃ - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨β, hβ⟩ := hbo
  have hvm2 : vz (a - 2) = 0 := by
    have : ¬ (2 ∣ (a - 2)) := by omega
    simp [vz, padicValNat.eq_zero_of_not_dvd this]
  have hvN3 : (0 : ℤ) ≤ vz N₃ := by simp only [vz]; exact Int.natCast_nonneg _
  have hsub : (Nat.digits 2 (a + 2)).sum
      ≤ (Nat.digits 2 (P + 1)).sum + (Nat.digits 2 (b + 4)).sum := by
    have h := sum_digits_two_add_le (2 * (P + 1) + (b + 4)) (2 * (P + 1)) (b + 4) rfl
    rw [sum_digits_two_mul, show 2 * (P + 1) + (b + 4) = a + 2 by omega] at h
    exact h
  have hLemA : 2 * (Nat.digits 2 (b + 4)).sum ≤ b + 3 := by
    have := two_mul_sum_digits_le (b + 4) (by omega); omega
  rw [hΔ, hvm2]
  have hsubz : ((Nat.digits 2 (a + 2)).sum : ℤ)
      ≤ ((Nat.digits 2 (P + 1)).sum : ℤ) + ((Nat.digits 2 (b + 4)).sum : ℤ) := by
    exact_mod_cast hsub
  have hLemAz : 2 * ((Nat.digits 2 (b + 4)).sum : ℤ) ≤ (b : ℤ) + 3 := by exact_mod_cast hLemA
  linarith

/-- **`c = 4` boundary, index `j = b+2`, `b` odd.** Forces `Δ(b+2) ≥ 3 > 0`.

*Proof.* `v₂(a−2) = 0`, `v₂(N₂) ≥ 2` (Lemma C(i)). Subadditivity `s₂(a+2) ≤ s₂(P+2) + s₂(b+2)`
(`a+2 = 2(P+2) + (b+2)`) and Lemma A `2 s₂(b+2) ≤ b+1` give `Δ ≥ (b+4) − (b+1) = 3`. -/
theorem threerow_c4_boundary_sub2_bodd {a b P β N₂ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4)
    (hb : 6 ≤ b) (hb2 : b = 2 * β + 1)
    (hN2 : N₂ = a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
      + 13 * (b * b) + 16 * b
      - (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8))
    (hΔ : Δ = (b : ℤ) + 2 * ((Nat.digits 2 (P + 2)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₂ - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvm2 : vz (a - 2) = 0 := by
    have : ¬ (2 ∣ (a - 2)) := by omega
    simp [vz, padicValNat.eq_zero_of_not_dvd this]
  have hvN2 := vz_N2_ge_two hP (Or.inr hb2) hN2
  have hsub : (Nat.digits 2 (a + 2)).sum
      ≤ (Nat.digits 2 (P + 2)).sum + (Nat.digits 2 (b + 2)).sum := by
    have h := sum_digits_two_add_le (2 * (P + 2) + (b + 2)) (2 * (P + 2)) (b + 2) rfl
    rw [sum_digits_two_mul, show 2 * (P + 2) + (b + 2) = a + 2 by omega] at h
    exact h
  have hLemA : 2 * (Nat.digits 2 (b + 2)).sum ≤ b + 1 := by
    have := two_mul_sum_digits_le (b + 2) (by omega); omega
  rw [hΔ, hvm2]
  have hsubz : ((Nat.digits 2 (a + 2)).sum : ℤ)
      ≤ ((Nat.digits 2 (P + 2)).sum : ℤ) + ((Nat.digits 2 (b + 2)).sum : ℤ) := by
    exact_mod_cast hsub
  have hLemAz : 2 * ((Nat.digits 2 (b + 2)).sum : ℤ) ≤ (b : ℤ) + 1 := by exact_mod_cast hLemA
  linarith

/-- **`c = 4` boundary, index `j = b+1`, `b` odd.** Forces `Δ(b+1) ≥ 2 > 0`.

*Proof.* `v₂(a−2) = 0`, `v₂(N₁) ≥ 2` (Lemma C(iii)). Subadditivity `s₂(a+2) ≤ s₂(P+3) + s₂(b)`
(`a+2 = 2(P+3) + b`) and Lemma A `2 s₂(b) ≤ b−1` give `Δ ≥ (b+1) − (b−1) = 2`. -/
theorem threerow_c4_boundary_sub1_bodd {a b P β N₁ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 4)
    (hb : 6 ≤ b) (hb2 : b = 2 * β + 1)
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96))
    (hΔ : Δ = (b : ℤ) - 3 + 2 * ((Nat.digits 2 (P + 3)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₁ - 2 * vz (a - 2)) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hvm2 : vz (a - 2) = 0 := by
    have : ¬ (2 ∣ (a - 2)) := by omega
    simp [vz, padicValNat.eq_zero_of_not_dvd this]
  have hvN1 := vz_N1_ge_two_bodd hP hb2 hN1
  have hsub : (Nat.digits 2 (a + 2)).sum ≤ (Nat.digits 2 (P + 3)).sum + (Nat.digits 2 b).sum := by
    have h := sum_digits_two_add_le (2 * (P + 3) + b) (2 * (P + 3)) b rfl
    rw [sum_digits_two_mul, show 2 * (P + 3) + b = a + 2 by omega] at h
    exact h
  have hLemA : 2 * (Nat.digits 2 b).sum ≤ b - 1 := by
    have := two_mul_sum_digits_le b (by omega); omega
  rw [hΔ, hvm2]
  have hsubz : ((Nat.digits 2 (a + 2)).sum : ℤ)
      ≤ ((Nat.digits 2 (P + 3)).sum : ℤ) + ((Nat.digits 2 b).sum : ℤ) := by exact_mod_cast hsub
  have hLemAz : 2 * ((Nat.digits 2 b).sum : ℤ) ≤ (b : ℤ) - 1 := by
    have h1 : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast (by omega : 1 ≤ b)
    have := hLemA
    have hbz : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    calc 2 * ((Nat.digits 2 b).sum : ℤ) = ((2 * (Nat.digits 2 b).sum : ℕ) : ℤ) := by push_cast; ring
      _ ≤ ((b - 1 : ℕ) : ℤ) := by exact_mod_cast hLemA
      _ = (b : ℤ) - 1 := hbz
  linarith

/-- **The three-row `c = 4` boundary lemma (assembled, end-to-end).**

Let `λ = (a, b, 4)` in the box-interior regime `a = 2P + b + 4`, `b ≥ 6`, and let
`val0, valb1, valb2, valb3, valb4` be the graded valuations `val(0), …, val(b+4)` with the
MN-verified §1/§2 master valuation differences. Since `c = 4` is even the offset is `θ = 0` for both
parities, so the threshold is `V = val0` and all four boundary values strictly exceed it:

> `V < valb1`,  `V < valb2`,  `V < valb3`,  `V < valb4`.

This closes the boundary residual of the three-row `c = 4` even-`|J*|` theorem: no boundary index is
an extra minimiser, so `J*` is exactly the interior 2-adic box and `|J*|` is even on every tie —
matching `c = 1, 2, 3`. The only inputs beyond pure 2-adic number theory are the closed forms
`hΔ4, …, hΔ1` and the definitions `hN1, hN2, hN3`, all MN-verified facts about the
symmetric-function object `G_λ`. -/
theorem threerow_c4_boundary {a b P N₁ N₂ N₃ : ℕ} (val0 valb1 valb2 valb3 valb4 V : ℤ)
    (hP : a = 2 * P + b + 4) (hb : 6 ≤ b) (hV : V = val0)
    (hN3 : N₃ = a * b + 4 * a - (b * b + 3 * b + 8))
    (hN2 : N₂ = a * a * b * b + 7 * (a * a) * b + 12 * (a * a) + b * b * b * b + 2 * (b * b * b)
      + 13 * (b * b) + 16 * b
      - (2 * a * (b * b * b) + 9 * a * (b * b) + 21 * (a * b) + 20 * a + 8))
    (hN1 : N₁ = a * a * (b * b * b) + 9 * (a * a) * (b * b) + 26 * (a * a) * b + 24 * (a * a)
      + b * b * b * b * b + 17 * (b * b * b)
      - (2 * a * (b * b * b * b) + 7 * a * (b * b * b) + 13 * a * (b * b) + 14 * (a * b)
          + 2 * (b * b * b * b) + 4 * (b * b) + 84 * b + 96))
    (hΔ4 : valb4 - val0 = (b : ℤ) + 8 + 2 * ((Nat.digits 2 P).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) - 2 * vz (a - 2))
    (hΔ3 : valb3 - val0 = (b : ℤ) + 5 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₃ - 2 * vz (a - 2))
    (hΔ2 : valb2 - val0 = (b : ℤ) + 2 * ((Nat.digits 2 (P + 2)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₂ - 2 * vz (a - 2))
    (hΔ1 : valb1 - val0 = (b : ℤ) - 3 + 2 * ((Nat.digits 2 (P + 3)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz N₁ - 2 * vz (a - 2)) :
    V < valb1 ∧ V < valb2 ∧ V < valb3 ∧ V < valb4 := by
  rcases Nat.even_or_odd b with hbe | hbo
  · obtain ⟨β, hβ⟩ := hbe
    have hb2 : b = 2 * β := by omega
    have h4 := threerow_c4_boundary_top_beven (valb4 - val0) hP hb ⟨β, hβ⟩ hΔ4
    have h3 := threerow_c4_boundary_sub3_beven (valb3 - val0) hP hb ⟨β, hβ⟩ hN3 hΔ3
    have h2 := threerow_c4_boundary_sub2_beven (valb2 - val0) hP hb hb2 hN2 hΔ2
    have h1 := threerow_c4_boundary_sub1_beven (valb1 - val0) hP hb hb2 hN1 hΔ1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
  · obtain ⟨β, hβ⟩ := hbo
    have hb2 : b = 2 * β + 1 := by omega
    have h4 := threerow_c4_boundary_top_bodd (valb4 - val0) hP hb ⟨β, hβ⟩ hΔ4
    have h3 := threerow_c4_boundary_sub3_bodd (valb3 - val0) hP hb ⟨β, hβ⟩ hΔ3
    have h2 := threerow_c4_boundary_sub2_bodd (valb2 - val0) hP hb hb2 hN2 hΔ2
    have h1 := threerow_c4_boundary_sub1_bodd (valb1 - val0) hP hb hb2 hN1 hΔ1
    refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end TworowD4Kernel
