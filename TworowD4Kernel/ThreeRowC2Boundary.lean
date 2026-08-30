/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ThreeRowC1Boundary
import TworowD4Kernel.LemmaF
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The three-row `c = 2` boundary lemma, end-to-end (`d = 4`)

This file assembles the **boundary lemma** for the three-row tie family `λ = (a, b, 2)` into a
single `sorry`-free declaration, closing the last residual of the `c = 2` interior theorem
(`~/projects/proofs/2026-06-13-threerow-c2-Jstar-even.md`) via §3 of
`~/projects/proofs/2026-06-15-boundary-lemma-threerow.md` (`c = 2`, COMPLETE).

## What is proved here, and what is assumed

For `λ = (a, b, 2) ⊢ 2m` the graded valuations are `val(j) = j + 2 v₂(G_j)`,
`G_j = ⟨s_λ, e₂^j h₁^{2(m−j)}⟩`. The interior theorem pins the minimiser set `J*` to the interior
2-adic box `{0, 2, 4}` (here `j₀ = 0` always, so the threshold is `V = val(0)`, i.e. `θ = 0`) and
leaves **one** residual: that neither boundary index `j ∈ {b+1, b+2}` is an extra minimiser, i.e.
`val(b+i) > V` for `i = 1, 2`.

We work in the box-interior / Lemma-T regime `a = 2P + b + 2` with `P ≥ 0` (equivalently
`a ≥ b + 2`); this is exactly the regime in which the `Δ` closed forms of §3 are derived and
Murnaghan–Nakayama-verified. The finitely many shapes with `a = b` (i.e. `P = −1`, outside this
regime) are the small-shape casework of the interior note, not the boundary lemma proper. Note that
`a = 2P + b + 2 ≡ b (mod 2)`, so the same-parity condition `a ≡ b` is automatic.

Writing `Δ(b+i) := val(b+i) − val(0)`, §3 gives the two MN-verified closed forms

> `Δ(b+2) = (b+6) + 2 s₂(P) − 2 s₂(a+2) − 2 v₂(a)`,
> `Δ(b+1) = (b+3) + 2 s₂(P+1) − 2 s₂(a+2) + 2 v₂(W₁) − 2 v₂(a)`,  `W₁ = a(b+2) − b(b+1)`,

where `s₂ n = (Nat.digits 2 n).sum`. These rest on the Murnaghan–Nakayama closed forms for `M_0`
(hook), `M_{b+2}` (Lemma T) and `M_{b+1}` (`= (b−1)W₁/2`) — symmetric-function facts out of
Mathlib's reach (the factor `v₂(a−b+1) = 0` of Lemma T is folded in, as `a−b+1 = 2P+3` is odd).
Consistent
with every prior session, they are therefore taken as the **hypotheses** `hΔ2`, `hΔ1`. Everything
downstream — the genuine 2-adic number theory — is proved here from scratch.

## The number-theoretic content (proved, not assumed)

* `TworowD4Kernel.vz_factorial` — Legendre at `p = 2`: `v₂(n!) = n − s₂(n)`.
* `TworowD4Kernel.factorial_mul_prod_Icc` — `P! · ∏_{t=1}^{Q}(P+t) = (P+Q)!`.
* `TworowD4Kernel.vz_prod_Icc` — the **bridge** `v₂(∏_{t=1}^{Q}(P+t)) = Q + s₂(P) − s₂(P+Q)`.
* `TworowD4Kernel.vz_dvd_le` — valuation monotonicity under divisibility.
* `TworowD4Kernel.threerow_c2_boundary_top` — the top index `Δ(b+2) ≥ 2`.
* `TworowD4Kernel.threerow_c2_boundary_sub` — the subtop index `Δ(b+1) ≥ 1`.
* `TworowD4Kernel.threerow_c2_boundary` — the assembled end-to-end statement: `V < valb1` and
  `V < valb2`.

## References

`2026-06-15-boundary-lemma-threerow.md`, §3 (`c = 2`, COMPLETE); the `c = 1` companion
`TworowD4Kernel.threerow_c1_boundary`; the factor-in-product engine `TworowD4Kernel.lemma_F`.
-/

namespace TworowD4Kernel

open Nat Finset

/-- **Legendre's theorem at `p = 2`** in `ℤ`-form: `v₂(n!) = n − s₂(n)`, where
`s₂ n = (Nat.digits 2 n).sum`. Direct from Mathlib's `sub_one_mul_padicValNat_factorial` (whose
`(p − 1)` factor is `1` at `p = 2`); the subtraction is honest because `s₂ n ≤ n`. -/
theorem vz_factorial (n : ℕ) : vz n ! = (n : ℤ) - ((Nat.digits 2 n).sum : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_factorial (p := 2) n
  have hle := Nat.digit_sum_le 2 n
  rw [show (2 : ℕ) - 1 = 1 by norm_num, one_mul] at h
  simp only [vz, h]
  omega

/-- The ascending-factorial / factorial identity `P! · ∏_{t=1}^{Q}(P+t) = (P+Q)!`. Proved by
induction on `Q`: the inductive step peels the top factor `P + (Q+1)` via `Finset.prod_Icc_succ_top`
and folds it into the factorial via `Nat.factorial_succ`. -/
theorem factorial_mul_prod_Icc (P : ℕ) :
    ∀ Q, P ! * ∏ t ∈ Finset.Icc 1 Q, (P + t) = (P + Q)! := by
  intro Q
  induction Q with
  | zero => simp
  | succ Q ih =>
    rw [Finset.prod_Icc_succ_top (show (1 : ℕ) ≤ Q + 1 by omega), ← mul_assoc, ih,
      show P + (Q + 1) = (P + Q) + 1 by ring, Nat.factorial_succ]
    ring

/-- **The bridge.** `v₂(∏_{t=1}^{Q}(P+t)) = Q + s₂(P) − s₂(P+Q)`.

The product of `Q` consecutive integers above `P` is `(P+Q)!/P!`; applying Legendre `vz_factorial`
to both factorials, the `Q` linear terms `Q − [s₂(P+Q) − s₂(P)]` survive. This is the form in which
the carry-sum `carries(P,Q)` plus `v₂(Q!)` of §3 enters every `a`-even boundary case. -/
theorem vz_prod_Icc (P Q : ℕ) :
    vz (∏ t ∈ Finset.Icc 1 Q, (P + t))
      = (Q : ℤ) + ((Nat.digits 2 P).sum : ℤ) - ((Nat.digits 2 (P + Q)).sum : ℤ) := by
  have hPne : P ! ≠ 0 := Nat.factorial_ne_zero P
  have hprodne : (∏ t ∈ Finset.Icc 1 Q, (P + t)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    have := (Finset.mem_Icc.mp ht).1
    omega
  have hsum : vz (P !) + vz (∏ t ∈ Finset.Icc 1 Q, (P + t)) = vz ((P + Q)!) := by
    rw [← vz_mul hPne hprodne, factorial_mul_prod_Icc P Q]
  rw [vz_factorial P, vz_factorial (P + Q)] at hsum
  push_cast at hsum ⊢
  linarith

/-- **Valuation monotonicity under divisibility.** If `x ∣ y` with `x, y ≠ 0` then
`v₂(x) ≤ v₂(y)`: the power `2^{v₂ x}` divides `x`, hence `y`. -/
theorem vz_dvd_le {x y : ℕ} (hy : y ≠ 0) (h : x ∣ y) : vz x ≤ vz y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd : (2 : ℕ) ^ padicValNat 2 x ∣ y := (pow_padicValNat_dvd).trans h
  have hle := (padicValNat_dvd_iff_le hy).mp hd
  simp only [vz]
  exact_mod_cast hle

/-- **`c = 2` boundary, top index `j = b+2`.** In the Lemma-T regime `a = 2P+b+2`, `b ≥ 3`, the
MN-verified closed form forces `Δ(b+2) ≥ 2`, hence `val(b+2) > val(0) = V`.

*Proof (§3.1).* If `a` is odd (`b` odd) then `v₂(a) = 0`, and subadditivity `s₂(a+2) ≤ s₂(P) +
s₂(b+4)` with Lemma A `2 s₂(b+4) ≤ b+3` (`b+4` odd `≥ 7`) give `Δ ≥ (b+6) − (b+3) = 3`. If `a` is
even (`b = 2β`, `β ≥ 2`), set `Q := β+2 ≥ 4`; then `a = 2(P+β+1)`, `a+2 = 2(P+β+2)`, and the bridge
collapses `Δ(b+2) = 2[v₂(∏_{t=1}^{Q}(P+t)) − v₂(P+β+1)]`, where `P+β+1` is the `t = β+1` factor, so
Lemma F (`Q ≥ 4`) gives `Δ ≥ 2`. -/
theorem threerow_c2_boundary_top {a b P : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 2) (hb : 3 ≤ b)
    (hΔ : Δ = (b : ℤ) + 6 + 2 * ((Nat.digits 2 P).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) - 2 * vz a) :
    2 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · -- `b = 2β` even ⟹ `a` even; the factor-in-product (Lemma F) case.
    have hb2 : b = 2 * β := by omega
    have hβ2 : 2 ≤ β := by omega
    have ha2eq : a + 2 = 2 * (P + β + 2) := by omega
    have haeq : a = 2 * (P + β + 1) := by omega
    -- `s₂(a+2) = s₂(P+β+2)` and `v₂(a) = 1 + v₂(P+β+1)`.
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 2)).sum := by
      rw [ha2eq, sum_digits_two_mul]
    have hva : vz a = 1 + vz (P + β + 1) := by
      rw [haeq, vz_mul (by norm_num) (by omega), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    -- the bridge at `Q = β + 2`, and Lemma F deleting the `t = β+1` factor `P+β+1`.
    have hbridge := vz_prod_Icc P (β + 2)
    rw [show P + (β + 2) = P + β + 2 by omega] at hbridge
    have hmem : (β + 1) ∈ Finset.Icc 1 (β + 2) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hF := lemma_F (R := P) (Q := β + 2) (t₀ := β + 1) (by omega) hmem
    have hFz : vz (P + β + 1) + 1 ≤ vz (∏ t ∈ Finset.Icc 1 (β + 2), (P + t)) := by
      rw [show P + β + 1 = P + (β + 1) by omega]
      simp only [vz]
      exact_mod_cast hF
    have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva]
    push_cast
    linarith
  · -- `b = 2β+1` odd ⟹ `a` odd; subadditivity + Lemma A (digit-sum envelope).
    have haodd : ¬ (2 ∣ a) := by omega
    have hva0 : vz a = 0 := by simp [vz, padicValNat.eq_zero_of_not_dvd haodd]
    -- subadditivity `s₂(a+2) ≤ s₂(P) + s₂(b+4)` (`a+2 = 2P + (b+4)`).
    have hsub : (Nat.digits 2 (a + 2)).sum
        ≤ (Nat.digits 2 P).sum + (Nat.digits 2 (b + 4)).sum := by
      have h := sum_digits_two_add_le (2 * P + (b + 4)) (2 * P) (b + 4) rfl
      rw [sum_digits_two_mul, show 2 * P + (b + 4) = a + 2 by omega] at h
      exact h
    -- Lemma A on `b+4` (odd `≥ 7`): `2 s₂(b+4) ≤ b+3`.
    have hLemA : 2 * (Nat.digits 2 (b + 4)).sum ≤ b + 3 := by
      have := two_mul_sum_digits_le (b + 4) (by omega); omega
    rw [hΔ, hva0]
    have hsubz : ((Nat.digits 2 (a + 2)).sum : ℤ)
        ≤ ((Nat.digits 2 P).sum : ℤ) + ((Nat.digits 2 (b + 4)).sum : ℤ) := by exact_mod_cast hsub
    have hLemAz : 2 * ((Nat.digits 2 (b + 4)).sum : ℤ) ≤ (b : ℤ) + 3 := by exact_mod_cast hLemA
    linarith

/-- **`c = 2` boundary, subtop index `j = b+1`.** In the Lemma-T regime `a = 2P+b+2`, `b ≥ 3`, with
`W₁ = a(b+2) − b(b+1)`, the MN-verified closed form forces `Δ(b+1) ≥ 1`, hence `val(b+1) > V`.

*Proof (§3.2).* If `a` is odd then `v₂(a) = 0`, `v₂(W₁) ≥ 0`, and subadditivity `s₂(a+2) ≤ s₂(P+1) +
s₂(b+2)` with Lemma A `2 s₂(b+2) ≤ b+1` (`b+2` odd `≥ 5`) give `Δ ≥ (b+3) − (b+1) = 2`. If `a` is
even (`b = 2β`, `β ≥ 2`), set `X := P+1`; then `W₁ = 2(2(β+1)X + β)` and the bridge (`Q = β+1`)
collapses `Δ(b+1) = 1 + 2[v₂(∏_{t=1}^{β+1}(X+t)) − v₂(X+β)] + 2 v₂(2(β+1)X+β)`; the bracket is `≥ 0`
because `X+β` is the `t = β` factor of the product, so `Δ ≥ 1`. -/
theorem threerow_c2_boundary_sub {a b P W₁ : ℕ} (Δ : ℤ) (hP : a = 2 * P + b + 2) (hb : 3 ≤ b)
    (hW : W₁ = a * (b + 2) - b * (b + 1))
    (hΔ : Δ = (b : ℤ) + 3 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz W₁ - 2 * vz a) :
    1 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.even_or_odd b with ⟨β, hβ⟩ | ⟨β, hβ⟩
  · -- `b = 2β` even ⟹ `a` even; the factor-divides-product case.
    have hb2 : b = 2 * β := by omega
    have hβ2 : 2 ≤ β := by omega
    have ha2eq : a + 2 = 2 * (P + β + 2) := by omega
    have haeq : a = 2 * (P + β + 1) := by omega
    have hsa2 : (Nat.digits 2 (a + 2)).sum = (Nat.digits 2 (P + β + 2)).sum := by
      rw [ha2eq, sum_digits_two_mul]
    have hva : vz a = 1 + vz (P + β + 1) := by
      rw [haeq, vz_mul (by norm_num) (by omega), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    -- the closed form `W₁ = 2(2(β+1)(P+1) + β)`, and its valuation `1 + v₂(2(β+1)(P+1)+β)`.
    have key : a * (b + 2) = 2 * (2 * (β + 1) * (P + 1) + β) + b * (b + 1) := by
      rw [hP, hb2]; ring
    have hWeq : W₁ = 2 * (2 * (β + 1) * (P + 1) + β) := by
      rw [hW, key, Nat.add_sub_cancel]
    have hvW : vz W₁ = 1 + vz (2 * (β + 1) * (P + 1) + β) := by
      rw [hWeq, vz_mul (by norm_num) (by positivity), vz]
      norm_num [padicValNat.self (show 1 < 2 by norm_num)]
    have hvWnn : 0 ≤ vz (2 * (β + 1) * (P + 1) + β) := by
      simp only [vz]; exact Int.natCast_nonneg _
    -- the bridge at `Q = β+1`, `R = X = P+1`; `X+β` is the `t = β` factor of the product.
    have hbridge := vz_prod_Icc (P + 1) (β + 1)
    rw [show (P + 1) + (β + 1) = P + β + 2 by omega] at hbridge
    have hprodne : (∏ t ∈ Finset.Icc 1 (β + 1), ((P + 1) + t)) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr ?_
      intro t ht
      omega
    have hdvd : ((P + 1) + β) ∣ ∏ t ∈ Finset.Icc 1 (β + 1), ((P + 1) + t) :=
      Finset.dvd_prod_of_mem (fun t => (P + 1) + t) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    have hdvdle := vz_dvd_le hprodne hdvd
    rw [show (P + 1) + β = P + β + 1 by omega] at hdvdle
    have hb2z : (b : ℤ) = 2 * (β : ℤ) := by exact_mod_cast hb2
    push_cast at hbridge
    rw [hΔ, hsa2, hva, hvW]
    push_cast
    linarith
  · -- `b = 2β+1` odd ⟹ `a` odd; subadditivity + Lemma A.
    have haodd : ¬ (2 ∣ a) := by omega
    have hva0 : vz a = 0 := by simp [vz, padicValNat.eq_zero_of_not_dvd haodd]
    have hvWnn : 0 ≤ vz W₁ := by simp only [vz]; exact Int.natCast_nonneg _
    -- subadditivity `s₂(a+2) ≤ s₂(P+1) + s₂(b+2)` (`a+2 = 2(P+1) + (b+2)`).
    have hsub : (Nat.digits 2 (a + 2)).sum
        ≤ (Nat.digits 2 (P + 1)).sum + (Nat.digits 2 (b + 2)).sum := by
      have h := sum_digits_two_add_le (2 * (P + 1) + (b + 2)) (2 * (P + 1)) (b + 2) rfl
      rw [sum_digits_two_mul, show 2 * (P + 1) + (b + 2) = a + 2 by omega] at h
      exact h
    -- Lemma A on `b+2` (odd `≥ 5`): `2 s₂(b+2) ≤ b+1`.
    have hLemA : 2 * (Nat.digits 2 (b + 2)).sum ≤ b + 1 := by
      have := two_mul_sum_digits_le (b + 2) (by omega); omega
    rw [hΔ, hva0]
    have hsubz : ((Nat.digits 2 (a + 2)).sum : ℤ)
        ≤ ((Nat.digits 2 (P + 1)).sum : ℤ) + ((Nat.digits 2 (b + 2)).sum : ℤ) := by
      exact_mod_cast hsub
    have hLemAz : 2 * ((Nat.digits 2 (b + 2)).sum : ℤ) ≤ (b : ℤ) + 1 := by exact_mod_cast hLemA
    linarith

/-- **The three-row `c = 2` boundary lemma (assembled, end-to-end).**

Let `λ = (a, b, 2)` in the Lemma-T regime `a = 2P + b + 2`, `b ≥ 3`, and let `val0, valb1, valb2` be
the graded valuations `val(0), val(b+1), val(b+2)` with the MN-verified §3 differences. With the
threshold `V = val0` (`θ = 0`, since `j₀ = 0` for `c = 2`), both boundary values strictly exceed the
threshold:

> `V < valb1`  and  `V < valb2`.

This closes the boundary residual (Gap 3) of the three-row `c = 2` even-`|J*|` theorem: neither
boundary index is an extra minimiser, so `J*` is exactly the interior 2-adic box `{0, 2, 4}` and
`|J*|` is even on every tie. The only inputs beyond pure 2-adic number theory are the closed forms
`hΔ2`, `hΔ1`, MN-verified facts about the symmetric-function object `G_λ`. -/
theorem threerow_c2_boundary {a b P W₁ : ℕ} (val0 valb1 valb2 V : ℤ) (hP : a = 2 * P + b + 2)
    (hb : 3 ≤ b) (hW : W₁ = a * (b + 2) - b * (b + 1))
    (hΔ2 : valb2 - val0 = (b : ℤ) + 6 + 2 * ((Nat.digits 2 P).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) - 2 * vz a)
    (hΔ1 : valb1 - val0 = (b : ℤ) + 3 + 2 * ((Nat.digits 2 (P + 1)).sum : ℤ)
      - 2 * ((Nat.digits 2 (a + 2)).sum : ℤ) + 2 * vz W₁ - 2 * vz a)
    (hV : V = val0) :
    V < valb1 ∧ V < valb2 := by
  have htop := threerow_c2_boundary_top (valb2 - val0) hP hb hΔ2
  have hsub := threerow_c2_boundary_sub (valb1 - val0) hP hb hW hΔ1
  omega

end TworowD4Kernel
