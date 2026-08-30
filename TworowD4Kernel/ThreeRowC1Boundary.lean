/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.HookKummerLemmas
import TworowD4Kernel.SubsetIdentityGeneralC
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The three-row `c = 1` boundary lemma, end-to-end (`d = 4`)

This file assembles the **boundary lemma** for the three-row tie family `λ = (a, b, 1)` into a
single `sorry`-free declaration, closing the last residual of the `c = 1` interior theorem
(`~/projects/proofs/2026-06-13-threerow-c1-Jstar-even.md`, §6) via the closed argument of
`~/projects/proofs/2026-06-15-boundary-lemma-threerow.md`, §2.

## What is proved here, and what is assumed

For `λ = (a, b, 1) ⊢ 2m` the relevant graded valuations are `val(j) = j + 2 v₂(G_j)` with
`G_j = ⟨s_λ, e₂^j h₁^{2(m−j)}⟩`. The interior theorem pins the minimiser set `J*` to an interior
2-adic box and leaves **one** residual: that the single boundary index `j = b+1` is *not* an extra
minimiser, i.e. `val(b+1) > V` where `V = val(0) − θ`, `θ ∈ {0, 3}` (`θ = 0` when `a` is even,
`θ = 3` when `a` is odd — the forced descent `val(3) = val(0) − 3`).

Writing `Δ := val(b+1) − val(0)`, **Proposition 1** of §2 is the MN-verified closed form

> `Δ = (b − 3) + 2 v₂(a + 2) + 2 (s₂(m − b) − s₂(a))`,

where `s₂ n = (Nat.digits 2 n).sum` is the binary digit sum. This closed form rests on the
Murnaghan–Nakayama closed forms for `M_0 = f^λ` (the hook formula) and `M_{b+1} = b`, which are
symmetric-function facts out of Mathlib's reach; consistent with every prior session in this
project, it is therefore taken as the **hypothesis** `hΔ`. Everything downstream of it — the genuine
2-adic number theory — is proved here from scratch.

## The number-theoretic content (proved, not assumed)

* `TworowD4Kernel.two_mul_sum_digits_le` — **Lemma A**, the digit-sum envelope
  `2 s₂(k) ≤ k − 1` for `k ≥ 4` (strong induction on the binary representation). This is the
  engine that closes the `c = 1` boundary, *not* Lemma F: §2 of the boundary note uses the digit-sum
  envelope, while Lemma F drives the `c = 2, 3` boundaries.
* `TworowD4Kernel.sum_digits_two_add_le` — subadditivity `s₂(x + y) ≤ s₂(x) + s₂(y)`, which supplies
  the Kummer bound `s₂(a) ≤ s₂(b−1) + s₂(m−b)` (i.e. the carry count `γ ≥ 0`).
* `TworowD4Kernel.threerow_c1_boundary_aeven` — the `a`-even closure: `Δ ≥ 2`.
* `TworowD4Kernel.threerow_c1_boundary_aodd` — the `a`-odd closure: `Δ ≥ −1`.
* `TworowD4Kernel.threerow_c1_boundary` — the assembled end-to-end statement: under the
  closed form `hΔ` and `V = val(0) − θ`, the boundary value strictly exceeds the threshold,
  `V < val(b+1)`.

## References

`2026-06-15-boundary-lemma-threerow.md`, §2 (`c = 1`, COMPLETE);
`2026-06-13-threerow-c1-Jstar-even.md` (the interior theorem this completes).
-/

namespace TworowD4Kernel

open Nat

/-- **Lemma A (digit-sum envelope).** `2 s₂(k) ≤ k − 1` for every `k ≥ 4`, where
`s₂ k = (Nat.digits 2 k).sum`.

This is the load-bearing 2-adic fact of the `c = 1` boundary closure (§2): on the residual range
`b ≥ 5` it bounds `2 s₂(b−1) ≤ b − 2`, which (with `γ ≥ 0` and `v₂(a+2) ≥ 1`) forces `Δ ≥ 1`, hence
`Δ ≥ 2` by parity.

*Proof.* Strong induction on the binary digits. For `k ∈ {4,5,6,7}` the bound is a finite check. For
`k = 2u` even, `s₂(k) = s₂(u)` and the inductive bound `2 s₂(u) ≤ u − 1 ≤ 2u − 1`. For `k = 2u + 1`
odd, `s₂(k) = s₂(u) + 1` and `2 s₂(k) = 2 s₂(u) + 2 ≤ u + 1 ≤ 2u`. -/
theorem two_mul_sum_digits_le : ∀ k : ℕ, 4 ≤ k → 2 * (Nat.digits 2 k).sum ≤ k - 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.even_or_odd k with ⟨u, hu⟩ | ⟨u, hu⟩
    · -- `k = u + u = 2u`, `u ≥ 2`
      have hk2 : k = 2 * u := by omega
      by_cases hu4 : 4 ≤ u
      · have hih := ih u (by omega) hu4
        rw [hk2, sum_digits_two_mul]; omega
      · have hu2 : 2 ≤ u := by omega
        interval_cases u <;> rw [hk2] <;> decide
    · -- `k = 2u + 1`, `u ≥ 2`
      have hk2 : k = 2 * u + 1 := by omega
      by_cases hu4 : 4 ≤ u
      · have hih := ih u (by omega) hu4
        rw [hk2, sum_digits_two_mul_add_one]; omega
      · have hu2 : 2 ≤ u := by omega
        interval_cases u <;> rw [hk2] <;> decide

/-- **Digit-sum subadditivity.** `s₂(x + y) ≤ s₂(x) + s₂(y)`.

Equivalently, the number of carries when adding `x + y` in base `2` is non-negative — this is the
`γ ≥ 0` of the boundary note. Used to bound `s₂(a) ≤ s₂(b−1) + s₂(m−b)` for `a = (b−1) + 2(m−b)`.

*Proof.* Strong induction on `x + y`, splitting both arguments by parity. The all-even and
mixed-parity cases recurse directly; the both-odd case `x = 2x'+1, y = 2y'+1` has
`x + y = 2(x'+y'+1)`, and bounds `s₂(x'+y'+1) ≤ s₂(x'+y') + 1` (the `+1` instance of the lemma) and
`s₂(x'+y') ≤ s₂(x') + s₂(y')`, both via the inductive hypothesis at smaller sums. -/
theorem sum_digits_two_add_le : ∀ (s x y : ℕ), x + y = s →
    (Nat.digits 2 (x + y)).sum ≤ (Nat.digits 2 x).sum + (Nat.digits 2 y).sum := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro x y hxy
    have hs1 : (Nat.digits 2 1).sum = 1 := by decide
    rcases Nat.eq_zero_or_pos x with hx0 | hxpos
    · subst hx0; simp
    rcases Nat.eq_zero_or_pos y with hy0 | hypos
    · subst hy0; simp
    rcases Nat.even_or_odd x with ⟨x', hx'⟩ | ⟨x', hx'⟩ <;>
      rcases Nat.even_or_odd y with ⟨y', hy'⟩ | ⟨y', hy'⟩
    · -- both even
      have eL : (Nat.digits 2 (x + y)).sum = (Nat.digits 2 (x' + y')).sum := by
        rw [show x + y = 2 * (x' + y') by omega, sum_digits_two_mul]
      have eX : (Nat.digits 2 x).sum = (Nat.digits 2 x').sum := by
        rw [show x = 2 * x' by omega, sum_digits_two_mul]
      have eY : (Nat.digits 2 y).sum = (Nat.digits 2 y').sum := by
        rw [show y = 2 * y' by omega, sum_digits_two_mul]
      rw [eL, eX, eY]; exact ih (x' + y') (by omega) x' y' rfl
    · -- `x` even, `y` odd
      have eL : (Nat.digits 2 (x + y)).sum = (Nat.digits 2 (x' + y')).sum + 1 := by
        rw [show x + y = 2 * (x' + y') + 1 by omega, sum_digits_two_mul_add_one]
      have eX : (Nat.digits 2 x).sum = (Nat.digits 2 x').sum := by
        rw [show x = 2 * x' by omega, sum_digits_two_mul]
      have eY : (Nat.digits 2 y).sum = (Nat.digits 2 y').sum + 1 := by
        rw [show y = 2 * y' + 1 by omega, sum_digits_two_mul_add_one]
      have := ih (x' + y') (by omega) x' y' rfl
      rw [eL, eX, eY]; omega
    · -- `x` odd, `y` even
      have eL : (Nat.digits 2 (x + y)).sum = (Nat.digits 2 (x' + y')).sum + 1 := by
        rw [show x + y = 2 * (x' + y') + 1 by omega, sum_digits_two_mul_add_one]
      have eX : (Nat.digits 2 x).sum = (Nat.digits 2 x').sum + 1 := by
        rw [show x = 2 * x' + 1 by omega, sum_digits_two_mul_add_one]
      have eY : (Nat.digits 2 y).sum = (Nat.digits 2 y').sum := by
        rw [show y = 2 * y' by omega, sum_digits_two_mul]
      have := ih (x' + y') (by omega) x' y' rfl
      rw [eL, eX, eY]; omega
    · -- both odd
      have eL : (Nat.digits 2 (x + y)).sum = (Nat.digits 2 (x' + y' + 1)).sum := by
        rw [show x + y = 2 * (x' + y' + 1) by omega, sum_digits_two_mul]
      have eX : (Nat.digits 2 x).sum = (Nat.digits 2 x').sum + 1 := by
        rw [show x = 2 * x' + 1 by omega, sum_digits_two_mul_add_one]
      have eY : (Nat.digits 2 y).sum = (Nat.digits 2 y').sum + 1 := by
        rw [show y = 2 * y' + 1 by omega, sum_digits_two_mul_add_one]
      have h1 := ih (x' + y' + 1) (by omega) (x' + y') 1 rfl
      have h2 := ih (x' + y') (by omega) x' y' rfl
      rw [hs1] at h1
      rw [eL, eX, eY]; omega

/-- The Kummer bound `s₂(a) ≤ s₂(b−1) + s₂(m−b)` specialised to the `c = 1` relation
`a = (b−1) + 2(m−b)` (i.e. `a + b + 1 = 2m`). This packages the carry count `γ ≥ 0`. -/
private theorem sum_digits_a_le {a b m : ℕ} (hsum : a + b + 1 = 2 * m) (hab : b ≤ a) (hb : 1 ≤ b) :
    (Nat.digits 2 a).sum ≤ (Nat.digits 2 (b - 1)).sum + (Nat.digits 2 (m - b)).sum := by
  have hbm : b ≤ m := by omega
  have hsplit : a = (b - 1) + 2 * (m - b) := by omega
  have h := sum_digits_two_add_le a (b - 1) (2 * (m - b)) hsplit.symm
  rw [sum_digits_two_mul, ← hsplit] at h
  exact h

/-- **The `c = 1` boundary lemma, `a` even.** For `λ = (a, b, 1) ⊢ 2m` with `a` even and `b ≥ 3`
(the residual range; `b ∈ {1}` is the boundary-tie family of the interior note), the Proposition-1
closed form forces `Δ(b+1) ≥ 2`, hence `val(b+1) > val(0) = V` (here `θ = 0`).

*Proof (§2).* `a` even gives `v₂(a+2) ≥ 1` and `b` odd, so `Δ` is even. For `b ≥ 5` Lemma A bounds
`2 s₂(b−1) ≤ b − 2`, and with `s₂(a) ≤ s₂(b−1) + s₂(m−b)` we get `Δ ≥ (b−3) + 2 − (b−2) = 1`, hence
`≥ 2` by parity. For `b = 3`: if `m` is odd then `4 ∣ a+2` so `v₂(a+2) ≥ 2` and `Δ ≥ 2`; if `m` is
even then `s₂(a) ≤ s₂(m−3)` (the predecessor bound `s₂(k) ≤ s₂(k−1)+1`), so `Δ ≥ 2 v₂(a+2) ≥ 2`. -/
theorem threerow_c1_boundary_aeven {a b m : ℕ} (Δ : ℤ) (hsum : a + b + 1 = 2 * m) (hab : b ≤ a)
    (ha : Even a) (hb : 3 ≤ b)
    (hΔ : Δ = ((b : ℤ) - 3) + 2 * (padicValNat 2 (a + 2) : ℤ)
      + 2 * (((Nat.digits 2 (m - b)).sum : ℤ) - ((Nat.digits 2 a).sum : ℤ))) :
    2 ≤ Δ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ka, hka⟩ := ha
  have hbodd : b % 2 = 1 := by omega
  have hsub := sum_digits_a_le hsum hab (by omega)
  -- `v₂(a + 2) ≥ 1` since `a` is even.
  have ha2ne : a + 2 ≠ 0 := by omega
  have hv1 : 1 ≤ padicValNat 2 (a + 2) :=
    (padicValNat_dvd_iff_le ha2ne).mp (by rw [pow_one]; exact ⟨ka + 1, by omega⟩)
  rcases Nat.lt_or_ge b 5 with hb5 | hb5
  · -- `b = 3` (the only odd `b` with `3 ≤ b < 5`); `a = 4km − 4` (`m` even) or `4km − 2` (`m` odd).
    have hb3 : b = 3 := by omega
    subst hb3
    have hs2 : (Nat.digits 2 (3 - 1)).sum = 1 := by decide
    rcases Nat.even_or_odd m with ⟨km, hkm⟩ | ⟨km, hkm⟩
    · -- `m` even: `s₂(a) ≤ s₂(m − 3)` via the predecessor bound `s₂(km−1) ≤ s₂(km−2) + 1`.
      have hk2 : 2 ≤ km := by omega
      -- `a = 4(km−1) = 2·(2(km−1))`, so `s₂(a) = s₂(km − 1)`; `m − 3 = 2(km−2)+1`.
      have ea : (Nat.digits 2 a).sum = (Nat.digits 2 (km - 1)).sum := by
        rw [show a = 2 * (2 * (km - 1)) by omega, sum_digits_two_mul, sum_digits_two_mul]
      have em3 : (Nat.digits 2 (m - 3)).sum = (Nat.digits 2 (km - 2)).sum + 1 := by
        rw [show m - 3 = 2 * (km - 2) + 1 by omega, sum_digits_two_mul_add_one]
      have hsucc := sum_digits_two_add_le (km - 1) (km - 2) 1 (by omega)
      have hs1 : (Nat.digits 2 1).sum = 1 := by decide
      rw [hs1, show km - 2 + 1 = km - 1 by omega] at hsucc
      have hkey : (Nat.digits 2 a).sum ≤ (Nat.digits 2 (m - 3)).sum := by
        rw [ea, em3]; omega
      rw [hΔ]; omega
    · -- `m` odd: `4 ∣ a + 2`, so `v₂(a + 2) ≥ 2`.
      have hv2 : 2 ≤ padicValNat 2 (a + 2) := by
        refine (padicValNat_dvd_iff_le ha2ne).mp ?_
        rw [show (2 : ℕ) ^ 2 = 4 from by norm_num]
        exact ⟨km, by omega⟩
      rw [hs2] at hsub
      rw [hΔ]; omega
  · -- `b ≥ 5`: Lemma A gives `2 s₂(b − 1) ≤ b − 2`.
    have hLemA : 2 * (Nat.digits 2 (b - 1)).sum ≤ b - 2 := by
      have := two_mul_sum_digits_le (b - 1) (by omega); omega
    rw [hΔ]; omega

/-- **The `c = 1` boundary lemma, `a` odd.** For `λ = (a, b, 1) ⊢ 2m` with `a` odd and `b ≥ 6`
(the residual range; `b ∈ {2, 4}` are the boundary-tie families of the interior note), the
Proposition-1 closed form forces `Δ(b+1) ≥ −1`, hence `val(b+1) > val(0) − 3 = V` (here `θ = 3`).

*Proof (§2).* `a` odd gives `b` even, so `Δ` is odd, and `v₂(a + 2) ≥ 0`. Since `b ≥ 6`, `b − 1` is
odd `≥ 5`, so Lemma A bounds `2 s₂(b−1) ≤ b − 2`; with `s₂(a) ≤ s₂(b−1) + s₂(m−b)` this gives
`Δ ≥ (b − 3) − (b − 2) = −1`. -/
theorem threerow_c1_boundary_aodd {a b m : ℕ} (Δ : ℤ) (hsum : a + b + 1 = 2 * m) (hab : b ≤ a)
    (ha : Odd a) (hb : 6 ≤ b)
    (hΔ : Δ = ((b : ℤ) - 3) + 2 * (padicValNat 2 (a + 2) : ℤ)
      + 2 * (((Nat.digits 2 (m - b)).sum : ℤ) - ((Nat.digits 2 a).sum : ℤ))) :
    -1 ≤ Δ := by
  have hbeven : b % 2 = 0 := by
    obtain ⟨ka, hka⟩ := ha; omega
  have hsub := sum_digits_a_le hsum hab (by omega)
  have hLemA : 2 * (Nat.digits 2 (b - 1)).sum ≤ b - 2 := by
    have := two_mul_sum_digits_le (b - 1) (by omega); omega
  rw [hΔ]; omega

/-- **The three-row `c = 1` boundary lemma (assembled, end-to-end).**

Let `λ = (a, b, 1) ⊢ 2m` and let `val0, valb1` be the graded valuations `val(0), val(b+1)` with the
MN-verified Proposition-1 difference `valb1 − val0 = (b−3) + 2 v₂(a+2) + 2(s₂(m−b) − s₂(a))`. With
the threshold `V = val0 − θ` (`θ = 0` for `a` even on the residual range `b ≥ 3`; `θ = 3` for `a`
odd on `b ≥ 6`), the boundary value strictly exceeds the threshold:

> `V < valb1`.

This closes Gap 3 (the boundary residual) of the three-row `c = 1` even-`|J*|` theorem: no boundary
index is an extra minimiser, so `J*` is exactly the interior 2-adic box and `|J*|` is even on every
tie. The only inputs beyond pure 2-adic number theory are the closed form `hΔ` and the threshold
`hcase`, both MN-verified facts about the symmetric-function object `G_λ`. -/
theorem threerow_c1_boundary {a b m : ℕ} (val0 valb1 V : ℤ) (hsum : a + b + 1 = 2 * m)
    (hab : b ≤ a)
    (hΔ : valb1 - val0 = ((b : ℤ) - 3) + 2 * (padicValNat 2 (a + 2) : ℤ)
      + 2 * (((Nat.digits 2 (m - b)).sum : ℤ) - ((Nat.digits 2 a).sum : ℤ)))
    (hcase : (Even a ∧ 3 ≤ b ∧ V = val0) ∨ (Odd a ∧ 6 ≤ b ∧ V = val0 - 3)) :
    V < valb1 := by
  rcases hcase with ⟨ha, hb, hV⟩ | ⟨ha, hb, hV⟩
  · have := threerow_c1_boundary_aeven (valb1 - val0) hsum hab ha hb hΔ
    omega
  · have := threerow_c1_boundary_aodd (valb1 - val0) hsum hab ha hb hΔ
    omega

end TworowD4Kernel
