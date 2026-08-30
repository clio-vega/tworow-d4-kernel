/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.D0ClosedForms
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Basic

/-!
# The Compensation Lemma `C` of the three-row `c = 1` even-`|J*|` closure (`d = 4`)

This file formalises the load-bearing 2-adic inequality of §4 of the **three-row `c = 1` family
closure** (`~/projects/proofs/2026-06-13-threerow-c1-Jstar-even.md`, "Lemma C"). It is the
three-row replacement for the two-row `a ≡ b (mod 2)` parity trick: the genuinely new arithmetic
that controls the *quadratic-in-`j` valuation* `v₂(b(a+1) − j(j−1))` arising in the `c = 1`
Proposition 2 collapse (the concrete face of the `e₂ mod 2` wall).

## The lemma

For naturals `a, b` and `1 ≤ j ≤ a + 1`, writing `v₂ = padicValNat 2`,

> `v₂(C(a+2, j)) + v₂(b(a+1) − j(j−1)) ≥ v₂(a+1)`,

where the middle valuation is the 2-adic valuation **over `ℤ`** (`padicValInt 2`), since the
quadratic `b(a+1) − j(j−1)` can be any sign.

### The honest hypothesis `D ≠ 0`

The paper states Lemma C "for all `a, b` and all `1 ≤ j`", and its proof uses a *strict-min rule*
that silently assumes the integer `D := b(a+1) − j(j−1)` is nonzero. With the Mathlib/standard
convention `padicValInt 2 0 = 0`, the bare statement is in fact **false** at the `D = 0` corner
(smallest witness `(a,b,j) = (3,3,4)`: `v₂(C(5,4)) + v₂(0) = 0 < 2 = v₂(4)`). In the actual
application the index range is `1 ≤ j ≤ b − 1` with `a ≥ b ≥ 1`, which forces
`b(a+1) ≥ b(b+1) > (b−1)(b−2) ≥ j(j−1)`, hence `D > 0` — so the corner never occurs there. We
therefore state the lemma with the explicit, sufficient hypothesis `D ≠ 0`, which is exactly the
assumption the informal proof relies on, is strictly more general than the `j ≤ b − 1` range, and
was numerically confirmed to give zero counterexamples over `a ≤ 400`, all `b`, `1 ≤ j ≤ a + 1`.

## Main results

* `TworowD4Kernel.vz_choose_ge` — the reusable helper `v₂(C(n,k)) ≥ v₂(n) − v₂(k)` (for
  `1 ≤ k ≤ n`), the `vz` image of the absorption identity `n · C(n−1,k−1) = C(n,k) · k`. (Wanted
  again for the `c ≥ 2` families.)

* `TworowD4Kernel.compensation_lemma_C` — **Lemma C**: for `1 ≤ j ≤ a + 1` and
  `D := b(a+1) − j(j−1) ≠ 0`,
  `v₂(a+1) ≤ v₂(C(a+2, j)) + padicValInt 2 D`.

## Proof outline (faithful to §4)

Let `A = v₂(a+1)`, `N = b(a+1)`, `Q = j(j−1)`, `e = v₂(Q)`, `D = N − Q`. Note `2^A ∣ a+1 ∣ N`
unconditionally. Case split on `2^A ∣ Q`:

* If `2^A ∣ Q`: then `2^A ∣ N − Q = D`; with `D ≠ 0`, `A ≤ padicValInt 2 D`, and
  `v₂(C(a+2,j)) ≥ 0` closes it. (This covers `Q = 0` and `e ≥ A`.)
* If `2^A ∤ Q`: then `Q ≠ 0` (so `j ≥ 2`) and `e < A`. The absorption identity
  `(a+2)·C(a+1,j−1) = C(a+2,j)·j` together with `vz_choose_ge` at `(a+1, j−1)` gives
  `v₂(C(a+2,j)) ≥ A − e`; and `2^e ∣ N`, `2^e ∣ Q` give `2^e ∣ D`, so `e ≤ padicValInt 2 D`. The
  two combine to `≥ (A − e) + e = A`.

## References

`2026-06-13-threerow-c1-Jstar-even.md`, §4 (Lemma C, "the compensation lemma") and §3
(Proposition 2, where the quadratic-valuation term `v₂(b(a+1) − j(j−1)) − v₂(a+1)` is isolated).
-/

namespace TworowD4Kernel

open Nat

/-- **The standard binomial valuation bound** `v₂(C(n,k)) ≥ v₂(n) − v₂(k)` for `1 ≤ k ≤ n`,
stated over `ℤ` via `vz`.

This is the `vz` image of the absorption identity `n · C(n−1, k−1) = C(n,k) · k`
(`Nat.add_one_mul_choose_eq`): taking valuations gives
`v₂(n) + v₂(C(n−1,k−1)) = v₂(C(n,k)) + v₂(k)`, and `v₂(C(n−1,k−1)) ≥ 0` yields the bound. It is the
reusable arithmetic lever behind both the compensation lemma here and (anticipated) the `c ≥ 2`
families. -/
theorem vz_choose_ge {n k : ℕ} (hk : 1 ≤ k) (hkn : k ≤ n) :
    vz n - vz k ≤ vz (n.choose k) := by
  have hn : n ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  have hck : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  have hc1 : (n - 1).choose (k - 1) ≠ 0 := (Nat.choose_pos (by omega : k - 1 ≤ n - 1)).ne'
  -- absorption `n · C(n-1, k-1) = C(n, k) · k`
  have habs : n * (n - 1).choose (k - 1) = n.choose k * k := by
    have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
    rwa [show n - 1 + 1 = n by omega, show k - 1 + 1 = k by omega] at h
  have hval : vz n + vz ((n - 1).choose (k - 1)) = vz (n.choose k) + vz k := by
    rw [← vz_mul hn hc1, ← vz_mul hck hk0, habs]
  have hnn : (0 : ℤ) ≤ vz ((n - 1).choose (k - 1)) := by
    simp only [vz]; exact Int.natCast_nonneg _
  linarith

/-- **Lemma C — the compensation lemma** (`2026-06-13-threerow-c1-Jstar-even.md`, §4).

For naturals `a, b` and `1 ≤ j ≤ a + 1`, if the integer `D := b(a+1) − j(j−1)` is nonzero, then

> `v₂(a+1) ≤ v₂(C(a+2, j)) + padicValInt 2 D`.

The quadratic-valuation term `padicValInt 2 (b(a+1) − j(j−1))`, added to `v₂(C(a+2,j))`, always
pays back `v₂(a+1)` — this is what tames the `e₂ mod 2` wall and forces `|J*|` even on the `c = 1`
ties. The hypothesis `D ≠ 0` is the strict-min assumption of the informal proof; see the module
docstring for why the `D = 0` corner is a genuine (convention-driven) exclusion rather than a true
counterexample. -/
theorem compensation_lemma_C (a b j : ℕ) (hj1 : 1 ≤ j) (hja : j ≤ a + 1)
    (hD : ((b * (a + 1) : ℕ) : ℤ) - ((j * (j - 1) : ℕ) : ℤ) ≠ 0) :
    padicValNat 2 (a + 1) ≤
      padicValNat 2 ((a + 2).choose j)
        + padicValInt 2 (((b * (a + 1) : ℕ) : ℤ) - ((j * (j - 1) : ℕ) : ℤ)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := padicValNat 2 (a + 1) with hAdef
  set N := b * (a + 1) with hNdef
  set Q := j * (j - 1) with hQdef
  set e := padicValNat 2 Q with hedef
  set D : ℤ := (N : ℤ) - (Q : ℤ) with hDdef
  -- `2^A ∣ N` unconditionally, via `2^A ∣ a + 1 ∣ N`.
  have hdvdN_nat : 2 ^ A ∣ N := by
    have h1 : 2 ^ A ∣ (a + 1) := pow_padicValNat_dvd
    rw [hNdef]; exact h1.trans (dvd_mul_left (a + 1) b)
  have hdvdN : (2 : ℤ) ^ A ∣ (N : ℤ) := by exact_mod_cast hdvdN_nat
  by_cases hcase : 2 ^ A ∣ Q
  · -- `2^A ∣ Q` ⟹ `2^A ∣ D` ⟹ `A ≤ padicValInt 2 D`.
    have hdvdQ : (2 : ℤ) ^ A ∣ (Q : ℤ) := by exact_mod_cast hcase
    have hdvdD : (2 : ℤ) ^ A ∣ D := by rw [hDdef]; exact dvd_sub hdvdN hdvdQ
    have hAle : A ≤ padicValInt 2 D := by
      rcases (padicValInt_dvd_iff (p := 2) A D).mp (by exact_mod_cast hdvdD) with h | h
      · exact absurd h hD
      · exact h
    omega
  · -- `2^A ∤ Q` ⟹ `Q ≠ 0` and `e < A`.
    have hQ0 : Q ≠ 0 := by rintro h; exact hcase (h ▸ dvd_zero _)
    have heA : e < A := by
      by_contra h
      exact hcase ((padicValNat_dvd_iff_le hQ0).mpr (by omega))
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with h | h
      · have hj1' : j = 1 := by omega
        rw [hQdef, hj1'] at hQ0
        simp at hQ0
      · exact h
    -- `2^e ∣ N` and `2^e ∣ Q`, hence `2^e ∣ D` and `e ≤ padicValInt 2 D`.
    have hdvdNe : (2 : ℤ) ^ e ∣ (N : ℤ) := by
      have : (2 : ℕ) ^ e ∣ N := (pow_dvd_pow 2 heA.le).trans hdvdN_nat
      exact_mod_cast this
    have hdvdQe : (2 : ℤ) ^ e ∣ (Q : ℤ) := by
      have : (2 : ℕ) ^ e ∣ Q := hedef ▸ pow_padicValNat_dvd
      exact_mod_cast this
    have hdvdDe : (2 : ℤ) ^ e ∣ D := by rw [hDdef]; exact dvd_sub hdvdNe hdvdQe
    have hele : e ≤ padicValInt 2 D := by
      rcases (padicValInt_dvd_iff (p := 2) e D).mp (by exact_mod_cast hdvdDe) with h | h
      · exact absurd h hD
      · exact h
    -- `v₂(C(a+2,j)) ≥ A − e` via the absorption `(a+2)·C(a+1,j−1) = C(a+2,j)·j`.
    have hjm1 : j - 1 ≠ 0 := by omega
    have hca2 : ((a + 2).choose j) ≠ 0 := (Nat.choose_pos (by omega : j ≤ a + 2)).ne'
    have hca1 : ((a + 1).choose (j - 1)) ≠ 0 := (Nat.choose_pos (by omega : j - 1 ≤ a + 1)).ne'
    have habs : (a + 2) * (a + 1).choose (j - 1) = (a + 2).choose j * j := by
      have h := Nat.add_one_mul_choose_eq (a + 1) (j - 1)
      rwa [show a + 1 + 1 = a + 2 by omega, show j - 1 + 1 = j by omega] at h
    have hval : vz (a + 2) + vz ((a + 1).choose (j - 1)) = vz ((a + 2).choose j) + vz j := by
      rw [← vz_mul (by omega) hca1, ← vz_mul hca2 (by omega), habs]
    -- `e = v₂(j) + v₂(j−1)`.
    have he_split : (e : ℤ) = vz j + vz (j - 1) := by
      have hmul : Q = j * (j - 1) := hQdef
      simp only [hedef, vz, hmul, padicValNat.mul (by omega : j ≠ 0) hjm1, Nat.cast_add]
    have hcge := vz_choose_ge (n := a + 1) (k := j - 1) (by omega) (by omega)
    have hva2 : (0 : ℤ) ≤ vz (a + 2) := by simp only [vz]; exact Int.natCast_nonneg _
    -- assemble `vz (C(a+2,j)) ≥ A − e`
    have hCge : (A : ℤ) - (e : ℤ) ≤ vz ((a + 2).choose j) := by
      have hAval : vz (a + 1) = (A : ℤ) := by simp only [hAdef, vz]
      rw [he_split, ← hAval]
      linarith
    have hCcast : vz ((a + 2).choose j) = (padicValNat 2 ((a + 2).choose j) : ℤ) := by
      simp only [vz]
    rw [hCcast] at hCge
    have heleZ : (e : ℤ) ≤ (padicValInt 2 D : ℤ) := by exact_mod_cast hele
    have : (A : ℤ) ≤ (padicValNat 2 ((a + 2).choose j) : ℤ) + (padicValInt 2 D : ℤ) := by
      linarith
    exact_mod_cast this

end TworowD4Kernel
