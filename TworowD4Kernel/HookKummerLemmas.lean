/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.D0ClosedForms
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Digits.Defs

/-!
# The Kummer carry lemmas `K` and `K′` of the hook tie closure (`d = 4`)

This file formalises the two load-bearing 2-adic inequalities of §3 of the **hook family closure**
(`~/projects/proofs/2026-06-12-hook-Jstar-even.md`), the first unconditional `d = 4` tie sub-case.
They are the arithmetic heart of `g(j) > 0` off the tie set `J* = {0, 2}`.

Throughout, `v₂ = padicValNat 2`, `s₂(n) = (Nat.digits 2 n).sum` is the binary digit sum, and
`C = Nat.choose`. Subtractions of valuations genuinely go negative, so the two main statements are
phrased over `ℤ` via the wrapper `vz n = (padicValNat 2 n : ℤ)` from `D0ClosedForms`.

## Main results

* `TworowD4Kernel.padicValNat_two_centralBinom` — the central-binomial valuation
  `v₂(C(2t, t)) = s₂(t)` (Kummer: the carries of `t + t` are the binary `1`s of `t`).

* `TworowD4Kernel.hook_v2_add_s2_le` — the helper `v₂(w) + s₂(w) ≤ w` (the `K′` closer).

* `TworowD4Kernel.hook_lemma_K` — **Lemma K** (even case): for `1 ≤ t`, `2t ≤ m`,
  `v₂(C(m−1, t)) − v₂(C(m, 2t)) ≤ s₂(t)`.

* `TworowD4Kernel.hook_lemma_K'` — **Lemma K′** (odd case): for `2s + 1 ≤ m`,
  `v₂(C(m−1, s)) − v₂(C(m, 2s+1)) ≤ s`.

## References

`2026-06-12-hook-Jstar-even.md`, §3 (Reduction of the hook tie to a Kummer inequality).
-/

namespace TworowD4Kernel

open Nat

/-- The binary digit sum is invariant under doubling: `s₂(2t) = s₂(t)`. The digit `0` prepended by
`Nat.digits_base_mul` contributes nothing to the sum. -/
theorem sum_digits_two_mul (t : ℕ) :
    (Nat.digits 2 (2 * t)).sum = (Nat.digits 2 t).sum := by
  rcases Nat.eq_zero_or_pos t with ht | ht
  · simp [ht]
  · rw [Nat.digits_base_mul (by norm_num) ht, List.sum_cons, Nat.zero_add]

/-- **The central-binomial 2-adic valuation.** `v₂(C(2t, t)) = s₂(t)`.

This is Kummer's theorem at `p = 2`: the number of carries when adding `t + t` in base `2` equals
the number of binary `1`s of `t`. Obtained from Mathlib's
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits` (whose `(p − 1)` factor is `1` at `p = 2`) and
the doubling identity `s₂(2t) = s₂(t)`. -/
theorem padicValNat_two_centralBinom (t : ℕ) :
    padicValNat 2 ((2 * t).choose t) = (Nat.digits 2 t).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := t) (n := 2 * t)
    (by omega)
  rw [show 2 * t - t = t by omega, sum_digits_two_mul] at h
  omega

/-- **The `K′` closer.** `v₂(w) + s₂(w) ≤ w` for every `w`.

Proved by strong induction: for `w` odd, `v₂(w) = 0` and `s₂(w) ≤ w`; for `w = 2u` even, the
inductive hypothesis at `u` gives `v₂(u) + 1 + s₂(u) ≤ u + 1 ≤ 2u`. The paper states it for `w ≥ 1`
(used at `w = s + 1`); the bound also holds vacuously at `w = 0`. -/
theorem hook_v2_add_s2_le (w : ℕ) :
    padicValNat 2 w + (Nat.digits 2 w).sum ≤ w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases Nat.even_or_odd w with ⟨u, hu⟩ | hodd
    · -- `w = u + u = 2u`
      rcases Nat.eq_zero_or_pos u with hu0 | hu0
      · simp [hu, hu0]
      · have hw2 : w = 2 * u := by omega
        have hlt : u < w := by omega
        have hv : padicValNat 2 w = padicValNat 2 u + 1 := by
          rw [hw2, padicValNat.mul (by norm_num) (by omega), padicValNat.self (by norm_num)]
          omega
        have hs : (Nat.digits 2 w).sum = (Nat.digits 2 u).sum := by
          rw [hw2, sum_digits_two_mul]
        have := ih u hlt
        omega
    · -- `w` odd: `v₂(w) = 0`
      have hv : padicValNat 2 w = 0 :=
        padicValNat.eq_zero_of_not_dvd (by rcases hodd with ⟨k, hk⟩; omega)
      have hs := Nat.digit_sum_le 2 w
      omega

/-- One direction of the ultrametric inequality at `p = 2`:
`min (v₂ a) (v₂ b) ≤ v₂ (a + b)` for `a, b ≠ 0`. The common power `2^min` divides both `a` and
`b`, hence their sum. -/
theorem min_padicValNat_two_le_add {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    min (padicValNat 2 a) (padicValNat 2 b) ≤ padicValNat 2 (a + b) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab : a + b ≠ 0 := by omega
  have hda : 2 ^ min (padicValNat 2 a) (padicValNat 2 b) ∣ a :=
    (padicValNat_dvd_iff_le ha).mpr (min_le_left _ _)
  have hdb : 2 ^ min (padicValNat 2 a) (padicValNat 2 b) ∣ b :=
    (padicValNat_dvd_iff_le hb).mpr (min_le_right _ _)
  exact (padicValNat_dvd_iff_le hab).mp (dvd_add hda hdb)

/-- **The bracket bound of Lemma K**: `v₂(m − t) ≤ v₂(m) + v₂(C(m − t, t))` for `1 ≤ t`, `2t ≤ m`.

This is the `≤ 0` half of the bracket `v₂(m−t) − v₂(m) − v₂(C(m−t,t))` in §3. If `v₂(m−t) ≤ v₂(m)`
the bound is immediate; otherwise the ultrametric forces `v₂(t) ≤ v₂(m)`, and the absorption
identity `(m−t)·C(m−t−1,t−1) = C(m−t,t)·t` gives `v₂(m−t) ≤ v₂(C(m−t,t)) + v₂(t) ≤ v₂(C(m−t,t)) +
v₂(m)`. -/
theorem hook_bracket {m t : ℕ} (ht : 1 ≤ t) (htm : 2 * t ≤ m) :
    padicValNat 2 (m - t) ≤ padicValNat 2 m + padicValNat 2 ((m - t).choose t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmt : m - t ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  have hmin : min (padicValNat 2 (m - t)) (padicValNat 2 t) ≤ padicValNat 2 m := by
    have h := min_padicValNat_two_le_add hmt ht0
    rwa [show (m - t) + t = m by omega] at h
  by_cases hcase : padicValNat 2 (m - t) ≤ padicValNat 2 m
  · omega
  · -- `v₂(m−t) > v₂(m)`, so `v₂(t) ≤ v₂(m)`
    have hvt : padicValNat 2 t ≤ padicValNat 2 m := by
      rcases le_total (padicValNat 2 (m - t)) (padicValNat 2 t) with hle | hle
      · rw [min_eq_left hle] at hmin; omega
      · rwa [min_eq_right hle] at hmin
    -- absorption `(m−t)·C(m−t−1,t−1) = C(m−t,t)·t`
    have habs : (m - t) * ((m - t - 1).choose (t - 1)) = ((m - t).choose t) * t := by
      have h := Nat.add_one_mul_choose_eq (m - t - 1) (t - 1)
      simp only [show m - t - 1 + 1 = m - t from by omega, show t - 1 + 1 = t from by omega] at h
      exact h
    have hc1 : (m - t - 1).choose (t - 1) ≠ 0 :=
      (Nat.choose_pos (by omega : t - 1 ≤ m - t - 1)).ne'
    have hval : padicValNat 2 (m - t) + padicValNat 2 ((m - t - 1).choose (t - 1))
        = padicValNat 2 ((m - t).choose t) + padicValNat 2 t := by
      rw [← padicValNat.mul hmt hc1,
        ← padicValNat.mul (Nat.choose_pos (by omega : t ≤ m - t)).ne' ht0, habs]
    omega

/-- The binary digit sum of an odd number: `s₂(2s + 1) = s₂(s) + 1`. The bit-`0` column is a `1`
that prepends to the digits of `s`. -/
theorem sum_digits_two_mul_add_one (s : ℕ) :
    (Nat.digits 2 (2 * s + 1)).sum = (Nat.digits 2 s).sum + 1 := by
  rw [Nat.digits_def' (b := 2) (by norm_num) (by omega),
    show (2 * s + 1) % 2 = 1 by omega, show (2 * s + 1) / 2 = s by omega, List.sum_cons]
  omega

/-- The binary digit sum of a positive number is at least `1` (its leading digit is nonzero). -/
theorem one_le_sum_digits_two {n : ℕ} (hn : n ≠ 0) : 1 ≤ (Nat.digits 2 n).sum := by
  have hnil : Nat.digits 2 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  have hpos : 0 < (Nat.digits 2 n).getLast hnil :=
    Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 2 hn)
  exact le_trans hpos (List.le_sum_of_mem (List.getLast_mem hnil))

/-- **The odd central-type valuation** (used in `K′`): `v₂(C(2s+1, s)) + 1 = s₂(s + 1)`.

Kummer at `p = 2`: the carries of `s + (s+1)` are the binary `1`s of `s + 1` minus one (the
no-carry bit-`0` column). Stated additively to avoid truncated `ℕ` subtraction. -/
theorem padicValNat_two_choose_two_succ (s : ℕ) :
    padicValNat 2 ((2 * s + 1).choose s) + 1 = (Nat.digits 2 (s + 1)).sum := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := 2) (k := s) (n := 2 * s + 1)
    (by omega)
  rw [show 2 * s + 1 - s = s + 1 by omega, sum_digits_two_mul_add_one] at h
  have hpos := one_le_sum_digits_two (n := s + 1) (by omega)
  omega

/-- The `ℤ`-form of `padicValNat_two_choose_two_succ`: `vz(C(2s+1, s)) = s₂(s + 1) − 1`. -/
theorem vz_choose_two_succ (s : ℕ) :
    vz ((2 * s + 1).choose s) = ((Nat.digits 2 (s + 1)).sum : ℤ) - 1 := by
  have h := padicValNat_two_choose_two_succ s
  simp only [vz]; omega

/-- **Lemma K (even case).** For `1 ≤ t` and `2t ≤ m`:
`v₂(C(m − 1, t)) − v₂(C(m, 2t)) ≤ s₂(t)`.

The two product identities `(m−1)·C(m−1,t) = (m−t)·C(m,t)` (`choose_mul_succ_eq`) and
`C(m,2t)·C(2t,t) = C(m,t)·C(m−t,t)` (`choose_mul`), combined with the central-binomial valuation
`v₂(C(2t,t)) = s₂(t)`, reduce the difference to `s₂(t) + [v₂(m−t) − v₂(m) − v₂(C(m−t,t))]`; the
bracket is `≤ 0` by `hook_bracket`. -/
theorem hook_lemma_K {m t : ℕ} (ht : 1 ≤ t) (htm : 2 * t ≤ m) :
    vz ((m - 1).choose t) - vz (m.choose (2 * t)) ≤ ((Nat.digits 2 t).sum : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : m ≠ 0 := by omega
  have hmt : m - t ≠ 0 := by omega
  have ht0 : t ≠ 0 := by omega
  have hcmt1 : (m - 1).choose t ≠ 0 := (Nat.choose_pos (by omega : t ≤ m - 1)).ne'
  have hcm : m.choose t ≠ 0 := (Nat.choose_pos (by omega : t ≤ m)).ne'
  have hcm2t : m.choose (2 * t) ≠ 0 := (Nat.choose_pos (by omega : 2 * t ≤ m)).ne'
  have hc2t : (2 * t).choose t ≠ 0 := (Nat.choose_pos (by omega : t ≤ 2 * t)).ne'
  have hcmtt : (m - t).choose t ≠ 0 := (Nat.choose_pos (by omega : t ≤ m - t)).ne'
  have hI1 : (m - 1).choose t * m = m.choose t * (m - t) := by
    have h := Nat.choose_mul_succ_eq (m - 1) t
    rwa [show m - 1 + 1 = m by omega] at h
  have e1 : vz ((m - 1).choose t) + vz m = vz (m.choose t) + vz (m - t) := by
    rw [← vz_mul hcmt1 hm, ← vz_mul hcm hmt, hI1]
  have hI2 : m.choose (2 * t) * (2 * t).choose t = m.choose t * ((m - t).choose t) := by
    have h := Nat.choose_mul (n := m) (k := 2 * t) (s := t) (by omega)
    rwa [show 2 * t - t = t by omega] at h
  have ecb : vz ((2 * t).choose t) = ((Nat.digits 2 t).sum : ℤ) := by
    rw [vz, padicValNat_two_centralBinom]
  have e2 : vz (m.choose (2 * t)) + ((Nat.digits 2 t).sum : ℤ)
      = vz (m.choose t) + vz ((m - t).choose t) := by
    rw [← ecb, ← vz_mul hcm2t hc2t, ← vz_mul hcm hcmtt, hI2]
  have hbr : vz (m - t) ≤ vz m + vz ((m - t).choose t) := by
    have h := hook_bracket ht htm
    simp only [vz]; exact_mod_cast h
  linarith

/-- **Lemma K′ (odd case).** For `2s + 1 ≤ m`:
`v₂(C(m − 1, s)) − v₂(C(m, 2s+1)) ≤ s`.

Same skeleton as `hook_lemma_K`: `(m−1)·C(m−1,s) = (m−s)·C(m,s)`, `C(m,2s+1)·C(2s+1,s) =
C(m,s)·C(m−s,s+1)`, the absorption `(m−s)·C(m−s−1,s) = C(m−s,s+1)·(s+1)`, and the odd valuation
`v₂(C(2s+1,s)) = s₂(s+1) − 1`. These collapse the difference to `≤ v₂(s+1) + s₂(s+1) − 1`, which is
`≤ s` by `hook_v2_add_s2_le` at `w = s + 1`. -/
theorem hook_lemma_K' {m s : ℕ} (hsm : 2 * s + 1 ≤ m) :
    vz ((m - 1).choose s) - vz (m.choose (2 * s + 1)) ≤ (s : ℤ) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm : m ≠ 0 := by omega
  have hms : m - s ≠ 0 := by omega
  have hs1 : (s + 1 : ℕ) ≠ 0 := by omega
  have hcms1 : (m - 1).choose s ≠ 0 := (Nat.choose_pos (by omega : s ≤ m - 1)).ne'
  have hcms : m.choose s ≠ 0 := (Nat.choose_pos (by omega : s ≤ m)).ne'
  have hcm2s1 : m.choose (2 * s + 1) ≠ 0 := (Nat.choose_pos (by omega : 2 * s + 1 ≤ m)).ne'
  have hc2s1 : (2 * s + 1).choose s ≠ 0 := (Nat.choose_pos (by omega : s ≤ 2 * s + 1)).ne'
  have hcmss1 : (m - s).choose (s + 1) ≠ 0 := (Nat.choose_pos (by omega : s + 1 ≤ m - s)).ne'
  have hcmss : (m - s - 1).choose s ≠ 0 := (Nat.choose_pos (by omega : s ≤ m - s - 1)).ne'
  have hI1 : (m - 1).choose s * m = m.choose s * (m - s) := by
    have h := Nat.choose_mul_succ_eq (m - 1) s
    rwa [show m - 1 + 1 = m by omega] at h
  have e1 : vz ((m - 1).choose s) + vz m = vz (m.choose s) + vz (m - s) := by
    rw [← vz_mul hcms1 hm, ← vz_mul hcms hms, hI1]
  have hI2 : m.choose (2 * s + 1) * (2 * s + 1).choose s
      = m.choose s * ((m - s).choose (s + 1)) := by
    have h := Nat.choose_mul (n := m) (k := 2 * s + 1) (s := s) (by omega)
    rwa [show 2 * s + 1 - s = s + 1 by omega] at h
  have e2 : vz (m.choose (2 * s + 1)) + vz ((2 * s + 1).choose s)
      = vz (m.choose s) + vz ((m - s).choose (s + 1)) := by
    rw [← vz_mul hcm2s1 hc2s1, ← vz_mul hcms hcmss1, hI2]
  have habs : (m - s) * ((m - s - 1).choose s) = ((m - s).choose (s + 1)) * (s + 1) := by
    have h := Nat.add_one_mul_choose_eq (m - s - 1) s
    simp only [show m - s - 1 + 1 = m - s from by omega] at h
    exact h
  have e3 : vz (m - s) + vz ((m - s - 1).choose s)
      = vz ((m - s).choose (s + 1)) + vz (s + 1) := by
    rw [← vz_mul hms hcmss, ← vz_mul hcmss1 hs1, habs]
  have ecb : vz ((2 * s + 1).choose s) = ((Nat.digits 2 (s + 1)).sum : ℤ) - 1 :=
    vz_choose_two_succ s
  have hhelpz : vz (s + 1) + ((Nat.digits 2 (s + 1)).sum : ℤ) ≤ (s : ℤ) + 1 := by
    have h := hook_v2_add_s2_le (s + 1)
    simp only [vz]; exact_mod_cast h
  have hvm : (0 : ℤ) ≤ vz m := by simp only [vz]; exact Int.natCast_nonneg _
  have hvc : (0 : ℤ) ≤ vz ((m - s - 1).choose s) := by simp only [vz]; exact Int.natCast_nonneg _
  linarith

end TworowD4Kernel
