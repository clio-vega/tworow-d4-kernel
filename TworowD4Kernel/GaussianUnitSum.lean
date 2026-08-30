/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Data.ZMod.Basic

/-!
# The arithmetic heart of the leading-π dichotomy: `Σ` of `|J*|` Gaussian units `≡ |J*| (mod 1+i)`

This file formalises the self-contained Gaussian-integer arithmetic at the core of **Theorem A**
of the leading-π-coefficient dichotomy for the `d = 4` fiber `G_λ(i)`
(`~/projects/proofs/2026-06-11-leading-pi-coefficient-dichotomy.md`). That theorem writes the
leading `π`-adic coefficient of `G_λ(i)` as
`C = Σ_{j ∈ J*} u_j · i^{j − a_j}`, a sum of `|J*|` **units** of `ℤ[i]` (each `±1, ±i`), and
observes that, because `i ≡ 1 (mod 1+i)`, every unit is `≡ 1 (mod 1+i)`, whence
`C ≡ |J*| (mod 1+i)`. Consequently `|J*|` odd `⟹ (1+i) ∤ C ⟹ C ≠ 0 ⟹ G_λ(i) ≠ 0`. This one line
prunes ~72% of general-`λ` `d = 4` shapes.

Everything is reduced to the ring homomorphism `φ : ℤ[i] → ZMod 2` realising the isomorphism
`ℤ[i]/(1+i) ≅ 𝔽₂` — built here via `Zsqrtd.lift` by sending `√(-1) = i ↦ 1`.

## Main results

* `TworowD4Kernel.GaussianUnitSum.pi_dvd_iff` — the kernel characterisation `(1+i) ∣ z ↔ φ z = 0`,
  i.e. `ℤ[i]/(1+i) ≅ 𝔽₂`. This is the workhorse.
* `TworowD4Kernel.GaussianUnitSum.pi_dvd_i_sub_one` — the crux `i ≡ 1 (mod 1+i)`
  (paper: `i − 1 = (1+i)·i`).
* `TworowD4Kernel.GaussianUnitSum.phi_unit` — every Gaussian unit reduces to `1 (mod 1+i)`.
* `TworowD4Kernel.GaussianUnitSum.sum_units_sub_card` — statement (3): for any multiset of units
  `us`, `(1+i) ∣ (Σ us − |us|)`, i.e. `Σ u ≡ |J*| (mod 1+i)`.
* `TworowD4Kernel.GaussianUnitSum.not_dvd_of_odd` — statement (4): if `S ≡ n (mod 1+i)` and `n` is
  odd then `(1+i) ∤ S`.
* `TworowD4Kernel.GaussianUnitSum.odd_card_not_dvd_sum` — the dichotomy heart: an odd number of
  Gaussian units never sums to a multiple of `1+i`; hence (with `S = C`) `C ≠ 0`.

## References

`2026-06-11-leading-pi-coefficient-dichotomy.md`, Theorem A and Corollary A1 (the 72% pruning).
-/

namespace TworowD4Kernel.GaussianUnitSum

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-- `π = 1 + i`, the prime of `ℤ[i]` above `2` (`π² = 2i`, `N(π) = 2`). -/
abbrev pi : ℤ[i] := ⟨1, 1⟩

/-- The reduction `φ : ℤ[i] → ZMod 2` realising `ℤ[i]/(1+i) ≅ 𝔽₂`, defined by `i ↦ 1`
(so `⟨a, b⟩ ↦ a + b`). Well-defined because `1 · 1 = -1` in `ZMod 2`. -/
def phi : ℤ[i] →+* ZMod 2 := Zsqrtd.lift ⟨(1 : ZMod 2), by decide⟩

@[simp]
theorem phi_apply (z : ℤ[i]) : phi z = (z.re : ZMod 2) + (z.im : ZMod 2) * 1 := rfl

@[simp]
theorem phi_pi : phi pi = 0 := by decide

/-- The crux, `i ≡ 1 (mod 1+i)`: indeed `i − 1 = (1+i)·i`. -/
theorem pi_dvd_i_sub_one : pi ∣ ((⟨0, 1⟩ : ℤ[i]) - 1) := ⟨⟨0, 1⟩, by decide⟩

/-- **Kernel characterisation `ℤ[i]/(1+i) ≅ 𝔽₂`.** `(1+i) ∣ z ↔ φ z = 0`.

`(⟹)` is immediate from `φ π = 0`; `(⟸)` exhibits the quotient witness
`z = (1+i)·⟨k, k − z.re⟩` where `2k = z.re + z.im`. -/
theorem pi_dvd_iff (z : ℤ[i]) : pi ∣ z ↔ phi z = 0 := by
  constructor
  · rintro ⟨w, rfl⟩
    rw [map_mul, phi_pi, zero_mul]
  · intro hz
    -- `φ z = 0` says `z.re + z.im` is even.
    have h2 : (2 : ℤ) ∣ (z.re + z.im) := by
      have : ((z.re + z.im : ℤ) : ZMod 2) = 0 := by
        rw [phi_apply, mul_one] at hz; push_cast; exact hz
      rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    obtain ⟨k, hk⟩ := h2
    refine ⟨⟨k, k - z.re⟩, ?_⟩
    apply Zsqrtd.ext
    · change z.re = 1 * k + (-1) * 1 * (k - z.re)
      ring
    · change z.im = 1 * (k - z.re) + 1 * k
      omega

/-- **Every Gaussian unit reduces to `1 (mod 1+i)`** — i.e. `φ u = 1` for `u ∈ {±1, ±i}`.
A unit has `u.re² + u.im² = 1`, and in `ZMod 2` one has `a² = a`, so
`φ u = u.re + u.im = u.re² + u.im² = 1`. -/
theorem phi_unit {u : ℤ[i]} (hu : IsUnit u) : phi u = 1 := by
  have hnorm : u.re * u.re + u.im * u.im = 1 := by
    have h := (Zsqrtd.norm_eq_one_iff' (by norm_num) u).2 hu
    rw [Zsqrtd.norm_def] at h; linarith
  have hcast : (u.re : ZMod 2) * u.re + (u.im : ZMod 2) * u.im = 1 := by
    have := congrArg (fun x : ℤ => (x : ZMod 2)) hnorm
    push_cast at this; exact this
  have sq : ∀ a : ZMod 2, a * a = a := by decide
  rw [phi_apply, mul_one, ← sq (u.re : ZMod 2), ← sq (u.im : ZMod 2), hcast]

/-- **Statement (3): `Σ u ≡ |J*| (mod 1+i)`.** For any multiset `us` of Gaussian *units*,
`(1+i) ∣ (Σ us − |us|)`. This is `C ≡ |J*| (mod π)` of Theorem A. -/
theorem sum_units_sub_card (us : Multiset ℤ[i]) (h : ∀ u ∈ us, IsUnit u) :
    pi ∣ (us.sum - (Multiset.card us : ℤ[i])) := by
  rw [pi_dvd_iff]
  have h1 : phi us.sum = (Multiset.card us : ZMod 2) := by
    rw [map_multiset_sum, Multiset.map_congr rfl (fun u hu => phi_unit (h u hu))]
    simp [Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul]
  rw [map_sub, h1, map_natCast, sub_self]

/-- **Statement (4): the odd-`|J*|` obstruction.** If `S ≡ n (mod 1+i)` and `n` is odd, then
`(1+i) ∤ S`. (With `S = C`, `n = |J*|`: an odd-`|J*|` leading coefficient is a `π`-adic unit,
so nonzero.) -/
theorem not_dvd_of_odd {S : ℤ[i]} {n : ℕ} (hn : Odd n) (hSn : pi ∣ (S - (n : ℤ[i]))) :
    ¬ pi ∣ S := by
  intro hS
  have hdvd : pi ∣ ((n : ℤ[i])) := by
    have := dvd_sub hS hSn
    rwa [sub_sub_cancel] at this
  rw [pi_dvd_iff, map_natCast, ZMod.natCast_eq_zero_iff_even] at hdvd
  exact (Nat.not_even_iff_odd.2 hn) hdvd

/-- **The dichotomy heart.** A multiset of Gaussian units whose cardinality is *odd* never sums to a
multiple of `1+i`. Applied to `C = Σ_{j ∈ J*} u_j i^{j − a_j}` with `|J*|` odd, this gives
`(1+i) ∤ C`, hence `C ≠ 0`, hence `G_λ(i) ≠ 0` — settling ~72% of `d = 4` shapes (Corollary A1). -/
theorem odd_card_not_dvd_sum (us : Multiset ℤ[i]) (h : ∀ u ∈ us, IsUnit u)
    (hodd : Odd (Multiset.card us)) : ¬ pi ∣ us.sum :=
  not_dvd_of_odd hodd (sum_units_sub_card us h)

/-- **The dichotomy conclusion `C ≠ 0`.** A sum of an *odd* number of Gaussian units is nonzero,
because `(1+i) ∣ 0` while `(1+i) ∤ C`. With `C = Σ_{j ∈ J*} u_j i^{j − a_j}` and `|J*|` odd this is
exactly the final step `C ≠ 0 ⟹ G_λ(i) ≠ 0` of Theorem A. -/
theorem odd_card_sum_ne_zero (us : Multiset ℤ[i]) (h : ∀ u ∈ us, IsUnit u)
    (hodd : Odd (Multiset.card us)) : us.sum ≠ 0 := by
  intro h0
  refine odd_card_not_dvd_sum us h hodd ?_
  rw [h0]
  exact dvd_zero pi

end TworowD4Kernel.GaussianUnitSum
