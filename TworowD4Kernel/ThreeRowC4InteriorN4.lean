/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# The c = 4 interior Number Lemma N4: `16 ∣ H` (`d = 4`)

This file machine-checks **Lemma N4**, the keystone of the three-row `(a, b, 4)` *interior*
theorem (`~/projects/proofs/2026-06-19-c4-interior-number-lemma.md`). It is the multiplicative-side
rigid floor `β'(4) = 4` made concrete: the sextic heavy quotient `H(a, b, j)` of the structural
decomposition `Q₄(j) = (a − 2)(b − 3) H(j) + P₈(j)` carries the **constant** 2-adic floor
`v₂ H ≥ 4`, i.e. `16 ∣ H`, on the tie lattice `a ≡ b (mod 2)`.

The informal proof observes that `H` is an integer polynomial, so `H mod 16` depends only on
`(a, b, j) mod 16`, reducing the claim to a finite residue check over the `16 · 8 · 16 = 2048`
admissible triples with `a ≡ b (mod 2)` (parity is preserved mod 16). Here that check is discharged
by `decide` over `ZMod 16`, and the parity hypothesis is transported through the ring hom
`ZMod 16 →+* ZMod 2`.

## Main results

* `TworowD4Kernel.Hpoly` — the sextic heavy quotient `H(a, b, j)` over an arbitrary commutative
  ring, transcribed byte-for-byte from `~/projects/code/threerow-c4/c4N4.py` (`Hval`) and
  cross-checked numerically (`H(10,8,8) = 347088`, `H(7,7,0) = 1306800`).
* `TworowD4Kernel.N4_residue_key` — the finite residue check: `Hpoly x y j = 0` in `ZMod 16`
  whenever `x, y` have equal image in `ZMod 2`. Proved by `decide` (2048 admissible triples).
* `TworowD4Kernel.N4` — **Lemma N4**: for integers `a ≡ b (mod 2)` and any `j`,
  `16 ∣ H(a, b, j)`.

## Sharpness

The floor `4` is exact: `v₂ H(10,8,8) = v₂(347088) = 4`, so `32 ∤ H` in general. See
`c4N4.py` for the sharpness check and the two auxiliary `j ∈ {8,10}` residue checks
(`2¹² ∣ Π₈`, `2¹⁴ ∣ Π₁₀`) that complete Case B of the interior proof.

## References

* Informal proof: `~/projects/proofs/2026-06-19-c4-interior-number-lemma.md`, §1 (Lemma N4).
* Residue check + polynomial `Hval`: `~/projects/code/threerow-c4/c4N4.py`.
-/

namespace TworowD4Kernel

/-- **The sextic heavy quotient `H(a, b, j)`** of the c = 4 structural decomposition
`Q₄(j) = (a − 2)(b − 3) H(j) + P₈(j)`, over an arbitrary commutative ring.

Transcribed byte-for-byte from `Hval` in `~/projects/code/threerow-c4/c4N4.py`. Numerically
cross-checked: `H(10,8,8) = 347088`, `H(7,7,0) = 1306800`, `H(3,5,2) = 105840`,
`H(13,4,9) = 1728`. -/
def Hpoly {R : Type*} [CommRing R] (a b j : R) : R :=
  a^3*b^3 + 9*a^3*b^2 + 26*a^3*b + 24*a^3 + 12*a^2*b^3 - 4*a^2*b^2*j^2
  - 8*a^2*b^2*j + 108*a^2*b^2 - 12*a^2*b*j^2 - 48*a^2*b*j + 312*a^2*b
  - 8*a^2*j^2 - 64*a^2*j + 288*a^2 + 47*a*b^3 - 20*a*b^2*j^2 - 64*a*b^2*j
  + 423*a*b^2 + 6*a*b*j^4 - 12*a*b*j^3 - 30*a*b*j^2 - 384*a*b*j + 1222*a*b
  + 24*a*j^3 - 40*a*j^2 - 488*a*j + 1128*a + 60*b^3 - 24*b^2*j^2 - 120*b^2*j
  + 540*b^2 + 6*b*j^4 + 12*b*j^3 - 42*b*j^2 - 696*b*j + 1560*b - 4*j^6
  + 48*j^5 - 244*j^4 + 648*j^3 - 664*j^2 - 648*j + 1440

/-- The reduction `ZMod 16 →+* ZMod 2`; two residues have equal image iff they agree mod 2. -/
abbrev parZMod : ZMod 16 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

/-- **The finite residue check behind Lemma N4.** In `ZMod 16`, `H(x, y, j) = 0` for every triple
`(x, y, j)` with `parZMod x = parZMod y` (i.e. `x ≡ y (mod 2)`). This is the exhaustive check of the
`16 · 8 · 16 = 2048` admissible residue triples from `c4N4.py`, discharged by the kernel. -/
theorem N4_residue_key :
    ∀ x y j : ZMod 16, parZMod x = parZMod y → Hpoly x y j = 0 := by decide

/-- **Lemma N4 (c = 4 interior Number Lemma).** For integers `a ≡ b (mod 2)` and any `j`, the sextic
heavy quotient `H(a, b, j)` is divisible by `16` — the constant 2-adic floor `v₂ H ≥ 4` that closes
the §6 residual of the three-row `(a, b, 4)` interior theorem.

Reference: `~/projects/proofs/2026-06-19-c4-interior-number-lemma.md`, §1. -/
theorem N4 (a b j : ℤ) (h : a % 2 = b % 2) : (16 : ℤ) ∣ Hpoly a b j := by
  -- Push the cast through the polynomial: `↑(H a b j) = H ↑a ↑b ↑j` in `ZMod 16`.
  have hcast : ((Hpoly a b j : ℤ) : ZMod 16)
      = Hpoly (a : ZMod 16) (b : ZMod 16) (j : ZMod 16) := by
    simp only [Hpoly]; push_cast; ring
  -- `16 ∣ H ↔ ↑H = 0` in `ZMod 16`; apply the residue check with the transported parity.
  have hdvd : ((16 : ℕ) : ℤ) ∣ Hpoly a b j := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast]
    apply N4_residue_key
    -- `parZMod ∘ Int.cast = Int.cast`, so parity reduces to `(a : ZMod 2) = (b : ZMod 2)`.
    rw [map_intCast, map_intCast, ZMod.intCast_eq_intCast_iff]
    exact h
  simpa using hdvd

end TworowD4Kernel
