/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.Hensel
import TworowD4Kernel.Fp2Irreducible

/-!
# `X² + X + 1` has no root in the `2`-adic integers

This file lifts the finite-field facts of `Fp2Irreducible.lean` to the `2`-adic conclusion they
were built for, in the proof of the **unique 2-adic root** result for the two-row `d = 4` law in
the residue classes `b ≡ 2, 3 (mod 4)`
(`~/projects/proofs/2026-06-09-tworow-d4-b23-2adic-single-candidate`).

Modulo `2`, the reduced model factors as `Q_b ≡ m · (m² + m + 1)^{⌊(b-1)/4⌋}`. The non-special
roots of `Q_b` are roots of `X² + X + 1`, which is irreducible over `𝔽₂`; hence they reduce into
`𝔽₄ ∖ 𝔽₂` and **cannot be `2`-adic integers**. That is precisely the statement proved here, and it
is what makes the lifted root `ρ_b` *unique* and forces the valuation `v₂(m − θ) = 0` for every
integer `m` (Lemma A, `2026-06-11-tworow-d4-b23-valuation-concentration`).

## Main results

* `TworowD4Kernel.no_padic_root_sq_add_self_add_one`: for every `r : ℤ_[2]`, `r² + r + 1 ≠ 0`.
  Proof: apply the reduction ring hom `PadicInt.toZMod : ℤ_[2] →+* ZMod 2` to a hypothetical root.
  It sends `r² + r + 1` to `(toZMod r)² + (toZMod r) + 1` in `ZMod 2`, which by
  `sq_add_self_add_one_ne_zero` is never `0`. So `r² + r + 1` cannot be `0` either. This is the
  *non-existence* half of the unique-root result (no non-special root is a `2`-adic integer).

* `TworowD4Kernel.hensel_unique_root_of_simple_root_mod_two`: an integer polynomial whose mod-`2`
  reduction has `0` as a *simple* root (`‖F.aeval 0‖ < 1`, `‖F.derivative.aeval 0‖ = 1`) has a
  unique root in the maximal ideal `2ℤ₂ = {z : ‖z‖ < 1}`. This is the *uniqueness* half — Hensel's
  lemma specialised to `a = 0` — and gives the unique lift `ρ_b` of the simple root `m ≡ 0`.

* `TworowD4Kernel.hensel_unique_root_reduced_model`: the concrete witness — the literal reduced
  model `X³ + X² + X = X · (X² + X + 1)` satisfies those hypotheses, so it has a unique root in
  `2ℤ₂` (which here is `0`). This shows the previous lemma is non-vacuous.

## References

The informal proof is `2026-06-09-tworow-d4-b23-2adic-single-candidate`; the finite-field input
`sq_add_self_add_one_ne_zero` lives in `Fp2Irreducible.lean`.
-/

namespace TworowD4Kernel

open Polynomial

/-- **The non-special roots of `Q_b` are not `2`-adic integers.**

`X² + X + 1` has no root in `ℤ_[2] = PadicInt 2`: any `2`-adic root `r` would reduce, under the
ring hom `PadicInt.toZMod : ℤ_[2] →+* ZMod 2`, to a root of `x² + x + 1` over the two-element
field, of which there are none (`sq_add_self_add_one_ne_zero`). This is the `2`-adic
non-existence behind the uniqueness of `ρ_b` and the valuation `v₂(m − θ) = 0`. -/
theorem no_padic_root_sq_add_self_add_one (r : ℤ_[2]) : r ^ 2 + r + 1 ≠ 0 := by
  intro h
  have hred : (PadicInt.toZMod r) ^ 2 + PadicInt.toZMod r + 1 = 0 := by
    have := congrArg (PadicInt.toZMod (p := 2)) h
    rwa [map_add, map_add, map_pow, map_one, map_zero] at this
  exact sq_add_self_add_one_ne_zero (PadicInt.toZMod r) hred

/-- **Hensel uniqueness of the lifted root `ρ_b`.**

Let `F` be an integer polynomial whose reduction mod `2` has `0` as a *simple* root: concretely,
its constant term lies in `2ℤ₂` (`‖F.aeval 0‖ < 1`, i.e. `F(0) ≡ 0 (mod 2)`) and its linear
coefficient is a `2`-adic unit (`‖F.derivative.aeval 0‖ = 1`, i.e. `F'(0) ≡ 1 (mod 2)`, the
non-vanishing-derivative / simple-root condition). Then `F` has a **unique** root `z` in the
maximal ideal `2ℤ₂ = {z : ‖z‖ < 1}` of the `2`-adic integers.

This is Hensel's lemma specialised to `a = 0`: with `‖F'.aeval 0‖ = 1` the Hensel hypothesis
`‖F.aeval 0‖ < ‖F'.aeval 0‖²` is exactly `‖F.aeval 0‖ < 1`, and the Hensel ball `‖z‖ < ‖F'.aeval 0‖`
is `‖z‖ < 1`. For the reduced model `Q̂_b ≡ X · (X² + X + 1) (mod 2)` the simple root `m ≡ 0` is
the one with non-vanishing derivative (`X ∤ X² + X + 1`, `not_X_dvd_X_sq_add_X_add_one`); this lemma
is the uniqueness of its `2`-adic lift `ρ_b`. -/
theorem hensel_unique_root_of_simple_root_mod_two {F : Polynomial ℤ}
    (h0 : ‖F.aeval (0 : ℤ_[2])‖ < 1) (h1 : ‖F.derivative.aeval (0 : ℤ_[2])‖ = 1) :
    ∃! z : ℤ_[2], F.aeval z = 0 ∧ ‖z‖ < 1 := by
  have hnorm : ‖F.aeval (0 : ℤ_[2])‖ < ‖F.derivative.aeval (0 : ℤ_[2])‖ ^ 2 := by
    rw [h1]; simpa using h0
  obtain ⟨z, hz, hzdist, _, huniq⟩ := hensels_lemma (p := 2) (F := F) (a := 0) hnorm
  rw [h1, sub_zero] at hzdist
  refine ⟨z, ⟨hz, hzdist⟩, ?_⟩
  rintro z' ⟨hz', hz'norm⟩
  exact huniq z' hz' (by rw [sub_zero, h1]; exact hz'norm)

/-- **Concrete witness: the reduced model `X³ + X² + X = X · (X² + X + 1)`.**

The hypotheses of `hensel_unique_root_of_simple_root_mod_two` are non-vacuous: the literal mod-`2`
shape `X³ + X² + X` of `Q_b` satisfies them — its constant term is `0` (so `‖aeval 0‖ = 0 < 1`)
and its linear coefficient is `1` (so `‖derivative.aeval 0‖ = 1`). Hence it has a unique root in
`2ℤ₂`, exhibiting the simple root `m ≡ 0` lifting uniquely to `ρ_b` (here the lift is `0` itself).
The non-vanishing derivative is the `2`-adic incarnation of `not_X_dvd_X_sq_add_X_add_one`. -/
theorem hensel_unique_root_reduced_model :
    ∃! z : ℤ_[2], (X ^ 3 + X ^ 2 + X : Polynomial ℤ).aeval z = 0 ∧ ‖z‖ < 1 :=
  hensel_unique_root_of_simple_root_mod_two
    (by simp) (by simp)

end TworowD4Kernel
