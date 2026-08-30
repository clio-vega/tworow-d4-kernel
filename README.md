# tworow_d4_kernel

A Lean 4 / Mathlib formalisation of the **arithmetic kernel** of the two-row `d = 4`
fiber-vanishing law `G_{(2m−b,b)}(i) = 0 ⟺ (2,2)`. The full law is proved on paper for the
residue classes `b ≡ 0, 1 (mod 4)` by a 2-adic valuation argument; the generating-function
machinery it rests on is not in Mathlib, so this project machine-checks the self-contained
arithmetic lemmas — the valuation bookkeeping a skeptic would most want verified.

All declarations compile with **zero errors, zero warnings, no `sorry`**, and depend only on the
three standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Contents

* `TworowD4Kernel.lean` — the `b ≡ 1 (mod 4)` kernel (informal proof
  `2026-06-07-tworow-d4-b1mod4-proved.md`):
  * `descFactorial_eq_factorial_mul_self_mul_choose_pred` — `(m)_{R+1} = R! · (m · C(m−1, R))`,
    the integrality of `τ₁`.
  * `padicValNat_two_factorial_two_mul` — `v₂((2h)!) = h + v₂(h!)`, the 2-adic doubling identity.
* `TworowD4Kernel/B0modKernel.lean` — the `b ≡ 0 (mod 4)` kernel (informal proof
  `2026-06-08-tworow-d4-b0mod4-proved.md`):
  * `padicValNat_two_choose_eq` — `v₂(C(R, h)) = v₂((R)_h) − v₂(h!)`, the "`h` consecutive
    integers ÷ `h!`" engine behind the `D₀(j)` closed forms (§3).
  * `odd_add_three` and `odd_sum_of_odd_card` — the parity-counting primitive
    "an odd number of odds sums to an odd" that rescues the law when domination fails (§6).
* `TworowD4Kernel/D0ClosedForms.lean` — **Lemma 1 of §3** of the `b ≡ 0 (mod 4)` proof: the two
  closed forms for the `m`-independent offset `D₀(j) = h + v₂(R!) − v₂(j!) − v₂(β_j!)`
  (`h = ⌊j/2⌋`), assembled directly from the choose-factorisation and the doubling identity:
  * `D0_odd` — `j = 2h+1` (`β_j = R−h`): `D₀(j) = v₂(C(R, h))`.
  * `D0_even` — `j = 2h` (`β_j = R+1−h`): `D₀(j) = v₂(C(R, h−1)) − v₂(h)`.

  These lift the proved-on-paper closed forms (which drive the tie analysis of §5) from the
  kernel facts to the offset values that use them. Stated over `ℤ` because the even-case offset
  can be negative.
* `TworowD4Kernel/Fp2Irreducible.lean` — the two **finite-field inputs to Hensel uniqueness** for
  the `b ≡ 2, 3 (mod 4)` case (informal proof `2026-06-09-tworow-d4-b23-2adic-single-candidate`).
  Modulo `2`, `Q_b ≡ m · (m² + m + 1)^{⌊(b−1)/4⌋}`, and Hensel's lemma needs `m` a simple root
  and `m² + m + 1` irreducible to force at most one root in `ℤ₂` (hence ≤ 1 rational root):
  * `sq_add_self_add_one_ne_zero` — the poly-free fact `∀ x : ZMod 2, x² + x + 1 ≠ 0` (shared
    input to the 2-adic no-root proof below).
  * `irreducible_X_sq_add_X_add_one` — `X² + X + 1` is irreducible over `ZMod 2` (degree `2`, no
    root, via the degree-`≤ 3` no-root criterion).
  * `not_X_dvd_X_sq_add_X_add_one` — `X ∤ (X² + X + 1)` over `ZMod 2`, i.e. `X` is a *simple*
    root of `X³ + X² + X` (nonzero constant term).
* `TworowD4Kernel/PadicNoRoot.lean` — the **2-adic lift** of the Hensel inputs, the conclusions the
  finite-field facts were built for (informal proof `2026-06-09-tworow-d4-b23-2adic-single-candidate`):
  * `no_padic_root_sq_add_self_add_one` — `X² + X + 1` has **no root in `ℤ_[2]`**: a hypothetical
    root reduces under `PadicInt.toZMod : ℤ_[2] →+* ZMod 2` to a (non-existent) root over `𝔽₂`.
    This forces `v₂(m − θ) = 0` for every integer `m` (Lemma A) and makes `ρ_b` unique.
  * `hensel_unique_root_of_simple_root_mod_two` — Hensel uniqueness: an integer polynomial whose
    mod-`2` reduction has `0` as a *simple* root has a **unique** root in `2ℤ₂ = {z : ‖z‖ < 1}`.
    This is the unique lift `ρ_b` of `m ≡ 0`.
  * `hensel_unique_root_reduced_model` — concrete non-vacuity witness: the literal reduced model
    `X³ + X² + X = X · (X² + X + 1)` satisfies the hypotheses, with unique `2`-adic root `0`.

## Building

```sh
lake exe cache get   # pull precompiled Mathlib oleans (~30 s)
lake build           # builds the whole library
```

Toolchain: `leanprover/lean4:v4.30.0`, Mathlib `v4.30.0` (pinned in `lakefile.toml` and
`lake-manifest.json`).
