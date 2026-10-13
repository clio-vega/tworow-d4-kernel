/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.CyclicAscent
import TworowD4Kernel.RegionMultiplicity

/-!
# The index-model bridge: `ZMod h` against `1`-based `ℕ`

Two earlier files prove the two halves of `ord_{t=1} Ψ_T = ν(T)` **on index models that do
not talk to each other**, and this file is the identification they were missing.  Until it
exists, `ν(T) = |J|` and `ord_{t=1} ∏(1 - t^{m_i}) = |J|` are statements about two different
`J`s, over two different types, and the two `|J|`s cannot be cancelled.

## Which model is which

* **Model A** — `TworowD4Kernel.CyclicAscent`.  Words are `θ : ZMod h → Bool`; the index type
  *is* the cycle, so the wrap is carried by the ring: the successor of `i` is `i + 1` and
  `h - 1` is followed by `0`.  Indices are **0-based**.  Its ascent set is
  `ZMod.J θ = univ.filter fun i => θ i = false ∧ θ (i + 1) = true`.
* **Model B** — `TworowD4Kernel.RegionMultiplicity`.  Words are `θ : ℕ → Bool` restricted to
  `1 ≤ i ≤ h`, matching the paper's subscripts verbatim; the wrap is carried by a *function*,
  `succIdx h i = if i = h then 1 else i + 1`.  Indices are **1-based**.  Its ascent set is the
  predicate `Region.inJ h θ i = (θ i = false ∧ θ (succIdx h i) = true)`.

Model B chose a function over a type on purpose: the region condition `x_1 ≥ ⋯ ≥ x_h` is
**not** cyclic, so `x` cannot live on `ZMod h`, while `m` and `J` are cyclic.  That choice was
right and is not revisited here; what is supplied is the translation.

## The intertwining square, and where the twist actually lives

`idxEquiv : ZMod h ≃ {i : ℕ // 1 ≤ i ∧ i ≤ h}` is `j ↦ j.val + 1`, and
`succIdx_val_idxEquiv` is the commuting square

```
      ZMod h  --( · + 1 )-->  ZMod h
        |                        |
   idxEquiv                  idxEquiv
        v                        v
    [1, h]  --( succIdx h )-->  [1, h]
```

**The square commutes on the nose — there is no twist in the intertwiner.**  That was the
open question (`LEAN.md` §2 warned that `ZMod.ascentSet_unitVector` reads the ascent set of
the `i`-th unit vector as the singleton `{i - 1}`, not `{i}`, and that the bridge might have
to absorb that shift).  It does not: the `{i - 1}` is a fact *internal to Model A* about which
slot a box's ascent occupies, and it transports along the square unchanged.

The `-1` is real, but it lives in the **word transport**, not the index map:
`toNatWord θ i = θ ((i : ZMod h) - 1)`.  A `1`-based word must read the `0`-based word one
place down, because `idxEquiv` sends `0 ↦ 1`.  Both facts are stated separately
(`succIdx_val_idxEquiv`, `toNatWord_val_idxEquiv`) so that neither can hide inside the other:
an off-by-one bridge is worse than no bridge, because it type-checks.

## Provenance

The index set is Korff's, **arXiv:1110.6356, Definition 5.5**; the region and the
multiplicity vector are Huh--Kim--Krattenthaler--Okada, **arXiv:2301.13117, Prop. 2.7** and
`(eq:mvec)`.  Gap 1 is `Polynomial.rootMultiplicity_prod_one_sub_X_pow_of_one_le`
(`RootMultiplicityProduct.lean`), gap 2 is `ZMod.nu_eq_card_of_content_ones`
(`CyclicAscent.lean`), gap 3 is `Region.one_le_multNat_of_mem_J` (`RegionMultiplicity.lean`).
-/

-- `autoImplicit` is ON project-wide (`lakefile.toml` sets only `relaxedAutoImplicit = false`,
-- and a probe confirmed a bare `α` auto-binds).  On 2026-10-12 that silently promoted a bare
-- `X` to a ring *variable*, making a `ring` control hold generically while saying nothing
-- about `Polynomial.X`.  This file opts out locally: every implicit below is declared.
set_option autoImplicit false

namespace TworowD4Kernel.Bridge

open Finset Polynomial TworowD4Kernel.Region TworowD4Kernel.CyclicAscent

variable {h : ℕ} [NeZero h]

/-! ### Target 1 — the index equivalence and the intertwining square -/

/-- **The index equivalence.**  `ZMod h ≃ {i : ℕ // 1 ≤ i ∧ i ≤ h}`, by `j ↦ j.val + 1`.
`ZMod.val` lands in `[0, h - 1]`, so adding one lands in `[1, h]` — the paper's range. -/
def idxEquiv (h : ℕ) [NeZero h] : ZMod h ≃ {i : ℕ // 1 ≤ i ∧ i ≤ h} where
  toFun j := ⟨j.val + 1, by omega, by have := ZMod.val_lt j; omega⟩
  invFun i := ((i.1 - 1 : ℕ) : ZMod h)
  left_inv j := by simp
  right_inv i := by
    obtain ⟨i, hi1, hih⟩ := i
    have hlt : i - 1 < h := by omega
    simp only [Subtype.mk.injEq, ZMod.val_cast_of_lt hlt]
    omega

@[simp] theorem val_idxEquiv (j : ZMod h) : (idxEquiv h j).1 = j.val + 1 := rfl

/-- `j + 1` in `ZMod h` is the cast of `j.val + 1`.  The one cast fact both halves of the
bridge rest on; isolated so that the square and the word transport cite the *same* step. -/
theorem natCast_val_add_one (j : ZMod h) : ((j.val + 1 : ℕ) : ZMod h) = j + 1 := by
  push_cast [ZMod.natCast_val, ZMod.cast_id]
  ring

/-- `(j + 1).val = (j.val + 1) % h`. -/
theorem val_add_one (j : ZMod h) : (j + 1 : ZMod h).val = (j.val + 1) % h := by
  rw [← natCast_val_add_one, ZMod.val_natCast]

/-- **Target 1 — the intertwining square, and it commutes on the nose.**
`succIdx` on Model B's `1`-based indices is exactly `· + 1` on Model A's `ZMod h`, read
through `idxEquiv`.  No twist.

Both branches are checked: when `j.val + 1 < h` the successor is literally `+1` on each
side; when `j.val + 1 = h` the left side wraps to `1` by `succIdx_self` and the right side
wraps to `0 + 1 = 1` because `h % h = 0`. -/
theorem succIdx_val_idxEquiv (j : ZMod h) :
    succIdx h (idxEquiv h j).1 = (idxEquiv h (j + 1)).1 := by
  have hjlt : j.val < h := ZMod.val_lt j
  rw [val_idxEquiv, val_idxEquiv, val_add_one]
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hjlt) with heq | hlt
  · have heq' : j.val + 1 = h := heq
    simp [succIdx, heq']
  · rw [succIdx_of_lt hlt, Nat.mod_eq_of_lt hlt]

/-! ### Target 2 — the word transport and the set identification

This is where the `-1` lives.  `idxEquiv` sends `0 ↦ 1`, so a `1`-based word must read the
`0`-based word one slot down, and `toNatWord` is the only declaration in this file that
shifts anything.  Keeping it out of `succIdx_val_idxEquiv` is the point: if the shift were
folded into the index map, the square would still type-check and the composite would be
silently off by one. -/

/-- **The word transport.**  Model A's word `θ : ZMod h → Bool` read as a `1`-based Model B
word.  The `- 1` is forced by `idxEquiv : 0 ↦ 1`; only the values on `[1, h]` are ever used,
and `inJ` never leaves that range because `succIdx` wraps. -/
def toNatWord (θ : ZMod h → Bool) : ℕ → Bool := fun i => θ ((i : ZMod h) - 1)

/-- The transport undoes `idxEquiv` on the nose: reading the transported word at Model B
index `j.val + 1` returns Model A's letter at `j`. -/
theorem toNatWord_val_idxEquiv (θ : ZMod h → Bool) (j : ZMod h) :
    toNatWord θ (idxEquiv h j).1 = θ j := by
  simp only [val_idxEquiv, toNatWord, natCast_val_add_one]
  simp

/-- **Target 2 — the set identification.**  Model B's ascent *predicate* at `idxEquiv h j`
holds exactly when `j` lies in Model A's ascent *set*.  The two `J`s are the same set.

The proof is the square plus the transport and nothing else: `succIdx_val_idxEquiv` moves the
`succIdx` to a `+ 1` in `ZMod h`, then `toNatWord_val_idxEquiv` strips both letters. -/
theorem inJ_iff_mem_J (θ : ZMod h → Bool) (j : ZMod h) :
    inJ h (toNatWord θ) (idxEquiv h j).1 ↔ j ∈ ZMod.J θ := by
  rw [inJ, succIdx_val_idxEquiv, toNatWord_val_idxEquiv, toNatWord_val_idxEquiv]
  simp [ZMod.J]

/-- `j ↦ j.val + 1` is injective: it is `Subtype.val ∘ idxEquiv`. -/
theorem idx_injective : Function.Injective fun j : ZMod h => (idxEquiv h j).1 :=
  Subtype.val_injective.comp (idxEquiv h).injective

/-- Model A's ascent set pushed into Model B's `1`-based `ℕ` indices. -/
def natJ (θ : ZMod h → Bool) : Finset ℕ := (ZMod.J θ).image fun j => (idxEquiv h j).1

/-- **The cardinality statement gaps 2 and 3 both need.**  Pushing the ascent set along
`idxEquiv` does not change its size, so the `|J|` produced by gap 2 and the `|J|` consumed by
gap 3 are the same natural number. -/
theorem card_natJ (θ : ZMod h → Bool) : (natJ θ).card = (ZMod.J θ).card :=
  Finset.card_image_of_injective _ idx_injective

/-- Every element of `natJ` satisfies gap 3's three hypotheses: in range, and in `J`. -/
theorem natJ_spec (θ : ZMod h → Bool) {i : ℕ} (hi : i ∈ natJ θ) :
    1 ≤ i ∧ i ≤ h ∧ inJ h (toNatWord θ) i := by
  rw [natJ, Finset.mem_image] at hi
  obtain ⟨j, hj, rfl⟩ := hi
  exact ⟨(idxEquiv h j).2.1, (idxEquiv h j).2.2, (inJ_iff_mem_J θ j).mpr hj⟩

/-! ### Target 3 — the composite, with every hypothesis discharged -/

/-- **Target 3a — gap 1 ∘ gap 3 ∘ bridge.**  For a Model A word `θ` and a step whose endpoint
lies in HKKO's region, the order of vanishing at `t = 1` of `∏_{i ∈ J}(1 - t^{m_i})` equals the
cardinality of **Model A's** cyclic ascent set.

This is the sentence that did not previously exist: the left-hand side is entirely Model B
(`multNat`, `Mem`, `shift`, `1`-based `ℕ`) and the right-hand side is entirely Model A
(`ZMod.J`, `ZMod h`).  Nothing is assumed about the multiplicities — the region condition
supplies `m_i ≥ 1` through gap 3. -/
theorem rootMultiplicity_prod_eq_card_ascentSet {R : Type*} [CommRing R] [IsDomain R]
    [CharZero R] {w : ℤ} {x : ℕ → ℤ} (θ : ZMod h → Bool)
    (hy : Mem h w (shift x (toNatWord θ))) :
    rootMultiplicity (1 : R) (∏ i ∈ natJ θ, (1 - X ^ (multNat h w x i))) = (ZMod.J θ).card := by
  rw [← card_natJ θ]
  exact rootMultiplicity_prod_mult_eq_card hy (natJ θ) fun i hi => natJ_spec θ hi

/-- **Target 3b — the full chain, `ord_{t=1} Ψ = ν(T) = n` at content `(1^n)`.**
Gap 2 (`ZMod.nu_eq_card_of_content_ones`, Model A) → bridge → gap 3 → gap 1, composed into one
declaration with no remaining hypothesis on the multiplicities.

For `n` single boxes at arbitrary cyclic positions `p a`, each step's endpoint lying in the
region, the total order of vanishing at `t = 1` is exactly `n`.  This is the numerical input to
the Q410 contradiction, and it is now stated on **one** index model.

**Scope, unchanged from `CyclicAscent`:** this is the *word-level* count.  That content
`(1^n)` forces each occupation word to *be* a unit vector is strip combinatorics and is still
not formalised.  See `projects/proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`. -/
theorem sum_rootMultiplicity_eq_content_ones {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {n : ℕ} {w : ℤ} (hh : 2 ≤ h) (p : Fin n → ZMod h) (x : Fin n → ℕ → ℤ)
    (hy : ∀ a, Mem h w (shift (x a) (toNatWord fun j => decide (j = p a)))) :
    (∑ a : Fin n, rootMultiplicity (1 : R)
      (∏ i ∈ natJ (fun j => decide (j = p a)), (1 - X ^ (multNat h w (x a) i)))) = n := by
  calc (∑ a : Fin n, rootMultiplicity (1 : R)
          (∏ i ∈ natJ (fun j => decide (j = p a)), (1 - X ^ (multNat h w (x a) i))))
      = ∑ a : Fin n, (ZMod.J (fun j => decide (j = p a))).card :=
        Finset.sum_congr rfl fun a _ => rootMultiplicity_prod_eq_card_ascentSet _ (hy a)
    _ = n := ZMod.nu_eq_card_of_content_ones hh p

/-! ### Controls

Two ablations, both about the *statement* rather than the proof: each drops something
load-bearing and exhibits the failure concretely. -/

/-- **Ablation 1: `NeZero h` is necessary about the statement.**  At `h = 0` the Model B index
range `{i // 1 ≤ i ∧ i ≤ 0}` is empty while `ZMod 0 = ℤ` is not, so *no* equivalence exists —
`idxEquiv` is not merely unprovable without `NeZero h`, its conclusion is false. -/
theorem no_idxEquiv_at_zero : IsEmpty (ZMod 0 ≃ {i : ℕ // 1 ≤ i ∧ i ≤ 0}) :=
  ⟨fun e => by obtain ⟨h1, h2⟩ := (e 0).2; omega⟩

/-- **Ablation 2: the `- 1` in `toNatWord` is load-bearing, and dropping it type-checks.**
Take `h = 2` and the unit vector at `0`.  The bridge puts its single ascent at Model B index
`2` (`natJ_unit_zero_at_two`).  The *naive* transport `fun i => θ i`, which forgets the shift,
puts an ascent at index `1` instead (`naive_inJ_at_one`) — and `1 ∉ {2}`.

So the naive transport is a well-typed bridge that reports the wrong slot.  This is exactly
the failure mode `LEAN.md` §2 warned about; it is real, and it is in the *word* map, not the
*index* map. -/
theorem natJ_unit_zero_at_two : natJ (fun j : ZMod 2 => decide (j = 0)) = {2} := by
  have hsub : (0 - 1 : ZMod 2) = 1 := by decide
  rw [natJ, ZMod.ascentSet_unitVector (by omega) (0 : ZMod 2), hsub,
    Finset.image_singleton, val_idxEquiv]
  rfl

theorem naive_inJ_at_one : inJ 2 (fun i : ℕ => decide ((i : ZMod 2) = 0)) 1 :=
  ⟨by decide, by decide⟩

theorem naive_slot_ne_bridge_slot :
    (1 : ℕ) ∉ natJ (fun j : ZMod 2 => decide (j = 0)) := by
  rw [natJ_unit_zero_at_two]; decide

end TworowD4Kernel.Bridge
