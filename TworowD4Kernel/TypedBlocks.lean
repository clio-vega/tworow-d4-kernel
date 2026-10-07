/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.LabelledBlocks

/-!
# The type-split product of labelled-block counts

`LabelledBlocks.card_blockFunctions_eq_multinomial` counts the ways to cut *one* finite
set into labelled blocks of prescribed sizes. This file performs the next step: the set
carries a *type map* `τ : A → T`, the block sizes are prescribed *per type*
(`m : T → V → ℕ`), and the count becomes a **product over types** of per-type
multinomials.

* `TypedBlocks.card_typedBlockFunctions_eq_prod_multinomial` :
  `#{f : A → V | ∀ s v, #{a | τ a = s ∧ f a = v} = m s v} = ∏ s, Nat.multinomial univ (m s)`,
  under the (necessary, see `card_typedBlockFunctions_eq_zero_of_sum_ne`) hypothesis
  `∀ s, ∑ v, m s v = Fintype.card {a // τ a = s}`.

## What is Mathlib's and what is not

The *transport* is Mathlib's: `Equiv.piCongrFiberwise` splits `A → V` into the product
over `s : T` of `{a // τ a = s} → V`, `Equiv.subtypePiEquivPi` pushes a pointwise
predicate through a `Pi`, and `Fintype.card_pi` turns the resulting `Pi` of subtypes into
a product of cardinalities. What Mathlib does not have — see the module docstring of
`LabelledBlocks` and the standing TODO on `Multiset.bell` — is that the per-factor
cardinality *is* a multinomial coefficient. That half is `LabelledBlocks`.

So this file is a composition, and the single new mathematical observation in it is that
the per-type conditions are *independent*: they constrain disjoint parts of the data.
That independence is what `typedBlockEquivPi` makes precise.

## Provenance

This is the product-over-types step of Theorem A of
`projects/proofs/2026-10-06-ls-corollary-4-coupling.tex`, which counts "Corollary-4 maps"
for the Lenart–Sottile skew Schubert polynomial identity (`arXiv:math/0202090`,
Lenart–Sottile, *Skew Schubert polynomials*, Corollary 4 and the remark after Theorem 2):

  `N(u,w) = ∏_α I_α(u,w)! / ∏_v (c^w_{u,v}!)^{I_α(w₀ v, w₀)}`.

The dictionary is: `A = Γ(u,w)` (increasing chains), `T` = the set of types `α`,
`τ = type`, `V = ⨆_v Γ(w₀ v, w₀)` (all blocks of the target, over all types), and
`m α C = c^w_{u,v}` for `C ∈ Γ_α(w₀ v, w₀)`, with `m α C = 0` for every block `C` whose
own type is not `α`.

Note that condition (i) of the paper's Definition — that `f` be *type-preserving* — is
**not** a separate hypothesis here: it is forced by those zero prescriptions, since a
chain of type `α` cannot land in a block `C` of type `≠ α` when that fibre is prescribed
to be empty. Blocks with `m s v = 0` contribute `0! = 1` to the denominator, so the
product `∏ s, Nat.multinomial univ (m s)` is exactly `N(u,w)`.

## What is still *not* formalised

The labelled Bruhat order, chains, `Γ_α` and the numbers `I_α(u,w)`, `c^w_{u,v}` do not
exist in Lean, so Theorem A itself is not formalised — only its two set-theoretic inputs
(one multinomial per type, and now the independence of the types). `unproved ≠
unformalised`; nothing on the paper side is promoted by this file.
-/

namespace TworowD4Kernel

open Finset Equiv Nat

namespace TypedBlocks

open LabelledBlocks

variable {A V T : Type*} [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V]
  [Fintype T] [DecidableEq T]

/-- The part of `A` of type `s`, i.e. the fibre of the type map `τ` over `s`. -/
abbrev typePart (τ : A → T) (s : T) : Type _ := {a : A // τ a = s}

/-- The restriction of `f : A → V` to the part of `A` of type `s`. -/
def restrict (τ : A → T) (f : A → V) (s : T) : typePart τ s → V := fun x => f x.1

/-- `TypedBlockSizes τ m f` says that `f` cuts *each* type part of `A` into blocks of the
sizes prescribed for that type: within the part of type `s`, the block labelled `v` has
exactly `m s v` elements. -/
def TypedBlockSizes (τ : A → T) (m : T → V → ℕ) (f : A → V) : Prop :=
  ∀ s, BlockSizes (m s) (restrict τ f s)

instance (τ : A → T) (m : T → V → ℕ) (f : A → V) : Decidable (TypedBlockSizes τ m f) :=
  inferInstanceAs (Decidable (∀ _, _))

variable (A) in
/-- The `Finset` of all type-split labelled partitions of `A` with per-type block
sizes `m`. -/
def typedBlockFunctions (τ : A → T) (m : T → V → ℕ) : Finset (A → V) :=
  univ.filter (TypedBlockSizes τ m)

@[simp]
theorem mem_typedBlockFunctions {τ : A → T} {m : T → V → ℕ} {f : A → V} :
    f ∈ typedBlockFunctions A τ m ↔ TypedBlockSizes τ m f := by
  simp [typedBlockFunctions]

/-! ### The types are independent

Restriction to the type parts is a bijection `(A → V) ≃ ∀ s, (typePart τ s → V)`
(Mathlib's `Equiv.piCongrFiberwise` for the type map `τ`), and under it the predicate
`TypedBlockSizes τ m` is *by definition* the pointwise conjunction of the per-type
predicates `BlockSizes (m s)`. That is the whole content of the product formula. -/

/-- Restriction to the type parts, as an equivalence. This is Mathlib's
`Equiv.piCongrFiberwise` for the type map `τ`, with constant fibres. -/
def restrictEquiv (τ : A → T) : (A → V) ≃ ∀ s, (typePart τ s → V) :=
  Equiv.piCongrFiberwise (f := τ) (γ₁ := fun _ => V) fun _ => Equiv.refl _

omit [Fintype A] [DecidableEq A] [Fintype V] [DecidableEq V] [Fintype T] [DecidableEq T] in
@[simp]
theorem restrictEquiv_apply (τ : A → T) (f : A → V) (s : T) :
    (restrictEquiv τ f) s = restrict τ f s := rfl

/-- **The types are independent.** A type-split labelled partition of `A` with per-type
block sizes `m` is the same thing as a choice, independently for each type `s`, of a
labelled partition of the type-`s` part with block sizes `m s`. -/
def typedBlockEquivPi (τ : A → T) (m : T → V → ℕ) :
    {f : A → V // TypedBlockSizes τ m f} ≃
      ∀ s, {g : typePart τ s → V // BlockSizes (m s) g} :=
  (Equiv.subtypeEquiv (restrictEquiv τ) fun _ => Iff.rfl).trans Equiv.subtypePiEquivPi

/-! ### The count -/

/-- **The type-split product formula.** The number of ways to cut `A` into blocks
labelled by `V`, with the block labelled `v` inside the part of type `s` prescribed to
have `m s v` elements, is the product over types of the per-type multinomial
coefficients. -/
theorem card_typedBlockFunctions_eq_prod_multinomial {τ : A → T} {m : T → V → ℕ}
    (hm : ∀ s, ∑ v, m s v = Fintype.card (typePart τ s)) :
    #(typedBlockFunctions A τ m) = ∏ s, Nat.multinomial univ (m s) := by
  rw [typedBlockFunctions, ← Fintype.card_subtype,
    Fintype.card_congr (typedBlockEquivPi τ m), Fintype.card_pi]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [Fintype.card_subtype, ← blockFunctions]
  exact card_blockFunctions_eq_multinomial (hm s)

/-! ### The hypothesis is load-bearing

The sizes prescribed for a type must add up to the size of that type part, or there is
nothing to count. This is the type-split form of the "if and only if" in the paper proof
of Theorem A: `∑_C |B_C| = ∑_v c^w_{u,v} I_α(w₀ v, w₀) ⟹ I_α(u,w)`. -/

/-- The blocks of `g : B → V` partition `B`. -/
theorem sum_card_fibre {B : Type*} [Fintype B] (g : B → V) :
    ∑ v, #(fibre g v) = Fintype.card B := by
  rw [← Finset.card_univ]
  exact (Finset.card_eq_sum_card_fiberwise fun b _ => Finset.mem_univ (g b)).symm

/-- **Necessity of the summation hypothesis.** If the sizes prescribed for even one type
fail to add up to the size of that type part, nothing is counted — while the product
`∏ s, Nat.multinomial univ (m s)` is always positive. So the hypothesis of
`card_typedBlockFunctions_eq_prod_multinomial` cannot be dropped. -/
theorem card_typedBlockFunctions_eq_zero_of_sum_ne {τ : A → T} {m : T → V → ℕ} {s : T}
    (hs : ∑ v, m s v ≠ Fintype.card (typePart τ s)) :
    #(typedBlockFunctions A τ m) = 0 := by
  rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro f hf
  refine hs ?_
  rw [← sum_card_fibre (restrict τ f s)]
  exact (Finset.sum_congr rfl fun v _ => ((mem_typedBlockFunctions.mp hf) s v)).symm

omit [DecidableEq V] [DecidableEq T] in
/-- The product of multinomials is always positive; combined with
`card_typedBlockFunctions_eq_zero_of_sum_ne` this says the summation hypothesis is
*exactly* the obstruction. -/
theorem prod_multinomial_pos (m : T → V → ℕ) : 0 < ∏ s, Nat.multinomial univ (m s) :=
  Finset.prod_pos fun s _ => Nat.multinomial_pos univ (m s)

/-- **Existence.** Under the summation hypothesis a type-split labelled partition exists.
This is the existence half of Theorem A of `2026-10-06-ls-corollary-4-coupling.tex`, at
the abstraction level of this file. -/
theorem typedBlockFunctions_nonempty {τ : A → T} {m : T → V → ℕ}
    (hm : ∀ s, ∑ v, m s v = Fintype.card (typePart τ s)) :
    (typedBlockFunctions A τ m).Nonempty := by
  rw [← Finset.card_pos, card_typedBlockFunctions_eq_prod_multinomial hm]
  exact prod_multinomial_pos m

/-! ### Non-vacuity: a concrete instance decided by enumeration

The theorem above is proved by transport (`typedBlockEquivPi`) plus
`LabelledBlocks.card_blockFunctions_eq_multinomial`. The witnesses below settle the same
numbers by a *different mechanism* — kernel enumeration of all `2 ^ 5 = 32` functions
`Fin 5 → Fin 2` — so they are an independent check, not a second reading of the proof.

The instance: `A = Fin 5` split by `tauEx` into parts `{0,1,2}` and `{3,4}`; block sizes
`(2,1)` on the first part and `(1,1)` on the second. The predicted count is
`3!/(2!·1!) · 2!/(1!·1!) = 3 · 2 = 6`. -/

/-- The type map on `Fin 5` with parts `{0,1,2}` and `{3,4}`. -/
def tauEx : Fin 5 → Fin 2 := fun a => if a.val < 3 then 0 else 1

/-- Block sizes `(2,1)` on the type-`0` part, `(1,1)` on the type-`1` part. -/
def mEx : Fin 2 → Fin 2 → ℕ := fun s v => if s = 0 then (if v = 0 then 2 else 1) else 1

/-- The summation hypothesis holds for `(tauEx, mEx)`: `2 + 1 = 3` and `1 + 1 = 2`. -/
theorem sum_mEx : ∀ s, ∑ v, mEx s v = Fintype.card (typePart tauEx s) := by decide

/-- The count, by enumeration of all `32` functions `Fin 5 → Fin 2`. -/
theorem card_typedBlockFunctions_ex : #(typedBlockFunctions (Fin 5) tauEx mEx) = 6 := by decide

/-- The product of multinomials, evaluated. Agrees with
`card_typedBlockFunctions_ex`, as `card_typedBlockFunctions_eq_prod_multinomial` predicts. -/
theorem prod_multinomial_ex : ∏ s, Nat.multinomial univ (mEx s) = 6 := by decide

/-! #### The negative control

`mBadEx` prescribes sizes `(2,0)` on the type-`0` part, which has `3` elements: `2 + 0 ≠ 3`.
The count collapses to `0` while the product of multinomials stays at `2`. So the
summation hypothesis of `card_typedBlockFunctions_eq_prod_multinomial` is load-bearing —
without it the stated equality is *false*, not merely unproved. -/

/-- Sizes `(2,0)` on the type-`0` part — they do not add up to its `3` elements. -/
def mBadEx : Fin 2 → Fin 2 → ℕ := fun s v => if s = 0 then (if v = 0 then 2 else 0) else 1

/-- The hypothesis really fails for `mBadEx`. -/
theorem sum_mBadEx_ne : ∑ v, mBadEx 0 v ≠ Fintype.card (typePart tauEx 0) := by decide

/-- Nothing is counted. -/
theorem card_typedBlockFunctions_badEx :
    #(typedBlockFunctions (Fin 5) tauEx mBadEx) = 0 := by decide

/-- But the product of multinomials is `2`. `0 ≠ 2`: the control fires. -/
theorem prod_multinomial_badEx : ∏ s, Nat.multinomial univ (mBadEx s) = 2 := by decide

end TypedBlocks

end TworowD4Kernel

/-! ### Axiom audit -/

section Audit
open TworowD4Kernel.TypedBlocks
#print axioms card_typedBlockFunctions_eq_prod_multinomial
#print axioms typedBlockEquivPi
#print axioms card_typedBlockFunctions_eq_zero_of_sum_ne
#print axioms typedBlockFunctions_nonempty
#print axioms sum_card_fibre
#print axioms prod_multinomial_pos
#print axioms card_typedBlockFunctions_ex
#print axioms prod_multinomial_ex
#print axioms card_typedBlockFunctions_badEx
#print axioms prod_multinomial_badEx
#print axioms sum_mEx
#print axioms sum_mBadEx_ne
end Audit
