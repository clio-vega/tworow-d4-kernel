/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.BigOperators

/-!
# Counting labelled blocks of prescribed sizes

The number of ways to partition a finite set `A` into blocks labelled by `V`, with the
block labelled `v` prescribed to have size `m v`, is the multinomial coefficient
`(#A)! / ∏ v, (m v)!`.

Specifying such a labelled partition is the same as specifying a function `f : A → V`
whose fibre over `v` has cardinality `m v`, so the statement proved here is

* `card_filter_fibreCard_eq_multinomial` :
  `#{f : A → V | ∀ v, #(fibre of f over v) = m v} = Nat.multinomial univ m`,

under the (necessary) hypothesis `∑ v, m v = Fintype.card A`.

## Why this is not already in Mathlib

Mathlib has the *arithmetic* of multinomial coefficients in full
(`Nat.multinomial`, `Nat.multinomial_spec`, and the algebraic multinomial theorem
`Finset.sum_pow`), and it has the *stabiliser* half of the orbit-stabiliser count
(`DomMulAct.stabilizer_card`). What it does not have is the *combinatorial
interpretation* — that these numbers count anything. This is explicit in Mathlib:
`Mathlib/Combinatorics/Enumerative/Bell.lean` defines `Multiset.bell` as an arithmetic
expression documented as "number of partitions of a set of cardinality `m.sum` whose
parts have cardinalities given by `m`" and carries the TODO

> Prove that it actually counts the number of partitions as indicated.

Likewise `Multiset.countPerms` is *defined* as a multinomial and named "the number of
permutations of a given multiset", with no theorem that it counts permutations. The
result below is the labelled (ordered-blocks) sibling of that TODO; `Multiset.bell` is
the unlabelled one, which divides further by the automorphisms permuting equal-size
blocks.

## Provenance

This is the mathematical content underneath Theorem A of
`projects/proofs/2026-10-06-ls-corollary-4-coupling.tex`, whose product formula

  `N(u,w) = ∏_α I_α(u,w)! / ∏_v (c^w_{u,v}!)^{I_α(w₀v, w₀)}`

counts "Corollary-4 maps" for the Lenart–Sottile skew Schubert polynomial identity
(`arXiv:math/0202090`, Lenart–Sottile, *Skew Schubert polynomials*, Corollary 4 and the
remark following Theorem 2). Everything in `N(u,w)` beyond the lemma below is indexing:
a chain has exactly one type, so the chain set splits as a disjoint union over types `α`
and the conditions for distinct `α` constrain disjoint parts of the data. The exponent
`I_α(w₀v, w₀)` is the number of `v`-components, each of which is an independent block of
prescribed size `c^w_{u,v}`.

The product over types -- a product of independent multinomials, which is the form in
which Theorem A uses this lemma -- is `TypedBlocks.card_typedBlockFunctions_eq_prod_multinomial`
in `TworowD4Kernel.TypedBlocks`.

(Until 2026-10-07 this paragraph pointed at a declaration named `multinomial_prod_pow`,
which was never written: a docstring is a claim about contents, and that one was false.)
-/

namespace TworowD4Kernel

open Finset Equiv Nat

namespace LabelledBlocks

variable {A V : Type*} [Fintype A] [DecidableEq V]

/-- The fibre of `f` over `v`, as a `Finset`. Its cardinality is the size of the block
labelled `v` in the labelled partition of `A` determined by `f`. -/
def fibre (f : A → V) (v : V) : Finset A := univ.filter (fun a => f a = v)

@[simp]
theorem mem_fibre {f : A → V} {v : V} {a : A} : a ∈ fibre f v ↔ f a = v := by
  simp [fibre]

theorem card_fibre_eq_card_subtype (f : A → V) (v : V) :
    #(fibre f v) = Fintype.card {a // f a = v} := by
  rw [Fintype.card_subtype]; rfl

/-- `BlockSizes m f` says that `f : A → V` cuts `A` into blocks of the prescribed sizes:
the block labelled `v` has exactly `m v` elements. -/
def BlockSizes (m : V → ℕ) (f : A → V) : Prop := ∀ v, #(fibre f v) = m v

instance [Fintype V] (m : V → ℕ) (f : A → V) : Decidable (BlockSizes m f) :=
  inferInstanceAs (Decidable (∀ _, _))

variable (A) in
/-- The `Finset` of all labelled partitions of `A` with block sizes `m`. -/
def blockFunctions [DecidableEq A] [Fintype V] (m : V → ℕ) : Finset (A → V) :=
  univ.filter (BlockSizes (A := A) m)

@[simp]
theorem mem_blockFunctions [DecidableEq A] [Fintype V] {m : V → ℕ} {f : A → V} :
    f ∈ blockFunctions A m ↔ BlockSizes m f := by
  simp [blockFunctions]

/-! ### The canonical model

`Σ v, Fin (m v)` is the canonical labelled partition with block sizes `m`, with the
labelling map `Sigma.fst`. Any `f` with block sizes `m` is isomorphic to it over `V`. -/

/-- The fibre of `Sigma.fst` over `v` in `Σ w, Fin (m w)` is `Fin (m v)`. -/
def sigmaFstFibreEquiv (m : V → ℕ) (v : V) :
    {x : (Σ w, Fin (m w)) // x.1 = v} ≃ Fin (m v) where
  toFun x := x.2 ▸ x.1.2
  invFun i := ⟨⟨v, i⟩, rfl⟩
  left_inv := by rintro ⟨⟨w, i⟩, rfl⟩; rfl
  right_inv := by intro i; rfl

/-- Any `f` with block sizes `m` identifies `A` with the canonical model `Σ v, Fin (m v)`
compatibly with the labelling maps. This is the single geometric input to the count. -/
theorem exists_equiv_sigma {m : V → ℕ} (f : A → V) (hf : BlockSizes m f) :
    ∃ e : A ≃ Σ v, Fin (m v), ∀ a, (e a).1 = f a := by
  have hcard : ∀ v, Fintype.card {a // f a = v} = m v := by
    intro v; rw [← card_fibre_eq_card_subtype]; exact hf v
  refine ⟨(Equiv.sigmaFiberEquiv f).symm.trans
    (Equiv.sigmaCongrRight fun v => Fintype.equivFinOfCardEq (hcard v)), fun a => rfl⟩

/-- The canonical model really does have block sizes `m`, provided the sizes add up. -/
theorem exists_blockSizes [Fintype V] {m : V → ℕ} (hm : ∑ v, m v = Fintype.card A) :
    ∃ f : A → V, BlockSizes m f := by
  have hc : Fintype.card A = Fintype.card (Σ v, Fin (m v)) := by
    rw [Fintype.card_sigma]; simp [hm]
  obtain e := Fintype.equivOfCardEq hc
  refine ⟨fun a => (e a).1, fun v => ?_⟩
  rw [card_fibre_eq_card_subtype]
  have : {a // (e a).1 = v} ≃ Fin (m v) :=
    (Equiv.subtypeEquiv e fun a => Iff.rfl).trans (sigmaFstFibreEquiv m v)
  rw [Fintype.card_congr this, Fintype.card_fin]

/-- Two labelled partitions with the same block sizes differ by a permutation of `A`.
Equivalently: `blockFunctions m` is a single orbit of `Perm A` acting by precomposition. -/
theorem exists_perm_comp_eq {m : V → ℕ} {f g : A → V}
    (hf : BlockSizes m f) (hg : BlockSizes m g) : ∃ σ : Perm A, g ∘ σ = f := by
  obtain ⟨ef, hef⟩ := exists_equiv_sigma f hf
  obtain ⟨eg, heg⟩ := exists_equiv_sigma g hg
  refine ⟨ef.trans eg.symm, funext fun a => ?_⟩
  have h : g (eg.symm (ef a)) = f a := by
    rw [← heg (eg.symm (ef a)), Equiv.apply_symm_apply]; exact hef a
  simpa using h

/-! ### The count

Double counting over `Perm A`. The map `σ ↦ f₀ ∘ σ` from `Perm A` onto `blockFunctions A m`
is surjective (`exists_perm_comp_eq`) with all fibres of the same size, namely the size of
the stabiliser `{σ | f₀ ∘ σ = f₀}`, which Mathlib computes to be `∏ v, (m v)!`
(`DomMulAct.stabilizer_card`). -/

/-- Block sizes are invariant under precomposition with a permutation of `A`. -/
theorem blockSizes_comp (σ : Perm A) {m : V → ℕ} {f : A → V} (hf : BlockSizes m f) :
    BlockSizes m (f ∘ σ) := by
  intro v
  rw [card_fibre_eq_card_subtype, ← hf v, card_fibre_eq_card_subtype]
  exact Fintype.card_congr (Equiv.subtypeEquiv σ fun _ => Iff.rfl)

/-- All fibres of `σ ↦ f₀ ∘ σ` are translates of the stabiliser of `f₀`. -/
def permFibreEquivStabilizer {f₀ f : A → V} (τ : Perm A) (hτ : f₀ ∘ τ = f) :
    {σ : Perm A // f₀ ∘ σ = f} ≃ {σ : Perm A // f₀ ∘ σ = f₀} where
  toFun σ := ⟨σ.1 * τ⁻¹, funext fun a => by
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    rw [show f₀ (σ.1 (τ⁻¹ a)) = f (τ⁻¹ a) from congrFun σ.2 _,
      show f (τ⁻¹ a) = f₀ (τ (τ⁻¹ a)) from (congrFun hτ _).symm]
    simp⟩
  invFun ρ := ⟨ρ.1 * τ, funext fun a => by
    simp only [Function.comp_apply, Equiv.Perm.mul_apply]
    rw [show f₀ (ρ.1 (τ a)) = f₀ (τ a) from congrFun ρ.2 _]
    exact congrFun hτ a⟩
  left_inv σ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

variable [DecidableEq A] [Fintype V]

/-- Every fibre of `σ ↦ f₀ ∘ σ` over a function with block sizes `m` has `∏ v, (m v)!`
elements. The stabiliser computation is Mathlib's `DomMulAct.stabilizer_card`. -/
theorem card_filter_comp_eq_prod_factorial {m : V → ℕ} {f₀ f : A → V}
    (hf₀ : BlockSizes m f₀) (hf : BlockSizes m f) :
    #(univ.filter fun σ : Perm A => f₀ ∘ σ = f) = ∏ v, (m v)! := by
  obtain ⟨τ, hτ⟩ := exists_perm_comp_eq hf hf₀
  rw [← Fintype.card_subtype, Fintype.card_congr (permFibreEquivStabilizer τ hτ),
    Fintype.card_subtype, ← Fintype.card_subtype (p := fun σ : Perm A => f₀ ∘ σ = f₀),
    DomMulAct.stabilizer_card f₀]
  exact Finset.prod_congr rfl fun v _ => by
    rw [← card_fibre_eq_card_subtype, hf₀ v]

/-- **The labelled-blocks count, in product form.** The number of ways to cut `A` into
blocks labelled by `V` with the block labelled `v` of size `m v`, times `∏ v, (m v)!`,
is `(#A)!`. -/
theorem card_blockFunctions_mul_prod_factorial {m : V → ℕ} (hm : ∑ v, m v = Fintype.card A) :
    #(blockFunctions A m) * ∏ v, (m v)! = (Fintype.card A)! := by
  obtain ⟨f₀, hf₀⟩ := exists_blockSizes (A := A) hm
  have hsum : #(univ : Finset (Perm A))
      = ∑ f ∈ blockFunctions A m, #(univ.filter fun σ : Perm A => f₀ ∘ σ = f) :=
    Finset.card_eq_sum_card_fiberwise fun σ _ => by
      simp only [Finset.mem_coe, mem_blockFunctions]
      exact blockSizes_comp σ hf₀
  rw [Finset.sum_congr rfl fun f hf =>
      card_filter_comp_eq_prod_factorial hf₀ (mem_blockFunctions.mp hf),
    Finset.sum_const, smul_eq_mul, Finset.card_univ, Fintype.card_perm] at hsum
  exact hsum.symm

/-- **The labelled-blocks count.** The number of functions `A → V` whose fibre over `v`
has exactly `m v` elements — equivalently, the number of partitions of `A` into blocks
labelled by `V` with prescribed block sizes `m` — is the multinomial coefficient
`(#A)! / ∏ v, (m v)!`.

This is the combinatorial interpretation of `Nat.multinomial` that Mathlib does not
provide; see the module docstring. It is the mathematical content of Theorem A of
`2026-10-06-ls-corollary-4-coupling.tex` (`arXiv:math/0202090`, Corollary 4). -/
theorem card_blockFunctions_eq_multinomial {m : V → ℕ} (hm : ∑ v, m v = Fintype.card A) :
    #(blockFunctions A m) = Nat.multinomial univ m := by
  have hpos : 0 < ∏ v, (m v)! := Finset.prod_pos fun _ _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [card_blockFunctions_mul_prod_factorial hm, mul_comm (Nat.multinomial univ m),
    Nat.multinomial_spec, hm]

end LabelledBlocks

end TworowD4Kernel
