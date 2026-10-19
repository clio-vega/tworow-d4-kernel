/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Head exclusion fires exactly at the type's own roots of unity

Formalises Corollary `cor:domain` of
`projects/proofs/2026-10-19-typeB-gauge-theorem.tex` (Clio, 19 Oct 2026, L727–L752),
together with the arithmetic half of its part (1) (the "G2 is not luck" clause).

## The paper's statement

> In type `X` the `τ`-fixed points at which head exclusion fires are exactly the
> `h_X`-th roots of unity: `{±1}` for `h = 2` (type `C`), `{+1}` for `h = 1`
> (type `B`).  These are exactly the points of the boundary root hyperplane
> `{w_m^h = 1}` of that type.

The two inputs, both read off `lem:typecompare` (L278–L296, boxed display at L291):

* the **type-`C`** head factor at a slot is `(1 - q)(v² - 1)`;
* the **type-`B`** head factor at a slot is `(1 - q)(v - 1)`.

So the uniform object is `(1 - q)(v^h - 1)` with `h = h_X`, and `h_B = 1`, `h_C = 2`.
A `τ`-fixed point is one with `v² = 1` (`lem:head`(b), L352–L360).

## What `h` is, and why Lean is evidence about it

`rem:h` (L805–L818) retracts the gloss "`h` = the length of the boundary root" from
`2026-10-17-typeB` `thm:rhoB`: `|2e_m|² = 4` and `|e_m|² = 1`, neither of which is `h`.
`h` is the exponent in the boundary character `w_m^h`, and it enters the head factor
*as an exponent*.  Below, `h : ℕ` is a genuine parameter of every statement: Lean will
not let a type dependence be smuggled into it, so the `h`-uniformity of the paper's
`ρ^α` formula is **exhibited** here rather than asserted.  The type-`B` and type-`C`
clauses are literally `h = 1` and `h = 2` of one theorem.

## What the sharpening is

The paper's own headline (`cor:domain`, and `rem:whatsnew` L770–L775) is that each
type's theorem is cut out by that type's own root system and reaches no further.
Formalised, the mechanism turns out to be **parity of `h` alone**
(`tauFiring_of_odd`, `tauFiring_of_even`): on the `τ`-fixed locus, `v^h = v^(h % 2)`.
Type `B`/`C` are the two parity classes at their smallest representatives.

## Honest scope

* Not formalised: that the boundary root of `B_N` is `e_m` and of `C_N` is `2e_m`,
  hence `h_B = 1`, `h_C = 2`.  That is a root-system input (`def:D`), carried in here
  as the numerals `1` and `2`.  Part (1) of `cor:domain` — "every root hyperplane of
  `B_N` delivers an admissible `D`, so G2 is untouched" — is formalised only in its
  arithmetic half, `neg_one_notMem_boundaryLocus_one`: `-1` is not a point of
  `{w^1 = 1}`.  The root-system half (that `{w_m = -1}` is not a root hyperplane of
  `B_N`) is *not* formalised.
* Not formalised: `lem:head` itself (the vanishing of `T^B_σ`), which needs the
  six-line `T`-operator.  What is here is the head **factor**'s zero locus, which is
  `lem:head`(b)'s discriminator and all of `cor:domain`'s content.
* The ambient ring is `CommRing` + `IsDomain`, not `Field`: nothing below inverts
  anything.  See the lesion register in the session note.

## External results this corollary is positioned against

`cor:domain`(2) claims content beyond Motegi's stability proposition, **not** a
re-proof of it.  The external anchors, cited for the record and *not* formalised:

* Motegi, arXiv:**2610.15344**, `stabilityWC` — the type-`C` stability statement, which
  is stated at `u_n = 1` only; `cor:domain`(2) observes that the type-`C` firing locus
  also contains the component `{w_m = -1}`.
* Motegi, arXiv:**2610.15344**, `normalizedsusythree`, L2767–L2771 — the type-`B` pair
  specialisation, read first-hand in `sec:priority` of the citing `.tex`.

The root-system facts behind `h_B = 1` and `h_C = 2` (boundary root `e_m` in `B_N`,
`2e_m` in `C_N`) enter below as the numerals `1` and `2`; `rem:h` (L805) is the
retraction of the gloss that `h` is a root length.
-/

namespace HeadExclusionRootsOfUnity

variable {K : Type*} [CommRing K] {q v : K} {h : ℕ}

/-- The head factor of a head slot carrying the value `v`, uniformly in the boundary
exponent `h`.  `lem:typecompare` (L291): `(1-q)(v-1)` in type `B` (`h = 1`),
`(1-q)(v²-1)` in type `C` (`h = 2`). -/
def headFactor (q v : K) (h : ℕ) : K := (1 - q) * (v ^ h - 1)

/-- `v` is a `τ`-fixed point: `lem:head`(b), L354, "a `τ`-fixed point has `u_p² = 1`". -/
def IsTauFixed (v : K) : Prop := v ^ 2 = 1

/-- Head exclusion **fires** at `v` when the head factor vanishes there. -/
def Fires (q v : K) (h : ℕ) : Prop := headFactor q v h = 0

/-- The boundary root hyperplane of the type with exponent `h`, as a locus in the
boundary character (`def:D`): `{w_m^h = 1}`. -/
def boundaryLocus (K : Type*) [CommRing K] (h : ℕ) : Set K := {w | w ^ h = 1}

/-- The `τ`-fixed locus. -/
def tauFixedLocus (K : Type*) [CommRing K] : Set K := {v | v ^ 2 = 1}

/-- The set of `τ`-fixed points at which type-`h` head exclusion fires. -/
def tauFiring (q : K) (h : ℕ) : Set K := {v | IsTauFixed v ∧ Fires q v h}

/-! ### The two type specialisations of the head factor -/

/-- Type `B`: `h = 1`.  `lem:typecompare`, boxed display L291. -/
theorem headFactor_one (q v : K) : headFactor q v 1 = (1 - q) * (v - 1) := by
  simp [headFactor]

/-- Type `C`: `h = 2`.  `lem:typecompare`, L289. -/
theorem headFactor_two (q v : K) : headFactor q v 2 = (1 - q) * (v ^ 2 - 1) := by
  simp [headFactor]

/-! ### Firing is exactly "`v` is an `h`-th root of unity" -/

/-- The prefactor `(1-q)` is a red herring: firing is a condition on `v` alone.
Hypothesis `q ≠ 1` is spent here and nowhere else. -/
theorem fires_iff_pow_eq_one [IsDomain K] (hq : q ≠ 1) : Fires q v h ↔ v ^ h = 1 := by
  unfold Fires headFactor
  constructor
  · intro hf
    rcases mul_eq_zero.mp hf with h1 | h2
    · exact absurd (eq_of_sub_eq_zero h1).symm hq
    · exact eq_of_sub_eq_zero h2
  · intro hv
    rw [hv, sub_self, mul_zero]

/-- `cor:domain`, the displayed identification: the firing `τ`-fixed points are
exactly `{v² = 1} ∩ {v^h = 1}`, the intersection of the `τ`-fixed locus with the
boundary root hyperplane of that type. -/
theorem tauFiring_eq_inter [IsDomain K] (hq : q ≠ 1) :
    tauFiring q h = tauFixedLocus K ∩ boundaryLocus K h := by
  ext v
  simp only [tauFiring, tauFixedLocus, boundaryLocus, IsTauFixed, Set.mem_setOf_eq,
    Set.mem_inter_iff]
  exact and_congr_right fun _ => fires_iff_pow_eq_one hq

/-! ### On the `τ`-fixed locus the exponent matters only mod 2 -/

/-- `v² = 1` reduces every exponent mod `2`. -/
theorem pow_eq_pow_mod_two (hv : IsTauFixed v) (h : ℕ) : v ^ h = v ^ (h % 2) := by
  conv_lhs => rw [← Nat.div_add_mod h 2]
  rw [pow_add, pow_mul, hv, one_pow, one_mul]

theorem pow_eq_one_of_even (hv : IsTauFixed v) (he : Even h) : v ^ h = 1 := by
  rw [pow_eq_pow_mod_two hv, Nat.even_iff.mp he, pow_zero]

theorem pow_eq_self_of_odd (hv : IsTauFixed v) (ho : Odd h) : v ^ h = v := by
  rw [pow_eq_pow_mod_two hv, Nat.odd_iff.mp ho, pow_one]

/-- **The pointwise form of `cor:domain`.**  At a `τ`-fixed point, head exclusion
fires iff the boundary exponent is even or the point is `+1`.  Type `C` (`h = 2`,
even) fires at both `τ`-fixed points; type `B` (`h = 1`, odd) only at `+1`. -/
theorem fires_at_tauFixed_iff [IsDomain K] (hq : q ≠ 1) (hv : IsTauFixed v) :
    Fires q v h ↔ (Even h ∨ v = 1) := by
  rw [fires_iff_pow_eq_one hq]
  constructor
  · intro hvh
    rcases Nat.even_or_odd h with he | ho
    · exact Or.inl he
    · exact Or.inr (by rw [← pow_eq_self_of_odd hv ho]; exact hvh)
  · rintro (he | rfl)
    · exact pow_eq_one_of_even hv he
    · exact one_pow h

/-! ### The two arms, as sets -/

/-- **Odd `h` (type `B` is `h = 1`): head exclusion fires at `+1` only.** -/
theorem tauFiring_of_odd [IsDomain K] (hq : q ≠ 1) (ho : Odd h) :
    tauFiring q h = ({1} : Set K) := by
  ext v
  simp only [tauFiring, IsTauFixed, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hv, hf⟩
    rcases (fires_at_tauFixed_iff hq hv).mp hf with he | h1
    · exact absurd he (Nat.not_even_iff_odd.mpr ho)
    · exact h1
  · rintro rfl
    refine ⟨one_pow 2, ?_⟩
    exact (fires_at_tauFixed_iff hq (one_pow 2)).mpr (Or.inr rfl)

/-- **Even `h` (type `C` is `h = 2`): head exclusion fires at every `τ`-fixed point.** -/
theorem tauFiring_of_even [IsDomain K] (hq : q ≠ 1) (he : Even h) :
    tauFiring q h = tauFixedLocus K := by
  ext v
  simp only [tauFiring, tauFixedLocus, IsTauFixed, Set.mem_setOf_eq]
  exact ⟨fun hx => hx.1, fun hv => ⟨hv, (fires_at_tauFixed_iff hq hv).mpr (Or.inl he)⟩⟩

/-- Type `B`, named. -/
theorem tauFiring_typeB [IsDomain K] (hq : q ≠ 1) : tauFiring q 1 = ({1} : Set K) :=
  tauFiring_of_odd hq odd_one

/-- Type `C`, named. -/
theorem tauFiring_typeC [IsDomain K] (hq : q ≠ 1) : tauFiring q 2 = tauFixedLocus K :=
  tauFiring_of_even hq (even_two)

/-- The `τ`-fixed locus is `{1, -1}` — in **any** domain.  No characteristic
hypothesis: in characteristic `2` the right-hand side is a one-element set written
with two names. -/
theorem tauFixedLocus_eq [IsDomain K] : tauFixedLocus K = {1, -1} := by
  ext v
  simp only [tauFixedLocus, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hv
    have : (v - 1) * (v + 1) = 0 := by ring_nf; linear_combination hv
    rcases mul_eq_zero.mp this with h1 | h2
    · exact Or.inl (eq_of_sub_eq_zero h1)
    · exact Or.inr (by linear_combination h2)
  · rintro (rfl | rfl)
    · exact one_pow 2
    · exact neg_one_sq

/-! ### The sharp control pair: where the characteristic hypothesis is spent -/

/-- **Type `B`'s locus is strictly smaller than type `C`'s** — this is the statement
"the type-`B` theorem reaches no `τ`-fixed point beyond its own root system"
(`cor:domain`(2)).  The witness of strictness is `-1`, and this is the **only**
declaration in the file that needs `-1 ≠ 1`. -/
theorem tauFiring_typeB_ssubset_typeC [IsDomain K] (hq : q ≠ 1) (hchar : (-1 : K) ≠ 1) :
    tauFiring q 1 ⊂ tauFiring q (2 : ℕ) := by
  have hsub : tauFiring q 1 ⊆ tauFiring q (2 : ℕ) := by
    rw [tauFiring_typeB hq, tauFiring_typeC hq]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact one_pow 2
  rw [Set.ssubset_iff_of_subset hsub]
  refine ⟨-1, ?_, ?_⟩
  · rw [tauFiring_typeC hq]; exact neg_one_sq
  · rw [tauFiring_typeB hq, Set.mem_singleton_iff]; exact hchar

/-- **The positive control for the characteristic hypothesis.**  In characteristic `2`
the two arms coincide: `+1 = -1`, the `τ`-fixed locus is a single point, and the whole
distinction this corollary is about collapses.  So `hchar` above is irremovable, and
this is a *proof* of that rather than a failed search for a counterexample. -/
theorem tauFiring_typeB_eq_typeC_of_charTwo [IsDomain K] [CharP K 2] (hq : q ≠ 1) :
    tauFiring q 1 = tauFiring q (2 : ℕ) := by
  have hneg : (-1 : K) = 1 := by
    have : (2 : K) = 0 := by
      simpa using (CharP.cast_eq_zero K 2)
    linear_combination -this
  rw [tauFiring_typeB hq, tauFiring_typeC hq, tauFixedLocus_eq, hneg]
  simp

/-! ### The "G2 is not luck" clause, arithmetic half -/

/-- `cor:domain`(1), arithmetic half: `-1` is not a point of the type-`B` boundary
root hyperplane `{w^1 = 1}`.  The paper's reading: `{w_m = -1}` is simply not a root
hyperplane of `B_N`, so G2's admissible `D` is untouched — that is not luck, it is the
same fact as `h_B` being odd. -/
theorem neg_one_notMem_boundaryLocus_one (hchar : (-1 : K) ≠ 1) :
    (-1 : K) ∉ boundaryLocus K 1 := by
  simpa [boundaryLocus] using hchar

/-- And `-1` **is** a point of the type-`C` boundary root hyperplane `{w² = 1}` — the
second component, which is a root hyperplane there.  No hypothesis at all. -/
theorem neg_one_mem_boundaryLocus_two : (-1 : K) ∈ boundaryLocus K 2 :=
  neg_one_sq

/-! ### Concrete instantiations (non-degeneracy of the hypotheses)

Both arms are inhabited by an actual ring, so neither theorem is an empty domain
wearing its clothes.  Compare the 10-17 finding that over `𝔽₂` the pair
`q ≠ 0 ∧ 1 - q ≠ 0` is unsatisfiable: the hypothesis used here is only `q ≠ 1`,
which `q = 0` satisfies in every ring with `1 ≠ 0`. -/

section Controls

/-- `ZMod 2` is a field, but the `Fact` instance has to be in scope for `IsDomain
(ZMod 2)` to be found when the *statement* below is elaborated. -/
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem control_typeB_rat : tauFiring (0 : ℚ) 1 = ({1} : Set ℚ) :=
  tauFiring_typeB (by norm_num)

theorem control_typeC_rat : tauFiring (0 : ℚ) 2 = tauFixedLocus ℚ :=
  tauFiring_typeC (by norm_num)

theorem control_ssubset_rat : tauFiring (0 : ℚ) 1 ⊂ tauFiring (0 : ℚ) (2 : ℕ) :=
  tauFiring_typeB_ssubset_typeC (by norm_num) (by norm_num)

/-- The char-2 arm, instantiated: over `ZMod 2` the two types' loci are equal. -/
theorem control_collapse_zmod2 : tauFiring (0 : ZMod 2) 1 = tauFiring (0 : ZMod 2) (2 : ℕ) :=
  tauFiring_typeB_eq_typeC_of_charTwo (by decide)

/-- `-1` fires in type `C` and does not fire in type `B`: the measured `9/9` split of
`rem:measured` (L359–L364), as a theorem over `ℚ`. -/
theorem control_neg_one_mem_typeC : (-1 : ℚ) ∈ tauFiring (0 : ℚ) (2 : ℕ) := by
  rw [tauFiring_typeC (by norm_num)]; exact neg_one_sq

theorem control_neg_one_notMem_typeB : (-1 : ℚ) ∉ tauFiring (0 : ℚ) 1 := by
  rw [tauFiring_typeB (by norm_num)]; norm_num

/-- The head factor itself at `v = -1`: `-2` in type `B` (`lem:head`'s "equals `-2`
at `u_p = -1`", L358), `0` in type `C`. -/
theorem control_headFactor_typeB_at_neg_one : headFactor (0 : ℚ) (-1) 1 = -2 := by
  norm_num [headFactor]

theorem control_headFactor_typeC_at_neg_one : headFactor (0 : ℚ) (-1) 2 = 0 := by
  norm_num [headFactor]

/-! #### Positive controls for the three irremovable hypotheses

Each lesion is settled by an explicit witness rather than by a failed build: a failed
build grades the edit, a witness grades the statement.  (10-17: five of six
delete-and-rebuild lesions failed with `Unknown identifier`, which measures nothing.) -/

/-- `q ≠ 1` is **irremovable** from `fires_iff_pow_eq_one`: at `q = 1` the prefactor
kills the head factor and firing says nothing about `v`. -/
theorem lesion_hq : Fires (1 : ℚ) 2 1 ∧ (2 : ℚ) ^ (1 : ℕ) ≠ 1 := by
  refine ⟨?_, by norm_num⟩
  norm_num [Fires, headFactor]

/-- `IsTauFixed v` is **irremovable** from `fires_at_tauFixed_iff`: at `v = 2`, `h = 2`
the exponent is even and head exclusion does not fire. -/
theorem lesion_tauFixed : ¬ Fires (0 : ℚ) 2 2 ∧ Even 2 ∧ ¬ IsTauFixed (2 : ℚ) := by
  refine ⟨?_, even_two, ?_⟩
  · norm_num [Fires, headFactor]
  · norm_num [IsTauFixed]

/-- `[IsDomain K]` is **irremovable** from `fires_iff_pow_eq_one`: over `ZMod 6`
(`q = 3 ≠ 1`) the head factor vanishes at `v = 2`, which is not a square root of `1`.
Both factors are nonzero and their product is `12 = 0`. -/
theorem lesion_isDomain :
    headFactor (3 : ZMod 6) 2 2 = 0 ∧ (2 : ZMod 6) ^ 2 ≠ 1 ∧ (3 : ZMod 6) ≠ 1 := by
  refine ⟨by decide, by decide, by decide⟩

/-- `h ≥ 1` is **removable**, and this is the `h`-uniformity statement: the degenerate
exponent `h = 0` is an even exponent and the even clause covers it, firing everywhere
on the `τ`-fixed locus. -/
theorem lesion_h_pos (hq : q ≠ 1) [IsDomain K] : tauFiring q 0 = tauFixedLocus K :=
  tauFiring_of_even hq (by decide)

/-- `v ≠ 0` is **absent and vacuously satisfied**: `0` is never `τ`-fixed, so the
`Fˣ`-valuedness of `def:iota` is not spent in `cor:domain`. -/
theorem lesion_v_ne_zero : (0 : ℚ) ∉ tauFixedLocus ℚ := by
  norm_num [tauFixedLocus]

end Controls

end HeadExclusionRootsOfUnity
