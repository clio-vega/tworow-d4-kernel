/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.HeadExclusionRootsOfUnity

/-!
# Rows 3 and 4 of the type-dependence table are one `h`-substitution — and two different loci

Q534 (`memory/questions/2026-10-20-dream-ledger.md`, L50–L78) lists five independently
verified type-`B`/type-`C` differences and claims they are all the long/short-root exchange
`α ↦ 2α`, *"so every type-dependence is supported at `v = −1`"*.  This module measures the
cheapest arm of that claim: **row 3 against row 4**.

The two rows, as the paper states them:

* **row 3** — the head factor of `lem:typecompare`
  (`projects/proofs/2026-10-19-typeB-gauge-theorem.tex`, L352–L357): `(1-q)(v-1)` in type
  `B`, `(1-q)(v²-1)` in type `C`.
* **row 4** — the normalisation character `ψ_X(v) = (1 - q v^h)/(1 - q)` with `h_B = 1`,
  `h_C = 2` (abstract L45; `cor:rhoB` L523 states the type-`B` case `ψ_B(v) = (1-qv)/(1-q)`).

## Correction to the session brief, measured

`state/LEAN.md` attributes row 4 to `TworowD4Kernel.HeadExclusionRootsOfUnity` and calls row 3
*"not yet in Lean"*.  That is **backwards**.  `HeadExclusionRootsOfUnity.headFactor` is
`(1-q) * (v^h - 1)`, and its own docstring cites `lem:typecompare` L291 — it is **row 3**.
Row 4's `ψ_X` has numerator `1 - q v^h`, which is a different polynomial in `v`, and was
**not** in Lean before this module.  So the unification theorem had to be stated against a
freshly defined `psiNum`, not against the existing module's `headFactor`.

## What is proved, and what it says about Q534

1. **Unification (`headFactor_eq_row3Shape`, `psiNum_eq_row4Shape`, both `rfl`).**  Each row
   is a *type-independent shape* precomposed with the monomial `v ↦ v^h`.  The whole
   type-dependence of both rows is the exponent `h`, and `B`/`C` are `h = 1`/`h = 2` of one
   family.  No ring hypotheses at all: char-free, domain-free.  This is the half of Q534's
   claim that survives.

2. **The zero sets are NOT the same set — they are `Disjoint`**
   (`row3Locus_disjoint_row4Locus`).  Row 3 vanishes on the `h`-th roots of unity `{v^h = 1}`;
   row 4 vanishes on the `q`-shifted locus `{q v^h = 1}`.  A point of both forces `q = 1`,
   which is exactly the hypothesis every statement here excludes.  So the brief's step 2
   (*"prove row 3's zero set and row 4's firing locus are the same set"*) is not merely
   unproved: its two sides **meet nowhere**.  Rows 3 and 4 share the substitution, not the
   locus.

3. **The localisation holds for row 3 and only for row 3**
   (`boundaryLocus_two_sdiff_one`): `{v² = 1} \ {v = 1} = {-1}` in any domain with `-1 ≠ 1`.
   Row 4's analogue fails at the level of nesting, not just of size: `{q v = 1} = {q⁻¹}` is
   **not contained** in `{q v² = 1}` for `q ≠ 1` (`row4Locus_one_not_subset_two`), so row 4's
   two types are not even ordered, let alone separated by one point.

4. **Is `h = 1` vs `2` special, or the smallest instance?**  Both.  It is the smallest
   instance of a divisibility family (`boundaryLocus_subset_of_dvd`), and `h = 2` is the only
   exponent whose difference from `h = 1` is a single point *in every* domain with `-1 ≠ 1`.
   For `h > 2` the answer is a property of the ambient field, not of `h`: over `ZMod 7` the
   `h = 3` difference has **two** points (`control_h3_not_localised`), while over `ℚ` every
   odd `h` gives `∅` and every even `h` gives `{-1}` — the parity statement already proved in
   `HeadExclusionRootsOfUnity.pow_eq_pow_mod_two`.

## Honest scope

Row 3's head factor and row 4's `ψ` are formalised here as **abstract polynomials in one
variable `v` over a commutative ring**.  There is no `w`, no `Ã`, no `W^X`, no `E^X`, no
fixed-point set, no `LG(N,2N)`, and no root system.  Nothing below connects either row to the
weight functions it came from; `h` is an exponent and nothing else.  In particular:

* Not formalised: that `h_B = 1` and `h_C = 2` (a root-system input, `def:D`), carried in as
  the numerals `1` and `2`.
* Not formalised: that row 3's factor *is* the head factor of `T^X_σ`, or that row 4's `ψ`
  *is* the gauge that makes `Ã^B`'s collapse multiplier `1` (`cor:rhoB`).
* Not formalised: rows 1, 2 and 5 of Q534's table.  The `0/18`-vs-`6/6` census of
  `rem:measured` (L359–L364) is not re-run here.
* ⚠ Motegi's `h` (`RTVtheorem`, L4495) is the character scaling the cotangent fibres and is a
  **different object** that happens to share the letter.  It does not appear in this file.
-/

namespace TypeDependenceLocus

open HeadExclusionRootsOfUnity

variable {K : Type*} [CommRing K] {q v : K} {h h₁ h₂ : ℕ}

/-! ### The two shapes, and the one substitution -/

/-- The type-independent **shape** of row 3: `u ↦ (1-q)(u-1)`.  Row 3 is this precomposed
with `u = v^h`.  `lem:typecompare`, L352–L357. -/
def row3Shape (q u : K) : K := (1 - q) * (u - 1)

/-- The type-independent **shape** of row 4, as a numerator: `u ↦ 1 - q u`.  Row 4 is this
precomposed with `u = v^h`, divided by the nonzero scalar `1 - q`.  Abstract L45,
`cor:rhoB` L523. -/
def row4Shape (q u : K) : K := 1 - q * u

/-- Row 4's numerator `1 - q v^h`.  Type `B` is `h = 1`, type `C` is `h = 2`.  This is
**new to Lean**; the existing `HeadExclusionRootsOfUnity.headFactor` is row 3, not row 4. -/
def psiNum (q v : K) (h : ℕ) : K := 1 - q * v ^ h

/-- **Row 3 factors through the monomial `v ↦ v^h`.**  True by `rfl`: the type-dependence is
the exponent and nothing else. -/
theorem headFactor_eq_row3Shape (q v : K) (h : ℕ) :
    headFactor q v h = row3Shape q (v ^ h) := rfl

/-- **Row 4 factors through the same monomial `v ↦ v^h`.**  True by `rfl`. -/
theorem psiNum_eq_row4Shape (q v : K) (h : ℕ) :
    psiNum q v h = row4Shape q (v ^ h) := rfl

/-- **The unification theorem.**  Rows 3 and 4 are one `h`-substitution: there are two
type-independent shapes `row3Shape`, `row4Shape` such that *both* rows are that shape
evaluated at `v^h`.  So `B` vs `C` is `h = 1` vs `h = 2` of a single family in both rows,
rather than two coincidences.  Char-free and domain-free — no hypothesis is spent. -/
theorem rows_share_substitution (q v : K) (h : ℕ) :
    headFactor q v h = row3Shape q (v ^ h) ∧ psiNum q v h = row4Shape q (v ^ h) :=
  ⟨rfl, rfl⟩

/-! ### The four type specialisations -/

/-- Row 4, type `B` (`h = 1`): `cor:rhoB` L523, `ψ_B(v) = (1-qv)/(1-q)`. -/
theorem psiNum_one (q v : K) : psiNum q v 1 = 1 - q * v := by simp [psiNum]

/-- Row 4, type `C` (`h = 2`): abstract L45 at `h = 2`. -/
theorem psiNum_two (q v : K) : psiNum q v 2 = 1 - q * v ^ 2 := rfl

/-! ### The two zero loci -/

/-- The zero locus of row 3. -/
def row3Locus (q : K) (h : ℕ) : Set K := {v | headFactor q v h = 0}

/-- The zero locus of row 4. -/
def row4Locus (q : K) (h : ℕ) : Set K := {v | psiNum q v h = 0}

/-- Row 3 vanishes exactly on the `h`-th roots of unity — the boundary root hyperplane of
its own type.  This is `HeadExclusionRootsOfUnity.fires_iff_pow_eq_one` restated as sets. -/
theorem row3Locus_eq_boundaryLocus [IsDomain K] (hq : q ≠ 1) :
    row3Locus q h = boundaryLocus K h := by
  ext v
  exact fires_iff_pow_eq_one hq

/-- Row 4 vanishes exactly on the `q`-shifted locus `{q v^h = 1}`.  No hypothesis. -/
theorem mem_row4Locus_iff : v ∈ row4Locus q h ↔ q * v ^ h = 1 := by
  simp only [row4Locus, psiNum, Set.mem_setOf_eq]
  constructor
  · intro hf; linear_combination -hf
  · intro hf; linear_combination -hf

/-- **The measured answer to the brief's step 2.**  The two rows' zero sets are not the same
set; they are `Disjoint`.  A common point gives `v^h = 1` and `q v^h = 1`, hence `q = 1`.
Uniform in `h`, so this is not an artefact of `h ∈ {1,2}`. -/
theorem row3Locus_disjoint_row4Locus [IsDomain K] (hq : q ≠ 1) :
    Disjoint (row3Locus q h) (row4Locus q h) := by
  rw [Set.disjoint_left]
  intro v h3 h4
  rw [row3Locus_eq_boundaryLocus hq] at h3
  rw [mem_row4Locus_iff] at h4
  exact hq (by rw [← h4, (by exact h3 : v ^ h = 1), mul_one])

/-! ### Row 3 localises: the divisibility family and the single point -/

/-- `boundaryLocus` is monotone along divisibility: `h₁ ∣ h₂` gives `μ_{h₁} ⊆ μ_{h₂}`.
No hypothesis. -/
theorem boundaryLocus_subset_of_dvd (K : Type*) [CommRing K] (hd : h₁ ∣ h₂) :
    boundaryLocus K h₁ ⊆ boundaryLocus K h₂ := by
  obtain ⟨k, rfl⟩ := hd
  intro v hv
  simp only [boundaryLocus, Set.mem_setOf_eq] at hv ⊢
  rw [pow_mul, hv, one_pow]

/-- The type-`B` locus, named: `{v : v^1 = 1} = {1}`. -/
theorem boundaryLocus_one : boundaryLocus K 1 = {1} := by
  ext v; simp [boundaryLocus]

/-- **The localisation theorem.**  The row-3 difference between the types is supported on
exactly one point, `-1`.  Needs `-1 ≠ 1` and needs it here only. -/
theorem boundaryLocus_two_sdiff_one [IsDomain K] (hchar : (-1 : K) ≠ 1) :
    boundaryLocus K 2 \ boundaryLocus K 1 = {-1} := by
  have h2 : boundaryLocus K 2 = tauFixedLocus K := rfl
  rw [h2, tauFixedLocus_eq, boundaryLocus_one]
  ext v
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hv | hv, hne⟩
    · exact absurd hv hne
    · exact hv
  · rintro rfl
    exact ⟨Or.inr rfl, fun hv => hchar hv⟩

/-- **The general form.**  When `h₁ ∣ h₂` the symmetric difference of the two loci collapses
to the one-sided difference, because the smaller divides into the larger.  So the whole
`h₁`-versus-`h₂` type-dependence is the set of `h₂`-th roots of unity that are not `h₁`-th
roots.  `h₁ = 1, h₂ = 2` is the smallest instance. -/
theorem boundaryLocus_symmDiff_of_dvd (K : Type*) [CommRing K] (hd : h₁ ∣ h₂) :
    (boundaryLocus K h₂ \ boundaryLocus K h₁) ∪ (boundaryLocus K h₁ \ boundaryLocus K h₂)
      = boundaryLocus K h₂ \ boundaryLocus K h₁ := by
  have hsub := boundaryLocus_subset_of_dvd K hd
  rw [Set.diff_eq_empty.mpr hsub, Set.union_empty]

/-! ### Row 4 does not localise, and does not even nest -/

/-- Row 4's type-`B` locus, unfolded: `{v : q v = 1}` (the single point `q⁻¹` when `q ≠ 0`).
Lesion result: **both** `[IsDomain K]` and `q ≠ 0` are removable here — the identification of
the locus is a rewriting of the definition and spends nothing. -/
theorem row4Locus_one (q : K) : row4Locus q 1 = {v | q * v = 1} := by
  ext v; rw [mem_row4Locus_iff, pow_one]; rfl

/-- **Row 4 fails the nesting that row 3 satisfies.**  Over a field with `q ∉ {0, 1}` the
type-`B` point `q⁻¹` is *not* in the type-`C` locus: `q · (q⁻¹)² = q⁻¹ = 1` would force
`q = 1`.  So for row 4 the two types' loci are incomparable and there is no "difference
supported at one point" to measure — unlike row 3, whose `B` locus sits inside its `C`
locus. -/
theorem row4Locus_one_not_subset_two {F : Type*} [Field F] {q : F} (hq0 : q ≠ 0)
    (hq : q ≠ 1) : ¬ row4Locus q 1 ⊆ row4Locus q 2 := by
  intro hsub
  have hmem : q⁻¹ ∈ row4Locus q 1 := by
    rw [mem_row4Locus_iff, pow_one, mul_inv_cancel₀ hq0]
  have hC := hsub hmem
  rw [mem_row4Locus_iff] at hC
  apply hq
  field_simp at hC
  exact hC.symm

/-! ### `ψ_X` itself, with its denominator -/

section Field

variable {F : Type*} [Field F] {q v : F} {h : ℕ}

/-- Row 4 as the paper writes it: `ψ_X(v) = (1 - q v^h)/(1 - q)`.  Abstract L45. -/
def psi (q v : F) (h : ℕ) : F := (1 - q * v ^ h) / (1 - q)

/-- `ψ_B`, `cor:rhoB` L523. -/
theorem psi_one (q v : F) : psi q v 1 = (1 - q * v) / (1 - q) := by simp [psi]

/-- `ψ_C`, abstract L45 at `h = 2`. -/
theorem psi_two (q v : F) : psi q v 2 = (1 - q * v ^ 2) / (1 - q) := rfl

/-- The denominator is a red herring for the zero locus, exactly as `(1-q)` was for row 3
(`fires_iff_pow_eq_one`).  `q ≠ 1` is spent here, and it is **relocated**: it is already the
well-definedness hypothesis of `ψ_X` in the paper, which divides by `1 - q`. -/
theorem psi_eq_zero_iff (hq : q ≠ 1) : psi q v h = 0 ↔ psiNum q v h = 0 := by
  have hd : (1 : F) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  simp [psi, psiNum, div_eq_zero_iff, hd]

/-- `ψ` normalises to `1` at `v = 1` in **every** type — the fixed point the two types share.
This is why all three plants of `rem:plants` coincide with the truth at `+1` (L973). -/
theorem psi_at_one (hq : q ≠ 1) (h : ℕ) : psi q 1 h = 1 := by
  have hd : (1 : F) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  unfold psi
  rw [one_pow, mul_one, div_self hd]

/-- **Row 4's type-dependence isolated**, the `cor:ratio` shape (L635–L648):
`ψ_C(v)/ψ_B(v) = (1 - q v²)/(1 - q v)`.  The `(1-q)` cancels, so the ratio of the two types
is the ratio of the two numerators — the boxed `u`-diagonal block ratio of the paper. -/
theorem psi_two_div_psi_one (hq : q ≠ 1) :
    psi q v 2 / psi q v 1 = (1 - q * v ^ 2) / (1 - q * v) := by
  have hd : (1 : F) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  rw [psi_two, psi_one, div_div_div_cancel_right₀]
  exact hd

end Field

/-! ### Controls and the lesion register

Each lesion is settled by an explicit witness, not by a failed build: a failed build grades
the edit, a witness grades the statement. -/

section Controls

/-- **`q ≠ 1` is IRREMOVABLE from `row3Locus_disjoint_row4Locus`** (pre-registered
irremovable).  At `q = 1` row 3's factor is identically `0`, so its locus is everything, and
`v = 1` lies in both loci. -/
theorem lesion_hq_disjoint : ¬ Disjoint (row3Locus (1 : ℚ) 1) (row4Locus (1 : ℚ) 1) := by
  rw [Set.not_disjoint_iff]
  refine ⟨1, ?_, ?_⟩
  · simp [row3Locus, headFactor]
  · simp [row4Locus, psiNum]

/-- **`(-1) ≠ 1` is IRREMOVABLE from `boundaryLocus_two_sdiff_one`** (pre-registered
irremovable), and this is the positive control: in characteristic `2` the difference is
`∅`, not `{-1}`, because the two loci coincide. -/
theorem lesion_hchar_charTwo :
    boundaryLocus (ZMod 2) 2 \ boundaryLocus (ZMod 2) 1 = (∅ : Set (ZMod 2)) := by
  ext v
  simp only [boundaryLocus, Set.mem_diff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
    not_and, not_not]
  revert v
  decide

/-- **`(-1) ≠ 1` is REMOVABLE from the unification theorem** (pre-registered removable):
`rows_share_substitution` holds over `ZMod 2`, where `-1 = 1`.  The type-dependence of the
*shapes* survives the collapse that kills the *separation*. -/
theorem lesion_hchar_removable_from_unification (q v : ZMod 2) (h : ℕ) :
    headFactor q v h = row3Shape q (v ^ h) ∧ psiNum q v h = row4Shape q (v ^ h) :=
  rows_share_substitution q v h

/-- **`h = 2` is special, not merely smallest.**  Over `ZMod 7` the `h = 3` difference has
**two** points, `2` and `4` — the primitive cube roots of `1` mod `7`.  So "the difference
is a single point" is a statement about `h = 2`, not about the divisibility family. -/
theorem control_h3_not_localised :
    boundaryLocus (ZMod 7) 3 \ boundaryLocus (ZMod 7) 1 = ({2, 4} : Set (ZMod 7)) := by
  ext v
  simp only [boundaryLocus, Set.mem_diff, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  revert v
  decide

/-- The same ambient at `h = 2`: one point, `6 = -1`.  The positive control that
`control_h3_not_localised` is measuring `h` and not `ZMod 7`. -/
theorem control_h2_localised_zmod7 :
    boundaryLocus (ZMod 7) 2 \ boundaryLocus (ZMod 7) 1 = ({6} : Set (ZMod 7)) := by
  ext v
  simp only [boundaryLocus, Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
  revert v
  decide

/-- Row 3 over `ℚ`, both types, and the single-point difference. -/
theorem control_row3_sdiff_rat :
    boundaryLocus ℚ 2 \ boundaryLocus ℚ 1 = ({-1} : Set ℚ) :=
  boundaryLocus_two_sdiff_one (by norm_num)

/-- **Row 4's two types are incomparable, instantiated.**  Over `ℚ` at `q = 4`: type `B`'s
locus is `{1/4}`, type `C`'s is `{±1/2}`, both nonempty and neither contained in the other.
Contrast row 3, whose type-`B` locus always sits *inside* its type-`C` locus
(`boundaryLocus_subset_of_dvd`).  This is the concrete form of
`row4Locus_one_not_subset_two`. -/
theorem control_row4_not_nested_rat :
    (1 / 4 : ℚ) ∈ row4Locus (4 : ℚ) 1 ∧ (1 / 4 : ℚ) ∉ row4Locus (4 : ℚ) 2 ∧
      (1 / 2 : ℚ) ∈ row4Locus (4 : ℚ) 2 ∧ (1 / 2 : ℚ) ∉ row4Locus (4 : ℚ) 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mem_row4Locus_iff]; norm_num
  · rw [mem_row4Locus_iff]; norm_num
  · rw [mem_row4Locus_iff]; norm_num
  · rw [mem_row4Locus_iff]; norm_num

/-- Row 3 at the same `q`, for contrast: its two loci **are** nested, in every ring. -/
theorem control_row3_nested (K : Type*) [CommRing K] :
    boundaryLocus K 1 ⊆ boundaryLocus K 2 :=
  boundaryLocus_subset_of_dvd K (one_dvd 2)

/-- The two rows meet nowhere, instantiated: `1 ∈ row3Locus`, `1 ∉ row4Locus` over `ℚ`. -/
theorem control_disjoint_rat : Disjoint (row3Locus (0 : ℚ) 2) (row4Locus (0 : ℚ) 2) :=
  row3Locus_disjoint_row4Locus (by norm_num)

end Controls

end TypeDependenceLocus
