/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Choose.Sum

/-!
# The prefix sign sum `N(S̄)`

Formalises the combinatorial heart of Q85, `proofs/2026-09-05-Q85-literal-gcd.tex`,
Proposition `prop:N` (§"The prefix sign sum").

## The objects

Expanding the nested bracket `[A₁,[A₂,[…,[A_{k-1},A_k]…]]]` into words produces exactly the
permutations of `[k] = {1,…,k}` that are **unimodal with peak `k`** — increasing up to the
letter `k` and decreasing after it — each once, with sign `(-1)^(q-1)` where `q` is the number
of letters at or before the peak (`lem:sign` of the source, itself Q81).

Such a word is determined by the set `T ⊆ [k-1]` of letters *strictly before* the peak:

  `ρ_T = (T ascending, k, ([k-1] \ T) descending)`,  `ε(ρ_T) = (-1)^|T|`.

**Only `ρ_T` is defined here** (`rho`), and only `(-1)^|T|` is used as the sign (`wordSign`).
The `(-1)^(q-1)` gloss is then a *lemma*, not a second definition: `rho_getElem_peak` says the
peak sits at 0-based index `|T|`, i.e. `q = |T| + 1`, so `(-1)^(q-1) = (-1)^|T|`. Writing both
formulas as definitions and hoping they agree is exactly the failure mode that
`a-true-lemma-can-have-a-false-gloss` records.

Everything here is computable: words are `List ℕ`, subsets are `Finset ℕ`, the sum is over a
`Finset.powerset`. So the file is exercised by `#guard` in `TworowD4KernelTests`, not only by
`lake build` — the coverage gap recorded as the registry node `Q83-lean-coverage-limit`
(`Polynomial ℤ` is `noncomputable`) does not apply.
-/

namespace TworowD4Kernel

open Finset

variable {k : ℕ} {T S : Finset ℕ}

/-- `ascList k T`: the elements of `T` in increasing order, for `T ⊆ {0,…,k-1}`.

Deliberately **not** `Finset.sort`. `Finset.sort` goes through `List.mergeSort`, which is
compiled to `WellFounded.fix`, so the kernel cannot reduce it and `decide` gets stuck on any
proposition mentioning it. `List.range` and `List.filter` are structurally recursive, so this
version reduces — which is what makes `prefixSignSum_eq_three` etc. provable by `decide`
rather than by `native_decide` (whose extra axiom is outside the allowlist). -/
def ascList (k : ℕ) (T : Finset ℕ) : List ℕ := (List.range k).filter (fun x => x ∈ T)

/-- `descentSet k T`: the letters of `[k-1]` that come *after* the peak in `ρ_T`. -/
def descentSet (k : ℕ) (T : Finset ℕ) : Finset ℕ := Icc 1 (k - 1) \ T

/-- `rho k T = ρ_T`: the unimodal word with peak `k` whose letters strictly before the peak
are exactly `T`, ascending, followed by `k`, followed by `[k-1] \ T` descending.
Source: `2026-09-05-Q85-literal-gcd.tex`, eq. `(eq:rhoT)`. -/
def rho (k : ℕ) (T : Finset ℕ) : List ℕ :=
  ascList k T ++ k :: (ascList k (descentSet k T)).reverse

/-- `ε(ρ_T) = (-1)^|T|`. See `rho_getElem_peak` for the equality with the source's
`(-1)^(q-1)`, `q` = number of letters at or before the peak. -/
def wordSign (T : Finset ℕ) : ℤ := (-1) ^ T.card

/-- `N(S̄)`: the signed count of unimodal words with peak `k` whose length-`|S̄|` time-prefix
has letter set exactly `S̄`. Source: `2026-09-05-Q85-literal-gcd.tex`, eq. `(eq:Ndef)`. -/
def prefixSignSum (k : ℕ) (S : Finset ℕ) : ℤ :=
  ∑ T ∈ (Icc 1 (k - 1)).powerset,
    if ((rho k T).take S.card).toFinset = S then wordSign T else 0

/-- The right-hand side of `prop:N`. -/
def prefixSignSumRHS (k : ℕ) (S : Finset ℕ) : ℤ :=
  if k - 1 ∈ S ∧ k ∉ S then (-1) ^ S.card
  else if k ∈ S ∧ k - 1 ∉ S then (-1) ^ (S.card - 1)
  else 0

/-! ## `ascList` really is the ascending enumeration -/

theorem ascList_nodup (k : ℕ) (T : Finset ℕ) : (ascList k T).Nodup :=
  (List.nodup_range).filter _

/-- `ascList k T` is strictly increasing: this is what makes it *the* ascending enumeration,
and it is manifest because `List.range` is. -/
theorem ascList_pairwise_lt (k : ℕ) (T : Finset ℕ) : (ascList k T).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

theorem mem_ascList {x : ℕ} (hT : T ⊆ range k) : x ∈ ascList k T ↔ x ∈ T := by
  simp only [ascList, List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨mem_range.mp (hT h), h⟩⟩

theorem ascList_toFinset (hT : T ⊆ range k) : (ascList k T).toFinset = T := by
  ext x; simpa using mem_ascList hT

theorem ascList_length (hT : T ⊆ range k) : (ascList k T).length = T.card := by
  have h := List.toFinset_card_of_nodup (ascList_nodup k T)
  rw [ascList_toFinset hT] at h
  exact h.symm

/-! ## The gloss: `(-1)^(q-1) = (-1)^|T|`, and `ρ_T` really is a word on `[k]` -/

theorem Icc_one_sub_subset_range (k : ℕ) : Icc 1 (k - 1) ⊆ range k := by
  intro x hx
  rw [mem_Icc] at hx
  rw [mem_range]
  omega

theorem descentSet_subset_range (k : ℕ) (T : Finset ℕ) : descentSet k T ⊆ range k :=
  (sdiff_subset).trans (Icc_one_sub_subset_range k)

/-- The peak `k` of `ρ_T` sits at 0-based index `|T|`. Hence the number `q` of letters at or
before the peak is `|T| + 1`, and the source's sign `(-1)^(q-1)` is `wordSign T = (-1)^|T|`.
This is the lemma the file's docstring promises: one definition, the other derived. -/
theorem rho_getElem_peak (hT : T ⊆ range k) : (rho k T)[T.card]? = some k := by
  unfold rho
  rw [List.getElem?_append_right (by rw [ascList_length hT])]
  simp [ascList_length hT]

/-- `ρ_T` has `k` letters. -/
theorem rho_length (hT : T ⊆ Icc 1 (k - 1)) : (rho k T).length = k - 1 + 1 := by
  have h := Finset.card_sdiff_add_card_eq_card hT
  rw [Nat.card_Icc] at h
  unfold rho
  rw [List.length_append, List.length_cons, List.length_reverse,
    ascList_length (hT.trans (Icc_one_sub_subset_range k)),
    ascList_length (descentSet_subset_range k T)]
  unfold descentSet
  omega

/-- Every letter of `[k]` occurs in `ρ_T`, and no other. -/
theorem rho_toFinset (hT : T ⊆ Icc 1 (k - 1)) :
    (rho k T).toFinset = insert k (Icc 1 (k - 1)) := by
  have hTr := hT.trans (Icc_one_sub_subset_range k)
  unfold rho
  ext x
  simp only [List.mem_toFinset, List.mem_append, List.mem_cons, List.mem_reverse,
    mem_ascList hTr, mem_ascList (descentSet_subset_range k T)]
  simp only [descentSet, Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro (h | rfl | ⟨h, -⟩)
    · exact Or.inr (hT h)
    · exact Or.inl rfl
    · exact Or.inr h
  · rintro (rfl | h)
    · exact Or.inr (Or.inl rfl)
    · by_cases hx : x ∈ T
      · exact Or.inl hx
      · exact Or.inr (Or.inr ⟨h, hx⟩)

/-! ## `prop:N` at small `k`, by kernel computation -/

/-- `prop:N` for `k = 3`, by exhaustive computation over the seven nonempty `S̄ ⊆ [3]`. -/
theorem prefixSignSum_eq_three (S : Finset ℕ) (hS : S ⊆ Icc 1 3) (hne : S ≠ ∅) :
    prefixSignSum 3 S = prefixSignSumRHS 3 S := by
  revert hS hne
  revert S
  decide

/-- `prop:N` for `k = 4`. Includes both vanishing branches (`S̄ ⊇ {3,4}` and `S̄ ∩ {3,4} = ∅`)
and both nonvanishing ones. -/
theorem prefixSignSum_eq_four (S : Finset ℕ) (hS : S ⊆ Icc 1 4) (hne : S ≠ ∅) :
    prefixSignSum 4 S = prefixSignSumRHS 4 S := by
  revert hS hne; revert S; decide

/-- `prop:N` for `k = 5`. -/
theorem prefixSignSum_eq_five (S : Finset ℕ) (hS : S ⊆ Icc 1 5) (hne : S ≠ ∅) :
    prefixSignSum 5 S = prefixSignSumRHS 5 S := by
  revert hS hne; revert S; decide

-- `k = 6` is **not** here: `decide` hits `maxRecDepth` on the 64 subsets. It is covered by
-- `#guard` in `TworowD4KernelTests` instead, which uses the compiled evaluator.

/-! ## The prefix of an ascending enumeration is an initial segment

This is the general-`k` lemma that `prefixSignSum_eq_three/_four/_five` sidestep by `decide`.
-/

/-- **Uniqueness of initial segments.** Two subsets of `T` of the same size, each of which lies
strictly below its complement in `T`, are equal. No sortedness is involved: this is pure order
combinatorics on `Finset ℕ`, and it is what upgrades the descriptive characterisation below
from "the prefix has this property" to "the prefix is the *unique* set with this property". -/
theorem eq_of_lt_sdiff {T S S' : Finset ℕ} (hS : S ⊆ T) (hS' : S' ⊆ T)
    (hcard : S.card = S'.card)
    (hsep : ∀ x ∈ S, ∀ y ∈ T \ S, x < y) (hsep' : ∀ x ∈ S', ∀ y ∈ T \ S', x < y) :
    S = S' := by
  by_contra hne
  -- If either were contained in the other, equal cardinality would force equality.
  obtain ⟨x, hxS, hxS'⟩ : ∃ x ∈ S, x ∉ S' :=
    Finset.not_subset.mp fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge)
  obtain ⟨y, hyS', hyS⟩ : ∃ y ∈ S', y ∉ S :=
    Finset.not_subset.mp fun h => hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
  -- `x` precedes everything outside `S`, in particular `y`; and symmetrically.
  have h1 : x < y := hsep x hxS y (Finset.mem_sdiff.mpr ⟨hS' hyS', hyS⟩)
  have h2 : y < x := hsep' y hyS' x (Finset.mem_sdiff.mpr ⟨hS hxS, hxS'⟩)
  exact absurd h1 (asymm h2)

/-- The length-`r` prefix of `ascList k T` *is* an initial segment of `T`: it is contained in
`T`, has `r` elements, and lies strictly below the rest of `T`. -/
theorem take_ascList_spec {r : ℕ} (hT : T ⊆ range k) (hr : r ≤ T.card) :
    ((ascList k T).take r).toFinset ⊆ T ∧
      ((ascList k T).take r).toFinset.card = r ∧
      ∀ x ∈ ((ascList k T).take r).toFinset, ∀ y ∈ T \ ((ascList k T).take r).toFinset, x < y := by
  set L := ascList k T with hL
  have hnd : (L.take r).Nodup := (ascList_nodup k T).sublist (L.take_sublist r)
  have hsub : (L.take r).toFinset ⊆ T := by
    intro x hx
    rw [List.mem_toFinset] at hx
    have := List.take_sublist r L |>.subset hx
    rwa [hL, mem_ascList hT] at this
  refine ⟨hsub, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hnd, List.length_take, ascList_length hT]
    omega
  · intro x hx y hy
    rw [Finset.mem_sdiff, List.mem_toFinset] at hy
    obtain ⟨hyT, hyt⟩ := hy
    rw [List.mem_toFinset] at hx
    -- `y` is in `L` but not in the prefix, hence in the suffix; `L` is strictly increasing.
    have hyL : y ∈ L := by rwa [hL, mem_ascList hT]
    have hyd : y ∈ L.drop r := by
      have := (List.take_append_drop r L) ▸ hyL
      rcases List.mem_append.mp this with h | h
      · exact absurd h hyt
      · exact h
    have hpw := ascList_pairwise_lt k T
    rw [← List.take_append_drop r (ascList k T), List.pairwise_append] at hpw
    exact hpw.2.2 x hx y hyd

/-- **The gap lemma.** For `T ⊆ {0,…,k-1}` and `r ≤ #T`, the length-`r` prefix of the ascending
enumeration of `T` is `S` exactly when `S` is an initial segment of `T` of size `r`.

This is the lemma the paper proof of `prop:N` (`2026-09-05-Q85-literal-gcd.tex`, §"The prefix
sign sum") uses to reindex the `T`-sum; without it the reindexing cannot even be stated. -/
theorem take_ascList_toFinset {r : ℕ} (hT : T ⊆ range k) (hr : r ≤ T.card) :
    ((ascList k T).take r).toFinset = S ↔
      S ⊆ T ∧ S.card = r ∧ ∀ x ∈ S, ∀ y ∈ T \ S, x < y := by
  obtain ⟨h1, h2, h3⟩ := take_ascList_spec hT hr
  constructor
  · rintro rfl
    exact ⟨h1, h2, h3⟩
  · rintro ⟨hs1, hs2, hs3⟩
    exact eq_of_lt_sdiff h1 hs1 (h2.trans hs2.symm) h3 hs3

/-- The mirror of `eq_of_lt_sdiff`: two subsets of `T` of the same size, each lying strictly
*above* its complement in `T`, are equal. Needed because `ρ_T`'s tail is descending. -/
theorem eq_of_gt_sdiff {T S S' : Finset ℕ} (hS : S ⊆ T) (hS' : S' ⊆ T)
    (hcard : S.card = S'.card)
    (hsep : ∀ x ∈ S, ∀ y ∈ T \ S, y < x) (hsep' : ∀ x ∈ S', ∀ y ∈ T \ S', y < x) :
    S = S' := by
  by_contra hne
  obtain ⟨x, hxS, hxS'⟩ : ∃ x ∈ S, x ∉ S' :=
    Finset.not_subset.mp fun h => hne (Finset.eq_of_subset_of_card_le h hcard.ge)
  obtain ⟨y, hyS', hyS⟩ : ∃ y ∈ S', y ∉ S :=
    Finset.not_subset.mp fun h => hne (Finset.eq_of_subset_of_card_le h hcard.le).symm
  have h1 : y < x := hsep x hxS y (Finset.mem_sdiff.mpr ⟨hS' hyS', hyS⟩)
  have h2 : x < y := hsep' y hyS' x (Finset.mem_sdiff.mpr ⟨hS hxS, hxS'⟩)
  exact absurd h1 (asymm h2)

/-- The length-`j` prefix of the *reversed* ascending enumeration of `T` is a final segment of
`T`: `j` elements, all above the rest of `T`. -/
theorem take_reverse_ascList_spec {j : ℕ} (hT : T ⊆ range k) (hj : j ≤ T.card) :
    (((ascList k T).reverse).take j).toFinset ⊆ T ∧
      (((ascList k T).reverse).take j).toFinset.card = j ∧
      ∀ x ∈ (((ascList k T).reverse).take j).toFinset,
        ∀ y ∈ T \ (((ascList k T).reverse).take j).toFinset, y < x := by
  set L := (ascList k T).reverse with hLdef
  have hmemL : ∀ x, x ∈ L ↔ x ∈ T := by
    intro x; rw [hLdef, List.mem_reverse]; exact mem_ascList hT
  have hndL : L.Nodup := List.nodup_reverse.mpr (ascList_nodup k T)
  have hlenL : L.length = T.card := by rw [hLdef, List.length_reverse, ascList_length hT]
  have hnd : (L.take j).Nodup := hndL.sublist (L.take_sublist j)
  have hsub : (L.take j).toFinset ⊆ T := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact (hmemL x).mp (L.take_sublist j |>.subset hx)
  refine ⟨hsub, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hnd, List.length_take, hlenL]
    omega
  · intro x hx y hy
    rw [Finset.mem_sdiff, List.mem_toFinset] at hy
    obtain ⟨hyT, hyt⟩ := hy
    rw [List.mem_toFinset] at hx
    have hyd : y ∈ L.drop j := by
      rcases List.mem_append.mp ((List.take_append_drop j L) ▸ (hmemL y).mpr hyT) with h | h
      · exact absurd h hyt
      · exact h
    -- `L` is strictly *decreasing*, being the reverse of a strictly increasing list.
    have hpw : L.Pairwise (· > ·) :=
      List.pairwise_reverse.mpr (ascList_pairwise_lt k T)
    rw [← List.take_append_drop j L, List.pairwise_append] at hpw
    exact hpw.2.2 x hx y hyd

/-- **The mirror gap lemma.** The length-`j` prefix of the descending enumeration of `T` is `S`
exactly when `S` is a final segment of `T` of size `j`.

This is the half of `prop:N` that lives in the descending tail of `ρ_T`
(`2026-09-05-Q85-literal-gcd.tex`, §"The prefix sign sum", case `k ∈ S̄`, regime `r > m+1`),
where the prefix picks out the `r-m-1` *largest* elements of `D = [k-1] \ T`. -/
theorem take_reverse_ascList_toFinset {j : ℕ} (hT : T ⊆ range k) (hj : j ≤ T.card) :
    (((ascList k T).reverse).take j).toFinset = S ↔
      S ⊆ T ∧ S.card = j ∧ ∀ x ∈ S, ∀ y ∈ T \ S, y < x := by
  obtain ⟨h1, h2, h3⟩ := take_reverse_ascList_spec hT hj
  constructor
  · rintro rfl
    exact ⟨h1, h2, h3⟩
  · rintro ⟨hs1, hs2, hs3⟩
    exact eq_of_gt_sdiff h1 hs1 (h2.trans hs2.symm) h3 hs3

/-- **The reindexing.** The `T` with `A ⊆ T ⊆ A ⊔ Y` are exactly the `A ∪ B`, `B ⊆ Y`, and the
signed count over them collapses by the alternating sum. Both cases of `prop:N` are instances. -/
theorem sum_interval_sign (A Y U : Finset ℕ) (hAY : Disjoint A Y) (hAU : A ⊆ U) (hYU : Y ⊆ U) :
    ∑ T ∈ U.powerset, (if A ⊆ T ∧ T ⊆ A ∪ Y then ((-1 : ℤ)) ^ T.card else 0)
      = (-1) ^ A.card * (if Y = ∅ then 1 else 0) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_nbij' (i := fun T => T \ A) (j := fun B => A ∪ B)
      (t := Y.powerset) (g := fun B => (-1 : ℤ) ^ A.card * (-1) ^ B.card)]
  · rw [← Finset.mul_sum, Finset.sum_powerset_neg_one_pow_card]
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    simp only [Finset.mem_powerset]
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rcases Finset.mem_union.mp (hT.2.2 hx.1) with h | h
    · exact absurd h hx.2
    · exact h
  · intro B hB
    rw [Finset.mem_powerset] at hB
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.union_subset hAU (hB.trans hYU), Finset.subset_union_left,
      Finset.union_subset_union_right hB⟩
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    by_cases hxA : x ∈ A
    · simp [hxA, hT.2.1 hxA]
    · simp [hxA]
  · intro B hB
    rw [Finset.mem_powerset] at hB
    exact Finset.union_sdiff_cancel_left (hAY.mono_right hB)
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    rw [← pow_add]
    congr 1
    have := Finset.card_sdiff_add_card_eq_card hT.2.1
    omega

/-! ## Splitting the prefix across the append -/

/-- Regime `r ≤ m`: the prefix never reaches the peak, so it is a prefix of `ascList k T`. -/
theorem rho_take_of_le {r : ℕ} (hT : T ⊆ range k) (hr : r ≤ T.card) :
    (rho k T).take r = (ascList k T).take r := by
  refine List.take_append_of_le_length ?_
  rw [ascList_length hT]; exact hr

/-- Regimes `r ≥ m+1`: the prefix has reached the peak, so it contains the letter `k`. -/
theorem mem_rho_take_of_gt {r : ℕ} (hT : T ⊆ range k) (hr : T.card < r) :
    k ∈ ((rho k T).take r).toFinset := by
  rw [List.mem_toFinset]
  refine List.mem_of_getElem? (i := T.card) ?_
  rw [List.getElem?_take, if_pos hr, rho_getElem_peak hT]

/-! ## Case `k ∉ S̄`: only the regime `r ≤ m` survives -/

/-- The prefix condition, for `k ∉ S̄`, is exactly "`T` lies between `S̄` and `S̄ ∪ (max S̄, k-1]`".
Source: `2026-09-05-Q85-literal-gcd.tex`, `prop:N`, case `k ∉ \bar S`. -/
theorem prefix_condition_not_mem (_hk : 2 ≤ k) (hne : S.Nonempty) (hkS : k ∉ S)
    (_hSk : S ⊆ Icc 1 (k - 1)) (hT : T ⊆ Icc 1 (k - 1)) :
    (((rho k T).take S.card).toFinset = S)
      ↔ (S ⊆ T ∧ T ⊆ S ∪ Ioc (S.max' hne) (k - 1)) := by
  have hTr : T ⊆ range k := hT.trans (Icc_one_sub_subset_range k)
  rcases lt_or_ge T.card S.card with hlt | hge
  · -- the prefix has reached the peak, so it contains `k ∉ S̄`
    constructor
    · intro h
      exact absurd (h ▸ mem_rho_take_of_gt hTr hlt) hkS
    · rintro ⟨h1, -⟩
      exact absurd (Finset.card_le_card h1) (by omega)
  · rw [rho_take_of_le hTr hge, take_ascList_toFinset hTr hge]
    constructor
    · rintro ⟨h1, -, h3⟩
      refine ⟨h1, fun x hx => ?_⟩
      by_cases hxS : x ∈ S
      · exact Finset.mem_union_left _ hxS
      · refine Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨?_, ?_⟩)
        · exact h3 _ (S.max'_mem hne) x (Finset.mem_sdiff.mpr ⟨hx, hxS⟩)
        · exact (Finset.mem_Icc.mp (hT hx)).2
    · rintro ⟨h1, h2⟩
      refine ⟨h1, rfl, fun x hx y hy => ?_⟩
      rw [Finset.mem_sdiff] at hy
      rcases Finset.mem_union.mp (h2 hy.1) with h | h
      · exact absurd h hy.2
      · exact lt_of_le_of_lt (S.le_max' x hx) (Finset.mem_Ioc.mp h).1

/-- `prop:N`, case `k ∉ S̄`, for every `k ≥ 2`.
Source: `2026-09-05-Q85-literal-gcd.tex`, `prop:N`, case `k \notin \bar S`. -/
theorem prefixSignSum_eq_of_not_mem (hk : 2 ≤ k) (hS : S ⊆ Icc 1 k) (hne : S.Nonempty)
    (hkS : k ∉ S) : prefixSignSum k S = prefixSignSumRHS k S := by
  have hSk : S ⊆ Icc 1 (k - 1) := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hS hx)
    rw [Finset.mem_Icc]
    refine ⟨hx'.1, ?_⟩
    rcases Nat.lt_or_ge x k with h | h
    · omega
    · exact absurd (le_antisymm hx'.2 h ▸ hx) hkS
  set M := S.max' hne with hM
  have hMmem := hSk (S.max'_mem hne)
  have hMk : M ≤ k - 1 := (Finset.mem_Icc.mp hMmem).2
  have hM1 : 1 ≤ M := (Finset.mem_Icc.mp hMmem).1
  have hdisj : Disjoint S (Ioc M (k - 1)) := by
    rw [Finset.disjoint_right]
    intro x hx hxS
    have := (Finset.mem_Ioc.mp hx).1
    exact absurd (S.le_max' x hxS) (by omega)
  have hYU : Ioc M (k - 1) ⊆ Icc 1 (k - 1) := by
    intro x hx
    have hx' := Finset.mem_Ioc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, hx'.2⟩
  have hstep : prefixSignSum k S
      = ∑ T ∈ (Icc 1 (k - 1)).powerset,
          (if S ⊆ T ∧ T ⊆ S ∪ Ioc M (k - 1) then ((-1 : ℤ)) ^ T.card else 0) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    rw [wordSign]
    exact if_congr (prefix_condition_not_mem hk hne hkS hSk hT) rfl rfl
  rw [hstep, sum_interval_sign S (Ioc M (k - 1)) (Icc 1 (k - 1)) hdisj hSk hYU]
  -- `(M, k-1] = ∅` iff `max S̄ = k-1` iff `k-1 ∈ S̄`, since `k ∉ S̄`.
  have hiff : Ioc M (k - 1) = ∅ ↔ k - 1 ∈ S := by
    constructor
    · intro h
      have hMeq : M = k - 1 := by
        by_contra hne'
        have hmem : k - 1 ∈ Ioc M (k - 1) := Finset.mem_Ioc.mpr ⟨by omega, le_rfl⟩
        rw [h] at hmem
        exact absurd hmem (Finset.notMem_empty _)
      rw [← hMeq]
      exact S.max'_mem hne
    · intro h
      have hMeq : M = k - 1 := le_antisymm hMk (S.le_max' _ h)
      rw [hMeq, Finset.Ioc_self]
  simp only [hiff]
  by_cases hc : k - 1 ∈ S <;> simp [prefixSignSumRHS, hc, hkS]

/-! ## Case `k ∈ S̄`: regimes `r = m+1` and `r > m+1`, which merge into one interval -/

/-- Regimes `r ≥ m+1`: the prefix is all of `T`, then the peak `k`, then the `r-m-1` largest
elements of `D = [k-1] \ T`. Source: `2026-09-05-Q85-literal-gcd.tex`, `prop:N`, first display
of the proof. -/
theorem rho_take_of_gt {r : ℕ} (hT : T ⊆ range k) (hr : T.card < r) :
    ((rho k T).take r).toFinset
      = insert k (T ∪ (((ascList k (descentSet k T)).reverse).take (r - T.card - 1)).toFinset) := by
  have hlen : (ascList k T).length = T.card := ascList_length hT
  obtain ⟨j, hj⟩ : ∃ j, r - T.card = j + 1 := ⟨r - T.card - 1, by omega⟩
  unfold rho
  rw [List.take_append, hlen, hj, List.take_of_length_le (by omega), List.take_succ_cons]
  rw [List.toFinset_append, List.toFinset_cons, ascList_toFinset hT]
  simp only [Nat.add_sub_cancel]
  ext x
  simp only [Finset.mem_union, Finset.mem_insert]
  tauto

/-- `topBlock k S₀ = Y = (m*, k-1]` of the paper, where `m* = max([k-1] \ S₀)`.

Defined as `{x ∈ [1,k-1] : [x,k-1] ⊆ S₀}` rather than through `max`, which removes the source's
`m* := 0 if that set is empty` convention — the empty case is not special here — and keeps the
definition decidable. Source: `2026-09-05-Q85-literal-gcd.tex`, `prop:N`, case `k ∈ \bar S`. -/
def topBlock (k : ℕ) (S₀ : Finset ℕ) : Finset ℕ :=
  (Icc 1 (k - 1)).filter (fun x => Icc x (k - 1) ⊆ S₀)

/-- The defining property: `x ∈ Y` iff `x` lies above every element of `[k-1] \ S₀`. -/
theorem mem_topBlock {x : ℕ} {S₀ : Finset ℕ} (hx : 1 ≤ x) :
    x ∈ topBlock k S₀ ↔ x ≤ k - 1 ∧ ∀ y ∈ Icc 1 (k - 1) \ S₀, y < x := by
  rw [topBlock, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    refine ⟨h2, fun y hy => ?_⟩
    rw [Finset.mem_sdiff] at hy
    by_contra hxy
    exact hy.2 (h3 (Finset.mem_Icc.mpr ⟨by omega, (Finset.mem_Icc.mp hy.1).2⟩))
  · rintro ⟨h2, h3⟩
    refine ⟨⟨hx, h2⟩, fun y hy => ?_⟩
    have hy' := Finset.mem_Icc.mp hy
    by_contra hyS
    exact absurd (h3 y (Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hy'.2⟩, hyS⟩))
      (by omega)

theorem topBlock_subset {S₀ : Finset ℕ} : topBlock k S₀ ⊆ S₀ := by
  intro x hx
  rw [topBlock, Finset.mem_filter, Finset.mem_Icc] at hx
  exact hx.2 (Finset.mem_Icc.mpr ⟨le_rfl, hx.1.2⟩)

/-- `Y = ∅` exactly when `k-1 ∉ S₀`: the dichotomy behind `prop:N`'s two branches when `k ∈ S̄`. -/
theorem topBlock_eq_empty_iff (hk : 2 ≤ k) {S₀ : Finset ℕ} :
    topBlock k S₀ = ∅ ↔ k - 1 ∉ S₀ := by
  constructor
  · intro h hmem
    have hkY : k - 1 ∈ topBlock k S₀ := by
      rw [topBlock, Finset.mem_filter]
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, by
        intro y hy; rw [Finset.mem_Icc] at hy
        exact (le_antisymm hy.2 hy.1) ▸ hmem⟩
    rw [h] at hkY
    exact absurd hkY (Finset.notMem_empty _)
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [topBlock, Finset.mem_filter, Finset.mem_Icc] at hx
    exact h (hx.2 (Finset.mem_Icc.mpr ⟨hx.1.2, le_rfl⟩))

/-- The prefix condition, for `k ∈ S̄`. The source splits this into `r = m+1` (the single term
`T = S̄₀`) and `r > m+1` (`T ⊊ S̄₀`); here the two regimes **merge into one interval**
`S̄₀ \ Y ⊆ T ⊆ S̄₀`, with `T = S̄₀` the top element. -/
theorem prefix_condition_mem (hk : 2 ≤ k) (hS : S ⊆ Icc 1 k) (hkS : k ∈ S)
    (hT : T ⊆ Icc 1 (k - 1)) :
    (((rho k T).take S.card).toFinset = S)
      ↔ (S.erase k \ topBlock k (S.erase k) ⊆ T ∧ T ⊆ S.erase k) := by
  have hTr : T ⊆ range k := hT.trans (Icc_one_sub_subset_range k)
  set S₀ := S.erase k with hS₀def
  set Y := topBlock k S₀ with hYdef
  have hYS : Y ⊆ S₀ := topBlock_subset
  have hS0k : S₀ ⊆ Icc 1 (k - 1) := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase hx))
    exact Finset.mem_Icc.mpr ⟨hx'.1, by
      have := Finset.ne_of_mem_erase hx; omega⟩
  have hS0card : S₀.card = S.card - 1 := Finset.card_erase_of_mem hkS
  have hScard : 1 ≤ S.card := Finset.card_pos.mpr ⟨k, hkS⟩
  have hrk : S.card ≤ k := by
    have := Finset.card_le_card hS
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at this
  rcases lt_or_ge T.card S.card with hlt | hge
  · -- Regimes `r ≥ m+1`: the prefix reaches the peak.
    rw [rho_take_of_gt hTr hlt]
    set j := S.card - T.card - 1 with hjdef
    set D := descentSet k T with hDdef
    have hDr : D ⊆ range k := descentSet_subset_range k T
    have hmemD : ∀ x, x ∈ D ↔ x ∈ Icc 1 (k - 1) ∧ x ∉ T := by
      intro x; rw [hDdef, descentSet, Finset.mem_sdiff]
    have hDcard : D.card = (k - 1) - T.card := by
      have h := Finset.card_sdiff_add_card_eq_card hT
      rw [Nat.card_Icc] at h
      rw [hDdef, descentSet]
      omega
    have hj : j ≤ D.card := by omega
    set F := (((ascList k D).reverse).take j).toFinset with hFdef
    have hFD : F ⊆ D := (take_reverse_ascList_spec hDr hj).1
    have hkTF : k ∉ T ∪ F := by
      intro h
      rcases Finset.mem_union.mp h with h' | h'
      · have := (Finset.mem_Icc.mp (hT h')).2; omega
      · have := Finset.mem_range.mp (hDr (hFD h')); omega
    -- `insert k (T ∪ F) = S` iff `T ∪ F = S₀`, since `k ∉ T ∪ F` and `k ∈ S`.
    have hstep1 : insert k (T ∪ F) = S ↔ T ∪ F = S₀ := by
      constructor
      · intro h; rw [hS₀def, ← h, Finset.erase_insert hkTF]
      · intro h; rw [h, hS₀def, Finset.insert_erase hkS]
    rw [hstep1]
    constructor
    · -- forward
      intro h
      have hTS0 : T ⊆ S₀ := h ▸ Finset.subset_union_left
      refine ⟨?_, hTS0⟩
      -- `F = S₀ \ T`, and `F` is a final segment of `D`, so `S₀ \ T ⊆ Y`.
      have hFeq : F = S₀ \ T := by
        rw [← h]
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · intro hx
          exact ⟨Or.inr hx, fun hxT => (Finset.mem_sdiff.mp (hFD hx)).2 hxT⟩
        · rintro ⟨hx | hx, hxT⟩
          · exact absurd hx hxT
          · exact hx
      have hsep := (take_reverse_ascList_spec hDr hj).2.2
      rw [← hFdef, hFeq] at hsep
      have hkey : S₀ \ T ⊆ Y := by
        intro x hx
        have hxS0 : x ∈ S₀ := (Finset.mem_sdiff.mp hx).1
        have hxIcc := Finset.mem_Icc.mp (hS0k hxS0)
        rw [hYdef, mem_topBlock hxIcc.1]
        refine ⟨hxIcc.2, fun y hy => ?_⟩
        refine hsep x hx y ?_
        rw [Finset.mem_sdiff] at hy ⊢
        refine ⟨Finset.mem_sdiff.mpr ⟨hy.1, fun hyT => hy.2 (hTS0 hyT)⟩, ?_⟩
        rw [Finset.mem_sdiff]
        tauto
      intro x hx
      rw [Finset.mem_sdiff] at hx
      by_contra hxT
      exact hx.2 (hkey (Finset.mem_sdiff.mpr ⟨hx.1, hxT⟩))
    · -- backward
      rintro ⟨hAT, hTS0⟩
      have hSTcard : (S₀ \ T).card = j := by
        have := Finset.card_sdiff_add_card_eq_card hTS0
        omega
      have hSTD : S₀ \ T ⊆ D := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        rw [hmemD]
        exact ⟨hS0k hx.1, hx.2⟩
      have hFeq : F = S₀ \ T := by
        rw [hFdef, take_reverse_ascList_toFinset hDr hj]
        refine ⟨hSTD, hSTcard, fun x hx y hy => ?_⟩
        -- `D \ (S₀ \ T) = [k-1] \ S₀`, and `x ∈ S₀ \ T ⊆ Y` lies above all of it.
        have hxY : x ∈ Y := by
          by_contra hxY
          rw [Finset.mem_sdiff] at hx
          exact hx.2 (hAT (Finset.mem_sdiff.mpr ⟨hx.1, hxY⟩))
        have hxIcc := Finset.mem_Icc.mp (hS0k ((Finset.mem_sdiff.mp hx).1))
        rw [hYdef, mem_topBlock hxIcc.1] at hxY
        refine hxY.2 y ?_
        rw [Finset.mem_sdiff] at hy ⊢
        have hy1 := (hmemD y).mp hy.1
        refine ⟨hy1.1, fun hyS0 => hy.2 (Finset.mem_sdiff.mpr ⟨hyS0, hy1.2⟩)⟩
      rw [hFeq, Finset.union_sdiff_of_subset hTS0]
  · -- Regime `r ≤ m`: the prefix stays inside `T ⊆ [k-1]`, so it misses `k ∈ S̄`.
    rw [rho_take_of_le hTr hge]
    constructor
    · intro h
      have := (take_ascList_spec hTr hge).1
      rw [h] at this
      have := Finset.mem_Icc.mp (hT (this hkS))
      omega
    · rintro ⟨-, hTS0⟩
      have := Finset.card_le_card hTS0
      omega

/-- `prop:N`, case `k ∈ S̄`, for every `k ≥ 2`. The source's two contributions — the single
term `T = S̄₀` and the alternating sum over `T ⊊ S̄₀` — are here one application of
`sum_interval_sign` to the interval `[S̄₀ \ Y, S̄₀]`. -/
theorem prefixSignSum_eq_of_mem (hk : 2 ≤ k) (hS : S ⊆ Icc 1 k) (hkS : k ∈ S) :
    prefixSignSum k S = prefixSignSumRHS k S := by
  set S₀ := S.erase k with hS₀def
  set Y := topBlock k S₀ with hYdef
  have hYS : Y ⊆ S₀ := topBlock_subset
  have hYIcc : Y ⊆ Icc 1 (k - 1) := by rw [hYdef, topBlock]; exact Finset.filter_subset _ _
  have hS0k : S₀ ⊆ Icc 1 (k - 1) := by
    intro x hx
    have hx' := Finset.mem_Icc.mp (hS (Finset.mem_of_mem_erase hx))
    exact Finset.mem_Icc.mpr ⟨hx'.1, by have := Finset.ne_of_mem_erase hx; omega⟩
  have hdisj : Disjoint (S₀ \ Y) Y := Finset.sdiff_disjoint
  have hAY : (S₀ \ Y) ∪ Y = S₀ := Finset.sdiff_union_of_subset hYS
  have hstep : prefixSignSum k S
      = ∑ T ∈ (Icc 1 (k - 1)).powerset,
          (if S₀ \ Y ⊆ T ∧ T ⊆ (S₀ \ Y) ∪ Y then ((-1 : ℤ)) ^ T.card else 0) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    rw [wordSign]
    refine if_congr ?_ rfl rfl
    rw [prefix_condition_mem hk hS hkS hT, hAY, and_comm]
  rw [hstep, sum_interval_sign (S₀ \ Y) Y (Icc 1 (k - 1)) hdisj
    ((Finset.sdiff_subset).trans hS0k) hYIcc]
  -- `Y = ∅` iff `k-1 ∉ S̄`; that is exactly `prop:N`'s dichotomy in this case.
  have hYempty : Y = ∅ ↔ k - 1 ∉ S := by
    rw [hYdef, topBlock_eq_empty_iff hk, hS₀def, Finset.mem_erase]
    constructor
    · intro h hmem; exact h ⟨by omega, hmem⟩
    · intro h hmem; exact h hmem.2
  simp only [hYempty]
  by_cases hc : k - 1 ∈ S
  · rw [if_neg (by simpa using hc), mul_zero, prefixSignSumRHS,
      if_neg (fun h => h.2 hkS), if_neg (fun h => h.2 hc)]
  · rw [if_pos hc, mul_one, prefixSignSumRHS, if_neg (fun h => h.2 hkS), if_pos ⟨hkS, hc⟩]
    congr 1
    rw [Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_right.mpr (fun x hx =>
      absurd ((hYdef ▸ hYempty).mpr hc ▸ hx) (Finset.notMem_empty x))),
      hS₀def, Finset.card_erase_of_mem hkS]

/-- **`prop:N` for every `k ≥ 2`.** Source: `2026-09-05-Q85-literal-gcd.tex`, Proposition
`prop:N`. Generalises `prefixSignSum_eq_three/_four/_five`, which were `decide` at fixed `k`. -/
theorem prefixSignSum_eq (hk : 2 ≤ k) (hS : S ⊆ Icc 1 k) (hne : S.Nonempty) :
    prefixSignSum k S = prefixSignSumRHS k S := by
  by_cases hkS : k ∈ S
  · exact prefixSignSum_eq_of_mem hk hS hkS
  · exact prefixSignSum_eq_of_not_mem hk hS hne hkS

/-!
## What this file now proves

`prop:N` for **every** `k ≥ 2` and every nonempty `S̄ ⊆ [k]`: `prefixSignSum_eq`. The
`decide`-at-fixed-`k` theorems `prefixSignSum_eq_three/_four/_five` are subsumed by it and are
kept as independent kernel-level cross-checks of the two definitions.

The route, matching `2026-09-05-Q85-literal-gcd.tex`, §"The prefix sign sum":

1. **The prefix split.** `rho_take_of_le` (regime `r ≤ m`: the prefix stays inside the ascending
   run) and `rho_take_of_gt` (regimes `r ≥ m+1`: the prefix is `T`, then the peak `k`, then the
   top `r-m-1` of `D`). `mem_rho_take_of_gt` is the cheap discriminator between them — past the
   peak the prefix contains `k`.
2. **The two order lemmas**, proved 2026-09-06: `take_ascList_toFinset` and its mirror
   `take_reverse_ascList_toFinset`.
3. **One reindexing, not two.** `sum_interval_sign` evaluates `∑_{A ⊆ T ⊆ A ⊔ Y} (-1)^|T|` as
   `(-1)^|A| · [Y = ∅]`, by `Finset.sum_nbij'` along `T ↦ T \ A` together with
   `Finset.sum_powerset_neg_one_pow_card`. Both cases of `prop:N` are instances: case `k ∉ S̄`
   with `A = S̄`, `Y = (max S̄, k-1]`; case `k ∈ S̄` with `A = S̄₀ \ Y`, `Y = topBlock`.

**Where this departs from the paper, and why it is not new mathematics.** The source splits the
case `k ∈ S̄` into `r = m+1` (one term, `T = S̄₀`) and `r > m+1` (an alternating sum over
`T ⊊ S̄₀`), then adds the two contributions. `prefix_condition_mem` shows the admissible `T` are
exactly the interval `S̄₀ \ Y ⊆ T ⊆ S̄₀`, of which `T = S̄₀` is the top element — so the two
regimes are one interval and the addition is not needed. Both computations agree; the Lean proof
takes the shorter of them.

Likewise `topBlock` is `{x ∈ [1,k-1] : [x,k-1] ⊆ S̄₀}` rather than the source's `(m*, k-1]` with
`m* := max([k-1] \ S̄₀)` and the convention `m* := 0` when that set is empty. The two sets are
equal; the filter form has no empty-set special case and, unlike `max'`, needs no nonemptiness
hypothesis.

Registry: `Q85-prefix-sign-sum-lean-general-gap`, `Q85-prefix-sign-sum-lean-initial-segments`.
Session note `proofs/2026-09-07-lean-prefix-sign-sum-general-k.md`.
-/

end TworowD4Kernel
