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

/-!
## What is NOT proved here

`prop:N` for general `k` is still open in Lean; `prefixSignSum_eq_three/_four/_five` remain the
only general-`S` statements, and they are `decide`.

**What this session removed.** The gap used to be stated as "one missing lemma, after which both
cases collapse by `∑_{B ⊆ C} (-1)^|B| = 0`". That description was wrong in one respect and is now
obsolete in the other:

* the ascending half is `take_ascList_toFinset`, proved above, sorry-free;
* the description missed a *second* order lemma. `ρ_T` is `ascList ++ k :: (ascList D).reverse`,
  and the case `k ∈ S̄`, regime `r > m+1` of the paper proof reads the prefix off the
  **descending tail** — the `r-m-1` largest elements of `D`. `take_ascList_toFinset` says nothing
  about that. Its mirror, `take_reverse_ascList_toFinset`, is proved above.

So the whole order-theoretic content of `prop:N` is now formalised. What is left is bookkeeping,
and it is genuinely of a different kind:

1. **Splitting the prefix across the append.** `((rho k T).take r).toFinset` in the three regimes
   `r ≤ m`, `r = m+1`, `r > m+1`, via `List.take_append` / `List.take_append_eq_append_take`.
   The two lemmas above then identify each piece. No new mathematics.
2. **Two sum reindexings.** Case `k ∉ S̄` reindexes the `T`-sum along `T = S̄ ⊔ B`,
   `B ⊆ (max S̄, k-1]`; case `k ∈ S̄` along `T = (S̄₀ \ Y) ∪ Y'`, `Y' ⊊ Y`. These are
   `Finset.sum_nbij'`-shaped and are where the remaining work actually is.
3. **The alternating sum.** `Finset.sum_powerset_neg_one_pow_card_of_nonempty`
   (`Mathlib/Data/Nat/Choose/Sum.lean`) — already in Mathlib, no work.

Registry: `Q85-prefix-sign-sum-lean-general-gap`. Session note
`proofs/2026-09-06-c2-lean-prefix-initial-segments.md`.
-/

end TworowD4Kernel
