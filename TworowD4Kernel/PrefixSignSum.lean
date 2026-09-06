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

/-!
## What is NOT proved here

`prop:N` for general `k` is **open in Lean**. The paper proof (§"The prefix sign sum") turns on
one lemma this file does not have:

> for `T ⊆ range k` and `r ≤ #T`, `((ascList k T).take r).toFinset = S ↔ S ⊆ T ∧ #S = r ∧
> ∀ x ∈ S, ∀ y ∈ T \ S, x < y`

— "the length-`r` prefix of the ascending enumeration of `T` is `S` iff `S` is an initial
segment of `T`". With it, both branches of the paper's case split collapse by
`∑_{B ⊆ C} (-1)^|B| = 0` for `C ≠ ∅`. Without it the reindexing of the `T`-sum cannot even be
stated. That lemma, not the algebra, is the whole gap; see the session note
`proofs/2026-09-06-lean-prefix-sign-sum.md`.
-/

end TworowD4Kernel
