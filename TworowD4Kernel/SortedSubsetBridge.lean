/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.MConvexExchange

/-!
# The sorted ↔ subset bridge `J = J'`

Formalisation of the **first sentence of the proof** of Proposition `prop:perm-mconvex`
of `projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex`:

> `J = {α ∈ ℕ^ℓ : sort(α) ⊴ λ̂}` equals
> `J' = {α ∈ ℕ^ℓ : α([ℓ]) = |λ̂|, α(S) ≤ Λ_{|S|} for all S ⊆ [ℓ]}`,
> because `max_{|S| = r} α(S)` is the sum of the `r` largest entries of `α`.

`MConvexExchange.insupp_exchange` proves the M-convex exchange axiom for `J'` only; this
file supplies the identification with the paper's `J`, so that the exchange axiom holds
for the paper's own object.  The same identity is the "therefore" in the SNP argument of
`state/PROVE.md` §3 (a lattice point of `conv(W_ℓ)` satisfying the linear inequalities
lies in `W_ℓ` — that is `J' ⊆ J`).

## What is proved

* `sortDesc α ℓ` — the entries `α 0, …, α (ℓ-1)` listed in weakly decreasing order,
  extended by `0`.  It is **not** defined as "the thing that makes the theorem true":
  it is `α` composed with an explicit sorting permutation of the index list, and the two
  properties that characterise a sorted rearrangement are proved, not assumed:
  - `sortDesc_antitone` : `Antitone (sortDesc α ℓ)`;
  - `sortDesc_multiset` : `sortDesc α ℓ` and `α` agree as multisets on `[ℓ]`.
  Those two together pin `sortDesc α ℓ` down uniquely, so a wrong definition here is
  falsifiable *inside* Lean, not only against the Python differential check.
* `sum_le_sum_take` — the crux: among sub-multisets of a fixed cardinality of a
  descending list, the sum is largest on the prefix.  Nothing about `λ̂` enters.
* `asum_le_psum_sortDesc` / `exists_subset_asum_eq` — the two halves of
  `max_{|S| = r} α(S) = Λ-free sum of the r largest`, i.e. `≤` for every `S` and
  attainment for one `S`.
* `insupp_iff_sorted` — **the target**: `InSupp ℓ lhat α ↔ InSuppSorted ℓ lhat α`.

## What Lean still does not see

`MConvexExchange`'s docstring lists one gap ("the sorted form is not formalised"); this
file closes it.  The *other* gap named there is untouched and remains owed: Murota's
**symmetric** exchange axiom (B-EXC) demands `β + eᵢ - e_j ∈ J` for the same `j`.  That
is not proved here, is equivalent to the one-sided form only by a Murota–Shioura theorem
which is neither formalised nor used, and is covered only by brute force
(0 failures / 876317 triples) in `proofs/code-q254-lean/`.

Indices are 0-based; the paper is 1-based.  `Λ_r` is `psum lhat r`.
-/

namespace SortedBridge

open Finset RobinHood MConvexExchange

/-! ### The sorting permutation of the index set -/

/-- The "weakly decreasing in `α`" preorder on indices.  Not antisymmetric (distinct
indices may carry equal entries), which is why `List.insertionSort` is used rather than
`Multiset.sort`. -/
def keyRel (α : ℕ → ℤ) : ℕ → ℕ → Prop := fun i j => α j ≤ α i

instance decKeyRel (α : ℕ → ℤ) : DecidableRel (keyRel α) :=
  fun i j => inferInstanceAs (Decidable (α j ≤ α i))

instance isTotalKeyRel (α : ℕ → ℤ) : Std.Total (keyRel α) :=
  ⟨fun i j => (le_total (α j) (α i)).imp id id⟩

instance isTransKeyRel (α : ℕ → ℤ) : IsTrans ℕ (keyRel α) :=
  ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

/-- `idxSort α ℓ` lists `0, …, ℓ-1` in weakly decreasing order of `α`. -/
def idxSort (α : ℕ → ℤ) (ℓ : ℕ) : List ℕ :=
  List.insertionSort (keyRel α) (List.range ℓ)

/-- The entry list of the sorted rearrangement: `α` read along `idxSort`. -/
def sortList (α : ℕ → ℤ) (ℓ : ℕ) : List ℤ := (idxSort α ℓ).map α

/-- **`sort(α)`** — the entries of `α` on `[ℓ]` in weakly decreasing order, extended by
`0` beyond position `ℓ`.  This is the paper's `sort(α)`. -/
def sortDesc (α : ℕ → ℤ) (ℓ : ℕ) : ℕ → ℤ := fun c => (sortList α ℓ).getD c 0

lemma idxSort_perm (α : ℕ → ℤ) (ℓ : ℕ) : (idxSort α ℓ).Perm (List.range ℓ) :=
  List.perm_insertionSort _ _

lemma idxSort_nodup (α : ℕ → ℤ) (ℓ : ℕ) : (idxSort α ℓ).Nodup :=
  (idxSort_perm α ℓ).nodup_iff.mpr (List.nodup_range)

lemma idxSort_length (α : ℕ → ℤ) (ℓ : ℕ) : (idxSort α ℓ).length = ℓ := by
  rw [(idxSort_perm α ℓ).length_eq, List.length_range]

lemma idxSort_mem {α : ℕ → ℤ} {ℓ i : ℕ} (h : i ∈ idxSort α ℓ) : i < ℓ := by
  have := (idxSort_perm α ℓ).mem_iff.mp h
  simpa using this

lemma sortList_length (α : ℕ → ℤ) (ℓ : ℕ) : (sortList α ℓ).length = ℓ := by
  rw [sortList, List.length_map, idxSort_length]

/-- The entry list really is sorted in weakly decreasing order. -/
lemma sortList_pairwise (α : ℕ → ℤ) (ℓ : ℕ) : (sortList α ℓ).Pairwise (· ≥ ·) := by
  have h : ((idxSort α ℓ)).Pairwise (keyRel α) := List.pairwise_insertionSort _ _
  rw [sortList, List.pairwise_map]
  exact h

/-- The entry list really is a rearrangement of `(α 0, …, α (ℓ-1))`. -/
lemma sortList_coe (α : ℕ → ℤ) (ℓ : ℕ) :
    ((sortList α ℓ : List ℤ) : Multiset ℤ) = (Finset.range ℓ).val.map α := by
  rw [sortList, ← Multiset.map_coe]
  congr 1
  exact Quot.sound (idxSort_perm α ℓ)

/-! ### The crux: the prefix of a descending list maximises the sum -/

/-- **The crux of `J = J'`.**  If `L` is weakly decreasing and `T` is a sub-multiset of
`L` with `r` elements, then `T.sum ≤ (L.take r).sum`: the sum of *any* `r` entries is at
most the sum of the `r` largest.  No hypothesis of positivity, and none on `r`. -/
lemma sum_le_sum_take : ∀ (L : List ℤ), L.Pairwise (· ≥ ·) → ∀ (r : ℕ) (T : Multiset ℤ),
    T ≤ (L : Multiset ℤ) → Multiset.card T = r → T.sum ≤ (L.take r).sum := by
  intro L
  induction L with
  | nil =>
      intro _ r T hT _
      rw [Multiset.coe_nil, Multiset.le_zero] at hT
      subst hT
      simp
  | cons a L' ih =>
      intro hL r T hT hcard
      have hhead : ∀ b ∈ L', a ≥ b := (List.pairwise_cons.mp hL).1
      have htail : L'.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hL).2
      have hcons : ((a :: L' : List ℤ) : Multiset ℤ) = a ::ₘ (L' : Multiset ℤ) := rfl
      rw [hcons] at hT
      match r with
      | 0 =>
          rw [Multiset.card_eq_zero] at hcard
          subst hcard
          simp
      | (r' + 1) =>
        by_cases ha : a ∈ T
        · have h1 : T.erase a ≤ (L' : Multiset ℤ) := by
            have := Multiset.erase_le_erase a hT
            rwa [Multiset.erase_cons_head] at this
          have h2 : Multiset.card (T.erase a) = r' := by
            rw [Multiset.card_erase_of_mem ha, hcard]; rfl
          have hIH := ih htail r' _ h1 h2
          have hTsum : T.sum = a + (T.erase a).sum := by
            conv_lhs => rw [← Multiset.cons_erase ha]
            simp
          rw [hTsum, List.take_succ_cons, List.sum_cons]
          linarith
        · have h1 : T ≤ (L' : Multiset ℤ) := (Multiset.le_cons_of_notMem ha).mp hT
          have hIH := ih htail (r' + 1) T h1 hcard
          have hlen : r' + 1 ≤ L'.length := by
            have := Multiset.card_le_card h1
            rwa [hcard, Multiset.coe_card] at this
          have hsplit : (L'.take (r' + 1)).sum = (L'.take r').sum + L'[r']'(by omega) :=
            List.sum_take_succ L' r' (by omega)
          have hle : L'[r']'(by omega) ≤ a := hhead _ (List.getElem_mem _)
          rw [List.take_succ_cons, List.sum_cons]
          linarith

/-! ### `psum` of `sortDesc` as a list prefix sum -/

lemma getD_lt {L : List ℤ} {c : ℕ} (h : c < L.length) : L.getD c 0 = L[c] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma getD_ge {L : List ℤ} {c : ℕ} (h : L.length ≤ c) : L.getD c 0 = 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma psum_getD (L : List ℤ) (r : ℕ) :
    psum (fun c => L.getD c 0) r = (L.take r).sum := by
  induction r with
  | zero => simp [psum]
  | succ n ih =>
      rw [psum_succ, ih]
      by_cases h : n < L.length
      · rw [List.sum_take_succ L n h, getD_lt h]
      · have hge : L.length ≤ n := by omega
        rw [getD_ge hge, List.take_of_length_le hge,
          List.take_of_length_le (show L.length ≤ n + 1 by omega)]
        ring

lemma psum_sortDesc (α : ℕ → ℤ) (ℓ r : ℕ) :
    psum (sortDesc α ℓ) r = ((sortList α ℓ).take r).sum :=
  psum_getD _ r

/-! ### `sortDesc` really is a sorted rearrangement -/

lemma sortDesc_vanish (α : ℕ → ℤ) (ℓ : ℕ) {c : ℕ} (h : ℓ ≤ c) : sortDesc α ℓ c = 0 :=
  getD_ge (by rw [sortList_length]; exact h)

/-- `sortDesc α ℓ` and `α` carry the same multiset of values on `[ℓ]`: it *is* a
rearrangement. -/
lemma sortDesc_map_range (α : ℕ → ℤ) (ℓ : ℕ) :
    (List.range ℓ).map (sortDesc α ℓ) = sortList α ℓ := by
  apply List.ext_getElem
  · simp [sortList_length]
  · intro n h1 h2
    simp only [List.getElem_map, List.getElem_range]
    change (sortList α ℓ).getD n 0 = _
    exact getD_lt h2

lemma sortDesc_multiset (α : ℕ → ℤ) (ℓ : ℕ) :
    (Finset.range ℓ).val.map (sortDesc α ℓ) = (Finset.range ℓ).val.map α := by
  rw [← sortList_coe α ℓ, ← sortDesc_map_range α ℓ, Finset.range_val, Multiset.range,
    Multiset.map_coe]

lemma sortList_mem_nonneg {α : ℕ → ℤ} (hα : ∀ c, 0 ≤ α c) (ℓ : ℕ) {x : ℤ}
    (h : x ∈ sortList α ℓ) : 0 ≤ x := by
  have h2 : x ∈ (idxSort α ℓ).map α := h
  rw [List.mem_map] at h2
  obtain ⟨i, _, hi⟩ := h2
  exact hi ▸ hα i

/-- `sortDesc α ℓ` is weakly decreasing — including across the boundary at `ℓ`, which is
where non-negativity of `α` is used. -/
lemma sortDesc_antitone {α : ℕ → ℤ} (hα : ∀ c, 0 ≤ α c) (ℓ : ℕ) :
    Antitone (sortDesc α ℓ) := by
  have hnn : ∀ c, 0 ≤ sortDesc α ℓ c := by
    intro c
    by_cases h : c < (sortList α ℓ).length
    · rw [sortDesc, getD_lt h]
      exact sortList_mem_nonneg hα ℓ (List.getElem_mem _)
    · rw [sortDesc, getD_ge (by omega)]
  apply antitone_nat_of_succ_le
  intro c
  by_cases h : c + 1 < (sortList α ℓ).length
  · have hc : c < (sortList α ℓ).length := by omega
    rw [sortDesc, sortDesc, getD_lt h, getD_lt hc]
    exact (List.pairwise_iff_getElem.mp (sortList_pairwise α ℓ)) c (c + 1) hc h (by omega)
  · rw [sortDesc, getD_ge (by omega)]
    exact hnn c

/-! ### `max_{|S| = r} α(S)` is the sum of the `r` largest -/

/-- Every `S ⊆ [ℓ]` has `α(S) ≤ Λ`-free sum of the `|S|` largest entries. -/
lemma asum_le_psum_sortDesc {ℓ : ℕ} (α : ℕ → ℤ) {S : Finset ℕ} (hS : S ⊆ Finset.range ℓ) :
    asum α S ≤ psum (sortDesc α ℓ) S.card := by
  rw [psum_sortDesc]
  have hsub : S.val.map α ≤ ((sortList α ℓ : List ℤ) : Multiset ℤ) := by
    rw [sortList_coe]
    exact Multiset.map_le_map (Finset.val_le_iff_val_subset.mpr hS)
  have hcard : Multiset.card (S.val.map α) = S.card := by simp
  have := sum_le_sum_take (sortList α ℓ) (sortList_pairwise α ℓ) S.card _ hsub hcard
  have hrfl : asum α S = (S.val.map α).sum := rfl
  rw [hrfl]
  exact this

/-- …and the bound is attained: the `r` largest entries sit on an actual `r`-subset of
`[ℓ]`, namely the first `r` indices of the sorting permutation. -/
lemma exists_subset_asum_eq {ℓ : ℕ} (α : ℕ → ℤ) {r : ℕ} (hr : r ≤ ℓ) :
    ∃ S ⊆ Finset.range ℓ, S.card = r ∧ asum α S = psum (sortDesc α ℓ) r := by
  classical
  set P := (idxSort α ℓ).take r with hP
  have hPnd : P.Nodup := (idxSort_nodup α ℓ).sublist (List.take_sublist _ _)
  have hPlen : P.length = r := by
    rw [hP, List.length_take, idxSort_length]; omega
  refine ⟨P.toFinset, ?_, ?_, ?_⟩
  · intro i hi
    rw [List.mem_toFinset, hP] at hi
    exact Finset.mem_range.mpr (idxSort_mem (List.mem_of_mem_take hi))
  · rw [List.toFinset_card_of_nodup hPnd, hPlen]
  · rw [psum_sortDesc, asum, List.sum_toFinset _ hPnd, hP, sortList, List.map_take]

/-! ### The target -/

/-- `J` in the paper's **sorted** form: `α ∈ ℕ^ℓ` with `sort(α) ⊴ λ̂`. -/
def InSuppSorted (ℓ : ℕ) (lhat α : ℕ → ℤ) : Prop :=
  (∀ c, ℓ ≤ c → α c = 0) ∧ (∀ c, 0 ≤ α c) ∧ psum α ℓ = psum lhat ℓ ∧
    Dom (sortDesc α ℓ) lhat

/-- **`J = J'`** — the first sentence of the proof of `prop:perm-mconvex`.  The sorted
form `sort(α) ⊴ λ̂` and the subset form `α(S) ≤ Λ_{|S|} ∀ S ⊆ [ℓ]` define the same set. -/
theorem insupp_iff_sorted {ℓ : ℕ} {lhat α : ℕ → ℤ} (hl : IsPart ℓ lhat) :
    InSupp ℓ lhat α ↔ InSuppSorted ℓ lhat α := by
  constructor
  · rintro ⟨hvan, hnn, hsize, hsub⟩
    refine ⟨hvan, hnn, hsize, ?_⟩
    intro r
    by_cases hr : r ≤ ℓ
    · obtain ⟨S, hS, hcard, heq⟩ := exists_subset_asum_eq α (ℓ := ℓ) hr
      have := hsub S (Finset.mem_powerset.mpr hS)
      rw [heq, hcard] at this
      exact this
    · push_neg at hr
      have h1 : psum (sortDesc α ℓ) r = psum (sortDesc α ℓ) ℓ := by
        rw [psum_split (sortDesc α ℓ) (le_of_lt hr)]
        have : ∑ c ∈ Finset.Ico ℓ r, sortDesc α ℓ c = 0 :=
          Finset.sum_eq_zero fun c hc =>
            sortDesc_vanish α ℓ (Finset.mem_Ico.mp hc).1
        omega
      have h2 : psum (sortDesc α ℓ) ℓ = psum α ℓ := by
        have := sortDesc_multiset α ℓ
        simpa [psum, Finset.sum] using congrArg Multiset.sum this
      have h3 : psum lhat ℓ ≤ psum lhat r := by
        rw [psum_split lhat (le_of_lt hr)]
        have : (0 : ℤ) ≤ ∑ c ∈ Finset.Ico ℓ r, lhat c :=
          Finset.sum_nonneg fun c _ => hl.nonneg c
        omega
      omega
  · rintro ⟨hvan, hnn, hsize, hdom⟩
    refine ⟨hvan, hnn, hsize, ?_⟩
    intro S hSmem
    exact le_trans (asum_le_psum_sortDesc α (Finset.mem_powerset.mp hSmem)) (hdom S.card)

/-- The M-convex exchange axiom for the **paper's** set `J = {α : sort(α) ⊴ λ̂}`.
Combines `MConvexExchange.insupp_exchange` with `insupp_iff_sorted`. -/
theorem sorted_exchange {ℓ : ℕ} {lhat α β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSuppSorted ℓ lhat α) (hβ : InSuppSorted ℓ lhat β) {i : ℕ} (hi : β i < α i) :
    ∃ j, α j < β j ∧ InSuppSorted ℓ lhat (ex i j α) := by
  obtain ⟨j, hj, hmem⟩ :=
    insupp_exchange hl ((insupp_iff_sorted hl).mpr hα) ((insupp_iff_sorted hl).mpr hβ) hi
  exact ⟨j, hj, (insupp_iff_sorted hl).mp hmem⟩

/-! ### Faithfulness of the definition, non-vacuity, and the negative control

`memory: a definition transported into Lean is unfalsifiable inside Lean.`  Three guards,
in increasing strength:

* `sortDesc_example` — `sortDesc` *computes* the descending rearrangement on a concrete
  input with distinct entries in scrambled order.  A wrong sorting direction, or a sort
  of the indices rather than the values, fails this by `decide`.
* `sortDesc_antitone` + `sortDesc_multiset` (above) — these two together **characterise**
  `sortDesc α ℓ` uniquely among functions vanishing off `[ℓ]`, and both are theorems, not
  definitions.  So the definition is falsifiable inside Lean, not only against the Python
  differential check in `proofs/code-q254-lean/`.
* `sorted_not_unsorted` — the **negative control**.  Deleting the word `sort` from
  `InSuppSorted` (i.e. asking for `Dom α λ̂` instead of `Dom (sort α) λ̂`) yields a
  *strictly weaker* condition: for `λ̂ = (3,1)`, `α = (0,4)` the unsorted condition holds
  and `InSupp` fails.  So `insupp_iff_sorted` is not true for trivial reasons, and the
  sort is doing the work.
-/
section Guards

private def a132 : ℕ → ℤ := fun c => if c = 0 then 1 else if c = 1 then 3 else
  if c = 2 then 2 else 0

/-- `sortDesc` really sorts, and in the decreasing direction. -/
theorem sortDesc_example :
    sortDesc a132 3 0 = 3 ∧ sortDesc a132 3 1 = 2 ∧ sortDesc a132 3 2 = 1 ∧
      sortDesc a132 3 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

private def lhat31 : ℕ → ℤ := fun c => if c = 0 then 3 else if c = 1 then 1 else 0
private def a04 : ℕ → ℤ := fun c => if c = 1 then 4 else 0

private lemma lhat31_isPart : IsPart 2 lhat31 := by
  constructor
  · apply antitone_nat_of_succ_le
    intro c
    simp only [lhat31]
    split_ifs <;> first | (exfalso; assumption) | omega
  · intro c hc; simp only [lhat31]; split_ifs <;> omega

/-- **Negative control.**  `α = (0,4)` satisfies the *unsorted* dominance condition
`∀ r, psum α r ≤ Λ_r` together with the size condition, yet is **not** in `J'` — its
largest entry `4` exceeds `Λ_1 = 3`.  Hence `insupp_iff_sorted` fails outright if `sort`
is dropped: a check that cannot fail is not a check. -/
theorem sorted_not_unsorted :
    (∀ c, (2 : ℕ) ≤ c → a04 c = 0) ∧ (∀ c, 0 ≤ a04 c) ∧ psum a04 2 = psum lhat31 2 ∧
      Dom a04 lhat31 ∧ ¬ InSupp 2 lhat31 a04 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [a04]; split_ifs <;> omega
  · intro c; simp only [a04]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, a04, lhat31]
  · intro r
    induction r with
    | zero => simp [psum]
    | succ n ih =>
        rw [psum_succ, psum_succ]
        have h1 : a04 n ≤ lhat31 n ∨ n = 1 := by
          simp only [a04, lhat31]; split_ifs <;> omega
        rcases h1 with h | rfl
        · omega
        · simp [psum, a04, lhat31]
  · intro h
    have := h.2.2.2 {1} (by decide)
    simp [asum, psum, a04, lhat31] at this

/-- Non-vacuity of the target: the sorted-form set is inhabited and `sorted_exchange`
delivers a genuine move on it (`λ̂ = (2,1)`, `α = (2,1) ↦ (1,2) = β`). -/
theorem insupp_sorted_witness :
    InSuppSorted 2 MConvexExchange.lhat21 MConvexExchange.al21 ∧
      ∃ j, MConvexExchange.al21 j < MConvexExchange.be12 j ∧
        InSuppSorted 2 MConvexExchange.lhat21 (ex 0 j MConvexExchange.al21) := by
  have hα := (insupp_iff_sorted MConvexExchange.lhat21_isPart).mp MConvexExchange.al21_mem
  have hβ := (insupp_iff_sorted MConvexExchange.lhat21_isPart).mp MConvexExchange.be12_mem
  exact ⟨hα, sorted_exchange MConvexExchange.lhat21_isPart hα hβ
    (i := 0) (by norm_num [MConvexExchange.al21, MConvexExchange.be12])⟩

end Guards

end SortedBridge
