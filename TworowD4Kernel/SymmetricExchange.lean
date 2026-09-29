/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SortedSubsetBridge

/-!
# B-EXC: Murota's **symmetric** exchange axiom for `J = {α : sort(α) ⊴ λ̂}`

`MConvexExchange.insupp_exchange` and `SortedBridge.sorted_exchange` prove the *one-sided*
exchange axiom — the definition of M-convexity quoted in
`projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex` §"The problem" and used
throughout the SNP / Lorentzian literature (WZZ, Brändén–Huh).  Murota's axiom **(B-EXC)**
demands more: the *same* `j` must also serve `β`.

    ∀ α β ∈ J, ∀ i, β i < α i → ∃ j, α j < β j ∧ α - eᵢ + e_j ∈ J ∧ β + eᵢ - e_j ∈ J

That is `insupp_symm_exchange` (subset form) and `sorted_symm_exchange` (the paper's own
sorted form) below.  Until this file, B-EXC was carried by brute force alone
(`proofs/code-q254-lean/`), and was flagged as owed in the docstrings of
`MConvexExchange` and `SortedSubsetBridge`, in the registry node
`polymatroid-exchange` and its parent, and in two commit messages.

## Where the proof comes from

The paper does **not** prove B-EXC; its argument stops at the one-sided form, and the
Murota–Shioura theorem that the two axioms cut out the same class is neither formalised
nor used here.  What is formalised is the classical argument for bases of an integral
submodular system, in the form armed in `state/LEAN.md` 2026-09-29 c1 §4: apply
`tight_union`/`tight_inter` to `α` **and** `β` and intersect the admissible sets for `j`.
Concretely, with `ρ(S) = Λ_{|S|}` and "tight" meaning `α(S) = ρ(S)`:

* `A = tightAvoid` — the **union** of all `α`-tight sets avoiding `i`.  It is `α`-tight
  (`tight_union`), and `j` makes `α - eᵢ + e_j ∈ J` exactly when `j ∉ A`.
* `B = minTight` — the **intersection** of all `β`-tight sets containing `i`.  It is
  `β`-tight (`tight_inter`), and `j` makes `β + eᵢ - e_j ∈ J` exactly when `j ∈ B`.

Then `B \ A` is nonempty at `i`, and the two-line chain

    α(B \ A) ≤ ρ(|A ∪ B|) - ρ(|A|) ≤ ρ(|B|) - ρ(|A ∩ B|) ≤ β(B \ A)

(the middle step is `rank_submodular`) forces some `j ∈ B \ A` other than `i` to have
`α j < β j`, since the `i`-term of `β - α` on `B \ A` is negative.  That `j` is the
witness.  Nothing here is postulated: submodularity of `ρ` is *derived* in
`MConvexExchange.rank_submodular` from `λ̂` being antitone.

## Falsifiability

`memory: a definition transported into Lean is unfalsifiable inside Lean.`  B-EXC is
stated as Murota states it — a literal second membership `InSupp ℓ lhat (ex j i β)` — not
as a definition engineered to hold.  The guard is the **negative control**
`symm_conjunct_not_automatic` at the end of the file: a concrete `(λ̂, α, β, i)` and a `j`
with `α j < β j` and `α - eᵢ + e_j ∈ J` for which `β + eᵢ - e_j ∉ J`.  So the second
conjunct is *not* implied by the first, and `insupp_symm_exchange` is strictly stronger
than `insupp_exchange` rather than a restatement of it.

Brute force, from the definitions, independent of this file
(`proofs/code-q254-lean/bexc_symmetric_check.py`): 0 B-EXC failures, and the witness set
predicted by the proof above, `{j : α j < β j} ∩ (B \ A)`, agrees with the true set of
good `j` **exactly** (not merely nonempty) on every triple in range.

Indices are 0-based (the paper is 1-based).  `Λ_r` is `psum lhat r`; `ex i j α` is
`α - eᵢ + e_j`, so `β + eᵢ - e_j` is `ex j i β`.
-/

namespace SymmetricExchange

open Finset RobinHood MConvexExchange

/-! ### The tight family is closed under intersection

`MConvexExchange.tight_union` is the union half (the paper's `lem:tight`).  The
intersection half comes from the same inequality and is what pins down the *minimal*
tight set containing a given index. -/

/-- **Mirror of `lem:tight`**: for `α ∈ J` the tight family `F_α = {S : α(S) = ρ(S)}` is
closed under intersection.  Same three ingredients as `tight_union`: the modular identity
for `asum`, the two `J`-inequalities, and `rank_submodular`. -/
lemma tight_inter {ℓ : ℕ} {lhat α : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) {S T : Finset ℕ}
    (hS : S ⊆ Finset.range ℓ) (hT : T ⊆ Finset.range ℓ)
    (htS : asum α S = psum lhat S.card) (htT : asum α T = psum lhat T.card) :
    asum α (S ∩ T) = psum lhat (S ∩ T).card := by
  classical
  have hsum : asum α (S ∪ T) + asum α (S ∩ T) = asum α S + asum α T :=
    Finset.sum_union_inter
  have hU : asum α (S ∪ T) ≤ psum lhat (S ∪ T).card :=
    hα.2.2.2 _ (Finset.mem_powerset.mpr (Finset.union_subset hS hT))
  have hI : asum α (S ∩ T) ≤ psum lhat (S ∩ T).card :=
    hα.2.2.2 _ (Finset.mem_powerset.mpr (Finset.inter_subset_left.trans hS))
  have hsub := rank_submodular hl S T
  linarith

/-! ### `A`: the maximal `α`-tight set avoiding `i` -/

/-- The union of all `α`-tight subsets of `[ℓ]` avoiding `i`.  By `tight_union` it is
itself tight, and it is the obstruction set for the surgery `α - eᵢ + e_j`. -/
def tightAvoid (ℓ : ℕ) (lhat α : ℕ → ℤ) (i : ℕ) : Finset ℕ :=
  ((Finset.range ℓ).powerset.filter
    (fun S => i ∉ S ∧ asum α S = psum lhat S.card)).sup id

lemma tightAvoid_spec {ℓ : ℕ} {lhat α : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) (i : ℕ) :
    tightAvoid ℓ lhat α i ⊆ Finset.range ℓ ∧ i ∉ tightAvoid ℓ lhat α i ∧
      asum α (tightAvoid ℓ lhat α i) = psum lhat (tightAvoid ℓ lhat α i).card := by
  classical
  refine Finset.sup_induction
    (p := fun T => T ⊆ Finset.range ℓ ∧ i ∉ T ∧ asum α T = psum lhat T.card)
    ⟨by simp, by simp, by simp [asum, psum]⟩ ?_ ?_
  · rintro a ⟨ha1, ha2, ha3⟩ b ⟨hb1, hb2, hb3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.sup_eq_union]; exact Finset.union_subset ha1 hb1
    · rw [Finset.sup_eq_union, Finset.mem_union]; tauto
    · rw [Finset.sup_eq_union]; exact tight_union hl hα ha1 hb1 ha3 hb3
  · intro S hS
    obtain ⟨hmem, hi, ht⟩ := Finset.mem_filter.mp hS
    exact ⟨Finset.mem_powerset.mp hmem, hi, ht⟩

/-- Every `α`-tight set avoiding `i` is contained in `A`; this is the direction that
turns `j ∉ A` into "no tight set blocks the surgery". -/
lemma subset_tightAvoid {ℓ : ℕ} {lhat α : ℕ → ℤ} {i : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range ℓ) (hi : i ∉ S) (ht : asum α S = psum lhat S.card) :
    S ⊆ tightAvoid ℓ lhat α i := by
  classical
  exact Finset.le_sup (f := id)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hi, ht⟩)

/-! ### `B`: the minimal `β`-tight set containing `i`

`Finset ℕ` has no `⊤`, so the intersection of a family cannot be written as a
`Finset.inf`.  It is taken instead as the complement, inside `[ℓ]`, of the **union of the
complements** — and the closure property that union needs is `tight_inter`. -/

/-- The union of the complements (inside `[ℓ]`) of all `β`-tight sets containing `i`. -/
def tightCoContain (ℓ : ℕ) (lhat β : ℕ → ℤ) (i : ℕ) : Finset ℕ :=
  ((Finset.range ℓ).powerset.filter
    (fun S => i ∈ S ∧ asum β S = psum lhat S.card)).sup (fun S => Finset.range ℓ \ S)

/-- **`B`** — the intersection of all `β`-tight subsets of `[ℓ]` containing `i`.  The
family is never empty: `[ℓ]` itself is tight, because `β([ℓ]) = |λ̂| = Λ_ℓ`. -/
def minTight (ℓ : ℕ) (lhat β : ℕ → ℤ) (i : ℕ) : Finset ℕ :=
  Finset.range ℓ \ tightCoContain ℓ lhat β i

lemma tightCoContain_spec {ℓ : ℕ} {lhat β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hβ : InSupp ℓ lhat β) (i : ℕ) :
    tightCoContain ℓ lhat β i ⊆ Finset.range ℓ ∧ i ∉ tightCoContain ℓ lhat β i ∧
      asum β (Finset.range ℓ \ tightCoContain ℓ lhat β i)
        = psum lhat (Finset.range ℓ \ tightCoContain ℓ lhat β i).card := by
  classical
  refine Finset.sup_induction
    (p := fun T => T ⊆ Finset.range ℓ ∧ i ∉ T ∧
      asum β (Finset.range ℓ \ T) = psum lhat (Finset.range ℓ \ T).card)
    ⟨by simp, by simp, ?_⟩ ?_ ?_
  · -- `T = ∅`: the whole of `[ℓ]` is tight, since `β([ℓ]) = Λ_ℓ`.
    simp only [Finset.bot_eq_empty, Finset.sdiff_empty, Finset.card_range]
    exact hβ.2.2.1
  · rintro a ⟨ha1, ha2, ha3⟩ b ⟨hb1, hb2, hb3⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.sup_eq_union]; exact Finset.union_subset ha1 hb1
    · rw [Finset.sup_eq_union, Finset.mem_union]; tauto
    · rw [Finset.sup_eq_union, Finset.sdiff_union_distrib]
      exact tight_inter hl hβ (Finset.sdiff_subset) (Finset.sdiff_subset) ha3 hb3
  · intro S hS
    obtain ⟨hmem, hi, ht⟩ := Finset.mem_filter.mp hS
    have hSr : S ⊆ Finset.range ℓ := Finset.mem_powerset.mp hmem
    refine ⟨Finset.sdiff_subset, ?_, ?_⟩
    · simp only [Finset.mem_sdiff]; tauto
    · rw [Finset.sdiff_sdiff_eq_self hSr]; exact ht

lemma minTight_subset {ℓ : ℕ} {lhat β : ℕ → ℤ} {i : ℕ} :
    minTight ℓ lhat β i ⊆ Finset.range ℓ := Finset.sdiff_subset

lemma mem_minTight {ℓ : ℕ} {lhat β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hβ : InSupp ℓ lhat β) {i : ℕ} (hi : i < ℓ) : i ∈ minTight ℓ lhat β i :=
  Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hi, (tightCoContain_spec hl hβ i).2.1⟩

lemma minTight_tight {ℓ : ℕ} {lhat β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hβ : InSupp ℓ lhat β) (i : ℕ) :
    asum β (minTight ℓ lhat β i) = psum lhat (minTight ℓ lhat β i).card :=
  (tightCoContain_spec hl hβ i).2.2

/-- The defining property of `B`: it is contained in every `β`-tight set containing `i`.
This is the direction that turns `j ∈ B` into "no tight set blocks the surgery
`β + eᵢ - e_j`". -/
lemma minTight_subset_of_tight {ℓ : ℕ} {lhat β : ℕ → ℤ} {i : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range ℓ) (hi : i ∈ S) (ht : asum β S = psum lhat S.card) :
    minTight ℓ lhat β i ⊆ S := by
  classical
  intro j hj
  obtain ⟨hjr, hjc⟩ := Finset.mem_sdiff.mp hj
  by_contra hjS
  exact hjc (Finset.le_sup (f := fun S => Finset.range ℓ \ S)
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS, hi, ht⟩)
    (Finset.mem_sdiff.mpr ⟨hjr, hjS⟩))

/-! ### The counting step

This is the step the one-sided argument does not need.  `α` is tight on `A` and `β` is
tight on `B`, so the submodular inequality squeezes `α(B \ A) ≤ β(B \ A)`; since `i` sits
in `B \ A` and contributes `β i - α i < 0`, some other index of `B \ A` must contribute
positively. -/

private lemma sdiff_union_left (A B : Finset ℕ) : (A ∪ B) \ A = B \ A := by
  ext x; simp only [Finset.mem_sdiff, Finset.mem_union]; tauto

private lemma sdiff_inter_left (A B : Finset ℕ) : B \ (A ∩ B) = B \ A := by
  ext x; simp only [Finset.mem_sdiff, Finset.mem_inter]; tauto

/-- **`α(B \ A) ≤ β(B \ A)`.**  The chain
`α(B \ A) = α(A ∪ B) - α(A) ≤ ρ(|A ∪ B|) - ρ(|A|) ≤ ρ(|B|) - ρ(|A ∩ B|) ≤ β(B \ A)`,
whose middle inequality is `rank_submodular`. -/
lemma asum_sdiff_le {ℓ : ℕ} {lhat α β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) (hβ : InSupp ℓ lhat β)
    {A B : Finset ℕ} (hA : A ⊆ Finset.range ℓ) (hB : B ⊆ Finset.range ℓ)
    (htA : asum α A = psum lhat A.card) (htB : asum β B = psum lhat B.card) :
    asum α (B \ A) ≤ asum β (B \ A) := by
  classical
  have hsplitα : asum α (B \ A) + asum α A = asum α (A ∪ B) := by
    have := Finset.sum_sdiff (f := α) (Finset.subset_union_left (s₁ := A) (s₂ := B))
    rwa [sdiff_union_left] at this
  have hsplitβ : asum β (B \ A) + asum β (A ∩ B) = asum β B := by
    have := Finset.sum_sdiff (f := β) (Finset.inter_subset_right (s₁ := A) (s₂ := B))
    rwa [sdiff_inter_left] at this
  have hαU : asum α (A ∪ B) ≤ psum lhat (A ∪ B).card :=
    hα.2.2.2 _ (Finset.mem_powerset.mpr (Finset.union_subset hA hB))
  have hβI : asum β (A ∩ B) ≤ psum lhat (A ∩ B).card :=
    hβ.2.2.2 _ (Finset.mem_powerset.mpr (Finset.inter_subset_left.trans hA))
  have hsubmod := rank_submodular hl A B
  linarith

/-- The counting step.  Some index of `B \ A` other than `i` gains from `α` to `β`. -/
lemma exists_gain_in_sdiff {ℓ : ℕ} {lhat α β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) (hβ : InSupp ℓ lhat β) {i : ℕ}
    {A B : Finset ℕ} (hA : A ⊆ Finset.range ℓ) (hB : B ⊆ Finset.range ℓ)
    (hiA : i ∉ A) (hiB : i ∈ B)
    (htA : asum α A = psum lhat A.card) (htB : asum β B = psum lhat B.card)
    (hi : β i < α i) :
    ∃ j ∈ B \ A, j ≠ i ∧ α j < β j := by
  classical
  have hle := asum_sdiff_le hl hα hβ hA hB htA htB
  have hiT : i ∈ B \ A := Finset.mem_sdiff.mpr ⟨hiB, hiA⟩
  by_contra hcon
  push_neg at hcon
  -- every index of `B \ A` other than `i` has `β ≤ α`
  have hnonpos : ∀ c ∈ (B \ A).erase i, β c - α c ≤ 0 := by
    intro c hc
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hc
    have := hcon c hmem hne
    omega
  have hsum : (β i - α i) + ∑ c ∈ (B \ A).erase i, (β c - α c)
      = ∑ c ∈ B \ A, (β c - α c) :=
    Finset.add_sum_erase (B \ A) (fun c => β c - α c) hiT
  have htail : ∑ c ∈ (B \ A).erase i, (β c - α c) ≤ 0 := Finset.sum_nonpos hnonpos
  have htot : ∑ c ∈ B \ A, (β c - α c) = asum β (B \ A) - asum α (B \ A) := by
    simp only [asum, Finset.sum_sub_distrib]
  linarith

/-! ### B-EXC -/

/-- **Murota's symmetric exchange axiom (B-EXC)** for
`J = {α ∈ ℕ^ℓ : α([ℓ]) = |λ̂|, α(S) ≤ Λ_{|S|} ∀ S ⊆ [ℓ]}`:

> for all `α, β ∈ J` and every index `i` with `β i < α i` there is an index `j` with
> `α j < β j` such that **both** `α - eᵢ + e_j ∈ J` **and** `β + eᵢ - e_j ∈ J`.

The `j` produced is any element of `B \ A` other than `i` on which `β` exceeds `α`, where
`A = tightAvoid` and `B = minTight`.  Strictly stronger than
`MConvexExchange.insupp_exchange`: see `symm_conjunct_not_automatic`. -/
theorem insupp_symm_exchange {ℓ : ℕ} {lhat α β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) (hβ : InSupp ℓ lhat β) {i : ℕ} (hi : β i < α i) :
    ∃ j, α j < β j ∧ InSupp ℓ lhat (ex i j α) ∧ InSupp ℓ lhat (ex j i β) := by
  classical
  have hiℓ : i < ℓ := by
    by_contra h
    push_neg at h
    rw [hα.1 i h, hβ.1 i h] at hi
    omega
  obtain ⟨hA1, hA2, hA3⟩ := tightAvoid_spec hl hα i
  obtain ⟨j, hjmem, hjne, hjlt⟩ :=
    exists_gain_in_sdiff hl hα hβ hA1 (minTight_subset (lhat := lhat) (β := β) (i := i))
      hA2 (mem_minTight hl hβ hiℓ) hA3 (minTight_tight hl hβ i) hi
  obtain ⟨hjB, hjA⟩ := Finset.mem_sdiff.mp hjmem
  have hjℓ : j < ℓ := Finset.mem_range.mp (minTight_subset hjB)
  refine ⟨j, hjlt, ?_, ?_⟩
  · -- `α - eᵢ + e_j ∈ J`: no `α`-tight set contains `j` and avoids `i`, since all of them
    -- are contained in `A` and `j ∉ A`.
    refine insupp_ex_of_no_tight hα hiℓ hjℓ (Ne.symm hjne) (by have := hβ.2.1 i; omega) ?_
    intro S hS hjS hiS htight
    exact hjA (subset_tightAvoid hS hiS htight hjS)
  · -- `β + eᵢ - e_j = ex j i β ∈ J`: no `β`-tight set contains `i` and avoids `j`, since
    -- all of them contain `B` and `j ∈ B`.
    refine insupp_ex_of_no_tight hβ hjℓ hiℓ hjne (by have := hα.2.1 j; omega) ?_
    intro S hS hiS hjS htight
    exact hjS (minTight_subset_of_tight hS hiS htight hjB)

/-- **B-EXC for the paper's own object** `J = {α : sort(α) ⊴ λ̂}`, via
`SortedBridge.insupp_iff_sorted`.  This is the statement a reader of
`2026-09-20-c1-cylindric-M-convexity.tex` needs. -/
theorem sorted_symm_exchange {ℓ : ℕ} {lhat α β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : SortedBridge.InSuppSorted ℓ lhat α) (hβ : SortedBridge.InSuppSorted ℓ lhat β)
    {i : ℕ} (hi : β i < α i) :
    ∃ j, α j < β j ∧ SortedBridge.InSuppSorted ℓ lhat (ex i j α) ∧
      SortedBridge.InSuppSorted ℓ lhat (ex j i β) := by
  obtain ⟨j, hj, h1, h2⟩ :=
    insupp_symm_exchange hl ((SortedBridge.insupp_iff_sorted hl).mpr hα)
      ((SortedBridge.insupp_iff_sorted hl).mpr hβ) hi
  exact ⟨j, hj, (SortedBridge.insupp_iff_sorted hl).mp h1,
    (SortedBridge.insupp_iff_sorted hl).mp h2⟩

/-! ### The negative control, and non-vacuity

`memory: a definition transported into Lean is unfalsifiable inside Lean`, and
`memory: a theorem whose hypotheses are never satisfiable type-checks perfectly.`  Two
guards.

**The negative control** is the one that matters here, because the entire content of
B-EXC over `MConvexExchange.insupp_exchange` is the words "for the same `j`".  If the
second conjunct followed from the first, `insupp_symm_exchange` would be a restatement of
`insupp_exchange` and its proof — `tight_inter`, `minTight`, the submodular squeeze —
would all be dead weight.  It does not: on

  `ℓ = 4`,  `λ̂ = (2,1,1,0)`,  `α = (1,0,1,2)`,  `β = (0,1,2,1)`,  `i = 3`

there are exactly two candidates `j` with `α j < β j`, and they behave differently.

* `j = 1` satisfies the conclusion of `insupp_exchange` — `α - e₃ + e₁ = (1,1,1,1) ∈ J` —
  and **fails** B-EXC: `β + e₃ - e₁ = (0,0,2,2) ∉ J`, since its two largest entries sum
  to `4 > Λ₂ = 3`.
* `j = 2` satisfies both: `α - e₃ + e₂ = (1,0,2,1) ∈ J` and `β + e₃ - e₂ = (0,1,1,2) ∈ J`.

So `insupp_exchange` may legitimately return `j = 1` and `insupp_symm_exchange` may not;
the theorem constrains the witness, and the constraint bites.

This is the **minimal** such configuration: an exhaustive search
(`proofs/code-q254-lean/bexc_symmetric_check.py`) finds no negative control at all for
`ℓ ≤ 3`, and at `ℓ = 4` the smallest `|λ̂|` admitting one is `4`, where `λ̂ = (2,1,1)` is
the unique partition that does.  Compare the 2026-09-26 session, where the brief's
negative control turned out to be *impossible* because the dropped half-space was
redundant; here it exists, and 1152 one-sided witnesses fail symmetrically within
`|λ̂| ≤ 7, ℓ ≤ 4` alone. -/

section Control

/-- `λ̂ = (2,1,1,0)`. -/
def lhat2110 : ℕ → ℤ := fun c =>
  if c = 0 then 2 else if c = 1 then 1 else if c = 2 then 1 else 0
/-- `α = (1,0,1,2)`. -/
def a1012 : ℕ → ℤ := fun c =>
  if c = 0 then 1 else if c = 1 then 0 else if c = 2 then 1 else if c = 3 then 2 else 0
/-- `β = (0,1,2,1)`. -/
def b0121 : ℕ → ℤ := fun c =>
  if c = 1 then 1 else if c = 2 then 2 else if c = 3 then 1 else 0

lemma lhat2110_isPart : IsPart 4 lhat2110 := by
  constructor
  · apply antitone_nat_of_succ_le
    intro c
    simp only [lhat2110]
    split_ifs <;> first | (exfalso; assumption) | omega
  · intro c hc; simp only [lhat2110]; split_ifs <;> omega

lemma a1012_mem : InSupp 4 lhat2110 a1012 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [a1012]; split_ifs <;> omega
  · intro c; simp only [a1012]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, a1012, lhat2110]
  · decide

lemma b0121_mem : InSupp 4 lhat2110 b0121 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [b0121]; split_ifs <;> omega
  · intro c; simp only [b0121]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, b0121, lhat2110]
  · decide

private lemma ex_mem (i j : ℕ) (α : ℕ → ℤ) (hvan : ∀ c, 4 ≤ c → α c = 0)
    (hi : i < 4) (hj : j < 4) (hnn : ∀ c, 0 ≤ ex i j α c)
    (hsize : psum (ex i j α) 4 = psum lhat2110 4)
    (hsub : ∀ S ∈ (Finset.range 4).powerset, asum (ex i j α) S ≤ psum lhat2110 S.card) :
    InSupp 4 lhat2110 (ex i j α) := by
  refine ⟨?_, hnn, hsize, hsub⟩
  intro c hc
  have h1 : c ≠ i := by omega
  have h2 : c ≠ j := by omega
  simp only [ex, if_neg h1, if_neg h2]
  simpa using hvan c hc

lemma a1012_ex31_mem : InSupp 4 lhat2110 (ex 3 1 a1012) := by
  refine ex_mem 3 1 a1012 (fun c hc => by simp only [a1012]; split_ifs <;> omega)
    (by omega) (by omega) ?_ ?_ ?_
  · intro c; simp only [ex, a1012]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, ex, a1012, lhat2110]
  · decide

lemma a1012_ex32_mem : InSupp 4 lhat2110 (ex 3 2 a1012) := by
  refine ex_mem 3 2 a1012 (fun c hc => by simp only [a1012]; split_ifs <;> omega)
    (by omega) (by omega) ?_ ?_ ?_
  · intro c; simp only [ex, a1012]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, ex, a1012, lhat2110]
  · decide

lemma b0121_ex23_mem : InSupp 4 lhat2110 (ex 2 3 b0121) := by
  refine ex_mem 2 3 b0121 (fun c hc => by simp only [b0121]; split_ifs <;> omega)
    (by omega) (by omega) ?_ ?_ ?_
  · intro c; simp only [ex, b0121]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, ex, b0121, lhat2110]
  · decide

/-- **Negative control.**  The symmetric conjunct of B-EXC is *not* automatic: `j = 1`
discharges the conclusion of `MConvexExchange.insupp_exchange` on this data and violates
B-EXC, while `j = 2` discharges both.  Hence `insupp_symm_exchange` is strictly stronger
than `insupp_exchange`, and is not a tautology dressed as a theorem. -/
theorem symm_conjunct_not_automatic :
    -- the hypotheses of `insupp_symm_exchange` hold on this data
    IsPart 4 lhat2110 ∧ InSupp 4 lhat2110 a1012 ∧ InSupp 4 lhat2110 b0121 ∧
      b0121 3 < a1012 3 ∧
    -- `j = 1`: one-sided YES, symmetric NO
    (a1012 1 < b0121 1 ∧ InSupp 4 lhat2110 (ex 3 1 a1012) ∧
      ¬ InSupp 4 lhat2110 (ex 1 3 b0121)) ∧
    -- `j = 2`: both YES
    (a1012 2 < b0121 2 ∧ InSupp 4 lhat2110 (ex 3 2 a1012) ∧
      InSupp 4 lhat2110 (ex 2 3 b0121)) := by
  refine ⟨lhat2110_isPart, a1012_mem, b0121_mem, by norm_num [a1012, b0121],
    ⟨by norm_num [a1012, b0121], a1012_ex31_mem, ?_⟩,
    ⟨by norm_num [a1012, b0121], a1012_ex32_mem, b0121_ex23_mem⟩⟩
  -- `β + e₃ - e₁ = (0,0,2,2)` puts `4` on the two-element set `{2,3}`, but `Λ₂ = 3`.
  intro h
  have hbad := h.2.2.2 ({2, 3} : Finset ℕ) (by decide)
  revert hbad
  decide

/-- Non-vacuity: `insupp_symm_exchange` fires on satisfiable hypotheses and the `j` it
returns is one of the two candidates, necessarily **not** the one ruled out above. -/
theorem symm_exchange_fires_on_control :
    ∃ j, a1012 j < b0121 j ∧ InSupp 4 lhat2110 (ex 3 j a1012) ∧
      InSupp 4 lhat2110 (ex j 3 b0121) :=
  insupp_symm_exchange lhat2110_isPart a1012_mem b0121_mem
    (i := 3) (by norm_num [a1012, b0121])

/-- Non-vacuity in the paper's own sorted form, on the `ℓ = 2` witness `λ̂ = (2,1)`:
`α = (2,1) ↦ (1,2)` and `β = (1,2) ↦ (2,1)` simultaneously. -/
theorem sorted_symm_exchange_witness :
    ∃ j, MConvexExchange.al21 j < MConvexExchange.be12 j ∧
      SortedBridge.InSuppSorted 2 MConvexExchange.lhat21 (ex 0 j MConvexExchange.al21) ∧
      SortedBridge.InSuppSorted 2 MConvexExchange.lhat21 (ex j 0 MConvexExchange.be12) :=
  sorted_symm_exchange MConvexExchange.lhat21_isPart
    ((SortedBridge.insupp_iff_sorted MConvexExchange.lhat21_isPart).mp
      MConvexExchange.al21_mem)
    ((SortedBridge.insupp_iff_sorted MConvexExchange.lhat21_isPart).mp
      MConvexExchange.be12_mem)
    (i := 0) (by norm_num [MConvexExchange.al21, MConvexExchange.be12])

end Control

end SymmetricExchange
