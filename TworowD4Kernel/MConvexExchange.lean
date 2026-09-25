/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.RobinHood

/-!
# The M-convex exchange axiom for `{α : sort(α) ⊴ λ̂}`

Formalisation of Proposition `prop:perm-mconvex` (and its Lemma `lem:tight`) of
`projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex`, the fourth and last pillar of
that paper's `thm:main`.

## Which rung, and what is assumed

*Rung 1 of the LEAN.md ladder, for the paper's own definition of M-convexity, with no
bound on `ℓ` and no bound on `λ̂`.*  Precisely what is **proved** here is

> `insupp_exchange` : for all `α, β ∈ J` and every `i` with `β i < α i` there is a `j`
> with `α j < β j` and `α - eᵢ + e_j ∈ J`,

which is the definition of M-convexity quoted verbatim in the paper (§"The problem",
lines 95--97 of the `.tex`), and the definition used throughout the SNP / Lorentzian
literature (WZZ, Brändén--Huh).  Murota's symmetric axiom (B-EXC) additionally demands
`β + eᵢ - e_j ∈ J` **for the same `j`**; that is *not* proved here, and the paper's
argument does not deliver it either.  The two axioms define the same class of sets by a
theorem of Murota--Shioura which is **not formalised** and **not used**.  The symmetric
form is instead checked by brute force in `proofs/code-q254-lean/`
(0 failures / 876317 triples `(α, β, i)`, all `λ̂` with `|λ̂| ≤ 9`, `ℓ ≤ 4`).

What is **assumed, not proved**: nothing.  No axiom, no `sorry`, no import of the
paper's conclusion.  Submodularity of the rank function is *derived* from `λ̂` being
antitone (`rank_submodular`), not postulated.

## What Lean cannot see

`J` is formalised in the **subset form**

  `α(S) ≤ Λ_{|S|}` for every `S ⊆ [ℓ]`, together with `α([ℓ]) = |λ̂|`,

not in the sorted form `sort(α) ⊴ λ̂`.  The paper asserts these describe the same set in
the first sentence of the proof of `prop:perm-mconvex` ("because `max_{|S|=r} α(S)` is
the sum of the `r` largest entries of `α`").  **That sentence is not formalised in this
file** — but it is no longer unformalised: it is `SortedBridge.insupp_iff_sorted` in
`TworowD4Kernel/SortedSubsetBridge.lean` (2026-09-25 c2), which also derives the exchange
axiom for the paper's own sorted-form `J` as `SortedBridge.sorted_exchange`.  So a reader
who needs the paper's object should cite `SortedBridge.sorted_exchange`, not
`insupp_exchange`.  The differential enumeration in
`proofs/code-q254-lean/mconvex_exchange_check.py` remains as an independent check of the
identification (0 disagreements / 1804 pairs `(λ̂, ℓ)`, `|λ̂| ≤ 16`, `ℓ ≤ 6`).

Cf. `memory: a-definition-transported-into-Lean-is-unfalsifiable-inside-Lean`.  The
guard applied here is that `InSupp` is stated as literal integer inequalities on sums —
so `insupp_exchange` is falsifiable inside Lean — plus the non-vacuity witness and the
negative control at the end of the file.

## Conventions

Indices are 0-based (the paper is 1-based).  The vocabulary `IsPart`, `psum`, `ex` and
the surgery lemma `psum_ex` are reused verbatim from `RobinHood`; `ex i j α` is the
paper's `α - eᵢ + e_j`.
-/

namespace MConvexExchange

open Finset RobinHood

/-- `asum α S = α(S) = ∑_{c ∈ S} α c`, the paper's `α(S)`. -/
def asum (α : ℕ → ℤ) (S : Finset ℕ) : ℤ := ∑ c ∈ S, α c

@[simp] lemma asum_empty (α : ℕ → ℤ) : asum α ∅ = 0 := rfl

lemma asum_range (α : ℕ → ℤ) (r : ℕ) : asum α (Finset.range r) = psum α r := rfl

/-- `α` lies in `J = {α ∈ ℕ^ℓ : α([ℓ]) = |λ̂|, α(S) ≤ Λ_{|S|} ∀ S ⊆ [ℓ]}`.

The last clause quantifies over `(range ℓ).powerset` rather than over all `S ⊆ range ℓ`
so that the predicate is *decidable* on concrete data; `Finset.mem_powerset` moves
between the two forms. -/
def InSupp (ℓ : ℕ) (lhat α : ℕ → ℤ) : Prop :=
  (∀ c, ℓ ≤ c → α c = 0) ∧ (∀ c, 0 ≤ α c) ∧ psum α ℓ = psum lhat ℓ ∧
    ∀ S ∈ (Finset.range ℓ).powerset, asum α S ≤ psum lhat S.card

/-- `α(S)` after the surgery `α - eᵢ + e_j`: one unit moves iff exactly one of `i`, `j`
lies in `S`. -/
lemma asum_ex (i j : ℕ) (α : ℕ → ℤ) (S : Finset ℕ) :
    asum (ex i j α) S
      = asum α S - (if i ∈ S then 1 else 0) + (if j ∈ S then 1 else 0) := by
  classical
  simp only [asum, ex, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' S i (fun _ => (1 : ℤ)), Finset.sum_ite_eq' S j (fun _ => (1 : ℤ))]

/-! ### Concavity of `r ↦ Λ_r`, and submodularity of `S ↦ Λ_{|S|}` -/

/-- A window of fixed width `k` slid to the right does not increase the sum of an
antitone function: `Λ_{n+k} - Λ_n ≤ Λ_{m+k} - Λ_m` for `m ≤ n`.  This is the concavity
of `r ↦ Λ_r` used in the proof of `prop:perm-mconvex`. -/
lemma psum_sub_le {f : ℕ → ℤ} (hf : Antitone f) {m n k : ℕ} (hmn : m ≤ n) :
    psum f (n + k) - psum f n ≤ psum f (m + k) - psum f m := by
  have e1 : psum f (n + k) = psum f n + ∑ c ∈ Finset.Ico n (n + k), f c :=
    psum_split f (Nat.le_add_right n k)
  have e2 : psum f (m + k) = psum f m + ∑ c ∈ Finset.Ico m (m + k), f c :=
    psum_split f (Nat.le_add_right m k)
  have e3 : ∑ c ∈ Finset.Ico n (n + k), f c = ∑ t ∈ Finset.range k, f (n + t) := by
    rw [Finset.sum_Ico_eq_sum_range]; simp
  have e4 : ∑ c ∈ Finset.Ico m (m + k), f c = ∑ t ∈ Finset.range k, f (m + t) := by
    rw [Finset.sum_Ico_eq_sum_range]; simp
  have e5 : ∑ t ∈ Finset.range k, f (n + t) ≤ ∑ t ∈ Finset.range k, f (m + t) :=
    Finset.sum_le_sum fun t _ => hf (by omega)
  linarith

/-- **`ρ(S) = Λ_{|S|}` is submodular** (first paragraph of the proof of
`prop:perm-mconvex`).  Derived from `λ̂` antitone; *not* postulated. -/
lemma rank_submodular {ℓ : ℕ} {lhat : ℕ → ℤ} (hl : IsPart ℓ lhat) (S T : Finset ℕ) :
    psum lhat (S ∪ T).card + psum lhat (S ∩ T).card
      ≤ psum lhat S.card + psum lhat T.card := by
  classical
  have hcard : (S ∪ T).card + (S ∩ T).card = S.card + T.card :=
    Finset.card_union_add_card_inter S T
  have h2 : (S ∩ T).card ≤ T.card := Finset.card_le_card Finset.inter_subset_right
  have h1 : (S ∩ T).card ≤ S.card := Finset.card_le_card Finset.inter_subset_left
  have hk : (S ∪ T).card = T.card + (S.card - (S ∩ T).card) := by omega
  have hq : S.card = (S ∩ T).card + (S.card - (S ∩ T).card) := by omega
  have key := psum_sub_le hl.1 (f := lhat) (m := (S ∩ T).card) (n := T.card)
    (k := S.card - (S ∩ T).card) h2
  rw [← hk, ← hq] at key
  linarith

/-- **Lemma `lem:tight`**: for `α ∈ J` the tight family
`F_α = {S : α(S) = ρ(S)}` is closed under union. -/
lemma tight_union {ℓ : ℕ} {lhat α : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) {S T : Finset ℕ}
    (hS : S ⊆ Finset.range ℓ) (hT : T ⊆ Finset.range ℓ)
    (htS : asum α S = psum lhat S.card) (htT : asum α T = psum lhat T.card) :
    asum α (S ∪ T) = psum lhat (S ∪ T).card := by
  classical
  have hsum : asum α (S ∪ T) + asum α (S ∩ T) = asum α S + asum α T :=
    Finset.sum_union_inter
  have hU : asum α (S ∪ T) ≤ psum lhat (S ∪ T).card :=
    hα.2.2.2 _ (Finset.mem_powerset.mpr (Finset.union_subset hS hT))
  have hI : asum α (S ∩ T) ≤ psum lhat (S ∩ T).card :=
    hα.2.2.2 _ (Finset.mem_powerset.mpr (Finset.inter_subset_left.trans hS))
  have hsub := rank_submodular hl S T
  linarith

/-! ### The single exchange step -/

/-- The displayed equivalence in the proof of `prop:perm-mconvex`, in its useful
direction: `α - eᵢ + e_j` leaves `J` **only** through a tight set containing `j` and
avoiding `i`.  So if no such tight set exists, the surgered vector is still in `J`. -/
lemma insupp_ex_of_no_tight {ℓ : ℕ} {lhat α : ℕ → ℤ} (hα : InSupp ℓ lhat α)
    {i j : ℕ} (hi : i < ℓ) (hj : j < ℓ) (hij : i ≠ j) (hpos : 1 ≤ α i)
    (hno : ∀ S ⊆ Finset.range ℓ, j ∈ S → i ∉ S → asum α S ≠ psum lhat S.card) :
    InSupp ℓ lhat (ex i j α) := by
  classical
  obtain ⟨hvan, hnn, hsize, hsub⟩ := hα
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    have h1 : c ≠ i := by omega
    have h2 : c ≠ j := by omega
    simp only [ex, if_neg h1, if_neg h2]
    simpa using hvan c hc
  · intro c
    have hc := hnn c
    simp only [ex]
    rcases eq_or_ne c i with rfl | h1
    · rw [if_pos rfl, if_neg hij]
      omega
    · rw [if_neg h1]
      split_ifs <;> omega
  · rw [psum_ex, if_pos hi, if_pos hj]
    omega
  · intro S hSmem
    have hS : S ⊆ Finset.range ℓ := Finset.mem_powerset.mp hSmem
    have hb := hsub S hSmem
    rw [asum_ex]
    by_cases hjS : j ∈ S
    · by_cases hiS : i ∈ S
      · rw [if_pos hiS, if_pos hjS]; omega
      · rw [if_neg hiS, if_pos hjS]
        have := hno S hS hjS hiS
        omega
    · rw [if_neg hjS]; split_ifs <;> omega

/-! ### The exchange axiom -/

/-- **Proposition `prop:perm-mconvex`** — the M-convex exchange axiom for
`J = {α ∈ ℕ^ℓ : α([ℓ]) = |λ̂|, α(S) ≤ Λ_{|S|} ∀ S ⊆ [ℓ]}`, in the form quoted in
§"The problem" of `2026-09-20-c1-cylindric-M-convexity.tex`:

> for all `α, β ∈ J` and every index `i` with `α_i > β_i` there is an index `j` with
> `α_j < β_j` and `α - eᵢ + e_j ∈ J`.

Murota's *symmetric* axiom additionally requires `β + eᵢ - e_j ∈ J` for the same `j`;
that is not proved here (see the module docstring). -/
theorem insupp_exchange {ℓ : ℕ} {lhat α β : ℕ → ℤ} (hl : IsPart ℓ lhat)
    (hα : InSupp ℓ lhat α) (hβ : InSupp ℓ lhat β) {i : ℕ} (hi : β i < α i) :
    ∃ j, α j < β j ∧ InSupp ℓ lhat (ex i j α) := by
  classical
  set D := (Finset.range ℓ).filter (fun c => α c < β c) with hD_def
  -- `i` is a live index, and `α i ≥ 1`.
  have hiℓ : i < ℓ := by
    by_contra h
    push_neg at h
    rw [hα.1 i h, hβ.1 i h] at hi
    omega
  have hpos : 1 ≤ α i := by have := hβ.2.1 i; omega
  -- `D ≠ ∅`, because `α` and `β` have the same total.
  have hDne : D.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hge : ∀ c ∈ Finset.range ℓ, β c ≤ α c := by
      intro c hc
      by_contra hlt
      push_neg at hlt
      have : c ∈ D := Finset.mem_filter.mpr ⟨hc, hlt⟩
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty c)
    have hstrict : psum β ℓ < psum α ℓ :=
      Finset.sum_lt_sum hge ⟨i, Finset.mem_range.mpr hiℓ, hi⟩
    have h1 := hα.2.2.1
    have h2 := hβ.2.2.1
    omega
  by_contra hcon
  push_neg at hcon
  -- For every `j ∈ D` the surgery fails, so a tight set `S_j ∋ j`, `i ∉ S_j` exists.
  have hchoice : ∀ j : ℕ, ∃ S : Finset ℕ, S ⊆ Finset.range ℓ ∧ i ∉ S ∧
      asum α S = psum lhat S.card ∧ (j ∈ D → j ∈ S) := by
    intro j
    by_cases hjD : j ∈ D
    · obtain ⟨hjr, hjlt⟩ := Finset.mem_filter.mp hjD
      have hij : i ≠ j := by intro h; rw [← h] at hjlt; omega
      by_contra hno
      push_neg at hno
      refine hcon j hjlt (insupp_ex_of_no_tight hα hiℓ (Finset.mem_range.mp hjr) hij hpos
        ?_)
      intro S hS hjS hiS htight
      exact (hno S hS hiS htight).2 hjS
    · exact ⟨∅, by simp, by simp, by simp [asum, psum], by simp [hjD]⟩
  choose S hS1 hS2 hS3 hS4 using hchoice
  -- `S* = ⋃_{j ∈ D} S_j` is tight, avoids `i`, and contains `D`.
  have hP : D.sup S ⊆ Finset.range ℓ ∧ i ∉ D.sup S ∧
      asum α (D.sup S) = psum lhat (D.sup S).card := by
    refine Finset.sup_induction
      (p := fun T => T ⊆ Finset.range ℓ ∧ i ∉ T ∧ asum α T = psum lhat T.card)
      ⟨by simp, by simp, by simp [asum, psum]⟩ ?_ ?_
    · rintro a ⟨ha1, ha2, ha3⟩ b ⟨hb1, hb2, hb3⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.sup_eq_union]; exact Finset.union_subset ha1 hb1
      · rw [Finset.sup_eq_union, Finset.mem_union]; tauto
      · rw [Finset.sup_eq_union]; exact tight_union hl hα ha1 hb1 ha3 hb3
    · intro j _
      exact ⟨hS1 j, hS2 j, hS3 j⟩
  have hDsub : D ⊆ D.sup S := fun j hj => Finset.le_sup (f := S) hj (hS4 j hj)
  -- `α(S*) < β(S*) ≤ ρ(S*) = α(S*)`.  **The contradiction is produced on the COMPLEMENT
  -- of `S*`**, where `α ≥ β` pointwise and `α i > β i`; the paper's displayed chain
  -- `β(S*) − α(S*) = ∑_{j ∈ S*} ≥ ∑_{j ∈ D} > 0` has its inequality the wrong way round
  -- (its own stated reason, "every term with `j ∈ S* ∖ D` is `≤ 0`", gives `≤`, not `≥`).
  -- See the module docstring.
  have hCompsplit : ∀ f : ℕ → ℤ,
      ∑ c ∈ Finset.range ℓ \ D.sup S, f c + ∑ c ∈ D.sup S, f c = psum f ℓ :=
    fun f => Finset.sum_sdiff hP.1
  have hlt : ∑ c ∈ Finset.range ℓ \ D.sup S, β c
      < ∑ c ∈ Finset.range ℓ \ D.sup S, α c := by
    refine Finset.sum_lt_sum (fun c hc => ?_)
      ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hiℓ, hP.2.1⟩, hi⟩
    obtain ⟨hcr, hcS⟩ := Finset.mem_sdiff.mp hc
    have hcD : c ∉ D := fun h => hcS (hDsub h)
    have : ¬ α c < β c := fun h => hcD (Finset.mem_filter.mpr ⟨hcr, h⟩)
    omega
  have hβS := hCompsplit β
  have hαS := hCompsplit α
  have hbb : asum β (D.sup S) ≤ psum lhat (D.sup S).card :=
    hβ.2.2.2 _ (Finset.mem_powerset.mpr hP.1)
  have h1 := hα.2.2.1
  have h2 := hβ.2.2.1
  have h3 := hP.2.2
  simp only [asum] at hbb h3
  omega

/-! ### Non-vacuity, and the negative control

`memory: a theorem whose hypotheses are never satisfiable type-checks perfectly.`  Two
guards, both on `ℓ = 2`, `λ̂ = (2,1)`, where `J = {(2,1), (1,2)}`:

* `insupp_exchange_witness` — the hypotheses *are* satisfiable, and the conclusion is a
  genuine surgery (`(2,1) ↦ (1,2)`), not a no-op.
* `insupp_exchange_hyp_load_bearing` — with `α = β` the hypothesis `β i < α i` fails for
  every `i`, and the conclusion is **false** (there is no `j` with `α j < β j` at all).
  So the hypothesis is doing work; the theorem is not a disguised tautology.
-/
section Witness

def lhat21 : ℕ → ℤ := fun c => if c = 0 then 2 else if c = 1 then 1 else 0
def al21 : ℕ → ℤ := fun c => if c = 0 then 2 else if c = 1 then 1 else 0
def be12 : ℕ → ℤ := fun c => if c = 0 then 1 else if c = 1 then 2 else 0

lemma lhat21_isPart : IsPart 2 lhat21 := by
  constructor
  · apply antitone_nat_of_succ_le
    intro c
    simp only [lhat21]
    split_ifs <;> first | (exfalso; assumption) | omega
  · intro c hc; simp only [lhat21]; split_ifs <;> omega

lemma al21_mem : InSupp 2 lhat21 al21 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [al21]; split_ifs <;> omega
  · intro c; simp only [al21]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, al21, lhat21]
  · decide

lemma be12_mem : InSupp 2 lhat21 be12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [be12]; split_ifs <;> omega
  · intro c; simp only [be12]; split_ifs <;> omega
  · simp [psum, Finset.sum_range_succ, be12, lhat21]
  · decide

/-- The hypotheses of `insupp_exchange` are satisfiable: `λ̂ = (2,1)`, `α = (2,1)`,
`β = (1,2)`, `i = 0`.  The exchange it produces is the genuine move `(2,1) ↦ (1,2)`. -/
theorem insupp_exchange_witness :
    ∃ j, al21 j < be12 j ∧ InSupp 2 lhat21 (ex 0 j al21) :=
  insupp_exchange lhat21_isPart al21_mem be12_mem
    (i := 0) (by norm_num [al21, be12])

private lemma witness_move : ex 0 1 al21 = be12 := by
  funext c
  simp only [ex, al21, be12]
  split_ifs <;> omega

private lemma witness_j_unique {j : ℕ} (h : al21 j < be12 j) : j = 1 := by
  by_contra hj
  simp only [al21, be12] at h
  split_ifs at h <;> omega

/-- The move `insupp_exchange` produces on the witness is **forced and genuine**: the
only admissible `j` is `1`, and `α - e₀ + e₁ = (1,2) = β`.  So the existential in
`insupp_exchange` is not being discharged by a no-op. -/
theorem insupp_exchange_witness_is_genuine :
    ∃ j, al21 j < be12 j ∧ InSupp 2 lhat21 (ex 0 j al21) ∧ j = 1 ∧ ex 0 j al21 = be12 := by
  obtain ⟨j, hj, hmem⟩ := insupp_exchange_witness
  exact ⟨j, hj, hmem, witness_j_unique hj, by rw [witness_j_unique hj]; exact witness_move⟩

/-- **Negative control.**  With `α = β = (2,1)` the hypothesis `β i < α i` fails for
every `i`, and the conclusion of `insupp_exchange` is false: no `j` has `α j < β j`.
Hence the hypothesis is load-bearing and the theorem is not vacuously true. -/
theorem insupp_exchange_hyp_load_bearing :
    (∀ i : ℕ, ¬ al21 i < al21 i) ∧ ¬ ∃ j, al21 j < al21 j ∧ InSupp 2 lhat21 (ex 0 j al21) := by
  refine ⟨fun i => lt_irrefl _, ?_⟩
  rintro ⟨j, hj, -⟩
  exact lt_irrefl _ hj

end Witness

end MConvexExchange
