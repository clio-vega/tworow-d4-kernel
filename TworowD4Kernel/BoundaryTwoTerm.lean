/-
Copyright (c) 2026 Clio. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Tactic.Ring

/-!
# The boundary two-term law, and the colength that cannot see which summand fired

Formalisation of the **arithmetic layer** of `thm:main` and `cor:inv` from
`proofs/2026-10-22-boundary-valuation-two-term.tex` (PROVE 2026-10-22 c1).

## What is and is not formalised

The paper's object is the boundary order of a diagonal weight,
`ord_{S^ε_m} Ã^X_{I,I}`, computed from `eq:inv`–`eq:diag`.  For `X ∈ {B, C}` those
three displays are **Motegi's theorem**, read first-hand at L1305–1335 (type `B`) and
L998–1046 (type `C`) of `arXiv:2610.15344`; for `X = BC` the display `eq:diag` with
`M = {1,2}` is the paper's own *definition*, with no weight function in the literature.

**None of that root-system apparatus is formalised here.**  What is formalised is the
arithmetic statement the valuation computation reduces to — a claim about `Finset ℕ`:

* the count of boundary factors at index `m` is a **two-term** function of `[m ∈ I]`
  (`boundary_count_two_term`), with **no hypothesis on `q`**;
* the two summand functions are **complementary** (`indicator_add_compl`);
* both have the **same total** over all `I ⊆ range N` (`colength_mem`, `colength_nmem`,
  both `2 ^ (N - 1)`), while being distinct functions (`total_cannot_witness`).

So the Lean content is exactly: *a total cannot witness a claim about which of its
summands contributed.*  The identification of `ord_{S^ε_m} Ã^X_{I,I}` with
`boundary_count` is **not** Lean-verified and must not be inferred from these names.

## The S4 discharge (what makes the hypothesis-removal meaningful)

`boundary_count_two_term` has no binder on `q`.  A *missing* binder and a *removable*
binder give the same green build, so the clean compile alone shows nothing.  The
section `ThmBD` therefore states the 10-21 hypothesis `q ≠ ε⁻ʰ` explicitly
(`ne_inv_pow_iff`, `gM_singleton_eq_zero_iff`) and derives the old one-term law from
the two-term law (`thmBD_of_two_term`).  That direction — new ⟹ old-with-binder — is
what makes "the hypothesis was removed" a type-checked claim rather than an absence.
-/

namespace TworowD4Kernel.BoundaryTwoTerm

open Finset

/-! ## The two multiplicity counts -/

section Counts

variable {K : Type*} [Monoid K] [DecidableEq K]

/-- `f_M(ε) = #{a ∈ M : ε ^ a = 1}` — the `m ∈ I` term of `eq:main`.  Note it does not
mention `q`. -/
def fM (M : Finset ℕ) (ε : K) : ℕ := (M.filter (fun a => ε ^ a = 1)).card

/-- `g_M(q, ε) = #{a ∈ M : q · ε ^ a = 1}` — the `m ∉ I` term of `eq:main`.  This is the
term that is invisible while `q` is transcendental. -/
def gM (M : Finset ℕ) (q ε : K) : ℕ := (M.filter (fun a => q * ε ^ a = 1)).card

/-- The number of boundary factors at index `m` that vanish at `S^ε_m`: the paper's
`#{a ∈ M : q ^ [m ∉ I] · ε ^ a = 1}`.  The indicator in the exponent is the whole
mechanism — `m ∈ I` puts the root `a·t_m` in `Inv(λ)` (no `q`), `m ∉ I` puts it in
`T(λ)` (with `q`). -/
def boundaryCount (M I : Finset ℕ) (m : ℕ) (q ε : K) : ℕ :=
  (M.filter (fun a => q ^ (if m ∈ I then 0 else 1) * ε ^ a = 1)).card

/-- **L1 — the two-term law** (`thm:main`, arithmetic half, `eq:main`).

`#{a ∈ M : q^[m∉I] ε^a = 1} = [m ∈ I] f_M(ε) + [m ∉ I] g_M(q,ε)`, in `if`-form.

**There is no hypothesis on `q`.**  The 10-21 binder `q ≠ ε^{-h}` was not protecting
against a degeneration; it named the locus `g_M = 0` (see `gM_singleton_eq_zero_iff`). -/
theorem boundary_count_two_term (M I : Finset ℕ) (m : ℕ) (q ε : K) :
    boundaryCount M I m q ε = if m ∈ I then fM M ε else gM M q ε := by
  unfold boundaryCount fM gM
  split_ifs with h <;> simp

/-- **L2 — indicator form.**  The shape the paper displays and the shape the colength
sums: `[m ∈ I] · f_M(ε) + [m ∉ I] · g_M(q, ε)`. -/
theorem boundary_count_indicator (M I : Finset ℕ) (m : ℕ) (q ε : K) :
    boundaryCount M I m q ε
      = (if m ∈ I then 1 else 0) * fM M ε + (if m ∈ I then 0 else 1) * gM M q ε := by
  rw [boundary_count_two_term]
  split_ifs <;> simp

/-- At `q = 1` the two terms coincide, for every `ε`: `g_M(1, ε) = f_M(ε)`.  This is the
10-21 lesion "`q := 1` leaves the `m ∈ I` half inert and breaks the `m ∉ I` half", read
off `eq:main` rather than measured. -/
theorem gM_one (M : Finset ℕ) (ε : K) : gM M 1 ε = fM M ε := by
  unfold gM fM; simp

end Counts

/-! ## The S4 discharge: the 10-21 hypothesis is the locus `g_M = 0` -/

section ThmBD

variable {K : Type*} [GroupWithZero K] [DecidableEq K]

/-- The paper writes the 10-21 binder as `q ≠ ε^{-h}`; `gM` is phrased multiplicatively.
The two agree whenever `ε ≠ 0`. -/
theorem ne_inv_pow_iff {K : Type*} [GroupWithZero K] {h : ℕ} {q ε : K} (hε : ε ≠ 0) :
    q ≠ (ε⁻¹) ^ h ↔ q * ε ^ h ≠ 1 := by
  rw [not_iff_not, inv_pow, mul_eq_one_iff_eq_inv₀ (pow_ne_zero h hε)]

/-- **`thm:BD`'s hypothesis is exactly the vanishing of the second term.**  For a
singleton multiplicity set `M = {h}` — which is the `X ∈ {B, C}` case, where `M = M_m(X)`
is a singleton — the 10-21 binder `q ≠ ε^{-h}` holds iff `g_M(q, ε) = 0`. -/
theorem gM_singleton_eq_zero_iff (h : ℕ) (q ε : K) :
    gM ({h} : Finset ℕ) q ε = 0 ↔ q * ε ^ h ≠ 1 := by
  unfold gM
  rw [Finset.card_eq_zero, Finset.filter_singleton]
  split_ifs with hq <;> simp [hq]

/-- **The 10-21 one-term law, derived from the two-term law.**  Under the old binder
`q ≠ ε^{-h}` (equivalently `q · ε^h ≠ 1`), the boundary count collapses to the single
term `[m ∈ I] · f_M(ε)` — i.e. `(BD)`: the order sees `I` only through `[m ∈ I]`.

This is the direction that makes the removal meaningful: `boundary_count_two_term`
carries no binder on `q` and **implies** the statement that does. -/
theorem thmBD_of_two_term (h m : ℕ) (I : Finset ℕ) (q ε : K) (hq : q * ε ^ h ≠ 1) :
    boundaryCount ({h} : Finset ℕ) I m q ε
      = (if m ∈ I then 1 else 0) * fM ({h} : Finset ℕ) ε := by
  rw [boundary_count_indicator, (gM_singleton_eq_zero_iff h q ε).2 hq]
  simp

end ThmBD


/-! ## The colength: the two summand functions have the same total -/

section Colength

/-- **L5 — complementarity.**  The two summand functions of `eq:main` do not merely
differ, they *partition*: `[m ∈ I] + [m ∉ I] = 1` pointwise.  This is why the coincidence
of the totals below is forced rather than accidental. -/
theorem indicator_add_compl (m : ℕ) (I : Finset ℕ) :
    (if m ∈ I then 1 else 0) + (if m ∈ I then 0 else 1) = 1 := by
  split_ifs <;> simp

/-- The subsets of `s` *avoiding* `m` are exactly the subsets of `s.erase m`. -/
theorem filter_nmem_powerset (s : Finset ℕ) (m : ℕ) :
    s.powerset.filter (fun I => m ∉ I) = (s.erase m).powerset := by
  ext I
  simp [Finset.mem_filter, Finset.mem_powerset, Finset.subset_erase]

/-- **L3, `m ∉ I` half**, for a general ambient `s`: `Σ_{I ⊆ s} [m ∉ I] = 2 ^ (#s - 1)`. -/
theorem colength_nmem_card (s : Finset ℕ) (m : ℕ) (hm : m ∈ s) :
    ∑ I ∈ s.powerset, (if m ∈ I then 0 else 1) = 2 ^ (s.card - 1) := by
  have hcongr : ∀ I ∈ s.powerset,
      (if m ∈ I then 0 else 1) = (if m ∉ I then 1 else 0) := by
    intro I _; split_ifs with h <;> simp_all
  rw [Finset.sum_congr rfl hcongr, ← Finset.card_filter, filter_nmem_powerset,
    Finset.card_powerset, Finset.card_erase_of_mem hm]

/-- **L3, `m ∈ I` half**, for a general ambient `s`: `Σ_{I ⊆ s} [m ∈ I] = 2 ^ (#s - 1)`.

Proved from the `m ∉ I` half *through complementarity* (`indicator_add_compl`), which is
the paper's own reason the two totals agree: the pointwise sum is the constant `1`, so the
two totals add to `#(powerset s) = 2 ^ #s`, and one of them is `2 ^ (#s - 1)`. -/
theorem colength_mem_card (s : Finset ℕ) (m : ℕ) (hm : m ∈ s) :
    ∑ I ∈ s.powerset, (if m ∈ I then 1 else 0) = 2 ^ (s.card - 1) := by
  have hsum : (∑ I ∈ s.powerset, (if m ∈ I then 1 else 0))
      + ∑ I ∈ s.powerset, (if m ∈ I then 0 else 1) = 2 ^ s.card := by
    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl
      (fun I _ => indicator_add_compl m I)]
    simp [Finset.card_powerset]
  have hn := colength_nmem_card s m hm
  have hc : 1 ≤ s.card := Finset.card_pos.2 ⟨m, hm⟩
  have h2 : (2 : ℕ) ^ s.card = 2 ^ (s.card - 1) * 2 := by
    conv_lhs => rw [show s.card = (s.card - 1) + 1 by omega]
    rw [pow_succ]
  omega

/-- **L3 — the `m ∈ I` colength** (`cor:colength`, specialised to `s = range N`). -/
theorem colength_mem (N m : ℕ) (hm : m ∈ Finset.range N) :
    ∑ I ∈ (Finset.range N).powerset, (if m ∈ I then 1 else 0) = 2 ^ (N - 1) := by
  simpa [Finset.card_range] using colength_mem_card (Finset.range N) m hm

/-- **L3 — the `m ∉ I` colength.**  The *same integer* `2 ^ (N - 1)`.  This is the
arithmetic of `cor:inv`: the `(B_N, ε = -1, q₀ = -1)` order is `[m ∉ I]`, the exact
complement of `(BD)`, and its colength is the same number. -/
theorem colength_nmem (N m : ℕ) (hm : m ∈ Finset.range N) :
    ∑ I ∈ (Finset.range N).powerset, (if m ∈ I then 0 else 1) = 2 ^ (N - 1) := by
  simpa [Finset.card_range] using colength_nmem_card (Finset.range N) m hm

-- The pre-registered statement below is kept verbatim, `hN` and all.  Lean's
-- `unusedVariables` linter fires on `hN`, and **that warning is the lesion verdict**:
-- S2 was predicted IRREMOVABLE and is REMOVABLE.  It is silenced only so the module
-- builds clean; `summands_differ` is the hypothesis-free form the linter is reporting.
set_option linter.unusedVariables false in
/-- **L4 — ★ the total is blind, and the summands are not.**

Equal totals, provably distinct summand functions.  The second conjunct is what no census
of the total can ever see; `cor:inv` is the `(B_N, ε = -1, q₀ = -1)` instance of it.

`hN : 2 ≤ N` is **unused** — see the comment above this declaration. -/
theorem total_cannot_witness (N m : ℕ) (hm : m ∈ Finset.range N) (hN : 2 ≤ N) :
    (∑ I ∈ (Finset.range N).powerset, (if m ∈ I then 1 else 0)
        = ∑ I ∈ (Finset.range N).powerset, (if m ∈ I then 0 else 1))
      ∧ ∃ I ∈ (Finset.range N).powerset,
          (if m ∈ I then 1 else 0) ≠ (if m ∈ I then 0 else 1) := by
  refine ⟨by rw [colength_mem N m hm, colength_nmem N m hm], ∅, ?_, ?_⟩
  · exact Finset.empty_mem_powerset _
  · simp

/-! ### Grading the pre-registered lesion table

The three declarations below are the *measured* verdicts, not predictions.  They are
stated so that each lesion grade is itself type-checked rather than asserted. -/

/-- **S2 graded: `2 ≤ N` is REMOVABLE** (predicted IRREMOVABLE for conjunct 2).

The witness `I = ∅` needs no lower bound on `N` whatsoever, so conjunct 2 survives at
`N = 1` — and in fact at `N = 0`.  Moreover `hm` is *also* unused by conjunct 2: for any
`I`, exactly one of the two `if`s is `1`, so the two can never be equal.  Conjunct 2 is
therefore **hypothesis-free**, and all of L4's content sits in conjunct 1. -/
theorem summands_differ (N m : ℕ) :
    ∃ I ∈ (Finset.range N).powerset,
      (if m ∈ I then 1 else 0) ≠ (if m ∈ I then 0 else 1) :=
  ⟨∅, Finset.empty_mem_powerset _, by simp⟩

/-- **S1 graded: `m ∈ s` is IRREMOVABLE** — negative control.  Drop it and the `m ∈ I`
total is `0`, not `2 ^ (#s - 1)`. -/
theorem colength_mem_of_nmem (s : Finset ℕ) (m : ℕ) (hm : m ∉ s) :
    ∑ I ∈ s.powerset, (if m ∈ I then 1 else 0) = 0 := by
  refine Finset.sum_eq_zero fun I hI => ?_
  have : m ∉ I := fun h => hm (Finset.mem_powerset.1 hI h)
  simp [this]

/-- The S1 control, with a numeral witness: at `N = 3`, `m = 5 ∉ range 3`, the `m ∈ I`
total is `0 ≠ 4 = 2 ^ (3 - 1)`.  (A named theorem, not an `example`: an anonymous
`example` is invisible to an environment scan.) -/
theorem colength_mem_lesion_witness :
    ∑ I ∈ (Finset.range 3).powerset, (if 5 ∈ I then 1 else 0) ≠ 2 ^ (3 - 1) := by
  rw [colength_mem_of_nmem _ _ (by decide)]
  decide

/-- **The sharp statement L4 should have been.**  Not merely "the functions differ at some
point", but: the two summand functions have *disjoint, both-nonempty* supports, while
their totals agree.  This needs `hm` (for the `I = {m}` witness) but still not `2 ≤ N`. -/
theorem total_blind_supports_split (N m : ℕ) (hm : m ∈ Finset.range N) :
    (∑ I ∈ (Finset.range N).powerset, (if m ∈ I then 1 else 0)
        = ∑ I ∈ (Finset.range N).powerset, (if m ∈ I then 0 else 1))
      ∧ (∃ I ∈ (Finset.range N).powerset,
          (if m ∈ I then 1 else 0) = 1 ∧ (if m ∈ I then 0 else 1) = 0)
      ∧ (∃ I ∈ (Finset.range N).powerset,
          (if m ∈ I then 1 else 0) = 0 ∧ (if m ∈ I then 0 else 1) = 1) := by
  refine ⟨by rw [colength_mem N m hm, colength_nmem N m hm], ⟨{m}, ?_, ?_⟩, ∅, ?_, ?_⟩
  · simpa [Finset.mem_powerset] using hm
  · simp
  · exact Finset.empty_mem_powerset _
  · simp


/-- **S3 graded: the PAIR (S1, S2) is jointly irremovable — but only because S1 is.**

Drop both hypotheses and conjunct 1 is *false*: at `N = 3`, `m = 5 ∉ range 3`, the
`m ∈ I` total is `0` and the `m ∉ I` total is `2 ^ 3 = 8`.  So unlike this morning's
`(0 ∉ M, range)` pair — each marginal removable, the joint false — here the joint
verdict adds nothing to the marginal: S1 already carries the whole load, and S2 carries
none.  A register of marginals was *sufficient* in this cell. -/
theorem total_cannot_witness_joint_lesion :
    ¬ (∑ I ∈ (Finset.range 3).powerset, (if 5 ∈ I then 1 else 0)
        = ∑ I ∈ (Finset.range 3).powerset, (if 5 ∈ I then 0 else 1)) := by
  decide

end Colength

end TworowD4Kernel.BoundaryTwoTerm
