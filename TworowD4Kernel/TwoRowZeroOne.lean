/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Combinatorics.Young.SemistandardTableau
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-!
# Two-row, two-part semistandard tableaux: uniqueness

A semistandard Young tableau whose entries all lie in `{0, 1}` is determined by its shape and
by how many `1`s it carries. This is the "one tableau" half of

> **Lemma `lem:mono`** of `proofs/2026-10-07-two-part-green-polynomials.tex` (l.176):
> for `ν ⊢ n` and a composition `(a, b)` of `n` with `a ≥ b ≥ 0`,
> `K_{ν,(a,b)}(t) = t^{b - ν₂}` if `ℓ(ν) ≤ 2` and `ν₂ ≤ b ≤ ν₁`, and `0` otherwise —
> *"So the tableau `T` is unique when it exists."*

## Translation of conventions — read this before comparing with the paper

The paper writes tableaux with entries in `{1, 2}` and calls the shape `ν = (ν₁, ν₂)` and the
content `(a, b)`. Mathlib's `SemistandardYoungTableau` is `0`-indexed: `highestWeight_apply`
reads `highestWeight μ i j = if (i, j) ∈ μ then i else 0`, so row `0` carries `0`s. Hence here

* the **shape** is `μ`, with `μ.rowLen 0` and `μ.rowLen 1` playing the paper's `ν₁` and `ν₂`;
* **entries lie in `{0, 1}`**, not `{1, 2}`;
* the paper's content entry `b` — *the number of `2`s* — is here **the number of `1`s**, the
  cardinality `#{c ∈ μ.cells | T c.1 c.2 = 1}`.

So the paper's existence range `ν₂ ≤ b ≤ ν₁` reads `μ.rowLen 1 ≤ k ≤ μ.rowLen 0` here. That
range was checked by brute force over every shape with `μ.rowLen 0 ≤ 7` before this file was
written: the number of such tableaux is `1` exactly on the range and `0` off it, no exceptions.

`zeros'` forces `T i j = 0` off the diagram, which collides with `0` as a legitimate entry
value. Every count and every quantifier below is therefore **restricted to cells of `μ`**.

## Main results

* `eq_of_monotone_zero_one_of_card_eq` — a weakly increasing `{0,1}`-valued sequence on
  `[0, N)` is determined by its number of `1`s. The engine.
* `SemistandardYoungTableau.rowLen_eq_zero_of_le_one` — entries in `{0,1}` *force* the shape to
  have at most two rows. This is the paper's *"a third row would need an entry ≥ 3"*, and it is
  why no two-row hypothesis appears in the main theorem.
* `SemistandardYoungTableau.eq_of_le_one_of_card_ones_eq` — **the target**: two tableaux of the
  same shape, entries in `{0,1}`, same number of `1`s, are equal.
* `SemistandardYoungTableau.twoRowZeroOneTableau` — the tableau itself: row `1` all `1`s, row
  `0` a block of `0`s then `k - rowLen 1` ones.
* `SemistandardYoungTableau.existsUnique_le_one_card_ones_eq` — the two halves combined into
  `∃!`, on the paper's range `rowLen 1 ≤ k ≤ rowLen 0`.

## Scope — what this file does NOT contain

No Kostka–Foulkes polynomial, no charge statistic, no Hall–Littlewood `P_λ`, and no Green
polynomial. `lem:mono` asserts `K_{ν,(a,b)}(t) = t^{b - ν₂}`; what is proved here is only the
*combinatorial* content behind it — that the tableau set is a singleton on the stated range and
empty off it. **The exponent `b - ν₂` is the charge of that tableau, and charge is not
formalised at all**, so the monomial identity itself is out of scope.

Uniqueness is stated as *"any two are equal"* rather than `Fintype.card … = 1` because Mathlib
has no `Fintype` instance and no cardinality API for `SemistandardYoungTableau` (the whole of
`Mathlib/Combinatorics/Young/SemistandardTableau.lean` is 146 lines and contains no `Fintype`,
`card`, `content` or `weight`), so that form cannot even be *stated* without building
finiteness from scratch. `∃!` needs only the API that exists.
-/

open Finset

namespace TworowD4Kernel.TwoRowZeroOne


private theorem card_lt_card_of_witness {N j : ℕ} {f g : ℕ → ℕ} (hjN : j < N)
    (hfj : f j = 0) (hgj : g j = 1)
    (hg1 : ∀ i, i < N → g i ≤ 1)
    (hfm : ∀ i₁ i₂, i₁ < i₂ → i₂ < N → f i₁ ≤ f i₂)
    (hgm : ∀ i₁ i₂, i₁ < i₂ → i₂ < N → g i₁ ≤ g i₂) :
    #{i ∈ range N | f i = 1} < #{i ∈ range N | g i = 1} := by
  have hsub : {i ∈ range N | f i = 1} ⊆ Ico (j + 1) N := by
    intro i hi
    simp only [mem_filter, mem_range] at hi
    obtain ⟨hiN, hfi⟩ := hi
    refine mem_Ico.2 ⟨?_, hiN⟩
    by_contra h
    have hij : i ≤ j := by omega
    have : f i ≤ f j := by
      rcases eq_or_lt_of_le hij with h' | h'
      · rw [h']
      · exact hfm i j h' hjN
    omega
  have hsup : Ico j N ⊆ {i ∈ range N | g i = 1} := by
    intro i hi
    obtain ⟨hji, hiN⟩ := mem_Ico.1 hi
    have : g j ≤ g i := by
      rcases eq_or_lt_of_le hji with h' | h'
      · rw [h']
      · exact hgm j i h' hiN
    have := hg1 i hiN
    simp only [mem_filter, mem_range]
    omega
  have h1 := card_le_card hsub
  have h2 := card_le_card hsup
  rw [Nat.card_Ico] at h1 h2
  omega

theorem eq_of_monotone_zero_one_of_card_eq {N : ℕ} {f g : ℕ → ℕ}
    (hf1 : ∀ i, i < N → f i ≤ 1) (hg1 : ∀ i, i < N → g i ≤ 1)
    (hfm : ∀ i₁ i₂, i₁ < i₂ → i₂ < N → f i₁ ≤ f i₂)
    (hgm : ∀ i₁ i₂, i₁ < i₂ → i₂ < N → g i₁ ≤ g i₂)
    (hcard : #{i ∈ range N | f i = 1} = #{i ∈ range N | g i = 1}) :
    ∀ i, i < N → f i = g i := by
  intro j hjN
  have hfj := hf1 j hjN
  have hgj := hg1 j hjN
  have hf0 : f j = 0 ∨ f j = 1 := by omega
  have hg0 : g j = 0 ∨ g j = 1 := by omega
  rcases hf0 with hf | hf <;> rcases hg0 with hg | hg
  · rw [hf, hg]
  · exact absurd (card_lt_card_of_witness hjN hf hg hg1 hfm hgm) (by omega)
  · exact absurd (card_lt_card_of_witness hjN hg hf hf1 hgm hfm) (by omega)
  · rw [hf, hg]

end TworowD4Kernel.TwoRowZeroOne

namespace SemistandardYoungTableau

open YoungDiagram TworowD4Kernel.TwoRowZeroOne

variable {μ : YoungDiagram}

/-- **Entries in `{0,1}` force at most two rows.** A cell in row `i ≥ 2` would sit under the
strictly increasing column chain `T 0 j < T 1 j < T i j`, forcing `T i j ≥ 2`. -/
theorem rowLen_eq_zero_of_le_one (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j ≤ 1) {i : ℕ} (hi : 2 ≤ i) : μ.rowLen i = 0 := by
  by_contra h
  have hmem : (i, 0) ∈ μ := mem_iff_lt_rowLen.2 (by omega)
  have h1 : (1, 0) ∈ μ := μ.up_left_mem (by omega) (le_refl 0) hmem
  have c01 : T 0 0 < T 1 0 := T.col_strict (by omega) h1
  have c1i : T 1 0 < T i 0 := T.col_strict (by omega) hmem
  have := hT i 0 hmem
  omega

/-- **The height-2 columns are pinned.** For `j < rowLen 1` the column `j` has two cells, so
`col_strict` plus entries in `{0,1}` forces `T 0 j = 0` and `T 1 j = 1`. -/
theorem entry_of_lt_rowLen_one (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j ≤ 1) {j : ℕ} (hj : j < μ.rowLen 1) :
    T 0 j = 0 ∧ T 1 j = 1 := by
  have h1 : (1, j) ∈ μ := mem_iff_lt_rowLen.2 hj
  have hcs := T.col_strict (show (0 : ℕ) < 1 by omega) h1
  have := hT 1 j h1
  omega

/-- **The content splits as `(row 0 tail) + rowLen 1`.** Every cell of row `1` carries a `1`,
so the total number of `1`s is the number of `1`s in row `0` plus the length of row `1`. -/
theorem card_ones_eq (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j ≤ 1) :
    #{c ∈ μ.cells | T c.1 c.2 = 1}
      = #{j ∈ range (μ.rowLen 0) | T 0 j = 1} + μ.rowLen 1 := by
  have hba : μ.rowLen 1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 1 (by omega)
  have hcells : μ.cells
      = {c ∈ (range 2) ×ˢ (range (μ.rowLen 0)) | c.2 < μ.rowLen c.1} := by
    ext ⟨i, j⟩
    simp only [mem_filter, mem_product, mem_range, mem_cells]
    constructor
    · intro h
      have hj : j < μ.rowLen i := mem_iff_lt_rowLen.1 h
      have hi : i < 2 := by
        by_contra hc
        have := T.rowLen_eq_zero_of_le_one hT (show 2 ≤ i by omega)
        omega
      exact ⟨⟨hi, lt_of_lt_of_le hj (μ.rowLen_anti 0 i (by omega))⟩, hj⟩
    · intro h
      exact mem_iff_lt_rowLen.2 h.2
  rw [hcells, filter_filter, card_filter, sum_product, sum_range_succ, sum_range_succ,
    sum_range_zero, zero_add]
  congr 1
  · rw [card_filter]
    refine sum_congr rfl fun j hj => ?_
    simp only [mem_range] at hj
    simp [hj]
  · rw [show μ.rowLen 1 = #{j ∈ range (μ.rowLen 0) | j < μ.rowLen 1} by
      rw [show {j ∈ range (μ.rowLen 0) | j < μ.rowLen 1} = range (μ.rowLen 1) by
        ext j; simp only [mem_filter, mem_range]; omega, card_range], card_filter]
    refine sum_congr rfl fun j hj => ?_
    by_cases hj1 : j < μ.rowLen 1
    · simp [hj1, (T.entry_of_lt_rowLen_one hT hj1).2]
    · simp [hj1]

/-- **Two-row, two-part uniqueness.** Any two semistandard Young tableaux of the same shape
whose entries all lie in `{0,1}` and which carry the same number of `1`s are equal.

The shape is not hypothesised to have two rows: by `rowLen_eq_zero_of_le_one` the
`{0,1}` condition already forces it. Counts and quantifiers are restricted to cells of `μ`,
since `zeros'` makes `0` the value off the diagram as well as a legitimate content value. -/
theorem eq_of_le_one_of_card_ones_eq (T T' : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j ≤ 1) (hT' : ∀ i j, (i, j) ∈ μ → T' i j ≤ 1)
    (hcard : #{c ∈ μ.cells | T c.1 c.2 = 1} = #{c ∈ μ.cells | T' c.1 c.2 = 1}) :
    T = T' := by
  have hc : #{j ∈ range (μ.rowLen 0) | T 0 j = 1}
      = #{j ∈ range (μ.rowLen 0) | T' 0 j = 1} := by
    have h := (T.card_ones_eq hT).symm.trans (hcard.trans (T'.card_ones_eq hT'))
    omega
  have hrow0 : ∀ j, j < μ.rowLen 0 → T 0 j = T' 0 j := by
    refine eq_of_monotone_zero_one_of_card_eq
      (fun j hj => hT 0 j (mem_iff_lt_rowLen.2 hj))
      (fun j hj => hT' 0 j (mem_iff_lt_rowLen.2 hj))
      (fun j₁ j₂ h h2 => T.row_weak h (mem_iff_lt_rowLen.2 h2))
      (fun j₁ j₂ h h2 => T'.row_weak h (mem_iff_lt_rowLen.2 h2)) hc
  ext i j
  by_cases hij : (i, j) ∈ μ
  · have hj : j < μ.rowLen i := mem_iff_lt_rowLen.1 hij
    have hi : i < 2 := by
      by_contra hc'
      have := T.rowLen_eq_zero_of_le_one hT (show 2 ≤ i by omega)
      omega
    interval_cases i
    · exact hrow0 j hj
    · rw [(T.entry_of_lt_rowLen_one hT hj).2, (T'.entry_of_lt_rowLen_one hT' hj).2]
  · simp [T.zeros hij, T'.zeros hij]

/-- The `{0,1}`-tableau of shape `μ` carrying `k` ones: row `1` is all `1`s, row `0` is
`0`s followed by `k - rowLen 1` ones. Needs `μ` to have at most two rows (`h2`) and
`rowLen 1 ≤ k ≤ rowLen 0`. -/
def twoRowZeroOneTableau (μ : YoungDiagram) (k : ℕ) (h2 : μ.rowLen 2 = 0)
    (hk1 : μ.rowLen 1 ≤ k) (hk2 : k ≤ μ.rowLen 0) : SemistandardYoungTableau μ where
  entry i j := if (i, j) ∈ μ then
      (if i = 0 then (if μ.rowLen 0 - (k - μ.rowLen 1) ≤ j then 1 else 0) else 1) else 0
  row_weak' {i j1 j2} hj hcell := by
    have hc1 : (i, j1) ∈ μ := μ.up_left_mem (le_refl i) (le_of_lt hj) hcell
    rw [if_pos hc1, if_pos hcell]
    by_cases hi : i = 0
    · simp only [if_pos hi]
      split_ifs <;> omega
    · simp only [if_neg hi, le_refl]
  col_strict' {i1 i2 j} hi hcell := by
    have hc1 : (i1, j) ∈ μ := μ.up_left_mem (le_of_lt hi) (le_refl j) hcell
    have hj2 : j < μ.rowLen i2 := mem_iff_lt_rowLen.1 hcell
    have hi2 : i2 = 1 := by
      by_contra hne
      have : μ.rowLen i2 ≤ μ.rowLen 2 := μ.rowLen_anti 2 i2 (by omega)
      omega
    have hi1 : i1 = 0 := by omega
    subst hi1; subst hi2
    have hjb : j < μ.rowLen 1 := hj2
    rw [if_pos hc1, if_pos hcell, if_pos rfl, if_neg (by omega), if_neg (by omega)]
    omega
  zeros' h := if_neg h

@[simp] theorem twoRowZeroOneTableau_apply {μ : YoungDiagram} {k : ℕ} {h2 hk1 hk2} {i j : ℕ} :
    twoRowZeroOneTableau μ k h2 hk1 hk2 i j = if (i, j) ∈ μ then
      (if i = 0 then (if μ.rowLen 0 - (k - μ.rowLen 1) ≤ j then 1 else 0) else 1) else 0 := rfl

theorem twoRowZeroOneTableau_le_one {μ : YoungDiagram} {k : ℕ} {h2 hk1 hk2} (i j : ℕ) :
    twoRowZeroOneTableau μ k h2 hk1 hk2 i j ≤ 1 := by
  rw [twoRowZeroOneTableau_apply]; split_ifs <;> omega

theorem twoRowZeroOneTableau_card_ones {μ : YoungDiagram} {k : ℕ} {h2 hk1 hk2} :
    #{c ∈ μ.cells | twoRowZeroOneTableau μ k h2 hk1 hk2 c.1 c.2 = 1} = k := by
  set T := twoRowZeroOneTableau μ k h2 hk1 hk2 with hTdef
  rw [T.card_ones_eq (fun i j _ => twoRowZeroOneTableau_le_one i j)]
  have hrow : {j ∈ range (μ.rowLen 0) | T 0 j = 1}
      = Ico (μ.rowLen 0 - (k - μ.rowLen 1)) (μ.rowLen 0) := by
    ext j
    simp only [mem_filter, mem_range, mem_Ico, hTdef, twoRowZeroOneTableau_apply,
      mem_iff_lt_rowLen, if_true]
    constructor
    · rintro ⟨hj, h⟩
      refine ⟨?_, hj⟩
      split_ifs at h
      omega
    · rintro ⟨h1, h2'⟩
      refine ⟨h2', ?_⟩
      split_ifs <;> omega
  rw [hrow, Nat.card_Ico]
  omega

/-- **Existence and uniqueness.** For a shape with at most two rows and
`rowLen 1 ≤ k ≤ rowLen 0`, there is exactly one semistandard Young tableau of that shape with
entries in `{0,1}` carrying `k` ones. -/
theorem existsUnique_le_one_card_ones_eq (μ : YoungDiagram) (k : ℕ) (h2 : μ.rowLen 2 = 0)
    (hk1 : μ.rowLen 1 ≤ k) (hk2 : k ≤ μ.rowLen 0) :
    ∃! T : SemistandardYoungTableau μ,
      (∀ i j, (i, j) ∈ μ → T i j ≤ 1) ∧ #{c ∈ μ.cells | T c.1 c.2 = 1} = k := by
  refine ⟨twoRowZeroOneTableau μ k h2 hk1 hk2,
    ⟨fun i j _ => twoRowZeroOneTableau_le_one i j, twoRowZeroOneTableau_card_ones⟩, ?_⟩
  rintro T ⟨hT, hTk⟩
  exact eq_of_le_one_of_card_ones_eq T _ hT
    (fun i j _ => twoRowZeroOneTableau_le_one i j)
    (by rw [hTk, twoRowZeroOneTableau_card_ones])


/-! ### Necessity of the hypotheses

Each block below establishes a fact about the **statement**, not about my proof: deleting a
hypothesis and watching `lake build` fail would only show that *this route* needs it. -/

/-- **`h2` is necessary for existence.** If the shape has a third row there is no `{0,1}`
tableau at all — the contrapositive of `rowLen_eq_zero_of_le_one`. -/
theorem not_le_one_of_rowLen_two_ne_zero {μ : YoungDiagram} (h : μ.rowLen 2 ≠ 0)
    (T : SemistandardYoungTableau μ) : ¬ (∀ i j, (i, j) ∈ μ → T i j ≤ 1) :=
  fun hT => h (T.rowLen_eq_zero_of_le_one hT (le_refl 2))

/-- **The range `rowLen 1 ≤ k ≤ rowLen 0` is necessary for existence.** Row `1` contributes
`rowLen 1` ones, and the ones of row `0` are confined to its last `rowLen 0 - rowLen 1` cells.
This is the *"`0` otherwise"* clause of `lem:mono`. -/
theorem card_ones_mem_range {μ : YoungDiagram} (T : SemistandardYoungTableau μ)
    (hT : ∀ i j, (i, j) ∈ μ → T i j ≤ 1) :
    μ.rowLen 1 ≤ #{c ∈ μ.cells | T c.1 c.2 = 1} ∧
      #{c ∈ μ.cells | T c.1 c.2 = 1} ≤ μ.rowLen 0 := by
  have hba : μ.rowLen 1 ≤ μ.rowLen 0 := μ.rowLen_anti 0 1 (by omega)
  rw [T.card_ones_eq hT]
  refine ⟨by omega, ?_⟩
  have hsub : {j ∈ range (μ.rowLen 0) | T 0 j = 1} ⊆ Ico (μ.rowLen 1) (μ.rowLen 0) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj
    refine mem_Ico.2 ⟨?_, hj.1⟩
    by_contra hc
    have := (T.entry_of_lt_rowLen_one hT (show j < μ.rowLen 1 by omega)).1
    omega
  have hle := card_le_card hsub
  rw [Nat.card_Ico] at hle
  omega

/-- **The content hypothesis is necessary for uniqueness.** Whenever two distinct admissible
counts exist, so do two distinct `{0,1}` tableaux of the same shape. So
`eq_of_le_one_of_card_ones_eq` genuinely needs `hcard`: this is a counterexample to the
statement with `hcard` deleted, not merely a failing build. -/
theorem exists_ne_of_lt {μ : YoungDiagram} (h2 : μ.rowLen 2 = 0) {k₁ k₂ : ℕ}
    (hk1 : μ.rowLen 1 ≤ k₁) (hlt : k₁ < k₂) (hk2 : k₂ ≤ μ.rowLen 0) :
    ∃ T T' : SemistandardYoungTableau μ, (∀ i j, (i, j) ∈ μ → T i j ≤ 1) ∧
      (∀ i j, (i, j) ∈ μ → T' i j ≤ 1) ∧ T ≠ T' := by
  refine ⟨twoRowZeroOneTableau μ k₁ h2 hk1 (by omega),
    twoRowZeroOneTableau μ k₂ h2 (by omega) hk2,
    fun i j _ => twoRowZeroOneTableau_le_one i j,
    fun i j _ => twoRowZeroOneTableau_le_one i j, fun hEq => ?_⟩
  have h := twoRowZeroOneTableau_card_ones (μ := μ) (k := k₁) (h2 := h2) (hk1 := hk1)
    (hk2 := by omega)
  rw [hEq, twoRowZeroOneTableau_card_ones] at h
  omega

/-- **Non-vacuity.** The hypotheses of `exists_ne_of_lt` are satisfiable: the single-row shape
`(2)` admits both `k₁ = 0` and `k₂ = 1`. Without this the ablation above would be a theorem
about an empty range, which is no ablation at all. -/
theorem exists_ne_of_lt_nonvacuous :
    ∃ (μ : YoungDiagram) (k₁ k₂ : ℕ), μ.rowLen 2 = 0 ∧ μ.rowLen 1 ≤ k₁ ∧ k₁ < k₂ ∧
      k₂ ≤ μ.rowLen 0 := by
  have hw : ([2] : List ℕ).SortedGE := by decide
  refine ⟨YoungDiagram.ofRowLens [2] hw, 0, 1, ?_, ?_, by omega, ?_⟩
  · have h : ((2 : ℕ), (0 : ℕ)) ∉ YoungDiagram.ofRowLens [2] hw := by
      simp [YoungDiagram.mem_ofRowLens]
    by_contra hc
    exact h (mem_iff_lt_rowLen.2 (by omega))
  · have h : ((1 : ℕ), (0 : ℕ)) ∉ YoungDiagram.ofRowLens [2] hw := by
      simp [YoungDiagram.mem_ofRowLens]
    rw [Nat.le_zero]
    by_contra hc
    exact h (mem_iff_lt_rowLen.2 (by omega))
  · have h : ((0 : ℕ), (0 : ℕ)) ∈ YoungDiagram.ofRowLens [2] hw := by
      simp [YoungDiagram.mem_ofRowLens]
    exact mem_iff_lt_rowLen.1 h

end SemistandardYoungTableau
