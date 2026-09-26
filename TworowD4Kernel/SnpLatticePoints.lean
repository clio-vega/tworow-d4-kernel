/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.SortedSubsetBridge
import Mathlib.Analysis.Convex.Hull

/-!
# Theorem 8.1 — the Newton polytope of the cylindric skew Schur polynomial is saturated

Formalisation of `thm:snp` of `projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex`:

> `conv(W_ℓ) ∩ ℤ^ℓ = W_ℓ`,  where  `W_ℓ = {α ∈ ℕ^ℓ : sort(α) ⊴ λ̂}`.

The paper proof is three lines.  `Q`, the set cut out by the linear inequalities, is a
finite intersection of half-spaces, hence convex; `W_ℓ ⊆ Q`; so `conv(W_ℓ) ⊆ Q` and
therefore `conv(W_ℓ) ∩ ℤ^ℓ ⊆ Q ∩ ℤ^ℓ = W_ℓ`.  The reverse inclusion is trivial.

## What is proved, and what is NOT

The one substantive input is `Q ∩ ℤ^ℓ = W_ℓ`, which is
`SortedBridge.insupp_iff_sorted` (2026-09-25) transported across the `ℤ → ℝ` coercion.
That transport is `mem_QR_iff_insupp` — an `iff`, stated as its own lemma and proved in
both directions, deliberately **not** hidden inside a `simp` set.

**`Q = P_λ̂` is NOT formalised and is NOT used.**  Only `W_ℓ ⊆ Q` enters.  The equality
is the real-coefficient form of Rado's theorem; the paper neither claims nor needs it.

## What Lean cannot see

Nothing is assumed here beyond `SortedSubsetBridge` and Mathlib.  The gap owed elsewhere
in this development is untouched and still owed: Murota's **symmetric** exchange axiom
(B-EXC) is not formalised — `MConvexExchange.insupp_exchange` proves the one-sided axiom
that the paper (and WZZ, Brändén–Huh) states, and the symmetric form is covered only by
brute force (0 failures / 876317 triples) in `proofs/code-q254-lean/`.  **Closing SNP
does not close B-EXC.**

`memory: a-definition-transported-into-Lean-is-unfalsifiable-inside-Lean`.  `QR` below is
a *new* definition, so it is exactly the place a wrong transport would hide.  Guards, all
theorems rather than assertions, in the `Guards` section: non-vacuity (`WR` inhabited),
a witness that the lattice intersection is doing real work (a non-integral point of
`conv(W)`), and a negative control for the size equation.

Indices are 0-based; the paper is 1-based.  `Λ_r` is `RobinHood.psum lhat r`.
-/

namespace SnpLattice

open Finset RobinHood MConvexExchange SortedBridge

/-! ### The coercion `ℤ^ℕ → ℝ^ℕ` -/

/-- The lattice embedding.  `Set.range toReal` is the set of integral points of `ℝ^ℕ`. -/
def toReal (α : ℕ → ℤ) : ℕ → ℝ := fun c => (α c : ℝ)

lemma sum_toReal (α : ℕ → ℤ) (S : Finset ℕ) :
    ∑ c ∈ S, toReal α c = ((∑ c ∈ S, α c : ℤ) : ℝ) := by
  simp [toReal]

/-! ### `Q`, the polyhedron cut out by the inequalities -/

/-- `Q = { x ∈ ℝ^ℓ : x ≥ 0, x([ℓ]) = |λ̂|, x(S) ≤ Λ_{|S|} ∀ S ⊆ [ℓ] }`, extended by the
hyperplanes `x c = 0` for `c ≥ ℓ` so that it lives in `ℝ^ℕ`.  Same clause order and same
quantification as `MConvexExchange.InSupp`, of which it is the real-coefficient form. -/
def QR (ℓ : ℕ) (lhat : ℕ → ℤ) : Set (ℕ → ℝ) :=
  { x | (∀ c, ℓ ≤ c → x c = 0) ∧ (∀ c, 0 ≤ x c) ∧
      ∑ c ∈ Finset.range ℓ, x c = ((psum lhat ℓ : ℤ) : ℝ) ∧
      ∀ S ∈ (Finset.range ℓ).powerset, ∑ c ∈ S, x c ≤ ((psum lhat S.card : ℤ) : ℝ) }

lemma sum_smul_add_smul (a b : ℝ) (x y : ℕ → ℝ) (S : Finset ℕ) :
    ∑ c ∈ S, (a • x + b • y) c = a * (∑ c ∈ S, x c) + b * (∑ c ∈ S, y c) := by
  simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- **`Q` is convex** — the first of the paper's three lines.  Proved from the definition
of `Convex`, one clause at a time, rather than by assembling half-spaces: every clause is
a linear equation or inequality, so the convex combination inherits it. -/
lemma convex_QR (ℓ : ℕ) (lhat : ℕ → ℤ) : Convex ℝ (QR ℓ lhat) := by
  rintro x ⟨hx1, hx2, hx3, hx4⟩ y ⟨hy1, hy2, hy3, hy4⟩ a b ha hb hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    simp [hx1 c hc, hy1 c hc]
  · intro c
    have h1 := hx2 c
    have h2 := hy2 c
    have : (a • x + b • y) c = a * x c + b * y c := by simp
    rw [this]
    positivity
  · rw [sum_smul_add_smul, hx3, hy3]
    have : a * ((psum lhat ℓ : ℤ) : ℝ) + b * ((psum lhat ℓ : ℤ) : ℝ)
        = (a + b) * ((psum lhat ℓ : ℤ) : ℝ) := by ring
    rw [this, hab, one_mul]
  · intro S hS
    have h1 := hx4 S hS
    have h2 := hy4 S hS
    have key : a * ((psum lhat S.card : ℤ) : ℝ) + b * ((psum lhat S.card : ℤ) : ℝ)
        = ((psum lhat S.card : ℤ) : ℝ) := by rw [← add_mul, hab, one_mul]
    rw [sum_smul_add_smul, ← key]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-! ### The coercion layer, stated as a lemma

This is the only place the `ℤ`/`ℝ` boundary is crossed.  It is an `iff`, and both
directions are proved; nothing is transported by fiat. -/

/-- **The transport.**  An integral point of `ℝ^ℕ` lies in `Q` exactly when the integer
vector it comes from lies in `MConvexExchange.InSupp`. -/
lemma mem_QR_iff_insupp (ℓ : ℕ) (lhat α : ℕ → ℤ) :
    toReal α ∈ QR ℓ lhat ↔ InSupp ℓ lhat α := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc
      have := h1 c hc
      simpa [toReal] using this
    · intro c
      have := h2 c
      simpa [toReal] using this
    · have := h3
      rw [sum_toReal] at this
      exact_mod_cast this
    · intro S hS
      have := h4 S hS
      rw [sum_toReal] at this
      rw [asum]
      exact_mod_cast this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro c hc
      simp [toReal, h1 c hc]
    · intro c
      have := h2 c
      simpa [toReal] using this
    · rw [sum_toReal]
      exact_mod_cast h3
    · intro S hS
      have := h4 S hS
      rw [asum] at this
      rw [sum_toReal]
      exact_mod_cast this

/-! ### `W_ℓ` -/

/-- `W_ℓ = {α ∈ ℕ^ℓ : sort(α) ⊴ λ̂}`, as a subset of `ℝ^ℕ` via the lattice embedding.
The predicate is `SortedBridge.InSuppSorted`, i.e. the paper's own sorted form. -/
def WR (ℓ : ℕ) (lhat : ℕ → ℤ) : Set (ℕ → ℝ) := toReal '' {α | InSuppSorted ℓ lhat α}

/-- `W_ℓ ⊆ Q` — the second of the paper's three lines.  This is where
`SortedBridge.insupp_iff_sorted` is consumed. -/
lemma WR_subset_QR {ℓ : ℕ} {lhat : ℕ → ℤ} (hl : IsPart ℓ lhat) :
    WR ℓ lhat ⊆ QR ℓ lhat := by
  rintro x ⟨α, hα, rfl⟩
  exact (mem_QR_iff_insupp ℓ lhat α).mpr ((insupp_iff_sorted hl).mpr hα)

/-! ### The target -/

/-- **Theorem 8.1 (SNP).**  `conv(W_ℓ) ∩ ℤ^ℓ = W_ℓ`: every lattice point of the convex
hull of `W_ℓ` already lies in `W_ℓ`.

Hypothesis: `λ̂` is a partition with at most `ℓ` parts (`IsPart ℓ lhat`).  Nothing else.
In particular `Q = P_λ̂` (Rado) is neither used nor proved. -/
theorem snp_lattice_points {ℓ : ℕ} {lhat : ℕ → ℤ} (hl : IsPart ℓ lhat) :
    convexHull ℝ (WR ℓ lhat) ∩ Set.range toReal = WR ℓ lhat := by
  apply Set.Subset.antisymm
  · rintro x ⟨hxhull, α, rfl⟩
    have hQ : toReal α ∈ QR ℓ lhat :=
      convexHull_min (WR_subset_QR hl) (convex_QR ℓ lhat) hxhull
    exact ⟨α, (insupp_iff_sorted hl).mp ((mem_QR_iff_insupp ℓ lhat α).mp hQ), rfl⟩
  · exact Set.subset_inter (subset_convexHull ℝ _) (fun _ ⟨α, _, h⟩ => ⟨α, h⟩)

/-! ### Faithfulness, non-vacuity, and the negative controls

`memory: a-definition-transported-into-Lean-is-unfalsifiable-inside-Lean`.  `QR` is a new
definition and `lake build` cannot see a wrong one, so four guards, every one a theorem:

* `toReal_injective` — `Set.range toReal` really is the lattice: distinct integer vectors
  have distinct images, so "integral point of `conv(W)`" is not a weaker condition than
  "point of `W`" by accident of the encoding.
* `snp_nonvacuous` — `W_ℓ` is **inhabited** for `λ̂ = (2,1)`.  A theorem about an empty
  set type-checks perfectly.
* `hull_strictly_larger` — the intersection with the lattice is **doing work**: the
  midpoint of `(2,1)` and `(1,2)` lies in `conv(W_2)` and is not integral.  Without this
  the theorem could hold because `conv(W) = W`, i.e. for no reason at all.
* `prefix_ineqs_insufficient` — the **negative control**: drop the half-spaces indexed by
  `|S| ≥ 2` and keep only the prefix inequalities `x(range r) ≤ Λ_r` (unsorted dominance).
  The resulting polyhedron is still convex and still contains `W`, so steps 1 and 2 of the
  paper proof survive — but its lattice points are strictly more than `W_2`, witnessed by
  `λ̂ = (3,1)`, `α = (0,4)`.  So step 3 is where the subset quantification is consumed and
  it cannot be weakened.  (Integer-side twin: `SortedBridge.sorted_not_unsorted`.)

Not formalised, and not needed by the proof: the non-negativity clause `x ≥ 0` of `Q` is
in fact **redundant** given the rest, since for each `i` the complement bound gives
`x_i = |λ̂| - x([ℓ] \ {i}) ≥ Λ_ℓ - Λ_{ℓ-1} = λ̂_ℓ ≥ 0`.  That is why the negative control
below drops the subset family rather than non-negativity: dropping `x ≥ 0` changes
nothing, so it could not be a control.  This observation is **recorded, not used** — and,
because it is a *reason for a design choice* rather than a step of the proof, no
instrument in this file grades it, so it is checked separately by enumeration in
`proofs/code-q256-snp/nonneg_redundant.py` (0 violations / 1877 feasible integer points,
97 pairs `(λ̂, ℓ)`, `ℓ ≤ 4`, `|λ̂| ≤ 7`, entries allowed down to `-(|λ̂|+2)`).
Cf. `memory: a-named-obstruction-is-never-the-object-of-the-check`.
-/

section Guards

/-- `Set.range toReal` is a faithful copy of `ℤ^ℕ`. -/
lemma toReal_injective : Function.Injective toReal := by
  intro α β h
  funext c
  have hc : ((α c : ℝ)) = ((β c : ℝ)) := congrFun h c
  exact_mod_cast hc

/-- Non-vacuity: for `λ̂ = (2,1)` the set `W_2` is inhabited, so `snp_lattice_points` is
not a statement about the empty set. -/
theorem snp_nonvacuous :
    toReal MConvexExchange.al21 ∈ WR 2 MConvexExchange.lhat21 :=
  ⟨MConvexExchange.al21, (insupp_iff_sorted MConvexExchange.lhat21_isPart).mp
    MConvexExchange.al21_mem, rfl⟩

/-- The lattice intersection is doing work: `conv(W_2) ⊋ W_2` for `λ̂ = (2,1)`, because
the midpoint of `(2,1)` and `(1,2)` is `(3/2, 3/2)`, which is in the hull and is not an
integral point. -/
theorem hull_strictly_larger :
    ((1 : ℝ)/2) • toReal MConvexExchange.al21 + ((1 : ℝ)/2) • toReal MConvexExchange.be12
        ∈ convexHull ℝ (WR 2 MConvexExchange.lhat21) ∧
      ((1 : ℝ)/2) • toReal MConvexExchange.al21 + ((1 : ℝ)/2) • toReal MConvexExchange.be12
        ∉ Set.range toReal := by
  constructor
  · have hx : toReal MConvexExchange.al21 ∈ convexHull ℝ (WR 2 MConvexExchange.lhat21) :=
      subset_convexHull ℝ _ snp_nonvacuous
    have hy : toReal MConvexExchange.be12 ∈ convexHull ℝ (WR 2 MConvexExchange.lhat21) :=
      subset_convexHull ℝ _ ⟨MConvexExchange.be12,
        (insupp_iff_sorted MConvexExchange.lhat21_isPart).mp MConvexExchange.be12_mem, rfl⟩
    exact (convex_convexHull ℝ _) hx hy (by norm_num) (by norm_num) (by norm_num)
  · rintro ⟨γ, hγ⟩
    have h0 := congrFun hγ 0
    simp only [toReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      MConvexExchange.al21, MConvexExchange.be12] at h0
    norm_num at h0
    have h2 : ((2 * γ 0 : ℤ) : ℝ) = ((3 : ℤ) : ℝ) := by push_cast; linarith
    have h3 : (2 : ℤ) * γ 0 = 3 := Int.cast_injective h2
    omega

private def lhat31 : ℕ → ℤ := fun c => if c = 0 then 3 else if c = 1 then 1 else 0
private def a04 : ℕ → ℤ := fun c => if c = 1 then 4 else 0

private lemma lhat31_isPart : IsPart 2 lhat31 := by
  constructor
  · apply antitone_nat_of_succ_le
    intro c
    simp only [lhat31]
    split_ifs <;> first | (exfalso; assumption) | omega
  · intro c hc; simp only [lhat31]; split_ifs <;> omega

private lemma a04_not_insupp : ¬ InSupp 2 lhat31 a04 := by
  intro h
  have := h.2.2.2 {1} (by decide)
  simp [asum, psum, a04, lhat31] at this

private lemma a04_prefix : ∀ r, psum a04 r ≤ psum lhat31 r := by
  intro r
  induction r with
  | zero => simp [psum]
  | succ n ih =>
      rw [psum_succ, psum_succ]
      have h1 : a04 n ≤ lhat31 n ∨ n = 1 := by
        simp only [a04, lhat31]; split_ifs <;> omega
      rcases h1 with h | rfl
      · omega
      · simp [psum, a04, lhat31]

/-- **Negative control.**  `x = (0,4)` satisfies non-negativity, the size equation, and
*every prefix* inequality `x(range r) ≤ Λ_r` for `λ̂ = (3,1)`; it is an integral point; and
it is **not** in `W_2`.  Hence the polyhedron obtained from `Q` by keeping only the prefix
half-spaces — still convex, still containing `W` — has strictly more lattice points than
`W`, and the quantification over all `S ⊆ [ℓ]` in `QR` is load-bearing. -/
theorem prefix_ineqs_insufficient :
    (∀ c, (2 : ℕ) ≤ c → toReal a04 c = 0) ∧ (∀ c, 0 ≤ toReal a04 c) ∧
      ∑ c ∈ Finset.range 2, toReal a04 c = ((psum lhat31 2 : ℤ) : ℝ) ∧
      (∀ r, ∑ c ∈ Finset.range r, toReal a04 c ≤ ((psum lhat31 r : ℤ) : ℝ)) ∧
      toReal a04 ∉ QR 2 lhat31 ∧ toReal a04 ∉ WR 2 lhat31 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [toReal, a04]; split_ifs <;> [omega; norm_num]
  · intro c; simp only [toReal, a04]; split_ifs <;> norm_num
  · rw [show (∑ c ∈ Finset.range 2, toReal a04 c) = ((psum a04 2 : ℤ) : ℝ) from
      sum_toReal a04 _]
    norm_num [psum, Finset.sum_range_succ, a04, lhat31]
  · intro r
    rw [show (∑ c ∈ Finset.range r, toReal a04 c) = ((psum a04 r : ℤ) : ℝ) from
      sum_toReal a04 _]
    exact_mod_cast a04_prefix r
  · intro h
    exact a04_not_insupp ((mem_QR_iff_insupp 2 lhat31 a04).mp h)
  · rintro ⟨γ, hγ, hEq⟩
    have : γ = a04 := toReal_injective hEq
    subst this
    exact a04_not_insupp ((insupp_iff_sorted lhat31_isPart).mpr hγ)

end Guards

end SnpLattice
