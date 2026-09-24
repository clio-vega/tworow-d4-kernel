/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Multiset.Sort
import Mathlib.Tactic.Ring

/-!
# The greedy chain for cylindric skew shapes

Formalisation of `§`"The greedy chain and the dominance maximum" of
`projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex`:

* `def:greedy` / `eq:greedy`  → `greedy`
* `lem:greedy`(1)             → `greedy_isCylindric`, `greedy_hstrip`, `greedy_sub_lam`
* `lem:greedy`(3)             → `greedy_dominates`
* `prop:noell`                → `greedy_eq_lam_of_le`, `incr_eq_zero_of_ge`,
                                `nonzeroIncr_indep_of_len`

The underlying combinatorial model (`def:shape`, `eq:hstrip`) is WZZ's cylindric skew
Schur setting, arXiv:2401.14632 §5, transported to bead coordinates by `prop:dictionary`
of the same note, following Lam–Postnikov.

## What is defined here versus assumed

Nothing is assumed.  Unlike `AffineAdditive.lean` — where `Additive` had to *define* the
paper's criterion because the affine symmetric group is not in Mathlib — every object
below is an explicit inequality on integer sequences, so `IsCylindric`, `Sub`, `HStrip`
and `greedy` are literal transcriptions of `def:shape`, `eq:hstrip` and `eq:greedy`.
The transcription itself is the only unfalsifiable step, and it is checked externally by
`projects/proofs/code-greedy/greedy_check.py` (brute-force enumeration of all chains for
small `(n, m)`).

Row indices increase **downwards**, so the dictionary sign is `xᵢ = Rᵢ + i`, not
`Rᵢ - i` (`rem:orient`).  That convention is invisible to the statements below — they
speak only of the bead coordinates `x : ℤ → ℤ` — but it is what makes them the paper's
statements.

## Scope

`prop:max` (the greedy weight is the dominance maximum of the support) and M-convexity
are **not** formalised here: they need `Sₗ`-stability and the Bender–Knuth corollary.

For `prop:noell` the `ℓ`-independence is stated as *the multiset of nonzero increments
does not depend on `ℓ`* (`nonzeroIncr_indep_of_len`).  This is the mathematical content
of "sorting discards the trailing zeros"; the further claim that

> `List.filter (· ≠ 0) (Multiset.sort (· ≥ ·) γ) = Multiset.sort (· ≥ ·) (γ.filter (· ≠ 0))`

— i.e. that passing to the sorted *presentation* commutes with dropping the zeros — is a
genuine proposition and is **not** proved here.  It is recorded as such rather than
waved through as presentation.

No `sorry`, no `native_decide`, no local axioms.
-/

namespace GreedyChain

variable {n m : ℕ} {lam mu : ℤ → ℤ}

/-! ### Cylindric shapes (`def:shape`) -/

/-- A **cylindric shape of type `(n, m)`** is a strictly increasing `x : ℤ → ℤ` with
`x (i + m) = x i + n`.  This is `def:shape`; `Cyl^{n,m}` in the paper. -/
structure IsCylindric (n m : ℕ) (x : ℤ → ℤ) : Prop where
  /-- `n`-periodicity with period `m` in the index: `x (i + m) = x i + n`. -/
  per : ∀ i : ℤ, x (i + m) = x i + n
  /-- Strict increase, in the successor form that generates it. -/
  inc : ∀ i : ℤ, x i < x (i + 1)

/-- Containment `x ⊆ y`: `xᵢ ≤ yᵢ` for all `i` (`prop:dictionary`(i)). -/
def Sub (x y : ℤ → ℤ) : Prop := ∀ i : ℤ, x i ≤ y i

/-- `HStrip x y` says `y / x` is a **horizontal strip**: `xᵢ ≤ yᵢ < xᵢ₊₁` for all `i`.
This is `eq:hstrip`. -/
def HStrip (x y : ℤ → ℤ) : Prop := ∀ i : ℤ, x i ≤ y i ∧ y i < x (i + 1)

/-- The weight functional `u x = ∑_{i=1}^{m} xᵢ`, a sum over one fundamental domain
(`def:shape`). -/
def u (m : ℕ) (x : ℤ → ℤ) : ℤ := ∑ i ∈ Finset.range m, x ((i : ℤ) + 1)

/-! ### The greedy chain (`def:greedy`) -/

/-- The **greedy chain** for `λ/μ`: `g⁰ = μ` and `gᵗᵢ = min (gᵗ⁻¹ᵢ₊₁ - 1, λᵢ)`.
This is `eq:greedy`.  Note the recursion does not mention the chain length `ℓ` — that is
the whole point of `prop:noell`. -/
def greedy (lam mu : ℤ → ℤ) : ℕ → ℤ → ℤ
  | 0 => mu
  | t + 1 => fun i => min (greedy lam mu t (i + 1) - 1) (lam i)

@[simp] theorem greedy_zero : greedy lam mu 0 = mu := rfl

theorem greedy_succ (t : ℕ) (i : ℤ) :
    greedy lam mu (t + 1) i = min (greedy lam mu t (i + 1) - 1) (lam i) := rfl

/-! ### Milestone A1: the greedy chain stays cylindric (`lem:greedy`(1), first sentence) -/

/-- `lem:greedy`(1): each `gᵗ` is again a cylindric shape, being a coordinatewise minimum
of two strictly increasing `n`-periodic sequences. -/
theorem greedy_isCylindric (hlam : IsCylindric n m lam) (hmu : IsCylindric n m mu) :
    ∀ t : ℕ, IsCylindric n m (greedy lam mu t) := by
  intro t
  induction t with
  | zero => simpa using hmu
  | succ t ih =>
    refine ⟨fun i => ?_, fun i => ?_⟩
    · have hshift : i + (m : ℤ) + 1 = (i + 1) + (m : ℤ) := by ring
      rw [greedy_succ, greedy_succ, hshift, ih.per (i + 1), hlam.per i]
      omega
    · have h1 := ih.inc (i + 1)
      have h2 := hlam.inc i
      rw [greedy_succ, greedy_succ]
      omega

/-! ### Milestone A2: one greedy step is a horizontal strip (`lem:greedy`(1)) -/

/-- `gᵗ ⊆ λ` for every `t`, given `μ ⊆ λ`.  For `t ≥ 1` this is `min_le_right`; the
hypothesis is only needed at `t = 0`. -/
theorem greedy_sub_lam (hmu : Sub mu lam) : ∀ t : ℕ, Sub (greedy lam mu t) lam := by
  intro t
  cases t with
  | zero => simpa using hmu
  | succ t => intro i; rw [greedy_succ]; exact min_le_right _ _

/-- `lem:greedy`(1): if `gᵗ ⊆ λ` then `gᵗ ⊆ gᵗ⁺¹`, i.e. the chain is weakly increasing
in `t`.  This is `prop:noell`'s step **C1**. -/
theorem greedy_le_succ (hg : IsCylindric n m (greedy lam mu t))
    (hsub : Sub (greedy lam mu t) lam) : Sub (greedy lam mu t) (greedy lam mu (t + 1)) := by
  intro i
  have h1 := hg.inc i
  have h2 := hsub i
  rw [greedy_succ]
  omega

/-- `lem:greedy`(1): `gᵗ⁺¹ / gᵗ` is a horizontal strip. -/
theorem greedy_hstrip (hg : IsCylindric n m (greedy lam mu t))
    (hsub : Sub (greedy lam mu t) lam) : HStrip (greedy lam mu t) (greedy lam mu (t + 1)) := by
  intro i
  refine ⟨greedy_le_succ (n := n) (m := m) hg hsub i, ?_⟩
  have := min_le_left (greedy lam mu t (i + 1) - 1) (lam i)
  rw [greedy_succ]
  omega

/-! ### Milestone B: the greedy chain dominates coordinatewise (`lem:greedy`(3)) -/

/-- Any chain of horizontal strips is weakly increasing: `xᵗ ⊆ xˢ` for `t ≤ s ≤ ℓ`. -/
theorem chain_mono {x : ℕ → ℤ → ℤ} {l : ℕ}
    (hstrip : ∀ t, t < l → HStrip (x t) (x (t + 1))) :
    ∀ s, s ≤ l → ∀ t, t ≤ s → Sub (x t) (x s) := by
  intro s
  induction s with
  | zero =>
    intro _ t ht i
    rw [Nat.le_zero.mp ht]
  | succ s ih =>
    intro hs t ht i
    rcases Nat.lt_or_ge t (s + 1) with h | h
    · exact le_trans (ih (by omega) t (Nat.lt_succ_iff.mp h) i) ((hstrip s (by omega)) i).1
    · have : t = s + 1 := le_antisymm ht h
      rw [this]

/-- Every shape in a chain from `μ` to `λ` is contained in `λ`: `xᵗ ⊆ xˡ = λ`. -/
theorem chain_sub_lam {x : ℕ → ℤ → ℤ} {l : ℕ}
    (hstrip : ∀ t, t < l → HStrip (x t) (x (t + 1))) (hxl : x l = lam) :
    ∀ t, t ≤ l → Sub (x t) lam := by
  intro t ht i
  have := chain_mono hstrip l le_rfl t ht i
  rw [hxl] at this
  exact this

/-- **`lem:greedy`(3).**  For every chain `T = (x⁰, …, xˡ)` with `x⁰ = μ`, `xˡ = λ` and
each `xᵗ⁺¹ / xᵗ` a horizontal strip, one has `xᵗᵢ ≤ gᵗᵢ` for all `t ≤ ℓ` and all `i`:
the greedy chain dominates every chain coordinatewise.

This is the lemma the dominance-maximum argument (`prop:max`) rests on.  Note it needs
neither periodicity nor `μ ⊆ λ` — only the strip conditions. -/
theorem greedy_dominates {x : ℕ → ℤ → ℤ} {l : ℕ}
    (hx0 : x 0 = mu) (hxl : x l = lam)
    (hstrip : ∀ t, t < l → HStrip (x t) (x (t + 1))) :
    ∀ t, t ≤ l → Sub (x t) (greedy lam mu t) := by
  have hsub := chain_sub_lam hstrip hxl
  intro t
  induction t with
  | zero => intro _ i; rw [hx0]; simp
  | succ t ih =>
    intro ht i
    have hgt : x t (i + 1) ≤ greedy lam mu t (i + 1) := ih (by omega) (i + 1)
    have hlt : x (t + 1) i < x t (i + 1) := ((hstrip t (by omega)) i).2
    have hlam : x (t + 1) i ≤ lam i := hsub (t + 1) ht i
    rw [greedy_succ]
    omega

/-- `lem:greedy`(3), weight form: `u xᵗ ≤ u gᵗ`. -/
theorem u_le_u_greedy {x : ℕ → ℤ → ℤ} {l : ℕ}
    (hx0 : x 0 = mu) (hxl : x l = lam)
    (hstrip : ∀ t, t < l → HStrip (x t) (x (t + 1))) :
    ∀ t, t ≤ l → u m (x t) ≤ u m (greedy lam mu t) := by
  intro t ht
  exact Finset.sum_le_sum fun i _ => greedy_dominates hx0 hxl hstrip t ht ((i : ℤ) + 1)

/-! ### Milestone C: `prop:noell`, `λ̂` does not depend on `ℓ` -/

/-- **C2.**  Once the greedy chain reaches `λ` it stays there:
`min (λᵢ₊₁ - 1, λᵢ) = λᵢ` because `λ` is strictly increasing.

This single sentence — strict increase of `λ`, nothing else — is what closes gap (iii)
of the 09-20 note, whose stated obstruction ("`λ̂` grows with `ℓ`") was false. -/
theorem greedy_fix (hlam : IsCylindric n m lam) {t : ℕ} (ht : greedy lam mu t = lam) :
    greedy lam mu (t + 1) = lam := by
  funext i
  have h := hlam.inc i
  rw [greedy_succ, ht]
  omega

/-- **C2, iterated.**  `gˢ = λ` for every `s ≥ ℓ₀` once `g^{ℓ₀} = λ`. -/
theorem greedy_eq_lam_of_le (hlam : IsCylindric n m lam) {l0 : ℕ}
    (h0 : greedy lam mu l0 = lam) : ∀ s, l0 ≤ s → greedy lam mu s = lam := by
  intro s hs
  induction s with
  | zero => rwa [Nat.le_zero.mp hs] at h0
  | succ s ih =>
    rcases Nat.lt_or_ge l0 (s + 1) with h | h
    · exact greedy_fix hlam (ih (by omega))
    · have : l0 = s + 1 := le_antisymm hs h
      rwa [this] at h0

/-- The increment `γₜ₊₁ = u gᵗ⁺¹ - u gᵗ` of the greedy chain (`def` before
`prop:noell`), indexed so that `incr t` is the paper's `γ_{t+1}`. -/
def incr (m : ℕ) (lam mu : ℤ → ℤ) (t : ℕ) : ℤ :=
  u m (greedy lam mu (t + 1)) - u m (greedy lam mu t)

/-- **C3, step one.**  All increments past `ℓ₀` vanish. -/
theorem incr_eq_zero_of_ge (hlam : IsCylindric n m lam) {l0 t : ℕ}
    (h0 : greedy lam mu l0 = lam) (ht : l0 ≤ t) : incr m lam mu t = 0 := by
  rw [incr, greedy_eq_lam_of_le (n := n) (m := m) hlam h0 t ht,
    greedy_eq_lam_of_le (n := n) (m := m) hlam h0 (t + 1) (by omega)]
  ring

/-- The multiset of **nonzero** increments of the greedy chain of length `ℓ`. -/
def nonzeroIncr (m : ℕ) (lam mu : ℤ → ℤ) (l : ℕ) : Multiset ℤ :=
  ((Multiset.range l).map (incr m lam mu)).filter (· ≠ 0)

/-- **`prop:noell`, C3.**  For `ℓ₁, ℓ₂ ≥ ℓ₀` the multiset of nonzero greedy increments is
the same: `λ̂` does not depend on `ℓ` on its whole domain of definition.

This is the mathematical content of "sorting discards the trailing zeros"; see the module
header for the presentation-level claim that is *not* proved. -/
theorem nonzeroIncr_indep_of_len (hlam : IsCylindric n m lam) {l0 l1 l2 : ℕ}
    (h0 : greedy lam mu l0 = lam) (h1 : l0 ≤ l1) (h12 : l1 ≤ l2) :
    nonzeroIncr m lam mu l2 = nonzeroIncr m lam mu l1 := by
  induction l2, h12 using Nat.le_induction with
  | base => rfl
  | succ l2 hl2 ih =>
    have hz : incr m lam mu l2 = 0 :=
      incr_eq_zero_of_ge (n := n) (m := m) hlam h0 (by omega)
    rw [nonzeroIncr, Multiset.range_succ, Multiset.map_cons,
      Multiset.filter_cons_of_neg _ (by simp [hz])]
    exact ih

/-! ### Non-vacuity

`greedy_dominates` is an implication, so it would be satisfied by an empty hypothesis
set.  The witnesses below rule that out, and rule out the weaker failure mode of the
conclusion being an equality: at `n = 2`, `m = 1`, `μ i = 2i`, `λ i = 2i + 1` the chain
`μ, μ, λ` is legal and its middle term is **strictly** below `g¹ = λ`.
-/

/-- `μ i = 2i` is a cylindric shape of type `(2, 1)`. -/
theorem witness_mu_cylindric : IsCylindric 2 1 (fun i : ℤ => 2 * i) :=
  ⟨fun i => by push_cast; ring, fun i => by omega⟩

/-- `λ i = 2i + 1` is a cylindric shape of type `(2, 1)`. -/
theorem witness_lam_cylindric : IsCylindric 2 1 (fun i : ℤ => 2 * i + 1) :=
  ⟨fun i => by push_cast; ring, fun i => by omega⟩

/-- The hypotheses of `greedy_dominates` are satisfiable, and its conclusion is a
strict inequality for at least one chain: the legal chain `μ, μ, λ` has
`x¹ 0 = 0 < 1 = g¹ 0`. -/
theorem witness_dominates_strictly :
    ∃ x : ℕ → ℤ → ℤ,
      x 0 = (fun i : ℤ => 2 * i) ∧ x 2 = (fun i : ℤ => 2 * i + 1) ∧
      (∀ t, t < 2 → HStrip (x t) (x (t + 1))) ∧
      x 1 0 < greedy (fun i : ℤ => 2 * i + 1) (fun i : ℤ => 2 * i) 1 0 := by
  refine ⟨fun t => if t ≤ 1 then (fun i : ℤ => 2 * i) else (fun i : ℤ => 2 * i + 1),
    by norm_num, by norm_num, ?_, ?_⟩
  · intro t ht i
    match t, ht with
    | 0, _ => exact (show 2 * i ≤ 2 * i ∧ 2 * i < 2 * (i + 1) by omega)
    | 1, _ => exact (show 2 * i ≤ 2 * i + 1 ∧ 2 * i + 1 < 2 * (i + 1) by omega)
  · show (2 : ℤ) * 0 < greedy (fun i : ℤ => 2 * i + 1) (fun i : ℤ => 2 * i) 1 0
    norm_num [greedy_succ]

end GreedyChain
