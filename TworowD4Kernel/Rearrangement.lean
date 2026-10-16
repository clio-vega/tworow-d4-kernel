/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Domination survives decreasing rearrangement (Q473, `lem:match`)

The proof of `lem:match` in `projects/proofs/2026-10-15-Q473-GDMW-independence.tex`
(line 233; the `⟹` direction at lines 244–249) runs on two clauses that the tex asserts
and does not prove:

1. *"since `ι` is injective these are `n'` distinct entries of the list `c`, so the `j`-th
   largest among them is at most the `j`-th largest of the whole list: `e_j ≤ c_[j]`"*;
2. *"pointwise domination is preserved by decreasing rearrangement"*.

Clause 2 is the headline target here (`antitone_sort_mono`); clause 1 falls out of the
same lemma (`sorted_comp_le_sorted`).  The Lean proof of `lem:match` already in
`TworowD4Kernel.HalfspaceOrder` (`Q473.exists_inj_iff`) routes *around* both clauses with a
direct counting argument, so nothing in the development depends on this file.  It exists
because routing around a gap and closing it are different acts.

The result these lemmas serve is the linear independence of the half-space symmetric
functions of Garbali–de Gier–Mead–Wheeler, *Symmetric functions from the six-vertex model in
half-space*, `arXiv:2312.14348` (source `Half_line_ASEP.tex`, Conjecture `conj:F-orth`,
line 443).

## The mechanism

Everything is the *level-set characterisation* `antitone_le_iff_countAbove_le`:

> for `a` antitone, `a j ≤ t ↔ #{i | t < a i} ≤ j`.

An antitone tuple is determined by its level-set counts, and the counts are
permutation-invariant; so a comparison between *rearrangements* becomes a comparison
between *counts*, where the permutations are simply not present.  Both clauses above, the
uniqueness of the antitone rearrangement, and a second proof of `lem:match` are then
corollaries of one master lemma, `le_of_countAbove_le`.

Honest note on independence: this is **not** a mechanism independent of
`Q473.exists_inj_iff`'s counting proof.  That proof's two steps — a sublevel set is
contained in an `Iio`, and `Iic j` injects into it — are exactly the two directions of
`antitone_le_iff_countAbove_le`.  What this file supplies is a lemma boundary drawn in a
different place, which is what makes the tex's clauses nameable and reusable; the kernel is
the same counting.

## Design note

`Tuple.sort` sorts *monotonically*, so the statements here never mention it.  Following
`Q473.exists_inj_iff`, a decreasing rearrangement is spelled *"antitone, and equal to
`c ∘ σ` for some `σ : Equiv.Perm (Fin N)`"*.  `Q473.exists_antitone_rearrangement`
(in `HalfspaceOrder`) supplies the witness via `OrderDual`.
-/

namespace Q473

open Finset

variable {m n N : ℕ}

/-- `#{i | t < a i}`: the number of entries of `a` strictly exceeding `t`.  This is the
level-set count that an antitone rearrangement is determined by, and it is the only thing
the lemmas of this file ever compare. -/
def countAbove (a : Fin N → ℕ) (t : ℕ) : ℕ :=
  #{i | t < a i}

theorem countAbove_def (a : Fin N → ℕ) (t : ℕ) : countAbove a t = #{i | t < a i} := rfl

/-- `countAbove` as an explicit `Finset.filter` card.  The `#{i | _}` notation of the
definition elaborates to a `Finset` only in that position; inside proofs the same brace
syntax is read as a `Set`, so every proof below goes through this spelling. -/
theorem countAbove_filter (a : Fin N → ℕ) (t : ℕ) :
    countAbove a t = (Finset.univ.filter (fun i => t < a i)).card := rfl

/-- Level-set counts are permutation-invariant.  This is the step at which the permutations
of the rearrangement statements disappear. -/
theorem countAbove_comp_perm (a : Fin N → ℕ) (σ : Equiv.Perm (Fin N)) (t : ℕ) :
    countAbove (a ∘ σ) t = countAbove a t :=
  Finset.card_equiv σ (by simp)

/-- **The level-set characterisation.**  An antitone tuple is pinned down by its level-set
counts: `a j ≤ t` exactly when at most `j` entries exceed `t`.

Both directions are a cardinality comparison against an interval, and they are the two
halves of the counting proof of `Q473.exists_inj_iff`:
`⟹` is *"the sublevel set sits inside `Iio j`"*, `⟸` is *"`Iic j` sits inside it"*. -/
theorem antitone_le_iff_countAbove_le {a : Fin N → ℕ} (ha : Antitone a) (j : Fin N) (t : ℕ) :
    a j ≤ t ↔ countAbove a t ≤ (j : ℕ) := by
  rw [countAbove_filter]
  constructor
  · intro hj
    have hsub : Finset.univ.filter (fun i => t < a i) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hge
      have := ha (not_lt.mp hge)
      omega
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h1
    exact h1
  · intro hcard
    by_contra hcon
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => t < a i) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have := ha hi
      omega
    have h1 := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h1
    omega

/-- An injection that raises entries above `t` wherever `a` is above `t` cannot decrease the
level-set count.  The hypothesis is deliberately `t < a i → t < b (ι i)` rather than
`a i ≤ b (ι i)`: the weaker form is what the sublist clause (clause 1) needs. -/
theorem countAbove_le_of_inj {a : Fin m → ℕ} {b : Fin N → ℕ} {t : ℕ} {ι : Fin m → Fin N}
    (hι : Function.Injective ι) (h : ∀ i, t < a i → t < b (ι i)) :
    countAbove a t ≤ countAbove b t := by
  rw [countAbove_filter, countAbove_filter]
  refine Finset.card_le_card_of_injOn ι ?_ hι.injOn
  intro i hi
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

/-- **Master lemma.**  Two antitone tuples, possibly of different lengths: domination of
level-set counts gives pointwise domination.  Everything below is an instance. -/
theorem le_of_countAbove_le {e : Fin m → ℕ} {d : Fin N → ℕ} (he : Antitone e) (hd : Antitone d)
    (hle : ∀ t, countAbove e t ≤ countAbove d t) (h : m ≤ N) (j : Fin m) :
    e j ≤ d (Fin.castLE h j) := by
  rw [antitone_le_iff_countAbove_le he j]
  have h1 : countAbove d (d (Fin.castLE h j)) ≤ ((Fin.castLE h j : Fin N) : ℕ) :=
    (antitone_le_iff_countAbove_le hd (Fin.castLE h j) _).mp le_rfl
  simp only [Fin.val_castLE] at h1
  exact le_trans (hle _) h1

/-- The equal-length case of `le_of_countAbove_le`. -/
theorem le_of_countAbove_le' {a' b' : Fin N → ℕ} (ha' : Antitone a') (hb' : Antitone b')
    (hle : ∀ t, countAbove a' t ≤ countAbove b' t) (j : Fin N) : a' j ≤ b' j := by
  simpa using le_of_countAbove_le ha' hb' hle le_rfl j

/-! ### Clause 2: domination survives decreasing rearrangement -/

/-- **The target.**  Clause 2 of the tex's `lem:match` proof, in the strongest form the
mechanism gives: the pointwise hypothesis `a i ≤ b i` is *lesioned* down to *"some injection
`ι` with `a i ≤ b (ι i)`"*.  Level-set counts do not see `ι`, so the cost is zero — and this
is the form `lem:match` actually wants, since there the domination arrives through exactly
such an injection. -/
theorem antitone_sort_mono_of_inj {a b : Fin N → ℕ} {ι : Fin N → Fin N}
    (hι : Function.Injective ι) (h : ∀ i, a i ≤ b (ι i)) {a' b' : Fin N → ℕ}
    (ha' : Antitone a') (hb' : Antitone b') (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, a' i = a (σ i))
    (τ : Equiv.Perm (Fin N)) (hτ : ∀ i, b' i = b (τ i)) :
    ∀ j, a' j ≤ b' j := by
  have hae : a' = a ∘ σ := funext hσ
  have hbe : b' = b ∘ τ := funext hτ
  refine le_of_countAbove_le' ha' hb' fun t => ?_
  rw [hae, hbe, countAbove_comp_perm, countAbove_comp_perm]
  exact countAbove_le_of_inj hι fun i hi => lt_of_lt_of_le hi (h i)

/-- **Clause 2 as the tex states it.**  *"Pointwise domination is preserved by decreasing
rearrangement"*: if `a i ≤ b i` for every `i`, then the antitone rearrangements satisfy
`a' j ≤ b' j` for every `j`.  Tex: `2026-10-15-Q473-GDMW-independence.tex` line 247. -/
theorem antitone_sort_mono {a b : Fin N → ℕ} (h : ∀ i, a i ≤ b i) {a' b' : Fin N → ℕ}
    (ha' : Antitone a') (hb' : Antitone b') (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, a' i = a (σ i))
    (τ : Equiv.Perm (Fin N)) (hτ : ∀ i, b' i = b (τ i)) :
    ∀ j, a' j ≤ b' j :=
  antitone_sort_mono_of_inj Function.injective_id h ha' hb' σ hσ τ hτ

/-- A tuple has exactly one antitone rearrangement.  Immediate from `antitone_sort_mono`
applied in both directions with `a = b = c`; the tex uses this silently when it writes
`κ'_[j] = κ'_j` for the already-decreasing `κ'`. -/
theorem antitone_rearrangement_unique {c a' b' : Fin N → ℕ} (ha' : Antitone a')
    (hb' : Antitone b') (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, a' i = c (σ i))
    (τ : Equiv.Perm (Fin N)) (hτ : ∀ i, b' i = c (τ i)) : a' = b' :=
  funext fun j => le_antisymm (antitone_sort_mono (fun _ => le_rfl) ha' hb' σ hσ τ hτ j)
    (antitone_sort_mono (fun _ => le_rfl) hb' ha' τ hτ σ hσ j)

/-! ### Clause 1: a sorted sub-list is dominated by the sorted list -/

/-- **Clause 1** of the tex's `lem:match` proof: *"since `ι` is injective these are `n'`
distinct entries of the list `c`, so the `j`-th largest among them is at most the `j`-th
largest of the whole list"*.  Tex line 245.  `e` is the decreasing rearrangement of
`c ∘ ι`, `d'` that of `c`.  Same master lemma, now across different lengths. -/
theorem sorted_comp_le_sorted {c : Fin N → ℕ} {ι : Fin m → Fin N} (hι : Function.Injective ι)
    {e : Fin m → ℕ} (he : Antitone e) (ρ : Equiv.Perm (Fin m))
    (hρ : ∀ i, e i = c (ι (ρ i))) {d' : Fin N → ℕ} (hd' : Antitone d')
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, d' i = c (σ i)) (h : m ≤ N) (j : Fin m) :
    e j ≤ d' (Fin.castLE h j) := by
  have hee : e = (c ∘ ι) ∘ ρ := funext hρ
  have hde : d' = c ∘ σ := funext hσ
  refine le_of_countAbove_le he hd' (fun t => ?_) h j
  rw [hee, hde, countAbove_comp_perm, countAbove_comp_perm]
  exact countAbove_le_of_inj hι fun i hi => hi

/-! ### The wire-back: a second proof of `lem:match` -/

/-- The `⟹` direction of `lem:match` by the tex's own route, i.e. through the level-set
characterisation rather than the ad-hoc count of `Q473.exists_inj_iff`.

Note what the Lean proof says about the tex: the two clauses can be *fused*.  The tex
interposes `e`, the rearrangement of the selected sub-list, and compares `κ' ≤ e ≤ c_[·]`.
The counts do not need the intermediate tuple — `countAbove a t ≤ countAbove c t` directly —
so `e` is an artefact of reasoning in terms of sorted lists instead of level sets. -/
theorem le_rearrangement_of_inj {a : Fin n → ℕ} {c d : Fin N → ℕ} (ha : Antitone a)
    (hd : Antitone d) (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, d i = c (σ i)) (h : n ≤ N)
    {ι : Fin n → Fin N} (hinj : Function.Injective ι) (hdom : ∀ j, a j ≤ c (ι j)) (j : Fin n) :
    a j ≤ d (Fin.castLE h j) := by
  have hde : d = c ∘ σ := funext hσ
  refine le_of_countAbove_le ha hd (fun t => ?_) h j
  rw [hde, countAbove_comp_perm]
  exact countAbove_le_of_inj hinj fun i hi => lt_of_lt_of_le hi (hdom i)

/-- **`lem:match`** (tex line 233) again, with the `⟹` direction proved by the tex's
rearrangement route.  Statement identical to `Q473.exists_inj_iff` in
`TworowD4Kernel.HalfspaceOrder`; the `⟸` direction is the same greedy injection. -/
theorem exists_inj_iff_rearrangement {a : Fin n → ℕ} {c d : Fin N → ℕ} (ha : Antitone a)
    (hd : Antitone d) (σ : Equiv.Perm (Fin N)) (hσ : ∀ i, d i = c (σ i)) (h : n ≤ N) :
    (∃ ι : Fin n → Fin N, Function.Injective ι ∧ ∀ j, a j ≤ c (ι j))
      ↔ ∀ j : Fin n, a j ≤ d (Fin.castLE h j) := by
  constructor
  · rintro ⟨ι, hinj, hdom⟩ j
    exact le_rearrangement_of_inj ha hd σ hσ h hinj hdom j
  · intro hdom
    refine ⟨fun j => σ (Fin.castLE h j), σ.injective.comp (Fin.castLE_injective h), fun j => ?_⟩
    rw [← hσ]
    exact hdom j

end Q473
