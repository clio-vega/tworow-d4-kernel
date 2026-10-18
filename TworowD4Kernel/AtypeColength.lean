/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Defs

/-!
# The two colength counts of Theorem A, as finite combinatorics

Formalisation of the combinatorial skeleton of `lem:colenG`, `lem:colenL` and
`lem:typeB` of `projects/proofs/2026-10-18-atype-divisors-and-the-gkm-lattice.tex`
(Theorem A, `L_ij = G_ij`).

Only the *counting* is formalised here.  The module theory (δ-surjectivity,
Smith normal form, valuation of a determinant) is NOT in scope: the paper
reduces both colengths to a cardinality over `Finset (Fin N)`, and those two
cardinalities are what is certified below.
-/

namespace AtypeColength

open Finset

variable {N : ℕ}

/-- `i ≠ j` in `Fin N` already forces `2 ≤ N`.  The paper leaves `2 ≤ N`
implicit; it is a consequence, not a hypothesis. -/
theorem two_le_of_ne {i j : Fin N} (h : i ≠ j) : 2 ≤ N := by
  have hi := i.isLt
  have hj := j.isLt
  have : i.val ≠ j.val := fun e => h (Fin.ext e)
  omega

/-- The reflection `s_ij` of the paper (`defn`, L178--L186), stated in the
paper's own case form: it exchanges membership of `i` and `j` exactly on the
points where precisely one of them is present. -/
def refl (i j : Fin N) (M : Finset (Fin N)) : Finset (Fin N) :=
  if (M ∩ {i, j}).card = 1 then symmDiff M {i, j} else M

/-- The moved locus `P^mv := {M : |M ∩ {i,j}| = 1}`. -/
def moved (i j : Fin N) : Finset (Finset (Fin N)) :=
  {M : Finset (Fin N) | (M ∩ {i, j}).card = 1}

/-- The label set of `lem:colenL`: `{I : i ∉ I ∧ j ∈ I}`. -/
def labels (i j : Fin N) : Finset (Finset (Fin N)) :=
  {I : Finset (Fin N) | i ∉ I ∧ j ∈ I}

@[simp] theorem mem_moved {i j : Fin N} {M : Finset (Fin N)} :
    M ∈ moved i j ↔ (M ∩ {i, j}).card = 1 := by
  simp [moved]

@[simp] theorem mem_labels {i j : Fin N} {I : Finset (Fin N)} :
    I ∈ labels i j ↔ i ∉ I ∧ j ∈ I := by
  simp [labels]


/-! ### The reflection is an involution, and what it does to the moved locus -/

/-- `s_ij = s_ji`: the definition is symmetric in `i, j`. -/
theorem refl_comm (i j : Fin N) (M : Finset (Fin N)) : refl i j M = refl j i M := by
  simp [refl, Finset.pair_comm]

/-- Membership in `P^mv`, unpacked.  Needs `i ≠ j`: at `i = j` the intersection
has card `0` or `1` and the right-hand side is unsatisfiable. -/
theorem mem_moved_iff {i j : Fin N} (h : i ≠ j) {M : Finset (Fin N)} :
    M ∈ moved i j ↔ (i ∈ M ∧ j ∉ M) ∨ (i ∉ M ∧ j ∈ M) := by
  rw [mem_moved]
  have hpair : ({i, j} : Finset (Fin N)).card = 2 := by
    rw [Finset.card_pair h]
  by_cases hi : i ∈ M <;> by_cases hj : j ∈ M
  · have : M ∩ {i, j} = {i, j} := by
      apply Finset.inter_eq_right.2
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    simp [this, hpair, hi, hj]
  · have : M ∩ {i, j} = {i} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxM, rfl | rfl⟩
        · rfl
        · exact absurd hxM hj
      · rintro rfl; exact ⟨hi, Or.inl rfl⟩
    simp [this, hi, hj]
  · have : M ∩ {i, j} = {j} := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hxM, rfl | rfl⟩
        · exact absurd hxM hi
        · rfl
      · rintro rfl; exact ⟨hj, Or.inr rfl⟩
    simp [this, hi, hj]
  · have : M ∩ {i, j} = ∅ := by
      ext x; simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro hxM (rfl | rfl)
      · exact hi hxM
      · exact hj hxM
    simp [this, hi, hj]

/-- On the half of `P^mv` where `i` is present, `s_ij` moves `i` out and `j` in. -/
theorem refl_eq_of_left {i j : Fin N} (h : i ≠ j) {M : Finset (Fin N)}
    (hi : i ∈ M) (hj : j ∉ M) : refl i j M = insert j (M.erase i) := by
  have hc : (M ∩ {i, j}).card = 1 := (mem_moved (i := i) (j := j)).1
    ((mem_moved_iff h).2 (Or.inl ⟨hi, hj⟩))
  rw [refl, if_pos hc]
  ext x
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton,
    Finset.mem_erase]
  rcases eq_or_ne x i with rfl | hxi
  · simp [hi, h, Ne.symm h]
  rcases eq_or_ne x j with rfl | hxj
  · simp [hj, hxi]
  · simp [hxi, hxj]

/-- `s_ij` is an involution on all of `P` (not just on `P^mv`). -/
theorem refl_involutive {i j : Fin N} (h : i ≠ j) (M : Finset (Fin N)) :
    refl i j (refl i j M) = M := by
  by_cases hM : M ∈ moved i j
  · rcases (mem_moved_iff h).1 hM with ⟨hi, hj⟩ | ⟨hi, hj⟩
    · have h1 : refl i j M = insert j (M.erase i) := refl_eq_of_left h hi hj
      have hj' : j ∈ insert j (M.erase i) := Finset.mem_insert_self _ _
      have hi' : i ∉ insert j (M.erase i) := by
        simp [h]
      rw [h1, refl_comm, refl_eq_of_left (Ne.symm h) hj' hi']
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
      rcases eq_or_ne x i with rfl | hxi
      · simp [hi, h]
      rcases eq_or_ne x j with rfl | hxj
      · simp [hj, hxi]
      · simp [hxi, hxj]
    · have h1 : refl i j M = insert i (M.erase j) := by
        rw [refl_comm]; exact refl_eq_of_left (Ne.symm h) hj hi
      have hi' : i ∈ insert i (M.erase j) := Finset.mem_insert_self _ _
      have hj' : j ∉ insert i (M.erase j) := by
        simp [Ne.symm h]
      rw [h1, refl_eq_of_left h hi' hj']
      ext x
      simp only [Finset.mem_insert, Finset.mem_erase, Finset.mem_singleton]
      rcases eq_or_ne x j with rfl | hxj
      · simp [hj, Ne.symm h]
      rcases eq_or_ne x i with rfl | hxi
      · simp [hi, hxj]
      · simp [hxi, hxj]
  · have : refl i j M = M := by
      rw [refl, if_neg]
      intro hc
      exact hM ((mem_moved (i := i) (j := j)).2 hc)
    rw [this, this]

/-- `s_ij` preserves `P^mv`. -/
theorem refl_mem_moved {i j : Fin N} (h : i ≠ j) {M : Finset (Fin N)}
    (hM : M ∈ moved i j) : refl i j M ∈ moved i j := by
  rcases (mem_moved_iff h).1 hM with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [refl_eq_of_left h hi hj]
    refine (mem_moved_iff h).2 (Or.inr ⟨by simp [h], Finset.mem_insert_self _ _⟩)
  · rw [refl_comm, refl_eq_of_left (Ne.symm h) hj hi]
    refine (mem_moved_iff h).2 (Or.inl ⟨Finset.mem_insert_self _ _, by simp [Ne.symm h]⟩)

/-- `s_ij` has no fixed point on `P^mv`: every orbit there has size exactly `2`. -/
theorem refl_ne_self {i j : Fin N} (h : i ≠ j) {M : Finset (Fin N)}
    (hM : M ∈ moved i j) : refl i j M ≠ M := by
  rcases (mem_moved_iff h).1 hM with ⟨hi, hj⟩ | ⟨hi, hj⟩
  · rw [refl_eq_of_left h hi hj]
    intro e
    exact hj (e ▸ Finset.mem_insert_self j (M.erase i))
  · rw [refl_comm, refl_eq_of_left (Ne.symm h) hj hi]
    intro e
    exact hi (e ▸ Finset.mem_insert_self i (M.erase j))


/-! ### `lem:colenL` — the order count -/

/-- `#{I : i ∉ I, j ∈ I} = 2^(N-2)`.  Bijection with the powerset of
`univ \ {i,j}`, via `I ↦ I.erase j`. -/
theorem labels_card {i j : Fin N} (h : i ≠ j) :
    (labels i j).card = 2 ^ (N - 2) := by
  have hsub : ({i, j} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
  have hcompl : (Finset.univ \ ({i, j} : Finset (Fin N))).card = N - 2 := by
    rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin,
      Finset.card_pair h]
  have hbij : (labels i j).card = (Finset.univ \ ({i, j} : Finset (Fin N))).powerset.card := by
    refine Finset.card_nbij' (fun I => I.erase j) (fun J => insert j J) ?_ ?_ ?_ ?_
    · intro I hI
      simp only [Finset.mem_coe, mem_labels] at hI
      simp only [Finset.mem_coe, Finset.mem_powerset]
      intro x hx
      rw [Finset.mem_erase] at hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      exact fun hc => hc.elim (fun e => hI.1 (e ▸ hx.2)) (fun e => hx.1 e)
    · intro J hJ
      simp only [Finset.mem_coe, Finset.mem_powerset] at hJ
      simp only [Finset.mem_coe, mem_labels]
      refine ⟨?_, Finset.mem_insert_self _ _⟩
      intro hc
      rcases Finset.mem_insert.1 hc with e | hiJ
      · exact h e
      · have := hJ hiJ
        simp at this
    · intro I hI
      simp only [Finset.mem_coe, mem_labels] at hI
      exact Finset.insert_erase hI.2
    · intro J hJ
      simp only [Finset.mem_coe, Finset.mem_powerset] at hJ
      refine Finset.erase_insert ?_
      intro hc
      have := hJ hc
      simp at this
  rw [hbij, Finset.card_powerset, hcompl]

/-- The paper's `ord Ã_{I,I}` on the `A`-type divisor `{w_i = w_j}`
(`lem:colenL`, eq. after L463): it is the indicator of `i ∉ I ∧ j ∈ I`. -/
def ord (i j : Fin N) (I : Finset (Fin N)) : ℕ :=
  if i ∉ I ∧ j ∈ I then 1 else 0

/-- **Decl 2** (`lem:colenL`, the order count).
`∑_{I ∈ P} ord Ã_{I,I} = #{I : i ∉ I, j ∈ I} = 2^(N-2)`. -/
theorem ord_sum {i j : Fin N} (h : i ≠ j) :
    ∑ I : Finset (Fin N), ord i j I = 2 ^ (N - 2) := by
  have key : ∑ I : Finset (Fin N), ord i j I = (labels i j).card := by
    rw [Finset.card_eq_sum_ones, labels, Finset.sum_filter]
    exact (Finset.sum_congr rfl fun I _ => by simp [ord]).symm
  rw [key, labels_card h]

/-! ### `lem:colenG` — the orbit count -/

/-- The `s_ij`-orbit of `M`, as an unordered pair of points of `P`. -/
def orbit (i j : Fin N) (M : Finset (Fin N)) : Finset (Finset (Fin N)) :=
  {M, refl i j M}

/-- The set of two-element `s_ij`-orbits, i.e. the orbits meeting `P^mv`. -/
def movedOrbits (i j : Fin N) : Finset (Finset (Finset (Fin N))) :=
  (moved i j).image (orbit i j)

theorem orbit_refl {i j : Fin N} (h : i ≠ j) (M : Finset (Fin N)) :
    orbit i j (refl i j M) = orbit i j M := by
  rw [orbit, orbit, refl_involutive h, Finset.pair_comm]

theorem self_mem_orbit (i j : Fin N) (M : Finset (Fin N)) : M ∈ orbit i j M :=
  Finset.mem_insert_self _ _

theorem orbit_card {i j : Fin N} (h : i ≠ j) {M : Finset (Fin N)}
    (hM : M ∈ moved i j) : (orbit i j M).card = 2 :=
  Finset.card_pair (Ne.symm (refl_ne_self h hM))

/-- The fibre of `M ↦ orbit M` over a moved orbit has exactly two members. -/
theorem fiber_card {i j : Fin N} (h : i ≠ j) {o : Finset (Finset (Fin N))}
    (ho : o ∈ movedOrbits i j) :
    ((moved i j).filter (fun M => orbit i j M = o)).card = 2 := by
  rw [movedOrbits, Finset.mem_image] at ho
  obtain ⟨M₀, hM₀, rfl⟩ := ho
  have hset : (moved i j).filter (fun M => orbit i j M = orbit i j M₀)
      = orbit i j M₀ := by
    ext M
    simp only [Finset.mem_filter, orbit, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, he⟩
      have : M ∈ ({M₀, refl i j M₀} : Finset (Finset (Fin N))) := by
        rw [← he]; exact Finset.mem_insert_self _ _
      simpa using this
    · rintro (rfl | rfl)
      · exact ⟨hM₀, rfl⟩
      · exact ⟨refl_mem_moved h hM₀, orbit_refl h M₀⟩
  rw [hset, orbit_card h hM₀]

/-- **Decl 1** (`lem:colenG`, the orbit count).  `s_ij` partitions `P^mv` into
exactly `2^(N-2)` orbits of size two. -/
theorem movedOrbits_card {i j : Fin N} (h : i ≠ j) :
    (movedOrbits i j).card = 2 ^ (N - 2) := by
  have h2 : 2 ≤ N := two_le_of_ne h
  have hmoved : (moved i j).card = 2 ^ (N - 1) := by
    have hun : moved i j = labels i j ∪ labels j i := by
      ext M
      rw [mem_moved_iff h, Finset.mem_union, mem_labels, mem_labels]
      exact ⟨fun hc => hc.elim (fun x => Or.inr ⟨x.2, x.1⟩) (fun x => Or.inl x),
        fun hc => hc.elim (fun x => Or.inr x) (fun x => Or.inl ⟨x.2, x.1⟩)⟩
    have hdisj : Disjoint (labels i j) (labels j i) := by
      rw [Finset.disjoint_left]
      intro M hM hM'
      rw [mem_labels] at hM hM'
      exact hM'.1 hM.2
    rw [hun, Finset.card_union_of_disjoint hdisj, labels_card h, labels_card (Ne.symm h)]
    have : N - 1 = (N - 2) + 1 := by omega
    rw [this, pow_succ]
    omega
  have hfib : (moved i j).card
      = ∑ o ∈ movedOrbits i j, ((moved i j).filter (fun M => orbit i j M = o)).card :=
    Finset.card_eq_sum_card_fiberwise (fun M hM => Finset.mem_image_of_mem _ hM)
  rw [hmoved] at hfib
  rw [Finset.sum_const_nat (m := 2) (fun o ho => fiber_card h ho)] at hfib
  have hNN : (2 : ℕ) ^ (N - 1) = 2 ^ (N - 2) * 2 := by
    have : N - 1 = (N - 2) + 1 := by omega
    rw [this, pow_succ]
  rw [hNN] at hfib
  omega

/-! ### **Decl 3** — the colength match -/

/-- **Decl 3** (Theorem A, the comparison step).  The GKM-side orbit count and
the span-side order count are both `2^(N-2)`, hence equal. -/
theorem colength_match {i j : Fin N} (h : i ≠ j) :
    (movedOrbits i j).card = ∑ I : Finset (Fin N), ord i j I := by
  rw [movedOrbits_card h, ord_sum h]


/-! ### TASK 1 — is the match between the two index sets canonical?

`SUMMARY.md` claimed of Theorem A that the two counts "run over *different index
sets* … and neither is derived from the other, which is the only way the match
carries information."  The paper's own `rem` (L551) is weaker and correct: it
names the bijection and observes only that it *is not used in the proof*.

The `Equiv` below decides between them.  If it type-checks, the index sets are
**canonically isomorphic** and the stronger `SUMMARY.md` phrasing is wrong.

⚠ This does **not** touch Theorem A.  Theorem A equates *colengths of lattices*;
this is a statement about *index sets*.  The theorem stands either way.  What is
at stake is only the epistemic claim about *why* the match is informative. -/

theorem labels_subset_moved {i j : Fin N} (h : i ≠ j) : labels i j ⊆ moved i j := by
  intro I hI
  rw [mem_labels] at hI
  exact (mem_moved_iff h).2 (Or.inr hI)

/-- `s_ij` carries a label out of the label set: it puts `i` back in. -/
theorem mem_refl_of_mem_labels {i j : Fin N} (h : i ≠ j) {I : Finset (Fin N)}
    (hI : I ∈ labels i j) : i ∈ refl i j I := by
  rw [mem_labels] at hI
  rw [refl_comm, refl_eq_of_left (Ne.symm h) hI.2 hI.1]
  exact Finset.mem_insert_self _ _

/-- The other half of a moved orbit, on the `i`-present side, *is* a label. -/
theorem refl_mem_labels {i j : Fin N} (h : i ≠ j) {M : Finset (Fin N)}
    (hi : i ∈ M) (hj : j ∉ M) : refl i j M ∈ labels i j := by
  rw [refl_eq_of_left h hi hj, mem_labels]
  exact ⟨by simp [h], Finset.mem_insert_self _ _⟩

/-- **TASK 1.**  The label set of `lem:colenL` and the set of two-element
`s_ij`-orbits of `lem:colenG` are *canonically* isomorphic, by `I ↦ {I, s I}`.
Each moved orbit contains exactly one member with `i ∉ ·` and `j ∈ ·`. -/
noncomputable def orbitLabelEquiv {i j : Fin N} (h : i ≠ j) :
    {I : Finset (Fin N) // I ∈ labels i j} ≃
      {o : Finset (Finset (Fin N)) // o ∈ movedOrbits i j} :=
  Equiv.ofBijective
    (fun I => ⟨orbit i j I.1,
      Finset.mem_image_of_mem _ (labels_subset_moved h I.2)⟩)
    (by
      constructor
      · rintro ⟨I, hI⟩ ⟨I', hI'⟩ he
        simp only [Subtype.mk.injEq] at he
        have hmem : I ∈ orbit i j I' := by
          rw [← he]; exact self_mem_orbit i j I
        rw [orbit, Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with rfl | hrefl
        · rfl
        · exfalso
          have hi : i ∈ I := hrefl ▸ mem_refl_of_mem_labels h hI'
          exact ((mem_labels).1 hI).1 hi
      · rintro ⟨o, ho⟩
        rw [movedOrbits, Finset.mem_image] at ho
        obtain ⟨M, hM, rfl⟩ := ho
        rcases (mem_moved_iff h).1 hM with ⟨hi, hj⟩ | ⟨hi, hj⟩
        · exact ⟨⟨refl i j M, refl_mem_labels h hi hj⟩, by
            simp only [Subtype.mk.injEq]; exact orbit_refl h M⟩
        · exact ⟨⟨M, (mem_labels).2 ⟨hi, hj⟩⟩, rfl⟩)

/-- Consequence of `orbitLabelEquiv`: the two cardinalities agree **for a
reason**, not merely by both being computed to be `2^(N-2)`.  Proved from the
`Equiv` alone — neither `labels_card` nor `movedOrbits_card` is used. -/
theorem labels_card_eq_movedOrbits_card {i j : Fin N} (h : i ≠ j) :
    (labels i j).card = (movedOrbits i j).card := by
  rw [← Fintype.card_coe (labels i j), ← Fintype.card_coe (movedOrbits i j)]
  exact Fintype.card_congr (orbitLabelEquiv h)

/-! ### TASK 2 — the count depends only on the indicator, hence not on the type -/

/-- `lem:colenL`'s sum depends on the diagonal *only* through the indicator
`[i ∉ I ∧ j ∈ I]`.  Isolating that is what makes `lem:typeB` free. -/
theorem ord_sum_of_indicator {i j : Fin N} (h : i ≠ j) (f : Finset (Fin N) → ℕ)
    (hf : ∀ I, f I = ord i j I) :
    ∑ I : Finset (Fin N), f I = 2 ^ (N - 2) := by
  rw [Finset.sum_congr rfl fun I _ => hf I]
  exact ord_sum h

/-- **`lem:typeB`**, the half of it that is combinatorics.  Given the paper's
type-`B` indicator identity `ord Ã^B_{I,I} = [i ∉ I ∧ j ∈ I]` as input, the
type-`B` sum is the *same* `2^(N-2)`.

What this shows: the **combinatorial skeleton** of `lem:colenL` is
type-independent.  What it does **not** show: that the weight functions are.
The whole type-dependence sits in `2t_k` vs `t_k` (Motegi `normalizationWB`
L1386 vs `normalizationWC` L1078, arXiv:2610.15344).

⚠ A numerical engine once produced a green type-`B` arm while normalising type
`B` by `E^C` — a shared wrong premise, invisible to the control.  Lean cannot
repeat that here, and the *reason* is worth stating: `ord` contains no
normaliser at all.  So this corollary is evidence about the indicator and
about nothing else; it must not be read as evidence about the weight
functions. -/
theorem ord_sum_typeB {i j : Fin N} (h : i ≠ j) (ordB : Finset (Fin N) → ℕ)
    (hordB : ∀ I, ordB I = if i ∉ I ∧ j ∈ I then 1 else 0) :
    ∑ I : Finset (Fin N), ordB I = 2 ^ (N - 2) :=
  ord_sum_of_indicator h ordB hordB

/-! ### Lesions

Each hypothesis is lesioned once, and the lesion is graded by **proving the
negation of the lesioned statement at a named instance** — not by deleting the
binder and watching the script fail with `Unknown identifier`, which grades the
script rather than the statement. -/

namespace Lesion

/-- `i ≠ j` is **irremovable** from `two_le_of_ne`: `Fin 1` is inhabited. -/
theorem two_le_lesion_fails : ∃ _i _j : Fin 1, ¬ (2 ≤ 1) := ⟨0, 0, by omega⟩

/-- `i ≠ j` is **irremovable** from `mem_moved_iff`: at `i = j` the right-hand
side is unsatisfiable while the left-hand side is not. -/
theorem mem_moved_iff_lesion_fails :
    ({0} : Finset (Fin 2)) ∈ moved (0 : Fin 2) 0 ∧
      ¬ (((0 : Fin 2) ∈ ({0} : Finset (Fin 2)) ∧ (0 : Fin 2) ∉ ({0} : Finset (Fin 2))) ∨
         ((0 : Fin 2) ∉ ({0} : Finset (Fin 2)) ∧ (0 : Fin 2) ∈ ({0} : Finset (Fin 2)))) := by
  constructor
  · decide
  · decide

/-- `i ≠ j` is **irremovable** from `labels_card`: at `i = j` the label set is
empty, so the count is `0`, not `2^(N-2) = 1`. -/
theorem labels_card_lesion_fails : (labels (0 : Fin 2) 0).card ≠ 2 ^ (2 - 2) := by
  decide

/-- `i ≠ j` is **irremovable** from `ord_sum`. -/
theorem ord_sum_lesion_fails :
    (∑ I : Finset (Fin 2), ord (0 : Fin 2) 0 I) ≠ 2 ^ (2 - 2) := by
  decide

/-- `i ≠ j` is **irremovable** from `movedOrbits_card`: at `i = j` the map
`M ↦ M.erase i` is injective on the moved locus, so there are `2^(N-1)` orbits,
not `2^(N-2)`. -/
theorem movedOrbits_card_lesion_fails :
    (movedOrbits (0 : Fin 2) 0).card ≠ 2 ^ (2 - 2) := by
  decide

/-- `i ≠ j` is **irremovable** from `refl_involutive`: at `i = j` the map is
`M ↦ M.erase i` on the moved locus, which is not an involution. -/
theorem refl_involutive_lesion_fails :
    refl (0 : Fin 2) 0 (refl (0 : Fin 2) 0 {0}) ≠ ({0} : Finset (Fin 2)) := by
  decide

end Lesion

/-- The free strengthening the lesion sweep bought: `i ≠ j` is **removable**
from `refl_ne_self`.  `symmDiff M T = M` forces `T = ∅`, and `{i,j}` is never
empty — so no point of `P^mv` is fixed, for *any* `i, j`, including `i = j`.

This is the sharp half of the pair: the binder is irremovable from
`refl_involutive` (see `Lesion.refl_involutive_lesion_fails`) and removable
here, and neither half is visible from the other. -/
theorem refl_ne_self_of_mem_moved (i j : Fin N) {M : Finset (Fin N)}
    (hM : M ∈ moved i j) : refl i j M ≠ M := by
  rw [mem_moved] at hM
  rw [refl, if_pos hM]
  intro e
  have hiff : i ∈ symmDiff M ({i, j} : Finset (Fin N)) ↔ i ∉ M := by
    simp [Finset.mem_symmDiff]
  rw [e] at hiff
  simp at hiff

end AtypeColength
