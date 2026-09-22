/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.RobinHood

/-!
# The weight set of a cylindric skew shape is a dominance order ideal

Formalisation of the **order-theoretic core** of Proposition `prop:ideal` of
`projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex` (lines 461-476):

> `P(W_ℓ(λ/μ))` is an order ideal of the dominance order on partitions of `d` with at
> most `ℓ` parts.

## What is and is not formalised here

The paper's proof consumes two combinatorial facts about the periodic-Maya bead-chain
model, which are **not** formalised — they appear as explicit hypotheses:

* `hperm` stands for Corollary `cor:bk` (`W_ℓ` is `S_ℓ`-stable, via the cylindric
  Bender-Knuth involution).  It is stated on transpositions `Equiv.swap i j` with
  `i, j < ℓ`, which generate `S_ℓ`; that is both the weakest form and the form the
  proof uses.
* `hexch` stands for Corollary `cor:exchange` (a bead slides one site): if a coordinate
  strictly exceeds its right neighbour, one unit may be moved right.

Everything else is proved.  The engine is `RobinHood.robin_hood_step` (Lemma `lem:hlp`,
machine-checked in `RobinHood.lean`).

## The terminating measure

The paper's proof says "by induction on the (finite) number of steps" and never names
the measure.  Lean does not accept that.  The measure is

  `gap ℓ σ ν = ∑_{r < ℓ} (psum ν r − psum σ r)`,

the total area between the two partial-sum profiles.  It is `≥ 0` exactly when
`σ ⊴ ν` (`gap_nonneg`), and a Robin Hood step `ν ↦ ν − e_a + e_b` with `a < b < ℓ`
drops it strictly, because the profile falls by one unit on the window `(a, b]` and
`r = b` is in range (`gap_lt`).  So the induction is on `(gap ℓ σ ν).toNat`.

This is the measure suggested by the `prop:ideal` brief; it is confirmed here, and the
key point the brief flagged as unchecked is the side condition `b < ℓ`, which is *not*
a conclusion of `robin_hood_step` and has to be recovered from the size equation
(`exch_snd_lt` below).

## What the proof consumes

`ν ∈ W` is used once (the base case, `σ = ν`).  `hperm` is used twice per step (once to
make `ν_a` and `ν_b` adjacent, once to undo that) and `hexch` once.  The size and
non-negativity conditions on `W` itself (every `β ∈ W` has `∑ β = d`, `β ≥ 0`) are
**not** consumed: the relevant instances are carried by `IsPart` and by the theorem's
own `psum σ ℓ = psum ν ℓ` hypothesis, so they are not assumed.  See the negative
control in the `Control` section for evidence that `hexch` *is* load-bearing.
-/

namespace RobinHood

open Finset

variable {ℓ : ℕ} {W : Set (ℕ → ℤ)}

/-! ### The terminating measure -/

/-- `gap ℓ σ ν` is the area between the partial-sum profiles of `ν` and `σ` over
`r < ℓ`.  This is the measure on which the induction in `prop:ideal` terminates. -/
def gap (ℓ : ℕ) (σ ν : ℕ → ℤ) : ℤ := ∑ r ∈ Finset.range ℓ, (psum ν r - psum σ r)

lemma gap_nonneg {σ ν : ℕ → ℤ} (h : Dom σ ν) : 0 ≤ gap ℓ σ ν :=
  Finset.sum_nonneg fun r _ => by have := h r; omega

/-- A Robin Hood step strictly drops the measure.  The witness is `r = b`: the profile
of `ν - e_a + e_b` falls by one unit on the window `(a, b]`, and `b` is in range. -/
lemma gap_lt {σ ν : ℕ → ℤ} {a b : ℕ} (hab : a < b) (hbℓ : b < ℓ)
    (hτν : Dom (ex a b ν) ν) : gap ℓ σ (ex a b ν) < gap ℓ σ ν := by
  apply Finset.sum_lt_sum
  · intro r _
    have := hτν r
    omega
  · refine ⟨b, Finset.mem_range.mpr hbℓ, ?_⟩
    have hb : psum (ex a b ν) b = psum ν b - 1 := by
      rw [psum_ex, if_pos hab, if_neg (lt_irrefl b)]; ring
    omega

/-- The second index of a Robin Hood step is inside the window.  `b < ℓ` is **not** a
conclusion of `robin_hood_step`; it has to be recovered, and the size equation is what
recovers it.  (`a < ℓ` because `ν a ≥ ν b + 2 ≥ 2 > 0`, and then the size equation
forces `b < ℓ` too.) -/
lemma exch_snd_lt {ν : ℕ → ℤ} (hν : IsPart ℓ ν) {a b : ℕ}
    (h2 : ν b + 2 ≤ ν a) (hsz : psum (ex a b ν) ℓ = psum ν ℓ) : b < ℓ := by
  have hbnn : 0 ≤ ν b := hν.nonneg b
  have haℓ : a < ℓ := by
    by_contra h
    rw [hν.2 a (by omega)] at h2
    omega
  rw [psum_ex, if_pos haℓ] at hsz
  by_contra h
  rw [if_neg h] at hsz
  omega

/-! ### The sorting bridge

The one genuinely new step: `hperm` plus `hexch` give the Robin Hood move on
*partitions*, for arbitrary `a < b`, not just adjacent indices.

The paper argues: `S_ℓ`-stability puts a vector `β ∈ W` with `β_t = ν_a` and
`β_{t+1} = ν_b` into `W`, the exchange corollary slides a unit, and the result sorts to
`τ = ν - e_a + e_b`.  Rather than construct a sorting function, the proof below
exhibits the sorting permutation explicitly, and the whole argument collapses to a
single pointwise identity:

  `ex a (a+1) (ν ∘ swap (a+1) b) = (ex a b ν) ∘ swap (a+1) b`.

That is, the near-exchange applied to the twisted vector *is* the far exchange,
twisted.  Since `swap` is an involution, one more application of `hperm` untwists it.
-/

/-- **The far Robin Hood move stays in `W`.**  If `ν ∈ W` and `a < b < ℓ` with
`ν a ≥ ν b + 2`, then `ν - e_a + e_b ∈ W`.

This is the body of the proof of `prop:ideal`: `hperm` (= `cor:bk`) makes positions `a`
and `b` adjacent, `hexch` (= `cor:exchange`) slides one unit across that adjacency, and
`hperm` again undoes the rearrangement. -/
lemma far_exchange_mem
    (hperm : ∀ β ∈ W, ∀ i j : ℕ, i < ℓ → j < ℓ → β ∘ Equiv.swap i j ∈ W)
    (hexch : ∀ β ∈ W, ∀ t : ℕ, t + 1 < ℓ → β (t + 1) < β t → ex t (t + 1) β ∈ W)
    {ν : ℕ → ℤ} (hν : ν ∈ W) {a b : ℕ} (hab : a < b) (hbℓ : b < ℓ)
    (h2 : ν b + 2 ≤ ν a) : ex a b ν ∈ W := by
  classical
  have ha1ℓ : a + 1 < ℓ := by omega
  set π : Equiv.Perm ℕ := Equiv.swap (a + 1) b with hπdef
  have hinv : ∀ c, π (π c) = c := fun c => Equiv.swap_apply_self _ _ c
  have hπa : π a = a := Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  have hπa1 : π (a + 1) = b := Equiv.swap_apply_left _ _
  have hπb : π b = a + 1 := Equiv.swap_apply_right _ _
  -- `β = ν ∘ π` has `β a = ν a` and `β (a+1) = ν b`, so `a` and `a+1` is a descent.
  have hβ : ν ∘ π ∈ W := hperm ν hν (a + 1) b ha1ℓ hbℓ
  have hlt : (ν ∘ π) (a + 1) < (ν ∘ π) a := by
    simp only [Function.comp_apply, hπa, hπa1]
    omega
  have hγ : ex a (a + 1) (ν ∘ π) ∈ W := hexch _ hβ a ha1ℓ hlt
  -- The near exchange on the twisted vector is the far exchange, twisted.
  have hkey : ex a (a + 1) (ν ∘ π) = (ex a b ν) ∘ π := by
    funext c
    -- The two `if` conditions on the right agree with those on the left, because `π`
    -- is an involution fixing `a` and swapping `a+1` with `b`.
    have e1 : (π c = a) = (c = a) := by
      refine propext ⟨fun h => ?_, fun h => ?_⟩
      · have hc := hinv c; rw [h, hπa] at hc; exact hc.symm
      · rw [h, hπa]
    have e2 : (π c = b) = (c = a + 1) := by
      refine propext ⟨fun h => ?_, fun h => ?_⟩
      · have hc := hinv c; rw [h, hπb] at hc; exact hc.symm
      · rw [h, hπa1]
    simp only [ex, Function.comp_apply, e1, e2]
  rw [hkey] at hγ
  have huntwist := hperm _ hγ (a + 1) b ha1ℓ hbℓ
  have hff : ((ex a b ν) ∘ π) ∘ π = ex a b ν := by
    funext c
    simp only [Function.comp_apply, hinv c]
  rwa [hff] at huntwist

/-! ### The order ideal -/

/-- **Proposition `prop:ideal`, order-theoretic core.**

Let `W ⊆ ℤ^ℕ` be stable under transpositions of the first `ℓ` coordinates (`hperm`,
standing for `cor:bk`) and under sliding one unit rightwards across a descent
(`hexch`, standing for `cor:exchange`).  Then the set of partitions lying in `W` is an
order ideal of the dominance order: if `ν ∈ W` is a partition with at most `ℓ` parts
and `σ ⊴ ν` is a partition of the same size with at most `ℓ` parts, then `σ ∈ W`.

The paper's `P(W_ℓ)` — the set of *sorted* elements of `W` — coincides with
`{ν ∈ W | IsPart ℓ ν}`, because `W` is `S_ℓ`-stable: the sorted rearrangement of any
`β ∈ W` is again in `W`.  So no sorting function is needed to state the result.

Cites `2026-09-20-c1-cylindric-M-convexity.tex`, Prop. `prop:ideal` (lines 461-476);
the engine is Lemma `lem:hlp` = `RobinHood.robin_hood_step` (lines 440-459). -/
theorem dominance_ideal
    (hperm : ∀ β ∈ W, ∀ i j : ℕ, i < ℓ → j < ℓ → β ∘ Equiv.swap i j ∈ W)
    (hexch : ∀ β ∈ W, ∀ t : ℕ, t + 1 < ℓ → β (t + 1) < β t → ex t (t + 1) β ∈ W)
    {ν σ : ℕ → ℤ} (hν : ν ∈ W) (hpν : IsPart ℓ ν) (hpσ : IsPart ℓ σ)
    (hsize : psum σ ℓ = psum ν ℓ) (hdom : Dom σ ν) : σ ∈ W := by
  classical
  -- Strong induction on the terminating measure `(gap ℓ σ ν).toNat`.
  suffices H : ∀ n : ℕ, ∀ ν' : ℕ → ℤ, ν' ∈ W → IsPart ℓ ν' → psum σ ℓ = psum ν' ℓ →
      Dom σ ν' → (gap ℓ σ ν').toNat = n → σ ∈ W by
    exact H _ ν hν hpν hsize hdom rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ν' hν' hpν' hsize' hdom' hg
    by_cases hEq : σ = ν'
    · exact hEq ▸ hν'
    obtain ⟨a, b, hab, h2, hpτ, hsz, hdomστ, hdomτν, -⟩ :=
      robin_hood_step hpν' hpσ hsize' hdom' hEq
    have hbℓ : b < ℓ := exch_snd_lt hpν' h2 hsz
    have hτW : ex a b ν' ∈ W := far_exchange_mem hperm hexch hν' hab hbℓ h2
    have hdrop : gap ℓ σ (ex a b ν') < gap ℓ σ ν' := gap_lt hab hbℓ hdomτν
    have h0τ : 0 ≤ gap ℓ σ (ex a b ν') := gap_nonneg hdomστ
    have h0ν : 0 ≤ gap ℓ σ ν' := gap_nonneg hdom'
    refine ih (gap ℓ σ (ex a b ν')).toNat ?_ _ hτW hpτ (hsize'.trans hsz.symm) hdomστ rfl
    subst hg
    omega

/-! ### Control

Two guards against the theorem being true for the wrong reason.

**Satisfiability.** `W = Set.univ` satisfies `hperm` and `hexch`, so the hypotheses are
not contradictory (`hyps_satisfiable`).  On its own that is a weak guard: the conclusion
`σ ∈ Set.univ` is free.

**`hexch` is load-bearing.** The sharper guard is a `W` for which everything *except*
`hexch` holds and the conclusion *fails*: the `S_2`-orbit `W₀ = {(3,1), (1,3)}`.  It is
transposition-stable, contains the partition `ν = (3,1)`, and `σ = (2,2)` is a partition
of the same size `4` with `σ ⊴ ν` — yet `σ ∉ W₀`.  So `dominance_ideal` genuinely
consumes `cor:exchange`; it is not an order-theoretic fact about `S_ℓ`-stable sets. -/
section Control

/-- The hypotheses of `dominance_ideal` are satisfiable. -/
lemma hyps_satisfiable (ℓ : ℕ) :
    (∀ β ∈ (Set.univ : Set (ℕ → ℤ)), ∀ i j : ℕ, i < ℓ → j < ℓ →
        β ∘ Equiv.swap i j ∈ (Set.univ : Set (ℕ → ℤ))) ∧
    (∀ β ∈ (Set.univ : Set (ℕ → ℤ)), ∀ t : ℕ, t + 1 < ℓ → β (t + 1) < β t →
        ex t (t + 1) β ∈ (Set.univ : Set (ℕ → ℤ))) :=
  ⟨fun _ _ _ _ _ _ => Set.mem_univ _, fun _ _ _ _ _ => Set.mem_univ _⟩

/-- `ν = (3,1)`. -/
def p31 : ℕ → ℤ := fun c => if c = 0 then 3 else if c = 1 then 1 else 0
/-- `σ = (2,2)`. -/
def p22 : ℕ → ℤ := fun c => if c = 0 then 2 else if c = 1 then 2 else 0

/-- The `S_2`-orbit of `(3,1)`, i.e. `{(3,1), (1,3)}`. -/
def orbit31 : Set (ℕ → ℤ) :=
  {β | ∃ π : Equiv.Perm ℕ, (∀ c, 2 ≤ c → π c = c) ∧ β = p31 ∘ π}

lemma p31_vanish : ∀ c, 2 ≤ c → p31 c = 0 := by
  intro c hc; simp only [p31]; split_ifs <;> omega

lemma p22_vanish : ∀ c, 2 ≤ c → p22 c = 0 := by
  intro c hc; simp only [p22]; split_ifs <;> omega

lemma p31_isPart : IsPart 2 p31 := by
  refine ⟨?_, p31_vanish⟩
  apply antitone_nat_of_succ_le
  intro c
  simp only [p31]
  split_ifs <;> first | (exfalso; assumption) | omega

lemma p22_isPart : IsPart 2 p22 := by
  refine ⟨?_, p22_vanish⟩
  apply antitone_nat_of_succ_le
  intro c
  simp only [p22]
  split_ifs <;> first | (exfalso; assumption) | omega

lemma psum_p31 : psum p31 0 = 0 ∧ psum p31 1 = 3 ∧ psum p31 2 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [psum, Finset.sum_range_succ, Finset.sum_range_zero, p31] <;> norm_num

lemma psum_p22 : psum p22 0 = 0 ∧ psum p22 1 = 2 ∧ psum p22 2 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [psum, Finset.sum_range_succ, Finset.sum_range_zero, p22] <;> norm_num

/-- **`hexch` is load-bearing in `dominance_ideal`.**  Every hypothesis of
`dominance_ideal` except `hexch` holds for `W₀ = orbit31` with `ν = (3,1)`,
`σ = (2,2)`, `ℓ = 2` — and the conclusion `σ ∈ W₀` is false. -/
theorem hexch_load_bearing :
    (∀ β ∈ orbit31, ∀ i j : ℕ, i < 2 → j < 2 → β ∘ Equiv.swap i j ∈ orbit31) ∧
    p31 ∈ orbit31 ∧ IsPart 2 p31 ∧ IsPart 2 p22 ∧
    psum p22 2 = psum p31 2 ∧ Dom p22 p31 ∧ p22 ∉ orbit31 := by
  classical
  obtain ⟨n0, n1, n2⟩ := psum_p31
  obtain ⟨s0, s1, s2⟩ := psum_p22
  refine ⟨?_, ⟨Equiv.refl ℕ, fun c _ => rfl, rfl⟩, p31_isPart, p22_isPart, by omega, ?_, ?_⟩
  · -- transposition-stability of the orbit
    rintro β ⟨π, hs, rfl⟩ i j hi hj
    refine ⟨(Equiv.swap i j).trans π, ?_, ?_⟩
    · intro c hc
      rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]
      exact hs c hc
    · funext c; rfl
  · -- `(2,2) ⊴ (3,1)`
    intro r
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · rw [psum_stab p22_vanish r h, psum_stab p31_vanish r h]; omega
  · -- `(2,2)` is not in the orbit: every entry of `p31` is `0`, `1` or `3`, never `2`.
    rintro ⟨π, -, he⟩
    have h0 := congrFun he 0
    have hv : p31 (π 0) = 0 ∨ p31 (π 0) = 1 ∨ p31 (π 0) = 3 := by
      simp only [p31]; split_ifs <;> omega
    simp only [p22, Function.comp_apply, if_pos] at h0
    omega

end Control

end RobinHood
