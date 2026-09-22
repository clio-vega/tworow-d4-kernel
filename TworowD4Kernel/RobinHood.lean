/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# The Robin Hood step for the dominance order on partitions

Formalisation of Lemma `lem:hlp` of
`projects/proofs/2026-09-20-c1-cylindric-M-convexity.tex` (§"The weight set is a
dominance ideal"), which reads, verbatim:

> Let `ν ▷ σ` be partitions of `d`. Then there are indices `a < b` with `ν_a ≥ ν_b + 2`
> such that `τ := ν − e_a + e_b` is again a partition and `ν ▷ τ ⊵ σ`.

## Representation

A partition with at most `ℓ` parts is an `Antitone` function `ν : ℕ → ℤ` with `ν c = 0`
for `c ≥ ℓ` (`IsPart`).  Three reasons, all about making the *statement* cheap:

* **`ℤ`, not `ℕ`**: the surgery `ν - e_a + e_b` appears in the statement, not merely in
  the proof, and truncated `ℕ` subtraction would force a side condition at every use.
* **indexed by `ℕ`, not `Fin ℓ`**: the proof manipulates `a + 1` and `b - 1` and the
  interval `Ico i j`; `Fin` coercions would dominate the proof script.
* **antitone + eventually zero**: non-negativity is then a *lemma* (`IsPart.nonneg`),
  not a hypothesis, and the partial sums are literally `∑ c ∈ Finset.range r, ν c`.

Note that indices here are **0-based**, whereas the paper is 1-based; the paper's
`N_r = ν_1 + ⋯ + ν_r` is `psum ν r`.
-/

namespace RobinHood

open Finset

/-- `ν` is a partition with at most `ℓ` parts: antitone, and zero from index `ℓ` on. -/
def IsPart (ℓ : ℕ) (ν : ℕ → ℤ) : Prop := Antitone ν ∧ ∀ c, ℓ ≤ c → ν c = 0

/-- `psum ν r = ν 0 + ⋯ + ν (r-1)`; the paper's `N_r`. -/
def psum (ν : ℕ → ℤ) (r : ℕ) : ℤ := ∑ c ∈ Finset.range r, ν c

/-- Dominance order: `Dom σ ν` is the paper's `σ ⊴ ν` (for partitions of equal size). -/
def Dom (σ ν : ℕ → ℤ) : Prop := ∀ r, psum σ r ≤ psum ν r

/-- The Robin Hood surgery `ν - e_a + e_b`. -/
def ex (a b : ℕ) (ν : ℕ → ℤ) : ℕ → ℤ :=
  fun c => ν c - (if c = a then 1 else 0) + (if c = b then 1 else 0)

lemma IsPart.nonneg {ℓ : ℕ} {ν : ℕ → ℤ} (h : IsPart ℓ ν) (c : ℕ) : 0 ≤ ν c := by
  have hle : ν (max c ℓ) ≤ ν c := h.1 (le_max_left c ℓ)
  rwa [h.2 _ (le_max_right c ℓ)] at hle

lemma psum_succ (ν : ℕ → ℤ) (r : ℕ) : psum ν (r + 1) = psum ν r + ν r :=
  Finset.sum_range_succ _ _

lemma psum_split (ν : ℕ → ℤ) {m n : ℕ} (h : m ≤ n) :
    psum ν n = psum ν m + ∑ c ∈ Finset.Ico m n, ν c :=
  (Finset.sum_range_add_sum_Ico ν h).symm

/-- Partial sums of the surgered vector: one unit is removed on the window `(a, b]`. -/
lemma psum_ex (a b : ℕ) (ν : ℕ → ℤ) (r : ℕ) :
    psum (ex a b ν) r
      = psum ν r - (if a < r then 1 else 0) + (if b < r then 1 else 0) := by
  induction r with
  | zero => simp [psum]
  | succ n ih =>
    rw [psum, psum, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [psum, psum] at ih
    simp only [ex] at *
    split_ifs at * <;> omega

/-- **Robin Hood step** (Lemma `lem:hlp`).  If `σ ⊴ ν`, `σ ≠ ν` are partitions of the
same size with at most `ℓ` parts, there are `a < b` with `ν b + 2 ≤ ν a` such that
`τ = ν - e_a + e_b` is again such a partition, of the same size, with `σ ⊴ τ ⊴ ν`
and `τ ≠ ν`. -/
theorem robin_hood_step {ℓ : ℕ} {ν σ : ℕ → ℤ}
    (hν : IsPart ℓ ν) (hσ : IsPart ℓ σ)
    (hsize : psum σ ℓ = psum ν ℓ) (hdom : Dom σ ν) (hne : σ ≠ ν) :
    ∃ a b : ℕ, a < b ∧ ν b + 2 ≤ ν a ∧
      IsPart ℓ (ex a b ν) ∧ psum (ex a b ν) ℓ = psum ν ℓ ∧
      Dom σ (ex a b ν) ∧ Dom (ex a b ν) ν ∧ ex a b ν ≠ ν := by
  classical
  -- `i`: the first index at which `ν` overtakes `σ`.
  have hexi : ∃ c, σ c < ν c := by
    by_contra hcon
    push_neg at hcon
    apply hne
    have hps : ∀ r, psum σ r = psum ν r := fun r =>
      le_antisymm (hdom r) (Finset.sum_le_sum fun c _ => hcon c)
    funext c
    have h1 := hps (c + 1)
    have h2 := hps c
    rw [psum_succ, psum_succ] at h1
    omega
  set i := Nat.find hexi with hi_def
  have hi : σ i < ν i := Nat.find_spec hexi
  have himin : ∀ c, c < i → ν c ≤ σ c := fun c hc => not_lt.mp (Nat.find_min hexi hc)
  have hpi : psum σ i = psum ν i :=
    le_antisymm (hdom i) (Finset.sum_le_sum fun c hc => himin c (Finset.mem_range.mp hc))
  have hiℓ : i < ℓ := by
    by_contra h
    push_neg at h
    rw [hν.2 i h, hσ.2 i h] at hi
    omega
  -- `j`: the first index after `i` at which `σ` overtakes `ν`.
  have hexj : ∃ c, i < c ∧ ν c < σ c := by
    by_contra hcon
    push_neg at hcon
    have h1 : psum σ (i + 1) < psum ν (i + 1) := by
      rw [psum_succ, psum_succ]; omega
    have h2 : ∑ c ∈ Finset.Ico (i + 1) ℓ, σ c ≤ ∑ c ∈ Finset.Ico (i + 1) ℓ, ν c :=
      Finset.sum_le_sum fun c hc => hcon c (by have := Finset.mem_Ico.mp hc; omega)
    have e1 := psum_split ν (show i + 1 ≤ ℓ by omega)
    have e2 := psum_split σ (show i + 1 ≤ ℓ by omega)
    omega
  set j := Nat.find hexj with hj_def
  have hj : i < j ∧ ν j < σ j := Nat.find_spec hexj
  have hjmin : ∀ c, i < c → c < j → σ c ≤ ν c := fun c hc1 hc2 =>
    not_lt.mp (fun h => Nat.find_min hexj hc2 ⟨hc1, h⟩)
  have hjℓ : j < ℓ := by
    by_contra h
    push_neg at h
    rw [hν.2 j h, hσ.2 j h] at hj
    omega
  -- `ν i ≥ ν j + 2`, since `ν i > σ i ≥ σ j > ν j`.
  have hij2 : ν j + 2 ≤ ν i := by
    have : σ j ≤ σ i := hσ.1 (le_of_lt hj.1)
    omega
  -- The partial-sum claim: `psum σ r < psum ν r` for `i < r ≤ j`.
  have claim : ∀ r, i < r → r ≤ j → psum σ r + 1 ≤ psum ν r := by
    intro r hr1 hr2
    have h1 : psum σ (i + 1) + 1 ≤ psum ν (i + 1) := by
      rw [psum_succ, psum_succ]; omega
    have h2 : ∑ c ∈ Finset.Ico (i + 1) r, σ c ≤ ∑ c ∈ Finset.Ico (i + 1) r, ν c :=
      Finset.sum_le_sum fun c hc => by
        have := Finset.mem_Ico.mp hc
        exact hjmin c (by omega) (by omega)
    have e1 := psum_split ν (show i + 1 ≤ r by omega)
    have e2 := psum_split σ (show i + 1 ≤ r by omega)
    omega
  -- `b`: the first index after `i` where `ν` has already dropped to its value at `j`.
  have hexb : ∃ c, i < c ∧ ν c = ν j := ⟨j, hj.1, rfl⟩
  set b := Nat.find hexb with hb_def
  have hb : i < b ∧ ν b = ν j := Nat.find_spec hexb
  have hbj : b ≤ j := Nat.find_le ⟨hj.1, rfl⟩
  have hbprev : ν b < ν (b - 1) := by
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hb.1) with h | h
    · -- `b = i + 1`
      have : b - 1 = i := by omega
      rw [this]; omega
    · have hne' : ν (b - 1) ≠ ν j := fun hq =>
        Nat.find_min hexb (show b - 1 < b by omega) ⟨by omega, hq⟩
      have hle : ν b ≤ ν (b - 1) := hν.1 (by omega)
      omega
  -- `a`: the last index before `j` where `ν` still equals its value at `i`.
  have hane : ((Finset.Ico i j).filter (fun c => ν c = ν i)).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨le_refl i, hj.1⟩, rfl⟩⟩
  set a := ((Finset.Ico i j).filter (fun c => ν c = ν i)).max' hane with ha_def
  have hamem : a ∈ (Finset.Ico i j).filter (fun c => ν c = ν i) := Finset.max'_mem _ hane
  have haIco : i ≤ a ∧ a < j := Finset.mem_Ico.mp (Finset.mem_filter.mp hamem).1
  have hava : ν a = ν i := (Finset.mem_filter.mp hamem).2
  have hanext : ν (a + 1) < ν a := by
    have hle : ν (a + 1) ≤ ν a := hν.1 (Nat.le_succ a)
    rcases Nat.lt_or_ge (a + 1) j with h | h
    · rcases eq_or_lt_of_le hle with heq | hlt
      · exfalso
        have hmem : a + 1 ∈ (Finset.Ico i j).filter (fun c => ν c = ν i) :=
          Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, h⟩, by omega⟩
        have := Finset.le_max' _ _ hmem
        omega
      · exact hlt
    · -- `a + 1 = j`
      have he : a + 1 = j := by omega
      have : ν (a + 1) = ν j := by rw [he]
      omega
  have hab : a < b := by
    by_contra h
    push_neg at h
    have := hν.1 h
    omega
  have hab2 : ν b + 2 ≤ ν a := by omega
  have haℓ : a < ℓ := by omega
  have hbℓ : b < ℓ := by omega
  refine ⟨a, b, hab, hab2, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · -- `ex a b ν` is antitone
    apply antitone_nat_of_succ_le
    intro c
    have hstep : ν (c + 1) ≤ ν c := hν.1 (Nat.le_succ c)
    simp only [ex]
    rcases eq_or_ne c a with rfl | hca
    · -- the `rfl` case replaced `c` by `a` throughout
      have h1 : ν (a + 1) ≤ ν a - 1 := by omega
      rcases eq_or_ne (a + 1) b with hcb | hcb
      · have h2 : ν (a + 1) = ν b := by rw [hcb]
        rw [if_pos hcb, if_neg (show a + 1 ≠ a by omega), if_pos rfl,
          if_neg (show a ≠ b by omega)]
        omega
      · rw [if_neg hcb, if_neg (show a + 1 ≠ a by omega), if_pos rfl,
          if_neg (show a ≠ b by omega)]
        omega
    · rcases eq_or_ne (c + 1) b with hcb | hcb
      · have e1 : ν (c + 1) = ν b := by rw [hcb]
        have e2 : ν c = ν (b - 1) := by congr 1; omega
        rw [if_pos hcb, if_neg (show c + 1 ≠ a by omega), if_neg hca,
          if_neg (show c ≠ b by omega)]
        omega
      · rw [if_neg hcb, if_neg hca]
        split_ifs <;> omega
  · -- `ex a b ν` vanishes from `ℓ` on
    intro c hc
    simp only [ex, if_neg (show c ≠ a by omega), if_neg (show c ≠ b by omega)]
    simpa using hν.2 c hc
  · -- same size
    rw [psum_ex, if_pos haℓ, if_pos hbℓ]; ring
  · -- `σ ⊴ ex a b ν`
    intro r
    rw [psum_ex]
    by_cases hbr : b < r
    · rw [if_pos hbr, if_pos (show a < r by omega)]
      have := hdom r; omega
    · rw [if_neg hbr]
      by_cases har : a < r
      · rw [if_pos har]
        have := claim r (by omega) (by omega)
        omega
      · rw [if_neg har]
        have := hdom r; omega
  · -- `ex a b ν ⊴ ν`
    intro r
    rw [psum_ex]
    by_cases hbr : b < r
    · rw [if_pos hbr, if_pos (show a < r by omega)]; omega
    · rw [if_neg hbr]; split_ifs <;> omega
  · -- strictness: `ex a b ν` differs from `ν` at `a`
    intro h
    have h2 := congrFun h a
    have e1 : ex a b ν a = ν a - 1 := by
      simp only [ex]
      split_ifs <;> omega
    rw [e1] at h2
    omega

/-! ### Non-vacuity

The hypotheses of `robin_hood_step` are satisfiable: `ν = (3,1)` dominates `σ = (2,2)`,
both partitions of `4` with at most `2` parts.  Without a witness a universally
quantified statement can be true because it is empty, so this is the guard against the
Lean statement having drifted away from `lem:hlp`. -/
section Witness

/-- Partial sums stabilise past the length bound. -/
lemma psum_stab {f : ℕ → ℤ} {ℓ : ℕ} (hf : ∀ c, ℓ ≤ c → f c = 0) :
    ∀ r, ℓ ≤ r → psum f r = psum f ℓ := by
  intro r hr
  induction r with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_or_ge n ℓ with h | h
    · have hn : n + 1 = ℓ := by omega
      rw [hn]
    · rw [psum_succ, ih h, hf n h, add_zero]

private def nu3 : ℕ → ℤ := fun c => if c = 0 then 3 else if c = 1 then 1 else 0
private def si22 : ℕ → ℤ := fun c => if c = 0 then 2 else if c = 1 then 2 else 0

private lemma nu3_vanish : ∀ c, 2 ≤ c → nu3 c = 0 := by
  intro c hc; simp only [nu3]; split_ifs <;> omega

private lemma si22_vanish : ∀ c, 2 ≤ c → si22 c = 0 := by
  intro c hc; simp only [si22]; split_ifs <;> omega

private lemma nu3_anti : Antitone nu3 := by
  apply antitone_nat_of_succ_le
  intro c
  simp only [nu3]
  -- `split_ifs` leaves a `False` hypothesis in the branches where the simproc had
  -- already decided `c + 1 = 0`; `omega` ignores `False`, so discharge those first.
  split_ifs <;> first | (exfalso; assumption) | omega

private lemma si22_anti : Antitone si22 := by
  apply antitone_nat_of_succ_le
  intro c
  simp only [si22]
  -- `split_ifs` leaves a `False` hypothesis in the branches where the simproc had
  -- already decided `c + 1 = 0`; `omega` ignores `False`, so discharge those first.
  split_ifs <;> first | (exfalso; assumption) | omega

private lemma psum_nu3 : psum nu3 0 = 0 ∧ psum nu3 1 = 3 ∧ psum nu3 2 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [psum, Finset.sum_range_succ, Finset.sum_range_zero, nu3] <;> norm_num

private lemma psum_si22 : psum si22 0 = 0 ∧ psum si22 1 = 2 ∧ psum si22 2 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [psum, Finset.sum_range_succ, Finset.sum_range_zero, si22] <;> norm_num

/-- The hypotheses of `robin_hood_step` are satisfiable: `ν = (3,1) ▷ σ = (2,2)`, both
partitions of `4` with at most `2` parts.  Without a witness a universally quantified
statement can be true because it is empty; this is the guard against the Lean statement
having drifted away from `lem:hlp`. -/
example : ∃ a b : ℕ, a < b ∧ nu3 b + 2 ≤ nu3 a ∧
    IsPart 2 (ex a b nu3) ∧ psum (ex a b nu3) 2 = psum nu3 2 ∧
    Dom si22 (ex a b nu3) ∧ Dom (ex a b nu3) nu3 ∧ ex a b nu3 ≠ nu3 := by
  obtain ⟨n0, n1, n2⟩ := psum_nu3
  obtain ⟨s0, s1, s2⟩ := psum_si22
  refine robin_hood_step ⟨nu3_anti, nu3_vanish⟩ ⟨si22_anti, si22_vanish⟩ (by omega) ?_ ?_
  · intro r
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · rw [psum_stab si22_vanish r h, psum_stab nu3_vanish r h]; omega
  · intro h
    have h2 := congrFun h 0
    have e1 : si22 0 = 2 := by norm_num [si22]
    have e2 : nu3 0 = 3 := by norm_num [nu3]
    rw [e1, e2] at h2
    omega

end Witness

end RobinHood
