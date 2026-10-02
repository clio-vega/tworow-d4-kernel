/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic
import TworowD4Kernel.DiscreteConcavity

/-!
# The upper tail of a `PF₂` sequence is `PF₂`

Formalises **`lem:tail`** of `proofs/2026-10-01-c2-inter-region-inequality.tex`
(§`sec:tail`), registry node `tail-of-pf2-logconcave` of
`proofs/registry/cylindric-lorentzian.json`.  It is the key lemma of the `m = 2` case:
the step that turns `β` `PF₂` into log-concavity of `G`, i.e. into condition (A).

**Statement.** `β : ℤ → ℤ` nonnegative, log-concave, with interval support (the paper's
`PF₂`) and vanishing above `N`.  Then the upper tail `γ y = ∑_{r = y}^{N} β r` is again
`PF₂`.

This is the discrete form of the classical fact that a log-concave probability mass
function has a log-concave survival function (equivalently, that the log-concave class is
contained in the increasing-failure-rate class).  No external reference is cited because
the paper proves it from scratch in three lines; the paper's own `\remark` after
`lem:tail` records the provenance.

## The proof, and where it differs from the paper

The paper argues analytically: for `Δ = β(y-1) - β y > 0` it sets `q = β y / β (y-1) ∈
(0,1)`, bounds `β (y+k) ≤ β y · qᵏ`, and sums the geometric series to get
`γ y ≤ β y / (1-q) = β (y-1) β y / Δ`.

Over `ℤ` there is no division, so the geometric series is replaced by the equivalent
*multiplicative* statement, `tail_bound_aux`:

  `Δ · ∑_{r=y}^{M} β r  +  β (y-1) · β (M+1)  ≤  β (y-1) · β y`   for all `M ≥ y - 1`,

proved by induction on `M`.  Taking `M = N` kills the second term (`β (N+1) = 0`) and
leaves exactly the paper's `Δ γ y ≤ β (y-1) β y`.  In the geometric case the inequality is
an *equality*, so nothing is lost: the extra term `β (y-1) β (M+1)` is precisely the
tail of the geometric series that the paper discards by summing to infinity.

The induction step needs exactly one input, `ratio_antitone`:
`β (y-1) · β (m+1) ≤ β y · β m` for all `m ≥ y` — the paper's "the ratios
`β(r+1)/β(r)` form a nonincreasing sequence", cleared of denominators.

## Where each hypothesis is spent

* **nonnegativity** — `tail_nonneg`, and the `Δ ≤ 0` branch of `tail_logConcave`.
* **log-concavity** — the base case and the step of `ratio_antitone`, nowhere else.
* **interval support** — only in `zero_of_right`, and only to propagate a zero rightwards.
  It is *not* implied by the other two: `DiscreteConcavity.gapTwo_not_PFtwo` exhibits
  `(1,0,0,1)`, which is globally log-concave with non-interval support.  Control
  `tail_gapTwo_not_logConcave` below shows its tail is not log-concave, so the hypothesis
  is load-bearing and not carried for safety.
* **`β` vanishes above `N`** — `tail_succ`, so that the tail satisfies the recurrence at
  every `y ∈ ℤ` and not merely for `y ≤ N`.

Concavity is **not** assumed; the paper's first version of this lemma assumed
truncated-concavity and the refusal control for that clause did not fire.
-/

namespace TworowD4Kernel.TailSum

open TworowD4Kernel.DiscreteConcavity

variable {β : ℤ → ℤ} {N : ℤ}

/-- The upper tail `γ y = ∑_{r = y}^{N} β r` of `β`, cut at `N`.  When `β` vanishes above
`N` (hypothesis `hN` throughout) this is the paper's `γ(y) = ∑_{r ≥ y} β(r)`. -/
noncomputable def tail (β : ℤ → ℤ) (N y : ℤ) : ℤ := ∑ r ∈ Finset.Icc y N, β r

lemma Icc_eq_insert_left {y N : ℤ} (h : y ≤ N) :
    Finset.Icc y N = insert y (Finset.Icc (y + 1) N) := by
  ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

lemma Icc_eq_insert_right {y M : ℤ} (h : y ≤ M + 1) :
    Finset.Icc y (M + 1) = insert (M + 1) (Finset.Icc y M) := by
  ext r; simp only [Finset.mem_Icc, Finset.mem_insert]; omega

/-- The defining recurrence `γ y = β y + γ (y+1)`, valid at **every** `y ∈ ℤ`.  Above `N`
both sides are `0`, which is where `hN` is spent. -/
lemma tail_succ (hN : ∀ r, N < r → β r = 0) (y : ℤ) :
    tail β N y = β y + tail β N (y + 1) := by
  rcases le_or_gt y N with h | h
  · rw [tail, tail, Icc_eq_insert_left h,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  · have h1 : Finset.Icc y N = (∅ : Finset ℤ) := Finset.Icc_eq_empty (by omega)
    have h2 : Finset.Icc (y + 1) N = (∅ : Finset ℤ) := Finset.Icc_eq_empty (by omega)
    rw [tail, tail, h1, h2, Finset.sum_empty, hN y h, add_zero]

lemma tail_nonneg (hβ : ∀ r, 0 ≤ β r) (N y : ℤ) : 0 ≤ tail β N y :=
  Finset.sum_nonneg fun r _ => hβ r

/-- `γ` is nonincreasing — the first clause of the paper's `lem:tail`. -/
lemma tail_antitone (hβ : ∀ r, 0 ≤ β r) (hN : ∀ r, N < r → β r = 0) (y : ℤ) :
    tail β N (y + 1) ≤ tail β N y := by
  have h := tail_succ (β := β) (N := N) hN y
  have := hβ y
  omega

/-- Interval support, used in exactly one direction: a zero to the right of a positive
value forces every later value to vanish. -/
lemma zero_of_right (hβ : PFtwo β) {y m r : ℤ} (hy : β y ≠ 0) (hym : y ≤ m)
    (hm : β m = 0) (hr : m ≤ r) : β r = 0 := by
  by_contra hne
  exact (hβ.suppInterval y m r hym hr hy hne) hm

/-- **The ratios are nonincreasing**, cleared of denominators: `β(m+1)/β(m) ≤ β y/β(y-1)`
for `m ≥ y`.  This is the one place log-concavity is spent. -/
lemma ratio_antitone (hβ : PFtwo β) {y : ℤ} (hy : 0 < β y) :
    ∀ m, y ≤ m → β (y - 1) * β (m + 1) ≤ β y * β m := by
  refine Int.leInduction ?_ ?_
  · exact hβ.logConcave y
  · intro m hm ih
    rcases eq_or_lt_of_le (hβ.nonneg (m + 1)) with h | h
    · have hz : β (m + 1) = 0 := h.symm
      have hz2 : β (m + 1 + 1) = 0 :=
        zero_of_right hβ hy.ne' (by omega) hz (by omega)
      rw [hz, hz2, mul_zero, mul_zero]
    · have key := hβ.logConcave (m + 1)
      rw [show m + 1 - 1 = m from by ring] at key
      refine le_of_mul_le_mul_right ?_ h
      nlinarith [hβ.nonneg (m + 1 + 1), hβ.nonneg y, hβ.nonneg (y - 1), ih, key]

/-- The replacement for the paper's geometric-series bound, over `ℤ` and without division.
Induction on the upper limit `M`; the second summand is the discarded geometric tail. -/
lemma tail_bound_aux (hβ : PFtwo β) {y : ℤ} (hy : 0 < β y) :
    ∀ M, y - 1 ≤ M →
      (β (y - 1) - β y) * (∑ r ∈ Finset.Icc y M, β r) + β (y - 1) * β (M + 1)
        ≤ β (y - 1) * β y := by
  refine Int.leInduction ?_ ?_
  · have he : Finset.Icc y (y - 1) = (∅ : Finset ℤ) := Finset.Icc_eq_empty (by omega)
    rw [he, show y - 1 + 1 = y from by ring]
    simp
  · intro M hM ih
    have hsplit : ∑ r ∈ Finset.Icc y (M + 1), β r = β (M + 1) + ∑ r ∈ Finset.Icc y M, β r := by
      rw [Icc_eq_insert_right (by omega),
        Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
    have hrat : β (y - 1) * β (M + 1 + 1) ≤ β y * β (M + 1) :=
      ratio_antitone hβ hy (M + 1) (by omega)
    rw [hsplit]
    nlinarith [ih, hrat]

/-- **`lem:tail`, log-concavity clause.**  The upper tail of a `PF₂` sequence is
log-concave.  `tail-of-pf2-logconcave`, `proofs/2026-10-01-c2-inter-region-inequality.tex`
§`sec:tail`. -/
theorem tail_logConcave (hβ : PFtwo β) (hN : ∀ r, N < r → β r = 0) (y : ℤ) :
    tail β N (y - 1) * tail β N (y + 1) ≤ tail β N y * tail β N y := by
  have h1 : tail β N (y - 1) = β (y - 1) + tail β N y := by
    have h := tail_succ (β := β) (N := N) hN (y - 1)
    rwa [show y - 1 + 1 = y from by ring] at h
  have h2 : tail β N y = β y + tail β N (y + 1) := tail_succ hN y
  have hGnn : 0 ≤ tail β N y := tail_nonneg hβ.nonneg N y
  -- `eq:tailid`: `γ(y)² - γ(y-1)γ(y+1) = β(y-1)β(y) - Δ·γ(y)`, so everything reduces to:
  suffices hkey : (β (y - 1) - β y) * tail β N y ≤ β (y - 1) * β y by
    rw [h1, show tail β N (y + 1) = tail β N y - β y from by omega]
    nlinarith [hkey]
  rcases le_or_gt (β (y - 1)) (β y) with hΔ | hΔ
  · -- `Δ ≤ 0`: the right side of `eq:tailid` is already `≥ 0`.
    linarith [mul_nonneg (sub_nonneg.mpr hΔ) hGnn,
      mul_nonneg (hβ.nonneg (y - 1)) (hβ.nonneg y)]
  · have hy1 : 0 < β (y - 1) := lt_of_le_of_lt (hβ.nonneg y) hΔ
    rcases eq_or_lt_of_le (hβ.nonneg y) with hy0 | hy0
    · -- Case `β y = 0`: `y` is past the support, so the whole tail vanishes.
      have hz : tail β N y = 0 := by
        refine Finset.sum_eq_zero fun r hr => ?_
        rw [Finset.mem_Icc] at hr
        exact zero_of_right hβ hy1.ne' (by omega) hy0.symm hr.1
      rw [hz, ← hy0]; simp
    · -- Case `β y > 0`: the geometric bound.
      rcases le_or_gt y (N + 1) with hyN | hyN
      · have hb := tail_bound_aux hβ hy0 N (by omega)
        rw [hN (N + 1) (by omega), mul_zero, add_zero] at hb
        exact hb
      · have hz : tail β N y = 0 := by
          rw [tail, Finset.Icc_eq_empty (by omega), Finset.sum_empty]
        rw [hz, mul_zero]
        exact mul_nonneg hy1.le (hβ.nonneg y)

/-- **`lem:tail`, in full.**  The upper tail of a `PF₂` sequence is itself `PF₂`.

The support clause of the paper (`{γ > 0}` is a down-set) is stronger than `PFtwo`'s
`suppInterval`, but a down-set *is* closed under betweenness, so this is the right
packaging: it lets the lemma compose with everything else in `DiscreteConcavity`. -/
theorem tail_PFtwo (hβ : PFtwo β) (hN : ∀ r, N < r → β r = 0) : PFtwo (tail β N) where
  nonneg := tail_nonneg hβ.nonneg N
  suppInterval := by
    intro r s t hrs hst _ ht
    -- `γ` is nonincreasing and nonnegative, so `γ s ≥ γ t > 0`.
    have hmono : ∀ a b : ℤ, a ≤ b → tail β N b ≤ tail β N a := by
      intro a b hab
      induction b, hab using Int.leInduction with
      | base => exact le_refl _
      | succ n _ ih => exact le_trans (tail_antitone hβ.nonneg hN n) ih
    have := hmono s t hst
    have := tail_nonneg hβ.nonneg N t
    omega
  logConcave := tail_logConcave hβ hN

/-- `{γ > 0}` is a down-set — the third clause of the paper's `lem:tail`, stated
separately because `PFtwo.suppInterval` is strictly weaker. -/
theorem tail_pos_downSet (hβ : ∀ r, 0 ≤ β r) (hN : ∀ r, N < r → β r = 0)
    {y z : ℤ} (hyz : y ≤ z) (h : 0 < tail β N z) : 0 < tail β N y := by
  have hmono : ∀ a b : ℤ, a ≤ b → tail β N b ≤ tail β N a := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => exact le_refl _
    | succ n _ ih => exact le_trans (tail_antitone hβ hN n) ih
  exact lt_of_lt_of_le h (hmono y z hyz)

/-! ## Controls

Three refusal controls.  Each is a statement that something is **false**, so each can only
be proved if the object really does fail; a control that cannot fire is not a control.
-/

/-- `tail` vanishes above the cut.  Used to evaluate the controls' tails by walking the
recurrence `tail_succ` down from `N + 1`, so no `Finset` is ever enumerated. -/
lemma tail_eq_zero_of_lt {y : ℤ} (h : N < y) : tail β N y = 0 := by
  rw [tail, Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-! ### Control 1: log-concavity is load-bearing

`ctrlA = (2,1,2)` on `{0,1,2}` is nonnegative with **interval support**, so it isolates the
log-concavity conjunct: it fails log-concavity at `1` (`2·2 > 1·1`) and its tail
`(…,5,3,2,0,…)` fails log-concavity at `1` too (`5·2 = 10 > 9 = 3²`). -/
def ctrlA : ℤ → ℤ := fun r => if r = 0 then 2 else if r = 1 then 1 else if r = 2 then 2 else 0

lemma ctrlA_nonneg (r : ℤ) : 0 ≤ ctrlA r := by unfold ctrlA; split_ifs <;> omega

lemma ctrlA_suppInterval (r s t : ℤ) (hrs : r ≤ s) (hst : s ≤ t)
    (hr : ctrlA r ≠ 0) (ht : ctrlA t ≠ 0) : ctrlA s ≠ 0 := by
  unfold ctrlA at *; split_ifs at * <;> omega

lemma ctrlA_vanish : ∀ r : ℤ, (2 : ℤ) < r → ctrlA r = 0 := by
  intro r hr; unfold ctrlA; split_ifs <;> omega

/-- `ctrlA` is **not** log-concave, so it is not `PF₂` even though it is nonnegative with
interval support. -/
theorem ctrlA_not_logConcave : ¬ (∀ s : ℤ, ctrlA (s - 1) * ctrlA (s + 1) ≤ ctrlA s * ctrlA s) := by
  intro h
  have := h 1
  norm_num [ctrlA] at this

/-- **Control 1 fires.**  Dropping log-concavity destroys the conclusion. -/
theorem ctrlA_tail_not_logConcave :
    ¬ (tail ctrlA 2 (1 - 1) * tail ctrlA 2 (1 + 1) ≤ tail ctrlA 2 1 * tail ctrlA 2 1) := by
  have e3 : tail ctrlA 2 3 = 0 := tail_eq_zero_of_lt (by norm_num)
  have s2 := tail_succ (β := ctrlA) (N := 2) ctrlA_vanish 2
  have s1 := tail_succ (β := ctrlA) (N := 2) ctrlA_vanish 1
  have s0 := tail_succ (β := ctrlA) (N := 2) ctrlA_vanish 0
  rw [show ((2 : ℤ) + 1) = 3 from by norm_num, e3,
    show ctrlA 2 = 2 from by norm_num [ctrlA]] at s2
  rw [show ((1 : ℤ) + 1) = 2 from by norm_num,
    show ctrlA 1 = 1 from by norm_num [ctrlA]] at s1
  rw [show ((0 : ℤ) + 1) = 1 from by norm_num,
    show ctrlA 0 = 2 from by norm_num [ctrlA]] at s0
  have v2 : tail ctrlA 2 2 = 2 := by omega
  have v1 : tail ctrlA 2 1 = 3 := by omega
  have v0 : tail ctrlA 2 0 = 5 := by omega
  rw [show ((1 : ℤ) - 1) = 0 from by norm_num, show ((1 : ℤ) + 1) = 2 from by norm_num,
    v0, v1, v2]
  norm_num

/-! ### Control 2: interval support is load-bearing

`ctrlB = (1,0,0,1)` on `{0,1,2,3}` is nonnegative and **globally log-concave** — this is
`DiscreteConcavity.gapTwo_not_PFtwo`'s sequence, and it is exactly why the three `PFtwo`
fields are independent.  So it isolates the interval-support conjunct.  Its tail is
`(…,2,1,1,1,0,…)`, which fails log-concavity at `1`: `2·1 = 2 > 1 = 1²`. -/
def ctrlB : ℤ → ℤ := fun r => if r = 0 then 1 else if r = 3 then 1 else 0

lemma ctrlB_nonneg (r : ℤ) : 0 ≤ ctrlB r := by unfold ctrlB; split_ifs <;> omega

lemma ctrlB_logConcave (s : ℤ) : ctrlB (s - 1) * ctrlB (s + 1) ≤ ctrlB s * ctrlB s := by
  unfold ctrlB; split_ifs <;> omega

lemma ctrlB_vanish : ∀ r : ℤ, (3 : ℤ) < r → ctrlB r = 0 := by
  intro r hr; unfold ctrlB; split_ifs <;> omega

/-- `ctrlB`'s support is not an interval, so it is not `PF₂` despite being nonnegative and
log-concave. -/
theorem ctrlB_not_suppInterval :
    ¬ (∀ r s t : ℤ, r ≤ s → s ≤ t → ctrlB r ≠ 0 → ctrlB t ≠ 0 → ctrlB s ≠ 0) := by
  intro h
  have := h 0 1 3 (by norm_num) (by norm_num) (by norm_num [ctrlB]) (by norm_num [ctrlB])
  norm_num [ctrlB] at this

/-- **Control 2 fires.**  Dropping interval support destroys the conclusion, even with
global log-concavity retained. -/
theorem ctrlB_tail_not_logConcave :
    ¬ (tail ctrlB 3 (1 - 1) * tail ctrlB 3 (1 + 1) ≤ tail ctrlB 3 1 * tail ctrlB 3 1) := by
  have e4 : tail ctrlB 3 4 = 0 := tail_eq_zero_of_lt (by norm_num)
  have s3 := tail_succ (β := ctrlB) (N := 3) ctrlB_vanish 3
  have s2 := tail_succ (β := ctrlB) (N := 3) ctrlB_vanish 2
  have s1 := tail_succ (β := ctrlB) (N := 3) ctrlB_vanish 1
  have s0 := tail_succ (β := ctrlB) (N := 3) ctrlB_vanish 0
  rw [show ((3 : ℤ) + 1) = 4 from by norm_num, e4,
    show ctrlB 3 = 1 from by norm_num [ctrlB]] at s3
  rw [show ((2 : ℤ) + 1) = 3 from by norm_num,
    show ctrlB 2 = 0 from by norm_num [ctrlB]] at s2
  rw [show ((1 : ℤ) + 1) = 2 from by norm_num,
    show ctrlB 1 = 0 from by norm_num [ctrlB]] at s1
  rw [show ((0 : ℤ) + 1) = 1 from by norm_num,
    show ctrlB 0 = 1 from by norm_num [ctrlB]] at s0
  have v2 : tail ctrlB 3 2 = 1 := by omega
  have v1 : tail ctrlB 3 1 = 1 := by omega
  have v0 : tail ctrlB 3 0 = 2 := by omega
  rw [show ((1 : ℤ) - 1) = 0 from by norm_num, show ((1 : ℤ) + 1) = 2 from by norm_num,
    v0, v1, v2]
  norm_num

/-! ### Control 3: the converse is false

`tail_PFtwo` is an implication, not an equivalence.  `ctrlGamma = (…,4,4,4,2,1,0,…)` is
`PF₂`, and it is the tail of `ctrlC = (2,1,1)` — it satisfies the defining recurrence
`γ y = β y + γ (y+1)` at every `y ∈ ℤ` — yet `ctrlC` is not `PF₂` (`β(0)β(2) = 2 > 1 =
β(1)²`).  So nobody may later read `tail_PFtwo` backwards.

The control is stated through the recurrence rather than through `tail` on purpose: `tail`
is cut at a finite `N`, and `ctrlGamma` is constant on the whole of `ℤ_{≤0}`, so stating it
as `ctrlGamma = tail ctrlC 2` would need a separate downward induction that adds nothing.
The recurrence plus `ctrlGamma y = 0` for `y > 2` pins `ctrlGamma` down completely. -/
def ctrlC : ℤ → ℤ := fun r => if r = 0 then 2 else if r = 1 then 1 else if r = 2 then 1 else 0

def ctrlGamma : ℤ → ℤ := fun y => if y ≤ 0 then 4 else if y = 1 then 2 else if y = 2 then 1 else 0

lemma ctrlGamma_tail_of_ctrlC (y : ℤ) : ctrlGamma y = ctrlC y + ctrlGamma (y + 1) := by
  unfold ctrlGamma ctrlC; split_ifs <;> omega

lemma ctrlGamma_PFtwo : PFtwo ctrlGamma where
  nonneg s := by unfold ctrlGamma; split_ifs <;> omega
  suppInterval r s t hrs hst hr ht := by unfold ctrlGamma at *; split_ifs at * <;> omega
  logConcave s := by unfold ctrlGamma; split_ifs <;> omega

/-- **Control 3 fires.**  A `PF₂` tail does not force a `PF₂` summand: the converse of
`tail_PFtwo` is false. -/
theorem converse_false :
    ∃ β γ : ℤ → ℤ, PFtwo γ ∧ (∀ y, γ y = β y + γ (y + 1)) ∧ ¬ PFtwo β :=
  ⟨ctrlC, ctrlGamma, ctrlGamma_PFtwo, ctrlGamma_tail_of_ctrlC, by
    intro h
    have := h.logConcave 1
    norm_num [ctrlC] at this⟩

/-! ## Axioms -/

#print axioms TworowD4Kernel.TailSum.tail_logConcave
#print axioms TworowD4Kernel.TailSum.tail_PFtwo
#print axioms TworowD4Kernel.TailSum.tail_pos_downSet
#print axioms TworowD4Kernel.TailSum.ratio_antitone
#print axioms TworowD4Kernel.TailSum.tail_bound_aux
#print axioms TworowD4Kernel.TailSum.ctrlA_tail_not_logConcave
#print axioms TworowD4Kernel.TailSum.ctrlB_tail_not_logConcave
#print axioms TworowD4Kernel.TailSum.converse_false

end TworowD4Kernel.TailSum
