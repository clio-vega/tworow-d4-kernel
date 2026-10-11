/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic

/-!
# The cyclic/open ascent dichotomy for binary words

A binary word of length `h` is a map to `Bool`.  Call a position an **ascent** when the
word reads `false` there and `true` at the next position.  Two readings of "next":

* **cyclic** -- index by `ZMod h`, so position `h - 1` is followed by position `0`;
* **open** -- index by `Fin (n + 1)`, so position `n` has no successor and the last letter
  is never the top of an ascent.

The two readings have wildly different ascent-free loci, and that asymmetry is the whole
content of this file:

* `ZMod.ascentFree_iff_const` : cyclically ascent-free **iff constant**, so there are
  exactly **2** such words for every `h ≥ 1` (`ZMod.card_ascentFree`);
* `Fin.ascentFree_iff_antitone` : openly ascent-free **iff antitone**, iff the threshold
  word `1^a 0^{h-a}` (`Fin.ascentFree_iff_exists_threshold`), so there are exactly
  **h + 1** such words (`Fin.card_ascentFree`).

Hence `Fin.card_ascentFree_lt` : the open locus is strictly larger as soon as `h ≥ 2`.

## Why the cyclic case is the hard one

The open statement is a *local-to-global* fact about a linear order, and Mathlib already
has it: `Fin.antitone_iff_succ_le`.  A word with no open ascent is literally a
sorted-descending list, and nothing needs to be proved about the shape of `Bool`.

The cyclic statement has no such reading, because the wrap turns the word into a necklace
and there is no order on `ZMod h` for `i ↦ i + 1` to respect.  What replaces the order is
the fact that `1` **generates**: every `j` is `i + n` for a natural `n`
(`ZMod.exists_natCast_add`), so a single-step inequality propagates all the way around and
closes up on itself.  Going round the cycle forces `θ j ≤ θ i` for *every* ordered pair,
and `Bool.le_antisymm` then collapses the word to a constant.  The conclusion is strictly
stronger than antitone -- it is rigid -- and that rigidity is why a cyclic grading can
carry so little.

## Provenance

This is the combinatorial half of the Q410 theorem
(`projects/proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`): no cyclically
`ψ`-graded weight carries Warnaar's determinant.  The cyclic index set being analysed is
Korff's, **arXiv:1110.6356, Definition 5.5**: `J(θ) = {i ∈ ℤ/hℤ : θ_i = 0, θ_{i+1} = 1}`, and
`ZMod.ascentFree_iff_const` is the assertion that it is empty exactly on the constants.  The
open index set it is contrasted with is Macdonald's ordinary `ψ` ascent set.  The determinant
on the far side is Warnaar, **arXiv:2511.17034, Section 6**; the combinatorial evaluation it
generalises is Huh--Kim--Krattenthaler--Okada, **arXiv:2301.13117, Theorem 3.3**.
The cyclic lemma is the step that
reduces a non-constant occupation word to an ascent; the companion `ord_{t=1}` count is
not formalised here.  The open half underwrites Q417: a wrap-blind grading sees `h + 1`
ascent-free strips where the cyclic one sees `2`.
-/

namespace TworowD4Kernel.CyclicAscent

open Finset

/-! ## Ascents

`Bool` carries `false < true`, and "no ascent at `i`" is exactly the inequality
`θ (next i) ≤ θ i`.  We record that translation once, for both readings. -/

/-- Not-an-ascent is the single-step inequality.  Both directions, because the `Finset`
characterisations below need each one. -/
theorem not_ascent_iff (b c : Bool) : ¬(b = false ∧ c = true) ↔ c ≤ b := by
  revert b c; decide

/-! ## The cyclic reading -/

namespace ZMod

/-- In `ZMod h` with `h ≥ 1`, the element `1` generates: every `j` is `i + n` for some
*natural* `n`.  This is the substitute for the missing order, and the only input the
cyclic lemma needs beyond one-step propagation. -/
theorem exists_natCast_add {h : ℕ} [NeZero h] (i j : ZMod h) : ∃ n : ℕ, j = i + (n : ZMod h) := by
  refine ⟨(j - i).val, ?_⟩
  rw [ZMod.natCast_zmod_val]
  ring

/-- One-step propagation, iterated: if `θ` never increases along the successor, it never
increases along any number of successor steps. -/
theorem le_of_natCast_add {h : ℕ} {θ : ZMod h → Bool} (hstep : ∀ i, θ (i + 1) ≤ θ i)
    (i : ZMod h) : ∀ n : ℕ, θ (i + (n : ZMod h)) ≤ θ i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have : θ (i + ((n : ZMod h) + 1)) ≤ θ (i + (n : ZMod h)) := by
        have := hstep (i + (n : ZMod h)); rwa [add_assoc] at this
      calc θ (i + ((n + 1 : ℕ) : ZMod h)) = θ (i + ((n : ZMod h) + 1)) := by push_cast; ring_nf
        _ ≤ θ (i + (n : ZMod h)) := this
        _ ≤ θ i := ih

/-- **The cyclic rigidity lemma.**  A word on `ZMod h` that never increases along the
cyclic successor is *constant* -- not merely antitone.  Going around the cycle makes the
inequality hold in both directions between any two positions. -/
theorem const_of_succ_le {h : ℕ} [NeZero h] {θ : ZMod h → Bool}
    (hstep : ∀ i, θ (i + 1) ≤ θ i) (i j : ZMod h) : θ i = θ j := by
  obtain ⟨n, hn⟩ := exists_natCast_add i j
  obtain ⟨m, hm⟩ := exists_natCast_add j i
  exact Bool.le_antisymm (hm ▸ le_of_natCast_add hstep j m) (hn ▸ le_of_natCast_add hstep i n)

/-- **Main result, contrapositive form.**  A non-constant cyclic binary word has a
`false → true` ascent somewhere. -/
theorem exists_ascent_of_not_const {h : ℕ} [NeZero h] {θ : ZMod h → Bool}
    (hne : ∃ i j, θ i ≠ θ j) : ∃ i, θ i = false ∧ θ (i + 1) = true := by
  obtain ⟨i, j, hij⟩ := hne
  by_contra hno
  push Not at hno
  exact hij (const_of_succ_le (fun k => (not_ascent_iff _ _).mp
    (fun hk => hno k hk.1 hk.2)) i j)

/-- The cyclic ascent set.  Needs `NeZero h` only to have a `Fintype` to filter over. -/
def J {h : ℕ} [NeZero h] (θ : ZMod h → Bool) : Finset (ZMod h) :=
  univ.filter fun i => θ i = false ∧ θ (i + 1) = true

/-- **The cyclic dichotomy.**  `J θ = ∅` iff `θ` is constant. -/
theorem ascentFree_iff_const {h : ℕ} [NeZero h] (θ : ZMod h → Bool) :
    J θ = ∅ ↔ ∀ i j, θ i = θ j := by
  constructor
  · intro hJ i j
    rw [J, filter_eq_empty_iff] at hJ
    exact const_of_succ_le (fun k => (not_ascent_iff _ _).mp fun hk => hJ (mem_univ k) hk) i j
  · intro hconst
    rw [J, filter_eq_empty_iff]
    intro i _ hi
    rw [hconst i (i + 1), hi.2] at hi
    exact Bool.noConfusion hi.1

end ZMod

/-! ## The open reading -/

namespace Fin

/-- The open ascent set of a word of length `n + 1`: positions `i < n` whose letter is
`false` and whose successor's letter is `true`.  The last letter is never read as the
bottom of an ascent -- that is the whole difference from `ZMod.J`. -/
def J {n : ℕ} (θ : Fin (n + 1) → Bool) : Finset (Fin n) :=
  univ.filter fun i => θ i.castSucc = false ∧ θ i.succ = true

/-- **The open dichotomy, order form.**  `J θ = ∅` iff `θ` is antitone.  The local-to-global
step is Mathlib's `Fin.antitone_iff_succ_le`; nothing here is special to `Bool`. -/
theorem ascentFree_iff_antitone {n : ℕ} (θ : Fin (n + 1) → Bool) :
    J θ = ∅ ↔ Antitone θ := by
  rw [Fin.antitone_iff_succ_le, J, filter_eq_empty_iff]
  exact ⟨fun hJ i => (not_ascent_iff _ _).mp fun hi => hJ (mem_univ i) hi,
    fun hA i _ hi => (not_ascent_iff _ _).mpr (hA i) hi⟩

/-- **The open dichotomy, word form.**  An ascent-free word of length `n + 1` is exactly a
threshold word `1^a 0^{n+1-a}`, and the threshold `a` is its number of `true`s. -/
theorem ascentFree_iff_exists_threshold {n : ℕ} (θ : Fin (n + 1) → Bool) :
    J θ = ∅ ↔ ∃ a : Fin (n + 2), ∀ i : Fin (n + 1), θ i = true ↔ (i : ℕ) < (a : ℕ) := by
  rw [ascentFree_iff_antitone]
  constructor
  · intro hA
    -- The threshold is the number of `true`s.  Antitonicity makes the `true` set
    -- downward closed, and a downward-closed subset of `Fin (n+1)` is an `Iic`.
    have hdown : ∀ {i j : Fin (n + 1)}, i ≤ j → θ j = true → θ i = true := by
      intro i j hij hj; have := hA hij; rw [hj] at this
      exact Bool.le_antisymm (Bool.le_true _) this
    set a := (univ.filter fun j : Fin (n + 1) => θ j = true).card with ha
    refine ⟨⟨a, Nat.lt_succ_of_le (le_trans (card_filter_le _ _) (by simp))⟩, fun i => ?_⟩
    simp only []
    constructor
    · -- `θ i = true` makes `Iic i` a subset of the `true` set, so `a ≥ i + 1`.
      intro hi
      have hsub : Finset.Iic i ⊆ univ.filter fun j : Fin (n + 1) => θ j = true := by
        intro j hj; exact mem_filter.mpr ⟨mem_univ j, hdown (mem_Iic.mp hj) hi⟩
      have := card_le_card hsub
      rw [Fin.card_Iic] at this
      omega
    · -- `θ i = false` makes the `true` set a subset of `Iio i`, so `a ≤ i`.
      intro hlt
      by_contra hi
      simp only [Bool.not_eq_true] at hi
      have hsub : (univ.filter fun j : Fin (n + 1) => θ j = true) ⊆ Finset.Iio i := by
        intro j hj
        refine mem_Iio.mpr (lt_of_not_ge fun hij => ?_)
        rw [hdown hij (mem_filter.mp hj).2] at hi
        exact Bool.noConfusion hi
      have := card_le_card hsub
      rw [Fin.card_Iio] at this
      omega
  · intro ⟨a, ha⟩ i j hij
    by_cases hj : θ j = true
    · have : (i : ℕ) < (a : ℕ) := lt_of_le_of_lt hij ((ha j).mp hj)
      simp [(ha i).mpr this]
    · simp only [Bool.not_eq_true] at hj
      rw [hj]
      exact Bool.false_le _

/-! ## The two counts, and the strict gap

`2` cyclic witnesses against `h + 1` open ones.  The numbers are the reason the dichotomy
matters: a cyclic grading has a two-element ascent-free locus whatever `h` is, while the
open grading's locus grows linearly. -/

/-- The threshold word `1^a 0^{h-a}`. -/
def thr {n : ℕ} (a : Fin (n + 2)) : Fin (n + 1) → Bool := fun i => decide ((i : ℕ) < (a : ℕ))

theorem thr_injective {n : ℕ} : Function.Injective (thr (n := n)) := by
  intro a b hab
  by_contra hne
  -- The two words first differ at index `min a b`, which is a legal index.
  rcases lt_or_gt_of_ne (fun h : (a : ℕ) = (b : ℕ) => hne (Fin.val_injective h)) with h | h
  · have hlt : (a : ℕ) < n + 1 := by omega
    have := congrFun hab ⟨(a : ℕ), hlt⟩
    simp only [thr, decide_eq_decide] at this
    omega
  · have hlt : (b : ℕ) < n + 1 := by omega
    have := congrFun hab ⟨(b : ℕ), hlt⟩
    simp only [thr, decide_eq_decide] at this
    omega

/-- **The open count.**  Exactly `h + 1 = n + 2` ascent-free words of length `n + 1`. -/
theorem card_ascentFree {n : ℕ} :
    (univ.filter fun θ : Fin (n + 1) → Bool => J θ = ∅).card = n + 2 := by
  classical
  have himg : (univ.filter fun θ : Fin (n + 1) → Bool => J θ = ∅)
      = univ.image (thr (n := n)) := by
    ext θ
    simp only [mem_filter, mem_univ, true_and, mem_image]
    rw [ascentFree_iff_exists_threshold]
    constructor
    · intro ⟨a, ha⟩
      refine ⟨a, funext fun i => ?_⟩
      simp only [thr]
      cases hθ : θ i
      · rw [decide_eq_false_iff_not]
        intro hlt
        rw [(ha i).mpr hlt] at hθ
        exact Bool.noConfusion hθ
      · rw [decide_eq_true_eq]
        exact (ha i).mp hθ
    · intro ⟨a, hθ⟩
      exact ⟨a, fun i => by rw [← hθ]; simp [thr]⟩
  rw [himg, card_image_of_injective _ thr_injective, card_univ, Fintype.card_fin]

end Fin

/-- **The cyclic count.**  Exactly `2` ascent-free cyclic words, for every `h ≥ 1`. -/
theorem ZMod.card_ascentFree {h : ℕ} [NeZero h] :
    (univ.filter fun θ : ZMod h → Bool => ZMod.J θ = ∅).card = 2 := by
  classical
  have hpair : (univ.filter fun θ : ZMod h → Bool => ZMod.J θ = ∅)
      = {(fun _ => false), (fun _ => true)} := by
    ext θ
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    rw [ZMod.ascentFree_iff_const]
    constructor
    · intro hconst
      cases hθ : θ 0 with
      | false => exact Or.inl (funext fun i => (hconst i 0).trans hθ)
      | true => exact Or.inr (funext fun i => (hconst i 0).trans hθ)
    · rintro (rfl | rfl) <;> intro i j <;> rfl
  rw [hpair, card_insert_of_notMem (by simp [funext_iff]), card_singleton]

/-! ## The gap, and two ablations

The strict inequality is the mathematical payload, and both of its hypotheses are
*necessary about the statement*, not merely about these proofs -- each has a witness
below. -/

/-- **The gap.**  For every `h = n + 1 ≥ 2`, strictly more open ascent-free words than
cyclic ones. -/
theorem card_ascentFree_lt {n : ℕ} (hn : 1 ≤ n) :
    (univ.filter fun θ : ZMod (n + 1) → Bool => ZMod.J θ = ∅).card
      < (univ.filter fun θ : Fin (n + 1) → Bool => Fin.J θ = ∅).card := by
  rw [ZMod.card_ascentFree, Fin.card_ascentFree]
  omega

/-- **Ablation 1: `h ≥ 2` is necessary for the gap**, and not because the proof needs it.
At `h = 1` both counts are `2` -- the single letter is its own cyclic successor, so the
two readings coincide.  So `card_ascentFree_lt` is sharp. -/
theorem card_ascentFree_eq_at_one :
    (univ.filter fun θ : ZMod 1 → Bool => ZMod.J θ = ∅).card
      = (univ.filter fun θ : Fin 1 → Bool => Fin.J θ = ∅).card := by
  rw [ZMod.card_ascentFree, Fin.card_ascentFree]

/-- **Ablation 2: `NeZero h` is necessary for cyclic rigidity, by counterexample.**
`ZMod 0` is `ℤ`, where `1` no longer generates: the step-down inequality holds along the
successor but never closes up, so `const_of_succ_le` is *false* there.  The witness is the
indicator of the negatives -- a word with no ascent that is not constant.  This is a fact
about the statement; deleting `NeZero` would not merely break the proof. -/
theorem not_const_of_succ_le_int :
    ∃ θ : ℤ → Bool, (∀ i : ℤ, θ (i + 1) ≤ θ i) ∧ ∃ i j, θ i ≠ θ j := by
  refine ⟨fun i => decide (i < 0), fun i => ?_, -1, 0, by simp⟩
  by_cases hc : i + 1 < 0
  · have h2 : i < 0 := by omega
    simp [hc, h2]
  · simp [hc]

/-- The same witness read in `ZMod 0`, which is `ℤ` on the nose.  This is the `h = 0`
instance of `const_of_succ_le` with its `NeZero` hypothesis removed, and it is false. -/
theorem not_const_of_succ_le_zmod_zero :
    ∃ θ : ZMod 0 → Bool, (∀ i : ZMod 0, θ (i + 1) ≤ θ i) ∧ ∃ i j, θ i ≠ θ j :=
  not_const_of_succ_le_int

/-! ## Brute-force cross-checks

The counts above are proved for all `h`; these evaluate the *definitions* over the whole
function space by kernel reduction, so they are an independent instrument -- they share no
lemma with the proofs, only the `Finset` definitions.  The point of the pair at `h = 1` is
that the gap is *absent* there; at `h = 2, 3, 4` it is `2 < 3, 4, 5`. -/

section Checks

example : (univ.filter fun θ : ZMod 1 → Bool => ZMod.J θ = ∅).card = 2 := by decide
example : (univ.filter fun θ : ZMod 2 → Bool => ZMod.J θ = ∅).card = 2 := by decide
example : (univ.filter fun θ : ZMod 3 → Bool => ZMod.J θ = ∅).card = 2 := by decide
example : (univ.filter fun θ : ZMod 4 → Bool => ZMod.J θ = ∅).card = 2 := by decide

example : (univ.filter fun θ : Fin 1 → Bool => Fin.J θ = ∅).card = 2 := by decide
example : (univ.filter fun θ : Fin 2 → Bool => Fin.J θ = ∅).card = 3 := by decide
example : (univ.filter fun θ : Fin 3 → Bool => Fin.J θ = ∅).card = 4 := by decide
example : (univ.filter fun θ : Fin 4 → Bool => Fin.J θ = ∅).card = 5 := by decide

end Checks

end TworowD4Kernel.CyclicAscent
