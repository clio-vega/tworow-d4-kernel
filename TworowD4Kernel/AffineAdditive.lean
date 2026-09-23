/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Length-additivity of cyclically decreasing factorisations: the combinatorial core

Formalisation of the **combinatorial core** of
`projects/proofs/2026-09-23-c1-bracketed-pair-deletion.tex` (Q232), together with the
counterexample census of its §"The bracket hypothesis is not load-bearing".

## What is and is not formalised here

The affine symmetric group `S̃ₙ` is **not** built — it is not in Mathlib, and it is not
what the theorem is about.  Instead this file takes as its *definition* of additivity
the criterion that the paper proves equivalent to `ℓ(u_S u_T) = |S| + |T|`:

* `lem:blocks` (Lemma 2.2 of `2026-09-21-c1-affine-stanley-exchange.tex`, restated with
  proof at l.104 of the Q232 note) says `u_S` rotates each block of `S` down by one:
  `u_S j = j - 1` if `j - 1 ∈ S`, and otherwise `u_S j = min {c ≥ j : c ∉ S}`.
  That formula is `uS` below.
* `lem:add` (Lemma 2.3, ibid., l.181) says `ℓ(w u_X) = ℓ(w) + |X|` iff for every run
  `[m, M]` of `X` and every `j ∈ [m, M]`, `w (M+1) > w j`.  With `w = u_S`, `X = T`
  that is `Additive` below.

Both equivalences are **assumed**, exactly as `2026-09-22` assumed `cor:bk` and
`cor:exchange`.  They are proved on paper and checked computationally against Shi's
inversion formula (`proofs/code-q220/affine.py`), *not* against the block model, so
they are tested rather than assumed on the computational side.  Nothing below is a
statement about `S̃ₙ`; everything below is a statement about `uS` and `Additive`.

## The finite quantifier is licensed, not assumed

`Additive` quantifies over one integer lift `k ∈ {0, …, n-1}` of each residue, rather
than over all runs in `ℤ`.  The paper justifies this by `n`-equivariance (eq. `equiv`).
Here that justification is *proved*: `uS_periodic`, `firstGap_periodic` and
`criterion_periodic` show the run condition at `j` and at `j + n` are equivalent.

## Status

`additive_not_hereditary` and `additive_erase_left_not_stable` are the formalised
counterexamples; the deletion theorem itself is **not** formalised (see the session
note for why).  No `sorry` in this file.
-/

namespace AffineAdditive

variable {n : ℕ}

/-! ### The block model of `u_S` -/

/-- `firstGapAux S j f` is the least `k < f` with `j + k` outside the `n`-periodic lift
of `S`, or `f` if there is none.  Fuel-bounded so that it is total and computable. -/
def firstGapAux (S : Finset (ZMod n)) (j : ℤ) : ℕ → ℕ
  | 0 => 0
  | f + 1 => if ((j : ZMod n)) ∈ S then firstGapAux S (j + 1) f + 1 else 0

/-- `firstGap S j = min {c ≥ j : c ∉ S}`, the next gap of `S` weakly above `j`.
Fuel `n` suffices whenever `S` is a proper subset, since every residue occurs in
`[j, j + n - 1]`.  (For `S = univ` this returns the junk value `j + n`; every statement
below carries `S.card < n`.) -/
def firstGap (S : Finset (ZMod n)) (j : ℤ) : ℤ := j + (firstGapAux S j n : ℤ)

/-- The block model of the cyclically decreasing element `u_S`, Lemma `lem:blocks`:
`u_S` sends `j ↦ j - 1` inside a block and rotates the bottom of a block to its top. -/
def uS (S : Finset (ZMod n)) (j : ℤ) : ℤ :=
  if ((j - 1 : ℤ) : ZMod n) ∈ S then j - 1 else firstGap S j

/-! ### Additivity, as the paper's criterion -/

/-- `Additive S T` is Lemma `lem:add` with `w = u_S`, `X = T`: for every run `[m, M]`
of `T` and every `j ∈ [m, M]`, `u_S (M+1) > u_S j`.

It is stated in the equivalent per-element form: for each `j ∈ T`, the top of the run
of `T` containing `j` is `firstGap T (j+1) - 1`, so `M + 1 = firstGap T (j+1)`.
Quantifying over lifts `k ∈ {0, …, n-1}` only is licensed by `criterion_periodic`.

The properness conditions `S.card < n`, `T.card < n` are the paper's `S, T ⊊ ℤ/n`. -/
def Additive (S T : Finset (ZMod n)) : Prop :=
  S.card < n ∧ T.card < n ∧
    ∀ k : Fin n, ((k.val : ℤ) : ZMod n) ∈ T →
      uS S (k.val : ℤ) < uS S (firstGap T ((k.val : ℤ) + 1))

instance (S T : Finset (ZMod n)) : Decidable (Additive S T) := by
  unfold Additive; infer_instance

/-! ### `n`-equivariance: the finite quantifier in `Additive` is faithful -/

private lemma cast_add_n (j : ℤ) : ((j + n : ℤ) : ZMod n) = (j : ZMod n) := by
  push_cast
  simp

lemma firstGapAux_periodic (S : Finset (ZMod n)) (j : ℤ) (f : ℕ) :
    firstGapAux S (j + n) f = firstGapAux S j f := by
  induction f generalizing j with
  | zero => rfl
  | succ f ih =>
      have hj : ((j + n : ℤ) : ZMod n) = (j : ZMod n) := cast_add_n j
      have hstep : (j + (n : ℤ) + 1) = (j + 1) + (n : ℤ) := by ring
      simp only [firstGapAux, hj, hstep, ih (j + 1)]

lemma firstGap_periodic (S : Finset (ZMod n)) (j : ℤ) :
    firstGap S (j + n) = firstGap S j + n := by
  simp only [firstGap, firstGapAux_periodic]
  ring

lemma uS_periodic (S : Finset (ZMod n)) (j : ℤ) : uS S (j + n) = uS S j + n := by
  have hc : ((j + (n : ℤ) - 1 : ℤ) : ZMod n) = ((j - 1 : ℤ) : ZMod n) := by
    rw [show (j + (n : ℤ) - 1) = (j - 1) + (n : ℤ) by ring, cast_add_n]
  simp only [uS, hc]
  split
  · ring
  · exact firstGap_periodic S j

/-- The run condition of `lem:add` is invariant under translating the lift by `n`.
This is what licenses `Additive` quantifying over `k : Fin n` instead of over all
runs in `ℤ`. -/
theorem criterion_periodic (S T : Finset (ZMod n)) (j : ℤ) :
    (uS S (j + n) < uS S (firstGap T ((j + n) + 1)))
      ↔ (uS S j < uS S (firstGap T (j + 1))) := by
  have h1 : (j + (n : ℤ)) + 1 = (j + 1) + (n : ℤ) := by ring
  rw [h1, firstGap_periodic, uS_periodic, uS_periodic]
  exact Int.add_lt_add_iff_right _

/-! ### The witnesses

Verified independently against Shi's inversion formula by
`reviews/code-2026-09-22-c2/g1_lemma2.py` (re-run 2026-09-23): at `n = 3` the
hereditary analogue has exactly 9 failing quadruples, the first being
`S = {0}, T = {0,1}, S' = T' = {0}`. -/

/-- `({0}, {0,1})` is additive at `n = 3`. -/
theorem additive_zero_zeroone : Additive ({0} : Finset (ZMod 3)) {0, 1} := by decide

/-- `({0}, {0})` is not additive at `n = 3`: `u_{0} u_{0} = s₀ s₀ = 1`, of length `0 ≠ 2`. -/
theorem not_additive_zero_zero : ¬ Additive ({0} : Finset (ZMod 3)) {0} := by decide

/-- `({0,1}, {1})` is additive at `n = 3`. -/
theorem additive_zeroone_one : Additive ({0, 1} : Finset (ZMod 3)) {1} := by decide

/-- `({1}, {1})` is not additive at `n = 3`. -/
theorem not_additive_one_one : ¬ Additive ({1} : Finset (ZMod 3)) {1} := by decide

/-! ### Milestone A: additivity is not hereditary -/

/-- **Additivity is not hereditary.**  Shrinking `S` and `T` arbitrarily inside an
additive pair can destroy additivity.  Witness `n = 3`, `S = {0}`, `T = {0,1}`,
`S' = {0}`, `T' = {0}`.

This is the statement the session brief called `unbracketed_deletion_false`.  Note
carefully what it does **not** show: in this witness nothing is deleted from `S` at
all, so it says nothing about whether `i + 1 ∈ T` is needed in Q232.  See
`additive_erase_left_not_stable` for the claim that is actually load-bearing, and
§"The bracket hypothesis is not load-bearing" of the Q232 note. -/
theorem additive_not_hereditary :
    ¬ ∀ (n : ℕ) (S T S' T' : Finset (ZMod n)),
        Additive S T → S' ⊆ S → T' ⊆ T → Additive S' T' := by
  intro h
  exact not_additive_zero_zero
    (h 3 {0} {0, 1} {0} {0} additive_zero_zeroone (by decide) (by decide))

/-- **The two deletions must be coupled.**  Deleting `i` from `S` while leaving `T`
alone can destroy additivity: witness `n = 3`, `S = {0,1}`, `T = {1}`, `i = 0`, where
`(S.erase 0, T) = ({1}, {1})` is not additive.

This is the hypothesis that is genuinely load-bearing in the deletion theorem of
`2026-09-23-c1-bracketed-pair-deletion.tex`: the theorem's conclusion is about
`(S \ {i}, T \ {i+1})`, and the deletion of `i+1` from `T` is what kills the one
dangerous case (eq. `notiplus1` of the note).  It is consumed as the *shape of the
conclusion*, not as a hypothesis — which is why the theorem also holds, with an empty
deletion on the right, when `i + 1 ∉ T`. -/
theorem additive_erase_left_not_stable :
    ¬ ∀ (n : ℕ) (S T : Finset (ZMod n)) (i : ZMod n),
        Additive S T → i ∈ S → Additive (S.erase i) T := by
  intro h
  have hx : Additive (({0, 1} : Finset (ZMod 3)).erase 0) {1} :=
    h 3 {0, 1} {1} 0 additive_zeroone_one (by decide)
  rw [show (({0, 1} : Finset (ZMod 3)).erase 0) = {1} by decide] at hx
  exact not_additive_one_one hx

/-! ### Milestone B, finite range: the deletion theorem itself

The Theorem of §"The theorem" of `2026-09-23-c1-bracketed-pair-deletion.tex` states:
if `(S, T)` is additive and `i ∈ S`, then `(S \ {i}, T \ {i+1})` is additive.  Note the
hypothesis `i + 1 ∈ T` of Q232 is **absent** — the paper proves the stronger, uncoupled
statement, and Q232 (`cor:q232`) is the corollary in which `i + 1 ∈ T` is used only to
count, `|T \ {i+1}| = |T| - 1`.

The general-`n` proof is **not** formalised here (see the session note).  What is
machine-checked is the full statement over all of `n = 3`, `n = 4` and `n = 5` — every pair of
subsets and every `i`, by kernel evaluation.  This is a genuine cross-check on the
transport: the paper's census of the same statement was run against Shi's inversion
formula, so agreement here is agreement between two independent implementations of
`ℓ(u_S u_T) = |S| + |T|`. -/

set_option maxRecDepth 1000000 in
/-- The deletion theorem at `n = 3`, exhaustively. -/
theorem deletion_n3 :
    ∀ (S T : Finset (ZMod 3)) (i : ZMod 3),
      Additive S T → i ∈ S → Additive (S.erase i) (T.erase (i + 1)) := by decide

set_option maxRecDepth 1000000 in
/-- The deletion theorem at `n = 4`, exhaustively. -/
theorem deletion_n4 :
    ∀ (S T : Finset (ZMod 4)) (i : ZMod 4),
      Additive S T → i ∈ S → Additive (S.erase i) (T.erase (i + 1)) := by decide

set_option maxRecDepth 4000000 in
/-- The deletion theorem at `n = 5`, exhaustively.  `n = 5` is the first `n` at which
the containment of `ms-crystal-comparison` is strict, so it is the first size at which
the statement is not forced by the smaller cases. -/
theorem deletion_n5 :
    ∀ (S T : Finset (ZMod 5)) (i : ZMod 5),
      Additive S T → i ∈ S → Additive (S.erase i) (T.erase (i + 1)) := by decide

end AffineAdditive
