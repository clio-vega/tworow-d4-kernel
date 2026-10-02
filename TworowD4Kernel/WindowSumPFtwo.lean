/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic
import TworowD4Kernel.Convolution

/-!
# The sliding-window sum of a `PF₂` sequence: the shift identity, and what it does not prove

This file works on `prop:regI` of `proofs/2026-09-30-c1-cylindric-kostka-logconcavity.tex`
(the paper's remaining unformalised proposition), via the reduction already proved in
`TworowD4Kernel.Convolution`: `conv_ind_left` says that convolving against an interval
indicator *is* a sliding window sum of constant width (`conv_ind_left_window_card`), so the
statement a Lean `prop:regI` needs is

  *a sliding window sum of a `PF₂` sequence is `PF₂`*.

## Which route, and why

Two routes were on the table at the start of this session.

* **(a) Composition.** Registry node `pf2-convolution` of
  `proofs/registry/cylindric-lorentzian.json` composed with `conv_ind_left`.
  **Not available in Lean.**  That node's `trust` is
  `proved` — a *paper* proof, via `T(f*g) = T(f) T(g)` on bi-infinite Toeplitz matrices plus
  Cauchy–Binet (classically Hoggar, arXiv:1906.09633), and its own text ends "This node itself
  remains trust=proved (paper proof), not lean-verified."  There is no Lean declaration
  asserting closure of `PF₂` under convolution anywhere in this development, so there is
  nothing for `conv_ind_left` to compose *with*.  Route (a) is not a short composition; it is
  the formalisation of Toeplitz matrices and Cauchy–Binet.
* **(b) The direct identity.**  Taken here, as far as it goes — which is not all the way, and
  the second half of this file is the proof that it does not go all the way.

## What is proved here

`winSum_pred` / `winSum_succ` — the two window-shift identities — and `winSum_sq_sub`, the
algebraic identity that `Convolution.lean` states in a comment and that the whole of route (b)
rests on.  It was an unverified comment until now; it is a theorem now.

## What is refuted here

`windowEnd_inequalities_insufficient`.  The registry node records the live worry that route
(b)'s two extra inequalities "may be true, provable and entirely surplus".  They are not
surplus — they are **insufficient**.  See the docstring there.

`prop:regI` itself is **not** formalised in this file, and **not** refuted: see
`regI_not_refuted_here`.
-/

namespace TworowD4Kernel.WindowSumPFtwo

open TworowD4Kernel.DiscreteConcavity TworowD4Kernel.Convolution

/-- The sliding window sum of width `B - A + 1`, i.e. `(1_[A,B] * w) (s)` by
`Convolution.conv_ind_left`. -/
noncomputable def winSum (A B : ℤ) (w : ℤ → ℤ) (s : ℤ) : ℤ :=
  ∑ x ∈ Finset.Icc (s - B) (s - A), w x

/-- `winSum` is the convolution of `Convolution.conv` against an interval indicator.  This is
the only place the two notions are tied together; everything below is about `winSum`. -/
theorem winSum_eq_conv (A B : ℤ) (w : ℤ → ℤ) (s : ℤ) :
    winSum A B w s = conv (ind A B) w s := (conv_ind_left A B w s).symm

/-! ### The two window-shift identities

Peeling one endpoint off an `Finset.Icc`.  Both are stated for `L ≤ R`, which for the window
`[s-B, s-A]` is exactly `A ≤ B`, i.e. the window is nonempty. -/

/-- Peel the bottom element off `Icc L R`. -/
private theorem sum_Icc_peel_bot {L R : ℤ} (hLR : L ≤ R) (w : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc L R, w x = w L + ∑ x ∈ Finset.Icc (L + 1) R, w x := by
  have h : Finset.Icc L R = insert L (Finset.Icc (L + 1) R) := by
    ext y; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]

/-- Peel the top element off `Icc L (R+1)`. -/
private theorem sum_Icc_peel_top {L R : ℤ} (hLR : L ≤ R + 1) (w : ℤ → ℤ) :
    ∑ x ∈ Finset.Icc L (R + 1), w x = (∑ x ∈ Finset.Icc L R, w x) + w (R + 1) := by
  have h : Finset.Icc L (R + 1) = insert (R + 1) (Finset.Icc L R) := by
    ext y; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [h, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega), add_comm]

/-- Shift the window down by one: the generic `Icc` form, with `L = s-B`, `R = s-A`. -/
private theorem winSum_shift_down {L R : ℤ} (hLR : L ≤ R) (w : ℤ → ℤ) :
    (∑ x ∈ Finset.Icc (L - 1) (R - 1), w x)
      = (∑ x ∈ Finset.Icc L R, w x) + w (L - 1) - w R := by
  have hb := sum_Icc_peel_bot (L := L - 1) (R := R - 1) (by omega) w
  rw [show L - 1 + 1 = L from by ring] at hb
  have ht := sum_Icc_peel_top (L := L) (R := R - 1) (by omega) w
  rw [show R - 1 + 1 = R from by ring] at ht
  rw [hb, ht]; ring

/-- Shift the window up by one: the generic `Icc` form. -/
private theorem winSum_shift_up {L R : ℤ} (hLR : L ≤ R) (w : ℤ → ℤ) :
    (∑ x ∈ Finset.Icc (L + 1) (R + 1), w x)
      = (∑ x ∈ Finset.Icc L R, w x) - w L + w (R + 1) := by
  have ht := sum_Icc_peel_top (L := L + 1) (R := R) (by omega) w
  have hb := sum_Icc_peel_bot (L := L) (R := R) hLR w
  rw [ht, hb]; ring

/-- **Window shift down.**  `W (s-1) = W (s) + α - γ`, where `α = w (s-1-B)` is the site the
window gains on the left and `γ = w (s-A)` the site it loses on the right. -/
theorem winSum_pred (A B : ℤ) (hAB : A ≤ B) (w : ℤ → ℤ) (s : ℤ) :
    winSum A B w (s - 1) = winSum A B w s + w (s - 1 - B) - w (s - A) := by
  simp only [winSum]
  rw [show s - 1 - B = s - B - 1 from by ring, show s - 1 - A = s - A - 1 from by ring]
  exact winSum_shift_down (L := s - B) (R := s - A) (by omega) w

/-- **Window shift up.**  `W (s+1) = W (s) - β + δ`, where `β = w (s-B)` is the site the window
loses on the left and `δ = w (s-A+1)` the site it gains on the right. -/
theorem winSum_succ (A B : ℤ) (hAB : A ≤ B) (w : ℤ → ℤ) (s : ℤ) :
    winSum A B w (s + 1) = winSum A B w s - w (s - B) + w (s - A + 1) := by
  simp only [winSum]
  rw [show s + 1 - B = s - B + 1 from by ring, show s + 1 - A = s - A + 1 from by ring]
  exact winSum_shift_up (L := s - B) (R := s - A) (by omega) w

/-! ### The identity route (b) rests on -/

/-- **The obstruction identity.**  With
`α = w (s-1-B)`, `β = w (s-B)`, `γ = w (s-A)`, `δ = w (s-A+1)` — so `β, γ` are the two ends of
the window at `s`, and `α, δ` the two sites just outside it —

  `W s ^ 2 - W (s-1) * W (s+1) = W s * (β + γ - α - δ) + (α - γ) * (β - δ)`.

`Convolution.lean`'s scope note states this in prose, as the algebra a later session has to
supply; it was an unverified comment until this declaration. -/
theorem winSum_sq_sub (A B : ℤ) (hAB : A ≤ B) (w : ℤ → ℤ) (s : ℤ) :
    winSum A B w s ^ 2 - winSum A B w (s - 1) * winSum A B w (s + 1)
      = winSum A B w s * (w (s - B) + w (s - A) - w (s - 1 - B) - w (s - A + 1))
        + (w (s - 1 - B) - w (s - A)) * (w (s - B) - w (s - A + 1)) := by
  rw [winSum_pred A B hAB w s, winSum_succ A B hAB w s]; ring

/-- Sanity check on the identity, not a proof of anything: at window width `1` (`A = B`) the two
ends coincide (`β = γ`) and the identity degenerates to `γ ^ 2 - α * δ`, exactly log-concavity
of `w`.  This is the width-`1` check recorded in the registry node. -/
theorem winSum_sq_sub_width_one (A : ℤ) (w : ℤ → ℤ) (s : ℤ) :
    winSum A A w s ^ 2 - winSum A A w (s - 1) * winSum A A w (s + 1)
      = w (s - A) ^ 2 - w (s - 1 - A) * w (s - A + 1) := by
  have hw : ∀ t : ℤ, winSum A A w t = w (t - A) := by
    intro t; simp only [winSum, Finset.Icc_self, Finset.sum_singleton]
  simp only [hw]
  rw [show s + 1 - A = s - A + 1 from by ring]

/-! ### The scope result: route (b)'s two inequalities are insufficient, not surplus -/

/-- **The two extra inequalities of route (b) do not imply the conclusion.**

The registry node `pf2-convolution` records the worry that route (b)'s two extra inequalities —

* `β * γ ≥ α * δ`, the monotone-ratio form of `PF₂` read at the two window ends, and
* `W s ≥ β + γ`, that the window carries both of its own ends —

"may be true, provable and entirely surplus".  That is the wrong worry.  Together with
nonnegativity of all four window-end values, of `W s`, **and** of both neighbouring window sums
`W (s±1)`, they still do not give `W s ^ 2 ≥ W (s-1) * W (s+1)`.

Witness `(α, β, γ, δ, S) = (10, 1, 1, 0, 2)`: then `β * γ = 1 ≥ 0 = α * δ`, `β + γ = 2 ≤ 2 = S`,
`W (s-1) = S + α - γ = 11 ≥ 0` and `W (s+1) = S - β + δ = 1 ≥ 0`, while
`S ^ 2 = 4 < 11 = W (s-1) * W (s+1)`.  The identity's right-hand side reads
`2 * (1 + 1 - 10 - 0) + (10 - 1) * (1 - 0) = -16 + 9 = -7`.

So any proof of `prop:regI` along route (b) must use more of the window than its two ends and
its total — and in particular, formalising these two inequalities on their own would have been
work spent on a hypothesis set that cannot close the goal. -/
theorem windowEnd_inequalities_insufficient :
    ∃ α β γ δ S : ℤ,
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧ 0 ≤ S ∧
      α * δ ≤ β * γ ∧
      β + γ ≤ S ∧
      0 ≤ S + α - γ ∧ 0 ≤ S - β + δ ∧
      S ^ 2 < (S + α - γ) * (S - β + δ) :=
  ⟨10, 1, 1, 0, 2, by norm_num⟩

/-- The same witness, read through the identity of `winSum_sq_sub`: its right-hand side is
`-7 < 0` there.  Stated separately so that the refutation is visibly about the *identity's*
right-hand side and not only about an inequality between products. -/
theorem windowEnd_identity_rhs_negative :
    ∃ α β γ δ S : ℤ,
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ 0 ≤ δ ∧ 0 ≤ S ∧ α * δ ≤ β * γ ∧ β + γ ≤ S ∧
      S * (β + γ - α - δ) + (α - γ) * (β - δ) < 0 :=
  ⟨10, 1, 1, 0, 2, by norm_num⟩

/-! ### `prop:regI` is not refuted here

`windowEnd_inequalities_insufficient` is a statement about a *hypothesis set*, not about
`prop:regI`.  The witness `(α, β, γ, δ, S) = (10, 1, 1, 0, 2)` is **not** realisable by an
actual `PF₂` sequence `w`, and the obstruction is instructive — it is exactly the information
route (b) discards.  Over `ℤ`, `β / α = 1 / 10` forces every later ratio of `w` to be at most
`1 / 10` (monotone ratios), so `w (s - B + 1) ≤ 0`, hence `= 0` by nonnegativity; interval
support then forces `w` to vanish at every site to the right, so `γ = w (s - A) = 0` unless the
window has width `1`.  At width `1` the ends coincide, `β = γ = 1` and `S = 1`, which violates
`β + γ ≤ S`.  Either way the witness dies — but it dies by an argument about the *interior* of
the window and the *global* monotonicity of the ratio sequence, neither of which appears in
route (b)'s two inequalities.

So this file leaves `prop:regI` open, with its status sharpened rather than advanced:
route (a) needs Toeplitz + Cauchy–Binet, and route (b) needs a hypothesis that sees the window
interior.  No `sorry` is used to stand in for either; nothing here asserts `prop:regI`. -/
theorem regI_not_refuted_here : True := trivial

end TworowD4Kernel.WindowSumPFtwo

/-! ### Axiom audit -/

section Audit
open TworowD4Kernel.WindowSumPFtwo
#print axioms winSum_eq_conv
#print axioms winSum_pred
#print axioms winSum_succ
#print axioms winSum_sq_sub
#print axioms winSum_sq_sub_width_one
#print axioms windowEnd_inequalities_insufficient
#print axioms windowEnd_identity_rhs_negative
end Audit
