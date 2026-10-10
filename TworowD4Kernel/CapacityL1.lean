/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The capacity lemma: a signed monomial weight cannot create objects

Formalisation of `lem:cap` of
`projects/proofs/2026-10-10-Q405-twisted-trace-cylindric-statistic.tex`.

The informal statement is about cylindric tableaux, but it mentions no cylindric geometry
at all.  Stripped to its content it says: *a sum of signs indexed by a finite set, pushed
forward along an arbitrary statistic to `ℕ`, has `ℓ¹`-norm at most the size of the set.*
A monomial weight can only **redistribute** objects among powers of `t`; it cannot create
them.

The external input being bounded is Huh--Kim--Krattenthaler--Okada, Theorem 3.3
(arXiv:2301.13117); the witness polynomial comes from `thm:main` of the proof note above.
-/

namespace TworowD4Kernel.Capacity

open Finset

variable {ι : Type*}

/-! ### The fibre count

Everything below is this one inequality in different clothing: the fibres of `stat` over
distinct values are disjoint subsets of `S`, so their sizes sum to at most `#S`. -/

/-- The fibres of `stat` over a finite set `E` of values have total size at most `#S`.
This is the entire content of the capacity lemma; the sign bookkeeping is cosmetic. -/
theorem sum_card_fiber_le (S : Finset ι) (stat : ι → ℕ) (E : Finset ℕ) :
    ∑ e ∈ E, (S.filter fun i => stat i = e).card ≤ S.card := by
  classical
  -- Restrict to the elements whose statistic actually lands in `E`, where the fibre
  -- decomposition is an *equality*, then forget the restriction.
  set S' : Finset ι := S.filter fun i => stat i ∈ E with hS'
  have hfib : S'.card = ∑ e ∈ E, (S'.filter fun i => stat i = e).card :=
    Finset.card_eq_sum_card_fiberwise (f := stat) (by intro x hx; simpa [hS'] using
      (Finset.mem_filter.mp hx).2)
  have hrestrict : ∀ e ∈ E, (S'.filter fun i => stat i = e)
      = S.filter fun i => stat i = e := by
    intro e he
    ext i
    simp only [hS', Finset.mem_filter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ he⟩, h.2⟩⟩
  calc ∑ e ∈ E, (S.filter fun i => stat i = e).card
      = ∑ e ∈ E, (S'.filter fun i => stat i = e).card :=
        Finset.sum_congr rfl fun e he => by rw [hrestrict e he]
    _ = S'.card := hfib.symm
    _ ≤ S.card := by simpa [hS'] using Finset.card_filter_le S (fun i => stat i ∈ E)

/-! ### Part (2): the signed bound

`lem:cap`(2).  If `(S^±)` holds then `‖c_α‖₁ ≤ TOT_α`.

Stated with `|ε i| ≤ 1` rather than `ε i = 1 ∨ ε i = -1`: that is what the proof uses, it
is strictly more general, and it makes the lemma reusable for weights that are allowed to
vanish. -/

/-- **Capacity lemma, signed form.**  If each `c e` is a sum of weights of absolute value
at most one over the fibre `stat⁻¹(e) ∩ S`, then the `ℓ¹`-norm of `c` over any finite set
of exponents is at most `#S`. -/
theorem l1_le_card (S : Finset ι) (ε : ι → ℤ) (stat : ι → ℕ) (c : ℕ → ℤ) (E : Finset ℕ)
    (hε : ∀ i ∈ S, |ε i| ≤ 1)
    (hc : ∀ e, c e = ∑ i ∈ S.filter fun i => stat i = e, ε i) :
    ∑ e ∈ E, |c e| ≤ (S.card : ℤ) := by
  classical
  calc ∑ e ∈ E, |c e|
      ≤ ∑ e ∈ E, ((S.filter fun i => stat i = e).card : ℤ) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [hc e]
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i ∈ S.filter fun i => stat i = e, |ε i|
            ≤ ∑ _i ∈ S.filter fun i => stat i = e, (1 : ℤ) :=
              Finset.sum_le_sum fun i hi => hε i (Finset.mem_of_mem_filter i hi)
          _ = ((S.filter fun i => stat i = e).card : ℤ) := by simp
    _ = ((∑ e ∈ E, (S.filter fun i => stat i = e).card : ℕ) : ℤ) := by push_cast; ring
    _ ≤ (S.card : ℤ) := by exact_mod_cast sum_card_fiber_le S stat E

/-! ### Part (1): the two one-sided bounds

`lem:cap`(1).  If `(S)` holds then `∑ₑ max([tᵉ]c_α, 0) ≤ A_α` and
`∑ₑ max(-[tᵉ]c_α, 0) ≤ B_α`.

Here `A` is the set of objects carrying sign `+1` and `B` the set carrying `-1`; the two
sets play symmetric roles and are *not* assumed disjoint, since the bound does not need
it. -/

/-- **Capacity lemma, unsigned form, positive part.** -/
theorem sum_posPart_le_card (A B : Finset ι) (stat : ι → ℕ) (c : ℕ → ℤ) (E : Finset ℕ)
    (hc : ∀ e, c e = ((A.filter fun i => stat i = e).card : ℤ)
                     - ((B.filter fun i => stat i = e).card : ℤ)) :
    ∑ e ∈ E, max (c e) 0 ≤ (A.card : ℤ) := by
  classical
  calc ∑ e ∈ E, max (c e) 0
      ≤ ∑ e ∈ E, ((A.filter fun i => stat i = e).card : ℤ) := by
        refine Finset.sum_le_sum fun e _ => ?_
        rw [hc e]
        have hB : (0 : ℤ) ≤ ((B.filter fun i => stat i = e).card : ℤ) := by positivity
        have hA : (0 : ℤ) ≤ ((A.filter fun i => stat i = e).card : ℤ) := by positivity
        exact max_le (by linarith) hA
    _ = ((∑ e ∈ E, (A.filter fun i => stat i = e).card : ℕ) : ℤ) := by push_cast; ring
    _ ≤ (A.card : ℤ) := by exact_mod_cast sum_card_fiber_le A stat E

/-- **Capacity lemma, unsigned form, negative part.**  The mirror of
`sum_posPart_le_card` under swapping the two sign classes. -/
theorem sum_negPart_le_card (A B : Finset ι) (stat : ι → ℕ) (c : ℕ → ℤ) (E : Finset ℕ)
    (hc : ∀ e, c e = ((A.filter fun i => stat i = e).card : ℤ)
                     - ((B.filter fun i => stat i = e).card : ℤ)) :
    ∑ e ∈ E, max (-c e) 0 ≤ (B.card : ℤ) :=
  sum_posPart_le_card B A stat (fun e => -c e) E (fun e => by change -c e = _; rw [hc e]; ring)

/-! ### The witness: `(S^±)` fails at `ℓ = 0`

`thm:main` Step 4 of the proof note.  At `(k,ℓ,n) = (1,0,4)`, content `α = (1⁴)`, the
coefficient is `c_α(t) = 2 - 3t + t³`, and the two shapes of size `4` in `Par(2,2)` are
`(2,2)` and `(3,1)`, so `TOT_α = A_α + B_α = 2 + 2 = 4`.  But `‖c_α‖₁ = 2 + 3 + 1 = 6 > 4`.

Hence no signed monomial statistic on cylindric tableaux exists for Warnaar's conjecture
`(Eq_PCn)`: Huh--Kim--Krattenthaler--Okada Theorem 3.3 (arXiv:2301.13117) with
`t^(stat T)` inserted cannot hold for *any* statistic `stat`. -/

/-- The coefficient polynomial `c_α(t) = 2 - 3t + t³` of `thm:main` at `M = 2`,
as a function `ℕ → ℤ` on exponents. -/
def witnessM2 : ℕ → ℤ := fun e => if e = 0 then 2 else if e = 1 then -3 else if e = 3 then 1 else 0

/-- **The obstruction.**  There is no set of `4` objects, no sign function of absolute value
at most one, and no statistic, whose signed fibre sums reproduce `2 - 3t + t³`.

The `4` is `TOT_α`, the total number of cylindric tableaux of content `(1⁴)` at
`(k,ℓ,n) = (1,0,4)`; the polynomial is the coefficient HKKO's theorem forces.  Since
`‖2 - 3t + t³‖₁ = 6 > 4`, `Capacity.l1_le_card` closes it. -/
theorem no_signed_statistic_M2 (S : Finset ι) (ε : ι → ℤ) (stat : ι → ℕ)
    (hcard : S.card = 4) (hε : ∀ i ∈ S, |ε i| ≤ 1)
    (hc : ∀ e, witnessM2 e = ∑ i ∈ S.filter fun i => stat i = e, ε i) : False := by
  have h := l1_le_card S ε stat witnessM2 {0, 1, 3} hε hc
  rw [hcard] at h
  norm_num [witnessM2, Finset.sum_insert, Finset.mem_insert] at h

/-! ### The strict form fails uniformly in `ℓ`

`thm:main` Step 3.  This is the statement that *is* uniform in `ℓ`: with
`M = m + 2 ≥ 2`, the coefficient of `t^(M-1)` is `-(2M-1)` while only `B_α = 2M-2`
objects carry the sign `-1`, so the deficit is exactly `1` at every `ℓ`.

Note this is part (1) of the capacity lemma, not part (2).  Part (2)'s gap is **not**
uniform: see the caveat at the end of this file. -/

/-- **The strict obstruction, uniformly in `ℓ`.**  If the coefficient of `t^(m+1)` is
`-(2m+3)` but only `2m+2` objects carry negative sign, the unsigned capacity bound is
violated.  Here `M = m + 2`, so this covers every `M ≥ 2`, i.e. every `ℓ ≥ 0`. -/
theorem no_strict_statistic (m : ℕ) (A B : Finset ι) (stat : ι → ℕ) (c : ℕ → ℤ)
    (hc : ∀ e, c e = ((A.filter fun i => stat i = e).card : ℤ)
                     - ((B.filter fun i => stat i = e).card : ℤ))
    (hB : B.card = 2 * m + 2) (hval : c (m + 1) = -(2 * m + 3)) : False := by
  have key : -c (m + 1) ≤ (B.card : ℤ) := by
    have h := sum_negPart_le_card A B stat c {m + 1} hc
    rw [Finset.sum_singleton] at h
    exact le_trans (le_max_left _ _) h
  rw [hval, hB] at key
  push_cast at key
  linarith

/-! ### Caveat: the bound is *not* uniform in `ℓ` for the signed form

The session brief asserted that the signed gap is "exactly `2` for every `M ≥ 2`", on the
arithmetic `‖c_α‖₁ = C_M + 2M` against `TOT_α = C_M + 2M - 2`.  The arithmetic is right but
the second quantity is `A_α + B_α`, **not** `TOT_α`.  They agree only at `M = 2`, where no
shape of size `4` in `Par(2,2)` has `c⁻ = 0`.  For `M ≥ 3` the intermediate even endpoints
`d = 2, 4, …, w-2` contribute shapes with `c⁻ = 0`, invisible to HKKO Theorem 3.3, and
`TOT_α` outgrows `A_α + B_α`: at `M = 3` one has `TOT_α = 18` against `‖c_α‖₁ = 11`, so the
capacity inequality is *satisfied* and `l1_le_card` yields nothing.

So `no_signed_statistic_M2` is sharp: `ℓ = 0` is the only place the signed form bites.
The uniform-in-`ℓ` statement is `no_strict_statistic` above, which uses part (1). -/

/-- At `M = 3` the signed capacity bound is satisfied, so no obstruction follows:
`‖c_α‖₁ = C₃ + 2·3 = 5 + 5 + 1 = 11` against `TOT_α = 18`. -/
example : (5 : ℤ) + 5 + 1 ≤ 18 := by norm_num

end TworowD4Kernel.Capacity
