/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel

/-!
# `lake test` driver: the non-vacuity witnesses, evaluated

Every check below is `#guard` on the *same decidable proposition* as a `by decide` witness
theorem in the library. `#guard p` evaluates `p` by kernel reduction and errors if it is `false`,
so a wrong expected value here fails `lake test`.

## Why this library is not in `defaultTargets`

Because it must be able to fail *alone*. If the test driver were part of the default build,
breaking a check would turn the `build` check red too, and the `test` check would carry no
information beyond it — a detector that can only fire when another has already fired is not a
detector. Kept out of `defaultTargets`, this library is built by `lake test` and by nothing else.

Each check names the theorem it shadows.
-/

open TworowD4Kernel Finset

-- `#guard` is exactly the point of this file; the Mathlib style linter bans `#`-commands in
-- library code, which this is not.
set_option linter.hashCommand false


section WindowBridge

-- Shadows `uglovLabel_injective_nonvacuous`.
#guard decide (uglovLabel (0 : Fin 2) (1 : Fin 3) ≠ uglovLabel (1 : Fin 2) (2 : Fin 3))

-- Shadows `uglovLabel_not_injective_mod_n`: the collision it exhibits really collides ...
#guard decide ((((0 : ℕ) + 2 * (0 : ℕ) : ℕ) : ZMod 2) = (((0 : ℕ) + 2 * (1 : ℕ) : ℕ) : ZMod 2))

-- ... and its two arguments really differ.
#guard decide (((0 : Fin 2), (0 : Fin 3)) ≠ ((0 : Fin 2), (1 : Fin 3)))

end WindowBridge

section AbacusRibbonInverse

-- Shadows `addRibbon_removeRibbon_nonvacuous`.
#guard decide (removeRibbon 3 (addRibbon 3 ({0, 1} : Finset ℤ) 0) 3 = ({0, 1} : Finset ℤ))

-- Shadows `removeRibbon_addRibbon`.
#guard decide (addRibbon 3 (removeRibbon 3 ({3, 1} : Finset ℤ) 3) 0 = ({3, 1} : Finset ℤ))

-- Shadows `addRibbon_mem_self`: the bead really is at `b + e` afterwards.
#guard decide ((3 : ℤ) ∈ addRibbon 3 ({0, 1} : Finset ℤ) 0)

-- Shadows `addRibbon_notMem_self`: and `b` really is vacated.
#guard decide ((0 : ℤ) ∉ addRibbon 3 ({0, 1} : Finset ℤ) 0)

end AbacusRibbonInverse

section AbacusRibbonDirection

-- Shadows `sum_addRibbon_nonvacuous`. **This is the check that would have caught the
-- 2026-09-03 DREAM note**: the bead sum of `{0,1}` is `1`, and adding the `3`-ribbon at `0` takes
-- it to `4`, not to `-2`. The sign of `e` is the direction.
#guard decide ((∑ x ∈ addRibbon 3 ({0, 1} : Finset ℤ) 0, x) = 4)

-- Shadows `sum_removeRibbon`: and removing takes `{3,1}` (sum `4`) back down to sum `1`.
#guard decide ((∑ x ∈ removeRibbon 3 ({3, 1} : Finset ℤ) 3, x) = 1)

end AbacusRibbonDirection

section AbacusRibbonHeight

-- Shadows `ribbonHeight_nonvacuous`: an *intermediate* height, neither `0` nor `e - 1`.
#guard decide (ribbonHeight 3 ({0, 2} : Finset ℤ) 0 = 1)

-- Shadows `ribbonHeight_Ico_nonvacuous`: the upper end `e - 1 = 2` is attained.
-- Written out as `{0,1,2}` rather than `Finset.Ico (0 : ℤ) 3` because `#guard` *compiles* its
-- argument, and the `LocallyFiniteOrder ℤ` instance is noncomputable in Mathlib v4.30.0
-- (kernel reduction inside `decide` is fine, native compilation is not). The two are the same
-- Finset, and that is itself checked here rather than asserted:
example : Finset.Ico (0 : ℤ) 3 = ({0, 1, 2} : Finset ℤ) := by decide
#guard decide (ribbonHeight 3 ({0, 1, 2} : Finset ℤ) 0 = 2)

-- Shadows `ribbonHeight_singleton`: the lower end `0` is attained.
#guard decide (ribbonHeight 3 ({0} : Finset ℤ) 0 = 0)

-- Shadows `ribbonHeight_addRibbon`: the height survives the move.
#guard decide (ribbonHeight 3 (addRibbon 3 ({0, 2} : Finset ℤ) 0) 0
  = ribbonHeight 3 ({0, 2} : Finset ℤ) 0)

end AbacusRibbonHeight

section NegativeControl

-- Shadows `addRibbon_collision`: with the side condition `b + e ∉ M` dropped, the two beads
-- collide and the round trip lands on `{0}`.
#guard decide (removeRibbon 2 (addRibbon 2 ({0, 2} : Finset ℤ) 0) 2 = ({0} : Finset ℤ))

-- Shadows `exists_addRibbon_not_removeRibbon_of_mem`: so it is *not* the identity.
#guard decide (removeRibbon 2 (addRibbon 2 ({0, 2} : Finset ℤ) 0) 2 ≠ ({0, 2} : Finset ℤ))

end NegativeControl

section Maya

/-! `Maya.size` is **noncomputable** — `wt` decides set membership through
`Classical.propDecidable` — and `#guard` *compiles* its argument, so the checks in this section
cannot be `#guard`s. They are statement-pinning `example`s instead: each restates the numeral a
library theorem claims and discharges it by that theorem, so editing the numeral in the library
breaks `lake test` here. This is a weaker detector than the `#guard`s above and is labelled as
such: it detects a changed *statement*, not a changed *value*. -/

-- Shadows `Maya.size_nil`: the vacuum has size `0`.
example : Maya.nil.size = 0 := Maya.size_nil

-- Shadows `Maya.size_onebox`: regime 1, the bead crosses the vacuum line. `|(1)| = 1`.
example : Maya.onebox.size = 1 := Maya.size_onebox

-- Shadows `Maya.size_addRibbon_above`: regime 2, entirely above the line. `1 + 2 = 3`.
example : (Maya.onebox.addRibbon 2 0).size = 3 := Maya.size_addRibbon_above

-- Shadows `Maya.size_addRibbon_below`: regime 3, entirely below the line. `1 + 2 = 3`.
example : (Maya.onebox.addRibbon 2 (-3)).size = 3 := Maya.size_addRibbon_below

-- Shadows `Maya.exists_size_addRibbon_ne_of_mem`: the negative control. Dropping `b + e ∉ M`
-- makes the size theorem false, so the hypothesis is load-bearing.
example : ∃ (e : ℕ) (M : Maya) (b : ℤ), 0 < e ∧ b ∈ M.carrier ∧ b + (e : ℤ) ∈ M.carrier ∧
    (M.addRibbon e b).size ≠ M.size + (e : ℤ) := Maya.exists_size_addRibbon_ne_of_mem

end Maya

section SignedCount

/-! `signedSubsetCount` is **computable** — `Finset.Ico` on `ℕ`, `powerset` and `card` all reduce
— so unlike the `Maya` section these are genuine `#guard`s on values, not statement pins. -/

-- Shadows `signedSubsetCount_eq_zero`: the vanishing branch, `m ≤ k - 2`.
#guard decide (signedSubsetCount 5 0 = 0)
#guard decide (signedSubsetCount 5 2 = 0)
#guard decide (signedSubsetCount 5 3 = 0)
#guard decide (signedSubsetCount 7 1 = 0)

-- Shadows `signedSubsetCount_of_succ` / `signedSubsetCount_pred`: `m = k - 1` gives `-1`,
-- the single term `T = ∅`. This is the boundary the paper's prose elides.
#guard decide (signedSubsetCount 5 4 = -1)
#guard decide (signedSubsetCount 1 0 = -1)
#guard decide (signedSubsetCount 7 6 = -1)

-- Shadows `signedSubsetCount_self`: **the sum model returns `-1` at `m = k`, not the paper's
-- `+1`.** If this ever evaluates to `1`, the `m < k` hypothesis has been wrongly dropped.
#guard decide (signedSubsetCount 5 5 = -1)

-- Shadows `signedSubsetCount_eq_neg_zero_pow`: the closed form under `0 ^ 0 = 1`, checked
-- against the sum on both sides of the boundary.
#guard decide (signedSubsetCount 6 4 = -(0 : ℤ) ^ (6 - 1 - 4))
#guard decide (signedSubsetCount 6 5 = -(0 : ℤ) ^ (6 - 1 - 5))

end SignedCount


section PrefixSignSum

/-! `prefixSignSum` is **computable** by construction — `ascList` is `List.range` filtered, not
`Finset.sort`, precisely so that the kernel and the evaluator can both run it. `k = 3,4,5` are
also `decide`-proved in the library; `k = 6,7` are here only, because `decide` blows
`maxRecDepth` on 64 subsets while the compiled evaluator does not. -/

-- Shadows `prefixSignSum_eq_three` / `_four` / `_five`: no nonempty `S̄ ⊆ [k]` disagrees with
-- `prop:N`. The empty counterexample set is the assertion.
#guard ((Icc 1 3).powerset.filter
  (fun S => S ≠ ∅ ∧ prefixSignSum 3 S ≠ prefixSignSumRHS 3 S)) = ∅
#guard ((Icc 1 4).powerset.filter
  (fun S => S ≠ ∅ ∧ prefixSignSum 4 S ≠ prefixSignSumRHS 4 S)) = ∅
#guard ((Icc 1 5).powerset.filter
  (fun S => S ≠ ∅ ∧ prefixSignSum 5 S ≠ prefixSignSumRHS 5 S)) = ∅

-- Beyond what `decide` can reach in the library.
#guard ((Icc 1 6).powerset.filter
  (fun S => S ≠ ∅ ∧ prefixSignSum 6 S ≠ prefixSignSumRHS 6 S)) = ∅
#guard ((Icc 1 7).powerset.filter
  (fun S => S ≠ ∅ ∧ prefixSignSum 7 S ≠ prefixSignSumRHS 7 S)) = ∅

/-! The three branches of `prop:N` at `k = 4`, on named values rather than on a quantifier, so
that a wrong *sign convention* — not just a wrong theorem — fails `lake test`. -/

-- Branch 1: `k-1 ∈ S̄`, `k ∉ S̄`, value `(-1)^|S̄|`.
#guard decide (prefixSignSum 4 {3} = -1)
#guard decide (prefixSignSum 4 {1, 3} = 1)

-- Branch 2: `k ∈ S̄`, `k-1 ∉ S̄`, value `(-1)^(|S̄|-1)`.
#guard decide (prefixSignSum 4 {4} = 1)
#guard decide (prefixSignSum 4 {1, 4} = -1)

-- Branch 3, THE VANISHING BRANCH — both of `k-1, k`, and neither. A lemma whose only tests are
-- nonzero has not tested the case that carries the theorem.
#guard decide (prefixSignSum 4 {3, 4} = 0)
#guard decide (prefixSignSum 4 {1, 2} = 0)
#guard decide (prefixSignSum 4 {1, 2, 3, 4} = 0)

-- Shadows `rho_getElem_peak`: the peak really is at index `|T|`, so `q = |T| + 1` and the
-- source's `(-1)^(q-1)` is `wordSign T`. `ρ_{{1,3}} = [1,3,4,2]` for `k = 4`.
#guard decide (rho 4 {1, 3} = [1, 3, 4, 2])
#guard decide (rho 4 ∅ = [4, 3, 2, 1])
#guard decide (rho 4 {1, 2, 3} = [1, 2, 3, 4])
#guard ((Icc 1 5).powerset.filter (fun T => (rho 6 T)[T.card]? ≠ some 6)) = ∅

end PrefixSignSum
