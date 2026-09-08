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

/-! ## The general-`k` `prop:N` (2026-09-07)

`prefixSignSum_eq` is proved for all `k ≥ 2`, so the `#guard`s above are no longer the only
evidence at `k = 6,7`. What still needs testing is the *new definition* the Lean proof
introduces: `topBlock`, which replaces the source's `Y = (m*, k-1]`, `m* = max([k-1] \ S̄₀)`
with the convention `m* := 0` when that set is empty. A definition of mine is a primary source
and gets its own warrant — so assert the two agree, on every `S̄₀`, including the empty-`m*` and
empty-`Y` cases the convention exists to paper over. -/

-- The source's `Y`, transcribed literally, `max` convention and all.
private def topBlockPaper (k : ℕ) (S₀ : Finset ℕ) : Finset ℕ :=
  Ioc ((Icc 1 (k - 1) \ S₀).max.getD 0) (k - 1)

#guard ((Icc 1 5).powerset.filter (fun S₀ => topBlock 6 S₀ ≠ topBlockPaper 6 S₀)) = ∅
#guard ((Icc 1 6).powerset.filter (fun S₀ => topBlock 7 S₀ ≠ topBlockPaper 7 S₀)) = ∅
-- `k = 2`: `[k-1] = {1}`, so `S₀ = ∅` gives `m* = 1`, `Y = ∅`, and `S₀ = {1}` gives `m* = 0`,
-- `Y = {1}`. Both extremes of the convention, at the smallest `k` the theorem claims.
#guard decide (topBlock 2 ∅ = (∅ : Finset ℕ))
#guard decide (topBlock 2 {1} = ({1} : Finset ℕ))

-- Shadows `topBlock_eq_empty_iff`: emptiness of `Y` is exactly `k-1 ∉ S̄₀`.
#guard ((Icc 1 5).powerset.filter
  (fun S₀ => (topBlock 6 S₀ = ∅) ≠ (5 ∉ S₀))) = ∅

end PrefixSignSum

/-! ## The one-bead matrix element of `R_f R_e` (2026-09-07)

Independent kernel cross-checks of `TworowD4Kernel.matrixElem_one_bead` and its commutator
corollary — evaluated route sets and weights, **not** a reproof. Two instances, chosen so the
route population varies: the first has both routes present, the second has both absent in one
order and both present in the other. A check that could not distinguish those two would be
constant in the direction it tests.

Instance 1: `e = 2`, `f = 3`, `M = {0,3,4}`, `b = 0`, so `b+e+f = 5 ∉ M`, `M' = {3,4,5}`.
`m(b+e) = m(2) = 0` (route B present), `m(b+f) = m(3) = 1` (route C present), `N = 2`. -/
section CrossRankOneBead

private def M₁ : Finset ℤ := {0, 3, 4}
private def M₁' : Finset ℤ := addRibbon (2 + 3) M₁ 0

#guard decide (M₁' = ({3, 4, 5} : Finset ℤ))
#guard decide (ribbonHeight (2 + 3) M₁ 0 = 2)
-- Route B `(b, b+e) = (0,2)` and route C `(b+f, b) = (3,0)`, and nothing else.
#guard decide (routes 2 3 M₁ M₁' = ({(0, 2), (3, 0)} : Finset (ℤ × ℤ)))
-- The two weights: `N` and `N - 1`. This is the pair the window lemmas compute.
#guard decide (routeWeight 2 3 M₁ 0 2 = 2)
#guard decide (routeWeight 2 3 M₁ 3 0 = 1)
-- `⟨M'|R_f R_e|M⟩ = (1-0) t² + 1·t¹`, evaluated at `t = 3`: `9 + 3 = 12`.
#guard decide (matrixElem 2 3 M₁ M₁' (3 : ℤ) = 12)
-- `⟨M'|R_e R_f|M⟩ = (1-1) t² + 0·t¹ = 0`.
#guard decide (matrixElem 3 2 M₁ M₁' (3 : ℤ) = 0)
-- The commutator, and `1 + t = 4` dividing it: `-12 = -3 * 4`.
#guard decide (matrixElem 3 2 M₁ M₁' (3 : ℤ) - matrixElem 2 3 M₁ M₁' (3 : ℤ) = -12)

/-! Instance 2: `e = 1`, `f = 2`, `M = {0,1}`, `b = 0`, so `b+e+f = 3 ∉ M`, `M' = {1,3}`.
Now `m(b+e) = m(1) = 1` and `m(b+f) = m(2) = 0`, so **both routes are absent** in the order
`R_f R_e` and both are present in the order `R_e R_f`. `N = 1`, so the `t^(N-1) = t^0` term is
the one that would expose an off-by-one in the interval convention. -/
private def M₂ : Finset ℤ := {0, 1}
private def M₂' : Finset ℤ := addRibbon (1 + 2) M₂ 0

#guard decide (M₂' = ({1, 3} : Finset ℤ))
#guard decide (ribbonHeight (1 + 2) M₂ 0 = 1)
#guard decide (routes 1 2 M₂ M₂' = (∅ : Finset (ℤ × ℤ)))
#guard decide (routes 2 1 M₂ M₂' = ({(0, 2), (1, 0)} : Finset (ℤ × ℤ)))
#guard decide (matrixElem 1 2 M₂ M₂' (3 : ℤ) = 0)
-- `t¹ + t⁰ = 3 + 1 = 4` at `t = 3`; the `t⁰` summand is route C's `t^(N-1)`.
#guard decide (matrixElem 2 1 M₂ M₂' (3 : ℤ) = 4)

end CrossRankOneBead

/-! ## The two-bead sector of `[R_e(t), R_f(s)]` (2026-09-08)

Kernel cross-checks of `TworowD4Kernel.twoBeadSector_commutator_eq_zero_of_mul_eq_one` and the
lemmas under it. The instances are chosen so the population *moves*: `k` takes all three of
its values `+1, 0, -1`, the `e = f` instance carries **two** legal assignments with opposite
`k`, and the `ts = 1` vanishing is checked against a neighbouring `ts ≠ 1` instance that does
**not** vanish. A vanishing check whose neighbours also vanish is a kernel, not evidence. -/
section CrossRankTwoBead

/-! Instance 1, `k = +1`. `e = 2`, `f = 3`, `M = {0,1,2}`, `M' = {0,3,5}`; the single legal
assignment is `(x,y) = (1,2)`, with `P = 1`, `Q = 0`, `P' = 0`, `Q' = 1`. -/
private def N₁ : Finset ℤ := {0, 1, 2}
private def N₁' : Finset ℤ := {0, 3, 5}

#guard decide (twoBeadRoutes 2 3 N₁ N₁' = ({(1, 2)} : Finset (ℤ × ℤ)))
#guard decide (twoBeadRoutes 3 2 N₁ N₁' = ({(2, 1)} : Finset (ℤ × ℤ)))
#guard decide (crossIndex 2 3 1 2 = 1)
-- Shadows `crossIndex_swap`: `k' = -k`.
#guard decide (crossIndex 3 2 2 1 = -1)
-- Shadows `twoBead_height_sum`: `P' + Q' = P + Q`, here `0 + 1 = 1 + 0`.
#guard decide (ribbonHeight 2 (addRibbon 3 N₁ 2) 1 + ribbonHeight 3 (addRibbon 2 N₁ 1) 2
  = ribbonHeight 2 N₁ 1 + ribbonHeight 3 N₁ 2)
-- The commutator two-bead part is `1 - st`; at `t = 3`, `s = 5` that is `-14`.
#guard decide (twoBeadSector 3 2 N₁ N₁' (5 : ℤ) 3 - twoBeadSector 2 3 N₁ N₁' (3 : ℤ) 5 = -14)

/-! Instance 2, `k = -1`, so the factor `1 - (ts)^k` is nontrivial in the *other* direction.
`e = 2`, `f = 3`, `M = {0,1,2}`, `M' = {1,3,4}`, assignment `(2,0)`, `P = 0`, `Q = 2`. -/
private def N₂' : Finset ℤ := {1, 3, 4}

#guard decide (twoBeadRoutes 2 3 N₁ N₂' = ({(2, 0)} : Finset (ℤ × ℤ)))
#guard decide (crossIndex 2 3 2 0 = -1)
#guard decide (crossIndex 3 2 0 2 = 1)
#guard decide (ribbonHeight 2 (addRibbon 3 N₁ 0) 2 + ribbonHeight 3 (addRibbon 2 N₁ 2) 0
  = ribbonHeight 2 N₁ 2 + ribbonHeight 3 N₁ 0)
-- The commutator two-bead part is `s²t - s = s(st - 1)`; at `t = 3`, `s = 5` that is `70`.
#guard decide (twoBeadSector 3 2 N₁ N₂' (5 : ℤ) 3 - twoBeadSector 2 3 N₁ N₂' (3 : ℤ) 5 = 70)

/-! Instance 3, `k = 0`. `e = 1`, `f = 3`, `M = {0,1,2}`, `M' = {0,3,4}`, assignment `(2,1)`.
**Labelled as a kernel:** at `k = 0` the two orderings contribute the same monomial for
*every* `t, s`, so this instance is identically zero and cannot distinguish `ts = 1` from
anything else. It is here to pin the third value of `k`, not as evidence for Cor. 4.2(iii). -/
private def N₃' : Finset ℤ := {0, 3, 4}

#guard decide (twoBeadRoutes 1 3 N₁ N₃' = ({(2, 1)} : Finset (ℤ × ℤ)))
#guard decide (crossIndex 1 3 2 1 = 0)
#guard decide (twoBeadSector 3 1 N₁ N₃' (5 : ℤ) 3 - twoBeadSector 1 3 N₁ N₃' (3 : ℤ) 5 = 0)
-- ... and it is zero at a generic point too, which is what makes it a kernel.
#guard decide (twoBeadSector 3 1 N₁ N₃' (7 : ℤ) 2 - twoBeadSector 1 3 N₁ N₃' (2 : ℤ) 7 = 0)

/-! Instance 4 — **the correction**. `e = f = 3`, `M = {0,1,2}`, `M' = {1,3,5}`. There are
**two** legal assignments, `(0,2)` with `k = +1` and `(2,0)` with `k = -1`, and the sector is
`s²t - st² - s + t = (t-s)(1-st)`: nonzero off the two loci, zero at `s = t`, zero at
`ts = 1`. This is exactly the entry that `\cite[Thm.~2.3(2)]{Clio0907}` declared to be `0`;
the one-parameter specialisation `s = t` is why the error survived. -/
private def N₄' : Finset ℤ := {1, 3, 5}

#guard decide (twoBeadRoutes 3 3 N₁ N₄' = ({(0, 2), (2, 0)} : Finset (ℤ × ℤ)))
#guard decide (crossIndex 3 3 0 2 = 1)
#guard decide (crossIndex 3 3 2 0 = -1)
-- Nonzero at `t = 3`, `s = 5`: `75 - 45 - 5 + 3 = 28`. THE SECTOR IS NOT EMPTY AT `e = f`.
#guard decide (twoBeadSector 3 3 N₁ N₄' (5 : ℤ) 3 - twoBeadSector 3 3 N₁ N₄' (3 : ℤ) 5 = 28)
-- Zero at `s = t = 3`: the one-parameter cancellation the old clause mistook for emptiness.
#guard decide (twoBeadSector 3 3 N₁ N₄' (3 : ℤ) 3 - twoBeadSector 3 3 N₁ N₄' (3 : ℤ) 3 = 0)

/-! ## `ts = 1` with `t ≠ s`, against a moving neighbour

Over `ℚ` with `t = 2`, `s = 1/2`: `ts = 1` and `t ≠ s`, so this is not the degenerate
`t = s = -1` point. Each vanishing is paired with the *same instance* at `s = 1` (`ts = 2`),
where it does **not** vanish. -/
#guard decide (twoBeadSector 3 2 N₁ N₁' ((1 : ℚ)/2) 2 - twoBeadSector 2 3 N₁ N₁' (2 : ℚ) (1/2) = 0)
#guard decide (twoBeadSector 3 2 N₁ N₁' (1 : ℚ) 2 - twoBeadSector 2 3 N₁ N₁' (2 : ℚ) 1 ≠ 0)

#guard decide (twoBeadSector 3 2 N₁ N₂' ((1 : ℚ)/2) 2 - twoBeadSector 2 3 N₁ N₂' (2 : ℚ) (1/2) = 0)
#guard decide (twoBeadSector 3 2 N₁ N₂' (1 : ℚ) 2 - twoBeadSector 2 3 N₁ N₂' (2 : ℚ) 1 ≠ 0)

#guard decide (twoBeadSector 3 3 N₁ N₄' ((1 : ℚ)/2) 2 - twoBeadSector 3 3 N₁ N₄' (2 : ℚ) (1/2) = 0)
#guard decide (twoBeadSector 3 3 N₁ N₄' (1 : ℚ) 2 - twoBeadSector 3 3 N₁ N₄' (2 : ℚ) 1 ≠ 0)

/-! ## Negative controls for `crossIndex_swap`

The lemma `k' = -k` needs `x ≠ y` and `x + e ≠ y + f`, and the paper states exactly those
two. Each is shown load-bearing by an instance where dropping it breaks the conclusion. -/

-- Drop `x ≠ y`: at `x = y = 0`, `e = 1`, `f = 2` one gets `k = 1` but `k' = 0 ≠ -1`.
#guard decide (crossIndex 1 2 0 0 = 1)
#guard decide (crossIndex 2 1 0 0 = 0)
#guard decide (crossIndex 2 1 0 0 ≠ -crossIndex 1 2 0 0)

-- Drop `x + e ≠ y + f`: at `x = 1`, `y = 0`, `e = 1`, `f = 2` both land on `2`;
-- `k = -1` but `k' = 0 ≠ 1`.
#guard decide (crossIndex 1 2 1 0 = -1)
#guard decide (crossIndex 2 1 0 1 = 0)
#guard decide (crossIndex 2 1 0 1 ≠ -crossIndex 1 2 1 0)

end CrossRankTwoBead
