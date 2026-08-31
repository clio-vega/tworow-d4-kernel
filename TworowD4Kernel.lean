/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ArithKernel
import TworowD4Kernel.B0modKernel
import TworowD4Kernel.CompensationLemma
import TworowD4Kernel.Fp2Irreducible
import TworowD4Kernel.GaussianUnitSum
import TworowD4Kernel.PadicNoRoot
import TworowD4Kernel.QuantumInteger
import TworowD4Kernel.LemmaF
import TworowD4Kernel.SubsetIdentityGeneralC
import TworowD4Kernel.ThreeRowC1Boundary
import TworowD4Kernel.ThreeRowC2Boundary
import TworowD4Kernel.ThreeRowC3Boundary
import TworowD4Kernel.ThreeRowC4Boundary
import TworowD4Kernel.ThreeRowC4InteriorN4

/-!
# Two-row / three-row `d = 4` fiber-vanishing kernels

Root aggregator. This module contains no declarations of its own; it exists so that
`import TworowD4Kernel` pulls in the whole development.

The two arithmetic kernel lemmas of the `b ≡ 1 (mod 4)` proof
(`descFactorial_eq_factorial_mul_self_mul_choose_pred` and
`padicValNat_two_factorial_two_mul`) used to be stated *here*. They now live in the leaf
module `TworowD4Kernel.ArithKernel`, which this file re-exports, so their fully qualified
names are unchanged. The move was forced: `D0ClosedForms` needs the doubling identity, and
the root reaches `D0ClosedForms` transitively via
`SubsetIdentityGeneralC → NumberLemmaC2`, so stating them here made the import graph
cyclic and `lake build` failed outright.

Note that `CompensationLemma`, `D0ClosedForms`, `Fp2Irreducible`, `GaussianUnitSum`,
`HookKummerLemmas`, `NumberLemmaC2`, `PadicNoRoot` and `QuantumInteger` are reached either
transitively through the imports above or by the `TworowD4Kernel.+` glob in `lakefile.toml`,
which is what `lake build` actually builds.
-/
