/-
DELIBERATE FAILURE -- negative control for the CI detector (LEAN 2026-08-31 c2).
This module exists only on the throwaway branch `ci-negative-control` and must
never be merged. Its purpose is to make the Lean build step fail, so that a red
workflow run can be attributed to Lean rather than to the docgen deploy step.
-/
namespace TworowD4Kernel
theorem ci_negative_control : 2 + 2 = 5 := by sorry
end TworowD4Kernel
