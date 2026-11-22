/-
G4 assembly, link L2 (LEAN 2026-11-22): Φ's output (support and labels) read off the window form.

Paper: `proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `def:phi`, `lem:A`, `lem:D`;
Purbhoo arXiv:0705.1184 §5.1 Cor. 5.3. Pure glue: `phi_values_destd` (gap 5) +
`slides_colsW_take` (window form) + `slides_fuel_eq` (Φ's fuel `R+C` ↔ `|U|+1`, on the whole
`slides` triple) + `holes_dsum_le`.
-/
import TworowD4Kernel.Destd
import TworowD4Kernel.PhiGlue

namespace TworowD4Kernel.PhiLabels

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.SlideIteration TworowD4Kernel.SlidesColsBridge TworowD4Kernel.PhiOut
open TworowD4Kernel.PhiGlue TworowD4Kernel.Destd

/-- **L2.** Under the named `SlidesOK revRule (R+C)` on Φ's run and `U ++ F` repetition-free,
Φ's output support is `U'.toFinset` and its label at `a` is `gU U (valOf U' a)`, where
`U' = (colsW |U| 0 |F| (U ++ F)).drop |F|` is the `U`-part of the window form. -/
theorem phi_eq_window (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hnd : (skewCells (compl R C A) [] ++ holesWith tilde R C A B f).Nodup)
    (hok : SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f)) :
    let U := skewCells (compl R C A) []
    let F := holesWith tilde R C A B f
    (phi R C A B f).1 = ((colsW U.length 0 F.length (U ++ F)).drop F.length).toFinset ∧
      ∀ a ∈ (phi R C A B f).1, (phi R C A B f).2 a =
        gU U (valOf ((colsW U.length 0 F.length (U ++ F)).drop F.length) a) := by
  intro U F
  have hF : F.Nodup := (List.nodup_append.1 hnd).2.1
  have hdis : ∀ h ∈ F, h ∉ U.toFinset := fun h hm hU =>
    (List.nodup_append.1 hnd).2.2 h (List.mem_toFinset.1 hU) h hm rfl
  have hcard : U.toFinset.card ≤ U.length + 1 := by
    have := List.toFinset_card_le U; omega
  have hfuel : slides revRule (R + C) U.toFinset (valOf U) F =
      slides revRule (U.length + 1) U.toFinset (valOf U) F :=
    (slides_fuel_eq (U.length + 1) (R + C) F U.toFinset (valOf U) hF hdis hcard
      (holes_dsum_le tilde R C A B f)).symm
  obtain ⟨-, ht1, ht2⟩ := slides_colsW_take U.length U F (valOf U) rfl hnd (fun _ _ => rfl)
  obtain ⟨pv1, pv2⟩ := phi_values_destd R C A B f hok
  change (slides revRule (R + C) U.toFinset (valOf U) F).1 = (phi R C A B f).1 at pv1
  rw [hfuel] at pv1
  refine ⟨by rw [← pv1, ht1], fun a ha => ?_⟩
  have h := pv2 a ha
  change (phi R C A B f).2 a = gU U ((slides revRule (R + C) U.toFinset (valOf U) F).2.1 a) at h
  rw [h, hfuel, ht2 a (pv1 ▸ ha)]

end TworowD4Kernel.PhiLabels
