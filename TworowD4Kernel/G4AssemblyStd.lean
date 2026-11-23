/-
G4 assembly with `hstd` discharged (LEAN 2026-11-23).

`thm_G4_of_slideOK'` = `G4Assembly.thm_G4_of_slideOK` with `hstd` replaced by `RRStd.hstd_of_ssyt`
(tex `lem:rrstd`, `proofs/2026-11-13c2-Q585-G4-evacuation.tex` l.158; Purbhoo arXiv:0705.1184
§5.1 Cor. 5.3). The price is the tex's own standing hypotheses made explicit: `A ⊇ B` partitions and
`f` semistandard on `A/B` (`hrow`, `hup`). `hokR`, `hokF` (Fulton 1.2 along both runs) remain named.
-/
import TworowD4Kernel.G4Assembly
import TworowD4Kernel.RRStd

namespace TworowD4Kernel.G4AssemblyStd

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOut
open TworowD4Kernel.StdSlideBridge TworowD4Kernel.RRStd TworowD4Kernel.PhiGlue

/-- **`thm:G4` with `hstd` discharged.** Hypotheses: `A/B` in the box, `f` column-injective
(`hcol`, kept: it is what `holesWith_spec` consumes), `A ⊇ B` partitions, `f` semistandard, and
the two Fulton-1.2 hypotheses `hokR`, `hokF`. -/
theorem thm_G4_of_slideOK' (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset) (hcol : ColInj (skewCells A B).toFinset f)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0)
    (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hBA : ∀ i, B.getD i 0 ≤ A.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2))
    (hokR : SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f))
    (hokF : SlidesOK fwdRule ((holesWith tilde R C A B f).length + 1)
      (holesWith tilde R C A B f).toFinset
      (rr R C (((skewCells A B).map f).foldr max 0) f)
      (skewCells (compl R C A) []).reverse) :
    (phi R C A B f).1 = (sigmaRR R C A B f).1 ∧
    ∀ a ∈ (phi R C A B f).1, (phi R C A B f).2 a = (sigmaRR R C A B f).2 a :=
  G4Assembly.thm_G4_of_slideOK R C A B f hbox hcol
    (hstd_of_ssyt R C A B f hbox hcol hA hB hBA hrow hup) hokR hokF

/-! ## Lesions of `hstd_of_ssyt` (kernel, one instance each)

Each instance satisfies `hbox` and `hcol` (and the shape hypotheses), violates exactly one of the
two semistandardness hypotheses, and `hstd` fails. So neither can be dropped, and `hstd` is not a
consequence of `hbox` + `hcol` (the hypotheses of the old `thm_G4_of_slideOK`). -/

instance decInBox (R C : ℕ) (S : Finset Cell) : Decidable (InBox R C S) := by
  unfold InBox; infer_instance

instance decColInj (S : Finset Cell) (X : Cell → ℕ) : Decidable (ColInj S X) := by
  unfold ColInj; infer_instance

/-- Column decreasing upward: `A = (1,1)`, `B = ∅`, `2 × 1` box, `f(0,0) = 2`, `f(1,0) = 1`. -/
def fDown : Cell → ℕ := fun y => if y = (0, 0) then 2 else 1

/-- **Lesion (drop `hup`).** Box and column-injectivity hold, rows are trivially weak, `hup` fails
at `(0,0)`, and `hstd` is false (kernel). -/
theorem lesion_hup :
    InBox 2 1 (skewCells [1, 1] []).toFinset ∧ ColInj (skewCells [1, 1] []).toFinset fDown ∧
    ¬ fDown (0, 0) < fDown (1, 0) ∧
    ¬ StdFrom ∅ (skewCells (compl 2 1 [1, 1]) [] ++ holesWith tilde 2 1 [1, 1] [] fDown) := by
  decide +kernel

/-- Row decreasing eastward: `A = (2)`, `B = ∅`, `1 × 2` box, `f(0,0) = 2`, `f(0,1) = 1`. -/
theorem lesion_hrow :
    InBox 1 2 (skewCells [2] []).toFinset ∧ ColInj (skewCells [2] []).toFinset fDown ∧
    ¬ fDown (0, 0) ≤ fDown (0, 1) ∧
    ¬ StdFrom ∅ (skewCells (compl 1 2 [2]) [] ++ holesWith tilde 1 2 [2] [] fDown) := by
  decide +kernel

/-! ## Non-vacuity control (kernel, hand-picked instances)

Replaces the 310-instance `g4_hyps_control_33` (did not finish in 25 min, 2026-11-22 c2). Each
`example` discharges EVERY hypothesis of `thm_G4_of_slideOK'` on one instance of `phiData33`
and then applies the theorem, so the hypothesis set is satisfiable there. -/

/-- `A = (2,1)`, `B = (1)`, `2 × 2` box, `f = 1, 1` (the `lesionRow` instance of `PhiOut`). -/
def f21 : Cell → ℕ := ofList [((0, 1), 1), ((1, 0), 1)]

example : (phi 2 2 [2, 1] [1] f21).1 = (sigmaRR 2 2 [2, 1] [1] f21).1 := by
  refine (thm_G4_of_slideOK' 2 2 [2, 1] [1] f21 (by decide +kernel) (by decide +kernel)
    ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)).1
  · intro i j h; rcases i with _ | _ | i <;> rcases j with _ | _ | j <;> simp <;> omega
  · intro i j h; rcases i with _ | i <;> rcases j with _ | j <;> simp <;> omega
  · intro i; rcases i with _ | _ | i <;> simp

/-- `A = (3,2,1)`, `B = (1)`, `3 × 3` box, `|A/B| = 5`, content `(2,2,1)` (`phiData33` row). -/
def f321 : Cell → ℕ := ofList [((0, 1), 1), ((0, 2), 1), ((1, 0), 2), ((1, 1), 2), ((2, 0), 3)]

example : (phi 3 3 [3, 2, 1] [1, 0, 0] f321).1 = (sigmaRR 3 3 [3, 2, 1] [1, 0, 0] f321).1 ∧
    ∀ a ∈ (phi 3 3 [3, 2, 1] [1, 0, 0] f321).1,
      (phi 3 3 [3, 2, 1] [1, 0, 0] f321).2 a = (sigmaRR 3 3 [3, 2, 1] [1, 0, 0] f321).2 a := by
  refine thm_G4_of_slideOK' 3 3 [3, 2, 1] [1, 0, 0] f321 (by decide +kernel) (by decide +kernel)
    ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro i j h
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;> simp <;> omega
  · intro i j h
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;> simp <;> omega
  · intro i; rcases i with _ | _ | _ | i <;> simp

/-- `A = (3,3,2)`, `B = (2,1)`, `3 × 3` box, `|A/B| = 5`, three rows of the skew shape. -/
def f332 : Cell → ℕ := ofList [((0, 2), 1), ((1, 1), 1), ((1, 2), 2), ((2, 0), 2), ((2, 1), 3)]

example : (phi 3 3 [3, 3, 2] [2, 1, 0] f332).1 = (sigmaRR 3 3 [3, 3, 2] [2, 1, 0] f332).1 ∧
    ∀ a ∈ (phi 3 3 [3, 3, 2] [2, 1, 0] f332).1,
      (phi 3 3 [3, 3, 2] [2, 1, 0] f332).2 a = (sigmaRR 3 3 [3, 3, 2] [2, 1, 0] f332).2 a := by
  refine thm_G4_of_slideOK' 3 3 [3, 3, 2] [2, 1, 0] f332 (by decide +kernel) (by decide +kernel)
    ?_ ?_ ?_ (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  · intro i j h
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;> simp <;> omega
  · intro i j h
    rcases i with _ | _ | _ | i <;> rcases j with _ | _ | _ | j <;> simp <;> omega
  · intro i; rcases i with _ | _ | _ | i <;> simp

end TworowD4Kernel.G4AssemblyStd
