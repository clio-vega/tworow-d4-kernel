/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.StdSlide
import TworowD4Kernel.PhiOutData

/-!
# G4: Purbhoo's outward map Φ (tex `def:phi`, item 3)

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, Definition `def:phi`, l.98–106,
the well-typed reading of Purbhoo, *Puzzles, tableaux, and mosaics*, arXiv:0705.1184, §5.1
Corollary 5.3 (p. 20), standard order of §2.2 (p. 7–8, "east to west" typo corrected).

> Let `f` be an LR tableau of skew shape `A/B`, `B ⊆ A ⊆ R × C` …
> 1. `f̃(rot X)` = the position of `X` in the reverse standard order of `f`.
> 2. `g = u_{A^∨}`, the straight LR tableau of the inner shape `A^∨` of `f̃`
>    (row `r` filled with `r+1`).
> 3. For `k = 1, …, |A/B|`, put a hole at the cell `f̃⁻¹(k)` and perform a reverse slide of `g`:
>    the hole takes the larger of its west and south `g`-neighbours, and on a tie the south one.
>    `Φ(f) := g̃`, the final position of `g`.

## Representation

Cells are `(r, c)` (`SlideSwitch.Cell`), as in `StdSlide`. Shapes are partitions as lists
(`A.getD r 0` = length of row `r`). Item 1 is `StdSlide.tilde` (0-based positions), the very
function of `StdSlide.lemmaC`. Item 3 is `StdSlide.slides revRule`, the very iteration of
`StdSlide.lemmaA_slides`/`V_std_reverse`, with the holes listed in increasing `f̃`. So Φ is built
from the objects the assembly of `thm:G4` consumes, not from a parallel implementation.

The hole list is `f̃⁻¹(0), f̃⁻¹(1), …`, computed by `List.find?` over an explicit cell list (no
`Finset.sort`, which the kernel cannot reduce).

## Checks

* `phi_eq_python_33`: kernel `decide` — Lean Φ equals the Python Φ (`g4.phi_out`) on all 310
  instances with `|A/B| ≤ 5`, `R, C ≤ 3` (support and values).
* Tests: `#guard` (evaluation, not kernel) on all 3556 instances with `R, C ≤ 4`.
* `lesion_row_order`: kernel — the standard order with ties broken by **row** first instead of
  column (row/column reading swapped) disagrees with Python on an explicit instance;
  `lesion_row_order_count`: on 55/310 (evaluation: 1151/3556 at `R, C ≤ 4`).
-/

namespace TworowD4Kernel.PhiOut

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOutData

/-- The cells of the skew shape `A/B`, row by row, west to east. -/
def skewCells (A B : List ℕ) : List Cell :=
  (List.range A.length).flatMap fun r =>
    ((List.range (A.getD r 0)).filter fun c => B.getD r 0 ≤ c).map fun c => (r, c)

/-- `A^∨` in the `R × C` box: row `r` has length `C - A_{R-1-r}`. -/
def compl (R C : ℕ) (A : List ℕ) : List ℕ :=
  (List.range R).map fun r => C - A.getD (R - 1 - r) 0

/-- `u_κ`: the straight LR tableau, row `r` filled with `r + 1` (tex item 2). -/
def uVal (y : Cell) : ℕ := y.1 + 1

/-- The holes of item 3: `f̃⁻¹(0), f̃⁻¹(1), …` for a ranking function `t` (item 1). -/
def holesWith (t : ℕ → ℕ → Finset Cell → (Cell → ℕ) → Cell → ℕ)
    (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ) : List Cell :=
  let cs := skewCells A B
  let rc := cs.map (rot R C)
  (List.range cs.length).filterMap fun j => rc.find? fun y => t R C cs.toFinset f y = j

/-- Item 3 for a given slide rule and ranking: slide `u_{A^∨}` outward through the holes.
Fuel `R + C` per slide (a reverse step lowers `r + c` by one). -/
def phiWith (Rl : Rule) (t : ℕ → ℕ → Finset Cell → (Cell → ℕ) → Cell → ℕ)
    (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ) : Finset Cell × (Cell → ℕ) :=
  let r := slides Rl (R + C) (skewCells (compl R C A) []).toFinset uVal (holesWith t R C A B f)
  (r.1, r.2.1)

/-- **Φ, tex `def:phi`** (Purbhoo 0705.1184 Cor. 5.3, well-typed reading): ranking `tilde`
(reverse standard order, ties by column), reverse slides `revRule` (larger of W/S, tie → south). -/
def phi (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ) : Finset Cell × (Cell → ℕ) :=
  phiWith revRule tilde R C A B f

/-- A filling given as a list of `(cell, value)`. -/
def ofList (l : List (Cell × ℕ)) (y : Cell) : ℕ := (l.lookup y).getD 0

/-- Agreement with an expected filling: same support, same values on it. -/
def agrees (out : Finset Cell × (Cell → ℕ)) (exp : List (Cell × ℕ)) : Bool :=
  decide (out.1 = (exp.map Prod.fst).toFinset) && exp.all fun p => out.2 p.1 == p.2

/-- One data row checked against a Φ-variant. -/
def checkRow (Φ : ℕ → ℕ → List ℕ → List ℕ → (Cell → ℕ) → Finset Cell × (Cell → ℕ))
    (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  agrees (Φ d.1 d.2.1 d.2.2.1 d.2.2.2.1 (ofList d.2.2.2.2.1)) d.2.2.2.2.2

/-- **Lean Φ = Python Φ** on all 310 instances `|A/B| ≤ 5`, `R, C ≤ 3` (kernel). -/
theorem phi_eq_python_33 : phiData33.all (checkRow phi) = true := by decide +kernel

/-! ### Lesions -/

/-- Lesioned ranking: reverse standard order with ties broken by **row first** (then column)
instead of by column — the row/column reading order swapped. Still a total order, so the hole
list has full length; only the order of equal entries in different rows changes. -/
def tildeRow (R C : ℕ) (S : Finset Cell) (f : Cell → ℕ) (y : Cell) : ℕ :=
  (S.filter fun Y => f (rot R C y) < f Y ∨ (f Y = f (rot R C y) ∧
    ((rot R C y).1 < Y.1 ∨ ((rot R C y).1 = Y.1 ∧ (rot R C y).2 < Y.2)))).card

/-- The smallest instance found where the row-first ranking changes Φ: `A/B = (2,1)/(1)` in the
`2 × 2` box, two `1`s in different rows. It is a row of `phiData33`. -/
def lesionRow : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ) :=
  (2, 2, [2, 1], [1, 0], [((0, 1), 1), ((1, 0), 1)], [((1, 0), 1)])

/-- **Lesion (reading order).** Swapping the tie-break of the standard order from column to row
breaks agreement with Python at `lesionRow`, where the true Φ agrees (kernel). -/
theorem lesion_row_order : lesionRow ∈ phiData33 ∧ checkRow phi lesionRow = true ∧
    checkRow (phiWith revRule tildeRow) lesionRow = false := by decide +kernel

/-- The row-first lesion disagrees with Python on 55 of the 310 instances (kernel). -/
theorem lesion_row_order_count :
    (phiData33.filter fun d => !checkRow (phiWith revRule tildeRow) d).length = 55 := by
  decide +kernel

end TworowD4Kernel.PhiOut
