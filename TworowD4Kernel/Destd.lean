/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.PhiGlue

/-!
# G4 gap 5: destandardising the final values

Source: `projects/proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:A` and `lem:D`
("The labels are recovered by `U⁻¹(k) ↦ row + 1`, and standardisation commutes with every move"),
the well-typed reading of Purbhoo arXiv:0705.1184 §5.1 Cor. 5.3 (p. 20).

`StdSlide.lemmaA_slides` says that the run on `std X` ends with `std` of the final values of
the run on `X`. Φ, however, outputs the final *unstandardised* values (`uVal = row + 1`). This
file recovers them.

**Form chosen: the invariant `X = g ∘ std X`** (`DestdBy g S X`), not "`X = g ∘ Y` with `g`
monotone and `Y` arbitrary". The reason is that `lemmaA_slides` is already stated against
`std S X`, so the invariant composes with it directly. Monotonicity of `g` is then never a
hypothesis. It is built in, because `g` acts on `std`-ranks, and those ranks carry `X`'s
(value, column) order by construction. The arbitrary-`Y` form must instead prove path
agreement again, and the tie-breaking would make weakly monotone `g` delicate.

* `destdBy_move`: one move preserves `DestdBy g` (via `std_move`, under the same column
  hypothesis as Lemma A).
* `destdBy_slide`, `destdBy_slides`: iterated, under `SlideOK` / `SlidesOK`.
* `slides_destd` (**transport form**): final `X`-values `= g ∘` final values of the run on
  `std X`. The same holds for any `Y` agreeing with `std X` on `S` (`slides_destd_of_eq`).
* `phi_values_destd`: for Φ, with `U = skewCells (A^∨) []`, `g i = uVal (U.getD i (0,0))`
  and `Y = valOf U`. Φ's output values are `uVal ∘ U[·]` of the *word* run's final values.
* Kernel control: 310/310 on `phiData33`. Lesion: the anti-monotone relabelling
  (`Y = valRev U`, `g` read off `U.reverse`, so `uVal = g ∘ Y` still holds on `U`) breaks the
  transport on 141/310.
-/

namespace TworowD4Kernel.Destd

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.PhiOut TworowD4Kernel.PhiOutData TworowD4Kernel.PhiGlue Finset

/-- `X` is recovered from its own standardisation on `S` by the relabelling `g`. -/
def DestdBy (g : ℕ → ℕ) (S : Finset Cell) (X : Cell → ℕ) : Prop :=
  ∀ a ∈ S, X a = g (std S X a)

lemma src_mem {S : Finset Cell} {h y a : Cell} (hyS : y ∈ S) (ha : a ∈ moveS S h y) :
    src h y a ∈ S := by
  unfold src
  split_ifs with hah
  · exact hyS
  · simp only [moveS, mem_insert, mem_erase] at ha
    rcases ha with ha | ⟨-, ha⟩
    · exact absurd ha hah
    · exact ha

/-- **One move.** Moving the entry at `y` into the hole `h` preserves `X = g ∘ std X`. -/
theorem destdBy_move {g : ℕ → ℕ} {S : Finset Cell} {X : Cell → ℕ} {h y : Cell}
    (hhS : h ∉ S) (hyS : y ∈ S)
    (hcol : ∀ b ∈ S, b ≠ y → X b = X y → b.2 ≠ y.2 ∧ b.2 ≠ h.2)
    (hhy : h.2 = y.2 ∨ h.2 + 1 = y.2 ∨ y.2 + 1 = h.2)
    (hD : DestdBy g S X) : DestdBy g (moveS S h y) (moveX X h y) := by
  intro a ha
  rw [std_move S X hhS hyS hcol hhy a ha, moveX_eq_src, moveX_eq_src]
  exact hD _ (src_mem hyS ha)

/-- **One slide.** -/
theorem destdBy_slide (R : Rule) (g : ℕ → ℕ) : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ)
    (h : Cell), h ∉ S → SlideOK R k S X h → DestdBy g S X →
    DestdBy g (slide R k S X h).1 (slide R k S X h).2.1 := by
  intro k
  induction k with
  | zero => intro S X h _ _ hD; exact hD
  | succ k ih =>
    intro S X h hhS hok hD
    simp only [slide]
    obtain ⟨h0, hrest⟩ := hok
    rcases hc : R.ch S X h with _ | y
    · exact hD
    · rw [hc] at hrest
      have hyS := R.mem S X h y hc
      have hyh : y ≠ h := fun e => hhS (e ▸ hyS)
      have hy' : y ∉ moveS S h y := by simp [moveS, hyh]
      have hcol := hcol_of_colInj hhS h0 hrest.colInj hyS
      exact ih _ _ y hy' hrest (destdBy_move hhS hyS hcol (R.col S X h y hc) hD)

/-- **All slides.** -/
theorem destdBy_slides (R : Rule) (g : ℕ → ℕ) (k : ℕ) : ∀ (hs : List Cell) (S : Finset Cell)
    (X : Cell → ℕ), SlidesOK R k S X hs → DestdBy g S X →
    DestdBy g (slides R k S X hs).1 (slides R k S X hs).2.1 := by
  intro hs
  induction hs with
  | nil => intro S X _ hD; exact hD
  | cons h hs ih =>
    intro S X ⟨hhS, hok, hrest⟩ hD
    exact ih _ _ hrest (destdBy_slide R g k S X h hhS hok hD)

/-- **Gap 5, transport form.** If `X = g ∘ std X` on `S` and the run on `X` is column-injective
throughout, then the final values of the run on `X` are `g` of the final values of the run on
`std X`. The two runs have the same final support (`lemmaA_slides`). -/
theorem slides_destd (R : Rule) (g : ℕ → ℕ) (k : ℕ) (hs : List Cell) (S : Finset Cell)
    (X : Cell → ℕ) (hok : SlidesOK R k S X hs) (hD : DestdBy g S X) :
    (slides R k S (std S X) hs).1 = (slides R k S X hs).1 ∧
    ∀ a ∈ (slides R k S X hs).1,
      (slides R k S X hs).2.1 a = g ((slides R k S (std S X) hs).2.1 a) := by
  obtain ⟨-, a2, a3⟩ := lemmaA_slides R k hs S X hok
  refine ⟨a2, fun a ha => ?_⟩
  rw [a3 a ha]
  exact destdBy_slides R g k hs S X hok hD a ha

/-- The same, with any `Y` that agrees with `std X` on `S` (e.g. `valOf U`). -/
theorem slides_destd_of_eq (R : Rule) (g : ℕ → ℕ) (k : ℕ) (hs : List Cell) (S : Finset Cell)
    (X Y : Cell → ℕ) (hY : ∀ a ∈ S, std S X a = Y a)
    (hok : SlidesOK R k S X hs) (hD : DestdBy g S X) :
    (slides R k S Y hs).1 = (slides R k S X hs).1 ∧
    ∀ a ∈ (slides R k S X hs).1,
      (slides R k S X hs).2.1 a = g ((slides R k S Y hs).2.1 a) := by
  obtain ⟨c1, -, c3⟩ := slides_congr R k hs S (std S X) Y hY
  obtain ⟨d1, d2⟩ := slides_destd R g k hs S X hok hD
  refine ⟨c1 ▸ d1, fun a ha => ?_⟩
  rw [d2 a ha, c3 a (d1 ▸ ha)]

/-! ### Φ -/

/-- The relabelling for `u_κ`: rank `i` ↦ the value `row + 1` of the `i`-th cell of the word. -/
def gU (U : List Cell) (i : ℕ) : ℕ := uVal (U.getD i (0, 0))

lemma getD_idxOf {U : List Cell} {a : Cell} (ha : a ∈ U) : U.getD (U.idxOf a) (0, 0) = a := by
  have hl : U.idxOf a < U.length := List.idxOf_lt_length_of_mem ha
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some,
    List.getElem_idxOf]

/-- `u_κ = gU U ∘ std u_κ` on the cells of `κ` (gap 1 gives `std u_κ = valOf U`). -/
theorem destdBy_uVal (κ : List ℕ) :
    DestdBy (gU (skewCells κ [])) (skewCells κ []).toFinset uVal := by
  intro a ha
  have ha' := List.mem_toFinset.1 ha
  rw [std_uVal_eq_valOf κ a ha']
  unfold gU valOf
  rw [getD_idxOf ha']

/-- **Gap 5 for Φ.** Under the named hypothesis `SlidesOK` on Φ's run, Φ's output support is the
final support of the *word* run (values `valOf U`), and Φ's output values are
`uVal (U[i])` where `i` is the word run's final value. So Φ's labels are read off the word run,
and that run is the window form of `SlidesColsBridge.slides_colsW`. -/
theorem phi_values_destd (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hok : SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f)) :
    (slides revRule (R + C) (skewCells (compl R C A) []).toFinset
        (valOf (skewCells (compl R C A) [])) (holesWith tilde R C A B f)).1 =
      (phi R C A B f).1 ∧
    ∀ a ∈ (phi R C A B f).1,
      (phi R C A B f).2 a = gU (skewCells (compl R C A) [])
        ((slides revRule (R + C) (skewCells (compl R C A) []).toFinset
          (valOf (skewCells (compl R C A) [])) (holesWith tilde R C A B f)).2.1 a) :=
  slides_destd_of_eq revRule _ (R + C) _ _ uVal _
    (fun a ha => std_uVal_eq_valOf _ a (List.mem_toFinset.1 ha)) hok
    (destdBy_uVal (compl R C A))

/-! ### Control and lesion (kernel; these are evaluations of finite instances) -/

/-- Transport check with a word valuation `Y` and relabelling `g`, on Φ's run. -/
def transCheckWith (Y : List Cell → Cell → ℕ) (g : List Cell → ℕ → ℕ)
    (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  let R := d.1; let C := d.2.1; let A := d.2.2.1; let B := d.2.2.2.1
  let f := ofList d.2.2.2.2.1
  let U := skewCells (compl R C A) []
  let F := holesWith tilde R C A B f
  let w := slides revRule (R + C) U.toFinset (Y U) F
  let p := phi R C A B f
  decide (w.1 = p.1 ∧ ∀ a ∈ p.1, p.2 a = g U (w.2.1 a))

/-- The true form: `Y = valOf U`, `g = gU`. -/
def transCheck := transCheckWith valOf gU

/-- The anti-monotone lesion: `Y = valRev U` (word read backwards) and `g` read off `U.reverse`.
Then `uVal = g ∘ Y` still holds on `U`, but `g` reverses the order of ranks. -/
def gURev (U : List Cell) (i : ℕ) : ℕ := uVal (U.reverse.getD i (0, 0))
def transCheckRev := transCheckWith valRev gURev

/-- The lesion's precondition holds: `uVal = gURev U ∘ valRev U` on `U` (any nodup `U`). So the
lesion fails only because `g` is not monotone, not because the relabelling is wrong. -/
def lesionPre (d : ℕ × ℕ × List ℕ × List ℕ × List (Cell × ℕ) × List (Cell × ℕ)) : Bool :=
  let U := skewCells (compl d.1 d.2.1 d.2.2.1) []
  U.all fun a => uVal a == gURev U (valRev U a)

/-- **Control (kernel).** On all 310 instances, Φ's output equals `gU ∘` the word run. -/
theorem destd_control_33 : phiData33.all transCheck = true := by decide +kernel

/-- **Lesion (kernel).** The anti-monotone relabelling satisfies its precondition
`uVal = g ∘ Y` on all 310 instances. Even so, the transport fails on 141 of them, including
`PhiGlue.lesionRevU` (`A = (1,1)` in the `2 × 2` box), where the true form passes. -/
theorem lesion_antimonotone :
    phiData33.all lesionPre = true ∧
    transCheck lesionRevU = true ∧ transCheckRev lesionRevU = false ∧
    (phiData33.filter fun d => !transCheckRev d).length = 141 := by
  decide +kernel

end TworowD4Kernel.Destd
