/-
G4 gap G3 (LEAN 2026-11-23 c2): on a skew (product-order convex) set of cells, a semistandard
filling is column-injective. Columns of a convex set are intervals, and the filling is strictly
increasing up each interval.

Consequence: the hypothesis `hcol` of `G4AssemblyStd.thm_G4_of_slideOK'` is derivable from
`hA`, `hB` (so `skewCells A B` is convex) and `hup`; `thm_G4_of_slideOK''` drops it.

Paper: tex `def:phi` standing hypothesis "f column strict" (proofs/2026-11-23-lean-G4-hstd.md);
the fact is elementary, no external citation.
-/
import TworowD4Kernel.G4AssemblyStd

namespace TworowD4Kernel.SkewColInj

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.PhiOut
open TworowD4Kernel.RRStd TworowD4Kernel.PhiGlue

/-- Semistandard on a set of cells: weak along rows (west → east), strict up columns
(`(r,c)` → `(r+1,c)`), adjacent cells only. -/
def SSOn (S : Finset Cell) (X : Cell → ℕ) : Prop :=
  (∀ a ∈ S, (a.1, a.2 + 1) ∈ S → X a ≤ X (a.1, a.2 + 1)) ∧
  (∀ a ∈ S, (a.1 + 1, a.2) ∈ S → X a < X (a.1 + 1, a.2))

instance decSSOn (S : Finset Cell) (X : Cell → ℕ) : Decidable (SSOn S X) := by
  unfold SSOn; infer_instance

/-- Convex in the product order (a skew shape). -/
def Skew (S : Finset Cell) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c : Cell, a.1 ≤ c.1 → a.2 ≤ c.2 → c.1 ≤ b.1 → c.2 ≤ b.2 → c ∈ S

/-- Strict increase up a column of a convex set, over any distance. -/
lemma col_lt {S : Finset Cell} {X : Cell → ℕ} (hS : Skew S) (hX : SSOn S X) :
    ∀ (d : ℕ) (a : Cell), a ∈ S → (a.1 + (d + 1), a.2) ∈ S → X a < X (a.1 + (d + 1), a.2) := by
  intro d
  induction d with
  | zero => intro a ha ht; exact hX.2 a ha ht
  | succ d ih =>
    intro a ha ht
    have hb : (a.1 + (d + 1), a.2) ∈ S :=
      hS a ha _ ht (a.1 + (d + 1), a.2) (by simp) le_rfl (by simp) le_rfl
    have h1 := ih a ha hb
    have h2 := hX.2 _ hb (by simpa [Nat.add_assoc] using ht)
    have e : (a.1 + (d + 1) + 1, a.2) = (a.1 + (d + 1 + 1), a.2) := by
      simp [Nat.add_assoc]
    rw [e] at h2
    omega

/-- **G3.** On a skew set, semistandard ⇒ column-injective. -/
theorem colInj_of_SS (S : Finset Cell) (X : Cell → ℕ) (hS : Skew S) (hX : SSOn S X) :
    ColInj S X := by
  have key : ∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → a.1 < b.1 → X a < X b := by
    intro a ha b hb hc hlt
    obtain ⟨d, hd⟩ : ∃ d, b.1 = a.1 + (d + 1) := ⟨b.1 - a.1 - 1, by omega⟩
    have hbeq : b = (a.1 + (d + 1), a.2) := Prod.ext hd hc.symm
    subst hbeq
    exact col_lt hS hX d a ha hb
  intro a ha b hb hc hv
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact absurd hv (key a ha b hb hc h).ne
  · exact Prod.ext h hc
  · exact absurd hv (key b hb a ha hc.symm h).ne'

/-- `skewCells A B` is convex when `A` and `B` are weakly decreasing. -/
theorem skew_skewCells (A B : List ℕ)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0)
    (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0) :
    Skew (skewCells A B).toFinset := by
  intro a ha b hb c h1 h2 h3 h4
  simp only [List.mem_toFinset, mem_skewCells] at ha hb ⊢
  have := hA c.1 b.1 h3
  have := hB a.1 c.1 h1
  refine ⟨by omega, by omega, by omega⟩

/-- `hup` + convexity give column-injectivity of `f` on `A/B`: the `hcol` hypothesis of
`thm_G4_of_slideOK'` is redundant. (`hrow` is carried along only to build `SSOn`.) -/
theorem hcol_of_hup (A B : List ℕ) (f : Cell → ℕ)
    (hA : ∀ i j, i ≤ j → A.getD j 0 ≤ A.getD i 0)
    (hB : ∀ i j, i ≤ j → B.getD j 0 ≤ B.getD i 0)
    (hrow : ∀ Y ∈ skewCells A B, (Y.1, Y.2 + 1) ∈ skewCells A B → f Y ≤ f (Y.1, Y.2 + 1))
    (hup : ∀ Y ∈ skewCells A B, (Y.1 + 1, Y.2) ∈ skewCells A B → f Y < f (Y.1 + 1, Y.2)) :
    ColInj (skewCells A B).toFinset f :=
  colInj_of_SS _ f (skew_skewCells A B hA hB)
    ⟨fun a ha hb => hrow a (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb),
     fun a ha hb => hup a (List.mem_toFinset.1 ha) (List.mem_toFinset.1 hb)⟩

/-- `thm_G4_of_slideOK'` without `hcol`. -/
theorem thm_G4_of_slideOK'' (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset)
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
  G4AssemblyStd.thm_G4_of_slideOK' R C A B f hbox (hcol_of_hup A B f hA hB hrow hup)
    hA hB hBA hrow hup hokR hokF

/-! ## Lesion: convexity cannot be dropped from G3

`S = {(0,0), (2,0)}` has a gap at `(1,0)` in column 0. With the constant filling `1`, `SSOn`
holds (no two cells are adjacent) and `ColInj` fails. -/

theorem lesion_skew :
    SSOn {(0, 0), (2, 0)} (fun _ => 1) ∧ ¬ ColInj {(0, 0), (2, 0)} (fun _ => 1) ∧
    ¬ Skew {(0, 0), (2, 0)} := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  have := h (0, 0) (by decide) (2, 0) (by decide) (1, 0) (by decide) le_rfl (by decide) le_rfl
  exact absurd this (by decide)

end TworowD4Kernel.SkewColInj
