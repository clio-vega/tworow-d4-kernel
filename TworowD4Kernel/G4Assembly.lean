/-
G4 assembly (LEAN 2026-11-22): link L6 and the assembled `thm:G4` under named hypotheses.

Paper: `proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `thm:G4` (Φ(f) = Σ(rr f));
Purbhoo arXiv:0705.1184 §5.1 Cor. 5.3. Links: L0 `stdFrom_nodup`, L1 `ChainInj.rowsW_eq_colsW`,
L2 `PhiLabels.phi_eq_window`, L3/L4 `RankList`, L5 `RowsSlidesBridge.V_rowsW_of_slidesOK_fuel`,
L6 below (list combinatorics: `V = U'.reverse` and the label dictionary).
-/
import TworowD4Kernel.ChainInj
import TworowD4Kernel.RankList
import TworowD4Kernel.PhiLabels
import TworowD4Kernel.RowsSlidesBridge

namespace TworowD4Kernel.G4Assembly

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.StdSlideBridge
open TworowD4Kernel.SlideIteration TworowD4Kernel.SlidesColsBridge TworowD4Kernel.PhiOut
open TworowD4Kernel.PhiGlue TworowD4Kernel.Destd TworowD4Kernel.RowsSlidesBridge
open TworowD4Kernel.ChainInj TworowD4Kernel.RankList TworowD4Kernel.PhiLabels

/-- `lookup` in a zip reads the partner at the first occurrence. -/
lemma lookup_zip : ∀ (V : List Cell) (L : List ℕ) (a : Cell), a ∈ V → V.length ≤ L.length →
    (V.zip L).lookup a = L[V.idxOf a]?
  | [], _, _, h, _ => absurd h (List.not_mem_nil)
  | _ :: _, [], _, _, hl => by simp at hl
  | v :: V, x :: L, a, ha, hl => by
    by_cases e : a = v
    · subst e; simp [List.lookup]
    · have ha' : a ∈ V := by
        rcases List.mem_cons.1 ha with h | h
        · exact absurd h e
        · exact h
      have hve : (v == a) = false := by simpa using Ne.symm e
      have hae : (a == v) = false := by simpa using e
      simp only [List.zip_cons_cons, List.lookup, hae, List.idxOf_cons, hve]
      rw [lookup_zip V L a ha' (by simpa using hl)]
      simp

/-- Index in the reverse of a repetition-free list. -/
lemma idxOf_reverse (l : List Cell) (hnd : l.Nodup) (a : Cell) (ha : a ∈ l) :
    l.reverse.idxOf a = l.length - 1 - l.idxOf a := by
  have hi : l.idxOf a < l.length := List.idxOf_lt_length_iff.2 ha
  have hj : l.length - 1 - l.idxOf a < l.reverse.length := by simp; omega
  have e : l.reverse[l.length - 1 - l.idxOf a] = a := by
    rw [List.getElem_reverse]
    have : l.length - 1 - (l.length - 1 - l.idxOf a) = l.idxOf a := by omega
    simp only [this, List.getElem_idxOf]
  have := (List.nodup_reverse.2 hnd).idxOf_getElem _ hj
  rwa [e] at this

/-- **L6 (label dictionary).** If `U'` is repetition-free with `|U'| = |U|`, then `Σ`'s label on
`a ∈ U'` — the row-plus-one of the partner of `a` in `U'.reverse.zip U.reverse` — equals Φ's
label `gU U (valOf U' a)`. -/
theorem label_transport (U U' : List Cell) (hl : U'.length = U.length) (hnd : U'.Nodup)
    (a : Cell) (ha : a ∈ U') :
    ofList (U'.reverse.zip (U.reverse.map fun h => h.1 + 1)) a = gU U (valOf U' a) := by
  have hi : U'.idxOf a < U'.length := List.idxOf_lt_length_iff.2 ha
  unfold ofList
  rw [lookup_zip _ _ a (List.mem_reverse.2 ha) (by simp [hl]), idxOf_reverse U' hnd a ha]
  have hk : U'.length - 1 - U'.idxOf a < (U.reverse.map fun h => h.1 + 1).length := by
    simp; omega
  rw [List.getElem?_eq_getElem hk]
  simp only [Option.getD_some, List.getElem_map, List.getElem_reverse, gU, uVal, valOf]
  have hU : U.length - 1 - (U'.length - 1 - U'.idxOf a) = U'.idxOf a := by omega
  have hU2 : U'.idxOf a < U.length := by omega
  simp only [hU, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hU2, Option.getD_some]

/-- **`thm:G4` (Φ(f) = Σ(rr f)), assembled under named hypotheses.** `hbox`, `hcol`: the standing
hypotheses of `def:phi`(1) (`A/B` in the box, `f` column-strict). `hstd`: `u_{A^∨}` followed by Φ's
holes is a standard filling. `hokR`, `hokF`: column-injectivity along Φ's and Σ's runs (the
recalled Fulton fact; NOT discharged here). Conclusion: same support, same values. -/
theorem thm_G4_of_slideOK (R C : ℕ) (A B : List ℕ) (f : Cell → ℕ)
    (hbox : InBox R C (skewCells A B).toFinset) (hcol : ColInj (skewCells A B).toFinset f)
    (hstd : StdFrom ∅ (skewCells (compl R C A) [] ++ holesWith tilde R C A B f))
    (hokR : SlidesOK revRule (R + C) (skewCells (compl R C A) []).toFinset uVal
      (holesWith tilde R C A B f))
    (hokF : SlidesOK fwdRule ((holesWith tilde R C A B f).length + 1)
      (holesWith tilde R C A B f).toFinset
      (rr R C (((skewCells A B).map f).foldr max 0) f)
      (skewCells (compl R C A) []).reverse) :
    (phi R C A B f).1 = (sigmaRR R C A B f).1 ∧
    ∀ a ∈ (phi R C A B f).1, (phi R C A B f).2 a = (sigmaRR R C A B f).2 a := by
  set U := skewCells (compl R C A) [] with hUdef
  set F := holesWith tilde R C A B f with hFdef
  set X := rr R C (((skewCells A B).map f).foldr max 0) f with hXdef
  -- L0
  have L0 : (U ++ F).Nodup := (stdFrom_nodup ∅ _ hstd).1
  -- L1
  have L1 : rowsW F.length U.length (U ++ F) = colsW U.length 0 F.length (U ++ F) :=
    rowsW_eq_colsW U.length F.length (U ++ F) (by simp) hstd
  -- L2
  have L2 : (phi R C A B f).1 = ((colsW U.length 0 F.length (U ++ F)).drop F.length).toFinset ∧
      ∀ a ∈ (phi R C A B f).1, (phi R C A B f).2 a =
        gU U (valOf ((colsW U.length 0 F.length (U ++ F)).drop F.length) a) :=
    phi_eq_window R C A B f L0 hokR
  -- L3, L4
  have L3 : F.toFinset = ((skewCells A B).map (rot R C)).toFinset :=
    L3_holes_toFinset R C A B f hbox hcol
  have L4 : ∀ a ∈ F, std F.toFinset X a = valOf F a := L4_std_eq_valOf R C A B f hbox hcol
  -- L5
  have L5 : (slides fwdRule (((skewCells A B).map (rot R C)).toFinset.card + (compl R C A).sum + 1)
      ((skewCells A B).map (rot R C)).toFinset X (sigmaHoles (compl R C A))).2.2 =
      ((rowsW F.length U.length (U ++ F)).drop F.length).reverse := by
    rw [sigmaHoles_eq, ← L3]
    exact V_rowsW_of_slidesOK_fuel _ U F X L0 L4 hokF
      (by have := List.toFinset_card_of_nodup (List.nodup_append.1 L0).2.1; omega)
  -- L6
  set W := rowsW F.length U.length (U ++ F) with hW
  set U' := W.drop F.length with hU'
  have hWnd : W.Nodup :=
    (stdFrom_nodup ∅ _ (stdFrom_rowsW ∅ (by simp [IsDiag]) F.length U.length 0 (U ++ F)
      (by simp [Nat.add_comm]) hstd)).1
  have hU'nd : U'.Nodup := hWnd.sublist (List.drop_sublist _ _)
  have hlen : U'.length = U.length := by
    have h := congrArg List.length L5
    rw [slides_length, sigmaHoles_eq, List.length_reverse, List.length_reverse] at h
    exact h.symm
  have hsig : sigmaRR R C A B f =
      ((U'.reverse).toFinset, ofList (U'.reverse.zip (U.reverse.map fun h => h.1 + 1))) := by
    show sigmaWith sigmaHoles (compl R C A) ((skewCells A B).map (rot R C)).toFinset X = _
    unfold sigmaWith
    simp only []
    rw [L5, sigmaHoles_eq]
  rw [← L1] at L2
  obtain ⟨P1, P2⟩ := L2
  rw [hsig]
  refine ⟨?_, fun a ha => ?_⟩
  · rw [P1]; ext y; simp [hU']
  · rw [P2 a ha]
    exact (label_transport U U' hlen hU'nd a (by
      have : a ∈ U'.toFinset := P1 ▸ ha
      exact List.mem_toFinset.1 this)).symm

/-! The kernel control `g4_hyps_control_33` (all five hypotheses on the 310 `phiData33`
instances, `decide +kernel`) did not finish inside a 25-minute build on 2026-11-22 c2; it was
moved out of the library (scratch copy: `proofs/code-1122c2-lean-G4/control_removed.lean`).
Non-vacuity is therefore NOT kernel-checked in this file. -/

end TworowD4Kernel.G4Assembly
