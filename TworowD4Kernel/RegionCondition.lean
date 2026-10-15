/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ContentDictionary

/-!
# `prop:dict`, region half (**D3**): cylindricity *is* the region condition

`ContentDictionary.toTableau` left exactly one hypothesis undischarged:

```
hmem : ∀ a : Fin n, Mem h w (F.xOf (a.1 + 1))
```

that is, **D3** — every lattice point of the path lies in
`R = {x : x₁ ≥ x₂ ≥ ⋯ ≥ x_h ≥ x₁ - w}`.  This is HKKO,
**arXiv:2301.13117, Prop. 2.7** proper.

## Why a new type was needed, and what the scope audit found

`ContentDictionary.Filling` carries row-strictness **and nothing else** — that is why D1 and
D2 came out stronger than the paper's statement.  It is also why D3 *cannot be stated* over
`Filling`: there is no column condition and no cylindric identification to consume, and D3 is
false without them (see `ablation_colWeak` and `ablation_wrapCol` below, which exhibit
row-strict fillings whose paths leave `R`).

So the first deliverable is a **definition**: `CylFilling`, a `Filling` plus the four things
the region condition actually eats.  The forgetful map is `CylFilling.toFilling`, supplied by
`extends`, so D1 and D2 transfer along it verbatim — they are *not* re-proved
(`content_eq_sum_rowCount`, `boxCount_occ`, `xOf_succ` are all used through `toFilling`).

## HKKO's proof, and what formalising it cost

HKKO's proof of Prop. 2.7 is two sentences (arXiv:2301.13117, p. 8):

> "We obtain the proposition by reading the vectors of row lengths of the subtableaux
> containing all entries at most `i` […]  The property that the tableau is `(h,w)`-cylindric
> translates into the property that the lattice walk is in the given region."

The second sentence is the whole of D3, and formalising it is a scope audit of that one
verb *translates*.  It splits into **two** inequalities fed by **four** hypotheses:

* `x_{i+1} ≤ x_i` for `1 ≤ i < h` — from `colWeak` (columns weakly increase) and `lenAnti`
  (`λ` is a partition, so the box above a box of the subtableau exists);
* `x_1 - w ≤ x_h` — from `wrapCol` (the column condition **at the seam**, between row `h` and
  the translate `T + (h, -w)` of row `1`) and `wrapLen` (`λ₁ - λ_h ≤ w`, which is exactly
  `λ ∈ Par(h,w)` and is what makes `T ∪ (T + (h,-w))` a valid skew shape — HKKO Def. 2.1,
  Def. 2.2).

Each of the four is a separate field below.  The audit's output is that the first inequality
and the second are fed by **disjoint** pairs of hypotheses: the interior of the region is the
column condition, the wrap is the cylindricity, and neither borrows from the other.

## The endpoint asset, measured rather than hoped

The brief carried an asset from 2026-10-13: the paper uses the region condition "only at the
endpoint `x + θ`", and asked whether that makes D3 a statement about *one* point.  **It does
not.**  `Tableau.mem` quantifies over `a : Fin n`, i.e. over the `n` points
`x^{(1)}, …, x^{(n)}`, each the endpoint of its own step; what the endpoint-only reading buys
is the exemption of the single point `x^{(0)}`.  So the saving is `n + 1 ↦ n` points, not
`n + 1 ↦ 1`.  `mem_xOf` below is therefore proved for **every** `b : ℕ` — which is both the
honest obligation and, as it happens, no harder, since the proof is uniform in `b`.

## Provenance

* Region `R`, lattice-path model, and Prop. 2.7: Huh–Kim–Krattenthaler–Okada,
  **arXiv:2301.13117, Prop. 2.7** (statement and proof, p. 8).
* `(h,w)`-cylindric RST, and `T ∪ (T + (h,-w))` an RST of a valid skew shape:
  **arXiv:2301.13117, Def. 2.1**; `Par(h,w)` and `λ₁ - λ_h ≤ w`: **Def. 2.2**.
* `prop:dict`, `(eq:mvec)`, `(eq:Psi)`:
  `proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`.
-/

set_option autoImplicit false

namespace TworowD4Kernel.RegionCondition

open Finset Polynomial TworowD4Kernel.Region TworowD4Kernel.Bridge
open TworowD4Kernel.TableauReduction TworowD4Kernel.ContentDictionary

variable {h n : ℕ} [NeZero h] {w : ℕ}

/-! ### The model

Rows are indexed by `ZMod h`, so the cyclic successor `r + 1` is the row below `r` **on the
cylinder**: for `r = -1` (the bottom row `h`) it is row `1` of the translate `T + (h, -w)`,
whose column `j` carries the entry of row `1`, column `j + w` of `T`.  That single wrap is the
only asymmetry, and it is why `colWeak`/`lenAnti` exclude `r = -1` and `wrapCol`/`wrapLen`
treat it separately. -/

/-- An **`(h,w)`-cylindric row-strict filling**: a `Filling` (row-strict, HKKO's RST row
condition) together with the four conditions `prop:dict`'s region half consumes.

Faithfulness to HKKO Def. 2.1 (`T ∪ (T + (h,-w))` is an RST of a valid skew shape):
row-strictness of the union is row-strictness of `T` (`toFilling.rowStrict`); weak column
increase of the union is `colWeak` in the interior and `wrapCol` at the seam; and the union
being a skew shape of a shape in `Par(h,w)` is `lenAnti` together with `wrapLen`. -/
structure CylFilling (h : ℕ) [NeZero h] (w : ℕ) extends Filling h where
  /-- `λ` is a partition: row lengths weakly decrease down the fundamental domain. -/
  lenAnti : ∀ r : ZMod h, r ≠ -1 → len (r + 1) ≤ len r
  /-- Columns weakly increase, in the interior of the fundamental domain. -/
  colWeak : ∀ r : ZMod h, r ≠ -1 → ∀ j : ℕ, j < len (r + 1) → ent r j ≤ ent (r + 1) j
  /-- `λ₁ - λ_h ≤ w`, i.e. `λ ∈ Par(h,w)` — HKKO Def. 2.2.  Equivalently, the translate
  `T + (h,-w)` of row `1` does not stick out past the end of row `h`. -/
  wrapLen : len 0 ≤ len (-1) + w
  /-- The column condition **at the seam**: row `h` sits above row `1` of `T + (h,-w)`, whose
  column `j` carries `ent 0 (j + w)`. -/
  wrapCol : ∀ j : ℕ, j + w < len 0 → ent (-1) j ≤ ent 0 (j + w)

namespace CylFilling

variable (F : CylFilling h w)

/-! ### The two inequalities of `R`, at the level of row lengths -/

/-- **Interior of `R`.**  The subtableau of entries `< b` has weakly decreasing row lengths.

Mechanism: a box `(r+1, j)` of the subtableau has `j < len (r+1) ≤ len r` (`lenAnti`), so the
box `(r, j)` exists, and `ent r j ≤ ent (r+1) j < b` (`colWeak`).  So the row-`(r+1)` index
set injects into the row-`r` one. -/
theorem rowLen_anti (r : ZMod h) (hr : r ≠ -1) (b : ℕ) :
    F.toFilling.rowLen (r + 1) b ≤ F.toFilling.rowLen r b := by
  refine Finset.card_le_card fun j hj => ?_
  simp only [mem_filter, mem_range] at hj ⊢
  have hlen := F.lenAnti r hr
  have hcol := F.colWeak r hr j hj.1
  exact ⟨by omega, by omega⟩

/-- **The wrap of `R`.**  `x_1 ≤ x_h + w` for the subtableau of entries `< b`.

Mechanism: the boxes of row `1` in columns `≥ w` are pushed down the seam.  A box `(1, j)`
with `j ≥ w` has `(j - w) + w < len 0 ≤ len (-1) + w` (`wrapLen`), so the box `(-1, j - w)`
of row `h` exists, and `ent (-1) (j - w) ≤ ent 0 j < b` (`wrapCol`).  The `≤ w` boxes of row
`1` in columns `< w` are the only ones unaccounted for, which is exactly the `+ w`. -/
theorem rowLen_wrap (b : ℕ) :
    F.toFilling.rowLen 0 b ≤ F.toFilling.rowLen (-1) b + w := by
  classical
  have hsub :
      ((range (F.len 0)).filter fun j => F.ent 0 j < b) ⊆
        (range w) ∪ (((range (F.len (-1))).filter fun j => F.ent (-1) j < b).image (· + w)) := by
    intro j hj
    simp only [mem_filter, mem_range] at hj
    rcases Nat.lt_or_ge j w with hlt | hge
    · exact Finset.mem_union_left _ (mem_range.2 hlt)
    · refine Finset.mem_union_right _ (Finset.mem_image.2 ⟨j - w, ?_, by omega⟩)
      have hjw : (j - w) + w < F.len 0 := by omega
      have hcol := F.wrapCol (j - w) hjw
      have hlen := F.wrapLen
      rw [Nat.sub_add_cancel hge] at hcol
      simp only [mem_filter, mem_range]
      exact ⟨by omega, by omega⟩
  calc F.toFilling.rowLen 0 b
      = ((range (F.len 0)).filter fun j => F.ent 0 j < b).card := rfl
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (range w).card
          + (((range (F.len (-1))).filter fun j => F.ent (-1) j < b).image (· + w)).card :=
        Finset.card_union_le _ _
    _ ≤ w + F.toFilling.rowLen (-1) b := by
        gcongr
        · simp
        · exact Finset.card_image_le
    _ = F.toFilling.rowLen (-1) b + w := Nat.add_comm _ _

/-! ### D3

`Mem` is stated in Model B's `1`-based `ℕ` indices, and `Filling.xOf` reads row `i` as the
`ZMod h` row `(i : ZMod h) - 1`.  The two lemmas above are in `ZMod h` rows, so the only work
left is the index translation — and the translation is where the `- 1` could have come apart,
so it is done explicitly rather than by `simp`. -/

omit [NeZero h] in
/-- `(i : ZMod h) ≠ 0` for `1 ≤ i < h`: the row index does not wrap inside the fundamental
domain.  This is what feeds the `r ≠ -1` side conditions of `rowLen_anti`. -/
theorem natCast_ne_zero_of_lt {i : ℕ} (hi1 : 1 ≤ i) (hih : i < h) : (i : ZMod h) ≠ 0 := by
  intro hc
  have hval : ((i : ZMod h)).val = i := ZMod.val_cast_of_lt hih
  rw [hc, ZMod.val_zero] at hval
  omega

/-- **D3 — HKKO Prop. 2.7.**  Every lattice point of the path of an `(h,w)`-cylindric
row-strict filling lies in the region `R`.

This is the hypothesis `ContentDictionary.toTableau` took as `hmem`, now discharged.  Proved
for **every** `b : ℕ`, not only the step endpoints — see the module docstring on the endpoint
asset. -/
theorem mem_xOf (b : ℕ) : Mem h (w : ℤ) (F.toFilling.xOf b) where
  mono := by
    intro i hi1 hih
    have hcast : (((i + 1 : ℕ)) : ZMod h) - 1 = ((i : ZMod h) - 1) + 1 := by
      push_cast; ring
    have hne : ((i : ZMod h) - 1) ≠ -1 := by
      intro hc
      exact natCast_ne_zero_of_lt hi1 hih (by linear_combination (norm := ring_nf) hc)
    simp only [Filling.xOf, hcast]
    exact_mod_cast F.rowLen_anti ((i : ZMod h) - 1) hne b
  wrap := by
    have h1 : (((1 : ℕ)) : ZMod h) - 1 = 0 := by push_cast; ring
    have hh : ((h : ℕ) : ZMod h) - 1 = -1 := by rw [ZMod.natCast_self]; ring
    simp only [Filling.xOf, h1, hh]
    have := F.rowLen_wrap b
    omega

/-! ### The composite: `prop:dict` with **no** hypothesis but the filling and its content -/

/-- **`prop:dict`, whole.**  A `Tableau` built from an `(h,w)`-cylindric row-strict filling of
content `(1ⁿ)`.  Every field is derived: `boxCount_eq_one` by D1, `step` by D2, `mem` by D3.
The only hypothesis is the content. -/
def toTableau (F : CylFilling h w) (hc : ∀ a : Fin n, F.toFilling.content a.1 = 1) :
    Tableau h n (w : ℤ) :=
  ContentDictionary.toTableau F.toFilling (w : ℤ) hc fun a => F.mem_xOf (a.1 + 1)

/-- **The full composite, with the region condition discharged.**  `ord_{t=1} Ψ_T = n` for
every `(h,w)`-cylindric row-strict filling of content `(1ⁿ)`, `h ≥ 2`.

Compare `ContentDictionary.rootMultiplicity_Psi_of_filling`, which still assumed D3. -/
theorem rootMultiplicity_Psi_of_cylFilling {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (hh : 2 ≤ h) (F : CylFilling h w) (hc : ∀ a : Fin n, F.toFilling.content a.1 = 1) :
    rootMultiplicity (1 : R) ((toTableau F hc).Psi R) = n :=
  (toTableau F hc).rootMultiplicity_Psi hh

end CylFilling

/-! ### Non-vacuity, with the contamination declared first

⚠ The 2026-10-13 lesson: a control built *by* the thing under test is not a second mechanism.
Here is what each control below is built from.

* `witCyl` **extends** `ContentDictionary.witF`, so its `Filling` data — and hence `xOf` — is
  *not* produced by anything in this file.
* `ContentDictionary.witF_mem` proves `Mem 2 2 (witF.xOf 1)` by **kernel evaluation** of the
  actual integers.  `CylFilling.mem_xOf` proves the same statement **structurally**, from
  `colWeak`/`wrapCol`.  These two routes share only the raw filling, so they are genuinely
  independent: a `sorry` in `mem_xOf` cannot reach `witF_mem`.
* `witCylT_Psi` and below are built *through* `CylFilling.toTableau`, hence **through**
  `mem_xOf`, and are therefore **contaminated** as controls for D3.  They are retained as
  controls for the *composite*, which is what they actually test. -/

section NonVacuity

/-- The one-box witness of `ContentDictionary`, promoted to a cylindric filling with `w = 2`.
`h = 2`, so `(-1 : ZMod 2) = 1` and the seam is between row `2` and row `1`.
Both column conditions hold *because every entry of `witF` is `0`*, so they are checked at
`0 ≤ 0`; `lenAnti` and `wrapLen` are decided over all of `ZMod 2`. -/
def witCyl : CylFilling 2 2 where
  toFilling := witF
  lenAnti := by decide
  colWeak := fun _ _ _ _ => Nat.le_refl 0
  wrapLen := by decide
  wrapCol := fun _ _ => Nat.le_refl 0

/-- **The independent control.**  `ContentDictionary.witF_mem` asserts exactly this, and
proves it by kernel evaluation of the integers; `mem_xOf` proves it from the cylindric
structure.  Two mechanisms, one statement. -/
theorem witCyl_mem_structural : Mem 2 (2 : ℤ) (witCyl.toFilling.xOf 1) :=
  witCyl.mem_xOf 1

/-- The same statement, by the independent route, quoted here so the two sit side by side. -/
theorem witCyl_mem_by_evaluation : Mem 2 (2 : ℤ) (witCyl.toFilling.xOf 1) :=
  witF_mem ⟨0, Nat.zero_lt_one⟩

/-- The witness tableau, with **every** field derived — content included, by D1. -/
def witCylT : Tableau 2 1 (2 : ℤ) := CylFilling.toTableau witCyl witF_content

/-- Contaminated-by-construction control for the composite: `Ψ` of the witness is `1 - X²`,
so the order of vanishing at `t = 1` answers a real question. -/
theorem witCylT_Psi : witCylT.Psi ℚ = 1 - X ^ 2 := witT_Psi

/-- The composite, end to end, with no hypothesis supplied by hand. -/
theorem witCylT_rootMultiplicity : rootMultiplicity (1 : ℚ) (witCylT.Psi ℚ) = 1 :=
  CylFilling.rootMultiplicity_Psi_of_cylFilling (by omega) witCyl witF_content

end NonVacuity

/-! ### Ablations — each cylindric field is load-bearing, and dropping it makes D3 **false**

Both ablations exhibit a `Filling` (row-strict, so D1 and D2 still hold of it) satisfying
*three* of the four cylindric conditions, whose path **leaves** `R`.  So D3 is not merely
unproved without the dropped field: its conclusion fails.

Neither ablation is built from anything in this file beyond `Filling` itself: the violated
`Mem` is decided by kernel evaluation of `xOf`, so these are independent of `mem_xOf`. -/

section Ablations

/-- In `ZMod 2` the only row that is not the seam row is row `0`.  Pulled out as its own
lemma because `decide` cannot be used on a goal with the column index `j` still free. -/
theorem eq_zero_of_ne_neg_one : ∀ r : ZMod 2, r ≠ -1 → r = 0 := by decide

/-- `h = 2`, `w = 2`: one box per row, row `1` carrying the entry `1` and row `2` the entry
`0` (`1 - i.val`).  Row-strict (each row has a single box, so the strictness hypotheses are
contradictory), `lenAnti` holds (`1 ≤ 1`), `wrapLen` holds (`1 ≤ 1 + 2`), `wrapCol` holds
vacuously (`j + 2 < 1` is never true) — only `colWeak` fails. -/
def ablF : Filling 2 where
  len := fun _ => 1
  ent := fun i _ => 1 - i.val
  rowStrict := by
    intro i j k hj hk hjk
    exfalso
    have hj' : j < 1 := hj
    have hk' : k < 1 := hk
    omega

/-- **Ablation 1 — `colWeak` is load-bearing.**  `ablF` satisfies `lenAnti`, `wrapLen` and
`wrapCol`, violates `colWeak` at `r = 0`, and its point `x^{(1)}` has `x₁ = 0 < 1 = x₂`, so
`Mem.mono` fails.  The region condition is therefore **false**, not unproved. -/
theorem ablation_colWeak :
    (∀ r : ZMod 2, r ≠ -1 → ablF.len (r + 1) ≤ ablF.len r) ∧
    ablF.len 0 ≤ ablF.len (-1) + 2 ∧
    (∀ j : ℕ, j + 2 < ablF.len 0 → ablF.ent (-1) j ≤ ablF.ent 0 (j + 2)) ∧
    ¬ (∀ r : ZMod 2, r ≠ -1 → ∀ j : ℕ, j < ablF.len (r + 1) → ablF.ent r j ≤ ablF.ent (r + 1) j)
      ∧ ¬ Mem 2 (2 : ℤ) (ablF.xOf 1) := by
  refine ⟨fun _ _ => Nat.le_refl 1, by decide, ?_, ?_, ?_⟩
  · intro j hj
    exfalso
    have hj' : j + 2 < 1 := hj
    omega
  · intro hc
    have hbad := hc 0 (by decide) 0 (Nat.zero_lt_one)
    have hbad' : (1 : ℕ) ≤ 0 := hbad
    omega
  · intro hm
    have hmono := hm.mono 1 le_rfl (by omega)
    revert hmono
    decide

/-- `h = 2`, `w = 1`: both rows of length `2`; row `1` is `(0,1)` and row `2` is `(2,3)`
(`ent i j = j + 2 * i.val`).  Row-strict, `colWeak` holds (`j ≤ j + 2`), `lenAnti` holds
(`2 ≤ 2`), `wrapLen` holds (`2 ≤ 2 + 1`) — only `wrapCol` fails, at `j = 0`, where
`ent (-1) 0 = 2 > 1 = ent 0 1`. -/
def ablFw : Filling 2 where
  len := fun _ => 2
  ent := fun i j => j + 2 * i.val
  rowStrict := by
    intro i j k _ _ hjk
    omega

/-- **Ablation 2 — `wrapCol` is load-bearing.**  `ablFw` satisfies `colWeak`, `lenAnti` and
`wrapLen`, violates `wrapCol` at `j = 0`, and its point `x^{(2)}` has
`x₁ - w = 2 - 1 = 1 > 0 = x₂`, so `Mem.wrap` fails.

This is the ablation that isolates the **cylindricity** from the column condition: the
interior inequality `x₂ ≤ x₁` still holds here (`0 ≤ 2`), and only the seam breaks. -/
theorem ablation_wrapCol :
    (∀ r : ZMod 2, r ≠ -1 → ∀ j : ℕ,
        j < ablFw.len (r + 1) → ablFw.ent r j ≤ ablFw.ent (r + 1) j) ∧
    (∀ r : ZMod 2, r ≠ -1 → ablFw.len (r + 1) ≤ ablFw.len r) ∧
    ablFw.len 0 ≤ ablFw.len (-1) + 1 ∧
    ¬ (∀ j : ℕ, j + 1 < ablFw.len 0 → ablFw.ent (-1) j ≤ ablFw.ent 0 (j + 1))
      ∧ ¬ Mem 2 (1 : ℤ) (ablFw.xOf 2) := by
  refine ⟨?_, fun _ _ => Nat.le_refl 2, by decide, ?_, ?_⟩
  · intro r hr j _
    have hr0 : r = 0 := eq_zero_of_ne_neg_one r hr
    subst hr0
    have hval : ((0 : ZMod 2) + 1).val = 1 := by decide
    change j + 2 * (0 : ZMod 2).val ≤ j + 2 * ((0 : ZMod 2) + 1).val
    rw [hval]
    simp
  · intro hc
    have hbad := hc 0 (by decide)
    have hbad' : (2 : ℕ) ≤ 1 := hbad
    omega
  · intro hm
    have hwrap := hm.wrap
    revert hwrap
    decide

end Ablations

end TworowD4Kernel.RegionCondition
