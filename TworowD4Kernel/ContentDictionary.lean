/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.TableauReduction

/-!
# `prop:dict`, content half: a tableau of content `(1ⁿ)` has one-box steps

`TableauReduction.Tableau` carries `boxCount_eq_one` as a **hypothesis field**.  That field is
the output of `prop:dict` of `proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`, and this
file turns it into a theorem by supplying the tableau side of the dictionary.

## The split, made before any Lean was written

`prop:dict` is not one sentence.  Split at the implication arrows, it is three:

* **(D1) content ⟹ box count.**  For a *row-strict* filling, `Σ_i θ^{(a)}_i = α_a`, where
  `θ^{(a)}_i` is the number of boxes of row `i` carrying entry `a` and `α_a` is the number of
  boxes carrying entry `a`.  Two sub-facts: row-strictness makes `θ^{(a)}_i ≤ 1` (so the step
  really is a `0/1` vector, which is what lets it live in `ZMod h → Bool` at all), and the
  content is the row-fibre sum of the row counts.
* **(D2) the path.**  `x^{(b)}` is the row-length vector of the subtableau of entries `< b`,
  and `x^{(b+1)} = x^{(b)} + θ^{(b)}`.  This is `Tableau.step`.
* **(D3) the region.**  `x^{(b)} ∈ R`.  This is HKKO, **arXiv:2301.13117, Prop. 2.7** proper,
  and it is the half that consumes the column condition, the cylindric identification
  `T(i,j) = T(i+k,j-n)`, and `λ ∈ Par(h,w)`.

**D1 and D2 are proved here.  D3 is not, and remains a hypothesis** — of `toTableau`, in the
same shape `Tableau.mem` already had it.  So the obstruction count goes `1 → 1`, not `1 → 0`:
what changed is *which* statement is assumed, and it is now the geometric one rather than the
combinatorial one.  (`Tableau.mem` was already a field, so no new assumption is introduced;
`boxCount_eq_one` stops being one.)

## Domain check — the two domains, side by side, and they differ

The brief required this comparison before the statement was written, because an English noun
need not declare its domain and a typed binder must.

| | paper's `prop:dict` | `Filling` below |
|---|---|---|
| rows | `h` rows of a shape `λ ∈ Par(h,w)` | `ZMod h`, lengths `len : ZMod h → ℕ` |
| rows strictly increasing | yes | **yes** — `Filling.rowStrict` |
| columns weakly increasing | yes | **no** |
| cylindric `T(i,j) = T(i+k,j-n)` | yes | **no** |
| `λ ∈ Par(h,w)` | yes | **no** |
| entries bounded by `n` | yes | **no** |

They are not the same set: **`Filling` is strictly larger**.  That is the right direction —
D1 and D2 are *stronger* than the paper's claim, because the three dropped conditions are
consumed only by D3.  Row-strictness is the only hypothesis the content half needs, and the
`rowCount_le_one` proof below is where one can see it being spent.

This is a finding, not a convenience: the paper's proof of `prop:dict` presents the content
statement as part of the cylindric package, and it is not — it is a statement about any
row-strict filling of any shape.

## Provenance

* HKKO's lattice-path model and the region `R`: Huh–Kim–Krattenthaler–Okada,
  **arXiv:2301.13117, Prop. 2.7** ("the `a`-th step being a `0/1` vector with `α_a` ones").
* Korff's cyclic index set `J` and the relation behind `(eq:korffrel)`: Korff,
  **arXiv:1110.6356, Def. 5.5 and Lemma 5.4**.
* `prop:dict`, `(eq:mvec)`, `(eq:Psi)`, `lem:nu`, `lem:wd`:
  `proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`.
-/

-- `autoImplicit` is ON project-wide; on 2026-10-12 it silently promoted a bare `X` to a ring
-- variable and made a control hold generically.  Every implicit below is declared.
set_option autoImplicit false

namespace TworowD4Kernel.ContentDictionary

open Finset Polynomial TworowD4Kernel.Region TworowD4Kernel.Bridge
open TworowD4Kernel.TableauReduction

variable {h n : ℕ} [NeZero h]

/-! ### The model: a row-strict filling, and nothing more

Only the conditions D1 and D2 actually consume are imposed.  See the domain table above. -/

/-- A **row-strict filling**: row lengths, entries, and strict increase along rows.

`ent i j` is the entry of the box in row `i`, column `j`, and is only ever read for
`j < len i`; `rowStrict` therefore quantifies over in-range columns only.  No column
condition, no cylindric identification, no bound on the entries — see the module docstring's
domain table for why each is absent. -/
structure Filling (h : ℕ) [NeZero h] where
  /-- The length of row `i` of the (fundamental domain of the) shape. -/
  len : ZMod h → ℕ
  /-- The entry of the box in row `i`, column `j`. -/
  ent : ZMod h → ℕ → ℕ
  /-- Entries strictly increase along each row.  This is the *only* tableau condition used. -/
  rowStrict : ∀ i : ZMod h, ∀ j k : ℕ, j < len i → k < len i → j < k → ent i j < ent i k

namespace Filling

variable (F : Filling h)

/-- `θ^{(a)}_i`: the number of boxes in row `i` carrying entry `a`. -/
def rowCount (i : ZMod h) (a : ℕ) : ℕ :=
  ((range (F.len i)).filter fun j => F.ent i j = a).card

/-- **D1, first half — row-strictness is a `0/1` bound.**  A row carries at most one box of
any given entry, because `ent i ·` is strictly monotone, hence injective, on the row.

This is the step that makes `θ^{(a)}` a *Boolean* word at all: without it the step vector
would live in `ℕ^h`, and `ZMod h → Bool` would be the wrong type. -/
theorem rowCount_le_one (i : ZMod h) (a : ℕ) : F.rowCount i a ≤ 1 := by
  rw [rowCount, Finset.card_le_one]
  intro j hj k hk
  simp only [mem_filter, mem_range] at hj hk
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hs := F.rowStrict i j k hj.1 hk.1 hlt
    rw [hj.2, hk.2] at hs
    exact absurd hs (lt_irrefl a)
  · have hs := F.rowStrict i k j hk.1 hj.1 hlt
    rw [hj.2, hk.2] at hs
    exact absurd hs (lt_irrefl a)

/-- The boxes of the shape, as a `Finset` of (row, column) pairs. -/
def boxes : Finset ((_ : ZMod h) × ℕ) := univ.sigma fun i => range (F.len i)

/-- `α_a`: the **content**, the number of boxes carrying entry `a`.  This is the definition
the paper uses — a count over boxes, not over rows. -/
def content (a : ℕ) : ℕ := ((F.boxes).filter fun b => F.ent b.1 b.2 = a).card

/-- **D1, second half — the fibre decomposition.**  The boxes of entry `a` are partitioned by
the row they sit in, so `α_a = Σ_i θ^{(a)}_i`.  Stated separately from `content` so that the
decomposition is a theorem rather than a definitional choice. -/
theorem content_eq_sum_rowCount (a : ℕ) :
    F.content a = ∑ i : ZMod h, F.rowCount i a := by
  have hset : ((F.boxes).filter fun b => F.ent b.1 b.2 = a)
      = univ.sigma fun i => (range (F.len i)).filter fun j => F.ent i j = a := by
    ext b
    simp only [boxes, mem_filter, Finset.mem_sigma, mem_range]
    tauto
  rw [content, hset, Finset.card_sigma]
  rfl

/-- The step word `θ^{(a)}` of Model A: row `i` is occupied by the `a`-th step exactly when it
carries a box of entry `a`. -/
def occ (a : ℕ) : ZMod h → Bool := fun i => decide (F.rowCount i a ≠ 0)

/-- **D1 — `Σ_i θ^{(a)}_i = α_a`.**  The box count of the `a`-th step word is the content at
`a`.  This is the sentence `Tableau.boxCount_eq_one` was assuming.

`rowCount_le_one` is spent exactly here: it is what turns the indicator `θ^{(a)}_i ≠ 0` back
into the number `θ^{(a)}_i`. -/
theorem boxCount_occ (a : ℕ) : boxCount (F.occ a) = F.content a := by
  rw [boxCount_eq_sum, content_eq_sum_rowCount]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := F.rowCount_le_one i a
  by_cases hz : F.rowCount i a = 0
  · simp [occ, hz]
  · have h2 : F.rowCount i a = 1 := by omega
    simp [occ, h2]

/-- Content `1` at `a` gives a one-box step — `boxCount_eq_one`, now derived. -/
theorem boxCount_occ_eq_one {a : ℕ} (ha : F.content a = 1) : boxCount (F.occ a) = 1 :=
  (F.boxCount_occ a).trans ha

/-! ### D2: the path, and its step relation

`x^{(b)}` is the row-length vector of the subtableau of entries `< b`.  Entries are `0`-based
here, matching `occ : Fin n → _`, so "entries `< b`" is the paper's "entries `≤ b`" with the
paper's `1`-based labels. -/

/-- The length of row `i` of the subtableau of entries `< b`. -/
def rowLen (i : ZMod h) (b : ℕ) : ℕ :=
  ((range (F.len i)).filter fun j => F.ent i j < b).card

/-- The lattice point `x^{(b)}` of HKKO's path, in **Model B**'s `1`-based `ℕ` indexing.
The `- 1` is `Bridge.toNatWord`'s, and is here for the same reason: `idxEquiv` sends `0 ↦ 1`,
so a `1`-based reading of a `ZMod h`-indexed vector must look one slot down. -/
def xOf (b : ℕ) : ℕ → ℤ := fun i => (F.rowLen ((i : ZMod h) - 1) b : ℤ)

/-- The row-length recursion: passing from entries `< b` to entries `< b+1` adds exactly the
boxes of entry `b`. -/
theorem rowLen_succ (i : ZMod h) (b : ℕ) :
    F.rowLen i (b + 1) = F.rowLen i b + F.rowCount i b := by
  rw [rowLen, rowLen, rowCount, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hlt : F.ent i j < b
  · simp [hlt, Nat.lt_succ_of_lt hlt, Nat.ne_of_lt hlt]
  · by_cases heq : F.ent i j = b
    · rw [heq]; simp
    · have hnlt : ¬ F.ent i j < b + 1 := by omega
      simp [hlt, heq, hnlt]

/-- **D2 — the step relation.**  `x^{(b+1)} = x^{(b)} + θ^{(b)}`, verbatim
`Tableau.step`, and it holds at **every** `ℕ` index, not only on `[1, h]`.

The `1`-based transport and the `0`-based word agree because both are defined through the
same `· - 1`; this is the only place the two could have come apart. -/
theorem xOf_succ (b : ℕ) : F.xOf (b + 1) = shift (F.xOf b) (toNatWord (F.occ b)) := by
  funext i
  simp only [xOf, shift, stepVal, toNatWord, rowLen_succ]
  have h1 := F.rowCount_le_one ((i : ZMod h) - 1) b
  by_cases hz : F.rowCount ((i : ZMod h) - 1) b = 0
  · simp [occ, hz]
  · have h2 : F.rowCount ((i : ZMod h) - 1) b = 1 := by omega
    simp [occ, h2]

end Filling

/-! ### The constructor: `boxCount_eq_one` is now an output, not an input -/

/-- **Target — a `Tableau` built from a row-strict filling of content `(1ⁿ)`.**

`boxCount_eq_one` and `step` are *derived* (D1, D2).  The only hypothesis beyond the filling
itself is `hmem`, which is D3 — HKKO's region condition, **arXiv:2301.13117, Prop. 2.7** —
and it was already a field of `Tableau`, so nothing new is assumed. -/
def toTableau (F : Filling h) (w : ℤ) (hc : ∀ a : Fin n, F.content a.1 = 1)
    (hmem : ∀ a : Fin n, Mem h w (F.xOf (a.1 + 1))) : Tableau h n w where
  x := F.xOf
  occ := fun a => F.occ a.1
  boxCount_eq_one := fun a => F.boxCount_occ_eq_one (hc a)
  step := fun a => F.xOf_succ a.1
  mem := hmem

/-- **The composite, with the content hypothesis discharged.**
`ord_{t=1} Ψ_T = n` for every row-strict filling whose content is `(1ⁿ)` and whose path stays
in the region.  Compare `Tableau.rootMultiplicity_Psi`, which assumes the box counts; here
they are computed from the tableau. -/
theorem rootMultiplicity_Psi_of_filling {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (hh : 2 ≤ h) (F : Filling h) (w : ℤ) (hc : ∀ a : Fin n, F.content a.1 = 1)
    (hmem : ∀ a : Fin n, Mem h w (F.xOf (a.1 + 1))) :
    rootMultiplicity (1 : R) ((toTableau F w hc hmem).Psi R) = n :=
  (toTableau F w hc hmem).rootMultiplicity_Psi hh

/-! ### Target 2 — non-vacuity, with `boxCount_eq_one` now derived

`TableauReduction.wit` exhibited a `Tableau` whose `boxCount_eq_one` was *supplied*.  The
witness below exhibits a `Filling` whose content is **computed** by the kernel, so the one-box
property is an output of D1 rather than an input.  Its `Ψ` is computed outright and is
`1 - X²` — not a unit, so `rootMultiplicity` is being asked a real question — and the
computation does not route through the reduction, so it corroborates by a second mechanism. -/

section NonVacuity

/-- One box, in row `0`, carrying entry `0`: `h = 2`, `w = 2`, `n = 1`. -/
def witF : Filling 2 where
  len := fun i => if i = 0 then 1 else 0
  ent := fun _ _ => 0
  rowStrict := by
    intro i j k hj hk hjk
    by_cases hi : i = 0 <;> simp [hi] at hj hk
    omega

/-- **The content is computed, not assumed.**  This is the hypothesis that used to be
`Tableau.boxCount_eq_one`; the kernel decides it. -/
theorem witF_content : ∀ a : Fin 1, witF.content a.1 = 1 := by decide

/-- D3 for the witness — the only hypothesis left.  `x^{(1)} = (1, 0)`, and
`1 ≥ 0 ≥ 1 - 2`. -/
theorem witF_mem : ∀ a : Fin 1, Mem 2 2 (witF.xOf (a.1 + 1)) := by
  intro a
  fin_cases a
  refine ⟨?_, ?_⟩
  · intro i hi1 hi2
    interval_cases i
    · decide
  · decide

/-- The witness tableau, built by `toTableau`: every field but `mem` is derived. -/
def witT : Tableau 2 1 2 := toTableau witF 2 witF_content witF_mem

/-- The derived step word is the unit vector at cyclic position `0` — D1 and D2 agreeing with
`TableauReduction.witOcc`, which was written by hand. -/
theorem witT_occ : witT.occ 0 = fun j : ZMod 2 => decide (j = 0) := by
  funext j; revert j; decide

/-- `ν(T) = 1` for the witness: the cyclic ascent set genuinely fires. -/
theorem witT_nuT : witT.nuT = 1 := by
  rw [Tableau.nuT, nu, Fin.sum_univ_one, witT_occ]
  decide

/-- The ascent sits at Model B index `2`, the wrap slot Macdonald's open `ψ` does not have. -/
theorem witT_natJ : natJ (witT.occ 0) = {2} := by
  rw [witT_occ]; exact natJ_unit_zero_at_two

/-- `m_2(x^{(0)}) = w - (x_1 - x_2) = 2`: the wrapped branch of `(eq:mvec)` is exercised. -/
theorem witT_multNat : multNat 2 2 (witT.x 0) 2 = 2 := by decide

/-- **`Ψ` of the witness is `1 - X²`.**  Non-constant, so the composite answers a real
question. -/
theorem witT_Psi : witT.Psi ℚ = 1 - X ^ 2 := by
  rw [Tableau.Psi, Fin.prod_univ_one, witT_natJ, Finset.prod_singleton]
  norm_num [witT_multNat]

/-- And the composite agrees: `ord_{t=1}(1 - X²) = 1 = n`. -/
theorem witT_rootMultiplicity : rootMultiplicity (1 : ℚ) (witT.Psi ℚ) = 1 :=
  witT.rootMultiplicity_Psi (by omega)

end NonVacuity

/-! ### Ablation — row-strictness is load-bearing, and dropping it makes D1 *false* -/

/-- **Ablation.**  Without `rowStrict`, `boxCount_occ` is not merely unproved — its conclusion
is false.  The data below is `h = 2`, row `0` of length `2` with both boxes carrying entry `0`:
the row-sum of row counts (the right-hand side of `content_eq_sum_rowCount`) is `2`, while the
box count of the Boolean word (the right-hand side of `boxCount_eq_sum`) is `1`.

The two expressions are literally the two sides `boxCount_occ` equates, with `Filling.rowCount`
unfolded, so this is an ablation of the theorem and not of a paraphrase. -/
theorem ablation_rowStrict :
    ∃ (len : ZMod 2 → ℕ) (ent : ZMod 2 → ℕ → ℕ),
      (∑ i : ZMod 2, ((range (len i)).filter fun j => ent i j = 0).card) = 2 ∧
      (∑ i : ZMod 2,
        (if ((range (len i)).filter fun j => ent i j = 0).card ≠ 0 then 1 else 0 : ℕ)) = 1 := by
  refine ⟨fun i => if i = 0 then 2 else 0, fun _ _ => 0, ?_, ?_⟩ <;> decide

end TworowD4Kernel.ContentDictionary
