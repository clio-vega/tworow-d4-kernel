/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.IndexModelBridge

/-!
# The tableau-to-word reduction: `ν(T) = n` at content `(1ⁿ)`

This file closes the **last** obstruction to `ord_{t=1} Ψ_T = ν(T)`.

## What was missing, stated exactly

`ZMod.nu_eq_card_of_content_ones` (`CyclicAscent.lean`) proves
`Σ_a |J(θ^{(a)})| = n` for words **already written** as `fun j => decide (j = p a)` — that
is, for words presented in unit-vector form.  The paper's Lemma `lem:nu` quantifies over the
words a *path* produces, and its first sentence is the step Lean did not carry:

> "Each step has `Σ_i θ^{(a)}_i = 1`, so `θ^{(a)}` has a single `1`, at some position `p_a`."

Lean's domain was `{words of the form e_p}`; the paper's domain was
`{words whose letters sum to 1}`.  Those are the same set, but *that they are* is a theorem,
and it is `eq_unitVector_of_boxCount_one` below.  The asymmetry was invisible in English
because the noun "strip" hid the quantifier; a typed binder cannot.

## The scope boundary, said once and precisely

What is formalised here is the implication

  **(b)**  `Σ_i θ_i = 1`  ⟹  `θ = e_p` for a unique `p`  ⟹  `|J(θ)| = 1`.

What is **not** formalised, and is a *different* gap, is

  **(a)**  that an HKKO cylindric tableau of content `α` corresponds to a path in the region
          `R` whose `a`-th step satisfies `Σ_i θ^{(a)}_i = α_a`.

(a) is `prop:dict` of `proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex` (the
semistandard/row-strict transpose dictionary, plus Korff's Lemma 5.4 relation), and it is
carried here as a **hypothesis field** of `Tableau`, not as a theorem.  `boxCount` is defined
as `Σ_i θ_i`, so the field `boxCount_eq_one` reads verbatim as the paper's `α = (1ⁿ)`.
Nothing below assumes anything else about tableaux.

## Provenance

* Index set `J(θ) = {i ∈ ℤ/hℤ : θ_i = 0, θ_{i+1} = 1}` — Korff, **arXiv:1110.6356, Def. 5.5**.
* Region `R = {x : x_1 ≥ ⋯ ≥ x_h ≥ x_1 - w}` and the multiplicity vector `(eq:mvec)` —
  Huh–Kim–Krattenthaler–Okada, **arXiv:2301.13117, Prop. 2.7**.
* `Ψ_P` is `(eq:Psi)`, Lemma `lem:nu` is the target, Lemma `lem:wd` is gap 3
  (`Region.one_le_multNat_of_mem_J`), all of
  `proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`.
-/

-- `autoImplicit` is ON project-wide (`lakefile.toml` sets only `relaxedAutoImplicit = false`).
-- On 2026-10-12 it silently promoted a bare `X` to a ring *variable*, making a `ring` control
-- hold generically while saying nothing about `Polynomial.X`.  Opt out: every implicit below
-- is declared.
set_option autoImplicit false

namespace TworowD4Kernel.TableauReduction

open Finset Polynomial TworowD4Kernel.Region TworowD4Kernel.CyclicAscent TworowD4Kernel.Bridge

variable {h n : ℕ} [NeZero h] {w : ℤ}

/-! ### Step (b): a one-box step *is* a unit vector -/

/-- The number of boxes a step adds: the paper's `Σ_{i} θ_i` for `θ ∈ {0,1}^h`.  Defined as
the cardinality of the support, which is the same natural number and is what
`Finset.card_eq_one` speaks about. -/
def boxCount (θ : ZMod h → Bool) : ℕ := (univ.filter fun i => θ i = true).card

/-- `boxCount` is the paper's sum `Σ_i θ_i` on the nose, with `θ_i ∈ {0,1} ⊆ ℕ`.  Recorded so
that the hypothesis `boxCount θ = 1` cannot be read as a different statistic than `α_a = 1`. -/
theorem boxCount_eq_sum (θ : ZMod h → Bool) :
    boxCount θ = ∑ i : ZMod h, (if θ i then 1 else 0 : ℕ) := by
  rw [boxCount, Finset.card_filter]

/-- **The reduction, step (b).**  A step whose letters sum to `1` *is* a unit vector: there is
a position `p` with `θ = e_p`.  This is the sentence of `lem:nu` that Lean did not carry.

The proof is `Finset.card_eq_one`: a support of size one is a singleton `{p}`, and a `Bool`
agreeing with `· = p` pointwise is that function. -/
theorem eq_unitVector_of_boxCount_one {θ : ZMod h → Bool} (hθ : boxCount θ = 1) :
    ∃ p : ZMod h, θ = fun j => decide (j = p) := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hθ
  refine ⟨p, funext fun j => ?_⟩
  have hiff : θ j = true ↔ j = p := by
    constructor
    · intro hj
      have : j ∈ ({p} : Finset (ZMod h)) := hp ▸ mem_filter.mpr ⟨mem_univ j, hj⟩
      simpa using this
    · intro hj
      subst hj
      have hmem : j ∈ univ.filter fun i => θ i = true := by rw [hp]; exact mem_singleton_self j
      exact (mem_filter.mp hmem).2
  rw [Bool.eq_iff_iff, decide_eq_true_eq]
  exact hiff

omit [NeZero h] in
/-- The position is unique: `e_p = e_q` forces `p = q`.  Without this, "a single `1`, at some
position `p_a`" would be a statement about an unspecified `p_a`, and the singleton
`J(e_p) = {p - 1}` would not identify *which* ascent the box contributes. -/
theorem unitVector_injective {p q : ZMod h}
    (hpq : (fun j : ZMod h => decide (j = p)) = fun j => decide (j = q)) : p = q := by
  have := congrFun hpq p
  simpa using this.symm

/-- **The local count from the paper's hypothesis.**  `Σ_i θ_i = 1` and `h ≥ 2` give
`|J(θ)| = 1`: the composite of step (b) with `ZMod.card_ascentSet_unitVector`. -/
theorem card_J_of_boxCount_one (hh : 2 ≤ h) {θ : ZMod h → Bool} (hθ : boxCount θ = 1) :
    (ZMod.J θ).card = 1 := by
  obtain ⟨p, rfl⟩ := eq_unitVector_of_boxCount_one hθ
  exact ZMod.card_ascentSet_unitVector hh p

/-- The set form, which says *where* the ascent is: `J(θ) = {p - 1}` where `p` is the box. -/
theorem ascentSet_of_boxCount_one (hh : 2 ≤ h) {θ : ZMod h → Bool} (hθ : boxCount θ = 1) :
    ∃ p : ZMod h, θ = (fun j => decide (j = p)) ∧ ZMod.J θ = {p - 1} := by
  obtain ⟨p, hp⟩ := eq_unitVector_of_boxCount_one hθ
  exact ⟨p, hp, by rw [hp]; exact ZMod.ascentSet_unitVector hh p⟩

/-! ### Lemma `lem:nu`, over the words a path actually produces -/

/-- `ν(P) = Σ_a |J(θ^{(a)})|`, the statistic of `(eq:Psi)`. -/
def nu (θ : Fin n → ZMod h → Bool) : ℕ := ∑ a : Fin n, (ZMod.J (θ a)).card

/-- **Target 1 — Lemma `lem:nu`.**  `ν(P) = n` for *every* family of steps each of which adds
one box, with no assumption that the steps are presented in unit-vector form.

This is the statement the paper proves.  Contrast `ZMod.nu_eq_card_of_content_ones`, which is
the same count over the narrower domain of words already written as `e_{p a}`. -/
theorem nu_eq_of_content_ones (hh : 2 ≤ h) (θ : Fin n → ZMod h → Bool)
    (hc : ∀ a, boxCount (θ a) = 1) : nu θ = n := by
  rw [nu, Finset.sum_congr rfl fun a _ => card_J_of_boxCount_one hh (hc a)]
  simp

/-! ### Target 2 — the composite `ord_{t=1} Ψ_T = ν(T) = n`

The states of the path live in Model B (`1`-based `ℕ → ℤ`, because the region condition is not
cyclic) and the step words in Model A (`ZMod h → Bool`, because `J` is).  `Bridge.toNatWord`
is the translation, and it is the only place the `- 1` appears. -/

/-- A **path of content `(1ⁿ)` in HKKO's region**, in the minimal form `lem:nu` and `lem:wd`
need together.

* `x a` is `x^{(a)}`, a point of `ℤ^h` in Model B indexing;
* `occ a` is the step word `θ^{(a)}` in Model A indexing;
* `boxCount_eq_one` is `α = (1ⁿ)` — see the scope note in the module docstring: this is
  `prop:dict`'s output, carried as a hypothesis, **not** proved here;
* `step` is `x^{(a)} = x^{(a-1)} + θ^{(a)}`;
* `mem` is that each step's **endpoint** lies in `R`.  The paper's `lem:wd` uses the region
  condition only at the endpoint, so that is all that is assumed — `x^{(0)}` is unconstrained.
-/
structure Tableau (h n : ℕ) [NeZero h] (w : ℤ) where
  /-- The lattice points `x^{(0)}, x^{(1)}, …` of the path, in Model B's `1`-based indexing. -/
  x : ℕ → (ℕ → ℤ)
  /-- The occupation word of the `a`-th step, in Model A's cyclic indexing. -/
  occ : Fin n → (ZMod h → Bool)
  /-- Content `(1ⁿ)`: every step adds exactly one box. -/
  boxCount_eq_one : ∀ a, boxCount (occ a) = 1
  /-- `x^{(a)} = x^{(a-1)} + θ^{(a)}`. -/
  step : ∀ a : Fin n, x (a.1 + 1) = shift (x a.1) (toNatWord (occ a))
  /-- Each step's endpoint lies in HKKO's region `R`. -/
  mem : ∀ a : Fin n, Mem h w (x (a.1 + 1))

namespace Tableau

variable (T : Tableau h n w)

/-- The endpoint hypothesis in the shape `lem:wd` consumes it. -/
theorem mem_shift (a : Fin n) : Mem h w (shift (T.x a.1) (toNatWord (T.occ a))) :=
  (T.step a) ▸ T.mem a

/-- `Ψ_T(t) = ∏_{a=1}^{n} ∏_{i ∈ J(θ^{(a)})} (1 - t^{m_i(x^{(a-1)})})`, equation `(eq:Psi)`,
as an honest *product* of polynomials.  The ascent set is pushed to Model B indices by
`Bridge.natJ` so that `m_i` and `J` are indexed the same way. -/
noncomputable def Psi (R : Type*) [CommRing R] : R[X] :=
  ∏ a : Fin n, ∏ i ∈ natJ (T.occ a), (1 - X ^ (multNat h w (T.x a.1) i))

/-- `ν(T)`, the statistic of `lem:nu`, read off the tableau. -/
def nuT : ℕ := nu T.occ

theorem nuT_eq (hh : 2 ≤ h) : T.nuT = n := nu_eq_of_content_ones hh T.occ T.boxCount_eq_one

/-- The double product rewritten over a single `Σ`-indexed finset, so that gap 1 — which is
stated for one finset — applies to the whole of `Ψ_T` at once rather than factor by factor. -/
theorem Psi_eq_sigma_prod (R : Type*) [CommRing R] :
    T.Psi R = ∏ p ∈ (univ : Finset (Fin n)).sigma (fun a => natJ (T.occ a)),
      (1 - X ^ (multNat h w (T.x p.1.1) p.2)) := by
  rw [Finset.prod_sigma]
  rfl

/-- **Target 2 — the full composite, one declaration.**
`ord_{t=1} Ψ_T = ν(T) = n` for every path of content `(1ⁿ)` in the region, `h ≥ 2`.

Assembles, in order: this file's `lem:nu` (via `card_J_of_boxCount_one`), the bridge
(`Bridge.card_natJ`, `Bridge.natJ_spec`), gap 3 (`Region.one_le_multNat_of_mem_J`, through
`natJ_spec` and `mem_shift`) and gap 1
(`Polynomial.rootMultiplicity_prod_one_sub_X_pow_of_one_le`).  No hypothesis is left
dangling: the multiplicities' positivity comes from the region, and the step words' shape
comes from the content. -/
theorem rootMultiplicity_Psi {R : Type*} [CommRing R] [IsDomain R] [CharZero R] (hh : 2 ≤ h) :
    rootMultiplicity (1 : R) (T.Psi R) = n := by
  rw [T.Psi_eq_sigma_prod R,
    rootMultiplicity_prod_one_sub_X_pow_of_one_le _ _ (fun p hp => ?_)]
  · -- the cardinality of the `Σ`-indexed finset is `ν(T)`, hence `n`
    rw [Finset.card_sigma]
    rw [Finset.sum_congr rfl fun a _ => (card_natJ (T.occ a)).trans
      (card_J_of_boxCount_one hh (T.boxCount_eq_one a))]
    simp
  · -- every multiplicity met is `≥ 1`: gap 3, applied through the bridge's `natJ_spec`
    obtain ⟨hi1, hih, hJ⟩ := natJ_spec (T.occ p.1) (Finset.mem_sigma.mp hp).2
    exact one_le_multNat_of_mem_J (T.mem_shift p.1) hi1 hih hJ

/-- `ord_{t=1} Ψ_T = ν(T)`, the composite in the form the node states it. -/
theorem rootMultiplicity_Psi_eq_nuT {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (hh : 2 ≤ h) : rootMultiplicity (1 : R) (T.Psi R) = T.nuT :=
  (T.rootMultiplicity_Psi hh).trans (T.nuT_eq hh).symm

end Tableau

/-! ### Target 3 — non-vacuity: `Tableau` is inhabited and `Ψ` is not the empty product

A composite over an empty type type-checks and says nothing.  The witness below is a genuine
one-box path at `h = 2`, `w = 2`, `n = 1`: a single box in row `1` of the all-zero state.  Its
`Ψ` is computed outright — it is `1 - X²`, a non-constant polynomial — so `rootMultiplicity`
is being asked a real question. -/

section NonVacuity

/-- The single step: one box at cyclic position `0`. -/
def witOcc : Fin 1 → (ZMod 2 → Bool) := fun _ => fun j => decide (j = 0)

/-- The path: `x^{(0)} = 0`, and `x^{(1)}` is literally the shift, so `step` is `rfl`. -/
def witX : ℕ → (ℕ → ℤ) :=
  fun a => if a = 0 then (fun _ => 0) else shift (fun _ => 0) (toNatWord (witOcc 0))

theorem witOcc_boxCount (a : Fin 1) : boxCount (witOcc a) = 1 := by
  revert a; decide

/-- The witness tableau. -/
def wit : Tableau 2 1 2 where
  x := witX
  occ := witOcc
  boxCount_eq_one := witOcc_boxCount
  step := by intro a; fin_cases a; rfl
  mem := by
    intro a
    fin_cases a
    constructor
    · intro i hi1 hi2
      interval_cases i
      · norm_num [witX, shift, stepVal, toNatWord, witOcc]
    · norm_num [witX, shift, stepVal, toNatWord, witOcc]

/-- `ν(T) = 1 > 0` for the witness: the cyclic ascent set genuinely fires. -/
theorem wit_nuT : wit.nuT = 1 := by
  change ∑ a : Fin 1, (ZMod.J (witOcc a)).card = 1
  decide

/-- The witness's ascent set sits at Model B index `2` — the wrap slot, which Macdonald's
open `ψ` does not have.  This is the arm that reports the cyclic reading is in play. -/
theorem wit_natJ : natJ (wit.occ 0) = {2} := natJ_unit_zero_at_two

/-- **`Ψ` of the witness is `1 - X²`.**  Not `1`, not a unit: the composite is answering a
real question.  The exponent `2` is `m_2(x^{(0)}) = w - (x_1 - x_2) = 2 - 0`, the wrapped
multiplicity, so the witness also exercises the `i = h` branch of `(eq:mvec)`. -/
theorem wit_multNat : multNat 2 2 (wit.x 0) 2 = 2 := by
  norm_num [wit, witX, multNat, mult]
  rfl

theorem wit_Psi : wit.Psi ℚ = 1 - X ^ 2 := by
  rw [Tableau.Psi, Fin.prod_univ_one, wit_natJ, Finset.prod_singleton]
  norm_num [wit_multNat]

/-- And the composite agrees: `ord_{t=1}(1 - X²) = 1 = n`. -/
theorem wit_rootMultiplicity : rootMultiplicity (1 : ℚ) (wit.Psi ℚ) = 1 :=
  wit.rootMultiplicity_Psi (by omega)

end NonVacuity

end TworowD4Kernel.TableauReduction
