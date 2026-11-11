/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ReciprocalPair

/-!
# Q565 `thm:red`: a reciprocal pair is a restriction, not a vanishing

Formalises `thm:red` of `projects/proofs/2026-10-24-Q565-zero-locus-in-M.tex`
(Clio, 24 Oct 2026, L241–L291):

> **Theorem (reduction).** Let `M` be admissible and `θ ∈ ℤ^r` arbitrary.
> (a) If `w_a² = 1` then `Ψ(M) = Ψ(M ∖ {w_a})`.
> (b) If `w_a w_b = 1` with `a ≠ b` then `Ψ(M) = Ψ(M ∖ {w_a, w_b})`.

The paper proof (L251–L291) uses `thm:alt`, then compares the weights `B(T)` term by
term. The terms with no counterpart vanish; the others agree because of a
**cross-factor identity** (L278–L283 for (b), L263–L266 for (a)): for `x ∈ T`,

  `(1 − 1/(w_a x))/(1 − w_a/x) · (1 − 1/(w_b x))/(1 − w_b/x) = 1`   when `w_b = 1/w_a`,
  `(1 − 1/(w_a x))/(1 − w_a/x) = 1`                                when `1/w_a = w_a`.

## Carrier

`M` is a `Finset ι` of **indices**, with weights `w : ι → K` — the paper's own
Convention `conv:psi` ("`M` carries the index order `1 < … < n`"). `M ∖ {w_a, w_b}` is
`(M.erase a).erase b`: one index each, so a repeated *value* is never collapsed. The
Q565-A carrier failure (`Finset` of values) cannot occur in this encoding; L3 below
records what does happen if one uses a `Finset` of values instead.

## Honest scope

* `thm:alt` is **not** formalised. `thm:red` for the head-injection definition
  `eq:Psidef` (`psiHead` below) is proved **conditional on `thm:alt` as an explicit
  hypothesis** (`AltExpansion`), a `Prop`, never an `axiom`.
* The alternant layer (`psiAlt`, with `B := Bfactor`) is proved **unconditionally**.
* Admissibility is **load-bearing** here, unlike in `prop:recip`: Lean's `x / 0 = 0`
  turns the identity `c · c⁻¹ = 1` into `0 = 1` at a degenerate point (L4).

## PRE-REGISTRATION — written before the first `lake build`

(Reformatted from a table to a list after the build, for the 100-column linter; the
wording is unchanged. The L3 and {L1,L3} rows are the brief's predictions, copied in.)

* **L1** drop `a ≠ b` in (b): **REFUTABLE** in general (then `{a,b}` is a singleton,
  `w_a² = 1`, and (b) says `Ψ(M) = Ψ(M∖{w_a})` *with one erase*, which is (a); but erasing
  `b = a` twice is erasing once, so actually the lesioned (b) **is** (a)) — see grade.
* **L2** `w_a w_b = 1` ↦ `w_a = w_b`: **REFUTABLE**; witness with `a ≠ b` is
  non-admissible, so refutable only once admissibility is dropped too; with admissibility
  the hypothesis is **vacuous**.
* **L3** `Finset` of values: **REFUTABLE** with a repeated entry.
* **L4** drop admissibility: **REFUTABLE** at the `B` layer (`x / 0 = 0`).
* **{L1,L3}** joint: **REFUTABLE**.

(The L1 row was revised *before* building, while writing it: `(M.erase a).erase a =
M.erase a`, so the lesioned (b) with `a = b` hypothesises `w_a² = 1` and concludes
exactly (a). Prediction stands as written in the cell: **not** refutable; it collapses
to (a). The brief's prediction "refutable" is therefore registered as *my brief's*, and
I predict it fails.)
-/

namespace TworowD4Kernel.ReciprocalRestriction

open Finset
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing

variable {ι : Type*} {K : Type*} [Field K]

/-! ## 1. The cross-factor identity (primary target; no `thm:alt`) -/

/-- **Cross-factor identity, (b).** `Q565 .tex` L278–L283. If `w_a w_b = 1` and
`x = w_i` is nonzero and distinct from `w_a` and `w_b`, the two cross factors contributed
by the reciprocal pair multiply to exactly `1`. -/
theorem crossFactor_mul_crossFactor_of_recip {w : ι → K} {a b i : ι}
    (hw : w a * w b = 1) (hi0 : w i ≠ 0) (hia : w i ≠ w a) (hib : w i ≠ w b) :
    crossFactor w a i * crossFactor w b i = 1 := by
  have hb : w b = (w a)⁻¹ := eq_inv_of_mul_eq_one_right hw
  -- `N = 1 − 1/(w_a x)` and `D = 1 − w_a/x`; the pair factor of `b` is `D/N`.
  have hN : 1 - (w a * w i)⁻¹ ≠ 0 := by
    intro h
    have h1 : w a * w i = 1 := by
      have := sub_eq_zero.1 h
      exact inv_eq_one.1 this.symm
    exact hib (by rw [hb]; exact eq_inv_of_mul_eq_one_right h1)
  have hD : 1 - w a / w i ≠ 0 := by
    rw [sub_ne_zero, ne_eq, eq_div_iff hi0, one_mul]; exact fun h => hia h
  have eN : 1 - ((w a)⁻¹ * w i)⁻¹ = 1 - w a / w i := by
    rw [mul_inv, inv_inv, div_eq_mul_inv]
  have eD : 1 - (w a)⁻¹ / w i = 1 - (w a * w i)⁻¹ := by
    rw [mul_inv, div_eq_mul_inv]
  rw [crossFactor, crossFactor, hb, eN, eD, div_mul_div_comm, mul_comm (1 - w a / w i),
    div_self (mul_ne_zero hN hD)]

/-- **Cross-factor identity, (a).** `Q565 .tex` L263–L266. If `w_a² = 1` and `x = w_i`
is nonzero and distinct from `w_a`, the cross factor of `t = a` is exactly `1`. -/
theorem crossFactor_eq_one_of_self_recip {w : ι → K} {a i : ι}
    (hw : w a * w a = 1) (hi0 : w i ≠ 0) (hia : w i ≠ w a) :
    crossFactor w a i = 1 := by
  have hinv : (w a)⁻¹ = w a := (eq_inv_of_mul_eq_one_right hw).symm
  have hden : 1 - w a / w i ≠ 0 := by
    rw [sub_ne_zero, ne_eq, eq_div_iff hi0, one_mul]; exact fun h => hia h
  rw [crossFactor, mul_inv, hinv, ← div_eq_mul_inv, div_self hden]

/-! ## 2. The `B(T)` layer: vanishing of the unmatched terms, equality of the matched ones -/

variable [DecidableEq ι]

/-- (b), unmatched terms: `T ⊆ M` meeting the reciprocal pair has `B(T) = 0`
(`.tex` L268–L272: pair factor if both lie in `T`, cross factor if exactly one does). -/
theorem Bfactor_eq_zero_of_meets_pair {w : ι → K} {M T : Finset ι} {a b : ι}
    (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1)
    (hmeet : a ∈ T ∨ b ∈ T) : Bfactor w M T = 0 := by
  have hw' : w b * w a = 1 := by rw [mul_comm]; exact hw
  have key : (∏ p ∈ T.powersetCard 2, pairFactor w p) = 0 ∨
      (∏ s ∈ M \ T, ∏ j ∈ T, crossFactor w s j) = 0 := by
    rcases hmeet with haT | hbT
    · by_cases hbT : b ∈ T
      · exact Or.inl (pairProd_eq_zero_of_recip hab haT hbT hw)
      · exact Or.inr (crossProd_eq_zero_of_recip (Finset.mem_sdiff.2 ⟨hb, hbT⟩) haT hw')
    · by_cases haT : a ∈ T
      · exact Or.inl (pairProd_eq_zero_of_recip hab haT hbT hw)
      · exact Or.inr (crossProd_eq_zero_of_recip (Finset.mem_sdiff.2 ⟨ha, haT⟩) hbT hw)
  rcases key with h | h <;> rw [Bfactor, h] <;> ring

/-- (b), matched terms: for `T ⊆ M ∖ {a, b}`, `B_M(T) = B_{M∖{a,b}}(T)`
(`.tex` L273–L285). The only consumer of admissibility: `w_i ≠ 0, w_a, w_b` on `T`. -/
theorem Bfactor_erase_pair {w : ι → K} {M T : Finset ι} {a b : ι}
    (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1)
    (hTM : T ⊆ (M.erase a).erase b)
    (hadm : ∀ i ∈ T, w i ≠ 0 ∧ w i ≠ w a ∧ w i ≠ w b) :
    Bfactor w M T = Bfactor w ((M.erase a).erase b) T := by
  set M' := (M.erase a).erase b with hM'
  have haT : a ∉ T := fun h => by
    have := hTM h; simp [hM'] at this
  have hbT : b ∉ T := fun h => by
    have := hTM h; simp [hM'] at this
  have hMeq : M = insert a (insert b M') := by
    rw [hM', Finset.insert_erase (Finset.mem_erase.2 ⟨hab.symm, hb⟩), Finset.insert_erase ha]
  have haNot : a ∉ insert b (M' \ T) := by
    simp [hM', hab]
  have hbNot : b ∉ M' \ T := by simp [hM']
  have hsd : M \ T = insert a (insert b (M' \ T)) := by
    rw [hMeq, Finset.insert_sdiff_of_notMem _ haT, Finset.insert_sdiff_of_notMem _ hbT]
  have hone : (∏ j ∈ T, crossFactor w a j) * (∏ j ∈ T, crossFactor w b j) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun i hi =>
      crossFactor_mul_crossFactor_of_recip hw (hadm i hi).1 (hadm i hi).2.1 (hadm i hi).2.2
  rw [Bfactor, Bfactor, hsd, Finset.prod_insert haNot, Finset.prod_insert hbNot,
    mul_assoc, ← mul_assoc (∏ i ∈ T, crossFactor w a i), hone, one_mul, mul_assoc]

/-- (a), unmatched terms: `a ∈ T` with `w_a² = 1` gives `B(T) = 0` (`.tex` L259–L260). -/
theorem Bfactor_eq_zero_of_mem_self_recip {w : ι → K} {M T : Finset ι} {a : ι}
    (haT : a ∈ T) (hw : w a * w a = 1) : Bfactor w M T = 0 := by
  rw [Bfactor, diagProd_eq_zero_of_self_recip haT hw, zero_mul, zero_mul]

/-- (a), matched terms: for `T ⊆ M ∖ {a}`, `B_M(T) = B_{M∖{a}}(T)` (`.tex` L260–L268). -/
theorem Bfactor_erase_self {w : ι → K} {M T : Finset ι} {a : ι}
    (ha : a ∈ M) (hw : w a * w a = 1) (hTM : T ⊆ M.erase a)
    (hadm : ∀ i ∈ T, w i ≠ 0 ∧ w i ≠ w a) :
    Bfactor w M T = Bfactor w (M.erase a) T := by
  have haT : a ∉ T := fun h => by have := hTM h; simp at this
  have haNot : a ∉ M.erase a \ T := by simp
  have hsd : M \ T = insert a (M.erase a \ T) := by
    conv_lhs => rw [← Finset.insert_erase ha]
    rw [Finset.insert_sdiff_of_notMem _ haT]
  have hone : (∏ j ∈ T, crossFactor w a j) = 1 :=
    Finset.prod_eq_one fun i hi =>
      crossFactor_eq_one_of_self_recip hw (hadm i hi).1 (hadm i hi).2
  rw [Bfactor, Bfactor, hsd, Finset.prod_insert haNot, hone, one_mul]

/-! ## 3. The alternant layer: `thm:red` for `psiAlt`, unconditionally

`psiAlt` is `thm:alt`'s right-hand side. Its alternant factor depends on `T` only —
the paper's "the alternant factor of a term depends only on `T`, not on `M`" (L253) is
here a fact about the *type* of `psiAlt`: `x`, `V`, `ord` take no `M`. -/

/-- Paper admissibility (`conv:psi`): weights nonzero and pairwise distinct on `M`. -/
def Admissible (w : ι → K) (M : Finset ι) : Prop :=
  (∀ t ∈ M, w t ≠ 0) ∧ ∀ s ∈ M, ∀ t ∈ M, s ≠ t → w s ≠ w t

/-- **`thm:red` (b), alternant layer.** -/
theorem psiAlt_erase_pair (M : Finset ι) (r : ℕ) (w x : ι → K) (V : Finset ι → K)
    (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) {a b : ι} (hadm : Admissible w M)
    (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    psiAlt M r x (Bfactor w M) V ord θ =
      psiAlt ((M.erase a).erase b) r x (Bfactor w ((M.erase a).erase b)) V ord θ := by
  have hsub : (M.erase a).erase b ⊆ M :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  unfold psiAlt
  symm
  calc _ = ∑ T ∈ ((M.erase a).erase b).powersetCard r,
        Bfactor w M T * ((Matrix.of fun i j => x (ord T i) ^ rhoShift θ j).det / V T) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        have hTM' := (Finset.mem_powersetCard.1 hT).1
        have hadmT : ∀ i ∈ T, w i ≠ 0 ∧ w i ≠ w a ∧ w i ≠ w b := by
          intro i hi
          have hiM : i ∈ M := hsub (hTM' hi)
          have hia : i ≠ a := fun h => by have := hTM' hi; simp [h] at this
          have hib : i ≠ b := fun h => by have := hTM' hi; simp [h] at this
          exact ⟨hadm.1 i hiM, hadm.2 i hiM a ha hia, hadm.2 i hiM b hb hib⟩
        rw [Bfactor_erase_pair hab ha hb hw hTM' hadmT]
    _ = _ := by
        refine Finset.sum_subset (Finset.powersetCard_mono hsub) fun T hT hT' => ?_
        obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hT
        have hmeet : a ∈ T ∨ b ∈ T := by
          by_contra hcon
          push Not at hcon
          refine hT' (Finset.mem_powersetCard.2 ⟨fun i hi => ?_, hTc⟩)
          refine Finset.mem_erase.2 ⟨fun h => hcon.2 (h ▸ hi),
            Finset.mem_erase.2 ⟨fun h => hcon.1 (h ▸ hi), hTM hi⟩⟩
        rw [Bfactor_eq_zero_of_meets_pair hab ha hb hw hmeet, zero_mul]

/-- **`thm:red` (a), alternant layer.** -/
theorem psiAlt_erase_self (M : Finset ι) (r : ℕ) (w x : ι → K) (V : Finset ι → K)
    (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) {a : ι} (hadm : Admissible w M)
    (ha : a ∈ M) (hw : w a * w a = 1) :
    psiAlt M r x (Bfactor w M) V ord θ =
      psiAlt (M.erase a) r x (Bfactor w (M.erase a)) V ord θ := by
  have hsub : M.erase a ⊆ M := Finset.erase_subset _ _
  unfold psiAlt
  symm
  calc _ = ∑ T ∈ (M.erase a).powersetCard r,
        Bfactor w M T * ((Matrix.of fun i j => x (ord T i) ^ rhoShift θ j).det / V T) := by
        refine Finset.sum_congr rfl fun T hT => ?_
        have hTM' := (Finset.mem_powersetCard.1 hT).1
        have hadmT : ∀ i ∈ T, w i ≠ 0 ∧ w i ≠ w a := by
          intro i hi
          have hiM : i ∈ M := hsub (hTM' hi)
          have hia : i ≠ a := fun h => by have := hTM' hi; simp [h] at this
          exact ⟨hadm.1 i hiM, hadm.2 i hiM a ha hia⟩
        rw [Bfactor_erase_self ha hw hTM' hadmT]
    _ = _ := by
        refine Finset.sum_subset (Finset.powersetCard_mono hsub) fun T hT hT' => ?_
        obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hT
        have haT : a ∈ T := by
          by_contra hcon
          exact hT' (Finset.mem_powersetCard.2
            ⟨fun i hi => Finset.mem_erase.2 ⟨fun h => hcon (h ▸ hi), hTM hi⟩, hTc⟩)
        rw [Bfactor_eq_zero_of_mem_self_recip haT hw, zero_mul]

/-! ## 4. `thm:red` for the definition `eq:Psidef`, conditional on `thm:alt`

`psiHead` is `eq:Psidef` (`.tex` L112–L118) literally, over `headInjections`
(`BoundaryEmptyIndex`). `thm:alt` enters as the **hypothesis** `AltExpansion`, a `Prop`
binder — not an `axiom` — so `#print axioms` cannot hide it: it is in the statement. -/

/-- **`eq:Psidef`.** The head-injection sum defining `Ψ^C_{(1^r),θ}(M)`. -/
noncomputable def psiHead (w : ι → K) (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) : K :=
  ∑ h ∈ headInjections M r,
    (∏ j, (1 - (w (h j))⁻¹ ^ 2) * w (h j) ^ θ j) *
    (∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
      (1 - (w (h j) * w (h k))⁻¹) / (1 - w (h j) / w (h k))) *
    ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor w t (h j)

/-- **`thm:alt` at `N`, as a proposition.** (`.tex` L134–L146, citing
`clio-Q553-alternant-expansion`, 2026-10-22.) The alternant data `x, V, ord` are the
paper's `x_i = w_i`, Vandermonde, increasing index order; they are left as parameters,
so the hypothesis is stated for whatever data the caller claims `thm:alt` for. -/
def AltExpansion (w x : ι → K) (V : Finset ι → K) {r : ℕ} (ord : Finset ι → Fin r → ι)
    (θ : Fin r → ℤ) (N : Finset ι) : Prop :=
  psiHead w N r θ = psiAlt N r x (Bfactor w N) V ord θ

/-- **`thm:red` (b)**, `.tex` L241–L249, for the defining sum `eq:Psidef`, **conditional on
`thm:alt` at `M` and at `M ∖ {a, b}`** (and nowhere else). -/
theorem thm_red_b (M : Finset ι) (r : ℕ) (w x : ι → K) (V : Finset ι → K)
    (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) {a b : ι}
    (hAltM : AltExpansion w x V ord θ M)
    (hAltM' : AltExpansion w x V ord θ ((M.erase a).erase b))
    (hadm : Admissible w M) (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    psiHead w M r θ = psiHead w ((M.erase a).erase b) r θ := by
  rw [hAltM, hAltM', psiAlt_erase_pair M r w x V ord θ hadm hab ha hb hw]

/-- **`thm:red` (a)**, `.tex` L241–L249, conditional on `thm:alt` at `M` and `M ∖ {a}`. -/
theorem thm_red_a (M : Finset ι) (r : ℕ) (w x : ι → K) (V : Finset ι → K)
    (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) {a : ι}
    (hAltM : AltExpansion w x V ord θ M)
    (hAltM' : AltExpansion w x V ord θ (M.erase a))
    (hadm : Admissible w M) (ha : a ∈ M) (hw : w a * w a = 1) :
    psiHead w M r θ = psiHead w (M.erase a) r θ := by
  rw [hAltM, hAltM', psiAlt_erase_self M r w x V ord θ hadm ha hw]

/-- **Control: the `thm:alt` hypothesis is satisfiable.** At `r = 0`, with `V ≡ 1`, it
holds for every `M` and every `w` — so `thm_red_a`/`thm_red_b` are not vacuous by an
unsatisfiable binder at least at `r = 0`. (This is *not* `thm:alt`; it is its emptiest
instance, both sides `= 1`.) -/
theorem altExpansion_rank_zero (w x : ι → K) (ord : Finset ι → Fin 0 → ι)
    (θ : Fin 0 → ℤ) (N : Finset ι) : AltExpansion w x (fun _ => 1) ord θ N := by
  have hH : headInjections N 0 = {Fin.elim0} := by
    ext g
    simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro _; funext j; exact j.elim0
    · rintro rfl; exact ⟨fun j => j.elim0, fun j => j.elim0⟩
  have hP : (∅ : Finset ι).powersetCard 2 = ∅ := Finset.powersetCard_eq_empty.2 (by simp)
  simp [AltExpansion, psiHead, psiAlt, hH, Bfactor, hP]

/-! ## 5. Lesions -/

/-- **L1 — VERDICT: REMOVABLE.** With `a ≠ b` dropped, (b) is still true: at `a = b` the
hypothesis is `w_a² = 1` and `(M.erase a).erase a = M.erase a`, so the lesioned (b) *is*
(a). Lean proves the lesioned statement rather than refuting it. -/
theorem L1_psiAlt_erase_pair_without_ne (M : Finset ι) (r : ℕ) (w x : ι → K)
    (V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) {a b : ι}
    (hadm : Admissible w M) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    psiAlt M r x (Bfactor w M) V ord θ =
      psiAlt ((M.erase a).erase b) r x (Bfactor w ((M.erase a).erase b)) V ord θ := by
  by_cases hab : a = b
  · subst hab
    have hidem : (M.erase a).erase a = M.erase a :=
      Finset.erase_eq_of_notMem (Finset.notMem_erase a M)
    rw [hidem]
    exact psiAlt_erase_self M r w x V ord θ hadm ha hw
  · exact psiAlt_erase_pair M r w x V ord θ hadm hab ha hb hw

omit [DecidableEq ι] in
/-- **L2 — VERDICT, half one: VACUOUS under admissibility.** `w_a = w_b` with `a ≠ b`
contradicts pairwise distinctness, so the lesioned (b) has no instances at all. -/
theorem L2_vacuous_under_admissibility {w : ι → K} {M : Finset ι} {a b : ι}
    (hadm : Admissible w M) (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a = w b) :
    False :=
  hadm.2 a ha b hb hab hw

/-- L2/L4 witness weights: `w_0 = w_1 = 2`, `w_2 = 3`. -/
def wL2 : ℕ → ℚ
  | 0 => 2
  | 1 => 2
  | _ => 3

/-- **L2 — VERDICT, half two: REFUTABLE without admissibility.** At the `B` layer, with
`w_a = w_b` (`a ≠ b`) the matched-term equality fails: `T = {2}` gets cross factors
`5/2 · 5/2 ≠ 1`. -/
theorem L2_refutable :
    ¬ (∀ (M T : Finset ℕ) (w : ℕ → ℚ) (a b : ℕ), a ≠ b → a ∈ M → b ∈ M → w a = w b →
        T ⊆ (M.erase a).erase b → Bfactor w M T = Bfactor w ((M.erase a).erase b) T) := by
  intro h
  have hz := h {0, 1, 2} {2} wL2 0 1 (by decide) (by decide) (by decide) rfl (by decide)
  rw [show ((({0, 1, 2} : Finset ℕ).erase 0).erase 1) = {2} from by decide] at hz
  rw [Bfactor, Bfactor, show ({0, 1, 2} : Finset ℕ) \ {2} = {0, 1} from by decide,
    show ({2} : Finset ℕ) \ {2} = ∅ from by decide,
    show ({2} : Finset ℕ).powersetCard 2 = ∅ from by decide] at hz
  norm_num [diagFactor, crossFactor, wL2, Finset.prod_pair] at hz

/-- L4 witness weights: the reciprocal pair `w_0 w_1 = 2 · ½ = 1`, and `w_2 = 2 = w_0`, a
**repeated value** — exactly the "repeated entry" the brief's L3 asked for, but it is
admissibility, not the carrier, that excludes it. -/
def wL4 : ℕ → ℚ
  | 0 => 2
  | 1 => 1/2
  | _ => 2

/-- **L4 — VERDICT: admissibility IRREMOVABLE at the `B` layer.** With `w_2 = w_0` the
cross factor `crossFactor w 0 2` has denominator `1 − 1 = 0`, Lean's `x/0 = 0` makes the
pair product `0` instead of `1`, and `B_M({2}) = 0 ≠ 3/4 = B_{{2}}({2})`. (At this point
the paper's `B` is undefined; the refutation is of the total extension, as expected.) -/
theorem L4_admissibility_irremovable :
    ¬ (∀ (M T : Finset ℕ) (w : ℕ → ℚ) (a b : ℕ), a ≠ b → a ∈ M → b ∈ M → w a * w b = 1 →
        T ⊆ (M.erase a).erase b → Bfactor w M T = Bfactor w ((M.erase a).erase b) T) := by
  intro h
  have hz := h {0, 1, 2} {2} wL4 0 1 (by decide) (by decide) (by decide)
    (by norm_num [wL4]) (by decide)
  rw [show ((({0, 1, 2} : Finset ℕ).erase 0).erase 1) = {2} from by decide] at hz
  rw [Bfactor, Bfactor, show ({0, 1, 2} : Finset ℕ) \ {2} = {0, 1} from by decide,
    show ({2} : Finset ℕ) \ {2} = ∅ from by decide,
    show ({2} : Finset ℕ).powersetCard 2 = ∅ from by decide] at hz
  norm_num [diagFactor, crossFactor, wL4, Finset.prod_pair] at hz

/-- **L3 — VERDICT: ABSENT under admissibility.** The `Finset`-of-*values* carrier is the
index carrier at `ι := K`, `w := id`; an admissible `Finset K` cannot hold a repeated
entry, and `MV ∖ {v, u}` is `(MV.erase v).erase u`. So the value-carrier (b) is a
corollary, not a refutation. -/
theorem L3_value_carrier (MV : Finset K) (r : ℕ) (x : K → K) (V : Finset K → K)
    (ord : Finset K → Fin r → K) (θ : Fin r → ℤ) {v u : K} [DecidableEq K]
    (hnz : ∀ t ∈ MV, t ≠ 0) (hvu : v ≠ u) (hv : v ∈ MV) (hu : u ∈ MV) (hw : v * u = 1) :
    psiAlt MV r x (Bfactor id MV) V ord θ =
      psiAlt (MV \ {v, u}) r x (Bfactor id (MV \ {v, u})) V ord θ := by
  have hset : MV \ {v, u} = (MV.erase v).erase u := by
    ext z; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
  rw [hset]
  exact psiAlt_erase_pair MV r id x V ord θ ⟨hnz, fun s _ t _ hst => hst⟩ hvu hv hu hw

/-- **{L1, L3} — PAIR VERDICT: ABSENT.** Value carrier *and* `v = u` allowed: `{v, v} = {v}`
as a `Finset`, which removes `v` once — exactly (a). The collapse that broke Q565-A
(`{a,a}` losing its square in a *product*) is harmless in a *removal*, where one copy is
what must go. -/
theorem L1_L3_value_carrier_without_ne (MV : Finset K) (r : ℕ) (x : K → K)
    (V : Finset K → K) (ord : Finset K → Fin r → K) (θ : Fin r → ℤ) {v u : K}
    [DecidableEq K] (hnz : ∀ t ∈ MV, t ≠ 0) (hv : v ∈ MV) (hu : u ∈ MV) (hw : v * u = 1) :
    psiAlt MV r x (Bfactor id MV) V ord θ =
      psiAlt (MV \ {v, u}) r x (Bfactor id (MV \ {v, u})) V ord θ := by
  have hset : MV \ {v, u} = (MV.erase v).erase u := by
    ext z; simp [Finset.mem_sdiff, Finset.mem_erase]; tauto
  rw [hset]
  exact L1_psiAlt_erase_pair_without_ne MV r id x V ord θ ⟨hnz, fun s _ t _ hst => hst⟩
    hv hu hw

/-! ## 6. Positive control: the identity is reached non-trivially

`w_0 = 2, w_1 = ½, w_2 = 3`, `T = {2}`. Neither cross factor is `1` (`5/2` and `2/5`), their
product is, and `B(T) = 8/9 ≠ 0` on both sides — so `Bfactor_erase_pair` is an equality
between nonzero numbers reached through a genuine cancellation. -/

theorem control_cross_factors_nontrivial :
    crossFactor wL1 0 2 = 5/2 ∧ crossFactor wL1 1 2 = 2/5 ∧
      crossFactor wL1 0 2 * crossFactor wL1 1 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [crossFactor, wL1]

theorem control_matched_term_nonzero :
    Bfactor wL1 {0, 1, 2} {2} = 8/9 ∧ Bfactor wL1 {2} {2} = 8/9 := by
  refine ⟨Bfactor_wL1, ?_⟩
  rw [Bfactor, show ({2} : Finset ℕ) \ {2} = ∅ from by decide,
    show ({2} : Finset ℕ).powersetCard 2 = ∅ from by decide]
  norm_num [diagFactor, wL1]

/-! ## GRADES — written 2026-11-11, after the build

`lake build` rc = 0 measured directly (no pipe); module built (`⚠ [3481/3482]`, the only
warnings are two long lines, since fixed). `sorry`: 0 in the file. `#print axioms` on all
15 headline declarations: `[propext, Classical.choice, Quot.sound]`; planted
`theorem bad_control : 1 = 2 := by sorry` in the same invocation printed `[sorryAx]`.
`unusedVariables` silent on every declaration, with no `_`-prefixed binder anywhere: every
hypothesis of `thm_red_a`/`thm_red_b` is consumed.

* **Primary target** (cross-factor identity, no `thm:alt`): **sorry-free**,
  `crossFactor_mul_crossFactor_of_recip` and `crossFactor_eq_one_of_self_recip`. It needs
  `w_i ≠ 0`, `w_i ≠ w_a`, `w_i ≠ w_b` and **nothing else**; `w_a ≠ 0` is derived.
* **Alternant layer** `psiAlt_erase_pair` / `psiAlt_erase_self`: **unconditional**.
* **`thm:red` on `eq:Psidef`**: `thm_red_a` / `thm_red_b`, **conditional on
  `AltExpansion` at exactly two sets** (`M` and the reduced set). The control
  `altExpansion_rank_zero` shows the binder is satisfiable at `r = 0` only; it is not
  evidence for `thm:alt` at `r ≥ 1`.

| # | PREDICTION | VERDICT |
|---|-----------|---------|
| L1 | brief: refutable; mine: = (a) | **REMOVABLE**; `L1_psiAlt_erase_pair_without_ne` |
| L2 | vacuous w/ adm., else refutable | **CONFIRMED** both halves (`5/2·5/2 ≠ 1`) |
| L3 | refutable with repeated entry | **REFUTED — ABSENT.** `L3_value_carrier` is a corollary. |
| L4 | refutable at `B` layer | **CONFIRMED.** `L4_admissibility_irremovable`. |
| {L1,L3} | jointly refutable | **REFUTED — ABSENT.** `L1_L3_value_carrier_without_ne`. |

### Why L3 and {L1,L3} did not fire

The brief transported Q565-A's carrier lesson ("true over `Multiset`, false over
`Finset`") from a **product** to a **removal**. In `prop:recip` the collapse
`{a,a} = {a}` *lost a square* inside `∏ w`. In `thm:red` the set `{a,b}` is only ever
*removed*, and at `a = b` one copy is exactly what must go. And the only "repeated entry"
a value carrier could forget is one admissibility already forbids. The repeated entry is
real — it is `wL4`'s `w_2 = w_0` — but it is caught by **L4**, not L3: the obstruction
lives in admissibility, not in the carrier.

### Scope

Nothing in `.tex` `thm:red` needed correcting. The paper's "every other factor is
unchanged" (L267, L284) is `Finset.prod_insert` twice plus the observation that the
factors of `B` indexed by `T` do not mention `M` — true by the *type* of `Bfactor`.
-/

end TworowD4Kernel.ReciprocalRestriction
