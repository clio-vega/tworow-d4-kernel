/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.LemOrder
import TworowD4Kernel.Reflection
import Mathlib.Algebra.Field.ZMod

/-!
# Q559 `thm:main`: the converse of the ρ-shift vanishing law

Formalises `thm:main` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
L360–L393 (Clio, 2026-10-23):

> Let `M` be a set of `n` indeterminates, `r ≥ 0` with `n ≥ r`, and `θ ∈ ℤ^r` with pairwise
> distinct ρ-shifts `m_j = θ_j + j − 1`. Then `Ψ^C_{(1^r),θ}(M) ≠ 0` in `ℚ(w_1,…,w_n)`.

## Encoding of "`≠ 0` in `ℚ(w_1,…,w_n)`" (the same as in `LemOrder`)

Over an infinite field `K`: **some admissible point** `w` (nonzero, pairwise distinct on `M`)
has `psiHead w M r θ ≠ 0`. At an admissible point every displayed denominator of `eq:Psidef`
is nonzero, so `psiHead w` *is* the value of the rational function there. A rational function
that is nonzero at one point where it is defined is a nonzero element of `ℚ(w)`. This is the
**global** form that the 2026-11-13 notes said Case B needs.

## Proof structure (the paper's, step for step)

* `r = 0`: `psiHead_rank_zero` (`Ψ = 1`) and `exists_admissible`.
* `r = k+1`, `n ∈ M` any element (`.tex`: "the largest index"; `SnocCompat` encodes the index order
  of `T' ⊔ {n}` and needs nothing else of `n`).
  - **Case A** (`∃ j, m_j ≥ 0`): `caseA_global`. This takes the IH at `M' = M ∖ {n}` and `θ̂`
    (`thetaHat_injective`), extends the witness to `M` (`exists_admissible_extend`,
    `psiHead_congr`), glues an ordering (`glueOrd`), and calls `lem_order`.
  - **Case B** (`∀ j, m_j ≤ −1`): Case A at `θ∨` (`m∨ = −m`, `rhoShiftPaper_thetaVee`), then
    `lem_reflect` at the witness `w`, which gives `Ψ_θ(w⁻¹) = (−1)^r e^{2r} Ψ_{θ∨}(w) ≠ 0`.
    The paper's "ι is injective" step becomes: the point `w⁻¹` is admissible.
-/

namespace TworowD4Kernel.ThmMain

open Finset
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction
open TworowD4Kernel.AlternantExpansion
open TworowD4Kernel.BlockB
open TworowD4Kernel.BlockA
open TworowD4Kernel.LemOrder
open TworowD4Kernel.Reflection

variable {ι : Type*} {K : Type*} [DecidableEq ι] [Field K]

/-! ## Base case: `Ψ^C_{(1^0),()}(M) = 1` (`.tex` conv:psi, last sentence) -/

theorem psiHead_rank_zero (w : ι → K) (M : Finset ι) (θ : Fin 0 → ℤ) : psiHead w M 0 θ = 1 := by
  have hH : headInjections M 0 = {Fin.elim0} := by
    ext g
    simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_singleton]
    constructor
    · intro _; funext j; exact j.elim0
    · rintro rfl; exact ⟨fun j => j.elim0, fun j => j.elim0⟩
  simp [psiHead, hH]

/-! ## Admissible points exist, and extend, over an infinite field -/

omit [DecidableEq ι] in
theorem exists_fresh [Infinite K] (w : ι → K) (s : Finset ι) :
    ∃ v : K, v ≠ 0 ∧ ∀ i ∈ s, v ≠ w i := by
  classical
  obtain ⟨v, hv⟩ := Infinite.exists_notMem_finset (insert (0 : K) (s.image w))
  simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and] at hv
  exact ⟨v, hv.1, fun i hi h => hv.2 i hi h.symm⟩

theorem admissible_update_insert {w : ι → K} {s : Finset ι} {a : ι} {v : K}
    (hadm : Admissible w s) (ha : a ∉ s) (hv0 : v ≠ 0) (hv : ∀ i ∈ s, v ≠ w i) :
    Admissible (Function.update w a v) (insert a s) := by
  have hag : ∀ i ∈ s, Function.update w a v i = w i := fun i hi =>
    Function.update_of_ne (by rintro rfl; exact ha hi) _ _
  refine ⟨fun t ht => ?_, fun s' hs t ht hst => ?_⟩
  · rcases Finset.mem_insert.1 ht with h | ht
    · subst h; simpa using hv0
    · rw [hag t ht]; exact hadm.1 t ht
  · rcases Finset.mem_insert.1 hs with h1 | hs1 <;> rcases Finset.mem_insert.1 ht with h2 | ht1
    · exact absurd (h1.trans h2.symm) hst
    · subst h1; rw [hag t ht1]; simpa using hv t ht1
    · subst h2; rw [hag s' hs1]; simpa using (hv s' hs1).symm
    · rw [hag s' hs1, hag t ht1]; exact hadm.2 s' hs1 t ht1 hst

omit [DecidableEq ι] in
theorem exists_admissible [Infinite K] (M : Finset ι) : ∃ w : ι → K, Admissible w M := by
  classical
  induction M using Finset.induction_on with
  | empty => exact ⟨fun _ => 1, by simp [Admissible]⟩
  | insert a s ha ih =>
    obtain ⟨w, hw⟩ := ih
    obtain ⟨v, hv0, hv⟩ := exists_fresh w s
    exact ⟨_, admissible_update_insert hw ha hv0 hv⟩

/-! ## `Ψ(M)` sees only `w` on `M` -/

theorem psiHead_congr {w w₂ : ι → K} {M : Finset ι} {r : ℕ} (θ : Fin r → ℤ)
    (h : ∀ i ∈ M, w i = w₂ i) : psiHead w M r θ = psiHead w₂ M r θ := by
  unfold psiHead
  refine Finset.sum_congr rfl fun g hg => ?_
  simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hg
  have hj : ∀ j, w (g j) = w₂ (g j) := fun j => h _ (hg.1 j)
  simp only [hj]
  congr 1
  refine Finset.prod_congr rfl fun t ht => Finset.prod_congr rfl fun j _ => ?_
  simp only [crossFactor, h t (Finset.mem_sdiff.1 ht).1, hj]

/-! ## The glued ordering: `snocOrd` on `T ∋ n`, anything `OrdOK` on `T ∌ n` -/

/-- `ord T = (ord' (T ∖ {n}), n)` if `n ∈ T`, else `ord₀ T`. -/
def glueOrd (n : ι) {k : ℕ} (ord' : Finset ι → Fin k → ι) (ord₀ : Finset ι → Fin (k + 1) → ι) :
    Finset ι → Fin (k + 1) → ι :=
  fun T => if n ∈ T then snocOrd n ord' T else ord₀ T

theorem glueOrd_ordOK (M : Finset ι) (n : ι) {k : ℕ} (ord' : Finset ι → Fin k → ι)
    (ord₀ : Finset ι → Fin (k + 1) → ι) (hord' : OrdOK (M.erase n) k ord')
    (hord₀ : OrdOK M (k + 1) ord₀) : OrdOK M (k + 1) (glueOrd n ord' ord₀) := by
  intro T hT
  by_cases hn : n ∈ T
  · simp only [glueOrd, if_pos hn]
    exact snocOrd_ordOK M n ord' hord' T (Finset.mem_filter.2 ⟨hT, hn⟩)
  · simp only [glueOrd, if_neg hn]
    exact hord₀ T hT

theorem glueOrd_compat (M : Finset ι) (n : ι) {k : ℕ} (ord' : Finset ι → Fin k → ι)
    (ord₀ : Finset ι → Fin (k + 1) → ι) : SnocCompat M n k (glueOrd n ord' ord₀) ord' := by
  intro T' hT'
  have h := snocOrd_compat M n ord' T' hT'
  simp only [glueOrd, if_pos (Finset.mem_insert_self n T')]
  exact h

/-! ## `θ̂` inherits distinct shifts (`.tex` L372: "`m̂` is a subfamily of `m`") -/

theorem thetaHat_injective {k : ℕ} {θ : Fin (k + 1) → ℤ} (js : Fin (k + 1))
    (hinj : Function.Injective (rhoShiftPaper θ)) :
    Function.Injective (rhoShiftPaper (thetaHat θ js)) := by
  intro a b hab
  simp only [rhoShiftPaper_thetaHat] at hab
  exact Fin.succAbove_right_injective (hinj hab)

/-- The statement of `thm:main` at rank `r`, in the global encoding. -/
def MainAt (K : Type*) [Field K] (ι : Type*) [DecidableEq ι] (r : ℕ) : Prop :=
  ∀ (M : Finset ι) (θ : Fin r → ℤ), r ≤ M.card → Function.Injective (rhoShiftPaper θ) →
    ∃ w : ι → K, Admissible w M ∧ psiHead w M r θ ≠ 0

/-! ## Case A, global form -/

/-- **Case A** (`.tex` L380–L381) in the global form: IH at rank `k` ⇒ every `θ` of rank `k+1`
with distinct shifts and **some** `m_j ≥ 0` (hence `max m ≥ 0`) has a nonvanishing point. -/
theorem caseA_global [Infinite K] {k : ℕ} (IH : MainAt K ι k) (M : Finset ι)
    (θ : Fin (k + 1) → ℤ) (hcard : k + 1 ≤ M.card) (hinj : Function.Injective (rhoShiftPaper θ))
    (hpos : ∃ j, 0 ≤ rhoShiftPaper θ j) :
    ∃ w : ι → K, Admissible w M ∧ psiHead w M (k + 1) θ ≠ 0 := by
  obtain ⟨n, hn⟩ : M.Nonempty := Finset.card_pos.1 (by omega)
  haveI : Nonempty ι := ⟨n⟩
  -- argmax
  obtain ⟨js, -, harg⟩ := Finset.exists_max_image Finset.univ (rhoShiftPaper θ) Finset.univ_nonempty
  have harg' : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js := fun j => harg j (Finset.mem_univ _)
  have hjs : 0 ≤ rhoShiftPaper θ js := by
    obtain ⟨j, hj⟩ := hpos; exact hj.trans (harg' j)
  -- orderings
  obtain ⟨ord', hord'⟩ := exists_ordOK (M.erase n) k
  obtain ⟨ord₀, hord₀⟩ := exists_ordOK M (k + 1)
  -- IH at M' = M ∖ {n}, θ̂
  have hcard' : k ≤ (M.erase n).card := by rw [Finset.card_erase_of_mem hn]; omega
  obtain ⟨w', hadm', hΨ'⟩ := IH (M.erase n) (thetaHat θ js) hcard' (thetaHat_injective js hinj)
  -- extend the witness to `M`
  obtain ⟨v, hv0, hv⟩ := exists_fresh w' (M.erase n)
  have hadm : Admissible (Function.update w' n v) M := by
    have := admissible_update_insert hadm' (Finset.notMem_erase n M) hv0 hv
    rwa [Finset.insert_erase hn] at this
  have hagree : ∀ i ∈ M.erase n, w' i = Function.update w' n v i := fun i hi =>
    (Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _).symm
  rw [psiHead_congr _ hagree] at hΨ'
  obtain ⟨u, hadmu, hΨu⟩ := lem_order (Function.update w' n v) M k θ (glueOrd n ord' ord₀) ord' js
    hadm hn (glueOrd_ordOK M n ord' ord₀ hord' hord₀) hord' (glueOrd_compat M n ord' ord₀) hinj
    harg' hjs hΨ'
  exact ⟨_, hadmu, hΨu⟩

/-! ## Case B: the reflection -/

omit [DecidableEq ι] in
theorem admissible_inv {w : ι → K} {M : Finset ι} (h : Admissible w M) :
    Admissible (fun t => (w t)⁻¹) M :=
  ⟨fun t ht => inv_ne_zero (h.1 t ht), fun s hs t ht hst e => h.2 s hs t ht hst (inv_injective e)⟩

/-- **Case B** (`.tex` L383–L391): `∀ j, m_j < 0`. Case A at `θ∨` (`m∨ = −m`, so some
`m∨_j > 0`), then `lem_reflect`: `Ψ_θ(w⁻¹) = (−1)^r e(w)^{2r} Ψ_{θ∨}(w) ≠ 0`. -/
theorem caseB_global [Infinite K] {k : ℕ} (IH : MainAt K ι k) (M : Finset ι)
    (θ : Fin (k + 1) → ℤ) (hcard : k + 1 ≤ M.card) (hinj : Function.Injective (rhoShiftPaper θ))
    (hneg : ∀ j, rhoShiftPaper θ j < 0) :
    ∃ w : ι → K, Admissible w M ∧ psiHead w M (k + 1) θ ≠ 0 := by
  have hvee := rhoShiftPaper_thetaVee θ
  have hinjV : Function.Injective (rhoShiftPaper (thetaVee θ)) := by
    rw [hvee]; exact neg_injective.comp hinj
  obtain ⟨w, hadm, hΨ⟩ := caseA_global IH M (thetaVee θ) hcard hinjV
    ⟨0, by rw [hvee]; have := hneg 0; simp only [Pi.neg_apply]; omega⟩
  refine ⟨fun t => (w t)⁻¹, admissible_inv hadm, ?_⟩
  rw [lem_reflect w M (k + 1) θ hadm]
  refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ ?_)) hΨ
  exact Finset.prod_ne_zero_iff.2 hadm.1

/-! ## `thm:main` -/

theorem mainAt_all [Infinite K] (r : ℕ) : MainAt K ι r := by
  induction r with
  | zero =>
    intro M θ _ _
    obtain ⟨w, hw⟩ := exists_admissible (K := K) M
    exact ⟨w, hw, by rw [psiHead_rank_zero]; exact one_ne_zero⟩
  | succ k IH =>
    intro M θ hcard hinj
    by_cases hpos : ∃ j, 0 ≤ rhoShiftPaper θ j
    · exact caseA_global IH M θ hcard hinj hpos
    · push Not at hpos
      exact caseB_global IH M θ hcard hinj hpos

/-- **`thm:main`** (Q559 `.tex` L360–L393, Clio 2026-10-23): for `|M| ≥ r` and `θ ∈ ℤ^r` with
pairwise distinct paper ρ-shifts `m_j = θ_j + j − 1` (1-indexed; `rhoShiftPaper`, 0-indexed
`θ_j + j`), `Ψ^C_{(1^r),θ}(M)` is not identically zero: over any infinite field, some
admissible point of `M` has `Ψ ≠ 0`. -/
theorem thm_main [Infinite K] (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) (hcard : r ≤ M.card)
    (hinj : Function.Injective (rhoShiftPaper θ)) :
    ∃ w : ι → K, Admissible w M ∧ psiHead w M r θ ≠ 0 :=
  mainAt_all r M θ hcard hinj

/-! ## `cor:criterion` (`.tex` L395–L409): the complete vanishing criterion, as an iff

"`Ψ = 0` in `ℚ(w)`" is encoded as "`Ψ` vanishes at every admissible point". `⇐` is
`psiHead_eq_zero_of_criterion` (forward ρ-shift law + boundary). `⇒` is `thm_main`. The
tie is the paper's hyperplane `θ_j − θ_k = k − j` with `j < k`, and Lean's 0-indexed
`j, k` give the same differences as the paper's 1-indexed ones. -/
theorem cor_criterion [Infinite K] [Nonempty ι] (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) :
    (∀ w : ι → K, Admissible w M → psiHead w M r θ = 0) ↔
      (M.card < r ∨ ∃ j k : Fin r, j < k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) := by
  constructor
  · intro hz
    by_contra hcon
    push Not at hcon
    obtain ⟨hcard, hnotie⟩ := hcon
    have hinj : Function.Injective (rhoShiftPaper θ) := by
      rw [injective_rhoShiftPaper_iff]
      by_contra hni
      obtain ⟨j, k, hjk, h⟩ :=
        (rhoTie_lt_iff_ne θ).2 ((exists_rhoTie_iff_not_injective θ).2 hni)
      exact absurd h (hnotie j k hjk)
    obtain ⟨w, hadm, hne⟩ := thm_main (K := K) M r θ hcard hinj
    exact hne (hz w hadm)
  · intro h w hadm
    obtain ⟨ord, hord⟩ := exists_ordOK M r
    exact psiHead_eq_zero_of_criterion w M r θ ord hadm hord h

/-! ## The statement at the paper's own conventions (one concrete instance)

The paper's `m_j = θ_j + j − 1` is 1-indexed. At `θ = (0,0)` it gives `m = (0,1)`, which is
distinct, and at `θ = (1,0)` it gives `m = (1,1)`, a tie (the hyperplane `θ_1 − θ_2 = 2 − 1`).
`rhoShiftPaper` returns exactly these. `thm_main` then applies at the first, and the
direct evaluation at `w = (2,3)` gives the value `5/9 ≠ 0`, with no existential. -/

theorem paper_m_00 : rhoShiftPaper (![0, 0] : Fin 2 → ℤ) = ![0, 1] := by
  funext j; fin_cases j <;> rfl

theorem paper_m_10 : rhoShiftPaper (![1, 0] : Fin 2 → ℤ) = ![1, 1] := by
  funext j; fin_cases j <;> rfl

theorem inst_thm_main : ∃ w : ℕ → ℚ, Admissible w {0, 1} ∧ psiHead w {0, 1} 2 ![0, 0] ≠ 0 :=
  thm_main {0, 1} 2 _ (by decide) (by rw [paper_m_00]; decide)

/-- Direct value: `Ψ^C_{(1,1),(0,0)}({2,3}) = (3/4)(8/9)(5/6) · det[[1,2],[1,3]] / (3−2) = 5/9`. -/
theorem inst_value : psiHead wI {0, 1} 2 ![0, 0] = 5 / 9 := by
  rw [thm_alt_paper wI {0, 1} 2 _ (snocOrd 1 ordI') admI ordI_ok]
  have e : ({0, 1} : Finset ℕ).powersetCard 2 = {{0, 1}} := by decide
  have e2 : (({0, 1} : Finset ℕ).powersetCard 2).powersetCard 2 = ∅ := by decide
  have e3 : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
  simp [e, Bfactor, diagFactor, pairFactor, wI, vand, Matrix.det_fin_two, snocOrd, ordI',
    rhoShiftPaper, Matrix.vandermonde, Fin.snoc]
  norm_num

/-! ## Lesions on the final theorem: ask Lean for `False` from each lesioned statement -/

/-- `thm_main` over `ℚ`, `ι = ℕ`, with `|M| ≥ r` and/or distinctness weakened to `P ∨ _`. -/
def ThmMainWith (Pcard Pinj : Prop) : Prop :=
  ∀ (M : Finset ℕ) (r : ℕ) (θ : Fin r → ℤ), (Pcard ∨ r ≤ M.card) →
    (Pinj ∨ Function.Injective (rhoShiftPaper θ)) →
    ∃ w : ℕ → ℚ, Admissible w M ∧ psiHead w M r θ ≠ 0

/-- Positive control: nothing dropped **is** `thm_main`. -/
theorem thmMainWith_control : ThmMainWith False False := fun M r θ hc hi =>
  thm_main M r θ (hc.resolve_left id) (hi.resolve_left id)

/-- **L-card (drop `|M| ≥ r`): refutable** at `M = ∅`, `r = 1`, `θ = (0)` (shifts are trivially
distinct): no head injection exists, so `Ψ = 0` at every point. -/
theorem lesion_card_refutable : ¬ ThmMainWith True False := by
  intro H
  obtain ⟨w, hadm, hne⟩ := H ∅ 1 ![0] (Or.inl trivial)
    (Or.inr fun a b _ => Subsingleton.elim a b)
  obtain ⟨ord, hord⟩ := exists_ordOK (ι := ℕ) (∅ : Finset ℕ) 1
  exact hne (psiHead_eq_zero_of_criterion w ∅ 1 _ ord hadm hord (Or.inl (by simp)))

/-- **L-dist (drop distinctness): refutable** at `M = {0,1}`, `r = 2`, `θ = (1,0)` (`m = (1,1)`,
and `|M| = r` holds): the forward ρ-shift law kills `Ψ` at every admissible point. -/
theorem lesion_dist_refutable' : ¬ ThmMainWith False True := by
  intro H
  obtain ⟨w, hadm, hne⟩ := H {0, 1} 2 ![1, 0] (Or.inr (by decide)) (Or.inl trivial)
  obtain ⟨ord, hord⟩ := exists_ordOK (ι := ℕ) ({0, 1} : Finset ℕ) 2
  exact hne (psiHead_eq_zero_of_criterion w _ 2 _ ord hadm hord
    (Or.inr ⟨0, 1, by decide, by decide⟩))

/-- **Pair (drop both): refutable**, a fortiori. Each single is already refutable with the other
hypothesis *discharged*, so joint fatality is not a separate question here. -/
theorem lesion_pair_refutable' : ¬ ThmMainWith True True := fun H =>
  lesion_dist_refutable' fun M r θ _ hi => H M r θ (Or.inl trivial) hi

local instance fact_prime_two' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **L-infinite (drop `Infinite K`): refutable** at `K = ZMod 2`, `M = {0,1}`, `r = 0`:
there is no admissible point at all (two distinct nonzero elements of `𝔽₂` do not exist).
So the encoding's "some admissible point" needs `K` large, as `ℚ(w)` is. -/
theorem lesion_infinite_refutable :
    ¬ ∃ w : ℕ → ZMod 2, Admissible w {0, 1} ∧ psiHead w {0, 1} 0 ![] ≠ 0 := by
  rintro ⟨w, ⟨h0, hd⟩, -⟩
  have a := h0 0 (by simp)
  have b := h0 1 (by simp)
  have c := hd 0 (by simp) 1 (by simp) (by decide)
  revert a b c
  generalize w 0 = x
  generalize w 1 = y
  revert x y
  decide

end TworowD4Kernel.ThmMain
