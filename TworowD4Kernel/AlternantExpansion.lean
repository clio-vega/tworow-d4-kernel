/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ReciprocalRestriction
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.LinearCombination

/-!
# `thm:alt`: the alternant expansion of `Ψ^C_{(1^r),θ}`, in this repository's encoding

Formalises `thm:alt` as quoted in `projects/proofs/2026-10-24-Q565-zero-locus-in-M.tex`
L134–L146 (Clio, 2026-10-22, registry node `clio-Q553-alternant-expansion`):

> `Ψ(M) = ∑_{T ⊆ M, |T| = r} B(T) · det(x_i^{m_j}) / V(T)`, `V(T) = ∏_{i<k}(x_k − x_i)`,
> `m_j = θ_j + j − 1` (`j` 1-indexed).

The paper proof (group the head injections by their image `T`; the factors symmetric in the
ordering are `B(T)`; the rest is `∑_σ ∏ x_{σ j}^{m_j} / V(x ∘ σ)`, which is Leibniz over
`V`) is formalised here with **no new mathematics**.

## Encoding correction (recorded, not patched into the paper)

This repository's `rhoShift θ j = θ j + j − 1` uses **0-indexed** `j` (`RhoShiftVanishing`
`rhoShiftPaper_eq`: paper `m = rhoShift + 1`). `psiAlt` therefore carries `det(x_i^{m_j−1})`,
which is `det(x_i^{m_j}) / ∏ x_i`. Hence `AltExpansion` holds with
`V(T) = Vand(T) / ∏_{i∈T} w_i` (`vandTw` below), and **not** with the paper's literal
Vandermonde. Measured before writing Lean (`scratch/1111c2_alt_shift.py`, exact
rationals, 60 random admissible `M`, signed entries): paper form `60/60`, this encoding with
`vandTw` `60/60`, this encoding with literal `Vand` `14/60` (the control separates). The
paper is right; only the Lean `V` parameter must absorb the shift. The vanishing results in
`RhoShiftVanishing`/`BoundaryEmptyIndex`/`ReciprocalPair` are unaffected (they never fix `V`).

## Ordering

The paper orders `T` "in increasing index order". Here `ord T` may be **any** bijection
`Fin r → T` (`OrdOK`); the ratio `det/V` does not depend on the choice, and the proof never
uses an order on `ι`.
-/

namespace TworowD4Kernel.AlternantExpansion

open Finset
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction

variable {ι : Type*} {K : Type*} [DecidableEq ι] [Field K]

/-- The Vandermonde determinant; by `Matrix.det_vandermonde` it is `∏_{i<k} (v_k − v_i)`. -/
noncomputable def vand {r : ℕ} (v : Fin r → K) : K := (Matrix.vandermonde v).det

/-- The `V` of `thm:alt` in this encoding: `Vand(w ∘ ord T) / ∏_i w(ord T i)`. -/
noncomputable def vandTw (w : ι → K) {r : ℕ} (ord : Finset ι → Fin r → ι) (T : Finset ι) : K :=
  vand (fun i => w (ord T i)) / ∏ i, w (ord T i)

/-- `ord T` is a bijection `Fin r → T` for every `r`-subset `T ⊆ M`. -/
def OrdOK (M : Finset ι) (r : ℕ) (ord : Finset ι → Fin r → ι) : Prop :=
  ∀ T ∈ M.powersetCard r, Function.Injective (ord T) ∧ ∀ i, ord T i ∈ T

/-- The summand of `eq:Psidef` (so that `psiHead` is `∑ h ∈ headInjections M r, headTerm`). -/
noncomputable def headTerm (w : ι → K) (M : Finset ι) {r : ℕ} (θ : Fin r → ℤ) (h : Fin r → ι) :
    K :=
  (∏ j, (1 - (w (h j))⁻¹ ^ 2) * w (h j) ^ θ j) *
    (∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
      (1 - (w (h j) * w (h k))⁻¹) / (1 - w (h j) / w (h k))) *
    ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor w t (h j)

theorem psiHead_eq_sum_headTerm (w : ι → K) (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) :
    psiHead w M r θ = ∑ h ∈ headInjections M r, headTerm w M θ h := rfl

/-! ## Step A: one head injection -/

theorem vand_ne_zero {r : ℕ} {v : Fin r → K} (hv : Function.Injective v) : vand v ≠ 0 := by
  rw [vand, Matrix.det_vandermonde]
  refine Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun k hk => ?_
  refine sub_ne_zero.2 fun h => ?_
  have := hv h
  subst this
  simp at hk

/-- `∏_{j<k} x_k = ∏_k x_k^k`. -/
theorem prod_Ioi_eq_prod_pow {r : ℕ} (v : Fin r → K) :
    ∏ j, ∏ k ∈ Ioi j, v k = ∏ k, v k ^ (k : ℕ) := by
  rw [Finset.prod_comm' (s' := fun k => Iio k) (t' := univ) (fun j k => by simp)]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finset.prod_const, Fin.card_Iio]

/-- The pair products: ordered pairs `j < k` of a head injection ↔ 2-subsets of its image. -/
theorem prod_pairs_eq_prod_powersetCard_two {r : ℕ} (w : ι → K) {h : Fin r → ι}
    (hh : Function.Injective h) :
    ∏ j, ∏ k ∈ Ioi j, (1 - (w (h j) * w (h k))⁻¹) =
      ∏ p ∈ (Finset.univ.image h).powersetCard 2, pairFactor w p := by
  rw [Finset.prod_sigma']
  refine Finset.prod_bij (fun x _ => ({h x.1, h x.2} : Finset ι)) ?_ ?_ ?_ ?_
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx
    refine Finset.mem_powersetCard.2 ⟨?_, Finset.card_pair (hh.ne hx.ne)⟩
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl <;> exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · rintro ⟨j, k⟩ hx ⟨j', k'⟩ hx' heq
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx hx'
    have heq' : ({h j, h k} : Finset ι) = {h j', h k'} := heq
    have h1 : h j ∈ ({h j', h k'} : Finset ι) := by rw [← heq']; simp
    have h2 : h k ∈ ({h j', h k'} : Finset ι) := by rw [← heq']; simp
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      replace h1 := hh h1 <;> replace h2 := hh h2 <;> subst h1 <;> subst h2
    · exact absurd hx (lt_irrefl _)
    · rfl
    · exact absurd (hx.trans hx') (lt_irrefl _)
    · exact absurd hx (lt_irrefl _)
  · intro p hp
    obtain ⟨hpT, hpc⟩ := Finset.mem_powersetCard.1 hp
    obtain ⟨y, z, hyz, rfl⟩ := Finset.card_eq_two.1 hpc
    have hy : y ∈ Finset.univ.image h := hpT (by simp)
    have hz : z ∈ Finset.univ.image h := hpT (by simp)
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hz
    have hjk : j ≠ k := fun e => hyz (e ▸ rfl)
    rcases lt_or_gt_of_ne hjk with hlt | hlt
    · exact ⟨⟨j, k⟩, by simp [hlt], rfl⟩
    · exact ⟨⟨k, j⟩, by simp [hlt], Finset.pair_comm _ _⟩
  · rintro ⟨j, k⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, Finset.mem_Ioi, true_and] at hx
    simp only [pairFactor, Finset.prod_pair (hh.ne hx.ne)]

/-- **Step A.** One head injection with image `T`: `headTerm = B(T) · ∏ X_j^{m_j} / V(X)`. -/
theorem headTerm_eq (w : ι → K) (M : Finset ι) {r : ℕ} (θ : Fin r → ℤ) {h : Fin r → ι}
    (hh : Function.Injective h) (h0 : ∀ j, w (h j) ≠ 0) :
    headTerm w M θ h = Bfactor w M (Finset.univ.image h) *
      ((∏ j, w (h j) ^ (rhoShift θ j + 1)) / vand (fun j => w (h j))) := by
  have hinjOn : Set.InjOn h ↑(Finset.univ : Finset (Fin r)) := hh.injOn
  have hD : ∏ j, (1 - (w (h j))⁻¹ ^ 2) * w (h j) ^ θ j =
      (∏ i ∈ Finset.univ.image h, diagFactor w i) * ∏ j, w (h j) ^ θ j := by
    rw [Finset.prod_image hinjOn, ← Finset.prod_mul_distrib]; rfl
  have hP : ∏ j, ∏ k ∈ Finset.univ.filter (j < ·),
        (1 - (w (h j) * w (h k))⁻¹) / (1 - w (h j) / w (h k)) =
      (∏ p ∈ (Finset.univ.image h).powersetCard 2, pairFactor w p) *
        (∏ j : Fin r, w (h j) ^ (j : ℕ)) / vand (fun j => w (h j)) := by
    rw [← prod_pairs_eq_prod_powersetCard_two w hh,
      ← prod_Ioi_eq_prod_pow (fun j => w (h j))]
    simp only [vand, Matrix.det_vandermonde]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hfilt : Finset.univ.filter (j < ·) = Ioi j := by ext k; simp
    rw [hfilt, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [one_sub_div (h0 k), div_div_eq_mul_div]
  have hC : ∏ t ∈ M \ Finset.univ.image h, ∏ j, crossFactor w t (h j) =
      ∏ t ∈ M \ Finset.univ.image h, ∏ i ∈ Finset.univ.image h, crossFactor w t i := by
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [Finset.prod_image hinjOn]
  have hexp : ∏ j, w (h j) ^ (rhoShift θ j + 1) =
      (∏ j, w (h j) ^ θ j) * ∏ j : Fin r, w (h j) ^ (j : ℕ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← zpow_natCast, ← zpow_add₀ (h0 j)]
    congr 1
    unfold rhoShift; ring
  unfold headTerm Bfactor
  rw [hD, hP, hC, hexp]
  ring

/-! ## Steps C–E: the fibre over one `T` is Leibniz over `V` -/

theorem fibre_sum (w : ι → K) (M : Finset ι) {r : ℕ} (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hord : OrdOK M r ord)
    {T : Finset ι} (hT : T ∈ M.powersetCard r) :
    ∑ h ∈ (headInjections M r).filter (fun h => Finset.univ.image h = T),
        (∏ j, w (h j) ^ (rhoShift θ j + 1)) / vand (fun j => w (h j)) =
      (Matrix.of fun i j => w (ord T i) ^ rhoShift θ j).det / vandTw w ord T := by
  obtain ⟨ho, ho'⟩ := hord T hT
  obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hT
  have himg : Finset.univ.image (ord T) = T := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact ho' i
    · rw [Finset.card_image_of_injective _ ho, Finset.card_univ, Fintype.card_fin, hTc]
  have hx0 : ∀ i, w (ord T i) ≠ 0 := fun i => hadm.1 _ (hTM (ho' i))
  have hxinj : Function.Injective (fun i => w (ord T i)) := by
    intro i j e
    by_contra hne
    exact hadm.2 _ (hTM (ho' i)) _ (hTM (ho' j)) (ho.ne hne) e
  have hV := vand_ne_zero hxinj
  calc _ = ∑ σ : Equiv.Perm (Fin r), (∏ j, w (ord T (σ j)) ^ (rhoShift θ j + 1)) /
          vand (fun j => w (ord T (σ j))) := by
        symm
        refine Finset.sum_bij (fun σ _ => fun j => ord T (σ j)) ?_ ?_ ?_ (fun _ _ => rfl)
        · intro σ _
          simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset]
          refine ⟨⟨fun j => hTM (ho' _), ho.comp σ.injective⟩, ?_⟩
          refine Eq.trans ?_ himg
          ext y
          simp only [Finset.mem_image, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨j, rfl⟩; exact ⟨σ j, rfl⟩
          · rintro ⟨i, rfl⟩; exact ⟨σ.symm i, by simp⟩
        · intro σ _ τ _ e
          exact Equiv.ext fun j => ho (congrFun e j)
        · intro g hg
          simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hg
          obtain ⟨⟨-, hginj⟩, hgimg⟩ := hg
          have hex : ∀ j, ∃ i, ord T i = g j := fun j => by
            have : g j ∈ Finset.univ.image (ord T) := by
              rw [himg, ← hgimg]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
            simpa using this
          choose f hf using hex
          have hfinj : Function.Injective f := fun j j' e => hginj (by rw [← hf j, ← hf j', e])
          exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfinj),
            Finset.mem_univ _, funext fun j => hf j⟩
    _ = ∑ σ : Equiv.Perm (Fin r), ((Equiv.Perm.sign σ : ℤ) : K) * (∏ i, w (ord T i)) *
          (∏ j, w (ord T (σ j)) ^ rhoShift θ j) / vand (fun j => w (ord T j)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        have hv : vand (fun j => w (ord T (σ j))) =
            ((Equiv.Perm.sign σ : ℤ) : K) * vand (fun j => w (ord T j)) := by
          have : Matrix.vandermonde (fun j => w (ord T (σ j))) =
              (Matrix.vandermonde (fun j => w (ord T j))).submatrix σ id := rfl
          rw [vand, vand, this, Matrix.det_permute]
        have hpc : ∏ i, w (ord T (σ i)) = ∏ i, w (ord T i) :=
          Equiv.prod_comp σ (fun i => w (ord T i))
        have hprod : ∏ j, w (ord T (σ j)) ^ (rhoShift θ j + 1) =
            (∏ i, w (ord T i)) * ∏ j, w (ord T (σ j)) ^ rhoShift θ j := by
          rw [← hpc, ← Finset.prod_mul_distrib]
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [zpow_add_one₀ (hx0 _), mul_comm]
        have hs : ((Equiv.Perm.sign σ : ℤ) : K) * ((Equiv.Perm.sign σ : ℤ) : K) = 1 := by
          rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp
        have hs0 : ((Equiv.Perm.sign σ : ℤ) : K) ≠ 0 := left_ne_zero_of_mul_eq_one hs
        rw [hv, hprod, div_eq_div_iff (mul_ne_zero hs0 hV) hV]
        linear_combination (-((∏ i, w (ord T i)) * (∏ j, w (ord T (σ j)) ^ rhoShift θ j) *
          vand (fun j => w (ord T j)))) * hs
    _ = _ := by
        rw [Matrix.det_apply, vandTw, div_div_eq_mul_div, Finset.sum_mul]
        simp only [div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [Units.smul_def, zsmul_eq_mul]
        simp only [Matrix.of_apply]
        ring

/-! ## `thm:alt` -/

/-- **`thm:alt`** (`.tex` L134–L146; `clio-Q553-alternant-expansion`, 2026-10-22), in this
repository's encoding: `AltExpansion` holds at every admissible `M`, with `x = w` and
`V = vandTw w ord`, for any bijective ordering `ord`. -/
theorem thm_alt (w : ι → K) (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hord : OrdOK M r ord) :
    AltExpansion w w (vandTw w ord) ord θ M := by
  unfold AltExpansion
  rw [psiHead_eq_sum_headTerm, psiAlt,
    ← Finset.sum_fiberwise_of_maps_to (g := fun h => Finset.univ.image h)
      (t := M.powersetCard r) ?maps]
  · refine Finset.sum_congr rfl fun T hT => ?_
    rw [← fibre_sum w M θ ord hadm hord hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h hh => ?_
    obtain ⟨hhM, himg⟩ := Finset.mem_filter.1 hh
    simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hhM
    obtain ⟨hmem, hinj⟩ := hhM
    rw [headTerm_eq w M θ hinj (fun j => hadm.1 _ (hmem j)), himg]
  · intro h hh
    simp only [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hh
    refine Finset.mem_powersetCard.2 ⟨fun y hy => ?_, ?_⟩
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hy
      exact hh.1 j
    · rw [Finset.card_image_of_injective _ hh.2, Finset.card_univ, Fintype.card_fin]

/-! ## `thm:red` unconditionally

`ReciprocalRestriction.thm_red_a/b` took `thm:alt` at `M` and at the reduced set as `Prop`
binders. `thm_alt` now discharges both, so `thm:red` holds for the defining sum `eq:Psidef`
with no hypothesis beyond the paper's. -/

omit [DecidableEq ι] in
theorem OrdOK.mono {M N : Finset ι} {r : ℕ} {ord : Finset ι → Fin r → ι} (hsub : N ⊆ M)
    (h : OrdOK M r ord) : OrdOK N r ord :=
  fun T hT => h T (Finset.powersetCard_mono hsub hT)

omit [DecidableEq ι] in
theorem admissible_mono {w : ι → K} {M N : Finset ι} (hsub : N ⊆ M) (h : Admissible w M) :
    Admissible w N :=
  ⟨fun t ht => h.1 t (hsub ht), fun s hs t ht => h.2 s (hsub hs) t (hsub ht)⟩

omit [DecidableEq ι] in
/-- **Non-vacuity of `OrdOK`.** Some ordering satisfies it (here: `Finset.equivFin`). -/
theorem exists_ordOK [Nonempty ι] (M : Finset ι) (r : ℕ) : ∃ ord, OrdOK M r ord := by
  classical
  refine ⟨fun T i => if h : T.card = r then (T.equivFin.symm (Fin.cast h.symm i) : ι)
    else Classical.arbitrary ι, ?_⟩
  intro T hT
  have hc := (Finset.mem_powersetCard.1 hT).2
  refine ⟨fun i j e => ?_, fun i => ?_⟩
  · simp only [dif_pos hc] at e
    have := T.equivFin.symm.injective (Subtype.ext e)
    simpa using this
  · simp only [dif_pos hc]
    exact (T.equivFin.symm _).2

/-- **`thm:red` (b), unconditional** (`.tex` L241–L249). -/
theorem thm_red_b_uncond (M : Finset ι) (r : ℕ) (w : ι → K) (ord : Finset ι → Fin r → ι)
    (θ : Fin r → ℤ) {a b : ι} (hord : OrdOK M r ord) (hadm : Admissible w M) (hab : a ≠ b)
    (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    psiHead w M r θ = psiHead w ((M.erase a).erase b) r θ := by
  have hsub : (M.erase a).erase b ⊆ M :=
    (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  exact thm_red_b M r w w (vandTw w ord) ord θ (thm_alt w M r θ ord hadm hord)
    (thm_alt w _ r θ ord (admissible_mono hsub hadm) (hord.mono hsub)) hadm hab ha hb hw

/-- **`thm:red` (a), unconditional** (`.tex` L241–L249). -/
theorem thm_red_a_uncond (M : Finset ι) (r : ℕ) (w : ι → K) (ord : Finset ι → Fin r → ι)
    (θ : Fin r → ℤ) {a : ι} (hord : OrdOK M r ord) (hadm : Admissible w M) (ha : a ∈ M)
    (hw : w a * w a = 1) :
    psiHead w M r θ = psiHead w (M.erase a) r θ := by
  have hsub : M.erase a ⊆ M := Finset.erase_subset _ _
  exact thm_red_a M r w w (vandTw w ord) ord θ (thm_alt w M r θ ord hadm hord)
    (thm_alt w _ r θ ord (admissible_mono hsub hadm) (hord.mono hsub)) hadm ha hw

/-! ## Lesion LV (pre-registered before this block was built)

Prediction: with the paper's **literal** `V = Vand` in place of `vandTw`, `AltExpansion` is
**refutable** in this encoding, witness `r = 1`, `M = {0}`, `w ≡ 2`, `θ = 0`: the head sum is
`B = 3/4`, the literal-`V` alternant is `B · 2⁻¹ / 1 = 3/8`. -/

theorem LV_literal_vandermonde_refutable :
    ¬ AltExpansion (fun _ : ℕ => (2 : ℚ)) (fun _ => 2) (fun _ => vand (fun _ : Fin 1 => (2 : ℚ)))
      (fun _ _ => 0) (0 : Fin 1 → ℤ) {0} := by
  intro H
  have hadm : Admissible (fun _ : ℕ => (2 : ℚ)) {0} :=
    ⟨fun _ _ => by norm_num, fun s hs t ht hst => by
      simp only [Finset.mem_singleton] at hs ht; exact absurd (hs.trans ht.symm) hst⟩
  have hord : OrdOK ({0} : Finset ℕ) 1 (fun _ _ => 0) := by
    intro T hT
    have hT' : T = {0} := by
      have := Finset.mem_powersetCard.1 hT
      exact Finset.eq_of_subset_of_card_le this.1 (by simp [this.2])
    subst hT'
    exact ⟨fun i j _ => Subsingleton.elim i j, fun _ => Finset.mem_singleton_self _⟩
  have h2 := thm_alt (fun _ : ℕ => (2 : ℚ)) {0} 1 0 (fun _ _ => 0) hadm hord
  unfold AltExpansion at H h2
  rw [H] at h2
  have hP : ({0} : Finset ℕ).powersetCard 1 = {{0}} := by
    simpa using Finset.powersetCard_self ({0} : Finset ℕ)
  simp only [psiAlt, hP, rhoShift, Pi.zero_apply, Fin.val_eq_zero, CharP.cast_eq_zero,
    add_zero, zero_sub, Int.reduceNeg, zpow_neg, zpow_one, Matrix.det_unique,
    Fin.default_eq_zero, Fin.isValue, Matrix.of_apply, vand, Matrix.vandermonde_apply, pow_zero,
    div_one, sum_singleton, vandTw, univ_unique, prod_const, card_singleton, pow_one, one_div,
    ne_eq, inv_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true, div_self, mul_one] at h2
  have hB : Bfactor (fun _ : ℕ => (2 : ℚ)) {0} {0} = 3 / 4 := by
    unfold Bfactor
    rw [Finset.powersetCard_eq_empty.2 (by simp), Finset.sdiff_self, Finset.prod_empty,
      Finset.prod_empty, Finset.prod_singleton]
    unfold diagFactor
    norm_num
  rw [hB] at h2
  norm_num at h2

/-! ## Axioms (measured 2026-11-11 c2, `lake env lean` on this file)

`thm_alt`, `thm_red_b_uncond`, `thm_red_a_uncond`, `LV_literal_vandermonde_refutable`,
`exists_ordOK`: `[propext, Classical.choice, Quot.sound]`. Control in the same invocation:
`theorem bad_control_1111c2 : (1 : ℕ) = 2 := by sorry` printed `[sorryAx]`. -/

end TworowD4Kernel.AlternantExpansion
