/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.AlternantExpansion

/-!
# Q559 `lem:blockB`: the block avoiding `n` has order `≤ −r` at `w_n → ∞`

Formalises `lem:blockB` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
L184–L219 (Clio, 2026-10-23; registry `clio-Q559-block-avoiding-n`):

> `deg_∞ Ψ^{C,−} ≤ −r`, and the coefficient of `w_n^{−r}` in `Ψ^{C,−}` is
> `(−1)^r Ψ^C_{(1^r),θ+1}(M')`, `M' = M ∖ {w_n}`.

Here `Ψ^{C,−} = ∑_{T ⊆ M', |T| = r} B_M(T) det(x_i^{m_j})/V(T)` (`psiMinus`), the summands of
`thm:alt` (`thm_alt_paper`, the paper's literal form) whose `T` avoids `n`.

## Encoding of "order at `w_n = ∞`" (decided before writing Lean)

`K` is an abstract field and `w n` a value in it, so there is no variable to expand in.
Substitute `w n = u⁻¹` with `u ≠ 0`. The statement is then the pair of **equalities**

* (I)  `psiMinus = (−u)^r · G(u)` for every admissible `u`, where
  `G(u) = ∑_{T ⊆ M'} (∏_{x∈T} F(u,x)) (∏_{x∈T} x) B_{M'}(T) det(x^m)/V(T)` (`gBlock`) and
  `F(u,x) = (1 − u/x)/(1 − u x)` (`regFactor`);
* (II) `G(0) = Ψ^C_{(1^r),θ+1}(M')` (`psiHead` at `M.erase n`, **by `eq:Psidef`**).

`G` is a rational function of `u` whose only `u`-dependent denominators are `1 − u x`
(`x ∈ M'`), each equal to `1` at `u = 0`; so `G` is regular at `u = 0` and (I) says
`Ψ^{C,−} = u^r · (regular)`, i.e. `deg_∞ ≤ −r`, with `u^r`-coefficient `(−1)^r G(0)`, which
(II) identifies. Regularity of `G` at `0` is read off the definition of `gBlock`, **not**
proved as a theorem about a valuation — this is the scope limit of the encoding. (Options
considered: `RatFunc`/`intDegree` — would need the whole `Bfactor` layer re-typed over
`RatFunc K`; a cleared-denominator polynomial identity — loses the `T`-indexing.)

Pre-measured before any Lean (`scratch/1112c2_blockB.py`, exact `Fraction`s, 58 random
admissible instances, `n ≤ 5`, `r ≤ 3`, signed `θ`): (I) `58/58`, (II) `58/58` against an
independent `eq:Psidef` evaluator, `w_n = 10⁹` numerics `58/58`; lesion control (II with
`θ` for `θ+1`) agrees `3/58`, all three degenerate (target `0`, two equal `m_j`).

Encoding: `rhoShift` is 0-indexed; the paper's `m` is `rhoShiftPaper` and the paper's
literal Vandermonde is `vand`; this file uses only the paper form.
-/

namespace TworowD4Kernel.BlockB

open Finset
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction
open TworowD4Kernel.AlternantExpansion

variable {ι : Type*} {K : Type*} [DecidableEq ι] [Field K]

/-- The regular factor `F(u,x) = (1 − u/x)/(1 − u x)`; `F(0,x) = 1`. -/
noncomputable def regFactor (u x : K) : K := (1 - u / x) / (1 - u * x)

/-- The alternant factor `det(x_i^{m_j}) / V(T)` of `thm:alt`, paper form. -/
noncomputable def altPaper (w : ι → K) {r : ℕ} (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ)
    (T : Finset ι) : K :=
  (Matrix.of fun i j => w (ord T i) ^ rhoShiftPaper θ j).det / vand (fun i => w (ord T i))

/-- `Ψ^{C,−}`: the `thm:alt` summands with `n ∉ T`. -/
noncomputable def psiMinus (w : ι → K) (M : Finset ι) (n : ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) : K :=
  ∑ T ∈ (M.erase n).powersetCard r, Bfactor w M T * altPaper w ord θ T

/-- `Ψ^{C,+}`: the `thm:alt` summands with `n ∈ T`. -/
noncomputable def psiPlus (w : ι → K) (M : Finset ι) (n : ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) : K :=
  ∑ T ∈ (M.powersetCard r).filter (n ∈ ·), Bfactor w M T * altPaper w ord θ T

/-- `G(u)`: the regular cofactor of `u^r` in `Ψ^{C,−}` at `w_n = u⁻¹`. -/
noncomputable def gBlock (w : ι → K) (M : Finset ι) (n : ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (u : K) : K :=
  ∑ T ∈ (M.erase n).powersetCard r,
    (∏ i ∈ T, regFactor u (w i)) * (∏ i ∈ T, w i) * Bfactor w (M.erase n) T *
      altPaper w ord θ T

/-! ## The split `Ψ = Ψ^+ + Ψ^-` -/

theorem powersetCard_filter_not_mem (M : Finset ι) (n : ι) (r : ℕ) :
    (M.powersetCard r).filter (fun T => n ∉ T) = (M.erase n).powersetCard r := by
  ext T
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_erase]
  tauto

/-- The paper's split of `thm:alt` by whether `T` contains the largest index. -/
theorem psiHead_split (w : ι → K) (M : Finset ι) (n : ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hord : OrdOK M r ord) :
    psiHead w M r θ = psiPlus w M n r θ ord + psiMinus w M n r θ ord := by
  rw [thm_alt_paper w M r θ ord hadm hord, psiPlus, psiMinus,
    ← powersetCard_filter_not_mem, Finset.sum_filter_add_sum_filter_not]
  rfl

/-! ## One cross factor at `t = n` -/

omit [DecidableEq ι] in
/-- `(1 − 1/(w_n x))/(1 − w_n/x) = −u x · F(u,x)` at `w_n = u⁻¹` (`.tex` L201–L206). -/
theorem crossFactor_at_inv {w : ι → K} {n i : ι} {u : K} (hu : u ≠ 0) (hwn : w n = u⁻¹)
    (hx : w i ≠ 0) (hux : 1 - u * w i ≠ 0) :
    crossFactor w n i = -u * w i * regFactor u (w i) := by
  have hux' : u * w i - 1 ≠ 0 := fun h => hux (by linear_combination -h)
  rw [crossFactor, regFactor, hwn]
  field_simp
  ring

/-- `B_M(T) = B_{M'}(T) · ∏_{x∈T} cross(n, x)` when `n ∈ M`, `n ∉ T` (`.tex` L196–L199). -/
theorem Bfactor_erase {w : ι → K} {M T : Finset ι} {n : ι} (hn : n ∈ M) (hnT : n ∉ T) :
    Bfactor w M T = Bfactor w (M.erase n) T * ∏ i ∈ T, crossFactor w n i := by
  have hdiff : M \ T = insert n ((M.erase n) \ T) := by
    ext t
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨htM, htT⟩
      by_cases h : t = n
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, htM⟩, htT⟩
    · rintro (rfl | ⟨⟨-, htM⟩, htT⟩)
      · exact ⟨hn, hnT⟩
      · exact ⟨htM, htT⟩
  have hnot : n ∉ (M.erase n) \ T := by simp
  rw [Bfactor, Bfactor, hdiff, Finset.prod_insert hnot]
  ring

/-! ## (I): `Ψ^{C,−} = (−u)^r G(u)` -/

/-- **`lem:blockB`, part (I).** At `w_n = u⁻¹`, `Ψ^{C,−} = (−u)^r · G(u)`. -/
theorem psiMinus_eq (w : ι → K) (M : Finset ι) {n : ι} (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hn : n ∈ M) {u : K}
    (hwn : w n = u⁻¹) :
    psiMinus w M n r θ ord = (-u) ^ r * gBlock w M n r θ ord u := by
  have hu : u ≠ 0 := by
    intro h; apply hadm.1 n hn; rw [hwn, h, inv_zero]
  rw [psiMinus, gBlock, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hT
  have hnT : n ∉ T := fun h => by simpa using hTM h
  have hcross : ∏ i ∈ T, crossFactor w n i =
      (-u) ^ r * ((∏ i ∈ T, regFactor u (w i)) * ∏ i ∈ T, w i) := by
    rw [Finset.prod_congr rfl fun i hi => crossFactor_at_inv hu hwn
      (hadm.1 i (Finset.mem_of_mem_erase (hTM hi))) ?_]
    · rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, hTc]; ring
    · intro h
      have hiM := hTM hi
      have hin : i ≠ n := Finset.ne_of_mem_erase hiM
      apply hadm.2 i (Finset.mem_of_mem_erase hiM) n hn hin
      rw [hwn]
      exact eq_inv_of_mul_eq_one_left (by linear_combination -h)
  rw [Bfactor_erase hn hnT, hcross]
  ring

/-! ## (II): `G(0) = Ψ^C_{(1^r),θ+1}(M')` -/

theorem regFactor_zero (x : K) : regFactor 0 x = 1 := by simp [regFactor]

theorem rhoShiftPaper_add_one {r : ℕ} (θ : Fin r → ℤ) (j : Fin r) :
    rhoShiftPaper (fun j => θ j + 1) j = rhoShiftPaper θ j + 1 := by
  simp only [rhoShiftPaper]; ring

/-- `(∏_{x∈T} x) det(x_i^{m_j}) = det(x_i^{m_j+1})` (row scaling, `.tex` L214–L216). -/
theorem prod_mul_altPaper (w : ι → K) (M : Finset ι) {r : ℕ} (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hord : OrdOK M r ord)
    {T : Finset ι} (hT : T ∈ M.powersetCard r) :
    (∏ i ∈ T, w i) * altPaper w ord θ T = altPaper w ord (fun j => θ j + 1) T := by
  obtain ⟨ho, ho'⟩ := hord T hT
  obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hT
  have himg : Finset.univ.image (ord T) = T := by
    refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
      exact ho' i
    · rw [Finset.card_image_of_injective _ ho, Finset.card_univ, Fintype.card_fin, hTc]
  have hprod : ∏ i ∈ T, w i = ∏ i, w (ord T i) := by
    conv_lhs => rw [← himg]
    rw [Finset.prod_image fun a _ b _ h => ho h]
  have hrow : (Matrix.of fun i j => w (ord T i) ^ rhoShiftPaper (fun j => θ j + 1) j) =
      Matrix.of fun i j => w (ord T i) * w (ord T i) ^ rhoShiftPaper θ j := by
    ext i j
    simp only [Matrix.of_apply, rhoShiftPaper_add_one]
    rw [zpow_add_one₀ (hadm.1 _ (hTM (ho' i)))]
    ring
  rw [altPaper, altPaper, hrow, Matrix.det_mul_column, hprod, mul_div_assoc]
  rfl

/-- **`lem:blockB`, part (II).** `G(0) = Ψ^C_{(1^r),θ+1}(M ∖ {n})`, the latter by `eq:Psidef`. -/
theorem gBlock_zero (w : ι → K) (M : Finset ι) (n : ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hord : OrdOK M r ord) :
    gBlock w M n r θ ord 0 = psiHead w (M.erase n) r (fun j => θ j + 1) := by
  have hsub : M.erase n ⊆ M := Finset.erase_subset _ _
  have hadm' := admissible_mono hsub hadm
  have hord' := OrdOK.mono hsub hord
  rw [thm_alt_paper w (M.erase n) r _ ord hadm' hord', gBlock]
  refine Finset.sum_congr rfl fun T hT => ?_
  simp only [regFactor_zero, Finset.prod_const_one, one_mul]
  rw [mul_comm (∏ i ∈ T, w i), mul_assoc, prod_mul_altPaper w (M.erase n) θ ord hadm' hord' hT]
  rfl

/-- **`lem:blockB`** (`.tex` L193–L219, Q559, Clio 2026-10-23), in the `w_n = u⁻¹` encoding:
`Ψ^{C,−} = (−u)^r G(u)` with `G` regular at `u = 0` and `G(0) = Ψ^C_{(1^r),θ+1}(M')`.
Hence `deg_∞ Ψ^{C,−} ≤ −r` and its `w_n^{−r}`-coefficient is `(−1)^r Ψ^C_{(1^r),θ+1}(M')`. -/
theorem lem_blockB (w : ι → K) (M : Finset ι) {n : ι} (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) (hadm : Admissible w M) (hord : OrdOK M r ord) (hn : n ∈ M)
    {u : K} (hwn : w n = u⁻¹) :
    psiMinus w M n r θ ord = (-u) ^ r * gBlock w M n r θ ord u ∧
      (-1) ^ r * gBlock w M n r θ ord 0 = (-1) ^ r * psiHead w (M.erase n) r (fun j => θ j + 1) :=
  ⟨psiMinus_eq w M r θ ord hadm hn hwn, by rw [gBlock_zero w M n r θ ord hadm hord]⟩

/-- Regularity of `G` at `0`, as far as this encoding states it: every `u`-dependent
denominator `1 − u·x` of `gBlock` is `1` at `u = 0`. -/
theorem gBlock_denoms_at_zero (w : ι → K) (M : Finset ι) (n : ι) :
    ∀ i ∈ M.erase n, (1 : K) - 0 * w i ≠ 0 := by simp

/-! ## Lesions (brief §3): ask Lean for `False` from each lesioned statement

`L-T`: drop `n ∉ T` (allow `T ∋ n`). `L-w`: drop `w ≠ 0` (keep only distinctness).
Both single lesions are refutable, so the pair lesion is refutable a fortiori; it is stated
separately anyway with its own witness. -/

/-- **L-T, termwise.** `Bfactor_erase` without `n ∉ T` is false: `M = T = {0}`, `w ≡ 2`. -/
theorem lesionT_termwise_refutable :
    ¬ ∀ (M T : Finset ℕ) (n : ℕ) (w : ℕ → ℚ), n ∈ M →
      Bfactor w M T = Bfactor w (M.erase n) T * ∏ i ∈ T, crossFactor w n i := by
  intro h
  have := h {0} {0} 0 (fun _ => 2) (by simp)
  have e1 : ({0} : Finset ℕ).powersetCard 2 = ∅ := by decide
  simp [Bfactor, crossFactor, diagFactor, e1] at this
  norm_num at this

/-- **L-T, block level.** Summing (I) over all `r`-subsets of `M` (not of `M'`) is false. -/
theorem lesionT_refutable :
    ¬ ∀ (M : Finset ℕ) (n : ℕ) (r : ℕ) (θ : Fin r → ℤ) (ord : Finset ℕ → Fin r → ℕ)
      (w : ℕ → ℚ) (u : ℚ), Admissible w M → OrdOK M r ord → n ∈ M → w n = u⁻¹ →
      ∑ T ∈ M.powersetCard r, Bfactor w M T * altPaper w ord θ T =
        (-u) ^ r * ∑ T ∈ M.powersetCard r,
          (∏ i ∈ T, regFactor u (w i)) * (∏ i ∈ T, w i) * Bfactor w (M.erase n) T *
            altPaper w ord θ T := by
  intro h
  have hadm : Admissible (fun _ => (2 : ℚ)) {0} := ⟨by simp, by simp⟩
  have hord : OrdOK ({0} : Finset ℕ) 1 (fun _ _ => 0) := by
    intro T hT
    have : T = {0} := by
      obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 hT
      exact Finset.eq_of_subset_of_card_le h1 (by simp [h2])
    subst this
    exact ⟨fun a b _ => Subsingleton.elim a b, fun _ => by simp⟩
  have := h {0} 0 1 (fun _ => 0) (fun _ _ => 0) (fun _ => 2) (1 / 2) hadm hord (by simp)
    (by norm_num)
  have e1 : ({0} : Finset ℕ).powersetCard 1 = {{0}} := by decide
  have e2 : ({0} : Finset ℕ).powersetCard 2 = ∅ := by decide
  simp [e1, e2, Bfactor, diagFactor, regFactor, altPaper, vand, rhoShiftPaper] at this
  norm_num at this

/-- **L-w.** (I) with `Admissible` weakened to distinctness alone is false:
`M = {0,1}`, `n = 1`, `w = (2, 0)`, `u = 0` (so `w n = 0⁻¹ = 0`), `r = 1`, `θ = 0`. -/
theorem lesionW_refutable :
    ¬ ∀ (M : Finset ℕ) (n : ℕ) (r : ℕ) (θ : Fin r → ℤ) (ord : Finset ℕ → Fin r → ℕ)
      (w : ℕ → ℚ) (u : ℚ), (∀ s ∈ M, ∀ t ∈ M, s ≠ t → w s ≠ w t) → n ∈ M → w n = u⁻¹ →
      psiMinus w M n r θ ord = (-u) ^ r * gBlock w M n r θ ord u := by
  intro h
  have := h {0, 1} 1 1 (fun _ => 0) (fun _ _ => 0) (fun i => if i = 0 then 2 else 0) 0
    (by decide) (by simp) (by simp)
  have e1 : (({0, 1} : Finset ℕ).erase 1).powersetCard 1 = {{0}} := by decide
  have e2 : ({0} : Finset ℕ).powersetCard 2 = ∅ := by decide
  have e3 : ({0, 1} : Finset ℕ) \ {0} = {1} := by decide
  simp [psiMinus, e1, e2, e3, Bfactor, diagFactor, crossFactor, altPaper, vand,
    rhoShiftPaper] at this
  norm_num at this

/-- **L-T ∧ L-w, the pair.** Both hypotheses dropped together; own witness (the `L-w`
instance summed over all of `M.powersetCard 1 = {{0},{1}}`: LHS `3/4 + 1`, RHS `0`). -/
theorem lesionTW_refutable :
    ¬ ∀ (M : Finset ℕ) (n : ℕ) (r : ℕ) (θ : Fin r → ℤ) (ord : Finset ℕ → Fin r → ℕ)
      (w : ℕ → ℚ) (u : ℚ), (∀ s ∈ M, ∀ t ∈ M, s ≠ t → w s ≠ w t) → n ∈ M → w n = u⁻¹ →
      ∑ T ∈ M.powersetCard r, Bfactor w M T * altPaper w ord θ T =
        (-u) ^ r * ∑ T ∈ M.powersetCard r,
          (∏ i ∈ T, regFactor u (w i)) * (∏ i ∈ T, w i) * Bfactor w (M.erase n) T *
            altPaper w ord θ T := by
  intro h
  have := h {0, 1} 1 1 (fun _ => 0) (fun T _ => if 0 ∈ T then 0 else 1)
    (fun i => if i = 0 then 2 else 0) 0 (by decide) (by simp) (by simp)
  have e1 : ({0, 1} : Finset ℕ).powersetCard 1 = {{0}, {1}} := by decide
  have e2 : ({0} : Finset ℕ).powersetCard 2 = ∅ := by decide
  have e2' : ({1} : Finset ℕ).powersetCard 2 = ∅ := by decide
  have e3 : ({0, 1} : Finset ℕ) \ {0} = {1} := by decide
  have e4 : ({0, 1} : Finset ℕ) \ {1} = {0} := by decide
  simp [e1, e2, e2', e3, e4, Bfactor, diagFactor, crossFactor, altPaper, vand,
    rhoShiftPaper] at this
  norm_num at this

end TworowD4Kernel.BlockB
