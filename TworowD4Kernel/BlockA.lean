/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.BlockB

/-!
# Q559 `lem:blockA`: the block containing `n` (a rank-lowering branching rule)

Formalises `lem:blockA` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
L224–L296 (Clio, 2026-10-23; registry `clio-Q559-block-containing-n`):

> If `m_1, …, m_r` are pairwise distinct and `j*` is the (unique) argmax, then
> `Ψ^{C,+} = w_n^{m_{j*}−r+1} ((−1)^{r+j*} Ψ^C_{(1^{r−1}),θ̂}(M') + O(w_n^{−1}))`.

## Encoding (the same as `BlockB.lean`, chosen jointly)

`r = k + 1`, indices `j : Fin (k+1)` are **0-indexed**, so the paper's sign `(−1)^{r+j*}`
(1-indexed `r`, `j*`) is `(−1)^{k + j*}` here; `m = rhoShiftPaper θ`;
`θ̂ l = m_{j*.succAbove l} − l`
(so `rhoShiftPaper θ̂ = m ∘ j*.succAbove`, the paper's `m̂` listed in increasing `j`).

Substitute `w n = u⁻¹`. The statement is the pair of **equalities**

* (I)  `u^{m_{j*} − k} · Ψ^{C,+} = H(u)` for every admissible `u` (`psiPlus_eq`), where
  `H(u) = ∑_{T' ⊆ M', |T'| = k} B_{M'}(T') β(u,T') L(u,T') / (V(T') ∏_{x∈T'} (1 − u x))`
  (`hBlock`), `β` is the `w_n`-part of the weight (`betaReg`, computation (i)), the factor
  `u^{−k}∏(1 − u x)` is the `w_n`-part of the Vandermonde (computation (ii)), and
  `L(u,T') = ∑_j (−1)^{k+j} u^{m_{j*}−m_j} D_j` is the Laplace expansion along the last row
  (`lapReg`, computation (iii));
* (II) `H(0) = (−1)^{k+j*} Ψ^C_{(1^k),θ̂}(M')` (`hBlock_zero`, `psiHead` = `eq:Psidef`).

`H`'s only `u`-dependent denominators are `1 − u x` (`x ∈ M'`), each `1` at `u = 0`, and its
`u`-powers `u^{m_{j*}−m_j}` have **natural** exponents (`expo`), so `H` is regular at `0`: the
regularity is read off the definition, exactly as for `BlockB.gBlock` (scope limit, shared).

**Where the hypotheses enter.** (I) needs only `m_j ≤ m_{j*}` for all `j` (`psiPlus_eq` is
stated under that weak hypothesis — Lean-verified that distinctness is not used there). (II)
needs the maximum to be **strict**: `expo j = 0 ↔ j = j*` is what kills the `j ≠ j*` Laplace
terms at `u = 0`. This is the `.tex`'s "the one place the distinctness hypothesis enters".

**Ordering.** `thm:alt` is used with the index order; here that is the hypothesis
`SnocCompat`: the order of `T' ∪ {n}` is the order of `T'` followed by `n` (`n` is the largest
index of `M`). `exists_snocCompat` shows it is satisfiable from any `OrdOK` data.

Pre-measured before any Lean (`scratch/1113_blockA.py`, exact `Fraction`s, 60 random
admissible instances, `n ≤ 5`, `r ≤ 3`, signed `θ`, `m` distinct): (I) `60/60`, (II) `60/60`
against an independent `eq:Psidef` evaluator, `w_n = 10⁹` numerics `60/60`. Controls: sign
dropped agrees `49/60`, **all 49 uninformative** (sign `+1` or target `0`); on the 11 informative
instances it agrees `0/11`. Non-argmax `j` agrees `0/60` and its target is nonzero in `37`, so
that control is not silent.
-/

namespace TworowD4Kernel.BlockA

open Finset
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction
open TworowD4Kernel.AlternantExpansion
open TworowD4Kernel.BlockB

variable {ι : Type*} {K : Type*} [DecidableEq ι] [Field K]

/-! ## Pure algebra: the Vandermonde along its last row -/

/-- `V(x_1,…,x_{k+1}) = V(x_1,…,x_k) · ∏_{i ≤ k} (x_{k+1} − x_i)` (computation (ii)). -/
theorem vand_succ_last {k : ℕ} (v : Fin (k + 1) → K) :
    vand v =
      vand (fun i : Fin k => v i.castSucc) * ∏ i : Fin k, (v (Fin.last k) - v i.castSucc) := by
  have hI : ∀ i : Fin (k + 1), Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
    intro i; ext j; simp
  simp only [vand, Matrix.det_vandermonde]
  rw [Fin.prod_univ_castSucc]
  simp_rw [hI, Finset.prod_filter]
  have hlast : ∏ j : Fin (k + 1), (if Fin.last k < j then v j - v (Fin.last k) else 1) = 1 := by
    refine Finset.prod_eq_one fun j _ => ?_
    rw [if_neg (not_lt.2 (Fin.le_last j))]
  rw [hlast, mul_one]
  simp_rw [Fin.prod_univ_castSucc (n := k), Fin.castSucc_lt_castSucc_iff,
    Fin.castSucc_lt_last, if_true]
  rw [Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  congr 1
  ext j; simp

/-! ## (i) The weight factors -/

/-- `β_{T'}` of `.tex` L251–L254, before substitution. -/
noncomputable def betaRaw (w : ι → K) (M' T' : Finset ι) (n : ι) : K :=
  diagFactor w n * (∏ i ∈ T', (1 - (w n * w i)⁻¹)) * ∏ t ∈ M' \ T', crossFactor w t n

/-- `B_M(T' ⊔ {n}) = B_{M'}(T') · β_{T'}` (`.tex` L249–L261). -/
theorem Bfactor_insert {w : ι → K} {M T' : Finset ι} {n : ι} (hT' : T' ⊆ M.erase n) :
    Bfactor w M (insert n T') = Bfactor w (M.erase n) T' * betaRaw w (M.erase n) T' n := by
  have hnT : n ∉ T' := fun h => by simpa using hT' h
  have hdiff : M \ insert n T' = M.erase n \ T' := by
    ext t; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
  have hpairs : ∏ p ∈ (insert n T').powersetCard 2, pairFactor w p =
      (∏ p ∈ T'.powersetCard 2, pairFactor w p) * ∏ i ∈ T', (1 - (w n * w i)⁻¹) := by
    rw [Finset.powersetCard_succ_insert hnT, Finset.prod_union, Finset.powersetCard_one,
      Finset.prod_image, Finset.prod_map]
    · congr 1
      refine Finset.prod_congr rfl fun i hi => ?_
      have hin : n ≠ i := fun h => hnT (h ▸ hi)
      simp [pairFactor, Finset.prod_pair hin]
    · intro a ha b hb hab
      simp only [Finset.coe_map, Set.mem_image, Finset.mem_coe] at ha hb
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      have hxn : x ≠ n := fun h => hnT (h ▸ hx)
      have hyn : y ≠ n := fun h => hnT (h ▸ hy)
      have := congrArg (fun s : Finset ι => x ∈ s) hab
      simp [hxn] at this
      simp [this]
    · rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hb
      exact hnT ((Finset.mem_powersetCard.1 ha).1 (Finset.mem_insert_self n b))
  rw [Bfactor, Bfactor, betaRaw, Finset.prod_insert hnT, hpairs, hdiff]
  simp_rw [Finset.prod_insert hnT]
  rw [Finset.prod_mul_distrib]
  ring

/-- `β` at `w_n = u⁻¹`; every factor is `1` at `u = 0`. -/
noncomputable def betaReg (w : ι → K) (M' T' : Finset ι) (u : K) : K :=
  (1 - u ^ 2) * (∏ i ∈ T', (1 - u / w i)) * ∏ t ∈ M' \ T', (1 - u / w t) / (1 - w t * u)

theorem betaRaw_at_inv {w : ι → K} {M' T' : Finset ι} {n : ι} {u : K}
    (hwn : w n = u⁻¹) : betaRaw w M' T' n = betaReg w M' T' u := by
  rw [betaRaw, betaReg, diagFactor, hwn, inv_inv]
  congr 1
  · congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_inv, inv_inv]; ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [crossFactor, mul_inv, hwn, inv_inv, div_inv_eq_mul]; ring

theorem betaReg_zero (w : ι → K) (M' T' : Finset ι) : betaReg w M' T' 0 = 1 := by
  simp [betaReg]

/-! ## (iii) The alternant: Laplace expansion along the last row -/

/-- `m_{j*} − m_j` as a natural number (`Int.toNat`; exact when `m_j ≤ m_{j*}`). -/
def expo {k : ℕ} (θ : Fin (k + 1) → ℤ) (js j : Fin (k + 1)) : ℕ :=
  (rhoShiftPaper θ js - rhoShiftPaper θ j).toNat

/-- The minor `D_j` of `.tex` L268: rows `T'` (order `ord'`), column `j` deleted. -/
noncomputable def minorD (w : ι → K) {k : ℕ} (ord' : Finset ι → Fin k → ι) (θ : Fin (k + 1) → ℤ)
    (T' : Finset ι) (j : Fin (k + 1)) : K :=
  (Matrix.of fun i l : Fin k => w (ord' T' i) ^ rhoShiftPaper θ (j.succAbove l)).det

/-- `L(u,T') = ∑_j (−1)^{k+j} u^{m_{j*}−m_j} D_j`: the Laplace expansion,
normalised by `w_n^{m_{j*}}`. -/
noncomputable def lapReg (w : ι → K) {k : ℕ} (ord' : Finset ι → Fin k → ι) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (T' : Finset ι) (u : K) : K :=
  ∑ j : Fin (k + 1), (-1) ^ (k + j : ℕ) * u ^ expo θ js j * minorD w ord' θ T' j

/-- The index order of `T' ⊔ {n}` is that of `T'` followed by `n` (`.tex` L243–L245). -/
def SnocCompat (M : Finset ι) (n : ι) (k : ℕ) (ord : Finset ι → Fin (k + 1) → ι)
    (ord' : Finset ι → Fin k → ι) : Prop :=
  ∀ T' ∈ (M.erase n).powersetCard k,
    (∀ i, ord (insert n T') i.castSucc = ord' T' i) ∧ ord (insert n T') (Fin.last k) = n

/-- **Laplace along the last row** (`.tex` L266–L268):
`det(x_i^{m_j}) = ∑_j (−1)^{k+j} w_n^{m_j} D_j`. -/
theorem det_laplace_last (w : ι → K) {k : ℕ} {ord : Finset ι → Fin (k + 1) → ι}
    {ord' : Finset ι → Fin k → ι} (θ : Fin (k + 1) → ℤ) {T' : Finset ι} {n : ι}
    (h1 : ∀ i, ord (insert n T') i.castSucc = ord' T' i) (h2 : ord (insert n T') (Fin.last k) = n) :
    (Matrix.of fun i j => w (ord (insert n T') i) ^ rhoShiftPaper θ j).det =
      ∑ j : Fin (k + 1), (-1) ^ (k + j : ℕ) * w n ^ rhoShiftPaper θ j * minorD w ord' θ T' j := by
  rw [Matrix.det_succ_row _ (Fin.last k)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Fin.val_last, Matrix.of_apply, h2, minorD]
  congr 2
  ext i l
  simp [Matrix.submatrix_apply, Fin.succAbove_last, h1]

/-! ## (ii) The Vandermonde at `w_n = u⁻¹` -/

theorem vand_insert_at_inv (w : ι → K) {k : ℕ} {ord : Finset ι → Fin (k + 1) → ι}
    {ord' : Finset ι → Fin k → ι} {T' : Finset ι} {n : ι} {u : K} (hu : u ≠ 0) (hwn : w n = u⁻¹)
    (h1 : ∀ i, ord (insert n T') i.castSucc = ord' T' i) (h2 : ord (insert n T') (Fin.last k) = n) :
    vand (fun i => w (ord (insert n T') i)) =
      vand (fun i => w (ord' T' i)) * (u⁻¹ ^ k * ∏ i, (1 - u * w (ord' T' i))) := by
  rw [vand_succ_last]
  simp only [h1, h2, hwn]
  congr 1
  rw [← Fin.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  field_simp

/-! ## The scalar core of the combination step (`.tex` L273–L278) -/

theorem combine_core {k : ℕ} {u X V P : K} (hu : u ≠ 0) (c D : Fin (k + 1) → K)
    (m : Fin (k + 1) → ℤ) (ms : ℤ) (e : Fin (k + 1) → ℕ) (he : ∀ j, m j + e j = ms) :
    u ^ (ms - k) * (X * ((∑ j, c j * u⁻¹ ^ m j * D j) / (V * (u⁻¹ ^ k * P)))) =
      X * (∑ j, c j * u ^ e j * D j) / (V * P) := by
  have hS : (∑ j, c j * u⁻¹ ^ m j * D j) = u ^ (-ms) * ∑ j, c j * u ^ e j * D j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : u⁻¹ ^ m j = u ^ (-ms) * u ^ e j := by
      rw [inv_zpow', ← zpow_natCast, ← zpow_add₀ hu]
      congr 1; linarith [he j]
    rw [this]; ring
  have hpow : u ^ (ms - k) * u ^ (-ms) = (u ^ k)⁻¹ := by
    rw [← zpow_add₀ hu, ← zpow_natCast, ← zpow_neg]; congr 1; ring
  have hk : (u ^ k)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hu)
  calc u ^ (ms - k) * (X * ((∑ j, c j * u⁻¹ ^ m j * D j) / (V * (u⁻¹ ^ k * P))))
      = (u ^ (ms - k) * u ^ (-ms)) * (X * ∑ j, c j * u ^ e j * D j) /
          ((u ^ k)⁻¹ * (V * P)) := by rw [hS, inv_pow]; ring
    _ = X * (∑ j, c j * u ^ e j * D j) / (V * P) := by rw [hpow, mul_div_mul_left _ _ hk]

/-! ## (I): `u^{m_{j*} − k} Ψ^{C,+} = H(u)` -/

/-- `H(u)`: the regular cofactor of `w_n^{m_{j*}−k}` in `Ψ^{C,+}` at `w_n = u⁻¹`. -/
noncomputable def hBlock (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord' : Finset ι → Fin k → ι) (u : K) : K :=
  ∑ T' ∈ (M.erase n).powersetCard k,
    Bfactor w (M.erase n) T' * betaReg w (M.erase n) T' u * lapReg w ord' θ js T' u /
      (vand (fun i => w (ord' T' i)) * ∏ i, (1 - u * w (ord' T' i)))

/-- Reindex `Ψ^{C,+}` by `T = T' ⊔ {n}`, `T' ⊆ M'`, `|T'| = k` (`.tex` L242). -/
theorem psiPlus_reindex (w : ι → K) (M : Finset ι) {n : ι} (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (ord : Finset ι → Fin (k + 1) → ι) (hn : n ∈ M) :
    psiPlus w M n (k + 1) θ ord =
      ∑ T' ∈ (M.erase n).powersetCard k,
        Bfactor w M (insert n T') * altPaper w ord θ (insert n T') := by
  rw [psiPlus]
  refine Finset.sum_nbij' (fun T => T.erase n) (fun T' => insert n T') ?_ ?_ ?_ ?_ ?_
  · intro T hT
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT ⊢
    obtain ⟨⟨hTM, hTc⟩, hnT⟩ := hT
    exact ⟨Finset.erase_subset_erase n hTM, by rw [Finset.card_erase_of_mem hnT, hTc]; rfl⟩
  · intro T' hT'
    simp only [Finset.mem_filter, Finset.mem_powersetCard] at hT' ⊢
    obtain ⟨hTM, hTc⟩ := hT'
    have hnT : n ∉ T' := fun h => by simpa using hTM h
    refine ⟨⟨Finset.insert_subset hn (hTM.trans (Finset.erase_subset _ _)), ?_⟩,
      Finset.mem_insert_self _ _⟩
    rw [Finset.card_insert_of_notMem hnT, hTc]
  · intro T hT
    simp only [Finset.mem_filter] at hT
    exact Finset.insert_erase hT.2
  · intro T' hT'
    simp only [Finset.mem_powersetCard] at hT'
    exact Finset.erase_insert fun h => by simpa using hT'.1 h
  · intro T hT
    simp only [Finset.mem_filter] at hT
    rw [Finset.insert_erase hT.2]

/-- **`lem:blockA`, part (I).** At `w_n = u⁻¹`, `u^{m_{j*}−k} Ψ^{C,+} = H(u)`.
Only `m_j ≤ m_{j*}` is assumed: distinctness is **not** used here. -/
theorem psiPlus_eq (w : ι → K) (M : Finset ι) {n : ι} (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι) (js : Fin (k + 1))
    (hadm : Admissible w M) (hn : n ∈ M) (hcomp : SnocCompat M n k ord ord')
    (hle : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) {u : K} (hwn : w n = u⁻¹) :
    u ^ (rhoShiftPaper θ js - k) * psiPlus w M n (k + 1) θ ord = hBlock w M n k θ js ord' u := by
  have hu : u ≠ 0 := by
    intro h; apply hadm.1 n hn; rw [hwn, h, inv_zero]
  rw [psiPlus_reindex w M k θ ord hn, hBlock, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T' hT' => ?_
  obtain ⟨h1, h2⟩ := hcomp T' hT'
  have hTM := (Finset.mem_powersetCard.1 hT').1
  rw [Bfactor_insert hTM, betaRaw_at_inv hwn, altPaper, det_laplace_last w θ h1 h2,
    vand_insert_at_inv w hu hwn h1 h2, lapReg,
    ← combine_core (X := Bfactor w (M.erase n) T' * betaReg w (M.erase n) T' u) hu
      (fun j => (-1) ^ (k + j : ℕ)) (minorD w ord' θ T') (rhoShiftPaper θ)
      (rhoShiftPaper θ js) (expo θ js) fun j => by simp only [expo]; have := hle j; omega]
  simp only [hwn]

/-! ## (II): `H(0) = (−1)^{k+j*} Ψ^C_{(1^k),θ̂}(M')` -/

/-- `θ̂_l = m̂_l − l` (0-indexed form of the `.tex`'s `θ̂_l = m̂_l − l + 1`),
`m̂ = m ∘ j*.succAbove`. -/
def thetaHat {k : ℕ} (θ : Fin (k + 1) → ℤ) (js : Fin (k + 1)) : Fin k → ℤ :=
  fun l => rhoShiftPaper θ (js.succAbove l) - l

theorem rhoShiftPaper_thetaHat {k : ℕ} (θ : Fin (k + 1) → ℤ) (js : Fin (k + 1)) (l : Fin k) :
    rhoShiftPaper (thetaHat θ js) l = rhoShiftPaper θ (js.succAbove l) := by
  simp only [rhoShiftPaper, thetaHat]; ring

omit [DecidableEq ι] in
/-- **The one place strictness enters** (`.tex` L269–L276): at `u = 0` only the `j*` Laplace term
survives, because `expo θ j* j ≠ 0` for `j ≠ j*`. -/
theorem lapReg_zero (w : ι → K) {k : ℕ} (ord' : Finset ι → Fin k → ι) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (hmax : ∀ j, j ≠ js → rhoShiftPaper θ j < rhoShiftPaper θ js)
    (T' : Finset ι) :
    lapReg w ord' θ js T' 0 = (-1) ^ (k + js : ℕ) * minorD w ord' θ T' js := by
  rw [lapReg, Finset.sum_eq_single js]
  · simp [expo]
  · intro j _ hj
    have hlt := hmax j hj
    have he : expo θ js j ≠ 0 := by simp only [expo]; omega
    simp [zero_pow he]
  · simp

omit [DecidableEq ι] in
theorem minorD_js (w : ι → K) {k : ℕ} (ord' : Finset ι → Fin k → ι) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (T' : Finset ι) :
    minorD w ord' θ T' js =
      (Matrix.of fun i l : Fin k => w (ord' T' i) ^ rhoShiftPaper (thetaHat θ js) l).det := by
  simp only [minorD, rhoShiftPaper_thetaHat]

/-- **`lem:blockA`, part (II).** `H(0) = (−1)^{k+j*} Ψ^C_{(1^k),θ̂}(M ∖ {n})`, by `eq:Psidef`. -/
theorem hBlock_zero (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord' : Finset ι → Fin k → ι) (hadm : Admissible w M)
    (hord' : OrdOK (M.erase n) k ord')
    (hmax : ∀ j, j ≠ js → rhoShiftPaper θ j < rhoShiftPaper θ js) :
    hBlock w M n k θ js ord' 0 = (-1) ^ (k + js : ℕ) * psiHead w (M.erase n) k (thetaHat θ js) := by
  have hadm' := admissible_mono (Finset.erase_subset n M) hadm
  rw [thm_alt_paper w (M.erase n) k (thetaHat θ js) ord' hadm' hord', Finset.mul_sum, hBlock]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [betaReg_zero, lapReg_zero w ord' θ js hmax, minorD_js]
  simp only [zero_mul, sub_zero, Finset.prod_const_one, mul_one]
  ring

/-! ## The lemma, with the paper's hypotheses -/

/-- **`lem:blockA`** (`.tex` L224–L296, Q559, Clio 2026-10-23), in the `w_n = u⁻¹` encoding
shared with `lem_blockB`. With `m = rhoShiftPaper θ` pairwise distinct and `j*` its argmax:
`u^{m_{j*}−k} Ψ^{C,+} = H(u)` with `H` regular at `u = 0` and
`H(0) = (−1)^{k+j*} Ψ^C_{(1^k),θ̂}(M')` (`r = k+1`, 0-indexed `j*`; the paper's `(−1)^{r+j*}`).
Hence `Ψ^{C,+} = w_n^{m_{j*}−r+1}((−1)^{r+j*} Ψ^C_{(1^{r−1}),θ̂}(M') + O(w_n^{−1}))`. -/
theorem lem_blockA (w : ι → K) (M : Finset ι) {n : ι} (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι) (js : Fin (k + 1))
    (hadm : Admissible w M) (hn : n ∈ M) (hord' : OrdOK (M.erase n) k ord')
    (hcomp : SnocCompat M n k ord ord') (hinj : Function.Injective (rhoShiftPaper θ))
    (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) {u : K} (hwn : w n = u⁻¹) :
    u ^ (rhoShiftPaper θ js - k) * psiPlus w M n (k + 1) θ ord = hBlock w M n k θ js ord' u ∧
      hBlock w M n k θ js ord' 0 =
        (-1) ^ (k + js : ℕ) * psiHead w (M.erase n) k (thetaHat θ js) := by
  refine ⟨psiPlus_eq w M k θ ord ord' js hadm hn hcomp harg hwn,
    hBlock_zero w M n k θ js ord' hadm hord' fun j hj => ?_⟩
  exact lt_of_le_of_ne (harg j) fun h => hj (hinj h)

/-- Regularity of `H` at `0`, as far as this encoding states it: the `u`-powers of `lapReg`
have natural exponents, and every `u`-dependent denominator (`1 − u·x`, `1 − x·u`) is `1` at `0`. -/
theorem hBlock_denoms_at_zero (x : K) : (1 : K) - 0 * x = 1 ∧ (1 : K) - x * 0 = 1 := by simp

/-! ## Non-vacuity of `SnocCompat`: the index order of `T' ⊔ {n}` exists and is an order -/

/-- `ord T = (ord' (T ∖ {n}), n)`. -/
def snocOrd (n : ι) {k : ℕ} (ord' : Finset ι → Fin k → ι) : Finset ι → Fin (k + 1) → ι :=
  fun T => Fin.snoc (α := fun _ => ι) (ord' (T.erase n)) n

theorem snocOrd_compat (M : Finset ι) (n : ι) {k : ℕ} (ord' : Finset ι → Fin k → ι) :
    SnocCompat M n k (snocOrd n ord') ord' := by
  intro T' hT'
  have hnT : n ∉ T' := fun h => by simpa using (Finset.mem_powersetCard.1 hT').1 h
  refine ⟨fun i => ?_, ?_⟩
  · simp [snocOrd, Finset.erase_insert hnT]
  · simp [snocOrd]

/-- `snocOrd` is a genuine ordering (`OrdOK`) of every `T ∋ n` in `M.powersetCard (k+1)`. -/
theorem snocOrd_ordOK (M : Finset ι) (n : ι) {k : ℕ} (ord' : Finset ι → Fin k → ι)
    (hord' : OrdOK (M.erase n) k ord') :
    ∀ T ∈ (M.powersetCard (k + 1)).filter (n ∈ ·),
      Function.Injective (snocOrd n ord' T) ∧ ∀ i, snocOrd n ord' T i ∈ T := by
  intro T hT
  obtain ⟨hTP, hnT⟩ := Finset.mem_filter.1 hT
  obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hTP
  have hE : T.erase n ∈ (M.erase n).powersetCard k :=
    Finset.mem_powersetCard.2 ⟨Finset.erase_subset_erase n hTM,
      by rw [Finset.card_erase_of_mem hnT, hTc]; rfl⟩
  obtain ⟨hinj, hmem⟩ := hord' _ hE
  have hne : ∀ i, ord' (T.erase n) i ≠ n := fun i h => by
    have := hmem i; rw [h] at this; simp at this
  refine ⟨fun a b hab => ?_, fun i => ?_⟩
  · induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast b => exact absurd (by simpa [snocOrd] using hab.symm) (hne b)
    | cast a =>
      induction b using Fin.lastCases with
      | last => exact absurd (by simpa [snocOrd] using hab) (hne a)
      | cast b => exact congrArg _ (hinj (by simpa [snocOrd] using hab))
  · induction i using Fin.lastCases with
    | last => simpa [snocOrd] using hnT
    | cast i => simpa [snocOrd] using Finset.mem_of_mem_erase (hmem i)

/-! ## Lesions (brief §3): ask Lean for `False` from each lesioned (II)

One instance throughout: `M = {0,1}`, `n = 1`, `k = 1` (`r = 2`), `w = (2, 3)`, `ord' ≡ 0`.
Then `M' = {0}` and every quantity is a `1 × 1` determinant. -/

/-- The instance's weights. -/
def wI : ℕ → ℚ := fun i => if i = 0 then 2 else 3

/-- `H(0)` on the instance, in closed form: `(3/4)(−0^{e_0} 2^{m_1} + 0^{e_1} 2^{m_0})`. -/
theorem inst_hBlock_zero (θ : Fin 2 → ℤ) (js : Fin 2) :
    hBlock wI {0, 1} 1 1 θ js (fun _ _ => 0) 0 =
      3 / 4 * (-(0 : ℚ) ^ expo θ js 0 * 2 ^ rhoShiftPaper θ 1 +
        (0 : ℚ) ^ expo θ js 1 * 2 ^ rhoShiftPaper θ 0) := by
  have e1 : ({0} : Finset ℕ).powersetCard 1 = {{0}} := by decide
  have e2 : ({0} : Finset ℕ).powersetCard 2 = ∅ := by decide
  have e3 : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
  simp [hBlock, e3, e1, e2, Bfactor, diagFactor, betaReg, lapReg, minorD, vand, wI,
    Fin.sum_univ_two, Matrix.det_unique]
  norm_num

/-- `Ψ^C_{(1),θ̂}(M') = (3/4) 2^{θ̂_0}` on the instance, via `thm_alt_paper`. -/
theorem inst_psiHead (φ : Fin 1 → ℤ) :
    psiHead wI (({0, 1} : Finset ℕ).erase 1) 1 φ = 3 / 4 * 2 ^ φ 0 := by
  have e3 : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
  have hadm : Admissible wI ({0} : Finset ℕ) := ⟨by simp [wI], by simp⟩
  have hord : OrdOK ({0} : Finset ℕ) 1 (fun _ _ => 0) := by
    intro T hT
    have : T = {0} := by
      obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 hT
      exact Finset.eq_of_subset_of_card_le h1 (by simp [h2])
    subst this
    exact ⟨fun a b _ => Subsingleton.elim a b, fun _ => by simp⟩
  rw [e3, thm_alt_paper wI {0} 1 φ _ hadm hord]
  have e1 : ({0} : Finset ℕ).powersetCard 1 = {{0}} := by decide
  have e2 : ({0} : Finset ℕ).powersetCard 2 = ∅ := by decide
  simp [e1, e2, Bfactor, diagFactor, vand, wI, Matrix.det_unique, rhoShiftPaper]
  norm_num

/-- The shape of (II) on the instance, as a predicate of `(θ, j*, sign)`. -/
def InstII (θ : Fin 2 → ℤ) (js : Fin 2) (sgn : ℚ) : Prop :=
  hBlock wI {0, 1} 1 1 θ js (fun _ _ => 0) 0 =
    sgn * psiHead wI (({0, 1} : Finset ℕ).erase 1) 1 (thetaHat θ js)

/-- **L-dist.** Drop distinctness, keep `j*` an argmax: false at `θ = (1,0)`, `m = (1,1)`, `j* = 0`
(`H(0) = 0`: the two tied Laplace terms cancel; target `−3/2`). -/
theorem lesion_dist_refutable :
    ¬ ∀ (θ : Fin 2 → ℤ) (js : Fin 2), (∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) →
      InstII θ js ((-1) ^ (1 + js : ℕ)) := by
  intro h
  have := h ![1, 0] 0 (by decide)
  simp only [InstII, inst_hBlock_zero, inst_psiHead] at this
  simp [expo, rhoShiftPaper, thetaHat] at this

/-- **L-arg.** Keep distinctness, let `j*` be a non-argmax: false at `θ = (0,0)`, `m = (0,1)`,
`j* = 0` (`H(0) = −3/4`, target `−3/2`). -/
theorem lesion_arg_refutable :
    ¬ ∀ (θ : Fin 2 → ℤ) (js : Fin 2), Function.Injective (rhoShiftPaper θ) →
      InstII θ js ((-1) ^ (1 + js : ℕ)) := by
  intro h
  have := h ![0, 0] 0 (by decide)
  simp only [InstII, inst_hBlock_zero, inst_psiHead] at this
  simp [expo, rhoShiftPaper, thetaHat] at this
  all_goals norm_num at this

/-- **L-sign.** All hypotheses, sign `(−1)^{k+j*}` dropped: false at `θ = (2,0)`, `m = (2,1)`,
`j* = 0` (the sign is `−1` there; `H(0) = −3/2`, unsigned target `+3/2`). -/
theorem lesion_sign_refutable :
    ¬ ∀ (θ : Fin 2 → ℤ) (js : Fin 2), Function.Injective (rhoShiftPaper θ) →
      (∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) → InstII θ js 1 := by
  intro h
  have := h ![2, 0] 0 (by decide) (by decide)
  simp only [InstII, inst_hBlock_zero, inst_psiHead] at this
  simp [expo, rhoShiftPaper, thetaHat] at this
  all_goals norm_num at this

/-- **L-dist ∧ L-arg, the pair.** Both hypotheses dropped. Refutable a fortiori (each single lesion
is); stated with the `L-arg` witness, which satisfies neither dropped hypothesis's *role*
(`j* = 0` is not an argmax of `m = (0,1)`). -/
theorem lesion_pair_refutable :
    ¬ ∀ (θ : Fin 2 → ℤ) (js : Fin 2), InstII θ js ((-1) ^ (1 + js : ℕ)) := fun h =>
  lesion_arg_refutable fun θ js _ => h θ js

/-- **Positive control on the same instance**: (II) *holds* at the `L-sign` witness with the sign,
so the instance itself is not what the lesions are refuting. -/
theorem inst_control : InstII ![2, 0] 0 ((-1) ^ (1 + (0 : Fin 2) : ℕ)) := by
  simp only [InstII, inst_hBlock_zero, inst_psiHead]
  simp [expo, rhoShiftPaper, thetaHat]

end TworowD4Kernel.BlockA
