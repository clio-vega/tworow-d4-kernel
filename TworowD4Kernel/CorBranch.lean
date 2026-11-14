/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ThmMain

/-!
# Q559 `cor:branch`: one-step branching at `w_n → ∞`

This file formalises `cor:branch` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
L427–L437 (Clio, 2026-10-23):

> Under the hypotheses of `thm:main` with `max_j m_j ≥ 0`,
> `lim_{w_n→∞} w_n^{−(m_{j*}−r+1)} Ψ^C_{(1^r),θ}(M) = (−1)^{r+j*} Ψ^C_{(1^{r−1}),θ̂}(M ∖ {w_n})`.

## Encoding (R2, as in `BlockA`/`LemOrder`, with no filters)

Substitute `w_n = u⁻¹`, so that `w_n^{−(m*−k)} = u^{m*−k}` where `r = k+1`. A *limit at `u = 0`*
of a function that agrees with a rational function regular at `0` is **the value of that
rational function at `0`**. So the corollary becomes two equalities:

* `cor_branch_exists`: some `F` with `RegAt0 F` agrees with `u^{m*−k} Ψ(w[n ↦ u⁻¹])` at every
  admissible `u`, and `F 0 = (−1)^{k+js} Ψ(M', θ̂)`. Here `js` is 0-indexed, so
  `(−1)^{k+js} = (−1)^{r+j*}` with the paper's 1-indexed `j*`.
* `cor_branch`: **every** `G` with `RegAt0 G` that agrees at the admissible `u` has
  `G 0 = (−1)^{k+js} Ψ(M', θ̂)`. This uniqueness is what makes `F 0` a *limit* rather than an
  arbitrary value. It rests on `RegAt0.zero_eq_of_eq_off`: two regular-at-0 functions that
  agree off a finite set have the same value at `0`, over an infinite field.

I did not use filters because the equality form exists. `Filter.Tendsto` along `𝓝[≠] 0` would
need a topology on `K`, while `ℚ(w_1,…,w_{n−1})`, the paper's field, carries none in Mathlib.
The coefficientwise limit in `K((w_n^{-1}))` *is* "the constant term of the regular part".

**Deviation (more general, not weaker).** `|M| ≥ r` is not assumed, since the identity does not
use it, and `n` is any element of `M` (the index order enters only through `glueOrd`, as in
`ThmMain`). `w` only needs to be admissible on `M' = M ∖ {n}`.
-/

namespace TworowD4Kernel.CorBranch

open Finset Polynomial
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction
open TworowD4Kernel.AlternantExpansion
open TworowD4Kernel.BlockB
open TworowD4Kernel.BlockA
open TworowD4Kernel.LemOrder
open TworowD4Kernel.ThmMain

variable {K : Type*} [Field K]

/-! ## Uniqueness of the value at `0` -/

/-- **The limit is well defined.** Over an infinite field, two functions that are regular at `0`
and agree off a finite set agree at `0`. -/
theorem RegAt0.zero_eq_of_eq_off [Infinite K] {f g : K → K} (hf : RegAt0 f) (hg : RegAt0 g)
    (S : Finset K) (h : ∀ u ∉ S, f u = g u) : f 0 = g 0 := by
  by_contra hne
  obtain ⟨u, huS, hu⟩ := (hf.sub hg).exists_ne (sub_ne_zero.2 hne) S
  exact hu (by simp only [h u huS, sub_self])

variable {ι : Type*} [DecidableEq ι]

/-! ## The finitely many `u` where `w[n ↦ u⁻¹]` is not admissible -/

/-- `{0} ∪ {1/w_i : i ∈ M ∖ {n}}`. -/
def badSet [DecidableEq K] (w : ι → K) (M : Finset ι) (n : ι) : Finset K :=
  insert 0 ((M.erase n).image fun i => (w i)⁻¹)

theorem admissible_update_inv [DecidableEq K] {w : ι → K} {M : Finset ι} {n : ι} (hn : n ∈ M)
    (hadm : Admissible w (M.erase n)) {u : K} (hu : u ∉ badSet w M n) :
    Admissible (Function.update w n u⁻¹) M := by
  simp only [badSet, Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and] at hu
  have h := admissible_update_insert hadm (Finset.notMem_erase n M) (v := u⁻¹)
    (inv_ne_zero hu.1) (fun i hi h => hu.2 i hi (by rw [← h, inv_inv]))
  rwa [Finset.insert_erase hn] at h

/-! ## `H(0)` needs admissibility on `M'` only -/

/-- `hBlock_zero` with `Admissible w (M ∖ {n})` instead of `Admissible w M`. The proof is the
same, because `hBlock_zero` only ever used the restriction. -/
theorem hBlock_zero' (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord' : Finset ι → Fin k → ι) (hadm' : Admissible w (M.erase n))
    (hord' : OrdOK (M.erase n) k ord')
    (hmax : ∀ j, j ≠ js → rhoShiftPaper θ j < rhoShiftPaper θ js) :
    hBlock w M n k θ js ord' 0 = (-1) ^ (k + js : ℕ) * psiHead w (M.erase n) k (thetaHat θ js) := by
  rw [thm_alt_paper w (M.erase n) k (thetaHat θ js) ord' hadm' hord', Finset.mul_sum, hBlock]
  refine Finset.sum_congr rfl fun T' _ => ?_
  rw [betaReg_zero, lapReg_zero w ord' θ js hmax, minorD_js]
  simp only [zero_mul, sub_zero, Finset.prod_const_one, mul_one]
  ring

/-! ## The identity, transported from `w[n ↦ u⁻¹]` back to `w` -/

/-- At every admissible `u`, `u^{m_{js}−k} Ψ(w[n ↦ u⁻¹]) = F(u)` with `F = orderF w`, which sees
only `w` on `M'`. This needs neither distinctness nor `|M| ≥ r`. -/
theorem order_identity_update (w : ι → K) (M : Finset ι) {n : ι} (hn : n ∈ M) (k : ℕ)
    (θ : Fin (k + 1) → ℤ) (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι)
    (js : Fin (k + 1)) (hord : OrdOK M (k + 1) ord) (hord' : OrdOK (M.erase n) k ord')
    (hcomp : SnocCompat M n k ord ord') (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js)
    (hpos : 0 ≤ rhoShiftPaper θ js) {u : K} (hadm₂ : Admissible (Function.update w n u⁻¹) M) :
    u ^ (rhoShiftPaper θ js - k) * psiHead (Function.update w n u⁻¹) M (k + 1) θ =
      orderF w M n k θ js ord ord' u := by
  have hagree : ∀ i ∈ M.erase n, w i = Function.update w n u⁻¹ i := fun i hi =>
    (Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _).symm
  have hid := psiHead_order_identity (Function.update w n u⁻¹) M k θ ord ord' js hadm₂ hn hord
    hcomp harg hpos (u := u) (by simp)
  have hord1 := OrdOK.mono (Finset.erase_subset n M) hord
  rw [hid, orderF, orderF, ← hBlock_congr θ js hord' hagree, ← gBlock_congr θ hord1 hagree]

/-- Any regular-at-0 `G` agreeing with `u^{m_{js}−k} Ψ` has `G 0 = F 0 = H(0)`. This is a lemma
for the lesions: it needs only `js` to be an argmax, not distinctness. -/
theorem limit_eq_orderF_zero [Infinite K] (w : ι → K) (M : Finset ι) {n : ι} (hn : n ∈ M)
    (k : ℕ) (θ : Fin (k + 1) → ℤ) (ord : Finset ι → Fin (k + 1) → ι)
    (ord' : Finset ι → Fin k → ι) (js : Fin (k + 1)) (hadm : Admissible w (M.erase n))
    (hord : OrdOK M (k + 1) ord) (hord' : OrdOK (M.erase n) k ord')
    (hcomp : SnocCompat M n k ord ord') (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js)
    (hpos : 0 ≤ rhoShiftPaper θ js) (G : K → K) (hG : RegAt0 G)
    (hGΨ : ∀ u : K, Admissible (Function.update w n u⁻¹) M →
      u ^ (rhoShiftPaper θ js - k) * psiHead (Function.update w n u⁻¹) M (k + 1) θ = G u) :
    G 0 = hBlock w M n k θ js ord' 0 := by
  classical
  rw [← orderF_zero w M n k θ js ord ord' hpos]
  refine RegAt0.zero_eq_of_eq_off hG (regAt0_orderF w M n k θ js ord ord') (badSet w M n)
    fun u hu => ?_
  have hadm₂ := admissible_update_inv hn hadm hu
  rw [← hGΨ u hadm₂, order_identity_update w M hn k θ ord ord' js hord hord' hcomp harg hpos hadm₂]

/-! ## The corollary -/

/-- **`cor:branch`, existence half** (`.tex` L427–L437, Q559, Clio 2026-10-23). With `r = k+1`,
`m = rhoShiftPaper θ` pairwise distinct, `js` its argmax, and `m_{js} ≥ 0`, there is a function
`F` regular at `u = 0` such that `u^{m_{js}−k} Ψ^C_{(1^r),θ}(M)(w[n ↦ u⁻¹]) = F(u)` at every
admissible `u`, and `F(0) = (−1)^{k+js} Ψ^C_{(1^k),θ̂}(M ∖ {n})(w)`. -/
theorem cor_branch_exists (w : ι → K) (M : Finset ι) {n : ι} (hn : n ∈ M) (k : ℕ)
    (θ : Fin (k + 1) → ℤ) (js : Fin (k + 1)) (hadm : Admissible w (M.erase n))
    (hinj : Function.Injective (rhoShiftPaper θ))
    (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) (hpos : 0 ≤ rhoShiftPaper θ js) :
    ∃ F : K → K, RegAt0 F ∧
      F 0 = (-1) ^ (k + js : ℕ) * psiHead w (M.erase n) k (thetaHat θ js) ∧
      ∀ u : K, Admissible (Function.update w n u⁻¹) M →
        u ^ (rhoShiftPaper θ js - k) * psiHead (Function.update w n u⁻¹) M (k + 1) θ = F u := by
  haveI : Nonempty ι := ⟨n⟩
  have hmax : ∀ j, j ≠ js → rhoShiftPaper θ j < rhoShiftPaper θ js :=
    fun j hj => lt_of_le_of_ne (harg j) fun h => hj (hinj h)
  obtain ⟨ord', hord'⟩ := exists_ordOK (M.erase n) k
  obtain ⟨ord₀, hord₀⟩ := exists_ordOK M (k + 1)
  have hord := glueOrd_ordOK M n ord' ord₀ hord' hord₀
  have hcomp := glueOrd_compat M n ord' ord₀
  refine ⟨orderF w M n k θ js (glueOrd n ord' ord₀) ord', regAt0_orderF _ _ _ _ _ _ _ _, ?_,
    fun u hadm₂ => order_identity_update w M hn k θ _ ord' js hord hord' hcomp harg hpos hadm₂⟩
  rw [orderF_zero w M n k θ js _ ord' hpos, hBlock_zero' w M n k θ js ord' hadm hord' hmax]

/-- **`cor:branch`** (`.tex` L427–L437, Q559, Clio 2026-10-23), as a limit. Over an infinite
field, **every** `G` regular at `u = 0` that agrees with `u^{m_{js}−k} Ψ^C_{(1^r),θ}(M)` at
`w_n = u⁻¹` (at the admissible `u`) has
`G(0) = (−1)^{k+js} Ψ^C_{(1^k),θ̂}(M ∖ {n})`. So "`lim_{w_n→∞} w_n^{−(m*−r+1)} Ψ`" is
well defined and equals the paper's value. -/
theorem cor_branch [Infinite K] (w : ι → K) (M : Finset ι) {n : ι} (hn : n ∈ M) (k : ℕ)
    (θ : Fin (k + 1) → ℤ) (js : Fin (k + 1)) (hadm : Admissible w (M.erase n))
    (hinj : Function.Injective (rhoShiftPaper θ))
    (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) (hpos : 0 ≤ rhoShiftPaper θ js)
    (G : K → K) (hG : RegAt0 G)
    (hGΨ : ∀ u : K, Admissible (Function.update w n u⁻¹) M →
      u ^ (rhoShiftPaper θ js - k) * psiHead (Function.update w n u⁻¹) M (k + 1) θ = G u) :
    G 0 = (-1) ^ (k + js : ℕ) * psiHead w (M.erase n) k (thetaHat θ js) := by
  classical
  obtain ⟨F, hF, hF0, hFΨ⟩ := cor_branch_exists w M hn k θ js hadm hinj harg hpos
  rw [← hF0]
  exact RegAt0.zero_eq_of_eq_off hG hF (badSet w M n) fun u hu => by
    have hadm₂ := admissible_update_inv hn hadm hu
    rw [← hGΨ u hadm₂, hFΨ u hadm₂]

/-! ## Paper-convention instance: a concrete value with no existential

`M = {0,1}`, `n = 1`, `w_0 = 2`, `θ = (0,0)`, so `m = (0,1)` and the argmax is `js = 1`
(the paper's `j* = 2`). The exponent is `m* − r + 1 = 0`, the sign is `(−1)^{2+2} = +1` and
`θ̂ = (0)`. So the limit is `Ψ^C_{(1),(0)}({2}) = 1 − 1/4 = 3/4`. An independent SymPy check
(`limit` of the head-injection sum `eq:Psidef`, not using this file) also gives `3/4`. -/

/-- The value `F(0) = H(0)` computed directly. -/
theorem inst_branch_value :
    orderF wI {0, 1} 1 1 ![0, 0] 1 (snocOrd 1 ordI') ordI' 0 = 3 / 4 := by
  rw [orderF_zero _ _ _ _ _ _ _ _ (by decide)]
  rw [show ordI' = fun _ _ => 0 from rfl, inst_hBlock_zero]
  simp [expo, rhoShiftPaper]

/-- `cor_branch` at the instance: every regular `G` agreeing with `Ψ_{(1,1),(0,0)}(2, u⁻¹)` has
`G(0) = 3/4`. -/
theorem inst_cor_branch (G : ℚ → ℚ) (hG : RegAt0 G)
    (hGΨ : ∀ u : ℚ, Admissible (Function.update wI 1 u⁻¹) {0, 1} →
      u ^ (rhoShiftPaper (![0, 0] : Fin 2 → ℤ) 1 - (1 : ℕ)) *
        psiHead (Function.update wI 1 u⁻¹) {0, 1} 2 ![0, 0] = G u) :
    G 0 = 3 / 4 := by
  rw [cor_branch wI {0, 1} (by decide) 1 ![0, 0] 1
    (admissible_mono (Finset.erase_subset 1 _) admI) (by rw [paper_m_00]; decide) (by decide)
    (by decide) G hG hGΨ, inst_psiHead]
  simp [thetaHat, rhoShiftPaper]

/-! ## Lesions (brief §2): ask Lean for `False` from each lesioned statement

`CorBranchWith Pinj Parg sgn` is `cor_branch_exists` over `ℚ`, `ι = ℕ`. Distinctness is weakened
to `Pinj ∨ _`, the argmax hypothesis to `Parg ∨ _`, and the stated value is multiplied by `sgn`.
Every refutation runs on BlockA's instance `M = {0,1}`, `n = 1`, `w = (2,3)`. There all
non-lesioned hypotheses are **discharged**, so the refutation is of the lesioned *statement*.
The mechanism is the uniqueness lemma: the claimed `F` and the true `orderF` must agree at `0`. -/

/-- `cor_branch_exists` with hypotheses weakened and the value scaled by `sgn`. -/
def CorBranchWith (Pinj Parg : Prop) (sgn : ℚ) : Prop :=
  ∀ (w : ℕ → ℚ) (M : Finset ℕ) (n k : ℕ) (θ : Fin (k + 1) → ℤ) (js : Fin (k + 1)), n ∈ M →
    Admissible w (M.erase n) → (Pinj ∨ Function.Injective (rhoShiftPaper θ)) →
    (Parg ∨ ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) → 0 ≤ rhoShiftPaper θ js →
    ∃ F : ℚ → ℚ, RegAt0 F ∧
      F 0 = sgn * ((-1) ^ (k + js : ℕ) * psiHead w (M.erase n) k (thetaHat θ js)) ∧
      ∀ u : ℚ, Admissible (Function.update w n u⁻¹) M →
        u ^ (rhoShiftPaper θ js - k) * psiHead (Function.update w n u⁻¹) M (k + 1) θ = F u

/-- Positive control: with nothing dropped and `sgn = 1`, this **is** `cor_branch_exists`. -/
theorem corBranchWith_control : CorBranchWith False False 1 :=
  fun w M n k θ js hn hadm hi ha hp => by
    simpa only [one_mul] using
      cor_branch_exists w M hn k θ js hadm (hi.resolve_left id) (ha.resolve_left id) hp

theorem admI' : Admissible wI (({0, 1} : Finset ℕ).erase 1) :=
  admissible_mono (Finset.erase_subset 1 _) admI

/-- On the instance, a regular `F` that agrees at the true argmax `js` has `F(0) = H(0)`, the
closed form of `inst_hBlock_zero`. -/
theorem inst_limit (θ : Fin 2 → ℤ) (js : Fin 2)
    (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) (hpos : 0 ≤ rhoShiftPaper θ js)
    (F : ℚ → ℚ) (hF : RegAt0 F)
    (hFΨ : ∀ u : ℚ, Admissible (Function.update wI 1 u⁻¹) {0, 1} →
      u ^ (rhoShiftPaper θ js - (1 : ℕ)) * psiHead (Function.update wI 1 u⁻¹) {0, 1} 2 θ = F u) :
    F 0 = 3 / 4 * (-(0 : ℚ) ^ expo θ js 0 * 2 ^ rhoShiftPaper θ 1 +
        (0 : ℚ) ^ expo θ js 1 * 2 ^ rhoShiftPaper θ 0) := by
  rw [limit_eq_orderF_zero wI {0, 1} (by decide) 1 θ (snocOrd 1 ordI') ordI' js admI' ordI_ok
    ordI'_ok (snocOrd_compat _ _ _) harg hpos F hF hFΨ]
  exact inst_hBlock_zero θ js

/-- **L-dist (drop distinctness): refutable** at `θ = (1,0)`, `m = (1,1)`, `js = 0` (an argmax).
The true limit is `H(0) = 0`, because the tied Laplace terms cancel. The claimed value is `−3/2`. -/
theorem lesion_dist_refutable : ¬ CorBranchWith True False 1 := by
  intro H
  obtain ⟨F, hF, hF0, hFΨ⟩ := H wI {0, 1} 1 1 ![1, 0] 0 (by decide) admI' (Or.inl trivial)
    (Or.inr (by decide)) (by decide)
  have h := inst_limit ![1, 0] 0 (by decide) (by decide) F hF hFΨ
  rw [hF0, inst_psiHead] at h
  simp [expo, rhoShiftPaper, thetaHat] at h

/-- **L-sign (sign `(−1)^{k+js}` flipped): refutable** at `θ = (2,0)`, `m = (2,1)`, `js = 0`.
The true limit is `−3/2` and the flipped claim is `+3/2`. -/
theorem lesion_sign_refutable : ¬ CorBranchWith False False (-1) := by
  intro H
  obtain ⟨F, hF, hF0, hFΨ⟩ := H wI {0, 1} 1 1 ![2, 0] 0 (by decide) admI'
    (Or.inr (by decide)) (Or.inr (by decide)) (by decide)
  have h := inst_limit ![2, 0] 0 (by decide) (by decide) F hF hFΨ
  rw [hF0, inst_psiHead] at h
  simp [expo, rhoShiftPaper, thetaHat] at h
  all_goals norm_num at h

/-- **L-arg (`js` need not be an argmax): refutable** at `θ = (0,0)`, `m = (0,1)`, `js = 0`.
A regular `F` with `u^{−1} Ψ = F(u)` would make `u·F(u)` a regular function agreeing with the
true `u^0 Ψ` (argmax `1`), so `0 = 0·F(0) = H_{js=1}(0) = 3/4`. Here no claimed value is even
needed: the exponent alone is impossible. -/
theorem lesion_arg_refutable : ¬ CorBranchWith False True 1 := by
  intro H
  obtain ⟨F, hF, -, hFΨ⟩ := H wI {0, 1} 1 1 ![0, 0] 0 (by decide) admI'
    (Or.inr (by rw [paper_m_00]; decide)) (Or.inl trivial) (by decide)
  have h := inst_limit ![0, 0] 1 (by decide) (by decide) (fun u => u * F u)
    (regAt0_id.mul hF) fun u hadm => by
      have hu : u ≠ 0 := by
        intro h0; apply hadm.1 1 (by decide); simp [h0]
      change _ = u * F u
      rw [← hFΨ u hadm]
      norm_num [rhoShiftPaper]
      field_simp
  simp [expo, rhoShiftPaper] at h
  all_goals norm_num at h

/-- **L-dist ∧ L-arg, the pair: refutable** a fortiori. -/
theorem lesion_pair_refutable : ¬ CorBranchWith True True 1 := fun H =>
  lesion_arg_refutable fun w M n k θ js hn hadm _ _ hp =>
    H w M n k θ js hn hadm (Or.inl trivial) (Or.inl trivial) hp

end TworowD4Kernel.CorBranch
