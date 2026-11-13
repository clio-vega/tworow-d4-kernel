/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.BlockA
import Mathlib.Algebra.Polynomial.Roots

/-!
# Q559 `lem:order` (= `prop:caseA`): the order comparison

Formalises `prop:caseA` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
L284–L302 (Clio, 2026-10-23), named `lem:order` in the 2026-11-13 LEAN brief:

> Let `r ≥ 1`, `m` pairwise distinct, `max_j m_j ≥ 0`, `Ψ^C_{(1^{r−1}),θ̂}(M') ≠ 0`.
> Then `Ψ^C_{(1^r),θ}(M) ≠ 0`.

## Encoding decision (Step 0, written before tactics)

`lem_blockA`/`lem_blockB` are pointwise identities at `w_n = u⁻¹` in an abstract field.
Combined with `psiHead_split` they give, for every admissible `u`,
`u^{m*−k} Ψ = F(u) := H(u) + (−1)^{k+1} u^{m*+1} G(u)`.

**Route R2 (elementary), chosen.** The reasons: both block files already read regularity off
denominators `1 − u x`, so R2 only has to *state* that reading. R1 would retype `Bfactor` over
`Frac ℚ[w]` or `LaurentSeries`. The regularity is now a **theorem**, not a reading:
`RegAt0 f := ∃ P Q : K[X], Q(0) ≠ 0 ∧ ∀ u, Q(u) ≠ 0 → f(u)·Q(u) = P(u)`.
`RegAt0` is closed under constants, `u`, `+`, `*`, `/const`, `^n`, finite `∑`/`∏`, and division by a
polynomial that is nonzero at `0` (`regAt0_*`). `hBlock`, `gBlock` and hence `F` are `RegAt0`.
The nonvanishing principle is `RegAt0.exists_ne`: if `f(0) ≠ 0` and `K` is infinite, then `f` is
nonzero off any finite set. Its proof is that `P(0) = f(0)Q(0) ≠ 0`, so `P ≠ 0`, and
`P.roots`, `Q.roots` are finite (`Polynomial.mem_roots`).

**What "`Ψ ≠ 0`" means here.** Over an infinite field `K`: **some admissible point** has `Ψ ≠ 0`.
Concretely, given `w` admissible on `M` with `Ψ(M', θ̂)(w) ≠ 0`, the conclusion is that moving `w_n`
alone gives an admissible `w₂` with `Ψ(M, θ)(w₂) ≠ 0`. For `K = ℚ` this is "not identically zero
as a rational function". The pointwise IH form is the one an induction on `r` can consume.

The gap `m* + 1 ≥ 1` (from `m* ≥ 0`) is where the hypothesis `max m ≥ 0` enters. It makes the
`G` term vanish at `u = 0` (`F_zero`).
-/

namespace TworowD4Kernel.LemOrder

open Finset Polynomial
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.RhoShiftVanishing
open TworowD4Kernel.ReciprocalRestriction
open TworowD4Kernel.AlternantExpansion
open TworowD4Kernel.BlockB
open TworowD4Kernel.BlockA

variable {K : Type*} [Field K]

/-! ## Regularity at `u = 0`, as a predicate with closure lemmas -/

/-- `f` agrees with `P/Q` wherever `Q ≠ 0`, and `Q(0) ≠ 0`: `f` is a rational function of `u`
regular at `0`, **and its value at `0` is the value of that rational function** (`u = 0` is
not exempted). -/
def RegAt0 (f : K → K) : Prop :=
  ∃ P Q : K[X], Q.eval 0 ≠ 0 ∧ ∀ u, Q.eval u ≠ 0 → f u * Q.eval u = P.eval u

theorem regAt0_const (c : K) : RegAt0 fun _ : K => c :=
  ⟨C c, 1, by simp, fun u _ => by simp⟩

theorem regAt0_id : RegAt0 fun u : K => u :=
  ⟨X, 1, by simp, fun u _ => by simp⟩

theorem RegAt0.add {f g : K → K} (hf : RegAt0 f) (hg : RegAt0 g) : RegAt0 fun u => f u + g u := by
  obtain ⟨P, Q, hQ, hf⟩ := hf
  obtain ⟨P', Q', hQ', hg⟩ := hg
  refine ⟨P * Q' + P' * Q, Q * Q', by simp [hQ, hQ'], fun u hu => ?_⟩
  simp only [eval_mul, eval_add, ne_eq, mul_eq_zero, not_or] at hu ⊢
  rw [← hf u hu.1, ← hg u hu.2]; ring

theorem RegAt0.mul {f g : K → K} (hf : RegAt0 f) (hg : RegAt0 g) : RegAt0 fun u => f u * g u := by
  obtain ⟨P, Q, hQ, hf⟩ := hf
  obtain ⟨P', Q', hQ', hg⟩ := hg
  refine ⟨P * P', Q * Q', by simp [hQ, hQ'], fun u hu => ?_⟩
  simp only [eval_mul, ne_eq, mul_eq_zero, not_or] at hu ⊢
  rw [← hf u hu.1, ← hg u hu.2]; ring

theorem RegAt0.sub {f g : K → K} (hf : RegAt0 f) (hg : RegAt0 g) : RegAt0 fun u => f u - g u := by
  have := hf.add ((regAt0_const (-1)).mul hg)
  simpa [sub_eq_add_neg] using this

theorem RegAt0.pow {f : K → K} (hf : RegAt0 f) (e : ℕ) : RegAt0 fun u => f u ^ e := by
  induction e with
  | zero => simpa using regAt0_const (1 : K)
  | succ e ih => simpa [pow_succ] using ih.mul hf

theorem RegAt0.div_const {f : K → K} (hf : RegAt0 f) (c : K) : RegAt0 fun u => f u / c := by
  simpa [div_eq_mul_inv] using hf.mul (regAt0_const c⁻¹)

/-- Division by a polynomial nonzero at `0` (the denominators `1 − u x`). -/
theorem RegAt0.div_poly {f : K → K} (hf : RegAt0 f) (R : K[X]) (hR : R.eval 0 ≠ 0) :
    RegAt0 fun u => f u / R.eval u := by
  obtain ⟨P, Q, hQ, hf⟩ := hf
  refine ⟨P, Q * R, by simp [hQ, hR], fun u hu => ?_⟩
  simp only [eval_mul, ne_eq, mul_eq_zero, not_or] at hu ⊢
  rw [← hf u hu.1]
  have := hu.2
  field_simp

theorem regAt0_sum {α : Type*} (s : Finset α) (g : α → K → K) (h : ∀ a ∈ s, RegAt0 (g a)) :
    RegAt0 fun u => ∑ a ∈ s, g a u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regAt0_const (0 : K)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (mem_insert_self a s)).add (ih fun b hb => h b (mem_insert_of_mem hb))

theorem regAt0_prod {α : Type*} (s : Finset α) (g : α → K → K) (h : ∀ a ∈ s, RegAt0 (g a)) :
    RegAt0 fun u => ∏ a ∈ s, g a u := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regAt0_const (1 : K)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun b hb => h b (mem_insert_of_mem hb))

/-- `u ↦ 1 − u x` is a polynomial nonzero at `0`. -/
theorem eval_one_sub_X_mul (x u : K) : (1 - X * C x : K[X]).eval u = 1 - u * x := by
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]

theorem eval_one_sub_mul_X (x u : K) : (1 - C x * X : K[X]).eval u = 1 - x * u := by
  simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X]

/-- **The nonvanishing principle.** Regular at `0` with nonzero value there ⇒ nonzero off any
finite set, over an infinite field. -/
theorem RegAt0.exists_ne [Infinite K] {f : K → K} (hf : RegAt0 f) (h0 : f 0 ≠ 0) (S : Finset K) :
    ∃ u ∉ S, f u ≠ 0 := by
  classical
  obtain ⟨P, Q, hQ, hfPQ⟩ := hf
  have hP0 : P.eval 0 ≠ 0 := by rw [← hfPQ 0 hQ]; exact mul_ne_zero h0 hQ
  have hP : P ≠ 0 := fun h => hP0 (by simp [h])
  have hQ' : Q ≠ 0 := fun h => hQ (by simp [h])
  obtain ⟨u, hu⟩ := Infinite.exists_notMem_finset (S ∪ P.roots.toFinset ∪ Q.roots.toFinset)
  simp only [Finset.mem_union, Multiset.mem_toFinset, mem_roots hP, mem_roots hQ', IsRoot.def,
    not_or] at hu
  obtain ⟨⟨huS, huP⟩, huQ⟩ := hu
  refine ⟨u, huS, fun h => huP ?_⟩
  rw [← hfPQ u huQ, h, zero_mul]


theorem RegAt0.congr {f g : K → K} (h : ∀ u, f u = g u) (hg : RegAt0 g) : RegAt0 f := by
  have : f = g := funext h
  rwa [this]

/-! ## `H` and `G` are regular at `0` (a theorem, replacing the blocks' "read off the definition") -/

variable {ι : Type*} [DecidableEq ι]

theorem regAt0_betaReg (w : ι → K) (M' T' : Finset ι) : RegAt0 fun u => betaReg w M' T' u := by
  simp only [betaReg]
  refine (((regAt0_const 1).sub (regAt0_id.pow 2)).mul
    (regAt0_prod _ _ fun i _ => (regAt0_const 1).sub (regAt0_id.div_const _))).mul
    (regAt0_prod _ _ fun t _ => ?_)
  refine RegAt0.congr (fun u => ?_)
    (((regAt0_const 1).sub (regAt0_id.div_const (w t))).div_poly (1 - C (w t) * X) (by simp))
  simp only [eval_one_sub_mul_X]

omit [DecidableEq ι] in
theorem regAt0_lapReg (w : ι → K) {k : ℕ} (ord' : Finset ι → Fin k → ι) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (T' : Finset ι) : RegAt0 fun u => lapReg w ord' θ js T' u := by
  simp only [lapReg]
  exact regAt0_sum _ _ fun j _ => ((regAt0_const _).mul (regAt0_id.pow _)).mul (regAt0_const _)

/-- **`H` is regular at `u = 0`.** -/
theorem regAt0_hBlock (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord' : Finset ι → Fin k → ι) :
    RegAt0 fun u => hBlock w M n k θ js ord' u := by
  simp only [hBlock]
  refine regAt0_sum _ _ fun T' _ => ?_
  refine RegAt0.congr (fun u => ?_)
    ((((regAt0_const (Bfactor w (M.erase n) T')).mul (regAt0_betaReg w (M.erase n) T')).mul (regAt0_lapReg w ord' θ js T')).div_const
      (vand fun i => w (ord' T' i)) |>.div_poly (∏ i, (1 - X * C (w (ord' T' i))))
      (by simp [eval_prod]))
  simp only [eval_prod, eval_one_sub_X_mul, div_mul_eq_div_div]

theorem regAt0_regFactor (x : K) : RegAt0 fun u => regFactor u x := by
  refine RegAt0.congr (fun u => ?_)
    (((regAt0_const 1).sub (regAt0_id.div_const x)).div_poly (1 - X * C x) (by simp))
  simp only [regFactor, eval_one_sub_X_mul]

/-- **`G` is regular at `u = 0`.** -/
theorem regAt0_gBlock (w : ι → K) (M : Finset ι) (n : ι) (r : ℕ) (θ : Fin r → ℤ)
    (ord : Finset ι → Fin r → ι) : RegAt0 fun u => gBlock w M n r θ ord u := by
  simp only [gBlock]
  exact regAt0_sum _ _ fun T _ =>
    (((regAt0_prod _ _ fun i _ => regAt0_regFactor (w i)).mul (regAt0_const _)).mul
      (regAt0_const _)).mul (regAt0_const _)

/-! ## `H`, `G` see only `w` on `M' = M ∖ {n}` -/

theorem Bfactor_congr {w w₂ : ι → K} {M T : Finset ι} (hT : T ⊆ M) (h : ∀ i ∈ M, w i = w₂ i) :
    Bfactor w M T = Bfactor w₂ M T := by
  unfold Bfactor diagFactor pairFactor crossFactor
  rw [Finset.prod_congr rfl fun i hi => congrArg (fun x => 1 - x⁻¹ ^ 2) (h i (hT hi)),
    Finset.prod_congr rfl fun p hp => congrArg (fun x => 1 - x⁻¹)
      (Finset.prod_congr rfl fun i hi => h i (hT ((Finset.mem_powersetCard.1 hp).1 hi))),
    Finset.prod_congr rfl fun t ht => Finset.prod_congr rfl fun i hi => by
      rw [h t (Finset.sdiff_subset ht), h i (hT hi)]]

theorem hBlock_congr {w w₂ : ι → K} {M : Finset ι} {n : ι} {k : ℕ} (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) {ord' : Finset ι → Fin k → ι} (hord' : OrdOK (M.erase n) k ord')
    (h : ∀ i ∈ M.erase n, w i = w₂ i) (u : K) :
    hBlock w M n k θ js ord' u = hBlock w₂ M n k θ js ord' u := by
  unfold hBlock
  refine Finset.sum_congr rfl fun T' hT' => ?_
  have hTM := (Finset.mem_powersetCard.1 hT').1
  have hm : ∀ i, w (ord' T' i) = w₂ (ord' T' i) := fun i => h _ (hTM ((hord' T' hT').2 i))
  have hB := Bfactor_congr hTM h
  have hβ : betaReg w (M.erase n) T' u = betaReg w₂ (M.erase n) T' u := by
    unfold betaReg
    rw [Finset.prod_congr rfl fun i hi => congrArg (fun x => 1 - u / x) (h i (hTM hi)),
      Finset.prod_congr rfl fun t ht => congrArg (fun x => (1 - u / x) / (1 - x * u))
        (h t (Finset.sdiff_subset ht))]
  have hL : lapReg w ord' θ js T' u = lapReg w₂ ord' θ js T' u := by
    unfold lapReg minorD; simp only [hm]
  simp only [hB, hβ, hL, hm]

theorem gBlock_congr {w w₂ : ι → K} {M : Finset ι} {n : ι} {r : ℕ} (θ : Fin r → ℤ)
    {ord : Finset ι → Fin r → ι} (hord : OrdOK (M.erase n) r ord)
    (h : ∀ i ∈ M.erase n, w i = w₂ i) (u : K) :
    gBlock w M n r θ ord u = gBlock w₂ M n r θ ord u := by
  unfold gBlock altPaper
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTM := (Finset.mem_powersetCard.1 hT).1
  have hm : ∀ i, w (ord T i) = w₂ (ord T i) := fun i => h _ (hTM ((hord T hT).2 i))
  rw [Bfactor_congr hTM h, Finset.prod_congr rfl fun i hi => congrArg (regFactor u) (h i (hTM hi)),
    Finset.prod_congr rfl fun i hi => h i (hTM hi)]
  simp only [hm]


/-! ## The order comparison -/

/-- `F(u) = H(u) + (−1)^{k+1} u^{m*+1} G(u)`, with the exponent `m*+1` as a natural number. -/
noncomputable def orderF (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι) (u : K) :
    K :=
  hBlock w M n k θ js ord' u +
    (-1) ^ (k + 1) * u ^ (rhoShiftPaper θ js + 1).toNat * gBlock w M n (k + 1) θ ord u

theorem regAt0_orderF (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι) :
    RegAt0 fun u => orderF w M n k θ js ord ord' u := by
  simp only [orderF]
  exact (regAt0_hBlock w M n k θ js ord').add
    (((regAt0_const _).mul (regAt0_id.pow _)).mul (regAt0_gBlock w M n (k + 1) θ ord))

/-- **The identity** `u^{m*−k} Ψ = F(u)` at `w_n = u⁻¹`
(`psiHead_split` + `lem:blockA` (I) + `lem:blockB` (I)). The hypothesis `m* ≥ 0` is used only to write
`u^{m*+1}` with a natural exponent. -/
theorem psiHead_order_identity (w : ι → K) (M : Finset ι) {n : ι} (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι) (js : Fin (k + 1))
    (hadm : Admissible w M) (hn : n ∈ M) (hord : OrdOK M (k + 1) ord)
    (hcomp : SnocCompat M n k ord ord') (hle : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js)
    (hpos : 0 ≤ rhoShiftPaper θ js) {u : K} (hwn : w n = u⁻¹) :
    u ^ (rhoShiftPaper θ js - k) * psiHead w M (k + 1) θ = orderF w M n k θ js ord ord' u := by
  have hu : u ≠ 0 := by
    intro h; apply hadm.1 n hn; rw [hwn, h, inv_zero]
  have h1 := psiPlus_eq w M k θ ord ord' js hadm hn hcomp hle hwn
  have h2 := psiMinus_eq w M (k + 1) θ ord hadm hn hwn
  have h3 : u ^ (rhoShiftPaper θ js - k) * u ^ (k + 1) = u ^ (rhoShiftPaper θ js + 1).toNat := by
    rw [← zpow_natCast u (k + 1), ← zpow_natCast u, ← zpow_add₀ hu]
    congr 1; push_cast; omega
  rw [psiHead_split w M n (k + 1) θ ord hadm hord, orderF, mul_add, h1, h2, neg_pow]
  linear_combination (-1) ^ (k + 1) * gBlock w M n (k + 1) θ ord u * h3

/-- **Where `max m ≥ 0` enters:** the `G`-term carries `u^{m*+1}`, `m*+1 ≥ 1`, so vanishes at `0`. -/
theorem orderF_zero (w : ι → K) (M : Finset ι) (n : ι) (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (js : Fin (k + 1)) (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι)
    (hpos : 0 ≤ rhoShiftPaper θ js) :
    orderF w M n k θ js ord ord' 0 = hBlock w M n k θ js ord' 0 := by
  have he : (rhoShiftPaper θ js + 1).toNat ≠ 0 := by omega
  simp [orderF, zero_pow he]

/-- **`lem:order` = `prop:caseA`** (`.tex` L284–L302, Q559, Clio 2026-10-23).
`r = k+1`, `m = rhoShiftPaper θ` pairwise distinct, `j*` its argmax, `m_{j*} ≥ 0`, `n ∈ M` the
largest index (`SnocCompat`). If `w` is admissible on `M` and `Ψ^C_{(1^k),θ̂}(M')(w) ≠ 0` (the
inductive hypothesis, pointwise), then moving `w_n` alone gives an admissible point where
`Ψ^C_{(1^{k+1}),θ}(M) ≠ 0`. Over an infinite field. -/
theorem lem_order [Infinite K] (w : ι → K) (M : Finset ι) {n : ι} (k : ℕ) (θ : Fin (k + 1) → ℤ)
    (ord : Finset ι → Fin (k + 1) → ι) (ord' : Finset ι → Fin k → ι) (js : Fin (k + 1))
    (hadm : Admissible w M) (hn : n ∈ M) (hord : OrdOK M (k + 1) ord)
    (hord' : OrdOK (M.erase n) k ord') (hcomp : SnocCompat M n k ord ord')
    (hinj : Function.Injective (rhoShiftPaper θ))
    (harg : ∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) (hpos : 0 ≤ rhoShiftPaper θ js)
    (hIH : psiHead w (M.erase n) k (thetaHat θ js) ≠ 0) :
    ∃ v : K, Admissible (Function.update w n v) M ∧
      psiHead (Function.update w n v) M (k + 1) θ ≠ 0 := by
  classical
  have hmax : ∀ j, j ≠ js → rhoShiftPaper θ j < rhoShiftPaper θ js :=
    fun j hj => lt_of_le_of_ne (harg j) fun h => hj (hinj h)
  -- `F(0) = H(0) = ±Ψ(M', θ̂) ≠ 0`
  have hF0 : orderF w M n k θ js ord ord' 0 ≠ 0 := by
    rw [orderF_zero w M n k θ js ord ord' hpos, hBlock_zero w M n k θ js ord' hadm hord' hmax]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hIH
  -- the finitely many inadmissible `u`
  obtain ⟨u, huS, hFu⟩ := (regAt0_orderF w M n k θ js ord ord').exists_ne hF0
    (insert 0 ((M.erase n).image fun i => (w i)⁻¹))
  simp only [Finset.mem_insert, Finset.mem_image, not_or, not_exists, not_and] at huS
  obtain ⟨hu0, huw⟩ := huS
  set w₂ := Function.update w n u⁻¹ with hw₂
  have hagree : ∀ i ∈ M.erase n, w i = w₂ i := fun i hi => by
    rw [hw₂, Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have hne : ∀ i ∈ M.erase n, u⁻¹ ≠ w i := fun i hi h => huw i hi (by rw [← h, inv_inv])
  have hadm₂ : Admissible w₂ M := by
    refine ⟨fun t ht => ?_, fun s hs t ht hst => ?_⟩
    · by_cases htn : t = n
      · subst htn; simpa [hw₂] using hu0
      · rw [← hagree t (Finset.mem_erase.2 ⟨htn, ht⟩)]; exact hadm.1 t ht
    · by_cases hsn : s = n
      · subst hsn
        have htm : t ∈ M.erase s := Finset.mem_erase.2 ⟨Ne.symm hst, ht⟩
        rw [← hagree t htm]; simpa [hw₂] using hne t htm
      · have hsm : s ∈ M.erase n := Finset.mem_erase.2 ⟨hsn, hs⟩
        by_cases htn : t = n
        · subst htn; rw [← hagree s hsm]; simpa [hw₂] using (hne s hsm).symm
        · rw [← hagree s hsm, ← hagree t (Finset.mem_erase.2 ⟨htn, ht⟩)]
          exact hadm.2 s hs t ht hst
  refine ⟨u⁻¹, hadm₂, fun hΨ => hFu ?_⟩
  have hid := psiHead_order_identity w₂ M k θ ord ord' js hadm₂ hn hord hcomp harg hpos
    (u := u) (by simp [hw₂])
  have hord1 := OrdOK.mono (Finset.erase_subset n M) hord
  rw [hΨ, mul_zero, orderF, ← hBlock_congr θ js hord' hagree, ← gBlock_congr θ hord1 hagree] at hid
  rw [orderF, ← hid]


/-! ## Lesions (brief): ask Lean for `False` from each lesioned statement

The instance is blockA's: `M = {0,1}`, `n = 1`, `k = 1` (`r = 2`), `ord' ≡ 0`,
`ord = snocOrd 1 ord'`. All the non-lesioned hypotheses are **discharged** on it, so each
refutation refutes the lesioned *lemma*, not a specialisation of it. -/

/-- `lem_order` with the hypothesis `hIH` and/or `hinj` replaced by `P`, over `ℚ`, `ι = ℕ`. -/
def LemOrderWith (Pinj Pih : Prop) : Prop :=
  ∀ (w : ℕ → ℚ) (M : Finset ℕ) (n k : ℕ) (θ : Fin (k + 1) → ℤ)
    (ord : Finset ℕ → Fin (k + 1) → ℕ) (ord' : Finset ℕ → Fin k → ℕ) (js : Fin (k + 1)),
    Admissible w M → n ∈ M → OrdOK M (k + 1) ord → OrdOK (M.erase n) k ord' →
    SnocCompat M n k ord ord' →
    (Pinj ∨ Function.Injective (rhoShiftPaper θ)) →
    (∀ j, rhoShiftPaper θ j ≤ rhoShiftPaper θ js) → 0 ≤ rhoShiftPaper θ js →
    (Pih ∨ psiHead w (M.erase n) k (thetaHat θ js) ≠ 0) →
    ∃ v : ℚ, Admissible (Function.update w n v) M ∧
      psiHead (Function.update w n v) M (k + 1) θ ≠ 0

/-- Positive control: with nothing dropped, `LemOrderWith False False` **is** `lem_order`. -/
theorem lemOrderWith_control : LemOrderWith False False :=
  fun w M _n k θ ord ord' js hadm hn hord hord' hcomp hinj harg hpos hIH =>
    lem_order w M k θ ord ord' js hadm hn hord hord' hcomp (hinj.resolve_left id) harg hpos
      (hIH.resolve_left id)

def ordI' : Finset ℕ → Fin 1 → ℕ := fun _ _ => 0

theorem ordI'_ok : OrdOK (({0, 1} : Finset ℕ).erase 1) 1 ordI' := by
  have e3 : ({0, 1} : Finset ℕ).erase 1 = {0} := by decide
  rw [e3]
  intro T hT
  have : T = {0} := by
    obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 hT
    exact Finset.eq_of_subset_of_card_le h1 (by simp [h2])
  subst this
  exact ⟨fun a b _ => Subsingleton.elim a b, fun _ => by simp [ordI']⟩

theorem ordI_ok : OrdOK ({0, 1} : Finset ℕ) 2 (snocOrd 1 ordI') := by
  intro T hT
  refine snocOrd_ordOK {0, 1} 1 ordI' ordI'_ok T (Finset.mem_filter.2 ⟨hT, ?_⟩)
  have : T = {0, 1} := by
    obtain ⟨h1, h2⟩ := Finset.mem_powersetCard.1 hT
    exact Finset.eq_of_subset_of_card_le h1 (by simp [h2])
  simp [this]

theorem admI : Admissible wI ({0, 1} : Finset ℕ) := ⟨by simp [wI], by simp [wI]⟩

/-- **L-IH (drop `Ψ(M',θ̂)(w) ≠ 0`): refutable.** At `w = (1, 3)`, `θ = (2,0)` (`m = (2,1)`,
distinct, `j* = 0`, `m* = 2 ≥ 0`): `w_0 = 1` kills the diagonal factor `1 − w_0^{−2}` in the only
`T = {0,1}`, so `Ψ(M)` vanishes for **every** `w_n`. The point is exactly outside `hIH`, which
reads `(1 − 1)·1^{θ̂} = 0` there. -/
theorem lesion_IH_refutable : ¬ LemOrderWith False True := by
  intro H
  set w₁ : ℕ → ℚ := fun i => if i = 0 then 1 else 3
  obtain ⟨v, hadm, hne⟩ := H w₁ {0, 1} 1 1 ![2, 0] (snocOrd 1 ordI') ordI' 0
    ⟨by simp [w₁], by simp [w₁]⟩ (by simp) ordI_ok ordI'_ok (snocOrd_compat _ _ _)
    (Or.inr (by decide)) (by decide) (by decide) (Or.inl trivial)
  apply hne
  rw [thm_alt_paper _ _ 2 _ (snocOrd 1 ordI') hadm ordI_ok]
  have e : ({0, 1} : Finset ℕ).powersetCard 2 = {{0, 1}} := by decide
  rw [e, Finset.sum_singleton, Bfactor, Finset.prod_insert (by simp)]
  simp [diagFactor, w₁, Function.update]

/-- **L-dist (drop distinctness of `m`): refutable.** At `w = (2,3)`, `θ = (1,0)` (`m = (1,1)`,
`j* = 0` an argmax, `m* = 1 ≥ 0`): `hIH` **holds** (`Ψ(M',θ̂) = (3/4)·2 ≠ 0`), yet `Ψ(M) ≡ 0` by the
forward ρ-shift law (`psiHead_eq_zero_of_criterion`). -/
theorem lesion_dist_refutable : ¬ LemOrderWith True False := by
  intro H
  obtain ⟨v, hadm, hne⟩ := H wI {0, 1} 1 1 ![1, 0] (snocOrd 1 ordI') ordI' 0
    admI (by simp) ordI_ok ordI'_ok (snocOrd_compat _ _ _)
    (Or.inl trivial) (by decide) (by decide)
    (Or.inr (by rw [inst_psiHead]; simp [thetaHat, rhoShiftPaper]))
  exact hne (psiHead_eq_zero_of_criterion _ _ 2 _ (snocOrd 1 ordI') hadm ordI_ok
    (Or.inr ⟨0, 1, by decide, by decide⟩))

/-- **Pair (drop both): refutable**, a fortiori (`True ∨ _` is implied by every hypothesis). -/
theorem lesion_pair_refutable : ¬ LemOrderWith True True := fun H =>
  lesion_dist_refutable fun w M n k θ ord ord' js h1 h2 h3 h4 h5 _ h7 h8 _ =>
    H w M n k θ ord ord' js h1 h2 h3 h4 h5 (Or.inl trivial) h7 h8 (Or.inl trivial)

/-- **L-gap (drop `m* ≥ 0`), at the step it feeds: refutable.** Without `m* ≥ 0` the `G`-term
survives at `u = 0`. Instance `M = {0,1}`, `n = 1`, `k = 0` (`r = 1`), `θ = (−1)` (`m* = −1`):
`F(0) − H(0) = −G(0) = −Ψ(M', θ+1) = −3/4`. (As a *statement* `lem:order` without `m* ≥ 0` is not
refutable: `thm:main` covers `m* ≤ −1` through the reflection. The gap is load-bearing for **this
proof**, not for the truth.) -/
theorem lesion_gap_refutable :
    ¬ ∀ (θ : Fin 1 → ℤ) (ord : Finset ℕ → Fin 1 → ℕ), OrdOK ({0, 1} : Finset ℕ) 1 ord →
      orderF wI {0, 1} 1 0 θ 0 ord (fun _ => Fin.elim0) 0 =
        hBlock wI {0, 1} 1 0 θ 0 (fun _ => Fin.elim0) 0 := by
  intro H
  obtain ⟨ord, hord⟩ := exists_ordOK (ι := ℕ) ({0, 1} : Finset ℕ) 1
  have h := H ![-1] ord hord
  rw [orderF, add_eq_left, gBlock_zero wI _ 1 1 _ ord admI hord, inst_psiHead] at h
  norm_num [rhoShiftPaper] at h

end TworowD4Kernel.LemOrder
