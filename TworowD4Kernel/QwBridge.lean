/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.ThmMain
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.Algebra.Rat

/-!
# Q559: the `ℚ(w)` ↔ pointwise bridge

`thm:main` and `cor:criterion` of `projects/proofs/2026-10-23-Q559-vanishing-converse.tex`
speak of `Ψ^C_{(1^r),θ}(M)` **as an element of `ℚ(w_1,…,w_n)`**. `ThmMain` encodes this pointwise
(over an infinite field, at admissible points). This file supplies the bridge.

## Encoding

`ℚ(w) := FractionRing (MvPolynomial ι ℚ)`, and `Ψ ∈ ℚ(w)` is `eq:Psidef` **at the generic point**
`w_i ↦ X_i` (`psiQ`). This is literally the paper's object: the defining sum, computed in `ℚ(w)`.

## Route (scoped in `proofs/2026-11-14-lean-cor-branch.md`, "Scoping note")

`D := ∏_{i∈M} X_i · ∏_{s≠t ∈ M} (X_s − X_t)`. Every denominator of `eq:Psidef` divides `D`.
* `Spec x y` (relation): `x = a / D^k` in `ℚ(w)` and `y = a(w) / D(w)^k` in `K`, for one `a`.
  It is closed under the ring operations and under inverting a divisor of `D`; so
  `Spec (psiQ M r θ) (psiHead w M r θ)` at every admissible `w` (`spec_psiHead`).
  This is the "`eval` commutes with `Ψ` at admissible points" lemma of the plan.
* Pointwise ⇒ generic: `D·a` vanishes at every point (admissible: `Ψ(w) = 0`; inadmissible:
  `D(w) = 0`), so `MvPolynomial.funext` gives `D·a = 0`, hence `a = 0`.
* Generic ⇒ pointwise: `a/D^k = 0` in `ℚ(w)` gives `a = 0`, so `Ψ(w) = 0`.
-/

namespace TworowD4Kernel.QwBridge

-- The `Spec` closure lemmas share `hD hDw` via `include`; several use only one of them.
set_option linter.unusedSectionVars false

open Finset MvPolynomial
open TworowD4Kernel.BoundaryEmptyIndex
open TworowD4Kernel.ReciprocalPair
open TworowD4Kernel.ReciprocalRestriction
open TworowD4Kernel.ThmMain
open TworowD4Kernel.RhoShiftVanishing

variable {ι : Type*}

/-- `ℚ(w_i : i ∈ ι)`. -/
abbrev Qw (ι : Type*) := FractionRing (MvPolynomial ι ℚ)

/-- The generic point `w_i ↦ X_i` of `ℚ(w)`. -/
noncomputable def gen (i : ι) : Qw ι := algebraMap (MvPolynomial ι ℚ) (Qw ι) (X i)

/-- **`Ψ^C_{(1^r),θ}(M)` as an element of `ℚ(w)`**: `eq:Psidef` at the generic point. -/
noncomputable def psiQ [DecidableEq ι] (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) : Qw ι :=
  psiHead gen M r θ

/-- The common denominator `D = ∏_{i∈M} X_i · ∏_{(s,t) ∈ M², s≠t} (X_s − X_t)`. -/
noncomputable def denom (M : Finset ι) : MvPolynomial ι ℚ :=
  (∏ i ∈ M, X i) * ∏ p ∈ M.offDiag, (X p.1 - X p.2)

theorem denom_ne_zero (M : Finset ι) : denom M ≠ 0 := by
  refine mul_ne_zero (prod_ne_zero_iff.2 fun i _ => X_ne_zero i) (prod_ne_zero_iff.2 fun p hp => ?_)
  rw [sub_ne_zero]
  exact fun h => (mem_offDiag.1 hp).2.2 (X_injective h)

theorem X_dvd_denom {M : Finset ι} {i : ι} (hi : i ∈ M) : X i ∣ denom M :=
  dvd_mul_of_dvd_left (dvd_prod_of_mem _ hi) _

theorem sub_dvd_denom {M : Finset ι} {s t : ι} (hs : s ∈ M) (ht : t ∈ M) (hst : s ≠ t) :
    (X s - X t : MvPolynomial ι ℚ) ∣ denom M := by
  have h : (s, t) ∈ M.offDiag := mem_offDiag.2 ⟨hs, ht, hst⟩
  exact dvd_mul_of_dvd_right (dvd_prod_of_mem (fun p : ι × ι => (X p.1 - X p.2 :
    MvPolynomial ι ℚ)) h) _

variable {K : Type*} [Field K] [CharZero K]

/-- `D(w) ≠ 0` **iff** `w` is admissible on `M`. -/
theorem aeval_denom_ne_zero_iff (w : ι → K) (M : Finset ι) :
    aeval w (denom M) ≠ 0 ↔ Admissible w M := by
  simp only [denom, map_mul, map_prod, map_sub, aeval_X, ne_eq, mul_eq_zero, not_or,
    prod_eq_zero_iff, not_exists, not_and, mem_offDiag, sub_eq_zero, and_imp, Prod.forall,
    Admissible]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun s hs t ht => h2 s t hs ht⟩,
    fun ⟨h1, h2⟩ => ⟨h1, fun s t hs ht => h2 s hs t ht⟩⟩

/-! ## The specialisation relation -/

section Spec

variable (D : MvPolynomial ι ℚ) (w : ι → K)

local notation "φ" => algebraMap (MvPolynomial ι ℚ) (Qw ι)

/-- `x ∈ ℚ(w)` specialises to `y ∈ K` through the denominator `D`. -/
def Spec (x : Qw ι) (y : K) : Prop :=
  ∃ (a : MvPolynomial ι ℚ) (k : ℕ), x = φ a / φ D ^ k ∧ y = aeval w a / aeval w D ^ k

variable {D w}

theorem spec_poly (a : MvPolynomial ι ℚ) : Spec D w (φ a) (aeval w a) :=
  ⟨a, 0, by simp, by simp⟩

theorem spec_one : Spec D w 1 1 := by simpa using spec_poly (D := D) (w := w) 1

theorem spec_X (i : ι) : Spec D w (gen i) (w i) := by
  simpa [gen] using spec_poly (D := D) (w := w) (X i)

variable (hD : D ≠ 0) (hDw : aeval w D ≠ 0)
include hD hDw

theorem phiD_ne_zero : φ D ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι ℚ) (Qw ι))).2 hD

theorem spec_add {x x' : Qw ι} {y y' : K} (h : Spec D w x y) (h' : Spec D w x' y') :
    Spec D w (x + x') (y + y') := by
  obtain ⟨a, k, rfl, rfl⟩ := h
  obtain ⟨b, l, rfl, rfl⟩ := h'
  have h0 := phiD_ne_zero hD hDw
  refine ⟨a * D ^ l + b * D ^ k, k + l, ?_, ?_⟩
  · simp only [map_add, map_mul, map_pow]; field_simp; ring
  · simp only [map_add, map_mul, map_pow]; field_simp; ring

theorem spec_mul {x x' : Qw ι} {y y' : K} (h : Spec D w x y) (h' : Spec D w x' y') :
    Spec D w (x * x') (y * y') := by
  obtain ⟨a, k, rfl, rfl⟩ := h
  obtain ⟨b, l, rfl, rfl⟩ := h'
  refine ⟨a * b, k + l, ?_, ?_⟩
  · simp only [map_mul]; rw [pow_add]; field_simp
  · simp only [map_mul]; rw [pow_add]; field_simp

theorem spec_neg {x : Qw ι} {y : K} (h : Spec D w x y) : Spec D w (-x) (-y) := by
  obtain ⟨a, k, rfl, rfl⟩ := h
  exact ⟨-a, k, by simp [neg_div], by simp [neg_div]⟩

theorem spec_sub {x x' : Qw ι} {y y' : K} (h : Spec D w x y) (h' : Spec D w x' y') :
    Spec D w (x - x') (y - y') := by
  simpa [sub_eq_add_neg] using spec_add hD hDw h (spec_neg hD hDw h')

theorem spec_pow {x : Qw ι} {y : K} (h : Spec D w x y) (n : ℕ) : Spec D w (x ^ n) (y ^ n) := by
  induction n with
  | zero => simpa using spec_one
  | succ n ih => simpa [pow_succ] using spec_mul hD hDw ih h

theorem spec_sum {α : Type*} (s : Finset α) {x : α → Qw ι} {y : α → K}
    (h : ∀ a ∈ s, Spec D w (x a) (y a)) : Spec D w (∑ a ∈ s, x a) (∑ a ∈ s, y a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using spec_poly (D := D) (w := w) 0
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact spec_add hD hDw (h a (mem_insert_self _ _)) (ih fun b hb => h b (mem_insert_of_mem hb))

theorem spec_prod {α : Type*} (s : Finset α) {x : α → Qw ι} {y : α → K}
    (h : ∀ a ∈ s, Spec D w (x a) (y a)) : Spec D w (∏ a ∈ s, x a) (∏ a ∈ s, y a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using spec_one
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha]
    exact spec_mul hD hDw (h a (mem_insert_self _ _)) (ih fun b hb => h b (mem_insert_of_mem hb))

theorem spec_div {x x' : Qw ι} {y y' : K} (h : Spec D w x y) (h' : Spec D w x'⁻¹ y'⁻¹) :
    Spec D w (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact spec_mul hD hDw h h'

/-- Inverting a divisor of `D` stays inside the relation. -/
theorem spec_inv_dvd {b : MvPolynomial ι ℚ} (hb : b ∣ D) : Spec D w (φ b)⁻¹ (aeval w b)⁻¹ := by
  obtain ⟨c, rfl⟩ := hb
  have hb0 : b ≠ 0 := left_ne_zero_of_mul hD
  have hc0 : c ≠ 0 := right_ne_zero_of_mul hD
  have hbw : aeval w b ≠ 0 := by intro h; apply hDw; simp [h]
  have hcw : aeval w c ≠ 0 := by intro h; apply hDw; simp [h]
  have inj := IsFractionRing.injective (MvPolynomial ι ℚ) (Qw ι)
  have hbφ : φ b ≠ 0 := (map_ne_zero_iff _ inj).2 hb0
  have hcφ : φ c ≠ 0 := (map_ne_zero_iff _ inj).2 hc0
  refine ⟨c, 1, ?_, ?_⟩
  · simp only [map_mul, pow_one]; field_simp
  · simp only [map_mul, pow_one]; field_simp

end Spec

/-! ## `eq:Psidef` specialises: the `eval`-commutes-with-`Ψ` lemma -/

theorem one_sub_div_inv {F : Type*} [Field F] (u v : F) (hv : v ≠ 0) :
    (1 - u / v)⁻¹ = v * (v - u)⁻¹ := by
  rw [one_sub_div hv, inv_div, div_eq_mul_inv]

local notation "φ" => algebraMap (MvPolynomial ι ℚ) (Qw ι)

theorem gen_ne_zero (i : ι) : (gen i : Qw ι) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial ι ℚ) (Qw ι))).2 (X_ne_zero i)

section Atoms

variable {M : Finset ι} {w : ι → K} (hw : Admissible w M)
include hw

theorem hDw_of_adm : aeval w (denom M) ≠ 0 := (aeval_denom_ne_zero_iff w M).2 hw

theorem spec_inv_gen {i : ι} (hi : i ∈ M) : Spec (denom M) w (gen i)⁻¹ (w i)⁻¹ := by
  simpa [gen] using spec_inv_dvd (denom_ne_zero M) (hDw_of_adm hw) (X_dvd_denom hi)

theorem spec_zpow {i : ι} (hi : i ∈ M) (n : ℤ) : Spec (denom M) w (gen i ^ n) (w i ^ n) := by
  have hD := denom_ne_zero M
  have hDw := hDw_of_adm hw
  rcases n with n | n
  · simpa using spec_pow hD hDw (spec_X i) n
  · simp only [zpow_negSucc, ← inv_pow]
    exact spec_pow hD hDw (spec_inv_gen hw hi) _

theorem spec_inv_one_sub_div {s t : ι} (hs : s ∈ M) (ht : t ∈ M) (hst : s ≠ t) :
    Spec (denom M) w (1 - gen s / gen t)⁻¹ (1 - w s / w t)⁻¹ := by
  have hD := denom_ne_zero M
  have hDw := hDw_of_adm hw
  rw [one_sub_div_inv _ _ (gen_ne_zero t), one_sub_div_inv _ _ (hw.1 t ht)]
  refine spec_mul hD hDw (spec_X t) ?_
  have := spec_inv_dvd hD hDw (w := w) (sub_dvd_denom ht hs (Ne.symm hst))
  simpa [gen] using this

theorem spec_inv_mul {s t : ι} (hs : s ∈ M) (ht : t ∈ M) :
    Spec (denom M) w (gen s * gen t)⁻¹ (w s * w t)⁻¹ := by
  rw [mul_inv, mul_inv]
  exact spec_mul (denom_ne_zero M) (hDw_of_adm hw) (spec_inv_gen hw hs) (spec_inv_gen hw ht)

theorem spec_cross {t i : ι} (ht : t ∈ M) (hi : i ∈ M) (hti : t ≠ i) :
    Spec (denom M) w (crossFactor gen t i) (crossFactor w t i) := by
  have hD := denom_ne_zero M
  have hDw := hDw_of_adm hw
  exact spec_div hD hDw (spec_sub hD hDw spec_one (spec_inv_mul hw ht hi))
    (spec_inv_one_sub_div hw ht hi hti)

/-- **`eval` commutes with `eq:Psidef` at admissible points.** -/
theorem spec_psiHead [DecidableEq ι] (r : ℕ) (θ : Fin r → ℤ) :
    Spec (denom M) w (psiQ M r θ) (psiHead w M r θ) := by
  have hD := denom_ne_zero M
  have hDw := hDw_of_adm hw
  unfold psiQ psiHead
  refine spec_sum hD hDw _ fun h hh => ?_
  simp only [headInjections, mem_filter, Fintype.mem_piFinset] at hh
  obtain ⟨hM, hinj⟩ := hh
  refine spec_mul hD hDw (spec_mul hD hDw ?_ ?_) ?_
  · refine spec_prod hD hDw _ fun j _ => spec_mul hD hDw ?_ (spec_zpow hw (hM j) _)
    exact spec_sub hD hDw spec_one (spec_pow hD hDw (spec_inv_gen hw (hM j)) 2)
  · refine spec_prod hD hDw _ fun j _ => spec_prod hD hDw _ fun k hk => ?_
    have hjk : h j ≠ h k := fun e => (ne_of_lt (mem_filter.1 hk).2) (hinj e)
    exact spec_div hD hDw (spec_sub hD hDw spec_one (spec_inv_mul hw (hM j) (hM k)))
      (spec_inv_one_sub_div hw (hM j) (hM k) hjk)
  · refine spec_prod hD hDw _ fun t ht => spec_prod hD hDw _ fun j _ => ?_
    obtain ⟨htM, htn⟩ := mem_sdiff.1 ht
    exact spec_cross hw htM (hM j) fun e => htn (mem_image.2 ⟨j, mem_univ _, e.symm⟩)

end Atoms

/-! ## The bridge -/

/-- A `Spec` value is determined by any representation `a / D^k` of the generic value. -/
theorem spec_rep {D a : MvPolynomial ι ℚ} {k : ℕ} {w : ι → K} {x : Qw ι} {y : K}
    (hD : D ≠ 0) (hDw : aeval w D ≠ 0) (h : Spec D w x y) (hx : x = φ a / φ D ^ k) :
    y = aeval w a / aeval w D ^ k := by
  obtain ⟨b, l, hb, rfl⟩ := h
  have h0 := phiD_ne_zero (w := w) hD hDw
  have inj := IsFractionRing.injective (MvPolynomial ι ℚ) (Qw ι)
  have e : a * D ^ l = b * D ^ k := by
    apply inj
    rw [hx] at hb
    simp only [map_mul, map_pow]
    field_simp at hb
    linear_combination hb
  have e' := congrArg (aeval w) e
  simp only [map_mul, map_pow] at e'
  field_simp
  linear_combination -e'

theorem infinite_of_charZero : Infinite K := Infinite.of_injective _ (Nat.cast_injective (R := K))

/-- **Generic ⇒ pointwise.** If `Ψ = 0` in `ℚ(w)`, then `Ψ(w) = 0` at every admissible point of
every characteristic-zero field. -/
theorem psiHead_eq_zero_of_psiQ_eq_zero [DecidableEq ι] {M : Finset ι} {r : ℕ} {θ : Fin r → ℤ}
    (h : psiQ M r θ = 0) {w : ι → K} (hw : Admissible w M) : psiHead w M r θ = 0 := by
  obtain ⟨a, k, hx, hy⟩ := spec_psiHead hw r θ
  have h0 := phiD_ne_zero (w := w) (denom_ne_zero M) (hDw_of_adm hw)
  rw [h, eq_comm, div_eq_zero_iff] at hx
  have ha : a = 0 := by
    rcases hx with hx | hx
    · exact (map_eq_zero_iff _ (IsFractionRing.injective (MvPolynomial ι ℚ) (Qw ι))).1 hx
    · exact absurd (pow_eq_zero_iff'.1 hx).1 h0
  rw [hy, ha, map_zero, zero_div]

/-- **Pointwise ⇒ generic.** If `Ψ(w) = 0` at every admissible point of a characteristic-zero
field `K`, then `Ψ = 0` in `ℚ(w)`. (The scoped route: `D·a` vanishes everywhere; `funext`.) -/
theorem psiQ_eq_zero_of_forall [DecidableEq ι] {M : Finset ι} {r : ℕ} {θ : Fin r → ℤ}
    (h : ∀ w : ι → K, Admissible w M → psiHead w M r θ = 0) : psiQ M r θ = 0 := by
  haveI := infinite_of_charZero (K := K)
  obtain ⟨w₀, hw₀⟩ := exists_admissible (K := K) M
  obtain ⟨a, k, hx, -⟩ := spec_psiHead hw₀ r θ
  have hDa : ∀ w : ι → K, aeval w (denom M * a) = 0 := by
    intro w
    rw [map_mul]
    by_cases hw : Admissible w M
    · have hy := spec_rep (denom_ne_zero M) (hDw_of_adm hw) (spec_psiHead hw r θ) hx
      rw [h w hw, eq_comm, div_eq_zero_iff] at hy
      rcases hy with hy | hy
      · rw [hy, mul_zero]
      · exact absurd (pow_eq_zero_iff'.1 hy).1 (hDw_of_adm hw)
    · rw [← aeval_denom_ne_zero_iff, not_not] at hw
      rw [hw, zero_mul]
  have hmap : MvPolynomial.map (algebraMap ℚ K) (denom M * a) = 0 :=
    MvPolynomial.funext fun w => by rw [eval_map, ← aeval_def, hDa, map_zero]
  have hzero : denom M * a = 0 :=
    MvPolynomial.map_injective _ (algebraMap ℚ K).injective (by rw [hmap, map_zero])
  have ha : a = 0 := (mul_eq_zero.1 hzero).resolve_left (denom_ne_zero M)
  rw [hx, ha, map_zero, zero_div]

/-- **The bridge.** `Ψ = 0` in `ℚ(w)` iff `Ψ(w) = 0` at every admissible point of `K`
(any field of characteristic zero). -/
theorem psiQ_eq_zero_iff [DecidableEq ι] (K : Type*) [Field K] [CharZero K] (M : Finset ι) (r : ℕ)
    (θ : Fin r → ℤ) :
    psiQ M r θ = 0 ↔ ∀ w : ι → K, Admissible w M → psiHead w M r θ = 0 :=
  ⟨fun h _ hw => psiHead_eq_zero_of_psiQ_eq_zero h hw, psiQ_eq_zero_of_forall⟩

/-! ## `thm:main` and `cor:criterion` in the paper's form: statements in `ℚ(w)` -/

/-- **`thm:main`** (`.tex` L360–L393), as stated: `Ψ^C_{(1^r),θ}(M) ≠ 0` in `ℚ(w_1,…,w_n)`. -/
theorem thm_main_Qw [DecidableEq ι] (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) (hcard : r ≤ M.card)
    (hinj : Function.Injective (rhoShiftPaper θ)) : psiQ M r θ ≠ 0 := by
  intro h
  obtain ⟨w, hw, hne⟩ := thm_main (K := ℚ) M r θ hcard hinj
  exact hne ((psiQ_eq_zero_iff ℚ M r θ).1 h w hw)

/-- **`cor:criterion`** (`.tex` L395–L409), as stated: `Ψ = 0` in `ℚ(w)` iff `n < r` or two
ρ-shifts coincide. -/
theorem cor_criterion_Qw [DecidableEq ι] [Nonempty ι] (M : Finset ι) (r : ℕ) (θ : Fin r → ℤ) :
    psiQ M r θ = 0 ↔
      (M.card < r ∨ ∃ j k : Fin r, j < k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) :=
  (psiQ_eq_zero_iff ℚ M r θ).trans (cor_criterion (K := ℚ) M r θ)

/-! ## Lesions on the bridge: ask Lean for `False` from each lesioned statement -/

/-- The pointwise ⇒ generic half over an **arbitrary** field (no characteristic-zero / infinite
hypothesis). -/
def BridgeAnyField : Prop :=
  ∀ (K : Type) [Field K] (M : Finset ℕ) (r : ℕ) (θ : Fin r → ℤ),
    (∀ w : ℕ → K, Admissible w M → psiHead w M r θ = 0) → psiQ M r θ = 0

theorem psiQ_rank_zero [DecidableEq ι] (M : Finset ι) (θ : Fin 0 → ℤ) : psiQ M 0 θ = 1 :=
  psiHead_rank_zero _ _ _

local instance fact_prime_two'' : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- **L-infinite (drop `CharZero K`, hence `Infinite K`): refutable** at `K = 𝔽₂`, `M = {0,1}`,
`r = 0`. There is no admissible point, so the hypothesis is vacuous, but `Ψ = 1 ≠ 0`. -/
theorem lesion_anyField_refutable : ¬ BridgeAnyField := by
  intro H
  have h := H (ZMod 2) {0, 1} 0 ![] fun w hw => by
    exfalso
    obtain ⟨h0, hd⟩ := hw
    have a := h0 0 (by simp)
    have b := h0 1 (by simp)
    have c := hd 0 (by simp) 1 (by simp) (by decide)
    revert a b c
    generalize w 0 = x
    generalize w 1 = y
    revert x y
    decide
  rw [psiQ_rank_zero] at h
  exact one_ne_zero h

/-- Admissibility with **nonzero dropped** (distinctness only). -/
def AdmDist (w : ι → K) (M : Finset ι) : Prop := ∀ s ∈ M, ∀ t ∈ M, s ≠ t → w s ≠ w t

/-- The generic ⇒ pointwise half with the nonzero condition dropped. -/
def BridgeNoNonzero : Prop :=
  ∀ (M : Finset ℕ) (r : ℕ) (θ : Fin r → ℤ),
    psiQ M r θ = 0 → ∀ w : ℕ → ℚ, AdmDist w M → psiHead w M r θ = 0

/-- **L-nonzero: refutable** at `M = {0,1}`, `r = 2`, `θ = (1,0)` (a ρ-shift tie, so `Ψ = 0` in
`ℚ(w)` by `cor_criterion_Qw`) and the point `w = (0, 2)`: Lean's `0⁻¹ = 0` gives the value
`3/2`. So the bridge needs `w_i ≠ 0`; junk values at a pole are not specialisations. -/
theorem lesion_nonzero_refutable : ¬ BridgeNoNonzero := by
  intro H
  have hz : psiQ ({0, 1} : Finset ℕ) 2 ![1, 0] = 0 :=
    (cor_criterion_Qw _ 2 _).2 (Or.inr ⟨0, 1, by decide, by decide⟩)
  have hd : AdmDist (![0, 2] ∘ (fun i : ℕ => (if i = 0 then 0 else 1 : Fin 2)) : ℕ → ℚ)
      ({0, 1} : Finset ℕ) := by
    intro s hs t ht hst
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs ht
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp_all
  have hv := H _ 2 _ hz _ hd
  have hH : headInjections ({0, 1} : Finset ℕ) 2 = {![0, 1], ![1, 0]} := by decide
  rw [psiHead, hH, Finset.sum_pair (by decide)] at hv
  have e1 : ({0, 1} : Finset ℕ) \ Finset.univ.image ![0, 1] = ∅ := by decide
  have e2 : ({0, 1} : Finset ℕ) \ Finset.univ.image ![1, 0] = ∅ := by decide
  have e3 : (Finset.univ.filter fun k : Fin 2 => (0 : Fin 2) < k) = {1} := by decide
  have e4 : (Finset.univ.filter fun k : Fin 2 => (1 : Fin 2) < k) = ∅ := by decide
  simp [e1, e2, Fin.prod_univ_two, e3, e4] at hv
  norm_num at hv

/-- Positive control for the instance: `cor_criterion_Qw` at the paper's distinct-shift instance
`θ = (0,0)` on `M = {0,1}` (ρ-shifts `(0,1)`) says `Ψ ≠ 0` in `ℚ(w)`. -/
theorem inst_thm_main_Qw : psiQ ({0, 1} : Finset ℕ) 2 ![0, 0] ≠ 0 :=
  thm_main_Qw _ 2 _ (by decide) (by rw [paper_m_00]; decide)

end TworowD4Kernel.QwBridge
