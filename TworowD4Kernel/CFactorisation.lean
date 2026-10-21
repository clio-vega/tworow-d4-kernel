/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.Ring

/-!
# Theorem A: the biorthogonality pairing does not see a single-index row factor

This module formalises the algebraic core of **Theorem A** of
`projects/proofs/2026-10-20-c2-G5-reduction.tex` (`thm:A`, §7).

## The setting, and what is abstract

The object of the paper is Motegi's deformed branching matrix
`B^c_{M,K} = (∏ t ∈ M \ K, c t) * G_{M,K}`, where `G` is a type-independent kernel
(`eq:G`) and the whole type `B` / type `C` dependence is carried by the single-index
family `c` (`prop:types`, from Motegi `lem:allcard-Bhat-product`, L4666).

Theorem A says the pairing
`T^c_{M,L} = ∑_K B^c_{M,K}(q) * q^{|λ(K)|-|λ(L)|} * B^c_{Lᶜ,Kᶜ}(q⁻¹)`
is, up to one scalar, independent of `c`.

**`G` and the `q`-power are kept abstract here** — arbitrary functions
`Finset ι → Finset ι → R`. That is not a weakening: it is the content. Theorem A
never looks inside either of them, and making them opaque is the only way to see
that.

The two evaluations `q` and `q⁻¹` are modelled by two *independent* kernels `G`,
`G'`, and hypothesis (H) of the paper (`c_t(w, q⁻¹) = c_t(w, q)`, `eq:H`) is
modelled by passing two *independent* families `c`, `c'` and demanding `c' = c`.
That keeps (H) a lesionable binder rather than a structural coincidence.

## What is NOT formalised

No `w`, no `q`, no root system, no branching matrix, no weight function, no
biorthogonality. In particular `T0_eq_delta` (the `c ≡ 1` core, `eq:core`) is an
*input* here, never proved: this module shows the type content of G5 is nil, not
that G5 holds.

## Three places where this is sharper than the paper proof

* `term_c_factor`: the identity holds **summand by summand**, so the paper's
  Step 3 bijection `U ↦ L ⊔ U` from `𝒫(M \ L)` onto the interval `[L, M]` is not
  needed. `T_c_eq` is therefore stated for an **arbitrary** index family
  `S : Finset (Finset ι)`, not just `𝒫([N])`.
* No hypothesis `L ⊆ M`. The paper's `eq:main` splits into three strata
  (`L ⊊ M`, `L = M`, `L ⊄ M`); the single formula
  `T^c = (∏ d ∈ M \ L, c d) * T^1` covers all three, because off the support both
  sides vanish and on the diagonal `M \ L = ∅`.
* No invertibility of `c` for the factorisation itself. Units are needed only for
  the `↔` of `T_delta_iff`, exactly as one would hope.

Reference: `arXiv:2409.06217` (Motegi), `lem:allcard-Bhat-product` L4666,
`prop:allcard-Bhat-inverse` L4910, `thm:BC-all-cardinality-biorthogonality`.
-/

namespace TworowD4Kernel.CFactorisation

open Finset

variable {ι : Type*} [DecidableEq ι] {R : Type*}

/-! ### The two set identities the paper proof suppresses -/

/-- Complement flip. This is what turns the support condition `Kᶜ ⊆ Lᶜ` of the second
factor of `eq:T` into `L ⊆ K`, and hence what produces the interval `L ⊆ K ⊆ M` in
Step 1 of the paper proof. -/
theorem compl_sdiff_compl [Fintype ι] (K L : Finset ι) : Lᶜ \ Kᶜ = K \ L := by
  ext x
  simp only [mem_sdiff, mem_compl, not_not]
  tauto

/-- The *relative* complement identity. Together with `Finset.prod_sdiff` this is the
actual content of the "`D = (D \ U) ⊔ U` is a partition" step of the paper proof: the
two products in the summand are over `M \ K` and `K \ L`, not over `D \ U` and `U`,
and reaching the partition needs this rewriting inside the ambient `M \ L`.

Note `L ⊆ K` is used and `K ⊆ M` is *not*. -/
theorem sdiff_sdiff_cancel {K L M : Finset ι} (hLK : L ⊆ K) :
    (M \ L) \ (K \ L) = M \ K := by
  ext x
  simp only [mem_sdiff, not_and, not_not]
  constructor
  · rintro ⟨⟨hM, hL⟩, h⟩
    exact ⟨hM, fun hK => hL (h hK)⟩
  · rintro ⟨hM, hK⟩
    exact ⟨⟨hM, fun hL => hK (hLK hL)⟩, fun hK' => absurd hK' hK⟩

/-- The assembly step, `eq:CD`: the `c`-factors of the two halves of a summand
multiply to a product that does not mention the summation index `K`.

Both hypotheses are used, and for *different* jobs: `hKM` supplies the subset side
condition of `Finset.prod_sdiff`, `hLK` supplies the set identity
`sdiff_sdiff_cancel`. See `prod_c_assemble_needs_hLK` / `_needs_hKM`. -/
theorem prod_c_assemble [CommMonoid R] (c : ι → R) {K L M : Finset ι}
    (hLK : L ⊆ K) (hKM : K ⊆ M) :
    (∏ t ∈ M \ K, c t) * (∏ t ∈ K \ L, c t) = ∏ t ∈ M \ L, c t := by
  have hsub : K \ L ⊆ M \ L := sdiff_subset_sdiff hKM (subset_refl L)
  rw [← Finset.prod_sdiff (f := c) hsub, sdiff_sdiff_cancel hLK]

/-! ### The deformed branching matrix -/

variable [CommSemiring R]

/-- `B^c_{M,K}`, `def:Bc`: the type-independent kernel `G` scaled by the single-index
product over `M \ K`, and `0` off the support `K ⊆ M`. -/
def B (c : ι → R) (G : Finset ι → Finset ι → R) (M K : Finset ι) : R :=
  if K ⊆ M then (∏ t ∈ M \ K, c t) * G M K else 0

/-- `B^1_{M,K}`: the same matrix at `c ≡ 1`. -/
def B0 (G : Finset ι → Finset ι → R) (M K : Finset ι) : R :=
  if K ⊆ M then G M K else 0

@[simp] theorem B_one (G : Finset ι → Finset ι → R) (M K : Finset ι) :
    B (fun _ => (1 : R)) G M K = B0 G M K := by
  simp [B, B0]

theorem B_of_not_subset (c : ι → R) (G : Finset ι → Finset ι → R) {M K : Finset ι}
    (h : ¬ K ⊆ M) : B c G M K = 0 := by
  simp [B, h]

theorem B0_of_not_subset (G : Finset ι → Finset ι → R) {M K : Finset ι}
    (h : ¬ K ⊆ M) : B0 G M K = 0 := by
  simp [B0, h]

/-- On the diagonal every product in `def:Bc` is empty, so `B^c_{A,A} = G_{A,A}` for
every `c`. This is Step 2 of the paper proof. -/
theorem B_diag (c : ι → R) (G : Finset ι → Finset ι → R) (A : Finset ι) :
    B c G A A = G A A := by
  simp [B]

/-! ### The pairing, and Theorem A -/

variable [Fintype ι]

/-- `T^c_{M,L}`, `eq:T`, over an arbitrary index family `S`.

`p` abstracts the scalar `q^{|λ(K)| - |λ(L)|}`; `G` is the kernel at `q` and `G'` the
kernel at `q⁻¹`. The paper's pairing is the case `S = Finset.univ.powerset`; see
`T_c_eq_powerset`. -/
def T (c c' : ι → R) (G G' p : Finset ι → Finset ι → R) (S : Finset (Finset ι))
    (M L : Finset ι) : R :=
  ∑ K ∈ S, B c G M K * p K L * B c' G' Lᶜ Kᶜ

/-- `T^1_{M,L}`. -/
def T0 (G G' p : Finset ι → Finset ι → R) (S : Finset (Finset ι)) (M L : Finset ι) : R :=
  ∑ K ∈ S, B0 G M K * p K L * B0 G' Lᶜ Kᶜ

/-- **The termwise form of Theorem A.** Each individual summand of `eq:T` already
carries the full factor `∏ d ∈ M \ L, c d`, with no reference to the summation index
`K` and no hypothesis relating `L` and `M`.

This is strictly stronger than the paper's Step 3: it needs no bijection
`U ↦ L ⊔ U`, and it is why `T_c_eq` holds for an arbitrary index family. -/
theorem term_c_factor (c : ι → R) (G G' p : Finset ι → Finset ι → R)
    (M L K : Finset ι) :
    B c G M K * p K L * B c G' Lᶜ Kᶜ
      = (∏ d ∈ M \ L, c d) * (B0 G M K * p K L * B0 G' Lᶜ Kᶜ) := by
  by_cases hKM : K ⊆ M
  · by_cases hLK : L ⊆ K
    · -- the support case: `L ⊆ K ⊆ M`, both factors live and their `c`-products assemble
      have hcompl : Kᶜ ⊆ Lᶜ := compl_subset_compl.mpr hLK
      rw [B, B0, B, B0, if_pos hKM, if_pos hKM, if_pos hcompl, if_pos hcompl,
        compl_sdiff_compl]
      rw [← prod_c_assemble c hLK hKM]
      ring
    · -- the second factor is off support: `Kᶜ ⊆ Lᶜ` fails
      have hcompl : ¬ Kᶜ ⊆ Lᶜ := fun h => hLK (compl_subset_compl.mp h)
      rw [B_of_not_subset _ _ hcompl, B0_of_not_subset _ hcompl]
      ring
  · rw [B_of_not_subset _ _ hKM, B0_of_not_subset _ hKM]
    ring

/-- **Theorem A** (`thm:A`, `eq:main`), in the sharp form: for *every* pair `M, L`
and *every* index family `S`,
`T^c_{M,L} = (∏ d ∈ M \ L, c d) * T^1_{M,L}`,
provided the two evaluations use the same `c` — which is hypothesis (H), `eq:H`.

The paper states this as a case split over three strata; there is no case split. -/
theorem T_c_eq (c c' : ι → R) (hc : c' = c) (G G' p : Finset ι → Finset ι → R)
    (S : Finset (Finset ι)) (M L : Finset ι) :
    T c c' G G' p S M L = (∏ d ∈ M \ L, c d) * T0 G G' p S M L := by
  subst hc
  rw [T, T0, Finset.mul_sum]
  exact Finset.sum_congr rfl fun K _ => term_c_factor _ G G' p M L K

/-- The paper's own pairing: `S = 𝒫([N])`. -/
theorem T_c_eq_powerset (c : ι → R) (G G' p : Finset ι → Finset ι → R)
    (M L : Finset ι) :
    T c c G G' p (Finset.univ : Finset ι).powerset M L
      = (∏ d ∈ M \ L, c d) * T0 G G' p (Finset.univ : Finset ι).powerset M L :=
  T_c_eq c c rfl G G' p _ M L

/-- On the diagonal the scalar is empty, so `T^c` and `T^1` agree outright. -/
theorem T_diag (c : ι → R) (G G' p : Finset ι → Finset ι → R)
    (S : Finset (Finset ι)) (M : Finset ι) :
    T c c G G' p S M M = T0 G G' p S M M := by
  rw [T_c_eq c c rfl, sdiff_self]
  simp

/-- **Corollary: types `B` and `C` are one theorem** (`cor:BC`). The pairing is
`δ` for `c` if and only if it is `δ` for `c ≡ 1`, hence for any other `c`.

This is the only statement in the module that needs the `c t` to be units. -/
theorem T_delta_iff {F : Type*} [Field F] (c : ι → F) (hc : ∀ t, c t ≠ 0)
    (G G' p : Finset ι → Finset ι → F) (S : Finset (Finset ι)) :
    (∀ M L : Finset ι, T c c G G' p S M L = if M = L then 1 else 0)
      ↔ (∀ M L : Finset ι, T0 G G' p S M L = if M = L then 1 else 0) := by
  have hprod : ∀ M L : Finset ι, (∏ d ∈ M \ L, c d) ≠ 0 := fun M L =>
    Finset.prod_ne_zero_iff.mpr fun t _ => hc t
  constructor
  · intro h M L
    rcases eq_or_ne M L with rfl | hne
    · rw [← T_diag c G G' p S M, h M M]
    · have := h M L
      rw [T_c_eq c c rfl, if_neg hne] at this
      simpa [hne, hprod M L] using (mul_eq_zero.mp this).resolve_left (hprod M L)
  · intro h M L
    rw [T_c_eq c c rfl, h M L]
    rcases eq_or_ne M L with rfl | hne
    · simp
    · simp [hne]

/-! ### The type `B` / type `C` specialisation

`prop:types` of the paper: the two types are the two values
`c^B_t = (1 - w_t⁻¹)⁻¹` and `c^C_t = (1 - w_t⁻²)⁻¹` of the single-index family.
Only the *ratio* is formalised here; `w` itself stays an element of an abstract field,
and no claim is made about `prop:types` (that is Motegi `lem:allcard-Bhat-product`,
L4666, verified computationally in the paper and NOT formalised). -/

section Types

variable {F : Type*} [Field F]

/-- `c^B_t`. -/
noncomputable def cB (w : F) : F := (1 - w⁻¹)⁻¹

/-- `c^C_t`. -/
noncomputable def cC (w : F) : F := (1 - w⁻¹ ^ 2)⁻¹

/-- The ratio of `cor:BC`: `c^B_t = (1 + w_t⁻¹) * c^C_t`.

The only hypothesis is `w ≠ -1`. The paper's informal reading needs `w ∉ {0, 1}` as
well — those are the poles of `c^B` — but they are *not* needed for this identity, and
`cB_eq_at_zero` / `cB_eq_at_one` below record why: at `w ∈ {0, 1}` Lean's junk value
`(0 : F)⁻¹ = 0` makes both sides agree off the domain of definition. `w = -1` is the one
point where the junk values do **not** conspire, and it is exactly the pole-zero
collision locus of Q538. -/
theorem cB_eq_one_add_inv_mul_cC {w : F} (hw : w ≠ -1) : cB w = (1 + w⁻¹) * cC w := by
  have hu : (1 : F) + w⁻¹ ≠ 0 := by
    intro h
    have hinv : w⁻¹ = -1 := by linear_combination h
    rcases eq_or_ne w 0 with rfl | hw0
    · simp at hinv
    · refine hw ?_
      have h2 : w * w⁻¹ = w * (-1) := by rw [hinv]
      rw [mul_inv_cancel₀ hw0] at h2
      linear_combination h2
  have hfac : (1 : F) - w⁻¹ ^ 2 = (1 - w⁻¹) * (1 + w⁻¹) := by ring
  rw [cB, cC, hfac, mul_inv,
    show (1 + w⁻¹) * ((1 - w⁻¹)⁻¹ * (1 + w⁻¹)⁻¹)
        = (1 - w⁻¹)⁻¹ * ((1 + w⁻¹) * (1 + w⁻¹)⁻¹) from by ring,
    mul_inv_cancel₀ hu, mul_one]

/-! #### Lesion register for the ratio lemma

`w ≠ 0` and `w ≠ 1` are REMOVABLE; `w ≠ -1` is IRREMOVABLE. -/

/-- `w ≠ 0` removable: the identity is an instance of the theorem at `w = 0`. -/
theorem cB_eq_at_zero : cB (0 : ℚ) = (1 + (0 : ℚ)⁻¹) * cC (0 : ℚ) :=
  cB_eq_one_add_inv_mul_cC (by norm_num)

/-- `w ≠ 1` removable: the identity is an instance of the theorem at `w = 1`. -/
theorem cB_eq_at_one : cB (1 : ℚ) = (1 + (1 : ℚ)⁻¹) * cC (1 : ℚ) :=
  cB_eq_one_add_inv_mul_cC (by norm_num)

/-- …but at `w = 1` the identity is `0 = 2 * 0`: both sides are junk values standing in
for a pole. The removability of `w ≠ 1` is an artefact of `(0 : F)⁻¹ = 0`, not a
mathematical strengthening. -/
theorem cB_at_one_eq_zero : cB (1 : ℚ) = 0 ∧ cC (1 : ℚ) = 0 := by
  constructor <;> norm_num [cB, cC]

/-- **`w ≠ -1` is irremovable**, and the witness is over `ℚ`:
`cB (-1) = 2⁻¹` while `(1 + (-1)⁻¹) * cC (-1) = 0 * 0 = 0`. -/
theorem cB_ne_ratio_at_neg_one :
    cB (-1 : ℚ) ≠ (1 + (-1 : ℚ)⁻¹) * cC (-1 : ℚ) := by
  norm_num [cB, cC]

end Types

/-! ### Lesion register for the core lemmas -/

/-- `L ⊆ K` is irremovable from `prod_c_assemble`: take `L = {0}`, `K = ∅`, `M = {0}`,
`c ≡ 2`. Then `K ⊆ M` holds, the left side is `2` and the right side is `1`. -/
theorem prod_c_assemble_needs_hLK :
    ∃ (c : Fin 2 → ℚ) (K L M : Finset (Fin 2)), K ⊆ M ∧ ¬ L ⊆ K ∧
      (∏ t ∈ M \ K, c t) * (∏ t ∈ K \ L, c t) ≠ ∏ t ∈ M \ L, c t := by
  refine ⟨fun _ => 2, ∅, {0}, {0}, by simp, by simp, ?_⟩
  norm_num

/-- `K ⊆ M` is irremovable from `prod_c_assemble`: take `L = ∅`, `K = {0}`, `M = ∅`,
`c ≡ 2`. Then `L ⊆ K` holds, the left side is `2` and the right side is `1`. -/
theorem prod_c_assemble_needs_hKM :
    ∃ (c : Fin 2 → ℚ) (K L M : Finset (Fin 2)), L ⊆ K ∧ ¬ K ⊆ M ∧
      (∏ t ∈ M \ K, c t) * (∏ t ∈ K \ L, c t) ≠ ∏ t ∈ M \ L, c t := by
  refine ⟨fun _ => 2, {0}, ∅, ∅, by simp, by simp, ?_⟩
  norm_num

/-- **Hypothesis (H) is irremovable from Theorem A.** This is the Lean form of
`prop:sharp`: with `ι = Fin 1`, `G = G' = p ≡ 1`, `c ≡ 1` but `c' ≡ 2`, the pairing is
`1 + 2 = 3` while `(∏ d ∈ M \ L, c d) * T^1 = 1 * 2 = 2`.

So the two evaluations really must use the *same* `c`; inversion-invariance `eq:H` is
not decoration. -/
theorem H_irremovable :
    ∃ (c c' : Fin 1 → ℚ) (G G' p : Finset (Fin 1) → Finset (Fin 1) → ℚ)
      (M L : Finset (Fin 1)),
      T c c' G G' p ({∅, {0}} : Finset (Finset (Fin 1))) M L
        ≠ (∏ d ∈ M \ L, c d) * T0 G G' p ({∅, {0}} : Finset (Finset (Fin 1))) M L := by
  refine ⟨fun _ => 1, fun _ => 2, fun _ _ => 1, fun _ _ => 1, fun _ _ => 1, {0}, ∅, ?_⟩
  rw [T, T0]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Finset.sum_singleton]
  norm_num [B, B0]

/-- The index family `{∅, {0}}` used in `H_irremovable` really is the paper's `𝒫([1])`. -/
theorem powerset_univ_fin_one :
    (Finset.univ : Finset (Fin 1)).powerset = ({∅, {0}} : Finset (Finset (Fin 1))) := by
  decide

/-- **Invertibility of `c` is irremovable from `T_delta_iff`** — and it is needed there
and nowhere else: `T_c_eq` holds over any `CommSemiring`, with no condition on `c`.

Witness: `c ≡ 0` over `ℚ` with `ι = Fin 1`, `G = G' = p ≡ 1`. The off-diagonal entry
`T^1_{{0},∅} = 2` is nonzero, but the scalar `∏ d ∈ {0} \ ∅, c d = 0` annihilates it, so
`T^c` vanishes off the diagonal while `T^1` does not. The `↔` of `cor:BC` therefore
really does need the paper's `c_t ∈ F^×`. -/
theorem T_delta_iff_needs_units :
    ∃ (c : Fin 1 → ℚ) (G G' p : Finset (Fin 1) → Finset (Fin 1) → ℚ)
      (S : Finset (Finset (Fin 1))) (M L : Finset (Fin 1)),
      M ≠ L ∧ T c c G G' p S M L = 0 ∧ T0 G G' p S M L ≠ 0 := by
  refine ⟨fun _ => 0, fun _ _ => 1, fun _ _ => 1, fun _ _ => 1,
    ({∅, {0}} : Finset (Finset (Fin 1))), {0}, ∅, by decide, ?_, ?_⟩
  · rw [T_c_eq _ _ rfl]
    simp
  · rw [T0, Finset.sum_insert (by decide), Finset.sum_singleton]
    norm_num [B0]

end TworowD4Kernel.CFactorisation
