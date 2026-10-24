/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.BoundaryEmptyIndex
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Multiset.Basic

/-!
# `prop:recip`: the reciprocal-pair structural vanishing

Formalises `prop:recip` of
`projects/proofs/2026-10-23-Q559-vanishing-converse.tex` (Clio, 23 Oct 2026, L455–L470),
whose statement quantifies over the factor `B(T)` of `eq:B` (L135–L144).

## The paper's statement

> **Proposition (reciprocal pairs; P3).** Let `w_1, …, w_n` be pairwise distinct nonzero
> complex numbers, so that every denominator in `eq:Psidef` and `eq:B` is nonzero and both
> formulas evaluate. Suppose `w_a w_b = 1` for some `a ≠ b`. If `n ≤ r+1` then `B(T) = 0`
> for *every* `r`-subset `T`, hence `Ψ^C_{(1^r),θ}(M) = 0` for *every* `θ` — including
> every `θ` with pairwise distinct ρ-shifts.
>
> *Proof.* Let `|T| = r`. Since `|M ∖ T| = n − r ≤ 1`, `T` cannot omit both `a` and `b`.
> If `a, b ∈ T` then the pair factor `1 − 1/(w_a w_b) = 0`. If exactly one of them lies in
> `T`, say `a ∈ T` and `b ∈ M ∖ T`, then the factor `1 − 1/(w_b w_a)` of the third product
> (with `t = b`, `x = w_a`) is `0`. Either way `B(T) = 0`, and `thm:alt` is a sum of terms
> each containing `B(T)`.

## Honest scope

* `thm:alt` — the passage from the head-injection definition `eq:Psidef` to the alternant
  sum — is **not** formalised. It is the standing gap of the whole development and it is
  too big for one slot. It enters `psiAlt_eq_zero_of_reciprocal_pair` the way `thm:main`
  entered `BoundaryEmptyIndex.criterion_iff`: as the *definition* `psiAlt`, which is the
  alternant side taken as given. **A Lean-verified summand is not a Lean-verified sum**;
  the parent registry node `clio-Q553-vanishing-converse-Q559` stays at `proved`.
* `eq:B` is formalised **literally, with division in a field** (`Bfactor` below), not with
  denominators cleared. See the L4 grade for what that costs and what it does not.
* The ordering `x_1, …, x_r` of `T` (`thm:alt`) stays abstracted as `ord`, inherited from
  `BoundaryEmptyIndex`.

## PRE-REGISTRATION — written 2026-10-24T10:40:56Z, before the first `lake build`

Grades are recorded in `§ Grades` at the foot of this file, never here.

| # | lesion | PREDICTION |
|---|--------|------------|
| L1 | drop `n ≤ r+1` | **IRREMOVABLE**, with an explicit witness: at `n = r+2` some `T` avoids both `a` and `b`, so no factor of `eq:B` is forced to vanish |
| L2 | drop `a ≠ b` | **SPLIT** — true at a *different* threshold. With `a = b`, `w_a w_a = 1` means `w_a = ±1`, `{a,b}` is a **singleton**, and "every `r`-subset meets a singleton" needs `n ≤ r`, not `n ≤ r+1`: the hypothesis shifts the bound by one |
| L3 | `r = 0` edge | **ABSENT (vacuous)** — `n ≤ 1` cannot hold while `M` carries two distinct indices |
| L4 | `w` nonzero / pairwise distinct | **ABSENT** — the proof only multiplies and compares to `0`; no inverse of a possibly-vanishing quantity is taken |
| {L1,L2} | both dropped | **PAIR PREDICTION: jointly FALSE**, two-line counterexample |

L2 is the one that matters: `state/PROVE.md` §3 Q565-A pre-registered a guess that this
note's two stated conditions (`w_a w_b = 1` and `w_a = ±1`) are **one** condition on a
*multiset* of indices with `a = b` as the diagonal degeneration, and that the artifact's
`w_a = ±1` is therefore stated at the wrong threshold. L2 decides it.
-/

namespace TworowD4Kernel.ReciprocalPair

open Finset
open TworowD4Kernel.BoundaryEmptyIndex

variable {ι : Type*} {K : Type*} [DecidableEq ι] [Field K]

/-! ### `eq:B`, literally

`eq:B` (L135–L144):
`B(T) = ∏_{x∈T} (1 − x⁻²) · ∏_{{x,y}⊆T} (1 − 1/(xy)) · ∏_{t∈M∖T} ∏_{x∈T} (1−1/(w_t x))/(1−w_t/x)`.

The middle product runs over *unordered pairs* of `T`, which is `T.powersetCard 2`; a pair
`p` contributes `1 − (∏_{i∈p} w i)⁻¹`. That the carrier is a `Finset` and not a `Multiset`
turns out to be exactly where L2 bites — see `pairFactor_singleton_ne_diagFactor`. -/

/-- The diagonal factor `1 − x⁻²` of the first product of `eq:B`. -/
noncomputable def diagFactor (w : ι → K) (i : ι) : K := 1 - (w i)⁻¹ ^ 2

/-- The pair factor `1 − 1/(xy)` of the second product of `eq:B`, as a function of the
unordered pair `p = {x, y} ⊆ T`. -/
noncomputable def pairFactor (w : ι → K) (p : Finset ι) : K := 1 - (∏ i ∈ p, w i)⁻¹

/-- The cross factor `(1 − 1/(w_t x))/(1 − w_t/x)` of the third product of `eq:B`. -/
noncomputable def crossFactor (w : ι → K) (t i : ι) : K :=
  (1 - (w t * w i)⁻¹) / (1 - w t / w i)

/-- **`eq:B`.** The coefficient `B(T)` of `thm:alt`, for `T ⊆ M`. -/
noncomputable def Bfactor (w : ι → K) (M T : Finset ι) : K :=
  (∏ i ∈ T, diagFactor w i) * (∏ p ∈ T.powersetCard 2, pairFactor w p) *
    (∏ t ∈ M \ T, ∏ i ∈ T, crossFactor w t i)

/-! ### The pigeonhole

The only interesting step of the paper proof: `|M ∖ T| = n − r ≤ 1`, so `T` cannot omit
both `a` and `b`. -/

/-- **Pigeonhole.** If `T ⊆ M` with `|T| = r` and `|M| ≤ r+1`, then `T` meets any pair of
distinct elements of `M`. This is the paper's "`T` cannot omit both `a` and `b`". -/
theorem mem_or_mem_of_card_le_succ {M T : Finset ι} {r : ℕ} {a b : ι}
    (hTM : T ⊆ M) (hT : T.card = r) (hM : M.card ≤ r + 1)
    (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) : a ∈ T ∨ b ∈ T := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨ha', hb'⟩ := hcon
  have hsub : ({a, b} : Finset ι) ⊆ M \ T := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact Finset.mem_sdiff.2 ⟨ha, ha'⟩
    · exact Finset.mem_sdiff.2 ⟨hb, hb'⟩
  have h2 : 2 ≤ (M \ T).card := by
    calc (2 : ℕ) = ({a, b} : Finset ι).card := (Finset.card_pair hab).symm
      _ ≤ (M \ T).card := Finset.card_le_card hsub
  rw [Finset.card_sdiff_of_subset hTM, hT] at h2
  omega

/-! ### The two cases of the case split

Each is one application of `Finset.prod_eq_zero`: *a product with a vanishing factor
vanishes*. The two cases vanish through **different products of `eq:B`**, and the positive
controls below check that both are actually reached. -/

/-- **Case `{a,b} ⊆ T`.** The pair factor `1 − 1/(w_a w_b)` of the *second* product is
`0`. -/
theorem pairProd_eq_zero_of_recip {w : ι → K} {T : Finset ι} {a b : ι} (hab : a ≠ b)
    (ha : a ∈ T) (hb : b ∈ T) (hw : w a * w b = 1) :
    ∏ p ∈ T.powersetCard 2, pairFactor w p = 0 := by
  refine Finset.prod_eq_zero (i := ({a, b} : Finset ι)) ?_ ?_
  · exact Finset.mem_powersetCard.2
      ⟨by simp [Finset.insert_subset_iff, ha, hb], Finset.card_pair hab⟩
  · rw [pairFactor, Finset.prod_pair hab, hw, inv_one, sub_self]

/-- **Case `|T ∩ {a,b}| = 1`.** With `t ∈ M ∖ T` and `i ∈ T` and `w_t w_i = 1`, the factor
`1 − 1/(w_t w_i)` of the *third* product is `0` — the paper's "with `t = b`, `x = w_a`". -/
theorem crossProd_eq_zero_of_recip {w : ι → K} {M T : Finset ι} {t i : ι}
    (ht : t ∈ M \ T) (hi : i ∈ T) (hw : w t * w i = 1) :
    ∏ s ∈ M \ T, ∏ j ∈ T, crossFactor w s j = 0 := by
  refine Finset.prod_eq_zero ht (Finset.prod_eq_zero hi ?_)
  rw [crossFactor, hw, inv_one, sub_self, zero_div]

/-! ### `prop:recip`, the `B(T)` layer -/

/-- **`prop:recip`, `B`-layer.** `w_a w_b = 1` with `a ≠ b` and `n ≤ r+1` forces
`B(T) = 0` for every `r`-subset `T ⊆ M`.

Note which hypotheses are *absent*: no `w t ≠ 0`, no pairwise distinctness. L4. -/
theorem Bfactor_eq_zero_of_reciprocal_pair {w : ι → K} {M T : Finset ι} {r : ℕ} {a b : ι}
    (hTM : T ⊆ M) (hT : T.card = r) (hM : M.card ≤ r + 1)
    (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    Bfactor w M T = 0 := by
  have key : (∏ p ∈ T.powersetCard 2, pairFactor w p) = 0 ∨
      (∏ s ∈ M \ T, ∏ j ∈ T, crossFactor w s j) = 0 := by
    rcases mem_or_mem_of_card_le_succ hTM hT hM hab ha hb with haT | hbT
    · by_cases hbT : b ∈ T
      · exact Or.inl (pairProd_eq_zero_of_recip hab haT hbT hw)
      · exact Or.inr (crossProd_eq_zero_of_recip (M := M)
          (Finset.mem_sdiff.2 ⟨hb, hbT⟩) haT (by rw [mul_comm]; exact hw))
    · by_cases haT : a ∈ T
      · exact Or.inl (pairProd_eq_zero_of_recip hab haT hbT hw)
      · exact Or.inr (crossProd_eq_zero_of_recip (M := M)
          (Finset.mem_sdiff.2 ⟨ha, haT⟩) hbT hw)
  rcases key with h | h <;> rw [Bfactor, h] <;> ring

/-- **`prop:recip`, paper form.** The statement with the paper's own standing hypotheses
("pairwise distinct nonzero") present. They are discharged by `fun _ _ _ => rfl`-level
inertness: the proof is the same term as above. Kept so that the paper's sentence exists
verbatim in Lean, and so that the L4 grade is a comparison of two real declarations
rather than of a declaration against a story. -/
theorem Bfactor_eq_zero_of_reciprocal_pair_paper {w : ι → K} {M T : Finset ι} {r : ℕ}
    {a b : ι} (_hnz : ∀ t ∈ M, w t ≠ 0)
    (_hdist : ∀ s ∈ M, ∀ t ∈ M, s ≠ t → w s ≠ w t)
    (hTM : T ⊆ M) (hT : T.card = r) (hM : M.card ≤ r + 1)
    (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    Bfactor w M T = 0 :=
  Bfactor_eq_zero_of_reciprocal_pair hTM hT hM hab ha hb hw

/-! ### Lifting to the alternant sum

`psiAlt` of `BoundaryEmptyIndex` takes `B` as an abstract parameter, so the lift is one
`Finset.sum_eq_zero`. This is the paper's "`thm:alt` is a sum of terms each containing
`B(T)`" — and it is *all* that `thm:alt` is used for here. -/

/-- A sum over `thm:alt`'s index set vanishes as soon as every `B(T)` does. -/
theorem psiAlt_eq_zero_of_forall_B_eq_zero (M : Finset ι) (r : ℕ) (x : ι → K)
    (B V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ)
    (hB : ∀ T ∈ M.powersetCard r, B T = 0) :
    psiAlt M r x B V ord θ = 0 := by
  rw [psiAlt]
  exact Finset.sum_eq_zero fun T hT => by rw [hB T hT, zero_mul]

/-- **`prop:recip`, the conclusion.** `Ψ^C_{(1^r),θ}(M) = 0` for **every** `θ` — in
particular for every `θ` with pairwise distinct ρ-shifts, which is the point of the
proposition: this zero is not the `thm:vanish` zero. -/
theorem psiAlt_eq_zero_of_reciprocal_pair (M : Finset ι) (r : ℕ) (w x : ι → K)
    (V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) {a b : ι}
    (hM : M.card ≤ r + 1) (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    psiAlt M r x (Bfactor w M) V ord θ = 0 := by
  refine psiAlt_eq_zero_of_forall_B_eq_zero M r x _ V ord θ fun T hT => ?_
  obtain ⟨hTM, hTc⟩ := Finset.mem_powersetCard.1 hT
  exact Bfactor_eq_zero_of_reciprocal_pair hTM hTc hM hab ha hb hw

/-- The conclusion holds *simultaneously for all* `θ`, which is how the paper states it.
Separated out because `∀ θ` after the hypotheses is a different proposition from the
`∀ θ`-closure of the above only in presentation — but the presentation is the claim. -/
theorem psiAlt_eq_zero_of_reciprocal_pair_forall (M : Finset ι) (r : ℕ) (w x : ι → K)
    (V : Finset ι → K) (ord : Finset ι → Fin r → ι) {a b : ι}
    (hM : M.card ≤ r + 1) (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) (hw : w a * w b = 1) :
    ∀ θ : Fin r → ℤ, psiAlt M r x (Bfactor w M) V ord θ = 0 :=
  fun θ => psiAlt_eq_zero_of_reciprocal_pair M r w x V ord θ hM hab ha hb hw

/-! ## L2 — the `a = b` arm: the diagonal degeneration, and its threshold

L2 predicted **SPLIT at `n ≤ r`**. The mechanism is not the one the pigeonhole sentence
suggests: with `a = b` the vanishing factor is the **first** product of `eq:B`, the
diagonal `1 − x⁻²`, because `{a, b}` is a singleton and so is not a member of
`T.powersetCard 2` at all. -/

/-- With `w_a² = 1` and `a ∈ T`, the *diagonal* factor `1 − w_a⁻²` of the **first**
product of `eq:B` vanishes. This is the `a = b` degeneration of
`pairProd_eq_zero_of_recip`, and it lives in a different product. -/
theorem diagProd_eq_zero_of_self_recip {w : ι → K} {T : Finset ι} {a : ι} (ha : a ∈ T)
    (hw : w a * w a = 1) : ∏ i ∈ T, diagFactor w i = 0 := by
  refine Finset.prod_eq_zero ha ?_
  rw [diagFactor, pow_two, ← mul_inv, hw, inv_one, sub_self]

/-- **`prop:recip` at `a = b`, at the shifted threshold `n ≤ r`.** Every `r`-subset of `M`
must *contain* `a` (not merely meet `{a, b}`), and `T ⊆ M` with `|M| ≤ r = |T|` forces
`T = M`. So the bound is `n ≤ r`, one lower than the `a ≠ b` bound `n ≤ r+1`. -/
theorem Bfactor_eq_zero_of_self_reciprocal {w : ι → K} {M T : Finset ι} {r : ℕ} {a : ι}
    (hTM : T ⊆ M) (hT : T.card = r) (hM : M.card ≤ r) (ha : a ∈ M)
    (hw : w a * w a = 1) : Bfactor w M T = 0 := by
  have hTeq : T = M := Finset.eq_of_subset_of_card_le hTM (by omega)
  rw [Bfactor, diagProd_eq_zero_of_self_recip (hTeq ▸ ha) hw, zero_mul, zero_mul]

/-! ### The Q565-A unification, and the carrier it needs

`state/PROVE.md` §3 Q565-A guessed that `w_a w_b = 1` and `w_a = ±1` are **one** condition
on a *multiset* of indices, with `a = b` the diagonal degeneration. Lean confirms the
guess — and sharpens it: the unification is true over `Multiset` and **false** over
`Finset`, because `({a, a} : Finset ι) = {a}` collapses the square. -/

/-- **The unification.** Read over a `Multiset` of indices, the pair factor at the
diagonal `{a, a}` *is* the diagonal factor: `1 − 1/(w_a · w_a) = 1 − w_a⁻²`. So `eq:B`'s
first two products are one product over the multiset `{{x, y}} ⊆⊆ T` with repeats. -/
theorem pairFactor_multiset_diagonal (w : ι → K) (a : ι) :
    1 - ((({a, a} : Multiset ι).map w).prod)⁻¹ = diagFactor w a := by
  simp [diagFactor, pow_two, mul_inv]

/-- **The carrier matters.** Over `Finset` the unification fails: `{a, a} = {a}` has
product `w_a`, not `w_a²`, so `pairFactor` at the collapsed pair is `1 − w_a⁻¹`, which is
not `diagFactor`. Witness `w ≡ 2` over `ℚ`: `1/2 ≠ 3/4`. -/
theorem pairFactor_singleton_ne_diagFactor :
    pairFactor (fun _ : ℕ => (2 : ℚ)) {0} ≠ diagFactor (fun _ : ℕ => (2 : ℚ)) 0 := by
  norm_num [pairFactor, diagFactor]

/-! ## Lesion witnesses

Every lesion is posed as a **refutation**: `¬ (∀ …)`, with Lean deriving `False` from the
lesioned statement. (On `prop:boundary` yesterday the prediction was "unprovable" and
Lean returned "refutable", a strictly stronger verdict, only because the question was
posed this way.) -/

/-- L1 witness weights: `w_0 w_1 = 2 · ½ = 1`, and `w_2 = 3` is off the reciprocal pair.
Pairwise distinct and nonzero, so the paper's standing hypotheses all hold. -/
def wL1 : ℕ → ℚ
  | 0 => 2
  | 1 => 1/2
  | _ => 3

/-- The L1 witness value, computed from `eq:B` directly. `r = 1`, `n = 3 = r + 2`,
`T = {2}` avoids **both** `a = 0` and `b = 1`, and no factor is forced to vanish. -/
theorem Bfactor_wL1 : Bfactor wL1 {0, 1, 2} {2} = 8/9 := by
  rw [Bfactor, show ({0, 1, 2} : Finset ℕ) \ {2} = {0, 1} from by decide,
    show ({2} : Finset ℕ).powersetCard 2 = ∅ from by decide]
  norm_num [diagFactor, crossFactor, wL1, Finset.prod_insert, Finset.prod_pair]

/-- **L1 — VERDICT.** The threshold `n ≤ r+1` is **IRREMOVABLE**: dropping it makes the
proposition false, witnessed at `n = r + 2`. -/
theorem L1_threshold_irremovable :
    ¬ (∀ (M T : Finset ℕ) (r : ℕ) (w : ℕ → ℚ) (a b : ℕ), T ⊆ M → T.card = r →
        a ≠ b → a ∈ M → b ∈ M → w a * w b = 1 → Bfactor w M T = 0) := by
  intro h
  have hz := h {0, 1, 2} {2} 1 wL1 0 1 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by norm_num [wL1])
  rw [Bfactor_wL1] at hz
  norm_num at hz

/-- L2 witness weights: `w_0 = 1`, so `w_0 · w_0 = 1` with `a = b = 0`; `w_1 = 2`. -/
def wL2 : ℕ → ℚ
  | 0 => 1
  | _ => 2

/-- The L2 witness value. `r = 1`, `n = 2 = r + 1`, so the *original* threshold holds —
and yet `B({1}) ≠ 0`, because `T = {1}` does not contain `a`. -/
theorem Bfactor_wL2 : Bfactor wL2 {0, 1} {1} = 3/4 := by
  rw [Bfactor, show ({0, 1} : Finset ℕ) \ {1} = {0} from by decide,
    show ({1} : Finset ℕ).powersetCard 2 = ∅ from by decide]
  norm_num [diagFactor, crossFactor, wL2]

/-- **L2 — VERDICT, half one.** Dropping `a ≠ b` while keeping the threshold `n ≤ r+1`
makes the proposition **FALSE**. Together with `Bfactor_eq_zero_of_self_reciprocal` (which
proves it at `n ≤ r`) this is the predicted **SPLIT**, at exactly the predicted bound. -/
theorem L2_distinctness_irremovable_at_succ_threshold :
    ¬ (∀ (M T : Finset ℕ) (r : ℕ) (w : ℕ → ℚ) (a b : ℕ), T ⊆ M → T.card = r →
        M.card ≤ r + 1 → a ∈ M → b ∈ M → w a * w b = 1 → Bfactor w M T = 0) := by
  intro h
  have hz := h {0, 1} {1} 1 wL2 0 0 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by norm_num [wL2])
  rw [Bfactor_wL2] at hz
  norm_num at hz

/-- **L3 — VERDICT.** The `r = 0` arm is **vacuous**: `n ≤ 0 + 1` is incompatible with two
distinct indices in `M`, so the hypotheses of `prop:recip` can never be met at `r = 0`.
Lean derives `False` from the hypotheses alone, with no reference to `eq:B`. -/
theorem L3_rank_zero_arm_is_vacuous {M : Finset ι} {a b : ι}
    (hM : M.card ≤ 0 + 1) (hab : a ≠ b) (ha : a ∈ M) (hb : b ∈ M) : False := by
  have hsub : ({a, b} : Finset ι) ⊆ M := by simp [Finset.insert_subset_iff, ha, hb]
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at h2
  omega

/-- Joint-lesion witness weights: `w_0 = 1` (so `a = b = 0` is self-reciprocal),
`w_1 = 2`, `w_2 = 3`. -/
def wJoint : ℕ → ℚ
  | 0 => 1
  | 1 => 2
  | _ => 3

/-- The joint-lesion witness value, `n = 3 = r + 2` and `a = b = 0`. -/
theorem Bfactor_wJoint : Bfactor wJoint {0, 1, 2} {1} = -5/4 := by
  rw [Bfactor, show ({0, 1, 2} : Finset ℕ) \ {1} = {0, 2} from by decide,
    show ({1} : Finset ℕ).powersetCard 2 = ∅ from by decide]
  norm_num [diagFactor, crossFactor, wJoint, Finset.prod_insert, Finset.prod_pair]

/-- **{L1, L2} — PAIR VERDICT.** With *neither* the threshold nor distinctness the
proposition is **jointly FALSE**, as predicted. Recorded separately from the marginals:
a register of marginals is not a register of the joint (Q546). -/
theorem L1_L2_jointly_false :
    ¬ (∀ (M T : Finset ℕ) (r : ℕ) (w : ℕ → ℚ) (a b : ℕ), T ⊆ M → T.card = r →
        a ∈ M → b ∈ M → w a * w b = 1 → Bfactor w M T = 0) := by
  intro h
  have hz := h {0, 1, 2} {1} 1 wJoint 0 0 (by decide) (by decide) (by decide) (by decide)
    (by norm_num [wJoint])
  rw [Bfactor_wJoint] at hz
  norm_num at hz

/-! ## Positive controls

`prop:recip` would be a theorem about nothing if `Bfactor` were constantly `0`, or if only
one of the two cases of the paper's split were ever reached. These controls separate both.
`r` takes the values `0, 1, 2` across the file and `n` takes `2, 3`. -/

/-- Control weights: the reciprocal pair `w_0 w_1 = 2 · ½ = 1`, pairwise distinct and
nonzero. -/
def wCtl : ℕ → ℚ
  | 0 => 2
  | _ => 1/2

/-- **Control P0 — `Bfactor` is not identically zero.** Immediate from `Bfactor_wL1`
(`8/9`), so every vanishing statement above has content. -/
theorem control_Bfactor_not_identically_zero : Bfactor wL1 {0, 1, 2} {2} ≠ 0 := by
  rw [Bfactor_wL1]; norm_num

/-- **Control P1 — case `{a,b} ⊆ T` is reached, through the PAIR product.** `r = 2`,
`n = 2`, `T = {0, 1} ∋ a, b`. The pair product is `0` while the diagonal product is
`-9/4 ≠ 0` and the cross product is the empty product `1`: the mechanism is isolated, not
merely the conclusion. -/
theorem control_case_both_in_T :
    (∏ p ∈ ({0, 1} : Finset ℕ).powersetCard 2, pairFactor wCtl p) = 0 ∧
      (∏ i ∈ ({0, 1} : Finset ℕ), diagFactor wCtl i) = -9/4 ∧
      (∏ t ∈ ({0, 1} : Finset ℕ) \ {0, 1}, ∏ i ∈ ({0, 1} : Finset ℕ),
        crossFactor wCtl t i) = 1 ∧
      Bfactor wCtl {0, 1} {0, 1} = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ({0, 1} : Finset ℕ).powersetCard 2 = {{0, 1}} from by decide]
    norm_num [pairFactor, wCtl, Finset.prod_pair]
  · norm_num [diagFactor, wCtl, Finset.prod_pair]
  · rw [show ({0, 1} : Finset ℕ) \ {0, 1} = ∅ from by decide, Finset.prod_empty]
  · exact Bfactor_eq_zero_of_reciprocal_pair (r := 2) (a := 0) (b := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by norm_num [wCtl])

/-- **Control P2 — case `|T ∩ {a,b}| = 1` is reached, through the CROSS product.** `r = 1`,
`n = 2 = r + 1`, `T = {0} ∋ a` and `b = 1 ∈ M ∖ T`. The cross product is `0` while the
diagonal product is `3/4 ≠ 0` and the pair product is the empty product `1`. So P1 and P2
vanish through **different** products of `eq:B` — the case split is not cosmetic. -/
theorem control_case_one_in_T :
    (∏ t ∈ ({0, 1} : Finset ℕ) \ {0}, ∏ i ∈ ({0} : Finset ℕ),
        crossFactor wCtl t i) = 0 ∧
      (∏ i ∈ ({0} : Finset ℕ), diagFactor wCtl i) = 3/4 ∧
      (∏ p ∈ ({0} : Finset ℕ).powersetCard 2, pairFactor wCtl p) = 1 ∧
      Bfactor wCtl {0, 1} {0} = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [show ({0, 1} : Finset ℕ) \ {0} = {1} from by decide]
    norm_num [crossFactor, wCtl]
  · norm_num [diagFactor, wCtl]
  · rw [show ({0} : Finset ℕ).powersetCard 2 = ∅ from by decide, Finset.prod_empty]
  · exact Bfactor_eq_zero_of_reciprocal_pair (r := 1) (a := 0) (b := 1)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by norm_num [wCtl])

/-! ## GRADES — written 2026-10-24, after the build

`lake build`: success, 0 `sorry` (grep), all 22 top-level theorems on
`[propext, Classical.choice, Quot.sound]` and no `sorryAx`. The planted-`sorry` control
printed `declaration uses 'sorry'` as a **warning** while `Build completed successfully`
still printed, so the success line is again confirmed worthless as a sorry-freeness grade.
`#print axioms` ran with a negative control (`theorem bad := by sorry` ⇒ `[sorryAx]`).

| # | PREDICTION | VERDICT |
|---|-----------|---------|
| L1 | IRREMOVABLE + witness | **CONFIRMED.** `L1_threshold_irremovable`; `Bfactor wL1 {0,1,2} {2} = 8/9` at `n = r+2 = 3`, `r = 1`. |
| L2 | SPLIT at `n ≤ r` | **CONFIRMED on the threshold, REFUTED on the mechanism.** See below. |
| L3 | ABSENT (vacuous) | **CONFIRMED.** `L3_rank_zero_arm_is_vacuous` derives `False` from the hypotheses alone. |
| L4 | ABSENT | **CONFIRMED, by the linter and not by me.** With the underscores removed, `unusedVariables` flags both `hnz` and `hdist` in `..._paper`. Caveat below. |
| {L1,L2} | jointly FALSE | **CONFIRMED.** `L1_L2_jointly_false`, witness `wJoint`, value `-5/4`. |

### L2: right threshold, wrong product

The bound `n ≤ r` is exactly as pre-registered (`Bfactor_eq_zero_of_self_reciprocal`
proves it; `L2_distinctness_irremovable_at_succ_threshold` refutes `n ≤ r+1`). But the
pre-registration's *reason* kept the vanishing in `eq:B`'s **pair** product — "`{a,b}` is a
singleton" — and that is where it is **not**. A singleton has card `1`, so `{a,a}` is not a
member of `T.powersetCard 2` at all and the pair product never sees the degeneration. The
vanishing factor is the **diagonal** `1 − x⁻²` of `eq:B`'s *first* product.

So the brief's claim that "only the pigeonhole is interesting" was wrong twice over: the
pigeonhole is eight routine lines, and the content sits in the case split it dismissed.

### Q565-A adjudicated

`state/PROVE.md` §3's guess — that `w_a w_b = 1` and `w_a = ±1` are one condition on a
*multiset* with `a = b` the diagonal degeneration — is **correct, and the carrier is load
bearing**: `pairFactor_multiset_diagonal` proves the unification over `Multiset`, and
`pairFactor_singleton_ne_diagFactor` shows it is **false** over `Finset`
(`1/2 ≠ 3/4`). `({a,a} : Finset ι) = {a}` collapses the square; `Multiset` does not.

### Two corrections owed to `2026-10-23-Q559-vanishing-converse.tex`

Both follow from `Bfactor_eq_zero_of_self_reciprocal`, and neither is new mathematics —
they are scope errors in sentences *about* `prop:recip`.

1. **§9, L648** poses the open question as whether "the reciprocal-pair locus (together
   with `w_a = ±1`) [is] the *whole* zero locus", as though `prop:recip` delivered both
   arms. It does not: `prop:recip` assumes `a ≠ b`, and the `w_a = ±1` arm holds at
   `n ≤ r`, a threshold `prop:recip` states nowhere.
2. **§ sampler hygiene, L560–L561** excludes `w_a = ±1` "[a]fter Proposition
   `prop:recip`". The exclusion is sound — but it is justified by a proposition that does
   not cover it. *An exclusion cited to the wrong proposition is an unproved exclusion.*

### L4's caveat: removable in Lean is wider, not stronger

`Bfactor` is a **total extension** of the paper's `B`: Lean's `x/0 = 0` makes it defined
where `eq:B` is not, which is why no step consumes `hnz`/`hdist`. At such a point `Bfactor`
is not the paper's `B`, so the removability is a statement about the extension's domain and
**not** a strengthening of `prop:recip`. The paper form is kept for exactly this reason.

### Free lesion pass, read as instructed

`unusedDecidableInType` flags `[DecidableEq ι]` on `mem_or_mem_of_card_le_succ`,
`pairProd_eq_zero_of_recip` and `psiAlt_eq_zero_of_forall_B_eq_zero`: needed by the proof
terms (`M \ T`), absent from the types. Left in place for uniformity with `Bfactor`, which
genuinely needs it — recorded rather than silently suppressed.
-/

end TworowD4Kernel.ReciprocalPair
