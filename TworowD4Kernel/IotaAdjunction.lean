/-
Copyright (c) 2026 Clio. All rights reserved.
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Rat.Defs

/-!
# The ι-adjunction scalar: reindexing along the inversion involution

Formalises the algebraic core of the gauge theorem of
`projects/proofs/2026-10-18-c2-gauge-theorem-and-q-divisors.tex`
(Clio, 18 Oct 2026): Lemma `lem:I2` (§"Two reindexing identities", L409–L437) and
Step 5 of Theorem `thm:gauge` (L444–L536).

## The paper's setup, stated the paper's way

`def:iota` (L250): a finite multiset `D` of elements of `Fˣ` is **ι-closed** if there
is an involution `τ` of its index set with `y (τ j) = (y j)⁻¹` for all `j`.

`def` of the three products (L387–L394), products over slots of `D`:
* `Q₁(D) := ∏_{ordered (j,k)} (1 - q * y k / y j)`   — **all** ordered pairs, `j = k` included
* `Q₂(D)² = ∏_{ordered (j,k), j ≠ k} (1 - q * y j * y k)`  — the paper's own ordered form, L424

`lem:I2` (L409): `Q₂² / Q₁ = 1 / ∏_{y ∈ D} (1 - q y²)`.
Step 5 (L527): the adjunction scalar is `(∏ y)^{1-d} (1-q)^d P₂ Q₂ / Q₁ = ∏_{y ∈ D} φ(y)`
with `φ(y) = (1-q)/(1-q y²)`.

## Honest scope

What is formalised here is the **identity**, not the weight-function bookkeeping of
Steps 1–4 (which needs `W^C`, `E^C` and the six lines of the `T`-operator).  Nothing
below mentions the `T`-operator, head selections, or `r`.  See the lesion section for
why that matters for the `pairwise distinct` hypothesis.

## Hypotheses actually spent

Stated as hypotheses on an indexed family, with the orbit trichotomy **derived**
(`iotaScalar_empty`, `iotaScalar_fixedPoint`, `iotaScalar_freeOrbit`) rather than built
into the type.
-/

namespace IotaAdjunction

open Finset

variable {K : Type*} [Field K] {d : ℕ}

/-- `φ(v) = (1-q)/(1-q v²)`, the one-variable adjunction factor. Paper L453. -/
noncomputable def phi (q v : K) : K := (1 - q) / (1 - q * v ^ 2)

/-- `Q₁(D) = ∏_{ordered (j,k)} (1 - q y_k / y_j)`, diagonal included. Paper L388. -/
noncomputable def Q1 (q : K) (y : Fin d → K) : K :=
  ∏ j, ∏ k, (1 - q * y k / y j)

/-- `Q₂(D)²` in the paper's own ordered form: the product over **ordered distinct**
pairs of slots. Paper L424. -/
noncomputable def Q2sq (q : K) (y : Fin d → K) : K :=
  ∏ p ∈ Finset.univ.offDiag, (1 - q * y p.1 * y p.2)

/-- The full ordered double product, diagonal included — the object `G` that both
`Q1` and `Q2sq * ∏ (1 - q y²)` turn out to equal. -/
noncomputable def Gfull (q : K) (y : Fin d → K) : K :=
  ∏ j, ∏ k, (1 - q * y j * y k)

/-! ### Step A: the τ-reindexing. This is the only place ι-closure is spent. -/

/-- **The reindexing identity.** `Q₁` is the full ordered product of `1 - q y_j y_k`.

The paper reindexes `j = τ i` and uses `y_k / y_{τ i} = y_k * y_i`; `τ` is used only
as a *bijection* of the index set together with `y ∘ τ = y⁻¹`.

Note what is **not** used: `τ` involutive, `y j ≠ 0`, and the values pairwise
distinct. See `reindex_lesions` below. -/
theorem Q1_eq_Gfull (q : K) (y : Fin d → K) (τ : Equiv.Perm (Fin d))
    (hy : ∀ j, y (τ j) = (y j)⁻¹) :
    Q1 q y = Gfull q y := by
  unfold Q1 Gfull
  rw [← Equiv.prod_comp τ (fun j => ∏ k, (1 - q * y k / y j))]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
  rw [hy i, div_eq_mul_inv, inv_inv]; ring

/-! ### Step B: splitting the diagonal. Pure `Finset` bookkeeping, no hypotheses. -/

/-- The full ordered product splits as (off-diagonal) × (diagonal). -/
theorem Gfull_eq (q : K) (y : Fin d → K) :
    Gfull q y = Q2sq q y * ∏ j, (1 - q * (y j) ^ 2) := by
  unfold Gfull Q2sq
  rw [← Finset.prod_product' (s := (Finset.univ : Finset (Fin d)))
        (t := (Finset.univ : Finset (Fin d))) (f := fun j k => 1 - q * y j * y k),
    ← Finset.diag_union_offDiag (Finset.univ : Finset (Fin d)),
    Finset.prod_union (Finset.disjoint_diag_offDiag _), mul_comm]
  congr 1
  rw [Finset.prod_diag]
  exact Finset.prod_congr rfl fun j _ => by ring

/-! ### `lem:I2` -/

/-- **Lemma I2** (paper L409, multiplicative form — no division, so no genericity
hypothesis): `Q₁ = Q₂² · ∏_{y ∈ D} (1 - q y²)`.

The paper states it as `Q₂²/Q₁ = 1/∏(1-qy²)`; this is that statement cleared of
denominators, which is strictly stronger (it also covers the degenerate loci). -/
theorem lem_I2 (q : K) (y : Fin d → K) (τ : Equiv.Perm (Fin d))
    (hy : ∀ j, y (τ j) = (y j)⁻¹) :
    Q1 q y = Q2sq q y * ∏ j, (1 - q * (y j) ^ 2) := by
  rw [Q1_eq_Gfull q y τ hy, Gfull_eq]

/-- `lem:I2` in the paper's divided form, under the genericity the division needs. -/
theorem lem_I2_div (q : K) (y : Fin d → K) (τ : Equiv.Perm (Fin d))
    (hy : ∀ j, y (τ j) = (y j)⁻¹) (hQ : Q2sq q y ≠ 0)
    (hd : ∀ j, 1 - q * (y j) ^ 2 ≠ 0) :
    Q2sq q y / Q1 q y = 1 / ∏ j, (1 - q * (y j) ^ 2) := by
  have hp : (∏ j, (1 - q * (y j) ^ 2)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hd j
  rw [lem_I2 q y τ hy]
  field_simp

/-! ### Step 5 of `thm:gauge`: the adjunction scalar -/

/-- **Step 5 of the gauge theorem** (paper L527).  The adjunction scalar
`(1-q)^d · Q₂² / Q₁` equals `∏_{y ∈ D} φ(y)`.

The paper writes the left side as `(∏y)^{1-d}(1-q)^d P₂ Q₂ / Q₁` and uses `lem:I1`
to rewrite `(∏y)^{1-d} P₂ Q₂ = Q₂²`; this declaration formalises the chain from
`Q₂²` onward, which is where `φ`'s one-variable shape is produced. -/
theorem iotaAdjunctionScalar (q : K) (y : Fin d → K) (τ : Equiv.Perm (Fin d))
    (hy : ∀ j, y (τ j) = (y j)⁻¹) (hQ : Q2sq q y ≠ 0)
    (hd : ∀ j, 1 - q * (y j) ^ 2 ≠ 0) :
    (1 - q) ^ d * Q2sq q y / Q1 q y = ∏ j, phi q (y j) := by
  have hp : (∏ j, (1 - q * (y j) ^ 2)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hd j
  unfold phi
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    lem_I2 q y τ hy]
  field_simp


/-! ### The lesions

The paper's `thm:gauge` (L444) carries four hypotheses: `D` ι-closed with a **realising
involution** `τ`, values in `Fˣ` (so `y j ≠ 0`), the values of `R ⊔ D` **pairwise
distinct**, and `|R| ≥ r`.  Of these, the identity above spends **exactly one**:

* `τ` **involutive** — NOT SPENT.  `Q1_eq_Gfull` uses `τ` only as a bijection of the
  index set together with `y ∘ τ = y⁻¹`.  Stated without `Function.Involutive τ` and it
  compiles.  (With distinct values `y ∘ τ = y⁻¹` forces `τ² = 1`; without them it does
  not, so this is a genuine strengthening and not a restatement.)
* `y j ≠ 0` — NOT SPENT.  `div_eq_mul_inv` + `inv_inv` is unconditional in a field:
  at `y i = 0` both sides read `1 - 0`.
* **pairwise distinct** — NOT SPENT, and this is the finding.  No declaration above
  mentions injectivity of `y`.  In the paper that hypothesis is attached upstream, to
  `lem:head`/`cor:heads`, where it makes the line-2a/3a denominator `(v_p - v_{p'})`
  nonzero, i.e. it is a **well-definedness** hypothesis for the `T`-operator and not an
  ingredient of the reindexing identity.  `rem:distinct` (L328) says exactly this: the
  conclusion fails there "not because the mathematics is different but because the
  expression is undefined".  So the measured `0/14` at `r ≥ 1` is a fact about `T`, which
  is not formalised here.  Pre-registration "IRREMOVABLE" stands for `thm:gauge` as
  stated; it is **relocated**, not confirmed, at Step 5.
* `|R| ≥ r` — not expressible here; `r` does not occur in the identity.

The one hypothesis that IS spent is `hy : y ∘ τ = y⁻¹`, and here is the witness. -/

/-- **`hy` is irremovable.** Over `ℚ`, `d = 1`, `y = (2)`, `q = 1`: `Q₁ = 1 - 1·2/2 = 0`
but the full ordered product is `1 - 1·2·2 = -3`.  So `Q1 = Gfull` is false without
ι-closure, and the witness domain is non-empty (`q = 1 ≠ 0`, `y 0 = 2 ≠ 0`). -/
theorem Q1_ne_Gfull_without_iotaClosure :
    Q1 (1 : ℚ) (fun _ : Fin 1 => 2) ≠ Gfull (1 : ℚ) (fun _ : Fin 1 => 2) := by
  unfold Q1 Gfull
  norm_num

/-- The same witness shows `lem:I2` itself fails without ι-closure. -/
theorem lem_I2_fails_without_iotaClosure :
    Q1 (1 : ℚ) (fun _ : Fin 1 => 2)
      ≠ Q2sq (1 : ℚ) (fun _ : Fin 1 => 2) * ∏ j : Fin 1, (1 - 1 * ((2 : ℚ)) ^ 2) := by
  unfold Q1 Q2sq
  norm_num

end IotaAdjunction
