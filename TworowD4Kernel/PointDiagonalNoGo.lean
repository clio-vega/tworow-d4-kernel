/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# A point-indexed product is determined by its singleton values

Formalisation of the hinge lemma of
`projects/proofs/2026-10-18-atype-divisors-and-the-gkm-lattice.tex`
(Definition and Lemma `lem:unit`, L566--L595; Remark `rem:task1`, L597--L616;
the scope limit at L690--L699 and the `gapthm` at L1039--L1047), together with
the scope limit on Theorem C of
`projects/proofs/2026-10-17-c2-coboundary-and-the-removable-defect.tex`
(L393--L405, L823).

Rick's off-diagonal computation at `N = 2` (email UID 824) is the external
input: `Koncki_∅ = Ã_∅ + c · Ã_{{1,2}}` with `c = q(1-q)/(1 - 1/(w₁w₂))`.

## The one fact, and its two opposite consequences

Write `Ψ_χ(M) = ∏_{m ∈ M} χ(w_m)` for a *point-indexed diagonal*
renormalisation of a GKM basis indexed by labels `M ⊆ [N]`. Here `χ : ι → K`
stands for the composite `m ↦ χ(w_m)`; nothing below uses anything about `w`.

The whole content is `psi_prod_eq_prod_singletons`: `Ψ_χ` is determined by its
values on singletons. Two consequences point in opposite directions.

* **It is a no-go.** `no_single_cell_move`: if `Ψ_χ` fixes every singleton inside
  `S` then it fixes `S`. Hence `moved_cell_card_le_one`: a point-diagonal `Ψ_χ`
  that moves *exactly one* label moves a label of cardinality `≤ 1`. In
  particular `Ψ_χ {a,b} ≠ 1` with `Ψ_χ {a} = Ψ_χ {b} = 1` is unsatisfiable
  (`no_single_cell_move_pair`) — stated as a negated conjunction, so the no-go
  is the theorem rather than an implication that could be read vacuously.
* **It makes an invariance argument vacuous.** `transposition_invariance_on_diagonal`:
  `∏_{m ∈ σS} f m = ∏_{m ∈ S} f m` for `σ = swap i j` and **any** `f` with
  `f i = f j`. It is quantified over `f`, not stated for `ψ`, because that is
  what makes "this carries zero bits about `ψ`" a theorem instead of a remark.
  `control_plant_cannot_fire` records why the pre-registered "non-invariant"
  control `∏_{m ∈ M} w_m + |M|` could not fire: it too has the invariant shape.

The no-go is not a no-go over an empty domain. `offdiagonal_can_move_one_cell`
exhibits a unipotent **off-diagonal** change of basis that does move exactly one
label, with Rick's `c` instantiated at a concrete rational point — the `𝔽₂`
lesson, where `q ≠ 0` and `1 - q ≠ 0` were jointly unsatisfiable and a
counterexample over too small a structure was an empty domain wearing its
clothes.

## Scope

Nothing here is a statement about `Ã`, about Koncki's class, or about which of
them is correct. The theorems are about the *shape* `∏_{m ∈ M} χ(w_m)` and about
a transvection in label space. The mechanism gap of the parent papers stands.
-/

namespace TworowD4Kernel.PointDiagonal

variable {ι K : Type*}

/-- `Ψ_χ(S) = ∏_{m ∈ S} χ(w_m)`, the point-indexed diagonal renormalisation of the
paper's Definition at L566. The argument `χ : ι → K` is the composite `m ↦ χ(w_m)`. -/
def Psi [CommMonoid K] (χ : ι → K) (S : Finset ι) : K := ∏ m ∈ S, χ m

section Monoid

variable [CommMonoid K]

@[simp]
theorem psi_empty (χ : ι → K) : Psi χ ∅ = 1 := by simp [Psi]

@[simp]
theorem psi_singleton (χ : ι → K) (m : ι) : Psi χ {m} = χ m := by simp [Psi]

/-- **The whole content.** A point-indexed product is determined by its singleton
values: `Ψ_χ(S) = ∏_{m ∈ S} Ψ_χ({m})`. Everything else in this file is a corollary. -/
theorem psi_prod_eq_prod_singletons (χ : ι → K) (S : Finset ι) :
    Psi χ S = ∏ m ∈ S, Psi χ {m} :=
  Finset.prod_congr rfl fun m _ => (psi_singleton χ m).symm

/-- Multiplicativity in the label, one cell at a time. -/
theorem psi_prod_insert [DecidableEq ι] (χ : ι → K) {m : ι} {S : Finset ι} (hm : m ∉ S) :
    Psi χ (insert m S) = Psi χ {m} * Psi χ S := by
  simp [Psi, Finset.prod_insert hm]

/-- Two point-diagonal renormalisations agreeing on singletons agree everywhere. This is
the "determined by" of the headline, in the form that makes the singleton values a
complete set of coordinates for the family. -/
theorem psi_determined_by_singletons {χ χ' : ι → K} (h : ∀ m, Psi χ {m} = Psi χ' {m})
    (S : Finset ι) : Psi χ S = Psi χ' S := by
  simp only [psi_singleton] at h
  exact Finset.prod_congr rfl fun m _ => h m

/-- **The no-go.** If `Ψ_χ` fixes every singleton contained in `S`, it fixes `S`. -/
theorem no_single_cell_move {χ : ι → K} {S : Finset ι} (h : ∀ m ∈ S, Psi χ {m} = 1) :
    Psi χ S = 1 :=
  Finset.prod_eq_one fun m hm => by simpa using h m hm

/-- The no-go for a pair, stated as a **negated conjunction** so that the no-go itself is
the theorem: moving the `{a,b}` cell while fixing `{a}` and `{b}` is unsatisfiable. This
is the scope limit on Theorem C of the 2026-10-17-c2 paper: `Ψ_χ({1,2}) ≠ 1` with
`Ψ_χ({1}) = Ψ_χ({2}) = 1` is impossible. No hypothesis `a ≠ b` is needed. -/
theorem no_single_cell_move_pair [DecidableEq ι] (χ : ι → K) (a b : ι) :
    ¬(Psi χ {a, b} ≠ 1 ∧ Psi χ {a} = 1 ∧ Psi χ {b} = 1) := by
  rintro ⟨hne, ha, hb⟩
  refine hne (no_single_cell_move ?_)
  intro m hm
  rcases Finset.mem_insert.mp hm with rfl | hm
  · exact ha
  · rw [Finset.mem_singleton] at hm
    subst hm
    exact hb

/-- The multiplicative shadow of the pair no-go, in the paper's own variables. -/
theorem psi_pair_eq_one {χ : ι → K} {a b : ι} (ha : χ a = 1) (hb : χ b = 1) :
    χ a * χ b = 1 := by rw [ha, hb, one_mul]

/-- **The no-go, sharp form.** A point-diagonal `Ψ_χ` that moves *exactly one* label moves
a label of cardinality at most one. So no point-diagonal renormalisation can single out a
cell of size `≥ 2`. -/
theorem moved_cell_card_le_one {χ : ι → K} {S : Finset ι} (hS : Psi χ S ≠ 1)
    (hother : ∀ T, T ≠ S → Psi χ T = 1) : S.card ≤ 1 := by
  by_contra hcard
  rw [Nat.not_le] at hcard
  refine hS (no_single_cell_move fun m _ => hother {m} ?_)
  intro hEq
  rw [← hEq] at hcard
  simp at hcard

/-- The instance that kills the point-diagonal route to Koncki's 15-of-16: no point-diagonal
renormalisation moves exactly the `{a,b}` label, for `a ≠ b`. -/
theorem no_point_diagonal_moves_exactly_a_pair [DecidableEq ι] (χ : ι → K) {a b : ι}
    (hab : a ≠ b) :
    ¬(Psi χ {a, b} ≠ 1 ∧ ∀ T, T ≠ ({a, b} : Finset ι) → Psi χ T = 1) := by
  rintro ⟨h1, h2⟩
  have hle := moved_cell_card_le_one h1 h2
  rw [Finset.card_pair hab] at hle
  omega

end Monoid

/-!
## The vacuity, quantified over `f`

The next three results are stated for an arbitrary `f : ι → K`. That is the point: the
transposition invariance on the diagonal `{w_i = w_j}` is a property of the *shape*
`∏_{m ∈ M} f(w_m)`, so observing it for `ψ` carries no information about `ψ`.
-/

section Vacuity

variable [DecidableEq ι]

/-- A function constant on `{i, j}` is unchanged by precomposition with `swap i j`. -/
theorem apply_swap_eq_self {i j : ι} (f : ι → K) (hf : f i = f j) (m : ι) :
    f (Equiv.swap i j m) = f m := by
  rcases eq_or_ne m i with rfl | hmi
  · simp [hf]
  rcases eq_or_ne m j with rfl | hmj
  · simp [hf]
  · rw [Equiv.swap_apply_of_ne_of_ne hmi hmj]

variable [CommMonoid K]

/-- **The vacuity, as a theorem.** For `σ = swap i j` and **any** `f` with `f i = f j`, the
point-indexed product over `σS` equals the product over `S`. Quantified over `f`, so
`ψ` is visibly never used. -/
theorem transposition_invariance_on_diagonal (f : ι → K) {i j : ι} (hf : f i = f j)
    (S : Finset ι) :
    ∏ m ∈ S.map (Equiv.swap i j).toEmbedding, f m = ∏ m ∈ S, f m := by
  rw [Finset.prod_map]
  exact Finset.prod_congr rfl fun m _ => by
    simpa using apply_swap_eq_self f hf m

/-- The specialisation to `Ψ_χ`. Correct, and it carries zero bits about `χ`: it is
`transposition_invariance_on_diagonal` with `f := χ`. -/
theorem psi_transposition_invariant (χ : ι → K) {i j : ι} (hχ : χ i = χ j) (S : Finset ι) :
    Psi χ (S.map (Equiv.swap i j).toEmbedding) = Psi χ S :=
  transposition_invariance_on_diagonal χ hχ S

end Vacuity

/-- **Why the pre-registered control could not fire.** The planted "non-invariant"
functional `M ↦ (∏_{m ∈ M} w_m) + |M|` is transposition-invariant on the diagonal too,
because both summands are: the product by `transposition_invariance_on_diagonal` and the
cardinality by `Finset.card_map`. The plant was drawn from inside the hypothesis class, so
its silence measured nothing. (`0` violations in `96` instances at `N = 4`, `h = 2`.) -/
theorem control_plant_cannot_fire [DecidableEq ι] [CommRing K] (f : ι → K) {i j : ι}
    (hf : f i = f j) (S : Finset ι) :
    (∏ m ∈ S.map (Equiv.swap i j).toEmbedding, f m)
        + ((S.map (Equiv.swap i j).toEmbedding).card : K)
      = (∏ m ∈ S, f m) + (S.card : K) := by
  rw [Finset.card_map, transposition_invariance_on_diagonal f hf]

/-!
## The complement: off-diagonal *can* move one cell

Without this section the no-go above would be a no-go over a possibly empty domain. We
exhibit the unipotent transvection `C = Id + c · E_{b,a}` in label space, show it changes
exactly the `a` coordinate, and show it is not of the point-diagonal form for **any** `χ`.
-/

section OffDiagonal

variable {L : Type*} [DecidableEq L] [Field K]

/-- The standard basis of the coordinate space `L → K` on labels `L`. Plays the role of
`{Ã_M}` in the paper; only its linear independence is used, and here that is evaluation. -/
def std (x : L) : L → K := Pi.single x 1

/-- The unipotent off-diagonal change of basis `C = Id + c · E_{b,a}`: it replaces the
basis vector at the label `a` by `std a + c • std b` and fixes every other basis vector.
This is Rick's `Koncki_∅ = Ã_∅ + c · Ã_{{1,2}}` (UID 824) with `a = ∅`, `b = {1,2}`. -/
def konckiFamily (a b : L) (c : K) (x : L) : L → K :=
  if x = a then std x + c • std b else std x

@[simp]
theorem konckiFamily_self (a b : L) (c : K) :
    konckiFamily a b c a = (std a + c • std b : L → K) := by simp [konckiFamily]

theorem konckiFamily_of_ne (a b : L) (c : K) {x : L} (hx : x ≠ a) :
    konckiFamily a b c x = (std x : L → K) := by simp [konckiFamily, hx]

/-- The transvection really does change the `a` coordinate, provided only `c ≠ 0`.

The hypothesis `a ≠ b` was **lesioned away** (2026-10-18): the `a = b` branch collapses to
`(1 + c) • std a ≠ std a`, which `c ≠ 0` already gives. A surviving lesion is a
stronger theorem for free. Contrast `konckiFamily_not_diagonal`, where `a ≠ b` is
**irremovable** —
at `a = b` the transvection *is* diagonal, with scaling `1 + c`. The two lesions of the same
binder land on opposite sides, which is what makes `a ≠ b` the sharp hypothesis there. -/
theorem konckiFamily_ne_std {a b : L} {c : K} (hc : c ≠ 0) :
    konckiFamily a b c a ≠ (std a : L → K) := by
  intro h
  rw [konckiFamily_self] at h
  rcases eq_or_ne b a with rfl | hba
  · have hb := congrFun h b
    simp only [Pi.add_apply, Pi.smul_apply, std, Pi.single_eq_same, smul_eq_mul,
      mul_one] at hb
    exact hc (by simpa using hb)
  · have hb := congrFun h b
    simp only [Pi.add_apply, Pi.smul_apply, std, Pi.single_eq_of_ne hba, Pi.single_eq_same,
      smul_eq_mul, mul_one, zero_add] at hb
    exact hc hb

/-- **The complement to the no-go.** The off-diagonal transvection moves exactly the label
`a`: it changes the `a` basis vector and fixes every other one. -/
theorem konckiFamily_moves_exactly_one_label {a b : L} {c : K} (hc : c ≠ 0) :
    konckiFamily a b c a ≠ (std a : L → K) ∧
      ∀ x : L, x ≠ a → konckiFamily a b c x = (std x : L → K) :=
  ⟨konckiFamily_ne_std hc, fun _ hx => konckiFamily_of_ne a b c hx⟩

/-- **The transvection is not point-diagonal**, and not for any scaling `d : L → K`
whatsoever — no hypothesis on `d`. So the family of `offdiagonal` moves is genuinely
outside the reach of the no-go, which is what keeps the no-go non-vacuous. -/
theorem konckiFamily_not_diagonal {a b : L} {c : K} (hc : c ≠ 0) (hab : a ≠ b) (d : L → K) :
    ¬∀ x : L, konckiFamily a b c x = d x • (std x : L → K) := by
  intro h
  have hba : b ≠ a := Ne.symm hab
  have hb := congrFun (h a) b
  simp only [konckiFamily_self, Pi.add_apply, Pi.smul_apply, std, Pi.single_eq_of_ne hba,
    Pi.single_eq_same, smul_eq_mul, mul_one, mul_zero, zero_add] at hb
  exact hc hb

end OffDiagonal

/-- Rick's constant from the `N = 2` computation, email UID 824:
`c = q(1-q)/(1 - 1/(w₁w₂))`, which has a simple pole on the pair divisor `H₁₂`. -/
def cKoncki [Field K] (q w₁ w₂ : K) : K := q * (1 - q) / (1 - 1 / (w₁ * w₂))

theorem cKoncki_ne_zero [Field K] {q w₁ w₂ : K} (hq : q ≠ 0) (hq1 : 1 - q ≠ 0)
    (hden : 1 - 1 / (w₁ * w₂) ≠ 0) : cKoncki q w₁ w₂ ≠ 0 :=
  div_ne_zero (mul_ne_zero hq hq1) hden

/-- A concrete rational witness. The `𝔽₂` lesson: `q ≠ 0` and `1 - q ≠ 0` are *jointly
unsatisfiable* over `𝔽₂`, so a nonvanishing hypothesis has to be discharged at a named
point of a field big enough to carry it, not merely assumed. -/
theorem cKoncki_rat : cKoncki (2 : ℚ) 2 2 = -8 / 3 := by norm_num [cKoncki]

theorem cKoncki_rat_ne_zero : cKoncki (2 : ℚ) 2 2 ≠ 0 := by
  rw [cKoncki_rat]; norm_num

/-- **The two halves side by side, over `ℚ`, at a named point.**

An off-diagonal unipotent change of basis with Rick's constant moves exactly the `∅`
label, and is not a point-diagonal `Ψ_χ` for *any* `χ`. Together with
`no_point_diagonal_moves_exactly_a_pair` this says: the move Koncki's class requires
exists, and it is not in the point-diagonal family. -/
theorem offdiagonal_can_move_one_cell :
    konckiFamily (∅ : Finset ℕ) {1, 2} (cKoncki (2 : ℚ) 2 2) ∅ ≠ std ∅ ∧
      (∀ x : Finset ℕ, x ≠ ∅ →
        konckiFamily (∅ : Finset ℕ) {1, 2} (cKoncki (2 : ℚ) 2 2) x = std x) ∧
      ∀ χ : ℕ → ℚ, ¬∀ x : Finset ℕ,
        konckiFamily (∅ : Finset ℕ) {1, 2} (cKoncki (2 : ℚ) 2 2) x = Psi χ x • std x := by
  have hab : (∅ : Finset ℕ) ≠ ({1, 2} : Finset ℕ) := by decide
  refine ⟨konckiFamily_ne_std cKoncki_rat_ne_zero,
    fun x hx => konckiFamily_of_ne _ _ _ hx,
    fun χ => konckiFamily_not_diagonal cKoncki_rat_ne_zero hab (Psi χ)⟩

end TworowD4Kernel.PointDiagonal
