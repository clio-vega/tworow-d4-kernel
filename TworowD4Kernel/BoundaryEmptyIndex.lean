/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.RhoShiftVanishing
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Pi

/-!
# Q559's boundary case: the hypothesis that was never written

Formalises `prop:boundary` of
`projects/proofs/2026-10-23-Q559-vanishing-converse.tex` (Clio, 23 Oct 2026, L409–L418),
and the `⇐` direction of `cor:criterion` (L392–L406), at the determinant/alternant layer.

## The paper's statement

> **Proposition (the hypothesis `n ≥ r` is necessary).** If `n < r` then
> `Ψ^C_{(1^r),θ}(M) = 0` for every `θ`, including every `θ` with pairwise distinct
> ρ-shifts.
>
> *Proof.* There is no injection `h` from `r` slots into an `n`-element set, so the sum
> `eq:Psidef` is empty. (Equivalently, `M` has no `r`-subset in `thm:alt`.)

The proof has two readings, and the paper gives both: one over the head-injection index
set of the *definition* `eq:Psidef`, one over the `r`-subset index set of `thm:alt`. Both
are formalised below, because they are different Lean facts (pigeonhole, and
`powersetCard_eq_empty`) even though they are the same sentence.

## Why this target

Q559 as posed on 2026-10-22 **omitted** `n ≥ r`, and the `424/424` sample that graded the
conjecture drew `n ∈ r…r+2`, so it never reached `n < r`: the evidence was generated
inside the unwritten assumption and was therefore worth nothing on that axis. Lean is the
one instrument that cannot skip a binder. `psiAlt_eq_zero_of_card_lt` below is three
tactic steps — the measurement is that the omission was that cheap to force.

## Honest scope

* `thm:alt` — the passage from `eq:Psidef` to the alternant sum — is **not** formalised.
* `thm:main` (the non-vanishing induction, L358 ff.) is **not** formalised. It enters
  `criterion_iff` as an explicit hypothesis binder `hmain`, carrying `r ≤ M.card`
  *in the binder* rather than in prose. That binder is the whole point of the file.
* The ordering `x_1, …, x_r` of `T` "in increasing index order" (`thm:alt`) is abstracted
  as a parameter `ord`. This makes the vanishing statements *stronger* (they hold for
  every ordering convention) and keeps `T.card = r`'s dependent typing out of the sum.

**A Lean-verified summand is not a Lean-verified sum**: the parent registry node
`clio-Q553-vanishing-converse-Q559` stays at `proved`.
-/

namespace TworowD4Kernel.BoundaryEmptyIndex

open Finset
open TworowD4Kernel.RhoShiftVanishing

variable {ι : Type*} {K : Type*}

/-! ### Reading 1 of the paper's proof: `M` has no `r`-subset (`thm:alt`'s index set) -/

/-- The index set of `thm:alt` is literally empty when `n < r`. Mathlib:
`Finset.powersetCard_eq_empty`. -/
theorem powersetCard_eq_empty_of_card_lt (M : Finset ι) (r : ℕ) (h : M.card < r) :
    M.powersetCard r = ∅ :=
  Finset.powersetCard_eq_empty.2 h

/-- **`prop:boundary`, abstract form.** A sum over an empty index set is `0`, whatever the
summand. No hypothesis on the summand `f`, and — L4 — none on `M`. -/
theorem sum_powersetCard_eq_zero_of_card_lt [AddCommMonoid K] (M : Finset ι) (r : ℕ)
    (f : Finset ι → K) (h : M.card < r) :
    ∑ T ∈ M.powersetCard r, f T = 0 := by
  rw [powersetCard_eq_empty_of_card_lt M r h, Finset.sum_empty]

/-! ### Reading 2 of the paper's proof: there is no injection of `r` slots into `M`

This is the index set of the *definition* `eq:Psidef` (L112–L118): the sum there runs over
tuples `h = (h_1, …, h_r)` of **distinct** elements of `M`. -/

/-- The paper's own sentence: "there is no injection `h` from `r` slots into an
`n`-element set". Pigeonhole, via `Finset.card_le_card_of_injOn`. -/
theorem no_head_injection_of_card_lt (M : Finset ι) (r : ℕ) (h : M.card < r) :
    ¬ ∃ g : Fin r → ι, Function.Injective g ∧ ∀ j, g j ∈ M := by
  rintro ⟨g, hinj, hmem⟩
  have hle : (Finset.univ : Finset (Fin r)).card ≤ M.card :=
    Finset.card_le_card_of_injOn g (fun j _ => hmem j) (fun a _ b _ hab => hinj hab)
  rw [Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The head-injection index set of `eq:Psidef`, as a `Finset`. -/
def headInjections [DecidableEq ι] (M : Finset ι) (r : ℕ) : Finset (Fin r → ι) :=
  (Fintype.piFinset fun _ : Fin r => M).filter Function.Injective

/-- `eq:Psidef`'s index set is empty when `n < r`. -/
theorem headInjections_eq_empty_of_card_lt [DecidableEq ι] (M : Finset ι) (r : ℕ)
    (h : M.card < r) : headInjections M r = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro g hg
  rw [headInjections, Finset.mem_filter, Fintype.mem_piFinset] at hg
  exact no_head_injection_of_card_lt M r h ⟨g, hg.2, hg.1⟩

/-- **`prop:boundary`, head-injection form.** The defining sum of `eq:Psidef` is empty. -/
theorem sum_headInjections_eq_zero_of_card_lt [DecidableEq ι] [AddCommMonoid K]
    (M : Finset ι) (r : ℕ) (f : (Fin r → ι) → K) (h : M.card < r) :
    ∑ g ∈ headInjections M r, f g = 0 := by
  rw [headInjections_eq_empty_of_card_lt M r h, Finset.sum_empty]

/-! ### The alternant sum of `thm:alt`, and both vanishing arms on it -/

/-- The alternant sum of `thm:alt` (L129–L144): `∑_{T ⊆ M, |T| = r} B(T) · det(x_i^{m_j}) / V(T)`,
with the ordering of each `T` abstracted as `ord` (see the module docstring). -/
noncomputable def psiAlt [Field K] (M : Finset ι) (r : ℕ) (x : ι → K)
    (B V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) : K :=
  ∑ T ∈ M.powersetCard r,
    B T * ((Matrix.of fun i j => x (ord T i) ^ rhoShift θ j).det / V T)

variable [Field K]

/-- **Arm 1 — `prop:boundary`.** `n < r ⇒ Ψ = 0`, because the index set is empty.
Three steps. This is the whole finding: the missing hypothesis was one `omega` away from
being forced, and no sample drawn from `n ∈ r…r+2` could ever have seen it. -/
theorem psiAlt_eq_zero_of_card_lt (M : Finset ι) (r : ℕ) (x : ι → K)
    (B V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) (h : M.card < r) :
    psiAlt M r x B V ord θ = 0 :=
  sum_powersetCard_eq_zero_of_card_lt M r _ h

/-- **Arm 2 — `thm:vanish`**, lifted from one determinant to the whole sum.
The determinant half is `det_zpow_eq_zero_of_not_injective` of `RhoShiftVanishing`. -/
theorem psiAlt_eq_zero_of_not_injective (M : Finset ι) (r : ℕ) (x : ι → K)
    (B V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ)
    (hθ : ¬ Function.Injective (rhoShift θ)) :
    psiAlt M r x B V ord θ = 0 := by
  refine Finset.sum_eq_zero fun T _ => ?_
  rw [det_zpow_eq_zero_of_not_injective (fun i => x (ord T i)) (rhoShift θ) hθ]
  simp

/-- **`cor:criterion`, the `⇐` direction**, as a single proposition: the two sufficient
conditions for vanishing, with the paper's `j < k` hypothesis verbatim. -/
theorem psiAlt_eq_zero_of_criterion (M : Finset ι) (r : ℕ) (x : ι → K)
    (B V : Finset ι → K) (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ)
    (h : M.card < r ∨ ∃ j k : Fin r, j < k ∧ θ j - θ k = (k.val : ℤ) - (j.val : ℤ)) :
    psiAlt M r x B V ord θ = 0 := by
  rcases h with h | h
  · exact psiAlt_eq_zero_of_card_lt M r x B V ord θ h
  · exact psiAlt_eq_zero_of_not_injective M r x B V ord θ
      ((exists_rhoTie_iff_not_injective θ).1 ((rhoTie_lt_iff_ne θ).1 h))

/-- **`cor:criterion` in full**, with `thm:main` as an explicit hypothesis.

`hmain` is the unformalised half (the induction of L358 ff.). What matters is where its
`r ≤ M.card` lives: **in the binder**, not in the surrounding prose. The equivalence then
holds, and `n < r` appears on the right-hand side as a genuine disjunct rather than as an
unstated side condition. -/
theorem criterion_iff (M : Finset ι) (r : ℕ) (x : ι → K)
    (B V : Finset ι → K) (ord : Finset ι → Fin r → ι)
    (hmain : ∀ θ : Fin r → ℤ, r ≤ M.card → Function.Injective (rhoShift θ) →
      psiAlt M r x B V ord θ ≠ 0) (θ : Fin r → ℤ) :
    psiAlt M r x B V ord θ = 0 ↔ (M.card < r ∨ ¬ Function.Injective (rhoShift θ)) := by
  constructor
  · intro hz
    by_contra hc
    push Not at hc
    exact hmain θ hc.1 hc.2 hz
  · intro h
    rcases h with h | h
    · exact psiAlt_eq_zero_of_card_lt M r x B V ord θ h
    · exact psiAlt_eq_zero_of_not_injective M r x B V ord θ h

/-! ### The lesion table

Predictions were written to
`projects/proofs/2026-10-23-c2-lean-Q559-boundary-case.md` **before** this section
compiled. Each lesion below is a Lean declaration, so the grade is the build, not my
recollection of the build.
-/

/-- **L1 — `r ≤ M.card` is IRREMOVABLE from `thm:main`.**

An `hmain` stated *without* the card hypothesis is not merely unproved, it is
**inconsistent**: the witness is `r = 1`, `M = ∅`, `θ = 0`, whose ρ-shift is injective
(vacuously, `Fin 1` being a subsingleton) while the alternant sum is empty. This is
`prop:boundary` doing exactly the job the paper claims for it. -/
theorem main_without_card_hypothesis_is_false
    (hmain' : ∀ (M : Finset ℕ) (θ : Fin 1 → ℤ), Function.Injective (rhoShift θ) →
      psiAlt M 1 (fun t => (t : ℚ)) (fun _ => 1) (fun _ => 1) (fun _ _ => 0) θ ≠ 0) :
    False := by
  refine hmain' ∅ 0 (fun a b _ => Subsingleton.elim a b) ?_
  exact psiAlt_eq_zero_of_card_lt _ _ _ _ _ _ _ (by simp)

/-- **L2, positive half.** For `r ≥ 1` the two spellings of the boundary hypothesis agree. -/
theorem card_lt_iff_le_pred (n r : ℕ) (hr : 0 < r) : n < r ↔ n ≤ r - 1 := by omega

/-- **L2, the split.** At `r = 0` they do **not** agree: `ℕ`-truncation turns `n ≤ r - 1`
into `n ≤ 0`, which holds at `n = 0`, while `0 < 0` fails. So `M.card ≤ r - 1` is the
*wrong* spelling of `prop:boundary` — it would claim vanishing at `r = 0, M = ∅`, where
`Ψ_{(1^0)}` is the empty product. A quantifier range carrying a hypothesis, again. -/
theorem card_lt_iff_le_pred_fails_at_rank_zero : ¬ ((0 : ℕ) < 0 ↔ (0 : ℕ) ≤ 0 - 1) := by
  decide

/-- **L3 — the `r = 0` edge.** The alternant sum at rank `0` is the single term `T = ∅`
with a `0 × 0` determinant, i.e. the empty product, **not** `0`. -/
theorem psiAlt_rank_zero (M : Finset ι) (x : ι → K) (B V : Finset ι → K)
    (ord : Finset ι → Fin 0 → ι) (θ : Fin 0 → ℤ) :
    psiAlt M 0 x B V ord θ = B ∅ * (1 / V ∅) := by
  rw [psiAlt, Finset.powersetCard_zero, Finset.sum_singleton, Matrix.det_fin_zero]

/-- **L3, the grade: ABSENT (vacuous).** `prop:boundary` never *claims* anything at
`r = 0`, because its hypothesis is unsatisfiable there. So the statement is not wrong at
`r = 0`; it is silent. -/
theorem card_lt_zero_is_unsatisfiable (M : Finset ι) : ¬ M.card < 0 := by omega

/-- **L3, non-vacuity control.** And the value at `r = 0` really is `1 ≠ 0`, so a
statement that *did* claim vanishing at `r = 0` would be false. -/
theorem psiAlt_rank_zero_eq_one (M : Finset ℕ) :
    psiAlt M 0 (fun t => (t : ℚ)) (fun _ => 1) (fun _ => 1) (fun _ _ => 0) 0 = 1 := by
  rw [psiAlt_rank_zero]; norm_num

/-- **The pair {L1, L3}** — lesion the pairs, not the marginals (22 Oct: two hypotheses
each Lean-verified removable and jointly false).

Here the pair comes out the *other* way: at `r = 0` the lesioned `hmain'` of L1 is
**true**, so dropping `r ≤ M.card` is harmless at rank `0`. L1's irremovability is
therefore witnessed only at `r ≥ 1`, and the two lesions are jointly consistent. -/
theorem main_without_card_hypothesis_holds_at_rank_zero (M : Finset ℕ) (θ : Fin 0 → ℤ) :
    psiAlt M 0 (fun t => (t : ℚ)) (fun _ => 1) (fun _ => 1) (fun _ _ => 0) θ ≠ 0 := by
  rw [psiAlt_rank_zero]; norm_num

/-- **L4 — `M` nonempty is ABSENT.** `prop:boundary` applies at `M = ∅`; indeed that is
where L1's witness lives. Note `sum_powersetCard_eq_zero_of_card_lt` carries no
nonemptiness binder at all. -/
theorem psiAlt_eq_zero_at_empty (r : ℕ) (hr : 0 < r) (x : ι → K) (B V : Finset ι → K)
    (ord : Finset ι → Fin r → ι) (θ : Fin r → ℤ) :
    psiAlt (∅ : Finset ι) r x B V ord θ = 0 :=
  psiAlt_eq_zero_of_card_lt _ _ _ _ _ _ _ (by simpa using hr)

/-! ### Positive controls: `psiAlt` is not identically zero

Every lesion above confirmed on the first build. That is the pattern that should be
distrusted, so: all four grades would also hold of a `psiAlt` that were *constantly* `0`,
in which case arm 1 would be a theorem about nothing. These two controls separate that.
-/

/-- **Control C1.** At `r = 1`, `M = {5}`, `θ = (3)` the alternant sum is the single term
`5^{m_1} = 5^2 = 25`, computed directly from the definition — not via any theorem above.
So `psiAlt` genuinely evaluates its summand, and `psiAlt_eq_zero_of_card_lt` is not
vacuous. -/
theorem control_psiAlt_rank_one :
    psiAlt ({5} : Finset ℕ) 1 (fun t => (t : ℚ)) (fun _ => 1) (fun _ => 1)
      (fun _ _ => 5) (fun _ => 3) = 25 := by
  rw [psiAlt]
  rw [show ({5} : Finset ℕ).powersetCard 1 = {{5}} by decide]
  rw [Finset.sum_singleton, Matrix.det_fin_one]
  norm_num [rhoShift]

/-- **Control C2 (the separating one).** At that same point *neither* disjunct of
`cor:criterion` holds — `M.card = 1 = r` so `M.card < r` fails, and `rhoShift θ` is
injective — and the value is nonzero. So the right-hand side of `criterion_iff` is not
always true, and arm 1's hypothesis `M.card < r` is carrying load rather than being
satisfied for free. -/
theorem control_criterion_rhs_fails :
    ¬ (({5} : Finset ℕ).card < 1 ∨
        ¬ Function.Injective (rhoShift (r := 1) (fun _ => (3 : ℤ)))) ∧
      psiAlt ({5} : Finset ℕ) 1 (fun t => (t : ℚ)) (fun _ => 1) (fun _ => 1)
        (fun _ _ => 5) (fun _ => 3) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rintro (h | h)
    · simp at h
    · exact h (fun a b _ => Subsingleton.elim a b)
  · rw [control_psiAlt_rank_one]; norm_num

end TworowD4Kernel.BoundaryEmptyIndex
