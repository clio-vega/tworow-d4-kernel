/-
Copyright (c) 2026 Clio. All rights reserved.
-/
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Set.Card

/-!
# The ε-profile is a Möbius transform of the indicator of the multiplicity set

Formalisation of `thm:profile` from
`proofs/2026-10-22-boundary-valuation-two-term.tex` (PROVE 2026-10-22, answering **Q546**).

## The paper statement

For a finite set `M` of positive integers and `ε_d` a primitive `d`-th root of unity,
the *ε-profile* is
```
  f_M(d) := #{a ∈ M : ε_d ^ a = 1} = #(M ∩ dℤ),
```
well defined because `ε_d ^ a = 1 ↔ d ∣ a` depends only on `d`.  The paper's theorem is the
explicit inversion
```
  1_M(n) = Σ_{k ≥ 1} μ(k) · f_M(k·n)        (n ≥ 1),
```
from which "the profile determines `M`" follows.  The root-of-unity layer is *not*
formalised here: `ε_d ^ a = 1 ↔ d ∣ a` is the standard order characterisation, and the
paper's own proof immediately discards it in favour of the divisibility statement.  What
carries the mathematical weight — and what Mathlib does *not* contain — is the
sum-over-**multiples** Möbius inversion.  Mathlib has only the sum-over-**divisors** form
(`ArithmeticFunction.moebius_mul_coe_zeta`); `moebius_inversion_over_multiples` below is
the transposed statement, proved from it.

## Main results

* `sum_divisors_moebius` — `Σ_{k ∣ j} μ k = [j = 1]`, extracted from Mathlib.
* `moebius_inversion_over_multiples` — the engine: for any `G : ℕ → ℤ`,
  `Σ_{k ∈ [1,B]} μ k · (Σ_{a ∈ [1,B], k·n ∣ a} G a) = G n` whenever `n ∈ [1,B]`.
* `indicator_eq_sum_moebius_profile` — the paper's displayed inversion for `G = 1_M`.
* `eq_of_profile_eq` — the brief's target: the profile determines `M`.

The multiplicity set of the application is `M_m(X) = {a > 0 : a·t_m ∈ Δ⁺(X_N)}`, with
`M(B) = {1}`, `M(C) = {2}`, `M(BC) = {1,2}`; see `profile_typeB`, `profile_typeC`,
`profile_typeBC` and `separates_BC` for the three-element case the application needs.
-/

namespace TworowD4Kernel.ProfileMoebius

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

/-- `Σ_{k ∣ j} μ k = [j = 1]`.  This is `ArithmeticFunction.moebius_mul_coe_zeta` read at a
point; it holds for `j = 0` too, both sides being `0` (`Nat.divisors 0 = ∅`). -/
lemma sum_divisors_moebius (j : ℕ) :
    ∑ k ∈ j.divisors, μ k = if j = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply (f := (μ : ArithmeticFunction ℤ)), moebius_mul_coe_zeta, one_apply]

/-- **The engine.**  Möbius inversion for the sum-over-multiples transform, in the finite
window `[1,B]`.  This is the second display of `thm:profile`; the paper's proof is the
reindexing `Σ_k μ(k) Σ_{kn ∣ n'} G = Σ_{n ∣ n'} G · Σ_{k ∣ n'/n} μ(k)`, which is exactly
the `Finset.sum_comm` below followed by `sum_divisors_moebius`. -/
theorem moebius_inversion_over_multiples (B : ℕ) (G : ℕ → ℤ) {n : ℕ}
    (hn1 : 1 ≤ n) (hnB : n ≤ B) :
    ∑ k ∈ Icc 1 B, (μ k) * (∑ a ∈ (Icc 1 B).filter (fun a => k * n ∣ a), G a) = G n := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn1
  -- push `μ k` inside and drop the filters in favour of `if`s
  have step1 : ∀ k ∈ Icc 1 B,
      (μ k) * (∑ a ∈ (Icc 1 B).filter (fun a => k * n ∣ a), G a)
        = ∑ a ∈ Icc 1 B, (if k * n ∣ a then (μ k) * G a else 0) := by
    intro k _
    rw [Finset.sum_filter, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [mul_ite, mul_zero]
  rw [Finset.sum_congr rfl step1, Finset.sum_comm]
  -- for each `a`, the inner sum over `k` is `(Σ_{k ∣ a/n} μ k) * G a`
  have step2 : ∀ a ∈ Icc 1 B,
      (∑ k ∈ Icc 1 B, (if k * n ∣ a then (μ k) * G a else 0))
        = if a = n then G a else 0 := by
    intro a ha
    simp only [Finset.mem_Icc] at ha
    obtain ⟨ha1, haB⟩ := ha
    have ha0 : a ≠ 0 := Nat.one_le_iff_ne_zero.mp ha1
    rw [← Finset.sum_filter]
    by_cases hdvd : n ∣ a
    · -- the index set is exactly `divisors (a/n)`
      obtain ⟨j, hj⟩ := hdvd
      have hj0 : j ≠ 0 := by rintro rfl; rw [Nat.mul_zero] at hj; exact ha0 hj
      have hset : (Icc 1 B).filter (fun k => k * n ∣ a) = j.divisors := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hk1, -⟩, hk⟩
          refine ⟨?_, hj0⟩
          rw [hj] at hk
          exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hn0)).mp
            (by rwa [mul_comm k n] at hk)
        · rintro ⟨hk, -⟩
          have hkj : k ≤ j := Nat.le_of_dvd (Nat.pos_of_ne_zero hj0) hk
          have hja : j ≤ a := by
            rw [hj]; exact Nat.le_mul_of_pos_left j (Nat.pos_of_ne_zero hn0)
          refine ⟨⟨?_, hkj.trans (hja.trans haB)⟩, ?_⟩
          · rcases Nat.eq_zero_or_pos k with rfl | hpos
            · exact absurd (Nat.eq_zero_of_zero_dvd hk) hj0
            · exact hpos
          · rw [hj, mul_comm n j]; exact mul_dvd_mul_right hk n
      rw [hset, ← Finset.sum_mul, sum_divisors_moebius]
      by_cases hj1 : j = 1
      · have han : a = n := by rw [hj, hj1, mul_one]
        rw [if_pos hj1, if_pos han, one_mul]
      · have hne : a ≠ n := by
          rw [hj]; intro h
          exact hj1 (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn0)
            (by rw [h, mul_one]))
        rw [if_neg hj1, if_neg hne, zero_mul]
    · -- no `k` contributes, and `a ≠ n`
      have hempty : (Icc 1 B).filter (fun k => k * n ∣ a) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro k _ hk
        exact hdvd (dvd_trans (dvd_mul_left n k) hk)
      have hne : a ≠ n := fun h => hdvd (h ▸ dvd_rfl)
      rw [hempty, Finset.sum_empty, if_neg hne]
  rw [Finset.sum_congr rfl step2]
  simp [Finset.sum_ite_eq', Finset.mem_Icc, hn1, hnB]

/-! ### The ε-profile and the inversion of `thm:profile` -/

/-- The **ε-profile** of a finite multiplicity set `M`:
`f_M(d) = #{a ∈ M : ε_d ^ a = 1} = #(M ∩ dℤ)`.

The identification of the two descriptions is the first display of `thm:profile` and is
*definitional here*: we take `#(M ∩ dℤ)` as the definition, since `ε_d ^ a = 1 ↔ d ∣ a` is
the standard order characterisation and the paper discards it immediately.  The
root-of-unity layer is deliberately outside this formalisation (see module docstring). -/
def profile (M : Finset ℕ) (d : ℕ) : ℕ := (M.filter (fun a => d ∣ a)).card

/-- Restricting the ambient window to `[1,B]` does not change the profile of an
`M ⊆ [1,B]`. -/
lemma filter_filter_mem {B : ℕ} {M : Finset ℕ} (hM : M ⊆ Icc 1 B) (d : ℕ) :
    (((Icc 1 B).filter (fun a => d ∣ a)).filter (fun a => a ∈ M))
      = M.filter (fun a => d ∣ a) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨-, hd⟩, hm⟩
    exact ⟨hm, hd⟩
  · rintro ⟨hm, hd⟩
    have h := hM hm
    simp only [Finset.mem_Icc] at h
    exact ⟨⟨h, hd⟩, hm⟩

/-- **`thm:profile`, second display.**  `1_M(n) = Σ_{k ≥ 1} μ(k) · f_M(k·n)` for `n ≥ 1`,
with the infinite sum realised in the finite window `[1,B]` that contains `M` (the paper's
"the sum being finite because `M` is finite"). -/
theorem indicator_eq_sum_moebius_profile {B : ℕ} {M : Finset ℕ} (hM : M ⊆ Icc 1 B)
    {n : ℕ} (hn1 : 1 ≤ n) (hnB : n ≤ B) :
    ∑ k ∈ Icc 1 B, (μ k) * (profile M (k * n) : ℤ) = if n ∈ M then (1 : ℤ) else 0 := by
  have key := moebius_inversion_over_multiples B (fun a => if a ∈ M then (1 : ℤ) else 0) hn1 hnB
  rw [show (if n ∈ M then (1 : ℤ) else 0)
        = (fun a => if a ∈ M then (1 : ℤ) else 0) n from rfl, ← key]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [Finset.sum_boole, filter_filter_mem hM, profile]

/-- The profile is supported in `[1, max M]`: `f_M(d) = 0` once `d` exceeds every element
of `M`.  This is what makes the window `[1,B]` above lossless. -/
lemma profile_eq_zero_of_lt {M : Finset ℕ} {d : ℕ} (hM : ∀ a ∈ M, 1 ≤ a)
    (hd : ∀ a ∈ M, a < d) : profile M d = 0 := by
  rw [profile, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro a ha hdvd
  exact absurd (Nat.le_of_dvd (hM a ha) hdvd) (not_le.mpr (hd a ha))

/-- **The target of the LEAN brief, and `thm:profile`'s "determine one another".**
The ε-profile determines the multiplicity set: two finite sets of *positive* integers with
equal profiles at every `d ≥ 1` are equal. -/
theorem eq_of_profile_eq {M M' : Finset ℕ} (hM : ∀ a ∈ M, 1 ≤ a) (hM' : ∀ a ∈ M', 1 ≤ a)
    (h : ∀ d, 1 ≤ d → profile M d = profile M' d) : M = M' := by
  set B := (M ∪ M').sup id with hBdef
  have hsub : ∀ {S : Finset ℕ}, (∀ a ∈ S, 1 ≤ a) → S ⊆ M ∪ M' → S ⊆ Icc 1 B := by
    intro S hS hSU a ha
    simp only [Finset.mem_Icc]
    exact ⟨hS a ha, Finset.le_sup (f := id) (hSU ha)⟩
  have hsubM : M ⊆ Icc 1 B := hsub hM Finset.subset_union_left
  have hsubM' : M' ⊆ Icc 1 B := hsub hM' Finset.subset_union_right
  ext n
  by_cases hn1 : 1 ≤ n
  · by_cases hnB : n ≤ B
    · have e1 := indicator_eq_sum_moebius_profile hsubM hn1 hnB
      have e2 := indicator_eq_sum_moebius_profile hsubM' hn1 hnB
      have hsum : (if n ∈ M then (1 : ℤ) else 0) = (if n ∈ M' then (1 : ℤ) else 0) := by
        rw [← e1, ← e2]
        refine Finset.sum_congr rfl fun k hk => ?_
        simp only [Finset.mem_Icc] at hk
        rw [h (k * n) (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hk.1) (Nat.one_le_iff_ne_zero.mp hn1)))]
      by_cases hm : n ∈ M <;> by_cases hm' : n ∈ M' <;> simp_all
    · constructor
      · intro hm; exact absurd (Finset.le_sup (f := id) (Finset.mem_union_left _ hm)) hnB
      · intro hm; exact absurd (Finset.le_sup (f := id) (Finset.mem_union_right _ hm)) hnB
  · constructor
    · intro hm; exact absurd (hM n hm) hn1
    · intro hm; exact absurd (hM' n hm) hn1

/-! ### The application: `M(B) = {1}`, `M(C) = {2}`, `M(BC) = {1,2}` -/

/-- Type `B_N`: the multiplicity set is `{1}`, with two-point profile `(1,0)`. -/
lemma profile_typeB_pair : profile {1} 1 = 1 ∧ profile {1} 2 = 0 := by decide

/-- Type `C_N`: the multiplicity set is `{2}`, with two-point profile `(1,1)`. -/
lemma profile_typeC_pair : profile {2} 1 = 1 ∧ profile {2} 2 = 1 := by decide

/-- Type `BC_N` (non-reduced): the multiplicity set is `{1,2}`, two-point profile `(2,1)`. -/
lemma profile_typeBC_pair : profile {1, 2} 1 = 2 ∧ profile {1, 2} 2 = 1 := by decide

/-- `f` is **additive** in `M`: `f_BC = f_B + f_C`, not `2 · f_B`.  At `d = 2` this reads
`1 = 0 + 1 ≠ 2 · 0` — the cell of the table that killed the multiplicative guess of Q544. -/
lemma profile_additive_typeBC (d : ℕ) :
    profile {1, 2} d = profile {1} d + profile {2} d := by
  rcases Nat.eq_zero_or_pos d with rfl | _
  · decide
  · rw [profile, profile, profile]
    rw [show ({1, 2} : Finset ℕ) = {1} ∪ {2} from rfl, Finset.filter_union]
    rw [Finset.card_union_of_disjoint]
    exact Finset.disjoint_filter_filter (by decide)

/-- **`cor:q546yes`, the arithmetic half.**  Two points suffice on the class the
application lives in: the profile at `d = 1, 2` separates every subset of `{1,2}`, hence
separates `B / C / BC`.  Decided over the whole powerset — four sets, sixteen pairs. -/
theorem two_points_suffice :
    ∀ M ∈ ({1, 2} : Finset ℕ).powerset, ∀ M' ∈ ({1, 2} : Finset ℕ).powerset,
      profile M 1 = profile M' 1 → profile M 2 = profile M' 2 → M = M' := by decide

/-- **`cor:q546yes`, the sharpness half.**  Outside `M ⊆ {1,2}` two points no longer
suffice: `{1}` and `{3}` share `(f(1), f(2)) = (1,0)` and separate first at `d = 3`. -/
theorem two_points_insufficient :
    profile {1} 1 = profile {3} 1 ∧ profile {1} 2 = profile {3} 2 ∧
      profile {1} 3 ≠ profile {3} 3 := by decide

/-! ### Lesion register

Verdicts pre-registered in `proofs/2026-10-22-lean-PREREG.md` *before* this module was
built.  Every verdict below is settled by a **proof** — a removability by a proof of the
weakened statement, an irremovability by an exhibited **witness** — never by the absence of
an error, since a surviving lesion and an absent binder give the same green build. -/

/-- **L2, pre-registered REMOVABLE — confirmed.**  Positivity of the elements deletes:
the profile determines an arbitrary `M : Finset ℕ`, `0` allowed.  The brief expected this
one to bite, because `d ∣ 0` puts `0` in *every* fibre.  That is exactly what exposes it:
at `d = B+1`, `B = max (M ∪ M')`, the fibre is `(M ∪ M') ∩ {0}`, so the profile reads off
`0`'s membership directly, and the positive part is handled by `eq_of_profile_eq` after
erasing `0`.  Unbounded `d` is what makes this work — see
`range_union_insufficient_when_zero_allowed` for the interaction. -/
theorem eq_of_profile_eq_zero_allowed {M M' : Finset ℕ}
    (h : ∀ d, 1 ≤ d → profile M d = profile M' d) : M = M' := by
  set B := (M ∪ M').sup id with hBdef
  -- `0`'s membership is read off at `d = B + 1`
  have hzero : ∀ {S : Finset ℕ}, S ⊆ M ∪ M' →
      profile S (B + 1) = if 0 ∈ S then 1 else 0 := by
    intro S hS
    have hfil : S.filter (fun a => (B + 1) ∣ a) = S.filter (fun a => a = 0) := by
      ext a
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨ha, hd⟩
        refine ⟨ha, ?_⟩
        by_contra hne
        have h1 := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd
        have h2 : a ≤ B := Finset.le_sup (f := id) (hS ha)
        omega
      · rintro ⟨ha, rfl⟩
        exact ⟨ha, dvd_zero _⟩
    rw [profile, hfil, Finset.filter_eq']
    split <;> simp
  have h0 : (0 ∈ M) ↔ (0 ∈ M') := by
    have e := h (B + 1) (by omega)
    rw [hzero Finset.subset_union_left, hzero Finset.subset_union_right] at e
    by_cases a : 0 ∈ M <;> by_cases b : 0 ∈ M' <;> simp_all
  -- erasing `0` shifts every positive-`d` profile by the same constant
  have herase : ∀ {S : Finset ℕ} {d : ℕ}, 1 ≤ d →
      profile S d = profile (S.erase 0) d + (if 0 ∈ S then 1 else 0) := by
    intro S d _
    rw [profile, profile, Finset.filter_erase]
    by_cases hz : 0 ∈ S
    · have hmem : 0 ∈ S.filter (fun a => d ∣ a) := by
        simp only [Finset.mem_filter]
        exact ⟨hz, dvd_zero _⟩
      have hpos := Finset.card_pos.mpr ⟨0, hmem⟩
      rw [Finset.card_erase_of_mem hmem, if_pos hz]
      omega
    · have hnot : 0 ∉ S.filter (fun a => d ∣ a) := by
        simp only [Finset.mem_filter]
        exact fun hc => hz hc.1
      rw [Finset.erase_eq_of_notMem hnot, if_neg hz, Nat.add_zero]
  have hplus : ∀ d, 1 ≤ d → profile (M.erase 0) d = profile (M'.erase 0) d := by
    intro d hd
    have e := h d hd
    rw [herase (S := M) hd, herase (S := M') hd] at e
    by_cases a : 0 ∈ M
    · have b : 0 ∈ M' := h0.mp a
      rw [if_pos a, if_pos b] at e
      omega
    · have b : 0 ∉ M' := fun hb => a (h0.mpr hb)
      rw [if_neg a, if_neg b] at e
      omega
  have hkey := eq_of_profile_eq
    (fun a ha => Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase ha))
    (fun a ha => Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase ha)) hplus
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact h0
  constructor
  · intro hm
    have hx : n ∈ M.erase 0 := Finset.mem_erase.mpr ⟨by omega, hm⟩
    rw [hkey] at hx
    exact Finset.mem_of_mem_erase hx
  · intro hm
    have hx : n ∈ M'.erase 0 := Finset.mem_erase.mpr ⟨by omega, hm⟩
    rw [← hkey] at hx
    exact Finset.mem_of_mem_erase hx

/-- **L3(a), pre-registered REMOVABLE/equivalent — confirmed.**  The quantifier range
`∀ d ≥ 1` may be cut down to the finite window `d ∈ [1, max (M ∪ M')]` with no loss: above
the window both profiles vanish (`profile_eq_zero_of_lt`).  Note the *proof* of
`indicator_eq_sum_moebius_profile` evaluates the profile as high as `B²`, so this is not
the vacuous reading — the surplus values are supplied by the vanishing lemma, not unused. -/
theorem eq_of_profile_eq_restricted {M M' : Finset ℕ} (hM : ∀ a ∈ M, 1 ≤ a)
    (hM' : ∀ a ∈ M', 1 ≤ a)
    (h : ∀ d ∈ Icc 1 ((M ∪ M').sup id), profile M d = profile M' d) : M = M' := by
  refine eq_of_profile_eq hM hM' fun d hd => ?_
  by_cases hdB : d ≤ (M ∪ M').sup id
  · exact h d (Finset.mem_Icc.mpr ⟨hd, hdB⟩)
  · rw [profile_eq_zero_of_lt hM (fun a ha => lt_of_le_of_lt
        (Finset.le_sup (f := id) (Finset.mem_union_left _ ha)) (not_le.mp hdB)),
      profile_eq_zero_of_lt hM' (fun a ha => lt_of_le_of_lt
        (Finset.le_sup (f := id) (Finset.mem_union_right _ ha)) (not_le.mp hdB))]

/-- **L3(b), pre-registered IRREMOVABLE — confirmed, with witness.**  Cutting the range to
`[1, max M]` — one side only, rather than the union — is *not* equivalent: `M = ∅` has
`max M = 0`, so the range is empty and the hypothesis is vacuous. -/
theorem range_max_left_insufficient :
    ∃ M M' : Finset ℕ, (∀ a ∈ M, 1 ≤ a) ∧ (∀ a ∈ M', 1 ≤ a) ∧
      (∀ d ∈ Icc 1 (M.sup id), profile M d = profile M' d) ∧ M ≠ M' :=
  ⟨∅, {5}, by simp, by decide, by simp, by decide⟩

/-- **L3', the pre-registered INTERACTION — confirmed.**  L2 and L3(a) are each survivable
and **jointly fatal**: once `0` is admitted, the window `[1, max (M ∪ M')]` collapses on
`M = {0}`, `M' = ∅` (the max is `0`, so the range is empty) and the conclusion fails.  A
lesion pass that deletes one hypothesis at a time grades both REMOVABLE and misses this. -/
theorem range_union_insufficient_when_zero_allowed :
    ∃ M M' : Finset ℕ,
      (∀ d ∈ Icc 1 ((M ∪ M').sup id), profile M d = profile M' d) ∧ M ≠ M' :=
  ⟨{0}, ∅, by simp, by decide⟩

/-- The `Set`-valued profile, for the L1 lesion only. -/
noncomputable def setProfile (M : Set ℕ) (d : ℕ) : ℕ := Set.ncard (M ∩ {a : ℕ | d ∣ a})

/-- **L1, pre-registered IRREMOVABLE (and a junk-value *counterexample*, not a junk-value
false removability) — confirmed.**  Finiteness is carried by the *type* `Finset ℕ`, so
there is no binder to delete; restating over `Set ℕ` with `Set.ncard` makes the theorem
**false**, because `Set.ncard` of an infinite set is the junk value `0`, so every fibre of
both sets reads `0`.  Witness: the positive integers versus the positive even integers. -/
theorem finiteness_irremovable :
    ∃ M M' : Set ℕ, (∀ a ∈ M, 1 ≤ a) ∧ (∀ a ∈ M', 1 ≤ a) ∧
      (∀ d, 1 ≤ d → setProfile M d = setProfile M' d) ∧ M ≠ M' := by
  -- a shared witness family: the multiples of `2d`, which lie in both fibres
  have hinj : ∀ d : ℕ, 1 ≤ d → Function.Injective (fun k : ℕ => (k + 1) * (2 * d)) := by
    intro d hd x y hxy
    have h2d : 0 < 2 * d := by omega
    exact Nat.succ_injective (Nat.eq_of_mul_eq_mul_right h2d hxy)
  refine ⟨{a | 1 ≤ a}, {a | 1 ≤ a ∧ 2 ∣ a}, fun a ha => ha, fun a ha => ha.1, ?_, ?_⟩
  · intro d hd
    have hmem : ∀ k : ℕ, 1 ≤ (k + 1) * (2 * d) ∧ 2 ∣ (k + 1) * (2 * d)
        ∧ d ∣ (k + 1) * (2 * d) := by
      intro k
      refine ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_, ?_⟩
      · exact ⟨(k + 1) * d, by ring⟩
      · exact ⟨2 * (k + 1), by ring⟩
    have hinf1 : ({a | 1 ≤ a} ∩ {a : ℕ | d ∣ a}).Infinite :=
      Set.infinite_of_injective_forall_mem (hinj d hd)
        (fun k => ⟨(hmem k).1, (hmem k).2.2⟩)
    have hinf2 : ({a | 1 ≤ a ∧ 2 ∣ a} ∩ {a : ℕ | d ∣ a}).Infinite :=
      Set.infinite_of_injective_forall_mem (hinj d hd)
        (fun k => ⟨⟨(hmem k).1, (hmem k).2.1⟩, (hmem k).2.2⟩)
    rw [setProfile, setProfile, Set.Infinite.ncard hinf1, Set.Infinite.ncard hinf2]
  · intro hcon
    have h1 : (1 : ℕ) ∈ ({a | 1 ≤ a ∧ 2 ∣ a} : Set ℕ) := by
      rw [← hcon]; exact le_refl 1
    exact absurd h1.2 (by decide)

end TworowD4Kernel.ProfileMoebius
