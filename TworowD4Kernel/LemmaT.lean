/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Tactic

/-!
# Lemma T: the two sign lemmas on one interior antidiagonal

Formalises the two lemmas of `proofs/2026-09-30-c2-lemma-T.tex` that carry a *because*:

* `lem_signs` — Lemma `lem:signs` (l.166): assuming `(INT)`, `l ≤ 0 ≤ r`.  This is where `Φ`'s
  `1`-Lipschitz hypothesis is spent, and it is spent exactly once.  The paper's proof turns on
  "`(i₀-1, x₁+1)` lies in the box, so `v_{i₀-1}` is **defined**".  With total functions `ℤ → ℤ`
  definedness is free, so that step would be invisible; it is made Lean-visible by restricting
  every hypothesis (`Φ_lip`, `Φ_concave`, `Ψ_lip`, `Ψ_convex`, `supp`) to the box.  `(INT)` is
  then genuinely load-bearing twice: it puts `i₀-1` and `i₁+1` inside the box so that `supp`
  applies there (giving `v (i₀-1) ≤ 0`, `v (i₁+1) ≤ 0`), and it puts `i₀` and `i₁+1` inside the
  range where `Φ_lip` applies.
* `lem_offJ_lower`, `lem_offJ_upper` — Lemma `lem:offJ` (l.238).  This lemma exists because the
  `.tex` originally justified these two cells *"by the decay lemma"*, and `v_i` is **undefined**
  off `J`, so that lemma has no object there.  The real reason is the `key_r` / `key_l`
  inequalities: `φ'(i₀-1) = -1` would force `r ≥ 2`, impossible for a `1`-Lipschitz `Ψ`.
  Both branches of both halves are formalised, so the pointer is now a proposition.

`key_r` and `key_l` are the intermediate inequalities inside the paper's proof of `lem:signs`
(`r ≥ 1 - φ'(i₀)`, `l ≤ -1 - φ'(i₁+1)`).  They are stated separately because `lem:offJ`
cites *them*, not the weaker published conclusion `l ≤ 0 ≤ r`.

`decay_left` / `decay_right` are Lemma `lem:decay` (l.157), stated for a sequence concave on an
interval rather than for `v`, since that is all its proof uses.

The reduction to cylindric Kostka numbers is `arXiv:2409.09055`-adjacent work of my own:
`proofs/2026-09-30-c1-cylindric-kostka-logconcavity.tex`, Prop. 4.3.
-/

namespace TworowD4Kernel.LemmaT

/-! ### Lemma `lem:decay`: a sequence concave on an interval decays past a unit step -/

/-- If `c` is concave on `[a, m+1]` and its increment at `m` is at least `1`, then every
increment to the left of `m` is at least `1`, so `c` drops by at least `1` per step going left.
This is the left half of `lem:decay` (l.157), with `v` replaced by the only property of it the
proof uses. -/
theorem decay_left {c : ℤ → ℤ} {a m : ℤ}
    (hconc : ∀ k, a + 1 ≤ k → k ≤ m → c (k - 1) + c (k + 1) ≤ 2 * c k)
    (hstep : 1 ≤ c (m + 1) - c m) :
    ∀ i, a ≤ i → i ≤ m → c i + (m - i) ≤ c m := by
  have main : ∀ n, n ≤ m → a ≤ n → 1 ≤ c (n + 1) - c n ∧ c n + (m - n) ≤ c m := by
    refine Int.leInductionDown ?_ ?_
    · intro _
      exact ⟨hstep, by omega⟩
    · intro n hnm ih ha
      have ha' : a ≤ n := by omega
      obtain ⟨hd, hc⟩ := ih ha'
      have hk := hconc n (by omega) hnm
      have e : n - 1 + 1 = n := by ring
      refine ⟨by rw [e]; omega, by rw [e] at *; omega⟩
  intro i hai him
  exact (main i him hai).2

/-- The mirror image: if `c` is concave on `[m-1, b]` and its increment at `m-1` is at most
`-1`, then `c` drops by at least `1` per step going right.  Right half of `lem:decay`. -/
theorem decay_right {c : ℤ → ℤ} {m b : ℤ}
    (hconc : ∀ k, m ≤ k → k + 1 ≤ b → c (k - 1) + c (k + 1) ≤ 2 * c k)
    (hstep : c m - c (m - 1) ≤ -1) :
    ∀ i, m ≤ i → i ≤ b → c i + (i - m) ≤ c m := by
  intro i hmi hib
  have hconc' : ∀ k, -b + 1 ≤ k → k ≤ -m → (fun t => c (-t)) (k - 1) + (fun t => c (-t)) (k + 1)
      ≤ 2 * (fun t => c (-t)) k := by
    intro k hk1 hk2
    have h := hconc (-k) (by omega) (by omega)
    have e1 : -(k - 1) = -k + 1 := by ring
    have e2 : -(k + 1) = -k - 1 := by ring
    simp only [e1, e2]
    omega
  have hstep' : 1 ≤ (fun t => c (-t)) (-m + 1) - (fun t => c (-t)) (-m) := by
    have e1 : -(-m + 1) = m - 1 := by ring
    have e2 : -(-m) = m := by ring
    simp only [e1, e2]
    omega
  have key := decay_left (c := fun t => c (-t)) (a := -b) (m := -m) hconc' hstep' (-i)
    (by omega) (by omega)
  have e1 : -(-i) = i := by ring
  have e2 : -(-m) = m := by ring
  simp only [e1, e2] at key
  omega

/-! ### The data of one antidiagonal -/

/-- The hypothesis class of Lemma T at one antidiagonal `s`, §2 of the paper (l.84).

Every hypothesis is **restricted to the box**: `Φ` is concave and `1`-Lipschitz only on `[A,B]`,
`Ψ` convex and `1`-Lipschitz only on `[C,D]`, and `supp` describes the cell-support only at
cells of the box.  This is what makes the paper's "lies in the box, so `v_i` is defined" steps
into real Lean obligations rather than no-ops. -/
structure Setup where
  Φ : ℤ → ℤ
  Ψ : ℤ → ℤ
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
  s : ℤ
  i₀ : ℤ
  i₁ : ℤ
  /-- `Φ` is concave on `[A,B]`. -/
  Φ_concave : ∀ i, A + 1 ≤ i → i + 1 ≤ B → Φ (i - 1) + Φ (i + 1) ≤ 2 * Φ i
  /-- `Φ` is `1`-Lipschitz on `[A,B]`. -/
  Φ_lip : ∀ i, A + 1 ≤ i → i ≤ B → |Φ i - Φ (i - 1)| ≤ 1
  /-- `Ψ` is convex on `[C,D]`. -/
  Ψ_convex : ∀ x, C + 1 ≤ x → x + 1 ≤ D → 2 * Ψ x ≤ Ψ (x - 1) + Ψ (x + 1)
  /-- `Ψ` is `1`-Lipschitz on `[C,D]`. -/
  Ψ_lip : ∀ x, C + 1 ≤ x → x ≤ D → |Ψ x - Ψ (x - 1)| ≤ 1
  /-- `I = [i₀, i₁]` is nonempty. -/
  i_le : i₀ ≤ i₁
  /-- `I = {i ∈ J : v i ≥ 1}` equals `[i₀, i₁] ∩ J`.  The paper gets this from concavity of `v`
  (l.95); here it is a hypothesis, which is how the published proof uses it. -/
  supp : ∀ i, A ≤ i → i ≤ B → C ≤ s - i → s - i ≤ D →
      (1 ≤ Φ i - Ψ (s - i) + 1 ↔ i₀ ≤ i ∧ i ≤ i₁)

namespace Setup

variable (S : Setup)

/-- The untruncated cell value `v_i = Φ(i) - Ψ(s-i) + 1` (l.90). -/
def v (i : ℤ) : ℤ := S.Φ i - S.Ψ (S.s - i) + 1

/-- `x₀ = s - i₁`. -/
def x₀ : ℤ := S.s - S.i₁

/-- `x₁ = s - i₀`. -/
def x₁ : ℤ := S.s - S.i₀

/-- `φ'(i) = Φ(i) - Φ(i-1)` (l.86). -/
def φ' (i : ℤ) : ℤ := S.Φ i - S.Φ (i - 1)

/-- `ψ'(x) = Ψ(x) - Ψ(x-1)` (l.86). -/
def ψ' (x : ℤ) : ℤ := S.Ψ x - S.Ψ (x - 1)

/-- `l = ψ'(x₀)` (l.99). -/
def l : ℤ := S.ψ' S.x₀

/-- `r = ψ'(x₁ + 1)` (l.99). -/
def r : ℤ := S.ψ' (S.x₁ + 1)

end Setup

/-- Definition `def:int` (l.112): antidiagonal `s` is **interior** when its cell-support is
strictly inside the box in both coordinates. -/
structure Setup.Interior (S : Setup) : Prop where
  lo : S.A ≤ S.i₀ - 1
  hi : S.i₁ + 1 ≤ S.B
  xlo : S.C ≤ S.x₀ - 1
  xhi : S.x₁ + 1 ≤ S.D

namespace Setup

variable {S : Setup}

/-- The numeric content of `(INT)`, unfolded. -/
theorem Interior.bounds (h : S.Interior) :
    S.A + 1 ≤ S.i₀ ∧ S.i₀ ≤ S.i₁ ∧ S.i₁ + 1 ≤ S.B ∧
      S.C + 1 ≤ S.s - S.i₁ ∧ S.s - S.i₀ + 1 ≤ S.D := by
  obtain ⟨lo, hi, xlo, xhi⟩ := h
  simp only [Setup.x₀, Setup.x₁] at xlo xhi
  exact ⟨by omega, S.i_le, by omega, by omega, by omega⟩

/-- `v i₀ ≥ 1`: the left end of `I` contributes. -/
theorem v_i₀ (h : S.Interior) : 1 ≤ S.v S.i₀ := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  exact (S.supp S.i₀ (by omega) (by omega) (by omega) (by omega)).mpr ⟨le_refl _, b2⟩

/-- `v i₁ ≥ 1`: the right end of `I` contributes. -/
theorem v_i₁ (h : S.Interior) : 1 ≤ S.v S.i₁ := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  exact (S.supp S.i₁ (by omega) (by omega) (by omega) (by omega)).mpr ⟨b2, le_refl _⟩

/-- `v (i₀ - 1) ≤ 0`.  **This is the step `(INT)` exists for**: `(i₀-1, x₁+1)` lies in the box,
so `supp` applies at `i₀-1`, and `i₀-1 < i₀` puts it outside `I`. -/
theorem v_lo (h : S.Interior) : S.v (S.i₀ - 1) ≤ 0 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  have := (S.supp (S.i₀ - 1) (by omega) (by omega) (by omega) (by omega)).mp
  by_contra hc
  exact absurd (this (by simpa [Setup.v] using (by omega : (1:ℤ) ≤ S.v (S.i₀ - 1)))).1 (by omega)

/-- `v (i₁ + 1) ≤ 0`, by the same use of `(INT)` at the other end. -/
theorem v_hi (h : S.Interior) : S.v (S.i₁ + 1) ≤ 0 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  have := (S.supp (S.i₁ + 1) (by omega) (by omega) (by omega) (by omega)).mp
  by_contra hc
  exact absurd (this (by simpa [Setup.v] using (by omega : (1:ℤ) ≤ S.v (S.i₁ + 1)))).2 (by omega)

/-! ### The two algebraic identities of `lem:signs` -/

/-- `v i₀ - v (i₀ - 1) = φ'(i₀) + r` (l.170).  Pure algebra: at fixed `i` the cells differ only
through `Ψ`. -/
theorem v_step_left : S.v S.i₀ - S.v (S.i₀ - 1) = S.φ' S.i₀ + S.r := by
  change (S.Φ S.i₀ - S.Ψ (S.s - S.i₀) + 1) - (S.Φ (S.i₀ - 1) - S.Ψ (S.s - (S.i₀ - 1)) + 1)
      = (S.Φ S.i₀ - S.Φ (S.i₀ - 1))
        + (S.Ψ (S.s - S.i₀ + 1) - S.Ψ (S.s - S.i₀ + 1 - 1))
  have e1 : S.s - (S.i₀ - 1) = S.s - S.i₀ + 1 := by ring
  have e2 : S.s - S.i₀ + 1 - 1 = S.s - S.i₀ := by ring
  rw [e1, e2]; ring

/-- `v (i₁ + 1) - v i₁ = φ'(i₁ + 1) + l` (l.175). -/
theorem v_step_right : S.v (S.i₁ + 1) - S.v S.i₁ = S.φ' (S.i₁ + 1) + S.l := by
  change (S.Φ (S.i₁ + 1) - S.Ψ (S.s - (S.i₁ + 1)) + 1) - (S.Φ S.i₁ - S.Ψ (S.s - S.i₁) + 1)
      = (S.Φ (S.i₁ + 1) - S.Φ (S.i₁ + 1 - 1))
        + (S.Ψ (S.s - S.i₁) - S.Ψ (S.s - S.i₁ - 1))
  have e1 : S.s - (S.i₁ + 1) = S.s - S.i₁ - 1 := by ring
  have e2 : S.i₁ + 1 - 1 = S.i₁ := by ring
  rw [e1, e2]; ring

/-! ### Lemma `lem:signs` -/

/-- `r ≥ 1 - φ'(i₀)` (l.173), the intermediate inequality inside the proof of `lem:signs`.
`lem:offJ` cites this, not the published conclusion. -/
theorem key_r (h : S.Interior) : 1 - S.φ' S.i₀ ≤ S.r := by
  have h1 := S.v_i₀ h
  have h2 := S.v_lo h
  have h3 := S.v_step_left
  omega

/-- `l ≤ -1 - φ'(i₁+1)` (l.177), the other intermediate inequality. -/
theorem key_l (h : S.Interior) : S.l ≤ -1 - S.φ' (S.i₁ + 1) := by
  have h1 := S.v_i₁ h
  have h2 := S.v_hi h
  have h3 := S.v_step_right
  omega

/-- **Lemma `lem:signs`** (l.166 of `proofs/2026-09-30-c2-lemma-T.tex`): assuming `(INT)`,
`l ≤ 0 ≤ r`.

This is the unique place `Φ`'s `1`-Lipschitz hypothesis is spent — `Φ_lip` is used here at
`i₀` and at `i₁+1` and nowhere else in the proof of `thm:main`. -/
theorem lem_signs (h : S.Interior) : S.l ≤ 0 ∧ 0 ≤ S.r := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  have hr := S.key_r h
  have hl := S.key_l h
  have lip₀ := abs_le.mp (S.Φ_lip S.i₀ (by omega) (by omega))
  have lip₁ := abs_le.mp (S.Φ_lip (S.i₁ + 1) (by omega) (by omega))
  simp only [Setup.φ'] at hr hl
  have e : S.i₁ + 1 - 1 = S.i₁ := by ring
  rw [e] at hl lip₁
  constructor
  · omega
  · omega


/-! ### Lemma `lem:offJ`

The paper's first draft justified the two off-`J` cells *"by the decay lemma"*.  That citation
has **no object**: `v_i` is only defined for `i ∈ J`, and these two indices are precisely the
ones outside `J`.  The repaired argument routes through the index `i'` one step *inside* `J`,
and closes the residual case with `key_r` / `key_l` against `Ψ`'s `1`-Lipschitz bound.  Both
branches are formalised below. -/

/-- `r` unfolded. -/
theorem r_eq : S.r = S.Ψ (S.s - S.i₀ + 1) - S.Ψ (S.s - S.i₀) := by
  change S.Ψ (S.s - S.i₀ + 1) - S.Ψ (S.s - S.i₀ + 1 - 1) = _
  have e : S.s - S.i₀ + 1 - 1 = S.s - S.i₀ := by ring
  rw [e]

/-- `l` unfolded. -/
theorem l_eq : S.l = S.Ψ (S.s - S.i₁) - S.Ψ (S.s - S.i₁ - 1) := rfl

/-- `|r| ≤ 1`: `(INT)` puts `x₁ + 1` inside `[C+1, D]`, where `Ψ_lip` applies. -/
theorem abs_r_le (h : S.Interior) : |S.r| ≤ 1 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  have hlip := S.Ψ_lip (S.s - S.i₀ + 1) (by omega) (by omega)
  have e : S.s - S.i₀ + 1 - 1 = S.s - S.i₀ := by ring
  rw [e] at hlip
  rw [S.r_eq]
  exact hlip

/-- `|l| ≤ 1`: likewise `x₀` lies inside `[C+1, D]`. -/
theorem abs_l_le (h : S.Interior) : |S.l| ≤ 1 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  have hlip := S.Ψ_lip (S.s - S.i₁) (by omega) (by omega)
  rw [S.l_eq]
  exact hlip

/-- `v` is concave at every `k` interior to `J`: `Φ` concave plus `Ψ` convex (l.95). -/
theorem v_concave (k : ℤ) (h1 : S.A + 1 ≤ k) (h2 : k + 1 ≤ S.B)
    (h3 : S.C + 1 ≤ S.s - k) (h4 : S.s - k + 1 ≤ S.D) :
    S.v (k - 1) + S.v (k + 1) ≤ 2 * S.v k := by
  have hΦ := S.Φ_concave k h1 h2
  have hΨ := S.Ψ_convex (S.s - k) h3 h4
  have e1 : S.s - (k - 1) = S.s - k + 1 := by ring
  have e2 : S.s - (k + 1) = S.s - k - 1 := by ring
  simp only [Setup.v, e1, e2]
  omega

/-- **Lemma `lem:offJ`, lower half** (l.238).  Antidiagonal `s-1` meets exactly one cell whose
`i` lies outside `J`, namely `i = s-1-D` at `j = D`.  Its untruncated value is `≤ 0`, so it
contributes nothing to `G(s-1)`.

The hypothesis is only `A ≤ i`: if `i < A` the cell is absent from the box altogether. -/
theorem lem_offJ_lower (h : S.Interior) (hA : S.A ≤ S.s - 1 - S.D) :
    S.Φ (S.s - 1 - S.D) - S.Ψ S.D + 1 ≤ 0 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  set i' : ℤ := S.s - S.D with hi'
  have hile : i' ≤ S.i₀ - 1 := by omega
  have hval : S.Φ (S.s - 1 - S.D) - S.Ψ S.D + 1 = S.v i' - S.φ' i' := by
    change _ = (S.Φ i' - S.Ψ (S.s - i') + 1) - (S.Φ i' - S.Φ (i' - 1))
    have e1 : S.s - i' = S.D := by omega
    have e2 : i' - 1 = S.s - 1 - S.D := by omega
    rw [e1, e2]; ring
  rw [hval]
  have hlip := abs_le.mp (S.Φ_lip i' (by omega) (by omega))
  simp only [Setup.φ'] at hlip ⊢
  rcases lt_or_eq_of_le hile with hlt | heq
  · -- `i' ≤ i₀ - 2`: the decay lemma applies, at an index where `v` *is* defined.
    have hstep : 1 ≤ S.v (S.i₀ - 1 + 1) - S.v (S.i₀ - 1) := by
      have e : S.i₀ - 1 + 1 = S.i₀ := by ring
      rw [e]
      have h1 := S.v_i₀ h
      have h2 := S.v_lo h
      omega
    have hdecay := decay_left (c := S.v) (a := i') (m := S.i₀ - 1)
      (fun k hk1 hk2 => S.v_concave k (by omega) (by omega) (by omega) (by omega))
      hstep i' (le_refl _) (by omega)
    have h2 := S.v_lo h
    omega
  · -- `i' = i₀ - 1`: here `φ'(i₀-1) = -1` would force `r ≥ 2`, impossible for `1`-Lipschitz `Ψ`.
    rw [heq] at hlip ⊢
    have hv := S.v_lo h
    have hr := S.key_r h
    have hrb := abs_le.mp (S.abs_r_le h)
    have hcc := S.Φ_concave (S.i₀ - 1) (by omega) (by omega)
    have e1 : S.i₀ - 1 + 1 = S.i₀ := by ring
    rw [e1] at hcc
    simp only [Setup.φ'] at hr
    omega

/-- **Lemma `lem:offJ`, upper half** (l.251).  Antidiagonal `s+1` meets exactly one cell whose
`i` lies outside `J`, namely `i = s+1-C` at `j = C`; its value is `≤ 0`.

The hypothesis is only `i ≤ B`: if `i > B` the cell is absent from the box. -/
theorem lem_offJ_upper (h : S.Interior) (hB : S.s + 1 - S.C ≤ S.B) :
    S.Φ (S.s + 1 - S.C) - S.Ψ S.C + 1 ≤ 0 := by
  obtain ⟨b1, b2, b3, b4, b5⟩ := h.bounds
  set i' : ℤ := S.s - S.C with hi'
  have hige : S.i₁ + 1 ≤ i' := by omega
  have hval : S.Φ (S.s + 1 - S.C) - S.Ψ S.C + 1 = S.v i' + S.φ' (S.s + 1 - S.C) := by
    change _ = (S.Φ i' - S.Ψ (S.s - i') + 1) + (S.Φ (S.s + 1 - S.C) - S.Φ (S.s + 1 - S.C - 1))
    have e1 : S.s - i' = S.C := by omega
    have e2 : S.s + 1 - S.C - 1 = i' := by omega
    rw [e1, e2]; ring
  rw [hval]
  have hlip := abs_le.mp (S.Φ_lip (S.s + 1 - S.C) (by omega) hB)
  simp only [Setup.φ'] at hlip ⊢
  rcases lt_or_eq_of_le hige with hlt | heq
  · -- `i' ≥ i₁ + 2`: decay to the right.
    have hstep : S.v (S.i₁ + 1) - S.v (S.i₁ + 1 - 1) ≤ -1 := by
      have e : S.i₁ + 1 - 1 = S.i₁ := by ring
      rw [e]
      have h1 := S.v_i₁ h
      have h2 := S.v_hi h
      omega
    have hdecay := decay_right (c := S.v) (m := S.i₁ + 1) (b := i')
      (fun k hk1 hk2 => S.v_concave k (by omega) (by omega) (by omega) (by omega))
      hstep i' (by omega) (le_refl _)
    have h2 := S.v_hi h
    omega
  · -- `i' = i₁ + 1`: here `φ'(i₁+2) = 1` would force `l ≤ -2`, impossible.
    have ea : S.s + 1 - S.C - 1 = S.i₁ + 1 := by omega
    have eb : S.s + 1 - S.C = S.i₁ + 2 := by omega
    rw [ea, eb] at hlip
    rw [← heq, ea, eb]
    have hv := S.v_hi h
    have hl := S.key_l h
    have hlb := abs_le.mp (S.abs_l_le h)
    have hcc := S.Φ_concave (S.i₁ + 1) (by omega) (by omega)
    have e3 : S.i₁ + 1 - 1 = S.i₁ := by ring
    have e4 : S.i₁ + 1 + 1 = S.i₁ + 2 := by ring
    rw [e3, e4] at hcc
    simp only [Setup.φ'] at hl
    rw [e3] at hl
    omega

end Setup

/-! ### Negative controls

A hypothesis class nobody instantiates proves nothing, and a hypothesis nobody plants a
violation of is not known to be load-bearing.  Three live controls.
-/

namespace Control

/-- `Φ ≡ 0`. -/
def wΦ : ℤ → ℤ := fun _ => 0

/-- `Ψ = |x - 1|`, written with `max` so `omega` can see it. -/
def wΨ : ℤ → ℤ := fun x => max (1 - x) (x - 1)

/-- **Satisfiability.**  `A = 0`, `B = 5`, `C = 0`, `D = 2`, `s = 4`, `I = {3}`, so
`J = [2,4]` and `v = (0, 1, 0)` on it.  Chosen so that *all four* conclusions are exercised:
`(INT)` holds, and both off-`J` cells (`i = s-1-D = 1` and `i = s+1-C = 5`) lie in the box. -/
def wit : Setup where
  Φ := wΦ
  Ψ := wΨ
  A := 0
  B := 5
  C := 0
  D := 2
  s := 4
  i₀ := 3
  i₁ := 3
  Φ_concave := by intro i _ _; simp [wΦ]
  Φ_lip := by intro i _ _; simp [wΦ]
  Ψ_convex := by intro x _ _; simp only [wΨ]; omega
  Ψ_lip := by intro x _ _; rw [abs_le]; simp only [wΨ]; omega
  i_le := le_refl _
  supp := by intro i _ _ _ _; simp only [wΦ, wΨ]; omega

theorem wit_interior : wit.Interior where
  lo := by norm_num [wit]
  hi := by norm_num [wit]
  xlo := by simp [Setup.x₀, wit]
  xhi := by simp [Setup.x₁, wit]

/-- The two end slopes of the witness are `l = -1` and `r = 1`, so `lem_signs` is not asserting
`0 ≤ 0` here. -/
theorem wit_slopes : wit.l = -1 ∧ wit.r = 1 := by
  constructor <;> simp [Setup.l, Setup.r, Setup.ψ', Setup.x₀, Setup.x₁, wit, wΨ]

/-- `lem_signs` on the witness. -/
example : wit.l ≤ 0 ∧ 0 ≤ wit.r := Setup.lem_signs wit_interior

/-- Both off-`J` cells of the witness exist in the box, and `lem:offJ`'s bound `≤ 0` is **tight**
at both: each cell has value exactly `0`.  So `lem_offJ_lower`/`lem_offJ_upper` cannot be
strengthened to `≤ -1`. -/
theorem wit_offJ_tight :
    wit.Φ (wit.s - 1 - wit.D) - wit.Ψ wit.D + 1 = 0 ∧
      wit.Φ (wit.s + 1 - wit.C) - wit.Ψ wit.C + 1 = 0 := by
  constructor <;> simp [wit, wΦ, wΨ]

example : wit.Φ (wit.s - 1 - wit.D) - wit.Ψ wit.D + 1 ≤ 0 :=
  Setup.lem_offJ_lower wit_interior (by norm_num [wit])

example : wit.Φ (wit.s + 1 - wit.C) - wit.Ψ wit.C + 1 ≤ 0 :=
  Setup.lem_offJ_upper wit_interior (by norm_num [wit])

/-! #### Control 1: the `(INT)` clause `A ≤ i₀ - 1` is load-bearing for `0 ≤ r` -/

/-- `Ψ = -x`: convex and `1`-Lipschitz on all of `ℤ`, with `ψ' ≡ -1`. -/
def dΨ : ℤ → ℤ := fun x => -x

/-- Same `Φ ≡ 0`, but now `A = i₀`: the left end of the cell-support sits *on* the wall.  The
other three `(INT)` clauses still hold, and `x₁ + 1 ≤ D`, so `r` is still a genuine increment of
`Ψ` inside its domain. -/
def noLo : Setup where
  Φ := wΦ
  Ψ := dΨ
  A := 0
  B := 5
  C := -10
  D := 10
  s := 2
  i₀ := 0
  i₁ := 2
  Φ_concave := by intro i _ _; simp [wΦ]
  Φ_lip := by intro i _ _; simp [wΦ]
  Ψ_convex := by intro x _ _; simp only [dΨ]; omega
  Ψ_lip := by intro x _ _; rw [abs_le]; simp only [dΨ]; omega
  i_le := by norm_num
  supp := by intro i _ _ _ _; simp only [wΦ, dΨ]; omega

/-- Exactly one `(INT)` clause fails, namely `lo`. -/
theorem noLo_only_lo_fails :
    ¬ (noLo.A ≤ noLo.i₀ - 1) ∧ noLo.i₁ + 1 ≤ noLo.B ∧ noLo.C ≤ noLo.x₀ - 1 ∧
      noLo.x₁ + 1 ≤ noLo.D := by
  refine ⟨by norm_num [noLo], by norm_num [noLo], ?_, ?_⟩ <;>
    simp [Setup.x₀, Setup.x₁, noLo]

/-- And the conclusion `0 ≤ r` of `lem_signs` **fails**: `r = -1`.  So `lem_signs` genuinely
needs `A ≤ i₀ - 1`; it is not removable bookkeeping. -/
theorem noLo_r_neg : noLo.r = -1 := by
  simp [Setup.r, Setup.ψ', Setup.x₁, noLo, dΨ]

theorem noLo_not_interior : ¬ noLo.Interior := fun h =>
  absurd h.lo noLo_only_lo_fails.1

/-- The other half, `l ≤ 0`, still holds here — the control isolates which clause feeds which
inequality. -/
theorem noLo_l_nonpos : noLo.l ≤ 0 := by
  simp [Setup.l, Setup.ψ', Setup.x₀, noLo, dΨ]

/-! #### Control 2: `Φ`'s `1`-Lipschitz hypothesis is load-bearing for `0 ≤ r`

`Φ_lip` is a *field* of `Setup`, so a counterexample to it cannot be a `Setup`.  The implication
is therefore written out inline and refuted. -/

/-- `Φ = (-10, 0, 0, …)`: concave on `[0,6]` (increments `10,0,0,0,0,0` are non-increasing) but
**not** `1`-Lipschitz — the step at `i = 1` is `10`. -/
def bigΦ : ℤ → ℤ := fun i => if i ≤ 0 then -10 else 0

/-- **Dropping `Φ_lip` destroys `lem_signs`.**  There are `Φ, Ψ` and a box satisfying every
hypothesis of `Setup` *except* `Φ_lip`, together with `(INT)` **in full**, for which `r = -1 < 0`.
So the `1`-Lipschitz bound on `Φ` is not decoration: `lem:signs` is exactly where it is spent. -/
theorem Φ_lipschitz_needed :
    ∃ Φ Ψ : ℤ → ℤ, ∃ A B C D s i₀ i₁ : ℤ,
      (∀ i, A + 1 ≤ i → i + 1 ≤ B → Φ (i - 1) + Φ (i + 1) ≤ 2 * Φ i) ∧
      (∀ x, C + 1 ≤ x → x + 1 ≤ D → 2 * Ψ x ≤ Ψ (x - 1) + Ψ (x + 1)) ∧
      (∀ x, C + 1 ≤ x → x ≤ D → |Ψ x - Ψ (x - 1)| ≤ 1) ∧
      i₀ ≤ i₁ ∧
      (∀ i, A ≤ i → i ≤ B → C ≤ s - i → s - i ≤ D →
        (1 ≤ Φ i - Ψ (s - i) + 1 ↔ i₀ ≤ i ∧ i ≤ i₁)) ∧
      (A ≤ i₀ - 1 ∧ i₁ + 1 ≤ B ∧ C ≤ s - i₁ - 1 ∧ s - i₀ + 1 ≤ D) ∧
      Ψ (s - i₀ + 1) - Ψ (s - i₀) < 0 ∧
      ¬ (∀ i, A + 1 ≤ i → i ≤ B → |Φ i - Φ (i - 1)| ≤ 1) := by
  refine ⟨bigΦ, dΨ, 0, 6, -10, 10, 4, 1, 4, ?_, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_⟩
  · intro i _ _; simp only [bigΦ]; split_ifs <;> omega
  · intro x _ _; simp only [dΨ]; omega
  · intro x _ _; rw [abs_le]; simp only [dΨ]; omega
  · intro i _ _ _ _; simp only [bigΦ, dΨ]; split_ifs <;> omega
  · norm_num
  · simp only [dΨ]; norm_num
  · intro hlip
    have := hlip 1 (by norm_num) (by norm_num)
    simp only [bigΦ] at this
    norm_num at this

end Control

end TworowD4Kernel.LemmaT

/-! ### Axiom audit -/

section Audit

#print axioms TworowD4Kernel.LemmaT.decay_left
#print axioms TworowD4Kernel.LemmaT.decay_right
#print axioms TworowD4Kernel.LemmaT.Setup.v_i₀
#print axioms TworowD4Kernel.LemmaT.Setup.v_i₁
#print axioms TworowD4Kernel.LemmaT.Setup.v_lo
#print axioms TworowD4Kernel.LemmaT.Setup.v_hi
#print axioms TworowD4Kernel.LemmaT.Setup.v_step_left
#print axioms TworowD4Kernel.LemmaT.Setup.v_step_right
#print axioms TworowD4Kernel.LemmaT.Setup.key_r
#print axioms TworowD4Kernel.LemmaT.Setup.key_l
#print axioms TworowD4Kernel.LemmaT.Setup.lem_signs
#print axioms TworowD4Kernel.LemmaT.Setup.v_concave
#print axioms TworowD4Kernel.LemmaT.Setup.abs_r_le
#print axioms TworowD4Kernel.LemmaT.Setup.abs_l_le
#print axioms TworowD4Kernel.LemmaT.Setup.lem_offJ_lower
#print axioms TworowD4Kernel.LemmaT.Setup.lem_offJ_upper
#print axioms TworowD4Kernel.LemmaT.Control.wit_interior
#print axioms TworowD4Kernel.LemmaT.Control.wit_slopes
#print axioms TworowD4Kernel.LemmaT.Control.wit_offJ_tight
#print axioms TworowD4Kernel.LemmaT.Control.noLo_r_neg
#print axioms TworowD4Kernel.LemmaT.Control.noLo_not_interior
#print axioms TworowD4Kernel.LemmaT.Control.noLo_only_lo_fails
#print axioms TworowD4Kernel.LemmaT.Control.noLo_l_nonpos
#print axioms TworowD4Kernel.LemmaT.Control.Φ_lipschitz_needed

end Audit
