/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.AbacusRibbon

/-!
# The one-bead matrix element of `R_f R_e`, and the structural `(1 + t)`

Formalises §3 Step 2 (the one-bead sector) of
`proofs/2026-09-07-Q92-cross-rank-commutator.tex` (`proofs@a26acae`), which in turn rests
on the abacus dictionary of Uglov (`arXiv:math/9905196`) and Leclerc–Thibon
(`arXiv:q-alg/9512031`) as packaged in `TworowD4Kernel.AbacusRibbon`.

## The statement

Fix `e, f ≥ 1`, a bead set `M`, a bead `b ∈ M` with `b + e + f ∉ M`, and let
`M' = M \ {b} ∪ {b+e+f}` be the *one-bead target*. Write `m x = [x ∈ M]` and
`N = #(M ∩ (b, b+e+f))` — the **open** interval, which is `ribbonHeight (e+f) M b`
verbatim. Then

* `⟨M'|R_f R_e|M⟩ = (1 - m (b+e)) * t^N + m (b+f) * t^(N-1)`,
* `⟨M'|R_e R_f|M⟩ = (1 - m (b+f)) * t^N + m (b+e) * t^(N-1)`,

and subtracting,

* `⟨M'|[R_e,R_f]|M⟩ = (m (b+e) - m (b+f)) * (t^N + t^(N-1))`.

So `1 + t` divides the one-bead matrix element of the commutator **before any
cancellation**, with the cofactor `m (b+e) - m (b+f) ∈ {-1, 0, 1}` read straight off two
bead occupancies.

**Sign.** The paper's cofactor is `m (b+e) - m (b+f)`, in that order, with
`[R_e, R_f] = R_e R_f - R_f R_e`. (The 2026-09-07 c2 LEAN brief restated it as
`m (b+f) - m (b+e)`; subtracting the two identities above shows the paper is right and the
brief's restatement is sign-flipped. Formalised here in the paper's convention.)

## Where the work is

Two routes reach `M'` (paper §3 Step 1: `|M Δ M'| = 4` unless a removed site coincides with
an added one, forcing `y = x + e` or `x = y + f`):

* **Route B, "in-order push"** `b → b+e → b+e+f`, legal iff `m (b+e) = 0`, weight `t^N`;
* **Route C, "leapfrog"** `b+f → b+e+f` then `b → b+f`, legal iff `m (b+f) = 1`, weight
  `t^(N-1)`.

The two weight computations are the content, and each has a side condition that is easy to
lose: the second leg's weight is read off the *intermediate* diagram `M₁`, not off `M`, and
agrees with the count on `M` only because the two sites where `M₁` differs from `M` fall
**outside the open interval** being counted. Route B needs the interval open at its **left**
end (`b + e` is the left endpoint); route C needs it open at its **right** end (`b + f` is
the right endpoint). Both are discharged by the single lemma
`ribbonHeight_addRibbon_outside`, and the two interval decompositions by the single lemma
`ribbonHeight_split` — one lemma used twice, in each case, rather than a mirror pair.

## On the truncated `N - 1`

`N - 1` is natural-number subtraction. It never bites: the term it exponentiates carries the
factor `m (b+f)` (resp. `m (b+e)`), and `one_le_ribbonHeight_of_mem` shows that factor forces
`1 ≤ N`. The `if`-guarded form used below makes this structural rather than incidental.
-/

namespace TworowD4Kernel

open Finset

section Counting

variable {M : Finset ℤ} {b : ℤ}

/-- **The splitting lemma.** The open window `(b, b + g + h)` is the disjoint union of the
open window `(b, b+g)`, the single site `b+g`, and the open window `(b+g, b+g+h)`.
Both positivity hypotheses are load-bearing: at `g = 0` the site `b + g = b` is *not* in the
open window `(b, b+h)`, and at `h = 0` it is not in `(b, b+g)` either, so the decomposition
genuinely fails at either endpoint.
Used twice: route B splits at `b+e` (unoccupied, middle term `0`), route C splits at `b+f`
(occupied, middle term `1`). -/
theorem ribbonHeight_split (M : Finset ℤ) (b : ℤ) {g h : ℕ} (hg : 0 < g) (hh : 0 < h) :
    ribbonHeight (g + h) M b
      = ribbonHeight g M b + (if b + (g : ℤ) ∈ M then 1 else 0)
          + ribbonHeight h M (b + (g : ℤ)) := by
  classical
  have hsplit : M.filter (fun x => b < x ∧ x < b + ((g + h : ℕ) : ℤ))
      = ((M.filter (fun x => b < x ∧ x < b + (g : ℤ)))
          ∪ (M.filter (fun x => x = b + (g : ℤ))))
        ∪ (M.filter (fun x => b + (g : ℤ) < x ∧ x < b + (g : ℤ) + (h : ℤ))) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Nat.cast_add]
    constructor
    · rintro ⟨hm, h1, h2⟩
      rcases lt_trichotomy x (b + (g : ℤ)) with hc | hc | hc
      · exact Or.inl (Or.inl ⟨hm, h1, hc⟩)
      · exact Or.inl (Or.inr ⟨hm, hc⟩)
      · exact Or.inr ⟨hm, hc, by omega⟩
    · rintro ((⟨hm, h1, h2⟩ | ⟨hm, he⟩) | ⟨hm, h1, h2⟩) <;>
        exact ⟨hm, by omega, by omega⟩
  have d1 : Disjoint (M.filter (fun x => b < x ∧ x < b + (g : ℤ)))
      (M.filter (fun x => x = b + (g : ℤ))) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    simp only [Finset.mem_filter] at hx hy
    omega
  have d2 : Disjoint ((M.filter (fun x => b < x ∧ x < b + (g : ℤ)))
        ∪ (M.filter (fun x => x = b + (g : ℤ))))
      (M.filter (fun x => b + (g : ℤ) < x ∧ x < b + (g : ℤ) + (h : ℤ))) := by
    rw [Finset.disjoint_left]
    rintro x hx hy
    simp only [Finset.mem_union, Finset.mem_filter] at hx hy
    rcases hx with ⟨-, h1, h2⟩ | ⟨-, he⟩ <;> omega
  have hmid : (M.filter (fun x => x = b + (g : ℤ))).card
      = if b + (g : ℤ) ∈ M then 1 else 0 := by
    rw [Finset.filter_eq']
    split <;> simp
  unfold ribbonHeight
  rw [hsplit, Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1, hmid]

/-- A bead in the open window forces the window count to be at least one. This is what makes
the truncated `N - 1` harmless in the statements below. -/
theorem one_le_ribbonHeight_of_mem {g : ℕ} {x : ℤ} (hx : x ∈ M) (h1 : b < x)
    (h2 : x < b + (g : ℤ)) : 1 ≤ ribbonHeight g M b := by
  unfold ribbonHeight
  exact Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hx, h1, h2⟩⟩

/-- **The window lemma.** Moving a bead from `x` to `x + e` does not change the count in the
open window `(c, c + f)`, provided **neither** endpoint of the move lies inside that window.
The two changed sites are exactly `x` (vacated) and `x + e` (occupied).

This is the lemma the paper's "both lie outside the *open* interval" is doing, and it is
stated once for both routes: route B applies it with `x = b`, `c = b + e` (the vacated site
`b` is below the window and the occupied site `b + e` **is the left endpoint**, excluded
because the window is open there); route C with `x = b + f`, `c = b` (the vacated site
`b + f` **is the right endpoint**, excluded because the window is open there, and the
occupied site `b + e + f` is above it). -/
theorem ribbonHeight_addRibbon_outside {e f : ℕ} (M : Finset ℤ) (x c : ℤ)
    (hx : ¬ (c < x ∧ x < c + (f : ℤ)))
    (hxe : ¬ (c < x + (e : ℤ) ∧ x + (e : ℤ) < c + (f : ℤ))) :
    ribbonHeight f (addRibbon e M x) c = ribbonHeight f M c := by
  unfold ribbonHeight
  congr 1
  ext z
  simp only [Finset.mem_filter, mem_addRibbon, ne_eq]
  constructor
  · rintro ⟨hz | ⟨-, hm⟩, h1, h2⟩
    · exact absurd (hz ▸ ⟨h1, h2⟩) hxe
    · exact ⟨hm, h1, h2⟩
  · rintro ⟨hm, h1, h2⟩
    exact ⟨Or.inr ⟨fun hzx => hx (hzx ▸ ⟨h1, h2⟩), hm⟩, h1, h2⟩

end Counting

section Routes

variable {e f : ℕ} {M M' : Finset ℤ} {b : ℤ}

/-- A route `M --(x,e)--> M₁ --(y,f)--> M'`: a pair of legal bead moves whose composite
lands on `M'`. Paper eq. `(eq:routes)`; note `R_f R_e` applies `R_e` **first**, so `x` is the
`e`-move and `y` the `f`-move. The ambient product is a container only — the real content is
`mem_routes` below. -/
def routes (e f : ℕ) (M M' : Finset ℤ) : Finset (ℤ × ℤ) :=
  (M ×ˢ (M ∪ M.image (· + (e : ℤ)))).filter
    (fun p => p.1 + (e : ℤ) ∉ M ∧ p.2 ∈ addRibbon e M p.1 ∧
      p.2 + (f : ℤ) ∉ addRibbon e M p.1 ∧ addRibbon f (addRibbon e M p.1) p.2 = M')

/-- Membership in `routes` is exactly the conjunction of the two legality conditions and the
landing condition; the ambient product imposes nothing extra. -/
theorem mem_routes {p : ℤ × ℤ} :
    p ∈ routes e f M M' ↔ p.1 ∈ M ∧ p.1 + (e : ℤ) ∉ M ∧ p.2 ∈ addRibbon e M p.1 ∧
      p.2 + (f : ℤ) ∉ addRibbon e M p.1 ∧ addRibbon f (addRibbon e M p.1) p.2 = M' := by
  simp only [routes, Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3, h4, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨⟨h1, ?_⟩, h2, h3, h4, h5⟩
    rw [mem_addRibbon] at h3
    rcases h3 with hz | ⟨-, hm⟩
    · exact Or.inr ⟨p.1, h1, hz.symm⟩
    · exact Or.inl hm

/-- The `t`-weight of a route: `w₁ + w₂`, where `w₂` is read off the **intermediate**
diagram `addRibbon e M x`, not off `M`. Paper eq. `(eq:routes)`. -/
def routeWeight (e f : ℕ) (M : Finset ℤ) (x y : ℤ) : ℕ :=
  ribbonHeight e M x + ribbonHeight f (addRibbon e M x) y

/-- The matrix element `⟨M'|R_f R_e|M⟩ = ∑_routes t^(w₁+w₂)`, in any commutative semiring. -/
def matrixElem (e f : ℕ) (M M' : Finset ℤ) {R : Type*} [CommSemiring R] (t : R) : R :=
  ∑ p ∈ routes e f M M', t ^ routeWeight e f M p.1 p.2

/-- **Route B lands on the target.** The in-order push `b → b+e → b+e+f`.
Uses `b + e ∉ M`. -/
theorem routeB_target (hbe : b + (e : ℤ) ∉ M) :
    addRibbon f (addRibbon e M b) (b + (e : ℤ)) = addRibbon (e + f) M b := by
  ext x
  simp only [mem_addRibbon, ne_eq, Nat.cast_add]
  constructor
  · rintro (hx | ⟨hx1, hx2 | ⟨hx3, hm⟩⟩)
    · exact Or.inl (by omega)
    · exact absurd hx2 hx1
    · exact Or.inr ⟨hx3, hm⟩
  · rintro (hx | ⟨hx1, hm⟩)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨fun hc => hbe (hc ▸ hm), Or.inr ⟨hx1, hm⟩⟩

/-- **Route C lands on the target.** The leapfrog `b+f → b+e+f`, then `b → b+f`.
Uses `b + f ∈ M`, and `0 < e`, `0 < f` to keep the four sites apart. -/
theorem routeC_target (he : 0 < e) (hf : 0 < f) (hbf : b + (f : ℤ) ∈ M) :
    addRibbon f (addRibbon e M (b + (f : ℤ))) b = addRibbon (e + f) M b := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  ext x
  simp only [mem_addRibbon, ne_eq, Nat.cast_add]
  constructor
  · rintro (hx | ⟨hx1, hx2 | ⟨hx3, hm⟩⟩)
    · exact Or.inr ⟨by omega, hx ▸ hbf⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨hx1, hm⟩
  · rintro (hx | ⟨hx1, hm⟩)
    · exact Or.inr ⟨by omega, Or.inl (by omega)⟩
    · by_cases hc : x = b + (f : ℤ)
      · exact Or.inl hc
      · exact Or.inr ⟨hx1, Or.inr ⟨hc, hm⟩⟩

/-- **The route classification (paper §3 Steps 1–2).** In the one-bead sector, exactly two
routes can reach `M' = M \ {b} ∪ {b+e+f}`: route B `(b, b+e)`, present iff `b + e ∉ M`, and
route C `(b+f, b)`, present iff `b + f ∈ M`.

Note that these are not alternatives: for a given `M` **both** may be present (they are
exclusive only as route *types*, since `y = x + e` and `x = y + f` together force `e + f = 0`).
The proof does not case split on an either/or; it splits on whether the second move vacates
`b`, and each branch determines the route completely. -/
theorem mem_routes_one_bead {p : ℤ × ℤ} (he : 0 < e) (hf : 0 < f) (hb : b ∈ M)
    (hbef : b + (e : ℤ) + (f : ℤ) ∉ M) :
    p ∈ routes e f M (addRibbon (e + f) M b)
      ↔ (p = (b, b + (e : ℤ)) ∧ b + (e : ℤ) ∉ M)
        ∨ (p = (b + (f : ℤ), b) ∧ b + (f : ℤ) ∈ M) := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  have hcomm : ∀ z : ℤ, z + (e : ℤ) + (f : ℤ) = z + (f : ℤ) + (e : ℤ) := fun z => by ring
  obtain ⟨x, y⟩ := p
  rw [mem_routes]
  constructor
  · rintro ⟨hx, hxe, hy, hyf, heq⟩
    -- `b` is vacated by the composite, so the second move must vacate it or the first must.
    have hbnot : b ∉ addRibbon f (addRibbon e M x) y := by
      rw [heq]; exact addRibbon_notMem_self _ _ _ (by omega)
    rw [mem_addRibbon] at hbnot
    push Not at hbnot
    by_cases hyb : y = b
    · -- Route C: the second move vacates `b`, so it *is* the move `b → b+f`.
      subst hyb
      right
      have hmem : y + (f : ℤ) ∈ addRibbon f (addRibbon e M x) y := addRibbon_mem_self _ _ _
      rw [heq, mem_addRibbon] at hmem
      have hbf : y + (f : ℤ) ∈ M := by
        rcases hmem with hc | ⟨-, hm⟩
        · push_cast at hc; omega
        · exact hm
      rw [mem_addRibbon] at hyf
      push Not at hyf
      have hxeq : x = y + (f : ℤ) := by
        by_contra hne
        exact (hyf.2 (fun hc => hne hc.symm)) hbf
      exact ⟨by rw [hxeq], hbf⟩
    · -- Route B: the second move does not vacate `b`, so the first move must: `x = b`.
      have hbn1 : b ∉ addRibbon e M x := hbnot.2 (fun hc => hyb hc.symm)
      rw [mem_addRibbon] at hbn1
      push Not at hbn1
      have hxb : x = b := by
        by_contra hne
        exact (hbn1.2 (fun hc => hne hc.symm)) hb
      subst hxb
      left
      -- `x + e` survives the first move but not the composite, so the second move erases it.
      have h1 : x + (e : ℤ) ∈ addRibbon e M x := addRibbon_mem_self _ _ _
      have h2 : x + (e : ℤ) ∉ addRibbon f (addRibbon e M x) y := by
        rw [heq, mem_addRibbon]
        push Not
        exact ⟨by push_cast; omega, fun _ => hxe⟩
      rw [mem_addRibbon] at h2
      push Not at h2
      have : y = x + (e : ℤ) := by
        by_contra hne
        exact (h2.2 (fun hc => hne hc.symm)) h1
      exact ⟨by rw [this], hxe⟩
  · rintro (⟨hp, hbe⟩ | ⟨hp, hbf⟩)
    · rw [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨hb, hbe, addRibbon_mem_self _ _ _, ?_, routeB_target hbe⟩
      intro hmem
      rw [mem_addRibbon] at hmem
      rcases hmem with hc | ⟨-, hm⟩
      · omega
      · exact hbef hm
    · rw [Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨hbf, fun hc => hbef (by rw [hcomm]; exact hc), ?_, ?_, routeC_target he hf hbf⟩
      · rw [mem_addRibbon]
        exact Or.inr ⟨by omega, hb⟩
      · intro hmem
        rw [mem_addRibbon] at hmem
        rcases hmem with hc | ⟨hne, -⟩
        · omega
        · exact hne rfl

end Routes

section Weights

variable {e f : ℕ} {M : Finset ℤ} {b : ℤ}

/-- **Route B's weight is `N`.** `w₁ = #(M ∩ (b, b+e))`; `w₂` is read off the intermediate
diagram but equals `#(M ∩ (b+e, b+e+f))` because the two changed sites `b` and `b+e` lie
outside that window — `b+e` only because the window is **open at its left end**. Their sum is
`#(M ∩ (b, b+e+f)) - m(b+e) = N`, using `m(b+e) = 0`. -/
theorem routeB_weight (he : 0 < e) (hf : 0 < f) (hbe : b + (e : ℤ) ∉ M) :
    routeWeight e f M b (b + (e : ℤ)) = ribbonHeight (e + f) M b := by
  have hwin : ribbonHeight f (addRibbon e M b) (b + (e : ℤ)) = ribbonHeight f M (b + (e : ℤ)) :=
    ribbonHeight_addRibbon_outside M b (b + (e : ℤ)) (by omega) (by omega)
  have hsplit := ribbonHeight_split M b he hf
  rw [if_neg hbe] at hsplit
  unfold routeWeight
  rw [hwin, hsplit]
  omega

/-- **Route C's weight is `N - 1`**, stated as `w + 1 = N` to keep it free of truncated
subtraction. Here `w₁ = #(M ∩ (b+f, b+e+f))` and `w₂ = #(M ∩ (b, b+f))`, the latter valid
because the changed sites `b+f` and `b+e+f` lie outside `(b, b+f)` — `b+f` only because the
window is **open at its right end**. Their sum is `#(M ∩ (b, b+e+f)) - m(b+f) = N - 1`, using
`m(b+f) = 1`. -/
theorem routeC_weight (he : 0 < e) (hf : 0 < f) (hbf : b + (f : ℤ) ∈ M) :
    routeWeight e f M (b + (f : ℤ)) b + 1 = ribbonHeight (e + f) M b := by
  have hwin : ribbonHeight f (addRibbon e M (b + (f : ℤ))) b = ribbonHeight f M b :=
    ribbonHeight_addRibbon_outside M (b + (f : ℤ)) b (by omega) (by omega)
  have hsplit := ribbonHeight_split M b hf he
  rw [if_pos hbf] at hsplit
  have hef : ribbonHeight (f + e) M b = ribbonHeight (e + f) M b := by rw [Nat.add_comm]
  rw [hef] at hsplit
  unfold routeWeight
  omega

end Weights

section MatrixElement

variable {e f : ℕ} {M : Finset ℤ} {b : ℤ}

/-- **The one-bead matrix element** (paper §3 Step 2):
`⟨M'|R_f R_e|M⟩ = (1 - m(b+e)) t^N + m(b+f) t^(N-1)`, where `N = #(M ∩ (b, b+e+f))`. -/
theorem matrixElem_one_bead {R : Type*} [CommSemiring R] (t : R)
    (he : 0 < e) (hf : 0 < f) (hb : b ∈ M) (hbef : b + (e : ℤ) + (f : ℤ) ∉ M) :
    matrixElem e f M (addRibbon (e + f) M b) t
      = (if b + (e : ℤ) ∈ M then 0 else t ^ ribbonHeight (e + f) M b)
        + (if b + (f : ℤ) ∈ M then t ^ (ribbonHeight (e + f) M b - 1) else 0) := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  unfold matrixElem
  by_cases hbe : b + (e : ℤ) ∈ M <;> by_cases hbf : b + (f : ℤ) ∈ M
  · have hr : routes e f M (addRibbon (e + f) M b) = {(b + (f : ℤ), b)} := by
      ext p
      rw [mem_routes_one_bead he hf hb hbef, Finset.mem_singleton]
      exact ⟨fun h => h.elim (fun h => absurd hbe h.2) (fun h => h.1),
        fun h => Or.inr ⟨h, hbf⟩⟩
    have hC := routeC_weight (M := M) (b := b) he hf hbf
    rw [hr, Finset.sum_singleton, if_pos hbe, if_pos hbf, zero_add]
    change t ^ routeWeight e f M (b + (f : ℤ)) b = t ^ (ribbonHeight (e + f) M b - 1)
    congr 1
    omega
  · have hr : routes e f M (addRibbon (e + f) M b) = ∅ := by
      ext p
      rw [mem_routes_one_bead he hf hb hbef]
      simp only [Finset.notMem_empty, iff_false, not_or]
      exact ⟨fun h => absurd hbe h.2, fun h => absurd h.2 hbf⟩
    rw [hr, Finset.sum_empty, if_pos hbe, if_neg hbf, add_zero]
  · have hne : ((b, b + (e : ℤ)) : ℤ × ℤ) ∉ ({(b + (f : ℤ), b)} : Finset (ℤ × ℤ)) := by
      simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]
      intro h; omega
    have hr : routes e f M (addRibbon (e + f) M b)
        = insert ((b, b + (e : ℤ)) : ℤ × ℤ) {(b + (f : ℤ), b)} := by
      ext p
      rw [mem_routes_one_bead he hf hb hbef, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun h => h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1),
        fun h => h.elim (fun h => Or.inl ⟨h, hbe⟩) (fun h => Or.inr ⟨h, hbf⟩)⟩
    have hB := routeB_weight (M := M) (b := b) he hf hbe
    have hC := routeC_weight (M := M) (b := b) he hf hbf
    have hC2 : routeWeight e f M (b + (f : ℤ)) b = ribbonHeight (e + f) M b - 1 := by omega
    rw [hr, Finset.sum_insert hne, Finset.sum_singleton, if_neg hbe, if_pos hbf]
    change t ^ routeWeight e f M b (b + (e : ℤ)) + t ^ routeWeight e f M (b + (f : ℤ)) b
      = t ^ ribbonHeight (e + f) M b + t ^ (ribbonHeight (e + f) M b - 1)
    rw [hB, hC2]
  · have hr : routes e f M (addRibbon (e + f) M b) = {(b, b + (e : ℤ))} := by
      ext p
      rw [mem_routes_one_bead he hf hb hbef, Finset.mem_singleton]
      exact ⟨fun h => h.elim (fun h => h.1) (fun h => absurd h.2 hbf),
        fun h => Or.inl ⟨h, hbe⟩⟩
    have hB := routeB_weight (M := M) (b := b) he hf hbe
    rw [hr, Finset.sum_singleton, if_neg hbe, if_neg hbf, add_zero]
    change t ^ routeWeight e f M b (b + (e : ℤ)) = t ^ ribbonHeight (e + f) M b
    rw [hB]

end MatrixElement

section Commutator

variable {e f : ℕ} {M : Finset ℤ} {b : ℤ}

/-- The exchanged identity `⟨M'|R_e R_f|M⟩ = (1 - m(b+f)) t^N + m(b+e) t^(N-1)`.
The target `M' = M \ {b} ∪ {b+e+f}` is unchanged by `e ↔ f`, which is the whole reason the
two identities can be subtracted. -/
theorem matrixElem_one_bead_swap {R : Type*} [CommSemiring R] (t : R)
    (he : 0 < e) (hf : 0 < f) (hb : b ∈ M) (hbef : b + (e : ℤ) + (f : ℤ) ∉ M) :
    matrixElem f e M (addRibbon (e + f) M b) t
      = (if b + (f : ℤ) ∈ M then 0 else t ^ ribbonHeight (e + f) M b)
        + (if b + (e : ℤ) ∈ M then t ^ (ribbonHeight (e + f) M b - 1) else 0) := by
  have hbef' : b + (f : ℤ) + (e : ℤ) ∉ M := by
    rw [show b + (f : ℤ) + (e : ℤ) = b + (e : ℤ) + (f : ℤ) from by ring]; exact hbef
  rw [Nat.add_comm e f]
  exact matrixElem_one_bead t hf he hb hbef'

/-- **The corollary the paper advertises.**
`⟨M'|[R_e,R_f]|M⟩ = (m(b+e) - m(b+f)) (t^N + t^(N-1))`, with `[R_e,R_f] = R_e R_f - R_f R_e`.
The cofactor `m(b+e) - m(b+f) ∈ {-1,0,1}` is read straight off two bead occupancies. -/
theorem commutator_one_bead {R : Type*} [CommRing R] (t : R)
    (he : 0 < e) (hf : 0 < f) (hb : b ∈ M) (hbef : b + (e : ℤ) + (f : ℤ) ∉ M) :
    matrixElem f e M (addRibbon (e + f) M b) t
        - matrixElem e f M (addRibbon (e + f) M b) t
      = ((if b + (e : ℤ) ∈ M then (1 : R) else 0) - (if b + (f : ℤ) ∈ M then (1 : R) else 0))
        * (t ^ ribbonHeight (e + f) M b + t ^ (ribbonHeight (e + f) M b - 1)) := by
  rw [matrixElem_one_bead_swap t he hf hb hbef, matrixElem_one_bead t he hf hb hbef]
  by_cases hbe : b + (e : ℤ) ∈ M <;> by_cases hbf : b + (f : ℤ) ∈ M <;>
    simp only [hbe, hbf, if_pos, if_neg, not_false_iff] <;> ring

/-- **The structural `(1 + t)`.** `1 + t` divides the one-bead matrix element of the
commutator, before any cancellation between routes. When `N = 0` the cofactor vanishes (both
`b+e` and `b+f` lie in the open interval `(b, b+e+f)`, so an occupied one forces `N ≥ 1`);
otherwise `t^N + t^(N-1) = t^(N-1)(1+t)`. -/
theorem one_add_dvd_commutator_one_bead {R : Type*} [CommRing R] (t : R)
    (he : 0 < e) (hf : 0 < f) (hb : b ∈ M) (hbef : b + (e : ℤ) + (f : ℤ) ∉ M) :
    (1 + t) ∣ (matrixElem f e M (addRibbon (e + f) M b) t
        - matrixElem e f M (addRibbon (e + f) M b) t) := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  rw [commutator_one_bead t he hf hb hbef]
  by_cases hocc : b + (e : ℤ) ∈ M ∨ b + (f : ℤ) ∈ M
  · have hN1 : 1 ≤ ribbonHeight (e + f) M b := by
      rcases hocc with h | h
      · exact one_le_ribbonHeight_of_mem h (by omega) (by push_cast; omega)
      · exact one_le_ribbonHeight_of_mem h (by omega) (by push_cast; omega)
    have hpow : t ^ ribbonHeight (e + f) M b + t ^ (ribbonHeight (e + f) M b - 1)
        = t ^ (ribbonHeight (e + f) M b - 1) * (1 + t) := by
      rw [mul_add, mul_one, ← pow_succ, Nat.sub_add_cancel hN1]
      ring
    rw [hpow]
    exact ⟨((if b + (e : ℤ) ∈ M then (1 : R) else 0)
      - (if b + (f : ℤ) ∈ M then (1 : R) else 0)) * t ^ (ribbonHeight (e + f) M b - 1), by ring⟩
  · push Not at hocc
    rw [if_neg hocc.1, if_neg hocc.2]
    simp

end Commutator

end TworowD4Kernel
