/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.CrossRankOneBead
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The two-bead sector of the two-parameter commutator `[R_e(t), R_f(s)]`

Formalises §4 of `proofs/2026-09-07-c2-Q96-order-over-sublattice.tex`: Theorem 4.1(2) (the
two-bead matrix element) and Corollary 4.2(iii) (it vanishes on the locus `ts = 1`).  The
abacus dictionary is Uglov (`arXiv:math/9905196`) and Leclerc–Thibon
(`arXiv:q-alg/9512031`), packaged in `TworowD4Kernel.AbacusRibbon`; the route enumeration is
`TworowD4Kernel.CrossRankOneBead`, whose `routes` and `mem_routes` are reused verbatim.

## Two parameters from the start

`R_e` carries `t` and `R_f` carries `s`, independent over a `CommRing`.  The one-parameter
case is `s = t`.  This is not cosmetic: the paper's Remark 4.3 records that
`\cite[Thm.~2.3(2)]{Clio0907}` asserted "`e = f` ⟹ the two-bead element is `0`", which is a
*one-parameter* statement — at `e = f` there are two legal assignments whose indices `k` are
negatives of one another, and they cancel only at `s = t`.  With `t ≠ s` the sector is
nonzero (e.g. `(t-s)(1-st)`).  The `e = f` clause is invisible in the one-parameter
formulation, which is how it survived.

## The statement

For a route `(x, y)` — the `e`-move from `x`, then the `f`-move from `y` — put

* `P = ribbonHeight e M x`, the height of the `e`-move done **first**;
* `Q = ribbonHeight f M y`, the height of the `f`-move done **first**;
* `Q' = ribbonHeight f (addRibbon e M x) y`, the `f`-move done **second**;
* `P' = ribbonHeight e (addRibbon f M y) x`, the `e`-move done **second**.

The paper writes `Q' = Q + k` and `P' = P - k` with
`k = 1[x+e ∈ (y, y+f)] - 1[x ∈ (y, y+f)]`.  Here `P'` and `Q'` are **defined as the
cardinalities they are** and the arithmetic is a theorem (`ribbonHeight_addRibbon_shift`,
`crossIndex_swap`), never a definition: `P - k` with `k : ℤ` would be either truncated
subtraction or a negative exponent, and the honest object is the count.

The two heights then satisfy `P' + Q' = P + Q` **in `ℕ`** (`twoBead_height_sum`), which is
the whole content of Cor. 4.2(iii): on `ts = 1`, `s^Q t^{P'} = t^P s^{Q'}`, so the two
orderings of the same pair of moves contribute equally and cancel.

## Where the distinctness hypotheses bite

`crossIndex_swap` (`k' = -k`, the paper's `β - α = -k`) is **false** without `x ≠ y` and
`x + e ≠ y + f`; both failures are exhibited as `#guard`s in the test driver.  The paper
states exactly these two, and no more — the other two pairwise-distinctness conditions
(`x ≠ y+f`, `x+e ≠ y`) are not needed for `crossIndex_swap` but *are* needed for the routes
to swap at all (`routes_swap`), which is a different lemma.  They are separated here.
-/

namespace TworowD4Kernel

open Finset

section Counting

/-- Deleting a bead lowers the window count by one exactly when the bead was in the window.
Stated in `ℤ` so that no truncated subtraction appears. -/
theorem ribbonHeight_erase {f : ℕ} (M : Finset ℤ) (b c : ℤ) (hb : b ∈ M) :
    (ribbonHeight f (M.erase b) c : ℤ)
      = (ribbonHeight f M c : ℤ) - (if c < b ∧ b < c + (f : ℤ) then 1 else 0) := by
  classical
  unfold ribbonHeight
  have h : (M.erase b).filter (fun x => c < x ∧ x < c + (f : ℤ))
      = (M.filter (fun x => c < x ∧ x < c + (f : ℤ))).erase b := by
    ext z; simp only [Finset.mem_filter, Finset.mem_erase]; tauto
  rw [h]
  by_cases hw : c < b ∧ b < c + (f : ℤ)
  · have hmem : b ∈ M.filter (fun x => c < x ∧ x < c + (f : ℤ)) :=
      Finset.mem_filter.2 ⟨hb, hw⟩
    have hpos : 1 ≤ (M.filter (fun x => c < x ∧ x < c + (f : ℤ))).card :=
      Finset.card_pos.2 ⟨b, hmem⟩
    rw [Finset.card_erase_of_mem hmem, if_pos hw]
    omega
  · have hmem : b ∉ M.filter (fun x => c < x ∧ x < c + (f : ℤ)) := by
      simp only [Finset.mem_filter]; tauto
    rw [Finset.erase_eq_of_notMem hmem, if_neg hw]
    ring

/-- Adding a fresh bead raises the window count by one exactly when the bead lands in the
window. -/
theorem ribbonHeight_insert {f : ℕ} (M : Finset ℤ) (a c : ℤ) (ha : a ∉ M) :
    (ribbonHeight f (insert a M) c : ℤ)
      = (ribbonHeight f M c : ℤ) + (if c < a ∧ a < c + (f : ℤ) then 1 else 0) := by
  classical
  unfold ribbonHeight
  by_cases hw : c < a ∧ a < c + (f : ℤ)
  · have h : (insert a M).filter (fun x => c < x ∧ x < c + (f : ℤ))
        = insert a (M.filter (fun x => c < x ∧ x < c + (f : ℤ))) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hz | hz, h1, h2⟩
        · exact Or.inl hz
        · exact Or.inr ⟨hz, h1, h2⟩
      · rintro (hz | ⟨hz, h1, h2⟩)
        · subst hz; exact ⟨Or.inl rfl, hw.1, hw.2⟩
        · exact ⟨Or.inr hz, h1, h2⟩
    have hnot : a ∉ M.filter (fun x => c < x ∧ x < c + (f : ℤ)) := by
      simp only [Finset.mem_filter]; tauto
    rw [h, Finset.card_insert_of_notMem hnot, if_pos hw]
    push_cast; ring
  · have h : (insert a M).filter (fun x => c < x ∧ x < c + (f : ℤ))
        = M.filter (fun x => c < x ∧ x < c + (f : ℤ)) := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hz | hz, h1, h2⟩
        · subst hz; exact absurd ⟨h1, h2⟩ hw
        · exact ⟨hz, h1, h2⟩
      · rintro ⟨hz, h1, h2⟩
        exact ⟨Or.inr hz, h1, h2⟩
    rw [h, if_neg hw]
    ring

/-- **The crossing index** `k` of the paper (Thm. 4.1(2)):
`k = 1[x+e ∈ (y, y+f)] - 1[x ∈ (y, y+f)]`, the change in the occupancy of the **open**
window `(y, y+f)` caused by the `e`-move `x ↦ x + e`. -/
def crossIndex (e f : ℕ) (x y : ℤ) : ℤ :=
  (if y < x + (e : ℤ) ∧ x + (e : ℤ) < y + (f : ℤ) then 1 else 0)
    - (if y < x ∧ x < y + (f : ℤ) then 1 else 0)

/-- **The height-shift lemma** (brief's `heightShift`; paper Thm. 4.1(2), "the subsequent
`f`-move sees a Maya set in which the count on `(c, c+f)` has changed by exactly `k`").

If `M₁` is `M` after the legal `e`-move `x ↦ x + e`, then the `f`-window at `y` counts
`Q + k` beads.  Both legality hypotheses are used: `x ∈ M` for the erase, `x + e ∉ M` for
the insert. -/
theorem ribbonHeight_addRibbon_shift {e f : ℕ} (M : Finset ℤ) (x y : ℤ)
    (hx : x ∈ M) (hxe : x + (e : ℤ) ∉ M) :
    (ribbonHeight f (addRibbon e M x) y : ℤ)
      = (ribbonHeight f M y : ℤ) + crossIndex e f x y := by
  classical
  have hne : x + (e : ℤ) ∉ M.erase x := fun h => hxe (Finset.mem_of_mem_erase h)
  have h1 := ribbonHeight_insert (f := f) (M.erase x) (x + (e : ℤ)) y hne
  have h2 := ribbonHeight_erase (f := f) M x y hx
  rw [show addRibbon e M x = insert (x + (e : ℤ)) (M.erase x) from rfl, h1, h2]
  unfold crossIndex
  ring

/-- **`k' = -k`** (paper Thm. 4.1(2) proof: "`β - α = -k` because `b ≠ c` and
`b + e ≠ c + f`").  Exactly those two disequalities are load-bearing, and they are in the
statement rather than in a comment: at `x = y` with `e < f` one gets `k = 1`, `k' = 0`, and
at `x + e = y + f` with `x > y` one gets `k = k' = -1`.  Both counterexamples are `#guard`ed
in the test driver. -/
theorem crossIndex_swap {e f : ℕ} {x y : ℤ} (he : 0 < e) (hf : 0 < f)
    (hxy : x ≠ y) (hxe : x + (e : ℤ) ≠ y + (f : ℤ)) :
    crossIndex f e y x = - crossIndex e f x y := by
  have he' : (0 : ℤ) < e := by exact_mod_cast he
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  unfold crossIndex
  split_ifs <;> omega

end Counting

section Swap

variable {e f : ℕ} {M M' : Finset ℤ} {x y : ℤ}

/-- Two legal moves at distinct sites commute, provided neither move's landing site is the
other move's starting site. Both hypotheses are used, once in each direction of the
extensionality. -/
theorem addRibbon_comm (M : Finset ℤ) (x y : ℤ)
    (h1 : y ≠ x + (e : ℤ)) (h2 : x ≠ y + (f : ℤ)) :
    addRibbon f (addRibbon e M x) y = addRibbon e (addRibbon f M y) x := by
  ext z
  simp only [mem_addRibbon, ne_eq]
  constructor
  · rintro (rfl | ⟨hzy, rfl | ⟨hzx, hm⟩⟩)
    · exact Or.inr ⟨Ne.symm h2, Or.inl rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hzx, Or.inr ⟨hzy, hm⟩⟩
  · rintro (rfl | ⟨hzx, rfl | ⟨hzy, hm⟩⟩)
    · exact Or.inr ⟨Ne.symm h1, Or.inl rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hzy, Or.inr ⟨hzx, hm⟩⟩

/-- **A legal assignment** (paper Thm. 4.1(2)): the four sites `x`, `y`, `x+e`, `y+f` are
pairwise distinct. The remaining two pairs, `x ≠ x+e` and `y ≠ y+f`, are supplied by
`0 < e` and `0 < f` and so are not part of the data. -/
def TwoBead (e f : ℕ) (x y : ℤ) : Prop :=
  x ≠ y ∧ x ≠ y + (f : ℤ) ∧ x + (e : ℤ) ≠ y ∧ x + (e : ℤ) ≠ y + (f : ℤ)

instance decidableTwoBead (e f : ℕ) (x y : ℤ) : Decidable (TwoBead e f x y) := by
  unfold TwoBead; infer_instance

theorem TwoBead.swap (h : TwoBead e f x y) : TwoBead f e y x :=
  ⟨Ne.symm h.1, Ne.symm h.2.2.1, Ne.symm h.2.1, Ne.symm h.2.2.2⟩

/-- In a two-bead route the second move is legal **on `M` itself**, not merely on the
intermediate diagram. Uses `x + e ≠ y` (so `y` was already a bead of `M`) and `x ≠ y + f`
(so `y + f` was already a hole of `M`). -/
theorem routes_snd_legal (hp : (x, y) ∈ routes e f M M') (h2b : TwoBead e f x y) :
    y ∈ M ∧ y + (f : ℤ) ∉ M := by
  rw [mem_routes] at hp
  obtain ⟨-, -, hy, hyf, -⟩ := hp
  obtain ⟨hxy, hxyf, hexy, -⟩ := h2b
  simp only at hy hyf
  constructor
  · rw [mem_addRibbon] at hy
    exact hy.elim (fun hc => absurd hc.symm hexy) (fun h => h.2)
  · intro hm
    exact hyf ((mem_addRibbon _ _ _).2 (Or.inr ⟨Ne.symm hxyf, hm⟩))

/-- **The routes swap.** Reversing the order of the two moves of a two-bead route is again a
route to the same target, with the roles of `(e,t)` and `(f,s)` exchanged. This is the
involution that makes the `ts = 1` cancellation happen; it is *not* available in the one-bead
sector, where the two routes have different shapes. -/
theorem mem_routes_swap (hp : (x, y) ∈ routes e f M M') (h2b : TwoBead e f x y) :
    (y, x) ∈ routes f e M M' := by
  obtain ⟨hyM, hyfM⟩ := routes_snd_legal hp h2b
  rw [mem_routes] at hp ⊢
  obtain ⟨hx, hxe, -, -, heq⟩ := hp
  obtain ⟨hxy, hxyf, hexy, hexyf⟩ := h2b
  simp only at hx hxe heq ⊢
  refine ⟨hyM, hyfM, (mem_addRibbon _ _ _).2 (Or.inr ⟨hxy, hx⟩), ?_, ?_⟩
  · intro hm
    rw [mem_addRibbon] at hm
    exact hm.elim (fun hc => hexyf hc) (fun h => hxe h.2)
  · rw [← addRibbon_comm (e := e) (f := f) M x y (Ne.symm hexy) hxyf]
    exact heq

end Swap

section Sector

variable {e f : ℕ} {M M' : Finset ℤ}

/-- The two-bead routes: those reaching `M'` by two moves at four pairwise-distinct sites. -/
def twoBeadRoutes (e f : ℕ) (M M' : Finset ℤ) : Finset (ℤ × ℤ) :=
  (routes e f M M').filter (fun p => TwoBead e f p.1 p.2)

/-- The two-bead sector of `⟨M'|R_f(s) R_e(t)|M⟩`: the `e`-move carries `t`, the `f`-move
carries `s`, and the second move's height is read off the **intermediate** diagram. -/
def twoBeadSector (e f : ℕ) (M M' : Finset ℤ) {R : Type*} [CommSemiring R] (t s : R) : R :=
  ∑ p ∈ twoBeadRoutes e f M M',
    t ^ ribbonHeight e M p.1 * s ^ ribbonHeight f (addRibbon e M p.1) p.2

theorem twoBeadRoutes_swap (e f : ℕ) (M M' : Finset ℤ) :
    twoBeadRoutes f e M M' = (twoBeadRoutes e f M M').image Prod.swap := by
  ext q
  obtain ⟨a, b⟩ := q
  simp only [twoBeadRoutes, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨hq, h2⟩
    exact ⟨(b, a), ⟨mem_routes_swap hq h2, h2.swap⟩, rfl⟩
  · rintro ⟨⟨c, d⟩, ⟨hq, h2⟩, heq⟩
    rw [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨mem_routes_swap hq h2, h2.swap⟩

/-- **The height of the `e`-move taken second** is `P - k`, the paper's `β - α = -k`. Stated
in `ℤ`; the left-hand side is an honest cardinality, so its nonnegativity is automatic rather
than an extra hypothesis. -/
theorem ribbonHeight_addRibbon_shift_swap {x y : ℤ} (he : 0 < e) (hf : 0 < f)
    (hy : y ∈ M) (hyf : y + (f : ℤ) ∉ M) (hxy : x ≠ y)
    (hxefy : x + (e : ℤ) ≠ y + (f : ℤ)) :
    (ribbonHeight e (addRibbon f M y) x : ℤ)
      = (ribbonHeight e M x : ℤ) - crossIndex e f x y := by
  rw [ribbonHeight_addRibbon_shift (e := f) (f := e) M y x hy hyf,
    crossIndex_swap he hf hxy hxefy]
  ring

/-- **The load-bearing identity.** The two orderings of the same pair of moves have total
height `P + Q` either way: `P' + Q' = P + Q`, in `ℕ`. This is `Q' = Q + k` and `P' = P - k`
with the `k` cancelled, and it is the entire content of Corollary 4.2(iii). -/
theorem twoBead_height_sum {x y : ℤ} (he : 0 < e) (hf : 0 < f)
    (hx : x ∈ M) (hxe : x + (e : ℤ) ∉ M) (hy : y ∈ M) (hyf : y + (f : ℤ) ∉ M)
    (hxy : x ≠ y) (hxefy : x + (e : ℤ) ≠ y + (f : ℤ)) :
    ribbonHeight e (addRibbon f M y) x + ribbonHeight f (addRibbon e M x) y
      = ribbonHeight e M x + ribbonHeight f M y := by
  have h1 := ribbonHeight_addRibbon_shift (e := e) (f := f) M x y hx hxe
  have h2 := ribbonHeight_addRibbon_shift_swap (e := e) (f := f) he hf hy hyf hxy hxefy
  omega

/-- If `t s = 1` then `t` and `s` are inverse units, so a monomial depends only on the
difference of its exponents; `P' + Q' = P + Q` says the two differences agree. Proved by
splitting on `P ≤ P'` and absorbing the surplus into `(ts)^d = 1` — no division, no
`Nat` subtraction. -/
theorem pow_swap_of_mul_eq_one {R : Type*} [CommSemiring R] {t s : R} (hts : t * s = 1)
    {P Q P' Q' : ℕ} (hsum : P' + Q' = P + Q) :
    s ^ Q * t ^ P' = t ^ P * s ^ Q' := by
  rcases le_total P P' with hle | hle
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    obtain rfl : Q = Q' + d := by omega
    have hd : (t * s) ^ d = 1 := by rw [hts, one_pow]
    calc s ^ (Q' + d) * t ^ (P + d)
        = t ^ P * s ^ Q' * (t * s) ^ d := by rw [mul_pow, pow_add, pow_add]; ring
      _ = t ^ P * s ^ Q' := by rw [hd, mul_one]
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    obtain rfl : Q' = Q + d := by omega
    have hd : (t * s) ^ d = 1 := by rw [hts, one_pow]
    calc s ^ Q * t ^ P'
        = s ^ Q * t ^ P' * (t * s) ^ d := by rw [hd, mul_one]
      _ = t ^ (P' + d) * s ^ (Q + d) := by rw [mul_pow, pow_add, pow_add]; ring

/-- **Per-assignment vanishing** (paper Cor. 4.2(iii)). For one legal assignment the two
orderings contribute the *same* monomial when `t s = 1`, so their difference — the net
contribution to `[R_e(t), R_f(s)]` — is zero. In the paper's notation the contribution is
`t^{P-k} s^Q (1 - (ts)^k)`; here it is the honest pair of cardinalities. -/
theorem twoBead_contribution_of_mul_eq_one {R : Type*} [CommSemiring R] {t s : R}
    (hts : t * s = 1) {x y : ℤ} (he : 0 < e) (hf : 0 < f)
    (hx : x ∈ M) (hxe : x + (e : ℤ) ∉ M) (hy : y ∈ M) (hyf : y + (f : ℤ) ∉ M)
    (hxy : x ≠ y) (hxefy : x + (e : ℤ) ≠ y + (f : ℤ)) :
    s ^ ribbonHeight f M y * t ^ ribbonHeight e (addRibbon f M y) x
      = t ^ ribbonHeight e M x * s ^ ribbonHeight f (addRibbon e M x) y :=
  pow_swap_of_mul_eq_one hts (twoBead_height_sum he hf hx hxe hy hyf hxy hxefy)

/-- **The two-bead sector of `[R_e(t), R_f(s)]` vanishes on `t s = 1`** — paper
Corollary 4.2(iii), the statement this session set out to machine-check.

Note this is proved *without* the classification of legal assignments (one when `e ≠ f`,
two when `e = f`): the cancellation is termwise under the route-reversing involution
`Prod.swap`, so it does not need to know how many terms there are. In particular it covers
the `e = f` case that `\cite[Thm.~2.3(2)]{Clio0907}` got wrong, with no case split. -/
theorem twoBeadSector_commutator_eq_zero_of_mul_eq_one {R : Type*} [CommRing R] (t s : R)
    (hts : t * s = 1) (he : 0 < e) (hf : 0 < f) :
    twoBeadSector f e M M' s t - twoBeadSector e f M M' t s = 0 := by
  rw [sub_eq_zero]
  unfold twoBeadSector
  rw [twoBeadRoutes_swap e f M M',
    Finset.sum_image (fun a _ b _ h => Prod.swap_injective h)]
  refine Finset.sum_congr rfl ?_
  rintro ⟨x, y⟩ hp
  simp only [twoBeadRoutes, Finset.mem_filter] at hp
  obtain ⟨hq, h2b⟩ := hp
  obtain ⟨hyM, hyfM⟩ := routes_snd_legal hq h2b
  rw [mem_routes] at hq
  obtain ⟨hx, hxe, -, -, -⟩ := hq
  simp only at hx hxe ⊢
  exact twoBead_contribution_of_mul_eq_one hts he hf hx hxe hyM hyfM h2b.1 h2b.2.2.2

end Sector

section TwoAssignmentSum

/-!
## The two-assignment sum, and the exact locus where it vanishes

This section formalises the **corrected** Corollary 4.2(iv) of
`proofs/2026-09-07-c2-Q96-order-over-sublattice.tex`.  As printed, (iv) asserts that
`[R_e(t), R_e(s)]` has a nonzero two-bead part whenever `t ≠ s` and `t s ≠ 1`.  That is
false for `e ∈ {1, 2}`; the self-review of 8 September 2026 (`clio-vega/rick-review@8223c88`,
finding F2) traced the defect to the closing clause of the printed proof, "this is not
identically zero", which is asserted rather than proved.  The corrected statement carries
the hypothesis `e ≥ 3`.

Two things are separated here, because the paper conflated them.

* `twoAssign_eq_zero_iff` is a **pure identity of Laurent polynomials** in three integer
  parameters `P, Q, k`.  It is an *iff*: the sum vanishes exactly on `k = 0 ∨ Q = P - k`.
  The forward direction is the content — it says four monomials in two variables fail to
  cancel — and it is where the printed corollary went wrong.
* `twoAssign_eq_zero_of_le_two` is the **abacus input**: for `e = f ≤ 2` every legal
  assignment lands on that vanishing locus, so the sector is identically zero.
  `exists_twoAssign_ne_zero_three` exhibits a legal assignment at `e = f = 3` that does not.

### The ring

Exponents in the two-assignment sum are genuine integers: `P - k` and `Q + k` are unbounded
below as `k` ranges over the crossing indices.  So the ambient ring is the two-variable
*Laurent* ring `ℤ[t^{±1}, s^{±1}]`, realised as the group algebra of `ℤ × ℤ`.  Monomials
`t^a s^b` are `mono a b`, and `mono_mul` / `mono_zero` say that `(a, b) ↦ mono a b` is a
homomorphism from `(ℤ², +)`, which is what pins `mono a b` down as `t^a s^b`.

### A convention warning that is deliberately *not* imported

`ribbonHeight` is used below purely as the window statistic `#{c ∈ M : b < c < b + e}` that
`TworowD4Kernel.AbacusRibbon` defines it to be.  Rick (Day 180,
`grandpa-rick/rick-research@616ea6e` §3) identifies it with the leg length of the `e`-ribbon,
standard since Littlewood's `e`-quotient theorem (James–Kerber §2.7), with range
`{0, …, e-1}`.  That identification is *not used*: the range bound `ribbonHeight_le_sub_one`
is proved from the definition, and an off-by-one in the ribbon-height convention would land
squarely in the range `[0, e-1]` that the `e ≤ 2` collapse is built on.  Likewise the `e = 2`
collapse is derived from the window statistic directly, not from Rick's parity argument.
-/

/-- The two-variable Laurent ring `ℤ[t^{±1}, s^{±1}]`, as the group algebra of `ℤ × ℤ`. -/
abbrev LaurentZ2 := AddMonoidAlgebra ℤ (ℤ × ℤ)

/-- The Laurent monomial `t^a s^b`, for `a b : ℤ`. -/
noncomputable def mono (a b : ℤ) : LaurentZ2 := AddMonoidAlgebra.single (a, b) 1

/-- `t^a s^b · t^c s^d = t^{a+c} s^{b+d}`. With `mono_zero` this says `mono` is a monoid
homomorphism from `(ℤ², +)`, which is what makes `mono a b` deserve the name `t^a s^b`. -/
@[simp] theorem mono_mul (a b c d : ℤ) : mono a b * mono c d = mono (a + c) (b + d) := by
  unfold mono
  rw [AddMonoidAlgebra.single_mul_single]
  norm_num [Prod.mk_add_mk]

/-- `t^0 s^0 = 1`. -/
@[simp] theorem mono_zero : mono 0 0 = 1 := rfl

/-- Every monomial is a unit — this is the point of working in the Laurent ring rather than
in `MvPolynomial (Fin 2) ℤ`, where `mono (P - k) Q` need not exist. -/
theorem mono_isUnit (a b : ℤ) : IsUnit (mono a b) :=
  ⟨⟨mono a b, mono (-a) (-b), by rw [mono_mul]; simp, by rw [mono_mul]; simp⟩, rfl⟩

/-- **The contribution of one legal assignment** (paper Thm. 4.1(2)): with the `e`-move
first the monomial is `t^P s^{Q+k}`, with the `f`-move first it is `t^{P-k} s^Q`, and the
net contribution to the commutator is their difference. -/
noncomputable def assignContrib (P Q k : ℤ) : LaurentZ2 :=
  mono (P - k) Q - mono P (Q + k)

/-- The paper's factorised form `t^{P-k} s^Q (1 - (ts)^k)`.  This is the factor that
Corollary 4.2(iii) kills on `ts = 1`; note it is *not* enough for (iv), because the sum of
two assignments can vanish without either factor doing so. -/
theorem assignContrib_eq_mul (P Q k : ℤ) :
    assignContrib P Q k = mono (P - k) Q * (1 - mono k k) := by
  unfold assignContrib
  rw [mul_sub, mul_one, mono_mul]
  ring_nf

/-- **The two-assignment sum** of Corollary 4.2(iv):
`t^{P-k} s^Q - t^P s^{Q+k} + t^{Q+k} s^P - t^Q s^{P-k}`.
At `e = f` both assignments `(b, c)` and `(c, b)` are legal; the second has heights `Q, P`
and crossing index `-k` (`crossIndex_swap`), which is `twoAssign_eq_add_swap` below. -/
noncomputable def twoAssign (P Q k : ℤ) : LaurentZ2 :=
  mono (P - k) Q - mono P (Q + k) + mono (Q + k) P - mono Q (P - k)

/-- The two-assignment sum really is the sum of the two assignments' contributions, the
second obtained by `b ↔ c` — heights swapped, crossing index negated. -/
theorem twoAssign_eq_add_swap (P Q k : ℤ) :
    twoAssign P Q k = assignContrib P Q k + assignContrib Q P (-k) := by
  unfold twoAssign assignContrib
  ring_nf

/-- Unfolding to the underlying `Finsupp`, so that coefficients can be read off. -/
theorem twoAssign_eq_finsupp (P Q k : ℤ) : twoAssign P Q k =
    (Finsupp.single (P - k, Q) 1 - Finsupp.single (P, Q + k) 1
      + Finsupp.single (Q + k, P) 1 - Finsupp.single (Q, P - k) 1 : (ℤ × ℤ) →₀ ℤ) := rfl

/-- The coefficient of `t^c s^d` in the two-assignment sum. -/
theorem twoAssign_apply (P Q k c d : ℤ) :
    (twoAssign P Q k : (ℤ × ℤ) →₀ ℤ) (c, d)
      = (if P - k = c ∧ Q = d then 1 else 0) - (if P = c ∧ Q + k = d then 1 else 0)
      + (if Q + k = c ∧ P = d then 1 else 0) - (if Q = c ∧ P - k = d then 1 else 0) := by
  rw [twoAssign_eq_finsupp]
  simp only [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.single_apply, Prod.ext_iff]

/-- **The corrected Corollary 4.2(iv), core identity.**  The two-assignment sum vanishes
identically **iff** `k = 0` or `Q = P - k`.

The reverse direction is the pair of substitutions the paper checks implicitly: at `k = 0`
terms 1–2 and 3–4 cancel, and at `Q = P - k` term 1 equals term 4 and term 2 equals term 3.

The forward direction is what the printed proof asserts without argument.  It is proved by
reading off a single coefficient: the monomial `t^{P-k} s^Q` occurs with coefficient `1`.
The three ways another term could cancel it are all excluded — `t^P s^{Q+k}` needs `k = 0`,
`t^Q s^{P-k}` needs `Q = P - k`, and `t^{Q+k} s^P` needs `P = Q` *and* `Q + k = P - k`,
hence `2k = 0`, hence `k = 0` again. -/
theorem twoAssign_eq_zero_iff (P Q k : ℤ) :
    twoAssign P Q k = 0 ↔ k = 0 ∨ Q = P - k := by
  constructor
  · intro h
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨hk, hQ⟩ := hc
    have hco := twoAssign_apply P Q k (P - k) Q
    rw [h] at hco
    rw [show ((0 : LaurentZ2) : (ℤ × ℤ) →₀ ℤ) (P - k, Q) = 0 from rfl] at hco
    split_ifs at hco <;> omega
  · rintro (rfl | rfl) <;> unfold twoAssign
    · simp only [sub_zero, add_zero]
      ring
    · simp only [sub_add_cancel]
      ring

end TwoAssignmentSum

section EDependence

open Finset

/-- The window `(b, b+1)` of integers is empty, so a `1`-ribbon has height `0`. -/
theorem ribbonHeight_one (M : Finset ℤ) (b : ℤ) : ribbonHeight 1 M b = 0 := by
  classical
  unfold ribbonHeight
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z _
  push_cast
  omega

/-- The window `(b, b+2)` contains the single integer `b+1`, so a `2`-ribbon has height
`1` or `0` according as `b+1` is a bead. -/
theorem ribbonHeight_two (M : Finset ℤ) (b : ℤ) :
    ribbonHeight 2 M b = if b + 1 ∈ M then 1 else 0 := by
  classical
  unfold ribbonHeight
  by_cases hb : b + 1 ∈ M
  · rw [if_pos hb, show M.filter (fun x => b < x ∧ x < b + ((2 : ℕ) : ℤ)) = {b + 1} from ?_,
      Finset.card_singleton]
    ext z
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h1, h2⟩; push_cast at h2; omega
    · rintro rfl; exact ⟨hb, by push_cast; omega⟩
  · rw [if_neg hb, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz ⟨h1, h2⟩
    push_cast at h2
    exact hb (by rwa [show b + 1 = z by omega])

/-- The crossing index takes only the values `-1, 0, 1`: it is the change in the occupancy
of one window caused by moving one bead. -/
theorem crossIndex_mem (e f : ℕ) (x y : ℤ) :
    crossIndex e f x y = -1 ∨ crossIndex e f x y = 0 ∨ crossIndex e f x y = 1 := by
  unfold crossIndex
  split_ifs <;> omega

/-- **The `e = f ≤ 2` collapse.**  For a legal two-bead assignment at `e = f ≤ 2` the
triple `(P, Q, k)` always lands on the vanishing locus of `twoAssign_eq_zero_iff`, so the
two-bead part of `[R_e(t), R_e(s)]` is identically zero — for *all* `t, s`, not merely on
`s = t` and `ts = 1`.  This is the case the printed Corollary 4.2(iv) excludes wrongly.

The two mechanisms are different and are kept apart:

* at `e = 1` the window `(c, c+1)` is empty, so `k = 0` outright;
* at `e = 2` a nonzero `k` *pins the geometry*: `k = 1` forces `b = c - 1` and `k = -1`
  forces `b = c + 1`, and in each case legality then evaluates both single-cell windows,
  giving `Q = P - k` exactly.

Note that legality (`hx`, `hxe`, `hy`, `hye`) is genuinely used in the `e = 2` branch: it is
what turns the two window counts into the constants `1` and `0`.  The distinctness
hypothesis `x ≠ y` of `TwoBead` is *not* needed and is deliberately absent: the two windows
`k = 1` and `k = -1` are already mutually exclusive (one forces `x < y`, the other `y < x`),
so the case split is exhaustive without it. -/
theorem twoAssign_eq_zero_of_le_two {e : ℕ} (he : 0 < e) (he2 : e ≤ 2) (M : Finset ℤ)
    (x y : ℤ) (hx : x ∈ M) (hxe : x + (e : ℤ) ∉ M) (hy : y ∈ M) (hye : y + (e : ℤ) ∉ M) :
    twoAssign (ribbonHeight e M x : ℤ) (ribbonHeight e M y : ℤ) (crossIndex e e x y) = 0 := by
  rw [twoAssign_eq_zero_iff]
  obtain rfl | rfl : e = 1 ∨ e = 2 := by omega
  · -- `e = 1`: the open window `(y, y+1)` is empty, so both indicators vanish.
    left
    unfold crossIndex
    push_cast
    split_ifs <;> omega
  · -- `e = 2`: a nonzero `k` pins `x` next to `y`, and legality evaluates the windows.
    have hk : crossIndex 2 2 x y
        = (if y < x + 2 ∧ x + 2 < y + 2 then 1 else 0)
          - (if y < x ∧ x < y + 2 then 1 else 0) := by
      unfold crossIndex; push_cast; rfl
    push_cast at hxe hye
    by_cases hA : y < x + 2 ∧ x + 2 < y + 2
    · -- `k = 1`, which forces `x = y - 1`; then `P = 1[y ∈ M] = 1` and `Q = 1[x+2 ∈ M] = 0`.
      have hB : ¬(y < x ∧ x < y + 2) := by omega
      right
      rw [hk, if_pos hA, if_neg hB, ribbonHeight_two, ribbonHeight_two,
        if_neg (show y + 1 ∉ M by rw [show y + 1 = x + 2 by omega]; exact hxe),
        if_pos (show x + 1 ∈ M by rw [show x + 1 = y by omega]; exact hy)]
      norm_num
    · by_cases hB : y < x ∧ x < y + 2
      · -- `k = -1`, which forces `x = y + 1`; then `P = 1[y+2 ∈ M] = 0` and `Q = 1[x ∈ M] = 1`.
        right
        rw [hk, if_neg hA, if_pos hB, ribbonHeight_two, ribbonHeight_two,
          if_pos (show y + 1 ∈ M by rw [show y + 1 = x by omega]; exact hx),
          if_neg (show x + 1 ∉ M by rw [show x + 1 = y + 2 by omega]; exact hye)]
        norm_num
      · -- neither window changes: `k = 0`.
        left
        rw [hk, if_neg hA, if_neg hB]
        norm_num

/-- **An `e = f = 3` witness.**  `M = {6, 7, 8}`, `b = 6`, `c = 8`: a legal two-bead
assignment with `P = 2`, `Q = 0`, `k = 1`, so `Q ≠ P - k` and the two-assignment sum is
`t s^2 - t^2 s + t - s`, the paper's `(t - s)(1 - st)` of Remark 4.3.  Together with
`twoAssign_eq_zero_of_le_two` this makes `e ≥ 3` exactly the right hypothesis. -/
theorem exists_twoAssign_ne_zero_three :
    ∃ (M : Finset ℤ) (x y : ℤ), x ∈ M ∧ x + ((3 : ℕ) : ℤ) ∉ M ∧ y ∈ M
      ∧ y + ((3 : ℕ) : ℤ) ∉ M ∧ TwoBead 3 3 x y
      ∧ twoAssign (ribbonHeight 3 M x : ℤ) (ribbonHeight 3 M y : ℤ)
          (crossIndex 3 3 x y) ≠ 0 := by
  classical
  refine ⟨Finset.Icc (6 : ℤ) 8, 6, 8, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num
  · norm_num [Finset.mem_Icc]
  · norm_num
  · norm_num [Finset.mem_Icc]
  · norm_num [TwoBead]
  · have hP : ribbonHeight 3 (Finset.Icc (6 : ℤ) 8) 6 = 2 := by
      unfold ribbonHeight
      rw [show (Finset.Icc (6 : ℤ) 8).filter (fun z => 6 < z ∧ z < 6 + ((3 : ℕ) : ℤ))
          = {7, 8} from ?_]
      · decide
      · ext z
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
        push_cast
        omega
    have hQ : ribbonHeight 3 (Finset.Icc (6 : ℤ) 8) 8 = 0 := by
      unfold ribbonHeight
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro z hz
      simp only [Finset.mem_Icc] at hz
      push_cast
      omega
    have hk : crossIndex 3 3 (6 : ℤ) 8 = 1 := by unfold crossIndex; norm_num
    rw [hP, hQ, hk, Ne, twoAssign_eq_zero_iff]
    norm_num

end EDependence

end TworowD4Kernel
