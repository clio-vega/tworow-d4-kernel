/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.CrossRankOneBead

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

end TworowD4Kernel
