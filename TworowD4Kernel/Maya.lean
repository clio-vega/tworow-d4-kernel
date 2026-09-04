/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.SymmDiff
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-!
# Maya diagrams and `|μ| = |λ| + e`

This module removes the boundary that `TworowD4Kernel.AbacusRibbon` stated about itself:

> "`M(λ)` is a `Finset`, not the cofinite Maya set, so `sum_addRibbon` is a *shadow* of
> `|μ| = |λ| + e`, not a proof."

Here the bead set is the genuine Maya set — a set `M ⊆ ℤ` which is cofinite in `ℤ_{<0}` and
finite in `ℤ_{≥0}` — and `Maya.size` is the honest `|λ|`. The theorem `Maya.size_addRibbon`
is then literally `|μ| = |λ| + e`, with no `Finset` truncation in the statement.

## The size, and why it is `|λ|`

For a partition `λ` the Maya set is `M(λ) = {λ_j - j : j ≥ 1}`, and the empty partition gives
the **vacuum** `vacuum = M(∅) = {-1, -2, …} = Set.Iio 0`. The bead sum `∑_{x ∈ M} x` diverges,
but the *vacuum-relative* bead sum does not:

`size M = ∑_{x ∈ M \ vacuum} x - ∑_{x ∈ vacuum \ M} x`

and this equals `|λ|`, because for `N ≥ ℓ(λ)`,
`∑_{j≤N} (λ_j - j) - ∑_{j≤N} (-j) = ∑_{j≤N} λ_j = |λ|`, while the two families agree for
`j > ℓ(λ)`, so the truncation may be dropped. Sanity anchors below: `size_vacuum = 0`, and
`size` of the one-box diagram is `1`.

## The finiteness condition, chosen to be one condition and not two

`(M ∩ ℤ_{≥0})` finite together with `(ℤ_{<0} \ M)` finite is *exactly* `(M ∆ vacuum).Finite`,
since `M ∆ vacuum = (M \ vacuum) ∪ (vacuum \ M)`. Carrying the single symmetric-difference
hypothesis is what makes the bead move cheap: a move is itself a symmetric difference, and
`∆` is associative, so
`(moveBead e M b) ∆ vacuum ⊆ (M ∆ vacuum) ∪ {b, b+e}` needs no case analysis.

## How the vacuum-crossing cases disappear

Naively `size_addRibbon` splits three ways on whether `b` and `b + e` lie below the vacuum
line (`b ≥ 0`; `b < 0 ≤ b + e`; `b + e < 0`) — the bead may cross the line, and then a bead
above the line is traded for a hole below it. The split is avoided by summing over a **common
finite window** `S ⊇ (M ∆ vacuum) ∪ {b, b+e}` and writing
`size = ∑_{x ∈ S} (wt M x - wt vacuum x)` (`sizeOn`, well-defined by
`sizeOn_eq_of_subset`). Subtracting, the `wt vacuum` terms cancel *identically* — before any
case analysis — and what is left is supported on `{b, b + e}`.

## Relation to `TworowD4Kernel.AbacusRibbon`

* **Superseded:** `sum_addRibbon`. Its `∑ x ∈ M, x` is replaced here by `Maya.size`, and
  `Maya.size_addRibbon` is the same orientation statement with the correct object.
* **Not superseded:** everything about `ribbonHeight` — `ribbonHeight_addRibbon`,
  `ribbonHeight_le_sub_one`, `ribbonHeight_lt`, the attainment witnesses. Height is a count
  of beads in the *bounded open window* `(b, b + e)`, so it is genuinely a finite quantity and
  the `Finset` model is faithful for it; nothing is gained by repeating it here.
* **Not superseded:** the round-trip lemmas `addRibbon_removeRibbon` / `removeRibbon_addRibbon`
  and the negative control `exists_addRibbon_not_removeRibbon_of_mem`. `Maya.moveBead` is the
  same formula on `Set ℤ`; the collision phenomenon is identical and is not re-derived.

The abacus dictionary being formalised (`lem:dict`(iii) of
`proofs/2026-08-31-Q59-commutator-rigidity.tex`) is classical, as used by Uglov
(`arXiv:math/9905196`, §3) and Leclerc–Thibon (`arXiv:q-alg/9512031`, §2).
-/

namespace TworowD4Kernel

open Finset

/-- The vacuum Maya diagram `M(∅) = {-1, -2, …}`, i.e. the charge-`0` empty partition. -/
def vacuum : Set ℤ := Set.Iio 0

open Classical in
/-- The weight a site contributes to a bead sum: its own value if occupied, `0` if empty. -/
noncomputable def wt (A : Set ℤ) (x : ℤ) : ℤ := if x ∈ A then x else 0

theorem wt_of_mem {A : Set ℤ} {x : ℤ} (h : x ∈ A) : wt A x = x := by
  unfold wt; exact if_pos h

theorem wt_of_notMem {A : Set ℤ} {x : ℤ} (h : x ∉ A) : wt A x = 0 := by
  unfold wt; exact if_neg h

/-- Off the symmetric difference the two sets agree, so their weights agree. This is the one
fact that makes `sizeOn` independent of the window. -/
theorem wt_eq_of_notMem_symmDiff {A B : Set ℤ} {x : ℤ} (h : x ∉ symmDiff A B) :
    wt A x = wt B x := by
  have key : x ∈ A ↔ x ∈ B := by
    rw [Set.mem_symmDiff] at h
    tauto
  by_cases hA : x ∈ A
  · rw [wt_of_mem hA, wt_of_mem (key.1 hA)]
  · rw [wt_of_notMem hA, wt_of_notMem (fun hB => hA (key.2 hB))]

/-- The vacuum-relative bead sum of `A`, computed over a finite window `S`. Meaningful
exactly when `S` contains `A ∆ vacuum`; see `sizeOn_eq_of_subset`. -/
noncomputable def sizeOn (S : Finset ℤ) (A : Set ℤ) : ℤ :=
  ∑ x ∈ S, (wt A x - wt vacuum x)

/-- Enlarging the window past `A ∆ vacuum` does not change `sizeOn`: the new sites contribute
`wt A x - wt vacuum x = 0`. -/
theorem sizeOn_eq_of_subset {A : Set ℤ} {S T : Finset ℤ}
    (hS : ∀ x ∈ symmDiff A vacuum, x ∈ S) (hST : S ⊆ T) :
    sizeOn S A = sizeOn T A := by
  refine Finset.sum_subset hST ?_
  intro x _ hxS
  have hx : x ∉ symmDiff A vacuum := fun h => hxS (hS x h)
  rw [wt_eq_of_notMem_symmDiff hx, sub_self]

/-- A **Maya diagram**: a set of beads differing from the vacuum in finitely many sites.
Unfolding `∆`, this says `M ∩ ℤ_{≥0}` is finite and `ℤ_{<0} \ M` is finite — the diagram is
finite above and cofinite below. -/
structure Maya where
  /-- The occupied sites. -/
  carrier : Set ℤ
  /-- Finitely many sites differ from the vacuum. -/
  fin : (symmDiff carrier vacuum).Finite

namespace Maya

/-- `|λ|`: the vacuum-relative bead sum, over the canonical window `M ∆ vacuum`. -/
noncomputable def size (M : Maya) : ℤ := sizeOn M.fin.toFinset M.carrier

/-- `size` may be computed over any window containing `M ∆ vacuum`. -/
theorem size_eq_sizeOn (M : Maya) {S : Finset ℤ}
    (hS : ∀ x ∈ symmDiff M.carrier vacuum, x ∈ S) : M.size = sizeOn S M.carrier := by
  refine sizeOn_eq_of_subset (fun x hx => ?_) ?_
  · exact M.fin.mem_toFinset.2 hx
  · intro x hx
    exact hS x (M.fin.mem_toFinset.1 hx)

/-- The vacuum is a Maya diagram: it differs from itself nowhere. -/
theorem vacuum_fin : (symmDiff vacuum vacuum).Finite := by
  rw [symmDiff_self]
  exact Set.finite_empty

/-- `M(∅)`, the empty partition. -/
noncomputable def nil : Maya := ⟨vacuum, vacuum_fin⟩

/-- **Anchor.** `|∅| = 0`. -/
@[simp]
theorem size_nil : nil.size = 0 := by
  unfold size sizeOn nil
  refine Finset.sum_eq_zero ?_
  intro x _
  exact sub_self _

end Maya

/-- Move the bead at `b` up to `b + e`: the abacus form of adding an `e`-ribbon.
Same formula as `TworowD4Kernel.addRibbon`, on `Set ℤ` instead of `Finset ℤ`.
Intended domain: `b ∈ A`, `b + e ∉ A` (paper `lem:dict`(iii)). -/
def moveBead (e : ℕ) (A : Set ℤ) (b : ℤ) : Set ℤ := insert (b + (e : ℤ)) (A \ {b})

theorem mem_moveBead {e : ℕ} {A : Set ℤ} {b x : ℤ} :
    x ∈ moveBead e A b ↔ x = b + (e : ℤ) ∨ (x ∈ A ∧ x ≠ b) := by
  simp [moveBead]

/-- Away from the two moved sites, the bead set is unchanged. -/
theorem mem_moveBead_of_ne {e : ℕ} {A : Set ℤ} {b x : ℤ} (h1 : x ≠ b)
    (h2 : x ≠ b + (e : ℤ)) : x ∈ moveBead e A b ↔ x ∈ A := by
  rw [mem_moveBead]
  tauto

theorem moveBead_mem_self (e : ℕ) (A : Set ℤ) (b : ℤ) : b + (e : ℤ) ∈ moveBead e A b := by
  rw [mem_moveBead]; exact Or.inl rfl

theorem moveBead_notMem_self {e : ℕ} (A : Set ℤ) (b : ℤ) (he : 0 < e) :
    b ∉ moveBead e A b := by
  rw [mem_moveBead]
  rintro (h | ⟨-, h⟩)
  · omega
  · exact h rfl

/-- A bead move is itself a symmetric difference, so it perturbs `A ∆ vacuum` inside
`{b, b + e}`. No case analysis on the vacuum line. -/
theorem symmDiff_moveBead_subset (e : ℕ) (A : Set ℤ) (b : ℤ) :
    symmDiff (moveBead e A b) vacuum ⊆ symmDiff A vacuum ∪ {b, b + (e : ℤ)} := by
  intro x hx
  by_cases h1 : x = b
  · exact Or.inr (by simp [h1])
  by_cases h2 : x = b + (e : ℤ)
  · exact Or.inr (by simp [h2])
  refine Or.inl ?_
  rw [Set.mem_symmDiff] at hx ⊢
  rw [mem_moveBead_of_ne h1 h2] at hx
  exact hx

theorem moveBead_fin {e : ℕ} {A : Set ℤ} (hA : (symmDiff A vacuum).Finite) (b : ℤ) :
    (symmDiff (moveBead e A b) vacuum).Finite :=
  Set.Finite.subset (hA.union ((Set.finite_singleton (b + (e : ℤ))).insert b))
    (symmDiff_moveBead_subset e A b)

namespace Maya

/-- Adding an `e`-ribbon to a Maya diagram. The finiteness condition survives the move. -/
noncomputable def addRibbon (M : Maya) (e : ℕ) (b : ℤ) : Maya :=
  ⟨moveBead e M.carrier b, moveBead_fin M.fin b⟩

@[simp]
theorem addRibbon_carrier (M : Maya) (e : ℕ) (b : ℤ) :
    (M.addRibbon e b).carrier = moveBead e M.carrier b := rfl

/-- **`|μ| = |λ| + e`.** Adding an `e`-ribbon to a Maya diagram raises its size by exactly
`e`. This is the theorem `AbacusRibbon.sum_addRibbon` was a shadow of: the bead set here is
the genuine cofinite Maya set and `size` is the genuine `|λ|`.

Paper `lem:dict`(iii) of `proofs/2026-08-31-Q59-commutator-rigidity.tex`; classical, cf.
Uglov `arXiv:math/9905196` §3, Leclerc–Thibon `arXiv:q-alg/9512031` §2. -/
theorem size_addRibbon {e : ℕ} {M : Maya} {b : ℤ} (he : 0 < e)
    (hb : b ∈ M.carrier) (hbe : b + (e : ℤ) ∉ M.carrier) :
    (M.addRibbon e b).size = M.size + e := by
  classical
  -- the common window: the canonical one for `M`, plus the two moved sites
  set S : Finset ℤ := M.fin.toFinset ∪ {b, b + (e : ℤ)} with hSdef
  have hbS : b ∈ S := by simp [hSdef]
  have hbeS : b + (e : ℤ) ∈ S := by simp [hSdef]
  have hne : b ≠ b + (e : ℤ) := by omega
  -- both sizes are computed over `S`
  have hM : M.size = sizeOn S M.carrier := by
    refine M.size_eq_sizeOn (fun x hx => ?_)
    simp only [hSdef, Finset.mem_union]
    exact Or.inl (M.fin.mem_toFinset.2 hx)
  have hM' : (M.addRibbon e b).size = sizeOn S (moveBead e M.carrier b) := by
    refine (M.addRibbon e b).size_eq_sizeOn (fun x hx => ?_)
    rcases symmDiff_moveBead_subset e M.carrier b hx with h | h
    · simp only [hSdef, Finset.mem_union]
      exact Or.inl (M.fin.mem_toFinset.2 h)
    · rcases h with h | h
      · exact h ▸ hbS
      · rw [Set.mem_singleton_iff] at h
        exact h ▸ hbeS
  -- the `wt vacuum` terms cancel identically, before any case analysis
  have hdiff : sizeOn S (moveBead e M.carrier b) - sizeOn S M.carrier
      = ∑ x ∈ S, (wt (moveBead e M.carrier b) x - wt M.carrier x) := by
    unfold sizeOn
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun x _ => by ring)
  -- what is left is supported on the two moved sites
  have hsupp : ∑ x ∈ S, (wt (moveBead e M.carrier b) x - wt M.carrier x)
      = ∑ x ∈ ({b, b + (e : ℤ)} : Finset ℤ), (wt (moveBead e M.carrier b) x - wt M.carrier x) := by
    refine (Finset.sum_subset ?_ ?_).symm
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with h | h
      · exact h ▸ hbS
      · exact h ▸ hbeS
    · intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      have h1 : x ≠ b := fun h => hx (Or.inl h)
      have h2 : x ≠ b + (e : ℤ) := fun h => hx (Or.inr h)
      rw [wt_eq_of_notMem_symmDiff (A := moveBead e M.carrier b) (B := M.carrier) ?_, sub_self]
      rw [Set.mem_symmDiff]
      rw [mem_moveBead_of_ne h1 h2]
      tauto
  -- and there it is `-b + (b + e)`
  have hpair : ∑ x ∈ ({b, b + (e : ℤ)} : Finset ℤ), (wt (moveBead e M.carrier b) x - wt M.carrier x)
      = (e : ℤ) := by
    rw [Finset.sum_pair hne]
    rw [wt_of_notMem (moveBead_notMem_self M.carrier b he), wt_of_mem hb,
      wt_of_mem (moveBead_mem_self e M.carrier b), wt_of_notMem hbe]
    ring
  have := hdiff.trans (hsupp.trans hpair)
  rw [hM, hM']
  omega

/-! ### Non-vacuity, and the three vacuum-crossing regimes

`size_addRibbon` was proved by summing over a common window, so the vacuum line never entered
the argument. That is exactly why the hypotheses must be witnessed in each regime separately:
a proof that is blind to a distinction cannot itself testify that the distinction is inhabited.
The three regimes are `b < 0 ≤ b + e` (the bead crosses the line, trading a hole below for a
bead above), `0 ≤ b` (entirely above), and `b + e < 0` (entirely below, filling a pre-existing
hole). All three occur, with the side conditions checked. -/

/-- `M((1))`: one box. From the vacuum, move the bead at `-1` up to `0`. -/
noncomputable def onebox : Maya := nil.addRibbon 1 (-1)

theorem mem_onebox {x : ℤ} : x ∈ onebox.carrier ↔ x = 0 ∨ (x < 0 ∧ x ≠ -1) := by
  unfold onebox
  rw [addRibbon_carrier, mem_moveBead]
  norm_num [nil, vacuum, Set.mem_Iio]

/-- **Regime 1, crossing the vacuum line** (`b = -1 < 0 ≤ b + e = 0`): `|(1)| = 1`. -/
theorem size_onebox : onebox.size = 1 := by
  have hb : (-1 : ℤ) ∈ nil.carrier := by norm_num [nil, vacuum, Set.mem_Iio]
  have hbe : (-1 : ℤ) + ((1 : ℕ) : ℤ) ∉ nil.carrier := by norm_num [nil, vacuum, Set.mem_Iio]
  have := size_addRibbon (e := 1) (M := nil) (b := -1) (by norm_num) hb hbe
  rw [onebox, this, size_nil]
  norm_num

/-- **Regime 2, entirely above the vacuum line** (`b = 0 ≥ 0`): `(1) ↦ (3)`, size `1 + 2 = 3`. -/
theorem size_addRibbon_above : (onebox.addRibbon 2 0).size = 3 := by
  have hb : (0 : ℤ) ∈ onebox.carrier := mem_onebox.2 (Or.inl rfl)
  have hbe : (0 : ℤ) + ((2 : ℕ) : ℤ) ∉ onebox.carrier := by
    rw [mem_onebox]; norm_num
  have := size_addRibbon (e := 2) (M := onebox) (b := 0) (by norm_num) hb hbe
  rw [this, size_onebox]
  norm_num

/-- **Regime 3, entirely below the vacuum line** (`b + e = -1 < 0`): the `2`-ribbon fills the
hole the first move left at `-1`. `(1) ↦ (1,1,1)`, size `1 + 2 = 3`. -/
theorem size_addRibbon_below : (onebox.addRibbon 2 (-3)).size = 3 := by
  have hb : (-3 : ℤ) ∈ onebox.carrier := mem_onebox.2 (Or.inr (by norm_num))
  have hbe : (-3 : ℤ) + ((2 : ℕ) : ℤ) ∉ onebox.carrier := by
    rw [mem_onebox]; norm_num
  have := size_addRibbon (e := 2) (M := onebox) (b := -3) (by norm_num) hb hbe
  rw [this, size_onebox]
  norm_num

/-! ### Negative control

`size_addRibbon` carries the side condition `b + e ∉ M.carrier`. Dropping it does not merely
weaken the lemma, it falsifies it: moving a bead onto an occupied site destroys a bead, and the
size then records the *hole left behind* rather than the `e` boxes claimed. Without a witness
this is only an assertion about a hypothesis nobody tested. -/

/-- Collision: from the vacuum, `b = -3` with `e = 1` lands on the occupied site `-2`. -/
theorem collision_carrier :
    (nil.addRibbon 1 (-3)).carrier = vacuum \ {(-3 : ℤ)} := by
  rw [addRibbon_carrier]
  ext x
  rw [mem_moveBead]
  simp only [nil, vacuum, Set.mem_Iio, Set.mem_diff, Set.mem_singleton_iff]
  norm_num
  omega

theorem collision_symmDiff :
    symmDiff (nil.addRibbon 1 (-3)).carrier vacuum = {(-3 : ℤ)} := by
  rw [collision_carrier]
  ext x
  rw [Set.mem_symmDiff]
  simp only [vacuum, Set.mem_Iio, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨⟨h, -⟩, h2⟩ | ⟨h, h2⟩)
    · omega
    · by_contra hx
      exact h2 ⟨h, hx⟩
  · rintro rfl
    exact Or.inr ⟨by norm_num, fun h => h.2 rfl⟩

/-- **The control fires.** Both `b ∈ M` and `b + e ∈ M` hold, and the size jumps by `3`, not
by `e = 1`. So `size_addRibbon` is genuinely false on the larger domain and its hypothesis
`hbe` is doing work — this is the `Maya` analogue of
`TworowD4Kernel.exists_addRibbon_not_removeRibbon_of_mem`. -/
theorem exists_size_addRibbon_ne_of_mem :
    ∃ (e : ℕ) (M : Maya) (b : ℤ), 0 < e ∧ b ∈ M.carrier ∧ b + (e : ℤ) ∈ M.carrier ∧
      (M.addRibbon e b).size ≠ M.size + (e : ℤ) := by
  refine ⟨1, nil, -3, by norm_num, by norm_num [nil, vacuum, Set.mem_Iio], by
    norm_num [nil, vacuum, Set.mem_Iio], ?_⟩
  have hS : ∀ x ∈ symmDiff (nil.addRibbon 1 (-3)).carrier vacuum, x ∈ ({-3} : Finset ℤ) := by
    intro x hx
    rw [collision_symmDiff, Set.mem_singleton_iff] at hx
    simp [hx]
  rw [(nil.addRibbon 1 (-3)).size_eq_sizeOn hS, size_nil]
  unfold sizeOn
  rw [Finset.sum_singleton, wt_of_notMem, wt_of_mem]
  · norm_num
  · norm_num [vacuum, Set.mem_Iio]
  · rw [collision_carrier]
    simp

/-! ### Nested hops: the bead count of an interval is invariant

The counting statement behind "**nested ribbon additions commute**".

A hop `b ↦ b + e` occupies the diagonal interval from `b` to `b + e`, and its weight — the
ribbon height of `TworowD4Kernel.ribbonHeight` — is a count of beads inside that interval. A
second hop `b' ↦ b' + e'` whose interval is *nested* inside the first moves a bead from one
site of the interval to another site of the same interval. The count is therefore unchanged,
so the outer hop's weight is unchanged, and the two graded operators commute.

Nesting is the counter-intuitive case. Disjoint intervals obviously commute; *properly
crossing* ones do not. That nested ones do is invisible to every parity or degree argument,
which is why the height-parity route to `[R_e, R_{e'}]` died: once `e ≠ e'` the height parity
is not invariant (2952 of 29644 targets carry both parities).

Everything reduces to `card_filter_addRibbon_of_mem_mem`, which is not about intervals at
all: it says a bead move is invisible to *any* window containing both of its endpoints.
The two interval statements are then read off, and they differ at the top endpoint —

* `count_Ioc_addRibbon_of_nested` needs only `b' + e' ≤ b + e`;
* `count_Ioo_addRibbon_of_nested`, which is the one that controls the **height**, needs the
  strict `b' + e' < b + e`, and `exists_count_Ioo_addRibbon_ne_of_top` shows the strictness
  cannot be dropped.

Both need `b < b'` strictly at the bottom; `exists_count_Ioc_addRibbon_ne_of_bot` shows that
one is tight too.
-/

open Classical in
/-- The number of beads of `M` in the half-open diagonal interval `(b, c]`. This is the
*occupancy* interval of a hop `b ↦ c`. -/
noncomputable def countIoc (M : Maya) (b c : ℤ) : ℕ :=
  ((Finset.Ioc b c).filter (fun x => x ∈ M.carrier)).card

open Classical in
/-- The number of beads of `M` in the open diagonal interval `(b, c)`. For `c = b + e` this
is the **ribbon height** of paper `lem:dict`(iii), matching
`TworowD4Kernel.ribbonHeight`, which filters on `b < x ∧ x < b + e`. -/
noncomputable def countIoo (M : Maya) (b c : ℤ) : ℕ :=
  ((Finset.Ioo b c).filter (fun x => x ∈ M.carrier)).card

open Classical in
/-- The move `b' ↦ b' + e'` rewrites any window `T` containing both endpoints: it erases `b'`
and inserts `b' + e'`. No hypothesis on `M` is needed for the set identity. -/
theorem filter_addRibbon_eq {e' : ℕ} {M : Maya} {T : Finset ℤ} {b' : ℤ}
    (hbe'T : b' + (e' : ℤ) ∈ T) :
    T.filter (fun x => x ∈ (M.addRibbon e' b').carrier)
      = insert (b' + (e' : ℤ)) ((T.filter (fun x => x ∈ M.carrier)).erase b') := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase, addRibbon_carrier,
    mem_moveBead]
  constructor
  · rintro ⟨hx, h | ⟨hA, hne⟩⟩
    · exact Or.inl h
    · exact Or.inr ⟨hne, hx, hA⟩
  · rintro (rfl | ⟨hne, hx, hA⟩)
    · exact ⟨hbe'T, Or.inl rfl⟩
    · exact ⟨hx, Or.inr ⟨hA, hne⟩⟩

open Classical in
/-- **The counting core.** A legal bead move is invisible to any window that contains *both*
of its endpoints: one bead leaves the window at `b'` and one enters it at `b' + e'`.

Nothing here is about intervals or about nesting; nesting enters only when this is applied,
as the statement that the inner hop's endpoints both lie in the outer hop's window. -/
theorem card_filter_addRibbon_of_mem_mem {e' : ℕ} {M : Maya} {T : Finset ℤ} {b' : ℤ}
    (hb'T : b' ∈ T) (hbe'T : b' + (e' : ℤ) ∈ T)
    (hmem : b' ∈ M.carrier) (hnot : b' + (e' : ℤ) ∉ M.carrier) :
    (T.filter (fun x => x ∈ (M.addRibbon e' b').carrier)).card
      = (T.filter (fun x => x ∈ M.carrier)).card := by
  have hmemF : b' ∈ T.filter (fun x => x ∈ M.carrier) := Finset.mem_filter.2 ⟨hb'T, hmem⟩
  have hnotF : b' + (e' : ℤ) ∉ (T.filter (fun x => x ∈ M.carrier)).erase b' := fun h =>
    hnot (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).2
  have hpos : 1 ≤ (T.filter (fun x => x ∈ M.carrier)).card :=
    Finset.card_pos.2 ⟨b', hmemF⟩
  rw [filter_addRibbon_eq hbe'T, Finset.card_insert_of_notMem hnotF,
    Finset.card_erase_of_mem hmemF]
  omega

/-- **`count_Ioc_addRibbon_of_nested`.** If the inner hop `b' ↦ b' + e'` is nested in the
outer hop's occupancy interval (`b < b'` and `b' + e' ≤ b + e`) and is legal, then the bead
count of `(b, b + e]` is unchanged.

Paper `lem:dict`(iii) of `proofs/2026-08-31-Q59-commutator-rigidity.tex`; the abacus
dictionary is classical, cf. Uglov `arXiv:math/9905196` §3 and Leclerc–Thibon
`arXiv:q-alg/9512031` §2. -/
theorem count_Ioc_addRibbon_of_nested {e e' : ℕ} {M : Maya} {b b' : ℤ}
    (hlt : b < b') (hle : b' + (e' : ℤ) ≤ b + (e : ℤ))
    (hmem : b' ∈ M.carrier) (hnot : b' + (e' : ℤ) ∉ M.carrier) :
    (M.addRibbon e' b').countIoc b (b + (e : ℤ)) = M.countIoc b (b + (e : ℤ)) := by
  have he' : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
  exact card_filter_addRibbon_of_mem_mem
    (Finset.mem_Ioc.2 ⟨hlt, by omega⟩) (Finset.mem_Ioc.2 ⟨by omega, hle⟩) hmem hnot

/-- **The height version.** Same statement for the *open* window `(b, b + e)`, which is the
one `TworowD4Kernel.ribbonHeight` counts — so this is literally "the outer hop's weight is
unchanged by a nested inner hop".

The top endpoint is **strict** here, and that is not cosmetic: at `b' + e' = b + e` the inner
hop moves a bead out of the open window onto its right endpoint, and the height drops by one.
See `exists_count_Ioo_addRibbon_ne_of_top`. -/
theorem count_Ioo_addRibbon_of_nested {e e' : ℕ} {M : Maya} {b b' : ℤ}
    (hlt : b < b') (hlt' : b' + (e' : ℤ) < b + (e : ℤ))
    (hmem : b' ∈ M.carrier) (hnot : b' + (e' : ℤ) ∉ M.carrier) :
    (M.addRibbon e' b').countIoo b (b + (e : ℤ)) = M.countIoo b (b + (e : ℤ)) := by
  have he' : (0 : ℤ) ≤ (e' : ℤ) := Int.natCast_nonneg e'
  exact card_filter_addRibbon_of_mem_mem
    (Finset.mem_Ioo.2 ⟨hlt, by omega⟩) (Finset.mem_Ioo.2 ⟨by omega, hlt'⟩) hmem hnot

/-! ### The two boundary controls

`count_Ioc_addRibbon_of_nested` and `count_Ioo_addRibbon_of_nested` differ in exactly one
inequality, and each has a strict inequality that a careless reading would relax. Both are
tight, and the witnesses below are in `onebox`, whose carrier is
`{0} ∪ (ℤ_{<0} \ {-1})` — occupied at `0, -2, -3, …`, empty at `-1` and at every site `≥ 1`.
-/

open Classical in
/-- Inside `(-2, 1]` the only bead of `onebox` is `0`. -/
theorem filter_Ioc_onebox : (Finset.Ioc (-2 : ℤ) 1).filter
    (fun x => x ∈ onebox.carrier) = {0} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton, mem_onebox]
  omega

open Classical in
/-- After the hop `-2 ↦ -1` there are two: the bead has entered the window at `-1` and the
one it left, `-2`, was never in the window to begin with. -/
theorem filter_Ioc_onebox_moved : (Finset.Ioc (-2 : ℤ) 1).filter
    (fun x => x ∈ (onebox.addRibbon 1 (-2)).carrier) = {-1, 0} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_insert, Finset.mem_singleton,
    addRibbon_carrier, mem_moveBead, mem_onebox]
  omega

theorem countIoc_onebox : onebox.countIoc (-2) 1 = 1 := by
  unfold countIoc
  rw [filter_Ioc_onebox]
  rfl

theorem countIoc_onebox_moved : (onebox.addRibbon 1 (-2)).countIoc (-2) 1 = 2 := by
  unfold countIoc
  rw [filter_Ioc_onebox_moved]
  decide

/-- **Control 1: `b < b'` cannot be relaxed to `b ≤ b'`.** With `b = b' = -2`, `e = 3`,
`e' = 1` the inner hop `-2 ↦ -1` is legal and lands inside `(b, b + e] = (-2, 1]`, but its
*source* `b'` is the excluded left endpoint — so a bead enters the window and none leaves,
and the count goes `1 ↦ 2`. Every other hypothesis of `count_Ioc_addRibbon_of_nested`
holds. -/
theorem exists_count_Ioc_addRibbon_ne_of_bot :
    ∃ (e e' : ℕ) (M : Maya) (b b' : ℤ), 0 < e ∧ 0 < e' ∧ b = b' ∧
      b' + (e' : ℤ) ≤ b + (e : ℤ) ∧ b' ∈ M.carrier ∧ b' + (e' : ℤ) ∉ M.carrier ∧
      (M.addRibbon e' b').countIoc b (b + (e : ℤ)) ≠ M.countIoc b (b + (e : ℤ)) := by
  refine ⟨3, 1, onebox, -2, -2, by norm_num, by norm_num, rfl, by norm_num,
    mem_onebox.2 (Or.inr (by norm_num)), by rw [mem_onebox]; norm_num, ?_⟩
  have hb : (-2 : ℤ) + ((3 : ℕ) : ℤ) = 1 := by norm_num
  rw [hb, countIoc_onebox, countIoc_onebox_moved]
  norm_num

open Classical in
/-- Inside the open window `(-4, -1)` the beads of `onebox` are `-3` and `-2`. -/
theorem filter_Ioo_onebox : (Finset.Ioo (-4 : ℤ) (-1)).filter
    (fun x => x ∈ onebox.carrier) = {-3, -2} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_insert, Finset.mem_singleton,
    mem_onebox]
  omega

open Classical in
/-- After the hop `-3 ↦ -1` only `-2` is left: the bead has landed on the window's excluded
right endpoint. -/
theorem filter_Ioo_onebox_moved : (Finset.Ioo (-4 : ℤ) (-1)).filter
    (fun x => x ∈ (onebox.addRibbon 2 (-3)).carrier) = {-2} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_singleton, addRibbon_carrier,
    mem_moveBead, mem_onebox]
  omega

theorem countIoo_onebox : onebox.countIoo (-4) (-1) = 2 := by
  unfold countIoo
  rw [filter_Ioo_onebox]
  decide

theorem countIoo_onebox_moved : (onebox.addRibbon 2 (-3)).countIoo (-4) (-1) = 1 := by
  unfold countIoo
  rw [filter_Ioo_onebox_moved]
  rfl

/-- **Control 2: in the *open* window the top endpoint must be strict.** With `b = -4`,
`e = 3`, `b' = -3`, `e' = 2` the inner hop `-3 ↦ -1` is legal and satisfies `b < b'` and
`b' + e' = b + e` — i.e. *every* hypothesis of `count_Ioc_addRibbon_of_nested`. The bead at
`-3` leaves the open window `(-4, -1)` and lands on its excluded right endpoint, so the
**height** drops `2 ↦ 1`.

So the half-open counting lemma does not by itself say the outer hop's *weight* is
preserved; `count_Ioo_addRibbon_of_nested`, with its strict `<`, is the statement that
does. -/
theorem exists_count_Ioo_addRibbon_ne_of_top :
    ∃ (e e' : ℕ) (M : Maya) (b b' : ℤ), 0 < e ∧ 0 < e' ∧ b < b' ∧
      b' + (e' : ℤ) = b + (e : ℤ) ∧ b' ∈ M.carrier ∧ b' + (e' : ℤ) ∉ M.carrier ∧
      (M.addRibbon e' b').countIoo b (b + (e : ℤ)) ≠ M.countIoo b (b + (e : ℤ)) := by
  refine ⟨3, 2, onebox, -4, -3, by norm_num, by norm_num, by omega, by norm_num,
    mem_onebox.2 (Or.inr (by norm_num)), by rw [mem_onebox]; norm_num, ?_⟩
  have hb : (-4 : ℤ) + ((3 : ℕ) : ℤ) = -1 := by norm_num
  rw [hb, countIoo_onebox, countIoo_onebox_moved]
  norm_num
end Maya

end TworowD4Kernel
