/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import TworowD4Kernel.MotegiOrder
import Mathlib.Order.Interval.Finset.Nat

/-!
# Motegi's order is the tail-counting order

Formalisation of `lem:order` (L261--L285) and `cor:order` (L286--L305) of
`projects/proofs/2026-10-19-c2-sa-divisors-full-q.tex`.

The order `MLe` itself is **not** defined here: it lives in
`TworowD4Kernel.MotegiOrder` (committed 2026-10-17) in Motegi's own increasing
enumeration, `M ≥ I ⟺ s ≥ r ∧ m_{s−r+j} ≥ i_j` (Motegi, *F-function
properties*, Thm 2.6(i), arXiv:2610.15344 L625--L636).  Everything below is
therefore a genuinely falsifiable theorem about a definition this session did
not author.

## Main results

* `tail` — the paper's `A_{≥k} := #{c ∈ A : c ≥ k}`.
* `MLe_iff_tail` (**T1**, `lem:order`) — `MLe B A ↔ ∀ k, tail B k ≤ tail A k`.
* `MLe_refl`, `MLe_trans`, `MLe_antisymm` (**T2**, `cor:order`(1)).
* `mem_iff_tail_lt` — *the counting function determines the set*,
  `k ∈ A ↔ tail A (k+1) < tail A k`.  The paper's route to antisymmetry.
* `MLe_antisymm_asc` — antisymmetry again, by a **different** mechanism
  (the sorted encoding alone, no counting function).  See `P3` in the record.
* `MLe_of_subset`, `MLe_erase` (**T3**, `cor:order`(2)).
* `MLe_iff_compl` (**T4**, `cor:order`(3)) — complementation inside
  `Finset.range N` reverses the order.
* `motegiComplOrderIso` — T4 upgraded: complementation is an `OrderIso` onto
  the **order dual**, i.e. an order-reversing involution.

## Index conventions

The paper works inside `[N] = {1,…,N}` and quantifies `k ∈ [N]`; Lean works
over all of `Finset ℕ` and quantifies `k : ℕ`.  These are *different*
statements and the Lean one is the correct generalisation: over `Finset ℕ` the
cardinality clause `r ≤ s` is the instance `k = 0` (`tail A 0 = A.card`),
whereas in `[N]` it is the instance `k = 1`, because no element is `< 1`.
See the named controls `L1a`/`L1b` at the end of the file.

Complementation is taken inside `Finset.range N = {0,…,N−1}`, so the paper's
`(Aᶜ)_{≥k} = (N−k+1) − A_{≥k}` reads here as `tail (range N \ A) k = (N−k) −
tail A k` (`tail_sdiff_range`).
-/

namespace TworowD4Kernel
namespace Motegi

open Finset List

/-! ### The tail-counting function -/

/-- The paper's `A_{≥k} := #{c ∈ A : c ≥ k}` (`lem:order`, L262). -/
def tail (A : Finset ℕ) (k : ℕ) : ℕ := (A.filter (fun c => k ≤ c)).card

@[simp] lemma tail_zero (A : Finset ℕ) : tail A 0 = A.card := by
  simp [tail]

lemma tail_le_card (A : Finset ℕ) (k : ℕ) : tail A k ≤ A.card :=
  Finset.card_filter_le _ _

/-- `tail` counts along the decreasing enumeration. -/
lemma tail_eq_countP (A : Finset ℕ) (k : ℕ) :
    tail A k = (descList A).countP (fun c => k ≤ c) := by
  rw [tail, descList, Finset.card, Finset.filter_val,
    ← Multiset.countP_eq_card_filter, ← Multiset.coe_countP, Finset.sort_eq]

/-! ### The bridge between the sorted enumeration and the tail count

For a list sorted **decreasingly**, "the `(i+1)`-st entry is `≥ k`" and "at
least `i+1` entries are `≥ k`" are the same statement.  This is the only place
where the sortedness of the enumeration is used, and it is what makes `lem:order`
true. -/

/-- A decreasingly sorted list of naturals: its `i`-th entry is `≥ k` exactly
when it has more than `i` entries `≥ k`. -/
theorem getD_le_iff_lt_countP {l : List ℕ} (hs : l.Pairwise (· ≥ ·)) {k i : ℕ}
    (hi : i < l.length) :
    k ≤ l.getD i 0 ↔ i < l.countP (fun c => k ≤ c) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a t ih =>
    rw [List.pairwise_cons] at hs
    obtain ⟨hhead, ht⟩ := hs
    rw [List.countP_cons]
    match i with
    | 0 =>
      simp only [List.getD_cons_zero]
      constructor
      · intro h
        simp only [decide_eq_true_eq, h, if_true]
        omega
      · intro h
        by_contra hlt
        simp only [decide_eq_true_eq, hlt, if_false] at h
        have hz : ¬ (t.countP (fun c => k ≤ c) = 0) := by omega
        rw [List.countP_eq_zero] at hz
        push Not at hz
        obtain ⟨x, hx, hpx⟩ := hz
        exact hlt (le_trans (by simpa using hpx) (hhead x hx))
    | (j+1) =>
      simp only [List.getD_cons_succ]
      rw [ih ht (by simpa using hi)]
      by_cases hak : k ≤ a
      · simp only [decide_eq_true_eq, hak, if_true]; omega
      · have h0 : t.countP (fun c => k ≤ c) = 0 := by
          rw [List.countP_eq_zero]
          intro x hx
          simp only [decide_eq_true_eq, not_le]
          exact lt_of_le_of_lt (hhead x hx) (by omega)
        simp only [decide_eq_true_eq, hak, if_false, h0]
        omega

/-- The `(i+1)`-st largest element of `A` is `≥ k` iff `A` has more than `i`
elements `≥ k`. -/
theorem le_desc_iff_lt_tail {A : Finset ℕ} {k i : ℕ} (hi : i < A.card) :
    k ≤ desc A i ↔ i < tail A k := by
  rw [tail_eq_countP, desc]
  exact getD_le_iff_lt_countP (descList_pairwise A) (by simpa using hi)

/-! ### T1 — `lem:order` -/

/-- **T1 = `lem:order`** (tex L261--L269).  Motegi's order is the tail-counting
order: `B ≤ A` iff `B_{≥k} ≤ A_{≥k}` for every `k`.

Over `Finset ℕ` the quantifier is `∀ k : ℕ`; the instance `k = 0` *is* the
cardinality clause `|B| ≤ |A|`, which in the paper's `[N]`-indexed statement is
carried by `k = 1`. -/
theorem MLe_iff_tail (B A : Finset ℕ) : MLe B A ↔ ∀ k, tail B k ≤ tail A k := by
  rw [MLe_iff_desc]
  constructor
  · rintro ⟨hcard, h⟩ k
    rcases Nat.eq_zero_or_pos (tail B k) with h0 | hpos
    · omega
    · -- the `(tail B k)`-th largest element of `B` is `≥ k`, hence so is `A`'s
      have hiB : tail B k - 1 < B.card := by
        have := tail_le_card B k; omega
      have hkB : k ≤ desc B (tail B k - 1) :=
        (le_desc_iff_lt_tail hiB).mpr (by omega)
      have hkA : k ≤ desc A (tail B k - 1) :=
        le_trans hkB (h _ hiB)
      have := (le_desc_iff_lt_tail (A := A) (k := k)
        (show tail B k - 1 < A.card by omega)).mp hkA
      omega
  · intro h
    have hcard : B.card ≤ A.card := by simpa using h 0
    refine ⟨hcard, fun c hc => ?_⟩
    -- take `k` to be the `(c+1)`-st largest element of `B`
    have hcB : c < tail B (desc B c) := (le_desc_iff_lt_tail hc).mp (le_refl _)
    have hcA : c < tail A (desc B c) := lt_of_lt_of_le hcB (h _)
    exact (le_desc_iff_lt_tail (show c < A.card by omega)).mpr hcA

/-! ### T2 — `cor:order`(1): `MLe` is a partial order -/

theorem MLe_refl (A : Finset ℕ) : MLe A A :=
  (MLe_iff_tail A A).mpr fun _ => le_refl _

theorem MLe_trans {C B A : Finset ℕ} (h₁ : MLe C B) (h₂ : MLe B A) : MLe C A :=
  (MLe_iff_tail C A).mpr fun k =>
    le_trans ((MLe_iff_tail C B).mp h₁ k) ((MLe_iff_tail B A).mp h₂ k)

/-- **The counting function determines the set** (tex L300--L301): `k ∈ A` iff
the tail count drops at `k`.  Stated via `tail A k = tail A (k+1) + [k ∈ A]`. -/
lemma tail_succ (A : Finset ℕ) (k : ℕ) :
    tail A k = tail A (k + 1) + (if k ∈ A then 1 else 0) := by
  simp only [tail]
  by_cases hk : k ∈ A
  · have hset : A.filter (fun c => k ≤ c) = insert k (A.filter (fun c => k + 1 ≤ c)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hx, hle⟩
        rcases Nat.lt_or_ge k x with h | h
        · exact Or.inr ⟨hx, h⟩
        · exact Or.inl (by omega)
      · rintro (rfl | ⟨hx, hle⟩)
        · exact ⟨hk, le_refl _⟩
        · exact ⟨hx, by omega⟩
    rw [hset, Finset.card_insert_of_notMem (by simp), if_pos hk]
  · have hset : A.filter (fun c => k ≤ c) = A.filter (fun c => k + 1 ≤ c) := by
      ext x
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hx, hle⟩
        refine ⟨hx, ?_⟩
        rcases Nat.lt_or_ge k x with h | h
        · omega
        · exact absurd (show x = k by omega) (by rintro rfl; exact hk hx)
      · rintro ⟨hx, hle⟩; exact ⟨hx, by omega⟩
    rw [hset, if_neg hk]
    omega

theorem mem_iff_tail_lt (A : Finset ℕ) (k : ℕ) : k ∈ A ↔ tail A (k + 1) < tail A k := by
  have h := tail_succ A k
  by_cases hk : k ∈ A
  · rw [if_pos hk] at h
    simp only [hk, true_iff]
    omega
  · rw [if_neg hk] at h
    simp only [hk, false_iff, not_lt]
    omega

/-- **T2, antisymmetry** (tex L299--L301), by the paper's route: `B ≤ A ≤ B`
forces equal tail counts, and the counting function determines the set. -/
theorem MLe_antisymm {B A : Finset ℕ} (h₁ : MLe B A) (h₂ : MLe A B) : B = A := by
  have hAB := (MLe_iff_tail B A).mp h₁
  have hBA := (MLe_iff_tail A B).mp h₂
  have heq : ∀ k, tail B k = tail A k := fun k => le_antisymm (hAB k) (hBA k)
  ext x
  rw [mem_iff_tail_lt, mem_iff_tail_lt, heq, heq]

/-! ### T2 again, by a second mechanism

Antisymmetry does **not** need the counting function: it already falls out of
the sorted encoding, because `MLe B A` and `MLe A B` pin the two increasing
enumerations entrywise.  Recorded because the paper's proof goes the other way
(pre-registration `P3`, arm 2). -/
theorem MLe_antisymm_asc {B A : Finset ℕ} (h₁ : MLe B A) (h₂ : MLe A B) : B = A := by
  obtain ⟨hc₁, k₁⟩ := h₁
  obtain ⟨hc₂, k₂⟩ := h₂
  have hcard : B.card = A.card := le_antisymm hc₁ hc₂
  have hlist : ascList B = ascList A := by
    apply List.ext_getElem (by simp [hcard])
    intro n h1 h2
    have hn : n < B.card := by simpa using h1
    have e₁ := k₁ n hn
    have e₂ := k₂ n (by omega)
    rw [hcard] at e₁ e₂
    simp only [Nat.sub_self, Nat.zero_add] at e₁ e₂
    have heq : asc B n = asc A n := le_antisymm e₁ e₂
    rw [← List.getD_eq_getElem (ascList B) 0 h1, ← List.getD_eq_getElem (ascList A) 0 h2]
    exact heq
  have : (↑(ascList B) : Multiset ℕ) = ↑(ascList A) := by rw [hlist]
  rw [ascList, ascList, Finset.sort_eq, Finset.sort_eq] at this
  exact Finset.val_injective this

/-! ### T3 — `cor:order`(2): closure under deleting an element -/

lemma tail_subset_le {B A : Finset ℕ} (h : B ⊆ A) (k : ℕ) : tail B k ≤ tail A k :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

/-- Any subset is Motegi-below.  (Strictly more than `cor:order`(2) asks, and
the shortest honest route to it.) -/
theorem MLe_of_subset {B A : Finset ℕ} (h : B ⊆ A) : MLe B A :=
  (MLe_iff_tail B A).mpr (tail_subset_le h)

/-- **T3 = `cor:order`(2)** (tex L293--L294, L302): `A ∖ {m} ≤ A`.  The paper
states this for `A ∋ m`; the hypothesis is **not needed** (lesion `L2`). -/
theorem MLe_erase (A : Finset ℕ) (m : ℕ) : MLe (A.erase m) A :=
  MLe_of_subset (Finset.erase_subset _ _)

/-- `cor:order`(2) as the paper uses it: every down-set is closed under
deleting an element. -/
theorem downset_erase_closed {ν A : Finset ℕ} (h : MLe A ν) (m : ℕ) :
    MLe (A.erase m) ν :=
  MLe_trans (MLe_erase A m) h

/-! ### T4 — `cor:order`(3): complementation reverses the order -/

@[simp] lemma tail_range (N k : ℕ) : tail (Finset.range N) k = N - k := by
  rw [tail]
  rw [show (Finset.range N).filter (fun c => k ≤ c) = Finset.Ico k N by
    ext x; simp [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega]
  simp

/-- The paper's `(Aᶜ)_{≥k} = (N−k+1) − A_{≥k}` (tex L303--L305), in `range N`
indexing where it reads `(N−k) − A_{≥k}`. -/
lemma tail_sdiff_range {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Finset.range N) (k : ℕ) :
    tail (Finset.range N \ A) k = (N - k) - tail A k := by
  have hsub : A.filter (fun c => k ≤ c) ⊆ (Finset.range N).filter (fun c => k ≤ c) :=
    Finset.filter_subset_filter _ hA
  have hset : (Finset.range N \ A).filter (fun c => k ≤ c)
      = (Finset.range N).filter (fun c => k ≤ c) \ A.filter (fun c => k ≤ c) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [tail, hset, Finset.card_sdiff_of_subset hsub, ← tail, ← tail, tail_range]

/-- **T4 = `cor:order`(3)** (tex L295--L297, L303--L305): inside `range N`,
complementation reverses Motegi's order.  `N` is a free parameter — any `N`
with `A ∪ B ⊆ range N` will do (lesion `L4`). -/
theorem MLe_iff_compl {A B : Finset ℕ} {N : ℕ}
    (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N) :
    MLe B A ↔ MLe (Finset.range N \ A) (Finset.range N \ B) := by
  rw [MLe_iff_tail, MLe_iff_tail]
  constructor
  · intro h k
    rw [tail_sdiff_range hA, tail_sdiff_range hB]
    have hBA := h k
    have hAk : tail A k ≤ N - k := by
      simpa using tail_subset_le hA k
    omega
  · intro h k
    have hk := h k
    rw [tail_sdiff_range hA, tail_sdiff_range hB] at hk
    have hAk : tail A k ≤ N - k := by simpa using tail_subset_le hA k
    have hBk : tail B k ≤ N - k := by simpa using tail_subset_le hB k
    omega


/-! ### `cor:order`(1) as a bundled partial order, and T4 as an order isomorphism

`Finset ℕ` already carries `≤` (inclusion), so Motegi's order cannot be
installed on it directly.  `MotegiBelow N` is the subsets of `range N` carrying
*Motegi's* order; this is also the ambient in which complementation is defined,
so it is the right home for `cor:order`(3). -/

/-- Subsets of `Finset.range N`, ordered by **Motegi's** order. -/
def MotegiBelow (N : ℕ) : Type := {A : Finset ℕ // A ⊆ Finset.range N}

/-- **T2 bundled** (`cor:order`(1)): `MLe` is a partial order. -/
instance instPartialOrderMotegiBelow (N : ℕ) : PartialOrder (MotegiBelow N) where
  le A B := MLe A.1 B.1
  le_refl A := MLe_refl A.1
  le_trans _ _ _ h₁ h₂ := MLe_trans h₁ h₂
  le_antisymm _ _ h₁ h₂ := Subtype.ext (MLe_antisymm h₁ h₂)

/-- Complementation inside `range N`. -/
def motegiCompl (N : ℕ) (A : MotegiBelow N) : MotegiBelow N :=
  ⟨Finset.range N \ A.1, Finset.sdiff_subset⟩

theorem motegiCompl_involutive (N : ℕ) (A : MotegiBelow N) :
    motegiCompl N (motegiCompl N A) = A :=
  Subtype.ext (Finset.sdiff_sdiff_eq_self A.2)

/-- **T4, strengthened** (pre-registration `P2`): complementation is not merely
an order anti-automorphism in the loose sense — it is an `OrderIso` from the
Motegi poset on subsets of `range N` **onto its order dual**, i.e. an
order-reversing involution. -/
def motegiComplOrderIso (N : ℕ) : MotegiBelow N ≃o (MotegiBelow N)ᵒᵈ where
  toFun A := OrderDual.toDual (motegiCompl N A)
  invFun A := motegiCompl N (OrderDual.ofDual A)
  left_inv := motegiCompl_involutive N
  right_inv _ := congrArg OrderDual.toDual (motegiCompl_involutive N _)
  map_rel_iff' {A B} := (MLe_iff_compl B.2 A.2).symm

/-! ### Controls

Named (not anonymous) so an environment scan can see them.  One per lesion in
the session's lesion register, plus positive and negative controls on T1. -/

/-- Helper: a singleton's tail count vanishes above the element. -/
lemma tail_singleton_eq_zero {a k : ℕ} (h : a < k) : tail ({a} : Finset ℕ) k = 0 := by
  rw [tail, Finset.card_eq_zero]
  ext x
  simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty, iff_false,
    not_and]
  rintro rfl
  omega

lemma tail_empty (k : ℕ) : tail (∅ : Finset ℕ) k = 0 := by simp [tail]

/-- **Control L1a.**  In T1 the quantifier `∀ k` cannot be restricted to
`k ≥ 2`: for `B = {1}`, `A = ∅` every tail count with `k ≥ 2` agrees (both `0`)
yet `B ≰ A`.  So the paper's instance `k = 1` is irremovable — it *is* the
cardinality clause `r ≤ s`, relocated. -/
theorem control_L1a_restrict_two_fails :
    (∀ k, 2 ≤ k → tail ({1} : Finset ℕ) k ≤ tail (∅ : Finset ℕ) k)
      ∧ ¬ MLe ({1} : Finset ℕ) (∅ : Finset ℕ) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [tail_singleton_eq_zero (by omega), tail_empty]
  · rintro ⟨h, -⟩
    simp at h

/-- **Control L1b.**  Over `Finset ℕ` the quantifier cannot even be restricted
to `k ≥ 1`, which is where the paper puts it: `B = {0}`, `A = ∅`.  The paper is
safe only because its sets live in `[N] = {1,…,N}`, so nothing is `< 1`; the
correct Lean quantifier is `∀ k : ℕ` and the cardinality clause is `k = 0`
(pre-registration `P1`, arm 3). -/
theorem control_L1b_restrict_one_fails :
    (∀ k, 1 ≤ k → tail ({0} : Finset ℕ) k ≤ tail (∅ : Finset ℕ) k)
      ∧ ¬ MLe ({0} : Finset ℕ) (∅ : Finset ℕ) := by
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [tail_singleton_eq_zero (by omega), tail_empty]
  · rintro ⟨h, -⟩
    simp at h

/-- **Control L2.**  `cor:order`(2) is stated for `A ∋ m`; the hypothesis is
removable — at `m ∉ A` the erasure is `A` itself and the claim is reflexivity.
Here `7 ∉ {1,2}`. -/
theorem control_L2_erase_notMem :
    (7 : ℕ) ∉ ({1, 2} : Finset ℕ) ∧ MLe (({1, 2} : Finset ℕ).erase 7) ({1, 2} : Finset ℕ) :=
  ⟨by decide, MLe_erase _ _⟩

/-- **Control L3.**  T1 and T3 carry no ambient bound: the comparison is
available for sets with no declared containing range. -/
theorem control_L3_no_ambient : MLe ({1000} : Finset ℕ) ({1000, 10 ^ 9} : Finset ℕ) :=
  MLe_of_subset (by simp)

/-- **Control L4a.**  The ambient hypothesis of T4 is *not* removable: with
`B = {0} ≤ A = {5}` but `A ⊈ range 3`, the complemented comparison fails.
Contrast `control_L3_no_ambient`: the same binder is unnecessary in T1 and
structurally required in T4. -/
theorem control_L4a_ambient_needed :
    MLe ({0} : Finset ℕ) ({5} : Finset ℕ)
      ∧ ¬ MLe (Finset.range 3 \ ({5} : Finset ℕ)) (Finset.range 3 \ ({0} : Finset ℕ)) := by
  refine ⟨(MLe_iff_tail _ _).mpr fun k => ?_, by decide⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [tail_singleton_eq_zero (show (0:ℕ) < k by omega)]
    exact Nat.zero_le _

/-- **Control L4b** (pre-registration `L4`, arm 3 confirmed).  `N` is a free
*parameter* of T4, not a hypothesis with content: any two bounding ambients give
the same complemented comparison. -/
theorem control_L4b_ambient_free {A B : Finset ℕ} {N N' : ℕ}
    (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N)
    (hA' : A ⊆ Finset.range N') (hB' : B ⊆ Finset.range N') :
    MLe (Finset.range N \ A) (Finset.range N \ B)
      ↔ MLe (Finset.range N' \ A) (Finset.range N' \ B) := by
  rw [← MLe_iff_compl hA hB, ← MLe_iff_compl hA' hB']

/-- **Positive control on T1**, against the separator of `MotegiOrder.lean`:
`{3,4} ≤ {1,3,4}` because the top two of `{1,3,4}` are `3,4`.  Read through the
tail criterion: the tails of `{3,4}` are `2,2,2,2,1,0,…` and of `{1,3,4}` are
`3,3,3,3,1,0,…`. -/
theorem control_T1_pos : ∀ k, tail ({3, 4} : Finset ℕ) k ≤ tail ({1, 3, 4} : Finset ℕ) k :=
  tail_subset_le (by decide)

/-- **Negative control on T1**: `{4,5} ≰ {1,3,5}`, detected by the tail count at
`k = 4` (`{4,5}` has two elements `≥ 4`, `{1,3,5}` has one).  A tail criterion
with the inequality reversed, or with `tail` counting `≤ k`, would make this
control pass. -/
theorem control_T1_neg :
    ¬ (∀ k, tail ({4, 5} : Finset ℕ) k ≤ tail ({1, 3, 5} : Finset ℕ) k) := by
  intro h
  have := h 4
  rw [tail, tail] at this
  revert this
  decide

end Motegi
end TworowD4Kernel
