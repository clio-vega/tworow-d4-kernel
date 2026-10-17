/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Motegi's order on finite subsets, and the combinatorial step of `thm:main`

Formalisation of `lem:comb` of `projects/proofs/2026-10-16-Q488-korepin-locus.tex`
(line 521), the combinatorial heart of `thm:main` (*jump `≤ 1` ⇒ Laurent*).

## Motegi's order

Tex `lem:tri` (line 234), quoting Motegi, *F-function properties*, Theorem 2.6(i)
(arXiv:2610.15344, L625--L636; restated as `eq:typeC-shifted-dominance`,
L3250--L3258).  For finite `M, I ⊆ ℕ` written **increasingly** as
`m₁ < ⋯ < m_s` and `i₁ < ⋯ < i_r`,

    M ≥ I  ⟺  s ≥ r  and  m_{s−r+j} ≥ i_j  for 1 ≤ j ≤ r,

i.e. *the top `r` elements of `M` dominate `I` elementwise*.  `|·|` is
**cardinality** (Motegi's own convention, L2790).

`Motegi.MLe I M` below is this relation, written `I ≤ M`, and defined **in
Motegi's own increasing enumeration** so that the definition can be compared
with the source line by line.  The "top `r` elements" reading is then a
*theorem*, `MLe_iff_desc`, proved against the independently-defined decreasing
enumeration — a different characterisation than the one the definition was
coded from.

## Main results

* `MLe_iff_desc` — the increasing definition agrees with the "first `r` entries
  of the decreasing rearrangement" form.
* `lem_comb` — the TFAE of `lem:comb`.
-/

namespace TworowD4Kernel
namespace Motegi

open Finset List

/-! ### Enumerations -/

/-- The elements of `M` listed in **increasing** order: Motegi's `m₁ < ⋯ < m_s`. -/
def ascList (M : Finset ℕ) : List ℕ := M.sort (· ≤ ·)

/-- The elements of `M` listed in **decreasing** order. -/
def descList (M : Finset ℕ) : List ℕ := M.sort (· ≥ ·)

/-- `asc M c` is the `(c+1)`-st smallest element of `M` (`0`-indexed), and `0`
past the end. -/
def asc (M : Finset ℕ) (c : ℕ) : ℕ := (ascList M).getD c 0

/-- `desc M c` is the `(c+1)`-st largest element of `M` (`0`-indexed), and `0`
past the end. -/
def desc (M : Finset ℕ) (c : ℕ) : ℕ := (descList M).getD c 0

@[simp] lemma length_ascList (M : Finset ℕ) : (ascList M).length = M.card :=
  Finset.length_sort _

@[simp] lemma length_descList (M : Finset ℕ) : (descList M).length = M.card :=
  Finset.length_sort _

@[simp] lemma mem_ascList {M : Finset ℕ} {x : ℕ} : x ∈ ascList M ↔ x ∈ M :=
  Finset.mem_sort _

@[simp] lemma mem_descList {M : Finset ℕ} {x : ℕ} : x ∈ descList M ↔ x ∈ M :=
  Finset.mem_sort _

lemma ascList_pairwise (M : Finset ℕ) : (ascList M).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort _ _

lemma descList_pairwise (M : Finset ℕ) : (descList M).Pairwise (· ≥ ·) :=
  Finset.pairwise_sort _ _

/-- The two enumerations are reverses of each other.  Proved from the
*characterising* properties (same multiset, oppositely sorted), not by
unfolding the sorting algorithm. -/
lemma descList_eq_reverse_ascList (M : Finset ℕ) :
    descList M = (ascList M).reverse := by
  have hm : (↑(descList M) : Multiset ℕ) = ↑(ascList M) := by
    change (↑(M.sort (· ≥ ·)) : Multiset ℕ) = ↑(M.sort (· ≤ ·))
    rw [Finset.sort_eq, Finset.sort_eq]
  have hp : descList M ~ (ascList M).reverse :=
    (Multiset.coe_eq_coe.mp hm).trans (List.reverse_perm _).symm
  refine Perm.eq_of_pairwise' (r := (· ≥ ·)) (descList_pairwise M) ?_ hp
  rw [List.pairwise_reverse]
  exact (ascList_pairwise M).imp (fun h => h)

/-! ### The order -/

/-- **Motegi's order**, `I ≤ M`, in Motegi's own increasing enumeration
(tex `lem:tri`; arXiv:2610.15344 Thm 2.6(i)).  Written `0`-indexed: Motegi's
`m_{s−r+j} ≥ i_j` for `1 ≤ j ≤ r` is, with `c = j − 1`,
`asc M (M.card − I.card + c) ≥ asc I c` for `c < I.card`. -/
def MLe (I M : Finset ℕ) : Prop :=
  I.card ≤ M.card ∧ ∀ c < I.card, asc I c ≤ asc M (M.card - I.card + c)

/-- Motegi's statement verbatim, in `1`-based indexing: `M ≥ I` iff `s ≥ r` and
`m_{s−r+j} ≥ i_j` for `1 ≤ j ≤ r`.  This is the index-shift check demanded by
the brief: a wrong shift in `MLe` would make this fail. -/
theorem MLe_iff_tex (I M : Finset ℕ) :
    MLe I M ↔ I.card ≤ M.card ∧
      ∀ j, 1 ≤ j → j ≤ I.card →
        asc I (j - 1) ≤ asc M (M.card - I.card + j - 1) := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun j hj1 hjr => ?_⟩
    have := h (j - 1) (by omega)
    have he : M.card - I.card + (j - 1) = M.card - I.card + j - 1 := by omega
    rwa [he] at this
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun c hc' => ?_⟩
    have := h (c + 1) (by omega) (by omega)
    simpa using this

/-- Within range, the `c`-th largest is the `(card − 1 − c)`-th smallest. -/
lemma desc_eq_asc {M : Finset ℕ} {c : ℕ} (hc : c < M.card) :
    desc M c = asc M (M.card - 1 - c) := by
  have h1 : c < (ascList M).reverse.length := by simp; omega
  have h2 : M.card - 1 - c < (ascList M).length := by simp; omega
  unfold desc asc
  rw [descList_eq_reverse_ascList, List.getD_eq_getElem _ 0 h1,
    List.getD_eq_getElem _ 0 h2, List.getElem_reverse h1]
  congr 1
  simp

/-- The "top `r` elements" reading of Motegi's order: `I ≤ M` iff `I` is no
bigger than `M` and the **first `|I|` entries of the decreasing** enumerations
compare entrywise.  This is a different characterisation from the increasing
one `MLe` is defined by, so it is a genuine check on the index shift
`s − r + j ↔ j`-th largest, not a restatement of it. -/
theorem MLe_iff_desc (I M : Finset ℕ) :
    MLe I M ↔ I.card ≤ M.card ∧ ∀ c < I.card, desc I c ≤ desc M c := by
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun c hcI => ?_⟩
    have hd := h (I.card - 1 - c) (by omega)
    rw [desc_eq_asc hcI, desc_eq_asc (show c < M.card by omega)]
    have e1 : I.card - 1 - c = I.card - 1 - c := rfl
    have e2 : M.card - I.card + (I.card - 1 - c) = M.card - 1 - c := by omega
    rwa [e2] at hd
  · rintro ⟨hc, h⟩
    refine ⟨hc, fun c hcI => ?_⟩
    have hd := h (I.card - 1 - c) (by omega)
    rw [desc_eq_asc (show I.card - 1 - c < I.card by omega),
      desc_eq_asc (show I.card - 1 - c < M.card by omega)] at hd
    have e1 : I.card - 1 - (I.card - 1 - c) = c := by omega
    have e2 : M.card - 1 - (I.card - 1 - c) = M.card - I.card + c := by omega
    rwa [e1, e2] at hd

/-! ### The key lemma: stripping the two smallest elements -/

/-- Peeling the minimum off the increasing enumeration. -/
lemma ascList_cons_min {ν : Finset ℕ} {a : ℕ} (ha : a ∈ ν) (hmin : ∀ x ∈ ν, a ≤ x) :
    ascList ν = a :: ascList (ν.erase a) := by
  conv_lhs => rw [← Finset.insert_erase ha]
  exact Finset.sort_insert (r := (· ≤ ·))
    (fun b hb => hmin b (Finset.mem_of_mem_erase hb)) (Finset.notMem_erase a ν)

/-- **Key lemma** (tex `lem:comb`, the sentence "the top `|λ|` elements of `ν'`
are the top `|λ|` elements of `ν`").  If `a` is the smallest and `b` the
second smallest element of `ν`, then the increasing enumeration of
`ν ∖ {a,b}` is the increasing enumeration of `ν` with its first two entries
stripped — so entry `m + 2` of `ν` is entry `m` of `ν ∖ {a,b}`. -/
lemma asc_erase_two {ν : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ν) (hamin : ∀ x ∈ ν, a ≤ x)
    (hb : b ∈ ν.erase a) (hbmin : ∀ x ∈ ν.erase a, b ≤ x) (m : ℕ) :
    asc ν (m + 2) = asc ((ν.erase a).erase b) m := by
  have hlist : ascList ν = a :: b :: ascList ((ν.erase a).erase b) := by
    rw [ascList_cons_min ha hamin, ascList_cons_min hb hbmin]
  unfold asc
  rw [hlist]
  rfl

/-- Motegi-order comparisons survive deletion of the two smallest elements of
the larger set, provided the cardinality gap is at least `2`. -/
lemma MLe_erase_two {ν lam : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ν) (hamin : ∀ x ∈ ν, a ≤ x)
    (hb : b ∈ ν.erase a) (hbmin : ∀ x ∈ ν.erase a, b ≤ x)
    (h : MLe lam ν) (hcard : lam.card + 2 ≤ ν.card) :
    MLe lam ((ν.erase a).erase b) := by
  have hcard' : ((ν.erase a).erase b).card = ν.card - 2 := by
    rw [Finset.card_erase_of_mem hb, Finset.card_erase_of_mem ha]
    omega
  refine ⟨by omega, fun c hc => ?_⟩
  have hstep := h.2 c hc
  have hidx : ν.card - lam.card + c
      = (((ν.erase a).erase b).card - lam.card + c) + 2 := by omega
  rw [hidx, asc_erase_two ha hamin hb hbmin] at hstep
  exact hstep

/-! ### `lem:comb` -/

/-- **(a) ⇒ (b) of `lem:comb` needs neither `ν ≥ λ` nor `ν ≥ μ`.**  A surviving
lesion: the tex states the implication under both order hypotheses, but the
proof ("`ν∖{a,b} ≥ λ` forces `|ν| − 2 ≥ |λ|`") only reads the cardinality
clause of the *conclusion's* comparisons. -/
theorem lem_comb_forward {ν lam mu : Finset ℕ}
    (h : ∃ a b : ℕ, a < b ∧ a ∈ ν ∧ b ∈ ν ∧
      MLe lam (ν \ {a, b}) ∧ MLe mu (ν \ {a, b})) :
    max lam.card mu.card + 2 ≤ ν.card := by
  obtain ⟨a, b, hab, haν, hbν, hla, hma⟩ := h
  have hsub : ({a, b} : Finset ℕ) ⊆ ν := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hpair : ({a, b} : Finset ℕ).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton]
  have hc : (ν \ {a, b}).card = ν.card - 2 := by
    rw [Finset.card_sdiff_of_subset hsub, hpair]
  have h2 : 2 ≤ ν.card := by
    have := Finset.card_le_card hsub; omega
  have := hla.1
  have := hma.1
  omega

/-- **`lem:comb`** (tex line 521).  Let `ν ≥ λ` and `ν ≥ μ` in Motegi's order.
Then there is a pair `a < b` in `ν` with `ν ∖ {a,b} ≥ λ` and `ν ∖ {a,b} ≥ μ`
if and only if `|ν| − max(|λ|,|μ|) ≥ 2`.

The cardinality clause is stated as `max … + 2 ≤ ν.card` to avoid truncated
`ℕ`-subtraction; `lem_comb_sub` restates it in the tex's subtracted form. -/
theorem lem_comb {ν lam mu : Finset ℕ} (hl : MLe lam ν) (hm : MLe mu ν) :
    (∃ a b : ℕ, a < b ∧ a ∈ ν ∧ b ∈ ν ∧
        MLe lam (ν \ {a, b}) ∧ MLe mu (ν \ {a, b}))
      ↔ max lam.card mu.card + 2 ≤ ν.card := by
  constructor
  · exact lem_comb_forward
  · intro hbig
    -- the two smallest elements of `ν`
    have hne : ν.Nonempty := Finset.card_pos.mp (by omega)
    set a := ν.min' hne with hadef
    have ha : a ∈ ν := ν.min'_mem hne
    have hamin : ∀ x ∈ ν, a ≤ x := fun x hx => ν.min'_le x hx
    have hne2 : (ν.erase a).Nonempty := by
      apply Finset.card_pos.mp
      rw [Finset.card_erase_of_mem ha]; omega
    set b := (ν.erase a).min' hne2 with hbdef
    have hb : b ∈ ν.erase a := (ν.erase a).min'_mem hne2
    have hbmin : ∀ x ∈ ν.erase a, b ≤ x := fun x hx => (ν.erase a).min'_le x hx
    have hbν : b ∈ ν := Finset.mem_of_mem_erase hb
    have hab : a < b := lt_of_le_of_ne (hamin b hbν) (Ne.symm (Finset.ne_of_mem_erase hb))
    have hset : ν \ ({a, b} : Finset ℕ) = (ν.erase a).erase b := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert,
        Finset.mem_singleton, not_or]
      tauto
    refine ⟨a, b, hab, ha, hbν, ?_, ?_⟩
    · rw [hset]
      exact MLe_erase_two ha hamin hb hbmin hl (by omega)
    · rw [hset]
      exact MLe_erase_two ha hamin hb hbmin hm (by omega)

/-- `lem:comb` in the tex's subtracted form `|ν| − max(|λ|,|μ|) ≥ 2`.  (The two
forms agree because `max |λ| |μ| ≤ |ν|` follows from `ν ≥ λ`.) -/
theorem lem_comb_sub {ν lam mu : Finset ℕ} (hl : MLe lam ν) (hm : MLe mu ν) :
    (∃ a b : ℕ, a < b ∧ a ∈ ν ∧ b ∈ ν ∧
        MLe lam (ν \ {a, b}) ∧ MLe mu (ν \ {a, b}))
      ↔ 2 ≤ ν.card - max lam.card mu.card := by
  rw [lem_comb hl hm]
  have := hl.1
  have := hm.1
  omega

instance decidableMLe (I M : Finset ℕ) : Decidable (MLe I M) :=
  inferInstanceAs (Decidable (I.card ≤ M.card ∧
    ∀ c < I.card, asc I c ≤ asc M (M.card - I.card + c)))

/-! ### Controls

Finite checks of the *definition* against hand computation, including negative
controls.  `decide` alone cannot evaluate `Finset.sort` (merge sort is
well-founded recursion and does not reduce in the kernel), so the enumeration
of each literal is supplied by `ascList_toFinset`, which is itself derived from
Mathlib's characterisation of `Finset.sort`. -/

/-- The increasing enumeration of a nodup, increasingly-sorted list's `toFinset`
is that list. -/
lemma ascList_toFinset {l : List ℕ} (hn : l.Nodup) (hp : l.Pairwise (· ≤ ·)) :
    ascList l.toFinset = l :=
  (List.toFinset_sort (r := (· ≤ ·)) hn).mpr hp

lemma card_toFinset {l : List ℕ} (hn : l.Nodup) (hp : l.Pairwise (· ≤ ·)) :
    l.toFinset.card = l.length := by
  rw [← length_ascList, ascList_toFinset hn hp]

/-- `{1,4} ≤ {1,3,5}`: the top two of `{1,3,5}` are `3,5`, and `3 ≥ 1`, `5 ≥ 4`. -/
example : MLe [1, 4].toFinset [1, 3, 5].toFinset := by
  constructor
  · rw [card_toFinset (by decide) (by decide), card_toFinset (by decide) (by decide)]
    decide
  · rw [card_toFinset (by decide) (by decide), card_toFinset (by decide) (by decide)]
    simp only [asc, ascList_toFinset (l := [1, 4]) (by decide) (by decide),
      ascList_toFinset (l := [1, 3, 5]) (by decide) (by decide)]
    decide

/-- Negative control: `{4,5} ≰ {1,3,5}`, because the second-largest `3 < 4`.
This is the control that distinguishes the "top `r`" reading from the
"bottom `r`" reading: under the bottom-two reading `1 ≥ 4` fails too, so see
the next control for the genuine separator. -/
example : ¬ MLe [4, 5].toFinset [1, 3, 5].toFinset := by
  rintro ⟨-, h⟩
  have := h 0 (by rw [card_toFinset (by decide) (by decide)]; decide)
  rw [card_toFinset (by decide) (by decide), card_toFinset (by decide) (by decide)] at this
  simp only [asc, ascList_toFinset (l := [4, 5]) (by decide) (by decide),
    ascList_toFinset (l := [1, 3, 5]) (by decide) (by decide)] at this
  exact absurd this (by decide)

/-- **Separator** between the "top `r`" and "bottom `r`" readings: `{3,4}` is
below `{1,3,4}` because the top two of `{1,3,4}` are `3,4`; the bottom-two
reading would demand `3 ≤ 1` and fail.  A definition with the index shift
dropped would make this `False`. -/
example : MLe [3, 4].toFinset [1, 3, 4].toFinset := by
  constructor
  · rw [card_toFinset (by decide) (by decide), card_toFinset (by decide) (by decide)]
    decide
  · rw [card_toFinset (by decide) (by decide), card_toFinset (by decide) (by decide)]
    simp only [asc, ascList_toFinset (l := [3, 4]) (by decide) (by decide),
      ascList_toFinset (l := [1, 3, 4]) (by decide) (by decide)]
    decide

/-- Negative control on the cardinality clause alone. -/
example : ¬ MLe {1, 2, 3} {5, 6} := by decide

end Motegi
end TworowD4Kernel
