/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Order.OrderIsoNat
import Mathlib.Order.WellFoundedSet
import Mathlib.Data.List.GetD
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# The strict-partition order `⪯` and the matching criterion (Q473)

Formalisation of the two structural lemmas of
`projects/proofs/2026-10-15-Q473-GDMW-independence.tex`:

* `lem:order` (tex line 208) → `Q473.SP.instPartialOrder`, `Q473.SP.instOrderBot`,
  `Q473.SP.finite_downset`, `Q473.SP.instWellFoundedLT`
* `lem:match` (tex line 222) → `Q473.card_le_of_dominating_inj`, `Q473.exists_inj_iff`

The result these lemmas carry is the linear independence of the half-space symmetric
functions of Garbali–de Gier–Mead–Wheeler, *Symmetric functions from the six-vertex model
in half-space*, `arXiv:2312.14348` (source `Half_line_ASEP.tex`, Conjecture `conj:F-orth`,
line 443: "subsets `κ ⊂ ℕ`"); so `|κ|` throughout is the *number of parts*, i.e. the
cardinality of that subset, never the sum.

## Design notes

* A strict partition is a strictly decreasing list of positive naturals. `SP.part` pads with
  `0` past the end of the list, so the paper's `κ'_j ≤ κ_j (1 ≤ j ≤ |κ'|)` extends to all `j`.
* Mathlib has `Set.Finite.wellFoundedOn` (well-foundedness *on* a finite set) but no global
  "all principal down-sets finite ⇒ well-founded". `wellFounded_of_finite_lowerSet` below is
  that missing step, proved by the down-set cardinality as a `ℕ`-valued measure.
-/

namespace Q473

/-! ### A general order-theoretic step -/

/-- A transitive irreflexive relation all of whose principal down-sets are finite is
well-founded.  This is the one-line *"Consequently `⪯` is well-founded"* of `lem:order`;
the quantifier it hides is the induction on the down-set cardinality. -/
theorem wellFounded_of_finite_lowerSet {α : Type*} {r : α → α → Prop} [IsStrictOrder α r]
    (h : ∀ a, {b | r b a}.Finite) : WellFounded r := by
  have key : ∀ a b : α, r b a → (h b).toFinset.card < (h a).toFinset.card := by
    intro a b hba
    refine Finset.card_lt_card ?_
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨b, ?_, ?_⟩
      · simpa using hba
      · simpa using (irrefl_of r b)
    · intro c hc
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hc ⊢
      exact _root_.trans hc hba
  exact Subrelation.wf (fun {a b} hab => key b a hab) (InvImage.wf _ wellFounded_lt)

/-! ### Strict partitions -/

/-- A strict partition: a strictly decreasing list of positive naturals.  `P` of the tex. -/
structure SP where
  /-- The parts, strictly decreasing. -/
  parts : List ℕ
  chain : parts.IsChain (· > ·)
  pos : ∀ x ∈ parts, 0 < x

namespace SP

theorem ext' {κ κ' : SP} (h : κ.parts = κ'.parts) : κ = κ' := by
  cases κ; cases κ'; subst h; rfl

/-- `|κ|` of the tex: the number of parts. -/
def len (κ : SP) : ℕ := κ.parts.length

/-- `κ_j` of the tex, `0`-indexed and padded with `0` past the last part. -/
def part (κ : SP) (j : ℕ) : ℕ := κ.parts.getD j 0

theorem part_eq_zero_iff (κ : SP) (j : ℕ) : κ.part j = 0 ↔ κ.len ≤ j := by
  constructor
  · intro hj
    by_contra hlt
    have hlt' : j < κ.len := by omega
    rw [part, List.getD_eq_getElem _ _ hlt'] at hj
    have := κ.pos _ (List.getElem_mem hlt')
    omega
  · intro hj
    exact List.getD_eq_default _ _ hj

theorem part_pos_of_lt_len {κ : SP} {j : ℕ} (hj : j < κ.len) : 0 < κ.part j :=
  Nat.pos_of_ne_zero fun h => absurd ((κ.part_eq_zero_iff j).mp h) (by omega)

/-- Two strict partitions with the same padded part function are equal.  Positivity of the
parts is what makes the padding injective. -/
theorem eq_of_part_eq {κ κ' : SP} (h : ∀ j, κ.part j = κ'.part j) : κ = κ' := by
  have key : ∀ a b : SP, (∀ j, a.part j = b.part j) → a.len ≤ b.len := by
    intro a b hab
    have hb : b.part b.len = 0 := (b.part_eq_zero_iff _).mpr le_rfl
    rw [← hab] at hb
    exact (a.part_eq_zero_iff _).mp hb
  have hlen : κ.len = κ'.len :=
    le_antisymm (key _ _ h) (key _ _ fun j => (h j).symm)
  refine ext' (List.ext_getElem hlen ?_)
  intro n h1 h2
  have := h n
  rwa [part, part, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this

/-- `def:order` of the tex, verbatim: `|κ'| ≤ |κ|` and `κ'_j ≤ κ_j` for `1 ≤ j ≤ |κ'|`. -/
instance instLE : LE SP :=
  ⟨fun κ' κ => κ'.len ≤ κ.len ∧ ∀ j < κ'.len, κ'.part j ≤ κ.part j⟩

theorem le_def {κ' κ : SP} : κ' ≤ κ ↔ κ'.len ≤ κ.len ∧ ∀ j < κ'.len, κ'.part j ≤ κ.part j :=
  Iff.rfl

/-- The padded reformulation.  Note the *length* clause of `def:order` is redundant: it is
forced by positivity of the parts.  The tex states both clauses; Lean shows one implies it. -/
theorem le_iff_forall {κ' κ : SP} : κ' ≤ κ ↔ ∀ j, κ'.part j ≤ κ.part j := by
  rw [le_def]
  constructor
  · rintro ⟨-, h⟩ j
    rcases lt_or_ge j κ'.len with hj | hj
    · exact h j hj
    · simp [(κ'.part_eq_zero_iff j).mpr hj]
  · intro h
    refine ⟨?_, fun j _ => h j⟩
    by_contra hc
    have h2 := h κ.len
    rw [(κ.part_eq_zero_iff κ.len).mpr le_rfl] at h2
    have := (κ'.part_eq_zero_iff κ.len).mp (Nat.le_zero.mp h2)
    omega

instance instPartialOrder : PartialOrder SP where
  le := (· ≤ ·)
  le_refl _ := le_iff_forall.mpr fun _ => le_rfl
  le_trans _ _ _ h1 h2 :=
    le_iff_forall.mpr fun j => (le_iff_forall.mp h1 j).trans (le_iff_forall.mp h2 j)
  le_antisymm _ _ h1 h2 :=
    eq_of_part_eq fun j => le_antisymm (le_iff_forall.mp h1 j) (le_iff_forall.mp h2 j)

/-- The empty partition `∅`. -/
instance instOrderBot : OrderBot SP where
  bot := ⟨[], List.isChain_nil, by simp⟩
  bot_le _ := le_iff_forall.mpr fun _ => by simp [part]

theorem bot_parts : (⊥ : SP).parts = [] := rfl

/-- `lem:order`, finiteness clause: every principal down-set `P_{⪯κ}` is finite.

The tex argues from `κ'_1 ≤ κ_1` (so every part of `κ'` lies in `[κ_1]`) together with
`|κ'| ≤ |κ|`.  Here the same count is packaged as an injection into the finite product
`∀ i : Fin |κ|, Fin (κ_i + 1)`, which uses only the pointwise bound — it does not need
monotonicity of `κ`, i.e. it does not use the `IsChain` field. -/
theorem finite_downset (κ : SP) : {κ' : SP | κ' ≤ κ}.Finite := by
  have hinj : Function.Injective
      (fun κ' : ↥{κ' : SP | κ' ≤ κ} => fun i : Fin κ.len =>
        (⟨κ'.1.part i, Nat.lt_succ_of_le (le_iff_forall.mp κ'.2 i)⟩ : Fin (κ.part i + 1))) := by
    intro a b hab
    refine Subtype.ext (eq_of_part_eq fun j => ?_)
    rcases lt_or_ge j κ.len with hj | hj
    · have h := congrFun hab ⟨j, hj⟩
      simpa using h
    · have ha : a.1.len ≤ j := le_trans (le_def.mp a.2).1 hj
      have hb : b.1.len ≤ j := le_trans (le_def.mp b.2).1 hj
      rw [(a.1.part_eq_zero_iff j).mpr ha, (b.1.part_eq_zero_iff j).mpr hb]
  have hfin : Finite ↥{κ' : SP | κ' ≤ κ} := Finite.of_injective _ hinj
  exact Set.toFinite _

/-- `lem:order`, final clause: `⪯` is well-founded.  This is the step the whole Q473
argument turns on — it is what lets the infinite relation `eq:relation` be attacked by
`⪯`-induction. -/
instance instWellFoundedLT : WellFoundedLT SP :=
  ⟨wellFounded_of_finite_lowerSet fun κ =>
    (finite_downset κ).subset fun _ (hx : _ < κ) => hx.le⟩

/-! ### The contrast: `⪰` is not well-founded (tex `§`"The order", the reason `⪯` was chosen) -/

/-- The one-part strict partition `(m+1)`. -/
def single (m : ℕ) : SP := ⟨[m + 1], List.isChain_singleton _, by simp⟩

theorem single_lt_single (m : ℕ) : single m < single (m + 1) := by
  refine lt_of_le_of_ne (le_iff_forall.mpr fun j => ?_) ?_
  · cases j with
    | zero => simp only [part, single, List.getD_cons_zero]; omega
    | succ k => simp [part, single]
  · intro h
    have h' := congrArg SP.parts h
    simp only [single, List.cons.injEq] at h'
    omega

/-- The reverse order `⪰` is **not** well-founded: `(1) ≺ (2) ≺ (3) ≺ ⋯` is an infinite
ascending chain.  This is the half of the Q473 headline that no computation in the tex
verified, and it is the reason the triangularity had to be taken with respect to `⪯`. -/
theorem not_wellFounded_gt : ¬ WellFounded ((· > ·) : SP → SP → Prop) :=
  (RelEmbedding.natGT single fun m => single_lt_single m).not_wellFounded

end SP

/-! ### `lem:match`: the matching criterion (tex line 222)

`a` plays `κ' = (κ'_1 > … > κ'_{n'})` — only *antitonicity* is used, so the statement is
proved for weakly decreasing `a`.  `d` plays the decreasing rearrangement
`c_[1] ≥ … ≥ c_[N]`, spelled out as: `d` is antitone and `d = c ∘ σ` for a permutation `σ`.
-/

/-- A dominating injection forces `n' ≤ N`.  This is the clause of `lem:match` that the tex
leaves to the word "injection". -/
theorem card_le_of_inj {n N : ℕ} {ι : Fin n → Fin N} (hι : Function.Injective ι) : n ≤ N := by
  simpa using Fintype.card_le_of_injective ι hι

/-- Every tuple has an antitone rearrangement: `c_[1] ≥ … ≥ c_[N]` exists.  Mathlib's
`Tuple.sort` sorts *increasingly*, so this goes through the order dual. -/
theorem exists_antitone_rearrangement {N : ℕ} (c : Fin N → ℕ) :
    ∃ σ : Equiv.Perm (Fin N), Antitone (c ∘ σ) := by
  refine ⟨Tuple.sort (fun i => OrderDual.toDual (c i)), ?_⟩
  intro i j hij
  exact Tuple.monotone_sort (fun i => OrderDual.toDual (c i)) hij

/-- **`lem:match`.**  There is an injection `ι : [n'] → [N]` with `κ'_j ≤ c_{ι(j)}` for all `j`
iff `n' ≤ N` and `κ'_j ≤ c_[j]` for all `j ≤ n'`.

The `n' ≤ N` half of the right-hand side is carried by the hypothesis `h` together with
`card_le_of_inj`.  The `⟸` direction is the greedy injection `σ ∘ castLE`; the `⟹`
direction is a counting argument (see the note below) rather than the tex's
*"pointwise domination is preserved by decreasing rearrangement"*, which the tex asserts in
a clause and does not prove. -/
theorem exists_inj_iff {n N : ℕ} {a : Fin n → ℕ} {c d : Fin N → ℕ} (ha : Antitone a)
    (hd : Antitone d) (σ : Equiv.Perm (Fin N)) (hσ : ∀ m, d m = c (σ m)) (h : n ≤ N) :
    (∃ ι : Fin n → Fin N, Function.Injective ι ∧ ∀ j, a j ≤ c (ι j))
      ↔ ∀ j : Fin n, a j ≤ d (Fin.castLE h j) := by
  constructor
  · rintro ⟨ι, hinj, hdom⟩ j
    by_contra hcon
    set m₀ : Fin N := Fin.castLE h j with hm₀
    -- `S` = the positions of the rearranged list that are big enough to host `a j`.
    set S : Finset (Fin N) := Finset.univ.filter (fun m => a j ≤ d m) with hS
    have hSsub : S ⊆ Finset.Iio m₀ := by
      intro m hm
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      simp only [Finset.mem_Iio]
      by_contra hge
      have hle : d m ≤ d m₀ := hd (not_lt.mp hge)
      omega
    have hcardS : S.card ≤ (j : ℕ) := by
      have h1 : S.card ≤ (Finset.Iio m₀).card := Finset.card_le_card hSsub
      rw [Fin.card_Iio] at h1
      simpa [hm₀] using h1
    -- the `j+1` indices `j' ≤ j` all land in `S`, injectively.
    have hmaps : Set.MapsTo (fun j' => σ.symm (ι j')) (Finset.Iic j) S := by
      intro j' hj'
      simp only [Finset.coe_Iic, Set.mem_Iic] at hj'
      simp only [hS, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and,
        hσ, Equiv.apply_symm_apply]
      exact le_trans (ha hj') (hdom j')
    have hinj' : Set.InjOn (fun j' => σ.symm (ι j')) (Finset.Iic j) :=
      fun _ _ _ _ hxy => hinj (σ.symm.injective hxy)
    have hcount := Finset.card_le_card_of_injOn _ hmaps hinj'
    rw [Fin.card_Iic] at hcount
    omega
  · intro hdom
    refine ⟨fun j => σ (Fin.castLE h j), σ.injective.comp (Fin.castLE_injective h), fun j => ?_⟩
    rw [← hσ]
    exact hdom j

end Q473
