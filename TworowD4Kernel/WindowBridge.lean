/-
Copyright (c) 2026 Clio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clio
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Card
import TworowD4Kernel.WindowLemma

/-!
# The window bridge: from "each label occurs once in a window" to a bound

This module supplies the step that `proofs/2026-09-01-Q63-wedge-fock-normalisation.tex`
leaves on paper: the passage from the window lemma (`TworowD4Kernel.WindowLemma`) to the
range statement of Corollary `cor:range`,
$$0 \le a \le \ell - 1, \qquad 0 \le h \le e - 1 .$$

## The mathematics being formalised

In Uglov's indexation (`arXiv:math/9905196`; recalled in §`sec:conv` of the paper, eq.
`eq:kcd`) every bead position `k ∈ ℤ` factorises uniquely as
`k = c + n(d-1) - Nμ` with `c ∈ {1,…,n}`, `d ∈ {1,…,ℓ}`, `μ ∈ ℤ`, and `N = nℓ`. The pair
`(c,d)` is the *label* of `k`, and `d` is its *runner*. Since `k ≡ c + n(d-1) (mod N)`,
the label is exactly the residue of `k` mod `N`: this is `uglovLabel` below.

The proof of Theorem `thm:closed` counts beads lying in the open window `(p, p+N)`:

* `a` counts those whose label is `(c, d')` with `d' ≠ d` — the same `c`, a different
  runner. There are `ℓ - 1` such labels, so `a ≤ ℓ - 1`.
* `h` counts those whose label is `(c', d)` with `c' ≠ c` — the same runner, a different
  `c`. There are `n - 1 = e - 1` such labels, so `h ≤ e - 1`.

Both bounds are the same lemma, applied along the two axes of the label. The engine is
`card_le_card_of_window_labels`: a window of `N` consecutive integers carries each residue
class *at most* once, so a set of beads inside it whose residues are confined to a
distinguished collection `L` of classes has at most `L.card` elements.

## What is, and is not, covered

The window hypothesis is stated for the half-open `Finset.Ico p (p + N)`, which contains
the paper's open window `(p, p+N)`; a caller holding the stronger hypothesis applies these
results directly.

**One** thing is deliberately not formalised here, and it is the boundary of this module:

* **The identification of the counts — the `κ`-coordinate ↔ `k`-coordinate change.** The
  paper's `a` is defined as `#{d' > d : κ ∈ M_{d'}} + #{d' < d : κ + e ∈ M_{d'}}`, in the
  `κ`-coordinate. That this equals the count of beads in the `k`-coordinate window is the
  last paragraph of the proof of `thm:closed` (solving `eq:kcd` to get `μ' = μ` for
  `d' > d` and `μ' = μ - 1` for `d' < d`). Here `S` *is* the `k`-coordinate set; the change
  of coordinate is **assumed**, and closing it needs the abacus given a type. This is the
  next target and it is a multi-session piece of work.

The lower bounds `0 ≤ a`, `0 ≤ h` are trivial for a cardinality and are not stated.

### What changed on 2026-09-03

Two overclaims recorded in the previous version of this docstring are now closed.

* **Joint injectivity.** `uglovLabel` used to be proved injective only along each axis
  separately, which is all the two counting arguments use — but "the label *is* the
  residue" is the *joint* statement, and it was not proved. `uglovLabel_injective` now
  proves it, and `uglovLabel_bijective` / `existsUnique_label` give the bijection with
  `ZMod (nℓ)` that the phrase actually asserts.
* **Surjectivity — the "exactly once" half.** Only "at most once" used to be proved,
  because only that half is needed for an upper bound. `card_filter_window_labels` now
  supplies the other half, and `exists_card_eq_sub_one_of_runner_ne` /
  `exists_card_eq_sub_one_of_residue_ne` upgrade the two bounds of `cor:range` from bounds
  to **attained** bounds, with `existsUnique_window_of_label` recording §`sec:conv`'s
  "exactly once" remark in full.

  Honest limit, which has *not* moved: this is sharpness of the **Lean** statement over an
  arbitrary `Finset ℤ` meeting the hypotheses. It is **not** the paper's attainment claim,
  which is about a genuine bead configuration and so waits on the abacus above.

## Mathlib

`Finset.card_le_card_of_injOn`, `Finset.card_bij`, `ZMod.intCast_zmod_eq_zero_iff_dvd`,
`Int.eq_zero_of_abs_lt_dvd` and `ZMod.val_cast_of_lt` do all the work; searched `v4.30.0`
under `Mathlib/Data/ZMod/` and `Mathlib/Data/Finset/Card.lean` for the bridge in this form
and found nothing stating it.

For joint injectivity, `finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n)`
(`Mathlib/Logic/Equiv/Fin/Basic.lean`) was searched first and is *not* directly reusable,
for two reasons worth recording rather than rediscovering: it sends `(x, y) ↦ y + n * x`,
so matching `uglovLabel` needs the factors in the order `ℓ * n` and then a transport along
`Nat.mul_comm`; and its codomain is `Fin (nℓ)`, which is not `ZMod (nℓ)` without a
`NeZero` hypothesis that `uglovLabel_injective` does not otherwise need. Its `left_inv`
field is proved by `Nat.add_mul_mod_self_left` and `Nat.add_mul_div_left`, and
`add_mul_inj_of_lt` below simply uses those two core lemmas directly — the same
mathematics, without the packaging.

`ZMod.chineseRemainder` is **not** applicable: `n` and `ℓ` need not be coprime. This is
positional notation, not CRT, and the proof uses `c < n` essentially — see the control
attached to `add_mul_inj_of_lt`.
-/

namespace TworowD4Kernel

open Finset

section Window

variable {N : ℕ}

/-- **Window lemma, injectivity form.** Distinct integers in a window of `N` consecutive
integers have distinct residues mod `N`.

This is the "at most once" half of `TworowD4Kernel.card_window_eq_one`, and the only half
the bound needs. Note that no `NeZero N` hypothesis is required: at `N = 0` the window is
empty and the statement is vacuous. -/
theorem window_injOn (p : ℤ) :
    Set.InjOn (fun k : ℤ => (k : ZMod N)) ↑(Finset.Ico p (p + N)) := by
  intro k hk k' hk' h
  simp only [Finset.coe_Ico, Set.mem_Ico] at hk hk'
  simp only at h
  have hdvd : (N : ℤ) ∣ (k - k') := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h, sub_self]
  have habs : |k - k'| < (N : ℤ) := by
    rw [abs_lt]; omega
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

/-- **The bridge.** A finite set `S` of integers contained in a window of `N` consecutive
integers, whose residues mod `N` all lie in a distinguished collection `L` of residue
classes, has at most `L.card` elements.

This is the interface through which the abacus enters the proof of `cor:range`. The abacus
itself is not formalised: `S` stands for the set of beads in the window that carry a label
from `L`, and the hypotheses record only what the counting argument uses. -/
theorem card_le_card_of_window_labels (p : ℤ) (S : Finset ℤ) (L : Finset (ZMod N))
    (hS : S ⊆ Finset.Ico p (p + N))
    (hL : ∀ k ∈ S, (k : ZMod N) ∈ L) :
    S.card ≤ L.card :=
  Finset.card_le_card_of_injOn (fun k : ℤ => (k : ZMod N)) hL
    ((window_injOn p).mono (by exact_mod_cast hS))

/-- **Exactly once, in counting form.** The integers of a window of `N` consecutive
integers whose residue lies in a prescribed collection `L` of classes number *exactly*
`L.card` — not merely at most, as in `card_le_card_of_window_labels`.

This is the surjective half that `TworowD4Kernel.card_window_eq_one` supplies and that the
upper-bound argument did not need. It is what turns the bounds of `cor:range` from bounds
into attained bounds. -/
theorem card_filter_window_labels [NeZero N] (p : ℤ) (L : Finset (ZMod N)) :
    ((Finset.Ico p (p + N)).filter (fun k : ℤ => (k : ZMod N) ∈ L)).card = L.card := by
  classical
  refine Finset.card_bij (fun k _ => (k : ZMod N)) (fun k hk => (Finset.mem_filter.1 hk).2)
    ?_ ?_
  · intro k hk k' hk' h
    exact window_injOn p (Finset.mem_coe.2 (Finset.mem_filter.1 hk).1)
      (Finset.mem_coe.2 (Finset.mem_filter.1 hk').1) h
  · intro r hr
    obtain ⟨k, hk⟩ := Finset.card_eq_one.1 (card_window_eq_one N p r)
    have hkm : k ∈ (Finset.Ico p (p + N)).filter (fun k : ℤ => (k : ZMod N) = r) := by
      rw [hk]; exact Finset.mem_singleton_self k
    rw [Finset.mem_filter] at hkm
    exact ⟨k, Finset.mem_filter.2 ⟨hkm.1, hkm.2 ▸ hr⟩, hkm.2⟩

end Window

section Label

variable {n l : ℕ}

/-- **Uglov's label map.** The label `(c, d)` of a bead determines its residue mod
`N = n * ℓ`: from `k = c + n(d-1) - Nμ` (eq. `eq:kcd`, Uglov `arXiv:math/9905196` §3) we get
`k ≡ c + n(d-1) (mod N)`.

Indices here are `0`-based (`Fin n`, `Fin l`) where the paper's are `1`-based, so this is
the paper's residue shifted by the constant `-n`; the shift is a bijection of `ZMod N` and
affects none of the statements below, all of which are about distinctness and counting. -/
def uglovLabel (c : Fin n) (d : Fin l) : ZMod (n * l) :=
  (((c : ℕ) + n * (d : ℕ) : ℕ) : ZMod (n * l))

lemma uglovLabel_rep_lt (c : Fin n) (d : Fin l) : (c : ℕ) + n * (d : ℕ) < n * l := by
  have hc := c.isLt
  have hd := d.isLt
  calc (c : ℕ) + n * (d : ℕ) < n + n * (d : ℕ) := by omega
    _ = n * ((d : ℕ) + 1) := by ring
    _ ≤ n * l := Nat.mul_le_mul_left n hd

lemma uglovLabel_rep_inj {c c' : Fin n} {d d' : Fin l}
    (h : uglovLabel c d = uglovLabel c' d') :
    (c : ℕ) + n * (d : ℕ) = (c' : ℕ) + n * (d' : ℕ) := by
  have h1 := uglovLabel_rep_lt c d
  have h2 := uglovLabel_rep_lt c' d'
  have := congrArg ZMod.val h
  rwa [uglovLabel, uglovLabel, ZMod.val_cast_of_lt h1, ZMod.val_cast_of_lt h2] at this

/-- For a fixed first coordinate `c`, the label map is injective in the runner `d`. -/
theorem uglovLabel_injective_runner (c : Fin n) :
    Function.Injective (fun d : Fin l => uglovLabel c d) := by
  intro d d' h
  have hn : 0 < n := by have := c.isLt; omega
  have hrep := uglovLabel_rep_inj h
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hn (by omega))

/-- For a fixed runner `d`, the label map is injective in the first coordinate `c`. -/
theorem uglovLabel_injective_residue (d : Fin l) :
    Function.Injective (fun c : Fin n => uglovLabel c d) := by
  intro c c' h
  exact Fin.ext (by have := uglovLabel_rep_inj h; omega)

/-- **Positional notation is unique.** If `c, c' < n` then `c + n * d = c' + n * d'`
forces `c = c'` and `d = d'`.

This is the arithmetic core of joint injectivity below, and the place where `c < n` is
*used*: without it the conclusion is false (`0 + 2 * 1 = 2 + 2 * 0`). It is the same pair
of core lemmas — `Nat.add_mul_mod_self_left` and `Nat.add_mul_div_left` — that Mathlib's
`finProdFinEquiv.left_inv` uses (`Mathlib/Logic/Equiv/Fin/Basic.lean`); see the module
docstring for why the equivalence itself is not reusable here. -/
private lemma add_mul_inj_of_lt {n c c' d d' : ℕ} (hc : c < n) (hc' : c' < n)
    (h : c + n * d = c' + n * d') : c = c' ∧ d = d' := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  constructor
  · have := congrArg (· % n) h
    simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hc'] using this
  · have := congrArg (· / n) h
    simpa [Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt hc, Nat.div_eq_of_lt hc'] using this

/-- **Control for `add_mul_inj_of_lt`: `c < n` is load-bearing, not decorative.** Drop it
and the conclusion is false — at `n = 2`, `0 + 2 * 1 = 2 + 2 * 0` with `0 ≠ 2`. So a proof
of the lemma that never used `hc` would be proving something untrue. -/
theorem add_mul_inj_of_lt_needs_lt : (0 : ℕ) + 2 * 1 = 2 + 2 * 0 ∧ (0 : ℕ) ≠ 2 := by
  decide

/-- **Joint injectivity of the label map.** Distinct pairs `(c, d)` carry distinct labels.

This is the honest content of "the label *is* the residue": `k = c + n(d-1)` read mod
`N = nℓ` is base-`n` positional notation with `n` digits and `ℓ` places, so recovering
`(c, d)` from the residue is uniqueness of quotient-and-remainder by `n`.

Note that this is *not* an instance of `ZMod.chineseRemainder`: `n` and `ℓ` need not be
coprime (in the application `ℓ` is a multiple of nothing in particular, and `n = ℓ` is
allowed). The proof goes through `add_mul_inj_of_lt`, which uses `c < n` essentially. -/
theorem uglovLabel_injective :
    Function.Injective (fun p : Fin n × Fin l => uglovLabel p.1 p.2) := by
  rintro ⟨c, d⟩ ⟨c', d'⟩ h
  obtain ⟨h1, h2⟩ := add_mul_inj_of_lt c.isLt c'.isLt (uglovLabel_rep_inj h)
  exact Prod.ext (Fin.ext h1) (Fin.ext h2)

/-- **Non-vacuity for `uglovLabel_injective`**, with both `n ≥ 2` and `ℓ ≥ 2`: two pairs
differing in *both* coordinates get distinct labels. Axis-wise injectivity does not see
this pair. -/
theorem uglovLabel_injective_nonvacuous :
    uglovLabel (0 : Fin 2) (1 : Fin 3) ≠ uglovLabel (1 : Fin 2) (2 : Fin 3) := by decide

/-- **The control: the statement can fail.** Joint injectivity is a statement about the
modulus, not a formality. The same formula read mod `n` instead of mod `n * ℓ` is *not*
injective — the runner is invisible mod `n`. A proof of `uglovLabel_injective` that would
also typecheck for this map would be measuring nothing.

(`decide` here evaluates a `ZMod 2` equality on two explicit pairs of `Fin 2 × Fin 3`.) -/
theorem uglovLabel_not_injective_mod_n :
    ¬ Function.Injective
      (fun p : Fin 2 × Fin 3 => (((p.1 : ℕ) + 2 * (p.2 : ℕ) : ℕ) : ZMod 2)) := by
  intro hinj
  have : ((0 : Fin 2), (0 : Fin 3)) = ((0 : Fin 2), (1 : Fin 3)) := hinj (by decide)
  exact absurd this (by decide)

/-- **`cor:range`, the `a` bound.** Beads in a window of `N = n * ℓ` consecutive integers
whose label has first coordinate `c` and runner different from `d` number at most `ℓ - 1`.

This is `0 ≤ a ≤ ℓ - 1` of Corollary `cor:range`, modulo the coordinate change described in
the module docstring: `S` is the set of such beads in the `k`-coordinate, and the paper's
`a` is the same count read in the `κ`-coordinate. -/
theorem card_le_sub_one_of_runner_ne
    (c : Fin n) (d : Fin l) (p : ℤ) (S : Finset ℤ)
    (hS : S ⊆ Finset.Ico p (p + (n * l : ℕ)))
    (hlab : ∀ k ∈ S, ∃ d' : Fin l, d' ≠ d ∧ (k : ZMod (n * l)) = uglovLabel c d') :
    S.card ≤ l - 1 := by
  refine (card_le_card_of_window_labels p S
      ((Finset.univ.erase d).image (fun d' : Fin l => uglovLabel c d')) hS ?_).trans ?_
  · intro k hk
    obtain ⟨d', hd', hkd⟩ := hlab k hk
    exact Finset.mem_image.2 ⟨d', Finset.mem_erase.2 ⟨hd', Finset.mem_univ _⟩, hkd.symm⟩
  · rw [Finset.card_image_of_injective _ (uglovLabel_injective_runner c)]
    simp [Finset.card_erase_of_mem]

/-- **`cor:range`, the `h` bound.** Beads in a window of `N = n * ℓ` consecutive integers
lying on runner `d` with first coordinate different from `c` number at most `n - 1 = e - 1`.

This is `0 ≤ h ≤ e - 1` of Corollary `cor:range`. In the paper's `κ`-coordinate these are
the elements of `M_d ∩ (κ, κ + e)`. -/
theorem card_le_sub_one_of_residue_ne
    (c : Fin n) (d : Fin l) (p : ℤ) (S : Finset ℤ)
    (hS : S ⊆ Finset.Ico p (p + (n * l : ℕ)))
    (hlab : ∀ k ∈ S, ∃ c' : Fin n, c' ≠ c ∧ (k : ZMod (n * l)) = uglovLabel c' d) :
    S.card ≤ n - 1 := by
  refine (card_le_card_of_window_labels p S
      ((Finset.univ.erase c).image (fun c' : Fin n => uglovLabel c' d)) hS ?_).trans ?_
  · intro k hk
    obtain ⟨c', hc', hkd⟩ := hlab k hk
    exact Finset.mem_image.2 ⟨c', Finset.mem_erase.2 ⟨hc', Finset.mem_univ _⟩, hkd.symm⟩
  · rw [Finset.card_image_of_injective _ (uglovLabel_injective_residue d)]
    simp [Finset.card_erase_of_mem]

/-- **Non-vacuity, and sharpness of the constant.** The hypotheses of
`card_le_sub_one_of_runner_ne` are satisfiable with the bound attained, so the theorem is
not vacuously true and `ℓ - 1` is not a slack constant.

Take `n = 2`, `l = 3`, so `N = 6`; `c = 0`, `d = 0`, window `[0, 6)`. The two labels
`(0,1)` and `(0,2)` are the residues `2` and `4`, realised by the beads `2` and `4`. So
`S = {2, 4}` has `S.card = 2 = l - 1`.

The same witness is a negative control on the constant: it refutes `S.card ≤ l - 2`. -/
example :
    ∃ S : Finset ℤ, S ⊆ Finset.Ico (0 : ℤ) (0 + ((2 * 3 : ℕ) : ℤ)) ∧
      (∀ k ∈ S, ∃ d' : Fin 3, d' ≠ (0 : Fin 3) ∧
        (k : ZMod (2 * 3)) = uglovLabel (0 : Fin 2) d') ∧
      S.card = 3 - 1 := by
  refine ⟨{2, 4}, by decide, ?_, by decide⟩
  intro k hk
  fin_cases hk
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

/-! ### Exactly once: the surjective half

Everything below needs `N = n * ℓ` to be nonzero, i.e. both `n ≥ 1` and `ℓ ≥ 1`. That is
no restriction in the application (`n = e ≥ 2`, `ℓ ≥ 1`), but at `N = 0` the ambient
`ZMod 0 = ℤ` is infinite and the counting statements are false, so the hypothesis is real.
-/

section Attained

variable {n l : ℕ} [NeZero (n * l)]

/-- **The label map is a bijection onto the residues mod `N = nℓ`.** Injectivity is
`uglovLabel_injective`; surjectivity is then forced by counting, since `Fin n × Fin ℓ` and
`ZMod (nℓ)` both have `nℓ` elements.

This is the precise sense in which "the label *is* the residue" (§`sec:conv`, eq.
`eq:kcd`, Uglov `arXiv:math/9905196` §3). -/
theorem uglovLabel_bijective :
    Function.Bijective (fun p : Fin n × Fin l => uglovLabel p.1 p.2) := by
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨uglovLabel_injective, by simp [ZMod.card]⟩

/-- **Every bead has exactly one label.** The converse reading of `uglovLabel_bijective`:
given `k ∈ ℤ`, the pair `(c, d)` with `k ≡ c + n(d-1)` exists and is unique. Uniqueness is
exactly the joint injectivity of `uglovLabel`; axis-wise injectivity does not give it. -/
theorem existsUnique_label (k : ℤ) :
    ∃! q : Fin n × Fin l, (k : ZMod (n * l)) = uglovLabel q.1 q.2 := by
  obtain ⟨q, hq⟩ := uglovLabel_bijective.surjective (k : ZMod (n * l))
  exact ⟨q, hq.symm, fun q' hq' => uglovLabel_bijective.injective (hq'.symm.trans hq.symm)⟩

/-- **Each label occurs exactly once in a window.** The paper's §`sec:conv` remark, in
full: in a window of `N = nℓ` consecutive integers there is exactly one bead carrying any
prescribed label `(c, d)`. -/
theorem existsUnique_window_of_label (p : ℤ) (c : Fin n) (d : Fin l) :
    ∃! k : ℤ, k ∈ Finset.Ico p (p + (n * l : ℕ)) ∧
      (k : ZMod (n * l)) = uglovLabel c d := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.1 (card_window_eq_one (n * l) p (uglovLabel c d))
  have hmem : ∀ y : ℤ, (y ∈ Finset.Ico p (p + (n * l : ℕ)) ∧
      (y : ZMod (n * l)) = uglovLabel c d) ↔ y = k := by
    intro y
    constructor
    · intro hy
      exact Finset.mem_singleton.1 (hk ▸ Finset.mem_filter.2 hy)
    · rintro rfl
      have hkm : y ∈ ({y} : Finset ℤ) := Finset.mem_singleton_self y
      rw [← hk, Finset.mem_filter] at hkm
      exact hkm
  exact ⟨k, (hmem k).2 rfl, fun y hy => (hmem y).1 hy⟩

/-- **`cor:range`, the `a` bound, is attained.** In *any* window of `N = nℓ` consecutive
integers there is a set `S` of beads satisfying the hypotheses of
`card_le_sub_one_of_runner_ne` with `S.card = ℓ - 1` exactly. So the constant `ℓ - 1` is
the truth, not slack: `a` is not merely bounded by `ℓ - 1`, it equals it.

This is `card_le_sub_one_of_runner_ne` upgraded from a bound to an attained bound. The
honest limit is unchanged: this is sharpness of the *Lean* statement over an arbitrary
`Finset ℤ` meeting the hypotheses. It is **not** the paper's attainment claim, which is
about a genuine bead configuration and therefore needs the abacus (gap 1 of the module
docstring). -/
theorem exists_card_eq_sub_one_of_runner_ne (c : Fin n) (d : Fin l) (p : ℤ) :
    ∃ S : Finset ℤ, S ⊆ Finset.Ico p (p + (n * l : ℕ)) ∧
      (∀ k ∈ S, ∃ d' : Fin l, d' ≠ d ∧ (k : ZMod (n * l)) = uglovLabel c d') ∧
      S.card = l - 1 := by
  classical
  refine ⟨(Finset.Ico p (p + (n * l : ℕ))).filter
      (fun k : ℤ => (k : ZMod (n * l)) ∈
        (Finset.univ.erase d).image (fun d' : Fin l => uglovLabel c d')),
    Finset.filter_subset _ _, ?_, ?_⟩
  · intro k hk
    obtain ⟨d', hd', hkd⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hk).2
    exact ⟨d', (Finset.mem_erase.1 hd').1, hkd.symm⟩
  · rw [card_filter_window_labels,
      Finset.card_image_of_injective _ (uglovLabel_injective_runner c)]
    simp [Finset.card_erase_of_mem]

/-- **`cor:range`, the `h` bound, is attained.** As `exists_card_eq_sub_one_of_runner_ne`,
along the other axis: the constant `n - 1 = e - 1` is realised in every window. -/
theorem exists_card_eq_sub_one_of_residue_ne (c : Fin n) (d : Fin l) (p : ℤ) :
    ∃ S : Finset ℤ, S ⊆ Finset.Ico p (p + (n * l : ℕ)) ∧
      (∀ k ∈ S, ∃ c' : Fin n, c' ≠ c ∧ (k : ZMod (n * l)) = uglovLabel c' d) ∧
      S.card = n - 1 := by
  classical
  refine ⟨(Finset.Ico p (p + (n * l : ℕ))).filter
      (fun k : ℤ => (k : ZMod (n * l)) ∈
        (Finset.univ.erase c).image (fun c' : Fin n => uglovLabel c' d)),
    Finset.filter_subset _ _, ?_, ?_⟩
  · intro k hk
    obtain ⟨c', hc', hkd⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hk).2
    exact ⟨c', (Finset.mem_erase.1 hc').1, hkd.symm⟩
  · rw [card_filter_window_labels,
      Finset.card_image_of_injective _ (uglovLabel_injective_residue d)]
    simp [Finset.card_erase_of_mem]

end Attained

end Label

end TworowD4Kernel
