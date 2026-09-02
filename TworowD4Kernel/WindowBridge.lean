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

Three things are deliberately *not* formalised here, and remain on paper. They are the
gap between these theorems and `cor:range` as the paper states it.

1. **The identification of the counts.** The paper's `a` is defined as
   `#{d' > d : κ ∈ M_{d'}} + #{d' < d : κ + e ∈ M_{d'}}`, in the `κ`-coordinate. That this
   equals the count `a'` of beads in the `k`-coordinate window is the last paragraph of the
   proof of `thm:closed` (solving `eq:kcd` to get `μ' = μ` for `d' > d` and `μ' = μ - 1`
   for `d' < d`). Here `S` *is* the `k`-coordinate set; the change of coordinate is assumed.
2. **Surjectivity — the "exactly once" half.** The paper's §`sec:conv` remark says each
   label other than `k`'s own occurs in the window *exactly* once. Only "at most once" is
   proved here, because only that half is needed for an upper bound. The existence half is
   what would make the bounds *attained*, and is not established below.
3. **The lower bounds `0 ≤ a`, `0 ≤ h`** are trivial for a cardinality and are not stated.

Correspondingly, `uglovLabel` is proved injective only along each axis separately
(`uglovLabel_injective_runner`, `uglovLabel_injective_residue`), not jointly: the two
counts each vary one coordinate with the other fixed, so separate injectivity is exactly
what the mathematics uses.

## Mathlib

`Finset.card_le_card_of_injOn`, `ZMod.intCast_zmod_eq_zero_iff_dvd`,
`Int.eq_zero_of_abs_lt_dvd` and `ZMod.val_cast_of_lt` do all the work; searched `v4.30.0`
under `Mathlib/Data/ZMod/` and `Mathlib/Data/Finset/Card.lean` for the bridge in this form
and found nothing stating it.
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

end Label

end TworowD4Kernel
