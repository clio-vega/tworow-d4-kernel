# LEAN 2026-10-17 c1 — `lem:comb` formalised sorry-free

**Target.** `lem:comb` of `proofs/2026-10-16-Q488-korepin-locus.tex`, line 521 — the
combinatorial step of `thm:main` (*jump ≤ 1 ⇒ Laurent*), the step that explains the
`max` in Q484's criterion.

**Project.** `/home/clio/projects/lean/tworow_d4_kernel`, new module
`TworowD4Kernel/MotegiOrder.lean`, imported from the root `TworowD4Kernel.lean`
(line 40). Toolchain `leanprover/lean4:v4.30.0`.

**Main declaration.**

```lean
theorem TworowD4Kernel.Motegi.lem_comb {ν lam mu : Finset ℕ}
    (hl : MLe lam ν) (hm : MLe mu ν) :
    (∃ a b : ℕ, a < b ∧ a ∈ ν ∧ b ∈ ν ∧
        MLe lam (ν \ {a, b}) ∧ MLe mu (ν \ {a, b}))
      ↔ max lam.card mu.card + 2 ≤ ν.card
```

with `lem_comb_sub` restating the right-hand side in the tex's subtracted form
`2 ≤ ν.card - max lam.card mu.card`.

## Status: 0 sorries, 0 axioms beyond the standard three

Full `lake build` of the whole project completes (3468 jobs). The module was rebuilt
after **deleting its `.olean`**, so this is an elaboration, not a trace-hash replay.

**Axiom audit, counted as records not lines.** 20 named declarations in the module;
`#print axioms` emitted **20 records**, count matched against the declaration count
extracted from the source. All 20 carry only `propext`, `Classical.choice`,
`Quot.sound` (9 of them only `propext, Quot.sound`). **Positive control**: a planted
`theorem planted_positive_control : True := by sorry` produced
`'...planted_positive_control' depends on axioms: [sorryAx]` and the
`declaration uses 'sorry'` warning — the scan fires. Control removed.

The 4 `example`s are anonymous and so are not in the 20; a `sorry` in one would have
raised a `declaration uses 'sorry'` warning, and the final build raised none.

## What was formalised

| declaration | content |
|---|---|
| `ascList`, `descList` | `M.sort (· ≤ ·)` / `M.sort (· ≥ ·)` |
| `asc`, `desc` | `c`-th smallest / `c`-th largest, 0-indexed, `0` past the end |
| `descList_eq_reverse_ascList` | the two enumerations are reverses — proved from *same multiset + oppositely sorted*, not by unfolding merge sort |
| `MLe` | **Motegi's order, in Motegi's own increasing enumeration** |
| `MLe_iff_tex` | the 1-based verbatim form `m_{s−r+j} ≥ i_j, 1 ≤ j ≤ r` |
| `desc_eq_asc`, `MLe_iff_desc` | the "top `r` elements" reading, via the decreasing enumeration |
| `ascList_cons_min` | peeling the minimum off the increasing enumeration |
| `asc_erase_two` | **the key lemma**: `asc ν (m+2) = asc (ν∖{a,b}) m` for `a,b` the two smallest |
| `MLe_erase_two` | comparisons survive deletion of the two smallest when the gap is ≥ 2 |
| `lem_comb_forward`, `lem_comb`, `lem_comb_sub` | the TFAE |

### Design choice, and why it is the safer one

The brief proposed *defining* the order by the descending rearrangement, to avoid the
`s − r + j` index shift. I did the opposite: `MLe` is defined **in Motegi's own
increasing enumeration**, so the definition can be read against arXiv:2610.15344
Thm 2.6(i) line by line, and the "top `r`" reading is a **theorem** (`MLe_iff_desc`)
proved against an independently constructed decreasing enumeration. That is a check
against a *different* characterisation than the one the definition was coded from —
the lesson of 2026-10-17 PROVE, applied at the point where it was cheapest.

Removing the two smallest elements turned out to be *easier* in the ascending
convention, not harder: it is a `cons`-strip at the **front** of the list, so the key
lemma is `(a :: b :: L).getD (m+2) 0 = L.getD m 0`, closed by `rfl`. The index shift
the brief feared never had to be fought; it was absorbed once, in `MLe_iff_desc`.

### Controls

`decide` **cannot** evaluate `Finset.sort` — merge sort is well-founded recursion and
does not reduce in the kernel (`decide` got stuck at `(asc {1,4} 0).ble …`). The
enumerations of literals are therefore supplied by `ascList_toFinset`, derived from
Mathlib's `List.toFinset_sort`. Four `example`s:

- `MLe {1,4} {1,3,5}` ✓ (top two of `{1,3,5}` are `3,5`)
- `¬ MLe {4,5} {1,3,5}` ✓ (second-largest `3 < 4`)
- **separator** `MLe {3,4} {1,3,4}` ✓ — holds under the top-two reading, fails under a
  bottom-two reading (`3 ≤ 1`). This is the control that would fire if the index shift
  in `MLe` were dropped.
- `¬ MLe {1,2,3} {5,6}` ✓ (cardinality clause alone)

### Lesions

Five hypothesis lesions were run (delete, rebuild from a deleted `.olean`):
`ascList_cons_min.hmin`, `asc_erase_two.hamin`, `asc_erase_two.hbmin`,
`MLe_erase_two.hamin`, `MLe_erase_two.hbmin`. **All five broke the build.**

⚠ **Honest grading of that evidence.** What the five lesions show is that each
hypothesis is *referenced by the proof script*, which is weaker than *needed by the
theorem* — every one failed with `Unknown identifier`. That is the instrument-lies
pattern from 2026-10-15 (`SP.chain` scanned as unused while being spent) running the
other way, and I am recording it as such rather than claiming more.

One lesion **did** survive and became a theorem: **(a) ⇒ (b) needs neither `ν ≥ λ`
nor `ν ≥ μ`.** The tex states the implication under both order hypotheses; the proof
only reads the cardinality clause of the conclusion's comparisons. That is
`lem_comb_forward`, now stated hypothesis-free, with `lem_comb` calling it.

`hl` is genuinely necessary for the converse — take `ν = {1,2,3,4}`, `λ = {9}`,
`μ = ∅`: (b) holds (`1 + 2 ≤ 4`) and (a) fails, since no subset of `ν` dominates `9`.
**Not formalised** (it needs `MLe I M → max I ≤ max M`, ~20 min I did not have);
flagged here so it is not mistaken for a verified claim.

## Gaps found in the paper proof

None. The tex sentence the brief flagged as most likely to hide a quantifier —
*"Motegi's order compares only the top `|λ|` elements"* — is exactly right, and
survives formalisation as `MLe_iff_desc` + `asc_erase_two`. The one imprecision is
cosmetic: the tex writes `|ν| − max(|λ|,|μ|) ≥ 2` with a subtraction that is
truncated over `ℕ`; the Lean statement uses `max + 2 ≤ |ν|`, and `lem_comb_sub`
proves the two agree *using* `hl`/`hm` (which supply `max |λ| |μ| ≤ |ν|`).

## `#print axioms` (main declarations)

```
'TworowD4Kernel.Motegi.lem_comb'          depends on axioms: [propext, Classical.choice, Quot.sound]
'TworowD4Kernel.Motegi.lem_comb_sub'      depends on axioms: [propext, Classical.choice, Quot.sound]
'TworowD4Kernel.Motegi.lem_comb_forward'  depends on axioms: [propext, Classical.choice, Quot.sound]
'TworowD4Kernel.Motegi.MLe_iff_desc'      depends on axioms: [propext, Classical.choice, Quot.sound]
'TworowD4Kernel.Motegi.MLe_iff_tex'       depends on axioms: [propext, Quot.sound]
'TworowD4Kernel.Motegi.asc_erase_two'     depends on axioms: [propext, Classical.choice, Quot.sound]
'TworowD4Kernel.Motegi.MLe_erase_two'     depends on axioms: [propext, Classical.choice, Quot.sound]
'TworowD4Kernel.Motegi.desc_eq_asc'       depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Scope held

`thm:main` itself was **not** attempted, per the brief. No new mathematics: every step
in the Lean file corresponds to a sentence of the tex proof.
