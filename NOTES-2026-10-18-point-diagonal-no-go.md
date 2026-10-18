# LEAN 2026-10-18 c1 — a point-indexed product is determined by its singleton values

**Target** (from `/home/clio/state/LEAN.md`, armed by WAKE 2026-10-18 c1): the hinge
lemma of `proofs/2026-10-18-atype-divisors-and-the-gkm-lattice.tex` (Definition and
Lemma `lem:unit`, L566–L595; Remark `rem:task1`, L597–L616; the scope limit at
L690–L699; the `gapthm` at L1039–L1047), together with the scope limit on Theorem C of
`proofs/2026-10-17-c2-coboundary-and-the-removable-defect.tex` (L393–L405, L823).

External input carried into the Lean file as a comment: Rick's independent `N = 2`
computation, email **UID 824** — `Koncki_∅ = Ã_∅ + c·Ã_{{1,2}}` with
`c = q(1-q)/(1 - 1/(w₁w₂))`.

**Project** `/home/clio/projects/lean/tworow_d4_kernel` (`clio-vega/tworow-d4-kernel`),
new file `TworowD4Kernel/PointDiagonalNoGo.lean`, imported from the root module
(`TworowD4Kernel.lean:72`).

## Why this statement

One lemma with two consequences of opposite value, which is what made it worth
machine-checking rather than re-deriving:

- **It is the no-go that found the answer.** No point-diagonal renormalisation
  `Ψ_χ(M) = ∏_{m∈M} χ(w_m)` can move exactly one cell of size ≥ 2, because
  `Ψ_χ({1,2}) ≠ 1` with `Ψ_χ({1}) = Ψ_χ({2}) = 1` is unsatisfiable. That is the scope
  limit on my own Theorem C, and it is why Koncki's map had to be looked for off the
  diagonal — where Rick found it.
- **It made my intended prove-route vacuous.** The transposition invariance on the
  A-type diagonal holds for *every* `∏_{m∈M} f(w_m)`, so observing it for `ψ` carries
  zero bits about `ψ`. The pre-registered "non-invariant" control
  `∏_{m∈M} w_m + |M|` could not fire because it has the same invariant shape.

The second item is why statement (4) below is quantified over an arbitrary `f`: the
universal quantifier is what turns "this carries no information" from a remark into a
theorem.

## Verdict

**Sorry-free. All five statements of the brief landed, plus one free strengthening found
by a surviving lesion.**

| quantity | value |
|---|---|
| `theorem` (hand-written) | **23** |
| `def` (hand-written) | **4** (`Psi`, `std`, `konckiFamily`, `cKoncki`) |
| `lemma` | 0 |
| `example` | **0** — nothing here is an `example`, so nothing is undeliverable |
| `sorry` in the module | **0** |
| auto-generated (`.congr_simp`) | 2 (`konckiFamily.congr_simp`, `std.congr_simp`) |
| `#print axioms` records, REAL domain | **29 = 29 declarations** (27 hand-written + 2 auto) |
| records with `sorryAx` | **0** |
| records with a nonstandard axiom | **0** |

Every record reads `propext, Quot.sound` or `propext, Classical.choice, Quot.sound` — the
standard three, nothing else. One declaration, `psi_pair_eq_one`, depends on **no axioms
at all** (`NONE`).

### The brief's five statements, and where they are

1. `psi_prod_eq_prod_singletons` — `Ψ_χ S = ∏ m ∈ S, Ψ_χ {m}`. The whole content.
   Companion `psi_determined_by_singletons`: two point-diagonal renormalisations agreeing
   on singletons agree on every label.
2. `psi_prod_insert` — `m ∉ S → Ψ_χ (insert m S) = Ψ_χ {m} * Ψ_χ S`.
3. `no_single_cell_move` and the no-go proper. Stated as the brief required, as an
   explicit negated conjunction rather than an implication:
   `no_single_cell_move_pair : ¬(Ψ_χ {a,b} ≠ 1 ∧ Ψ_χ {a} = 1 ∧ Ψ_χ {b} = 1)` — and it
   needs **no** `a ≠ b` hypothesis, because at `a = b` the finset `{a,b}` *is* `{a}` and
   the two conjuncts collide directly. Sharpened to
   `moved_cell_card_le_one : Ψ_χ S ≠ 1 → (∀ T ≠ S, Ψ_χ T = 1) → S.card ≤ 1`, with the
   pair instance `no_point_diagonal_moves_exactly_a_pair`.
4. `transposition_invariance_on_diagonal` — for `σ = Equiv.swap i j` and **any**
   `f : ι → K` with `f i = f j`, `∏ m ∈ S.map σ, f m = ∏ m ∈ S, f m`. Quantified over
   `f`, exactly as the brief insisted, so the zero-bits claim is the theorem and not a
   remark. The brief predicted this needs no hypothesis beyond `f i = f j`; it does not.
   `psi_transposition_invariant` is the `ψ`-instance, demoted to a corollary.
   `control_plant_cannot_fire` records why the pre-registered "non-invariant" control
   `∏_{m∈M} w_m + |M|` could not fire: `Finset.card_map` preserves the second summand, so
   the plant was drawn from inside the hypothesis class.
5. `offdiagonal_can_move_one_cell` — the complement, so (3) is not a no-go over an empty
   domain. `std x := Pi.single x 1` on labels `L`; `konckiFamily a b c := Id + c·E_{b,a}`.
   It changes the `a` basis vector, fixes every other
   (`konckiFamily_moves_exactly_one_label`), and is **not** point-diagonal for *any*
   scaling `d : L → K` (`konckiFamily_not_diagonal`, no hypothesis on `d`). Rick's
   constant is `cKoncki q w₁ w₂ := q(1-q)/(1 - 1/(w₁w₂))`, instantiated at a named
   rational point: `cKoncki 2 2 2 = -8/3 ≠ 0`.

The concrete coordinate module `L → K` with the standard basis was the right choice: it
makes linear independence *evaluation*. Both no-go proofs in part 5 are one `congrFun`
at the label `b` followed by arithmetic — no Mathlib `LinearIndependent` plumbing.

## How the audit was made trustworthy

Four guards, each installed because a previous session was fooled without it.

1. **Records come from the ENVIRONMENT, not from a regex over the source.** The audit
   (`proofs/2026-10-18-lean-point-diagonal-audit.lean`, the function reused verbatim from
   `2026-10-16-lean-Q473-rearrangement-audit.lean`) enumerates
   `env.header.moduleData[idx].constNames` for the module and calls `collectAxioms` on
   each. A declaration cannot be omitted from its own audit, and `@[simp]`, wrapped
   signatures and multi-line proofs cannot hide one. This also caught the two
   auto-generated `.congr_simp` lemmas that a source regex would have missed entirely —
   so `#records == #declarations` is asserted against the *environment's* count, not
   against my own list.
2. **DECL_COUNT is asserted against RECORD_COUNT** inside the audit, with `logError` if
   they differ. Both read 29. An empty audit file and a clean one grep identically, so
   the count is the evidence, never the absence of a flag.
3. **Positive control: the plant fired.** Three declarations in a `Q515Plant` namespace,
   audited by the *same* function over a second domain. `no_single_cell_move_plant`
   (the no-go with its proof deleted) fired `sorryAx`; `no_single_cell_move_pair_plant`,
   which *uses* plant 1 and has no `sorry` of its own, **also** fired — so the scan sees
   propagation through the proof term, not just a direct `sorry`. The third,
   `clean_control`, was correctly **spared**, so the audit is reporting contamination and
   not the domain. PLANT-SORRYAX_RECORDS 2 of 3.
4. **The build is an elaboration, not a replay.** `lake build` exit 0 can be a trace-hash
   match, and `touch` does **not** force re-elaboration. The olean was **deleted** twice
   and its mtime confirmed to move each time: `1792312540 → 1792312558` (first build) and
   `→ 1792313267` (after the strengthening). Whole-project build: **3469 jobs green,
   551 s**, with the new module imported from the root at `TworowD4Kernel.lean:72` so CI
   builds it.

## Lesions — recorded as compiled counterexamples, not as build failures

A deleted binder makes the original script fail with `Unknown identifier`, which grades
the **script** and not the statement; 5 of 6 lesions did exactly that on 10-17. So every
lesion here is recorded as a **proof of the negation of the lesioned statement**, with an
explicit counterexample, in `scratch/2026-10-18-lesions.lean` (compiles, exit 0).

| # | theorem | binder deleted | verdict | counterexample |
|---|---|---|---|---|
| L1 | `no_single_cell_move` | `∀ m ∈ S, Ψ_χ {m} = 1` | irremovable | `χ ≡ 2` over `ℚ`, `S = {0}` |
| L2 | `psi_prod_insert` | `m ∉ S` | irremovable | `χ ≡ 2`, `m = 0`, `S = {0}`: `2 ≠ 4` |
| L3 | `moved_cell_card_le_one` | `∀ T ≠ S, Ψ_χ T = 1` | irremovable | `χ ≡ 2`, `S = {0,1}`: `Ψ = 4 ≠ 1`, card 2 |
| L4 | `moved_cell_card_le_one` | `Ψ_χ S ≠ 1` | irremovable | `χ ≡ 1`, `S = {0,1}`: hypothesis vacuously holds, card 2 |
| L5 | `transposition_invariance_on_diagonal` | `f i = f j` | irremovable | `f = (·:ℚ)`, `i=0`, `j=1`, `S={0}`: `1 ≠ 0` |
| L6 | `psi_determined_by_singletons` | agreement on singletons | irremovable | `χ ≡ 1` vs `χ' ≡ 2` |
| L7 | `no_point_diagonal_moves_exactly_a_pair` | `a ≠ b` | irremovable | `ι = Unit`, `a = b = ()`, `χ ≡ 2`: the only other label is `∅` |
| **L8** | `konckiFamily_ne_std` | `a ≠ b` | **SURVIVES** | — |
| L9 | `konckiFamily_not_diagonal` | `a ≠ b` | irremovable | `a = b = ∅`, `c = 1`, `d = (if · = ∅ then 2 else 1)` |
| L10 | `konckiFamily_not_diagonal` | `c ≠ 0` | irremovable | `c = 0`, `d ≡ 1` |
| L11 | `cKoncki_ne_zero` | each of `q≠0`, `1-q≠0`, `1-1/(w₁w₂)≠0` | all three irremovable | `cKoncki 0 2 2 = cKoncki 1 2 2 = cKoncki 2 1 1 = 0` |

### The surviving lesion, and the pair it forms with L9

**L8 is a stronger theorem for free, and it has been applied to the module.**
`konckiFamily_ne_std` now reads `c ≠ 0 → konckiFamily a b c a ≠ std a`, with no `a ≠ b`.
At `a = b` the transvection collapses to `(1 + c) • std a`, and `c ≠ 0` already separates
that from `std a`; the proof is a two-way case split on `b = a` with the original
evaluation-at-`b` argument in the second branch. `konckiFamily_moves_exactly_one_label`
inherited the strengthening.

The interesting part is **L9 against L8**: the *same* binder `a ≠ b`, deleted from the
*adjacent* theorem, is **irremovable** — and not marginally so, because at `a = b` the
transvection genuinely **is** diagonal, with scaling `1 + c`, which is exactly the witness
`d` that refutes the lesioned statement. So the two lesions of one binder land on opposite
sides, and that pair is the sharp control for `a ≠ b` in part 5. This is the same shape as
`rem:hyp` of the paper, where the two `Ψ`-lesions differed only in whether the perturbation
was `≡ 1` mod the uniformiser and landed on opposite sides of `G^×`-membership.

What the strengthening cost, recorded because it is the only thing that moved in the axiom
table: `konckiFamily_ne_std` and `konckiFamily_moves_exactly_one_label` picked up
`Classical.choice` (from `eq_or_ne`), going from `propext, Quot.sound` to
`propext, Classical.choice, Quot.sound`. Still the standard three. The record **set** is
otherwise identical across the two audit runs, verified as a set difference and not by
comparing the two counts, which were both 29.

## Scope — what this does not say

Nothing here is a statement about `Ã`, about Koncki's twisted motivic Chern class, or
about which of them is correct. The theorems are about the *shape* `∏_{m∈M} χ(w_m)` and
about a transvection in label space. In particular:

- `no_point_diagonal_moves_exactly_a_pair` limits **point-diagonal** renormalisations
  only. It is not a claim that no change of basis reaches Koncki's class; part 5 exhibits
  one that does.
- `offdiagonal_can_move_one_cell` formalises the **shape** of Rick's UID 824 discrepancy.
  It does not assert `Koncki_∅ = Ã_∅ + c·Ã_{{1,2}}`; that is his measurement, carried into
  the Lean file as a cited comment.
- **The parents are not promoted.** The mechanism gap stands: `ρ`'s numerator `(1-q)²`
  comes from the bulk factor and contains no `K`-matrix. Promoting a parent would convert
  a named gap into a certificate.

## Artifacts

| file | repo | content |
|---|---|---|
| `TworowD4Kernel/PointDiagonalNoGo.lean` | `clio-vega/tworow-d4-kernel`, commit `908a597` | the module, 27 declarations, sorry-free |
| `TworowD4Kernel.lean:72` | same | root import, so CI builds it |
| `proofs/2026-10-18-lean-point-diagonal-audit.lean` | `clio-vega/proofs` | environment-enumerated axiom audit + the 3-declaration plant |
| `proofs/2026-10-18-lean-point-diagonal-axioms.txt` | same | the audit's 40 output lines, both domains |
| `proofs/2026-10-18-lean-point-diagonal-lesions.lean` | same | the 11 lesions as compiled counterexamples |

Push verified as a **two-way set difference** (`git log origin/main..HEAD` and
`HEAD..origin/main` both empty), not by reading a "pushed" line — a `git add` inside an
`&&` chain once failed while the next line printed "pushed" having pushed the *previous*
commit.

## Registry

Four new children under `coboundary-and-removable-poles` in
`proofs/registry/motegi-typeBC-multiplication.json`, each `lean-verified` with an explicit
`scope` clause:

- `psi-determined-by-singletons-lean` → `psi_prod_eq_prod_singletons`
- `point-diagonal-no-go-lean` → `no_point_diagonal_moves_exactly_a_pair`
- `transposition-invariance-is-shape-only-lean` → `transposition_invariance_on_diagonal`
- `offdiagonal-moves-one-cell-lean` → `offdiagonal_can_move_one_cell`

**The parent's trust is unchanged at `proved`.** `registry_validate.py --proofs-dir .`
reports `OK ... (status: proved)` with 7 warnings, all pre-existing `sources.json`
index misses; the one warning my nodes introduced (an email UID is not an arXiv source id)
was fixed by moving that provenance into the node's `statement` text, where it belongs.

## What I would do next

The brief's five statements are closed. The open thread this leaves is **Q513**: the
no-go says the point-diagonal family is the whole admissible family *and* that it cannot
reach Koncki's class, so the remaining freedom after the three lattice equalities is
exactly the off-diagonal part — and part 5 is now a machine-checked statement that that
part is non-empty. Counting it is the gate Q513 already names.
