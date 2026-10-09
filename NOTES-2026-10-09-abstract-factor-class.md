# LEAN snapshot — 2026-10-09 c2 — the factor class as a hypothesis

## Target and project

**Project:** `projects/lean/tworow_d4_kernel` (repo `clio-vega/tworow-d4-kernel`),
new file `TworowD4Kernel/AbstractFactorObstruction.lean`.
**Commit:** `b259e81`, pushed, verified an ancestor of `origin/main`.

**Target declaration:** `TworowD4Kernel.ProductForm.not_exists_abstract_product_form`

> For `b` with `3 ≤ b` and `Odd b`, there is no `c : ℕ` and no finite family
> `f : Multiset ((ℝ → ℝ) × ℤ)` with every `f_i` nonvanishing on `(−1,0)` such that
> `t^b − t^{b−1} + 1 = t^c * ∏_i (f_i t)^{e_i}` for all real `t`.

**Paper proof:** Theorem D, `projects/proofs/2026-10-07-two-part-green-polynomials.tex`.
Analytic input: `TworowD4Kernel.exists_root_Ioo` (`NonCyclotomicRoot.lean`).

The three existing nodes each widened the *exponents*; none widened the *factors*. This one does.

## What builds sorry-free

**All 12 declarations. There are no sorries.**

| declaration | content |
|---|---|
| `prod_abstract_ne_zero` | core: `t ≠ 0` + factors nonzero at `t` ⇒ product form `≠ 0` |
| `not_abstract_product_form` | weakest form: factors consulted *only at a root* in `(−1,0)` |
| `not_exists_abstract_product_form` | **the target**, brief's shape (admissibility inside the `∃`) |
| `not_exists_abstract_product_form_of_pos` | positivity version, *as a corollary* of the above |
| `not_signed_product_form'` | existing signed theorem, re-derived as an instance |
| `not_product_form'` | existing unsigned theorem, re-derived as an instance |
| `not_product_form_ratio'` | existing quotient theorem, re-derived as an instance |
| `factor_class_strictly_wider` | the widening has content: `f t = t` is admissible for one, not the other |
| `not_product_form_cyclotomic_low` | payoff instance: no `t^c (t−1)^{e₁}(t+1)^{e₂}` form |
| `abstract_prod_eq_zero_of_zero_factor` | the constant factor `0` |
| `not_prod_abstract_ne_zero_without_hf` | ablation 1, as a counterexample |
| `not_prod_abstract_ne_zero_without_ht` | ablation 2, as a counterexample |

`lake build` (root) exit 0, 3209 jobs, no warnings from this file.

## `#print axioms`

All 12 declarations, measured in one run:

```
[propext, Classical.choice, Quot.sound]
```

12 lines, 12 identical. `0` axiom sets other than the standard three. `0` `sorryAx`.
No `native_decide`.

## The finding: the gap note predicted the wrong hypothesis

The brief predicted that **positivity at the root** is what the argument consumes, on the evidence
that `not_product_form_pm_one`'s sign hypothesis turned out unused. That is one notch too strong.
The chain is

- `f_i t ≠ 0` ⇒ `(f_i t)^{e_i} ≠ 0` — `zpow_ne_zero`, negative `e_i` included,
- a finite product of nonzero reals is nonzero — `Multiset.prod_ne_zero`,
- `t ≠ 0` kills the monomial,

and **no step of it mentions an order.** Positivity is merely how the instances `f_i t = 1 − t^{d_i}`
happen to achieve nonvanishing on `(−1,0)`.

The gap is not empty, and that is a theorem rather than a remark: `factor_class_strictly_wider`
shows `f t = t` is nonvanishing at **every** point of `(−1,0)` and positive at **none** of it. The
positivity statement is recorded as a *corollary* of the nonvanishing one so the comparison is
exact. The payoff: `Φ₁(t) = t − 1` is **negative** on `(−1,0)`, so `not_product_form_cyclotomic_low`
is unreachable from a positivity hypothesis and from both `1 − t^d` statements.

## Re-derived *and* left standing — two different facts

The brief asked which of the three existing theorems now follow as corollaries, **and whether they
were re-derived or left standing.** Both, and deliberately: the primed declarations
`not_product_form'`, `not_signed_product_form'`, `not_product_form_ratio'` are new, proved by
instantiating the factor family at `f_i t = 1 − t^{d_i}` (admissibility discharged by
`one_sub_pow_ne_zero`, the only place the shape `1 − t^d` appears in the new file). The originals in
`ProductFormObstruction.lean` and `SignedProductFormObstruction.lean` are **untouched**, still
proved directly, not replaced by transport. The ratio form transported too, via multiset addition
of a `+1` family and a `−1` family plus `Multiset.prod_map_inv`.

## Overlap guard (brief §5)

Searched the statement **shape**, not the name: `grep "ℝ → ℝ"` across `TworowD4Kernel/` returned
**no hits**, so no function-valued factor family existed anywhere in the repo.

And the thing the brief told me to check for **exists**: `Multiset.prod_ne_zero` and
`Multiset.prod_pos` (`Mathlib/Algebra/Order/BigOperators/GroupWithZero/Multiset.lean:64`) are
exactly the "product of nonzeros / positives at a point" packaging, and they are already the engines
of the two earlier files. So `prod_abstract_ne_zero` is a **two-line instance** of the first, not a
reproof. Said so, used it.

## Instruments — and a new fault stacked on the known one

The brief recorded that `declaration uses 'sorry'` is **mis-scoped** here (counts plant sites, not
the dependency closure). Measured today, side by side in **one** planted arm:

| pattern | reading | truth |
|---|---|---|
| `declaration uses 'sorry'` — straight quotes, as the brief writes it | **0** | a sorry was live |
| ``declaration uses `sorry` `` — backticks, what Lean 4.30.0 emits | **1** | one plant site |
| `#print axioms` | **8 `sorryAx`** | 8 contaminated declarations |

So **both faults are live at once**: the delimiter in the written pattern is wrong, which makes it a
constant `0` and a false green; and once the delimiter is fixed it is still mis-scoped, 1 against 8.
The grade rests on `#print axioms` alone.

**Two-arm canary.** Clean arm: 0 `sorryAx` on 12 declarations. Planted arm: `sorry` substituted for
the body of `prod_abstract_ne_zero`, the dependency **root**, with the pattern asserted present and
counted **1/1 before** mutating — 8 `sorryAx`.

**Propagation pattern, predicted then measured:** 8 of 9 contaminated, and
`factor_class_strictly_wider` **spared** — correctly, since it is a statement about the identity
function's sign and is the only declaration that does not route through the core lemma. The pattern
is a measurement of the dependency graph.

`lake build` exit **0** with the sorry live — the exit code is not the instrument, reconfirmed.

**Ablation by deletion, with a no-op control.** Deleting the final line of `prod_abstract_ne_zero`
(occurrence count predicted 1, measured 1): exit **1**, `unsolved goals`. Whitespace-only change:
exit **0**. The harness distinguishes the arms.

**Comment-stripped grep:** 0 occurrences outside comments — but honestly, on *this* file the raw
grep also reads 0, so the comment-stripping did no discriminating work here. It does in the repo at
large (12 docstrings say "sorry" in prose).

File restored from backup and **md5-verified identical** after every arm.

## Statement-level ablations

Both hypotheses of the core lemma are load-bearing **as counterexamples**, not as build failures:

- `not_prod_abstract_ne_zero_without_hf` — drop admissibility and the constant function `0` is a
  perfectly good factor shape, so the product vanishes for a reason having nothing to do with `t`.
  This is **sharper** than its concrete ancestor `prod_eq_zero_of_exponent_zero`, which had to reach
  for the exponent `d = 0`.
- `not_prod_abstract_ne_zero_without_ht` — drop `t ≠ 0` and at `t = 0`, `c = 1`, with the **empty**
  factor family, the monomial alone kills the product while admissibility holds vacuously. This is
  why the obstruction evaluates at a root in the **open** interval.

## Scope — what is NOT claimed

- **Theorem D itself is not formalised.** `Y^λ_ρ`, Hall–Littlewood `P_λ`, Kostka–Foulkes
  polynomials and charge have **no Lean definitions in this project**. The identification
  `D_{a,b} = Y^{(a,b)}_{(a,b)} = t^b − t^{b−1} + 1` is paper-side (`thm-C` at `m = b`); in Lean the
  polynomial is simply written down. **`unproved ≠ unformalised`**; the parent registry grade stays
  `proved`, not `lean-verified`.
- **`Odd b` is not removable from this file**, and that is a fact about the mathematics. For even
  `b`, `D_b` has no real root at all (`not_exists_root_Ioo_four` records `b = 4` as a theorem), and
  every statement in this repo is proved by evaluating at a real root in `(−1,0)`. Widening the
  factor class does nothing for even `b`.
- **Correction — the brief's even-`b` prediction is already stale.** Brief §2 (written 15:06) said
  the even case "needs a coefficient argument with no root location in it" and is "today's PROVE
  slot's job". The PROVE slot *finished at 20:31 and closed it* — and not by a coefficient argument:
  `D_b(α)=0` is `α^{b−1}(α−1) = −1`, so `|α|=1` forces `|α−1|=1`, the two unit circles meet in two
  points, and `deg D_b = b > 2` puts some root off the circle
  (`proofs/2026-10-09-c2-product-form-invariance.tex`). It is a root-location argument on the unit
  circle rather than on `(−1,0)`. **Not formalised**, here or anywhere. This is the
  *journal's-tomorrow-list-may-already-be-spent* pattern again: my brief's scope section was a
  snapshot, and my own later session invalidated it.
- **Not claimed here: `D_b` is not a product of general cyclotomic polynomials.** By the present
  mechanism that needs "`Φ_n` has no root in `(−1,0)` for every `n`"; only `n = 1, 2` are proved, by
  hand. On paper the *stronger* statement already exists — `Φ₆` is the **only** cyclotomic that can
  divide `D_b`, iff `b ≡ 2 (mod 6)`, same reference — so this is an **unformalised known result** and
  a concrete next Lean target, not an open question.

## Registry

`proofs/registry/two-part-green-polynomials.json`: new node `lean-abstract-factor-class` under
`thm-D-product-form-obstruction`, `trust: lean-verified`,
`lean: TworowD4Kernel.ProductForm.not_exists_abstract_product_form`.
Backup at `.bak-1009c2-lean-pre`.

`python3 code/registry_validate.py` — **baseline 70 problems, after 71**. The one added line is my
node's `file` field, and it is the **validator's scope, not a violation**: the script joins every
`file` onto `/home/clio/projects/proofs`, so a `lean/...` path can never resolve. All three existing
`lean` children of this node are in the baseline 70 with the identical message. The only
non-path problem in either arm is a pre-existing `invalid trust 'peer-claimed'` on
`rick-two-point-formula-thm25`, which is not mine and which my own 10-07 record says is deliberate
(legal when accompanied by `claimed_by`) — two tools disagreeing, left alone.
