# Lean snapshot — 2026-10-10 — removing `Odd b` from the product-form obstruction

**Project:** `clio-vega/tworow-d4-kernel`, module `TworowD4Kernel/UnitCircleObstruction.lean`
(new file, registered in the root aggregator `TworowD4Kernel.lean`).
**Registry:** `proofs/registry/two-part-green-polynomials.json`, node
`thm-D-product-form-obstruction/thm-D-prime-all-b/lean-unit-circle-obstruction-all-b`.
**Paper proof:** `proofs/2026-10-09-c2-product-form-invariance.tex` (Theorem D′, all `b ≥ 3`).

## Headline

`Odd b` is gone. **15 declarations, 0 sorries, 15/15 reading exactly
`[propext, Classical.choice, Quot.sound]`.**

Target declaration:

```lean
theorem TworowD4Kernel.UnitCircle.not_exists_abstract_product_form_all_b
    (b : ℕ) (hb : 3 ≤ b) :
    ¬ ∃ (c : ℕ) (f : Multiset ((ℂ → ℂ) × ℤ)),
      (∀ p ∈ f, ∀ z : ℂ, ‖z‖ ≠ 1 → p.1 z ≠ 0) ∧
      ∀ z : ℂ, z ^ b - z ^ (b - 1) + 1 = z ^ c * (f.map (fun p => (p.1 z) ^ p.2)).prod
```

Content lemma (the mathematics):

```lean
theorem TworowD4Kernel.UnitCircle.exists_root_normSq_ne_one (b : ℕ) (hb : 3 ≤ b) :
    ∃ α : ℂ, α ^ b - α ^ (b - 1) + 1 = 0 ∧ Complex.normSq α ≠ 1
```

## Two departures from the brief, both measured

### 1. The brief's literal target is FALSE, and that is now a theorem

The brief asked for "the existing statement with the parity hypothesis dropped" — i.e.
`ProductForm.not_exists_abstract_product_form` minus `Odd b`, **keeping** its factor class
`Multiset ((ℝ → ℝ) × ℤ)` admissible when nonvanishing on `(-1,0)`.

That statement has a one-line counterexample for even `b`, formalised here:

```lean
theorem exists_abstract_product_form_real_of_even (b : ℕ) (hb : 2 ≤ b) (heven : Even b) :
    ∃ (c : ℕ) (f : Multiset ((ℝ → ℝ) × ℤ)), … -- witness: c = 0, f = {(D_b, 1)}
```

For even `b`, `D_b` has **no real root at all**, so `D_b` is *itself* an admissible factor. The
real-interval class is too wide the moment there is no evaluation point inside it. **Widening the
*factors* cannot repair the loss of the *evaluation point*.** The brief's own step 5 already
needed the unit circle ("some root lies off the unit circle ⇒ the nonvanishing hypothesis fails"),
but the hypothesis it was pointing at lives on `(-1,0)`, not on the circle — two different classes
silently identified.

So the generalisation moves to `ℂ` with admissibility = **nonvanishing off the unit circle**,
which is the condition the concrete factors `1 - t^(d_i)` actually satisfy (their zeros are roots
of unity — `one_sub_pow_ne_zero_of_norm_ne_one`). `exists_root_Ioo` is not extended; it is
replaced by `exists_root_normSq_ne_one`. The transported instance
`not_signed_product_form_all_b` recovers the `1 - z^(d_i)` shape over `ℂ` with no parity
hypothesis.

A failed `lake build` would have been a fact about my proof. The counterexample is a fact about
the statement.

### 2. A shorter finish than the paper's, which drops a premise

The brief's route: `‖α‖=1` ⇒ `re α = 1/2` ⇒ `α = exp(±iπ/3)` ⇒ `α - 1 = α²` ⇒ `α^(b+1) = -1`
⇒ `b ≡ 2 (mod 6)`; then `deg D_b = b > 2` forces a root off the circle. That last step needs the
roots of `D_b` to be **simple** (registry node `lem-D-roots-simple`), plus a conjugacy argument.

The formalised route stops at `re α = 1/2` and never names the two points:

1. `D_b(α)=0` ⇔ `α^(b-1)(α-1) = -1`.
2. `‖α‖=1` ⇒ `normSq (α-1) = 1`.
3. `normSq α = 1 ∧ normSq (α-1) = 1` ⇒ **`re α = 1/2`** (`re_eq_half_of_normSq`; expand
   `normSq (α-1) = normSq α - 2 re α + 1`, the two ones cancel — four lines, `nlinarith`).
4. Hence `normSq (-1 - α) = normSq α + 2 re α + 1 = 3` for **every** on-circle root.
5. If all `b` roots were on the circle, then evaluating the monic root factorisation at `t = -1`
   and taking `normSq` gives `3 ^ b` (`Multiset.prod_replicate`). But
   `D_b(-1) = (-1)^b - (-1)^(b-1) + 1` is `3` or `-1`, so `normSq (D_b(-1)) ≤ 9 < 27 ≤ 3 ^ b`.

**`3 ≤ b` is consumed exactly once, in step 5, as `3^b > 9`.** It is not a degree bound in
disguise. And there is **no case split on the parity of `b`** anywhere: both possible values of
`D_b(-1)` have `normSq ≤ 9`, so the two parities need not be separated at all — the hypothesis
whose removal was the whole point of the session turns out not to be a case in the proof either.

`lem-D-roots-simple` is **not consumed** and stays `proved`/unformalised, correctly: the route
here does not need it. *A stated route is a claim about necessity* — and this one named a premise
the finish does without.

## Declaration inventory — 15/15 sorry-free

| # | Declaration | Role |
|---|---|---|
| 1 | `re_eq_half_of_normSq` | the algebraic heart; dependency ROOT |
| 2 | `re_eq_half_of_root` | root on circle ⇒ `re = 1/2` |
| 3 | `Dpoly` (def) | `X^(n+2) - X^(n+1) + 1` over `ℂ` |
| 4 | `Dpoly_monic` | `monicity!` |
| 5 | `Dpoly_natDegree` | `compute_degree!` |
| 6 | `Dpoly_eval` | eval bridge to the bare expression |
| 7 | `Dpoly_splits` | `IsAlgClosed.splits` |
| 8 | `Dpoly_card_roots` | `card roots = n + 2` |
| 9 | `exists_root_normSq_ne_one` | **the content** |
| 10 | `normSq_ne_one_iff` | `normSq`/`‖·‖` bridge |
| 11 | `prod_abstract_ne_zero` | core lemma over `ℂ` |
| 12 | `not_exists_abstract_product_form_all_b` | **the target** |
| 13 | `one_sub_pow_ne_zero_of_norm_ne_one` | class contains the paper's factors |
| 14 | `not_signed_product_form_all_b` | transported instance |
| 15 | `exists_abstract_product_form_real_of_even` | **counterexample to the brief** |

Parametrising by `n` with `b = n + 2` is what makes 4 and 5 one-liners: truncated subtraction
never appears inside the polynomial, so `natDegree` is a literal successor.

## `#print axioms`

All 15, verbatim:

```
'TworowD4Kernel.UnitCircle.<decl>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. Whole-project `lake build`: **0 errors, 0 sorries.**

*Measurement note, and it bit me:* `grep -c` on the raw `#print axioms` output read **12 of 15**,
because Lean's pretty-printer **wraps** the axiom list across three lines for long declaration
names. The three "missing" declarations were clean all along. A line count is not a declaration
count when the output is pretty-printed — join first, then count.

## Canary — planted at the dependency ROOT

A `sorry` in `re_eq_half_of_normSq` (declaration #1, the root of the dependency graph):

| arm | `#print axioms` contaminated | spared |
|---|---|---|
| baseline | **0 of 15** | 15 |
| planted | **5 of 15** | 10 |

The 5 are exactly the predicted closure: `re_eq_half_of_normSq`, `re_eq_half_of_root`,
`exists_root_normSq_ne_one`, `not_exists_abstract_product_form_all_b`,
`not_signed_product_form_all_b`. The other 10 — the `Dpoly_*` degree/root facts, the two bridge
lemmas, the core lemma, the admissibility instance and the real-case counterexample — do **not**
route through the algebraic heart, and were correctly spared. The finding is the *difference*
between two readings.

Two known instrument faults reproduced live in the planted arm:

- **`lake build` exited 0 with a sorry live.** The exit code is not the instrument.
- **`grep "declaration uses 'sorry'"` (straight quotes) read 0** while
  ``grep 'declaration uses `sorry`'`` (backticks) read **1**. Lean 4.30.0 emits backticks; the
  straight-quote pattern is a constant function.

File `md5` verified identical to the pre-plant hash after restore
(`eed0b670e47502ebcffa89419a76f3ee`).

## Instrument fault found in `registry_validate.py`

`python3 code/registry_validate.py proofs/registry/two-part-green-polynomials.json` reports
**72 problems**; with `--proofs-dir /home/clio/projects` it reports **3**. The default is
`dirname(dirname(abspath(registry)))` = `/home/clio/projects/proofs`, and the node `file` fields
already carry the `proofs/` prefix, so `os.path.join` yields `proofs/proofs/…` — **69 phantom
"not found" problems.** This is the *same* double-prefix fault already recorded for
`trustcheck.py`'s `--files-dir`, in a second tool. Correct invocation from `projects/`:

```
python3 code/registry_validate.py proofs/registry/<name>.json --proofs-dir /home/clio/projects
```

Of the 3 real problems, 2 are pre-existing and untouched by this session:
`rick-two-point-formula-thm25` uses `trust: peer-claimed`, which is **absent from
`registry_validate.py`'s enum** while being legal in `trustcheck.py` — the stale-constant pattern
again, in a third place; and it points at a registry file `rick/hikita-star-dominance-support.json`
that does not exist. **Not repaired here** — out of a Lean session's scope, recorded so the next
session has the diagnosis rather than the number.

## Scope — stated so this is not read as more than it is

`Y^λ_ρ`, Hall–Littlewood `P_λ`, Kostka–Foulkes polynomials and charge have **no Lean definitions
in this project**. The identification `D_{a,b} = Y^{(a,b)}_{(a,b)} = t^b - t^(b-1) + 1` is
paper-side (Theorem C at `m = b`); here `t^b - t^(b-1) + 1` is simply written down. **This
formalises the polynomial obstruction, not Theorem D's combinatorial content.**
`unproved ≠ unformalised`. The parent `thm-D` registry grade stays `proved` and was not touched.

Also still unformalised, and deliberately: `Φ₆` is the only cyclotomic that can divide `D_b`, and
does so iff `b ≡ 2 (mod 6)`. The brief offered it as a stretch target and the paper proves it, but
the route above does not pass through it, so formalising it would have been a second target rather
than this one finished. The same applies to the companion family `E_b = t^b - t^(b-1) + 2`.
