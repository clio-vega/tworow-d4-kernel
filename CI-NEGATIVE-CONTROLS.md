# CI negative controls — what a red run means

This repository deliberately keeps two branches that **must fail CI**. A red run on either of
them is a **PASS**: it proves a detector is alive. This file exists because, until now, a red
run that meant "the detector works" and a red run that meant "the build is broken" were
indistinguishable in the GitHub failure-email subject line. That ambiguity has already produced
one false *"CI is red on main"* alarm.

Neither branch is ever to be merged.

---

## The two controls

| Branch | Plants | Breaks | Detector it proves alive |
|---|---|---|---|
| `NEGATIVE-CONTROL-expected-red-axiom-audit` | `theorem ci_negative_control : 2 + 2 = 5 := by sorry` in `TworowD4Kernel/NegativeControl.lean`, imported from the root | the **axiom-audit** step | a `sorry` cannot reach a green badge |
| `NEGATIVE-CONTROL-expected-red-test-driver` | flips `#guard decide ((∑ x ∈ addRibbon 3 ({0,1} : Finset ℤ) 0, x) = 4)` to `= -2` in `TworowD4KernelTests.lean` | the **test** step (`lake test`) | the test driver actually runs, and pins the ribbon *direction* |

They are deliberately aimed at **different detectors**. The `sorry` is invisible to `lake build`
and the `#guard` is invisible to the axiom audit, so neither control can pass by accident
because the other detector fired.

### `NEGATIVE-CONTROL-expected-red-axiom-audit` — expected failure

Planted at `TworowD4Kernel/NegativeControl.lean:8`. The build step **succeeds**, emitting only

```
warning: TworowD4Kernel/NegativeControl.lean:8:8: declaration uses `sorry`
```

A `sorry` is a *warning* to `lake build`, never an error — this is exactly why run
`33370053897` on this branch finished **`success`** before `axiom-audit` was turned on. The
detector is the audit step:

```
axiom-audit: 1 declaration(s) under 'TworowD4Kernel' use disallowed axioms:
  TworowD4Kernel.ci_negative_control → [sorryAx]
allowed: [propext, Classical.choice, Quot.sound]
##[error]axiom-audit check failed
```

The second commit on the branch (`import TworowD4Kernel.NegativeControl` in the root) is
load-bearing: the audit follows the root module's **import closure**, not the namespace, so an
unimported file with a `sorry` in it is not audited at all.

Reference run: `33551104884` (failure, 1m48s).

### `NEGATIVE-CONTROL-expected-red-test-driver` — expected failure

Planted in `TworowD4KernelTests.lean`, `section AbacusRibbonDirection`. The bead sum of `{0,1}`
is `1`; adding the `3`-ribbon at `0` takes it to `4`, not to `-2`. The `-2` is the direction
error from the 2026-09-03 DREAM note, planted verbatim. `#guard` fails at elaboration and the
run ends:

```
##[error] lake test failed
##[error]Process completed with exit code 1.
```

Reference runs: `33817055657` (failure, 1m30s) and `33817248757` (failure, 1m38s).

**Step ordering matters here.** When `test` fails, the later steps — `lint`, `nanoda`,
`axiom-audit` — all report `outcome=skipped`. A red run on this branch therefore carries **no
information about the axiom audit**; that is what the other control is for.

---

## The discriminator is the branch name — NOT the timing

An earlier working hypothesis held that the planted direction error fails in ~1m30s where clean
`main` takes ~44m, and that *a one-minute red is therefore diagnostic on its own*. **That is
false, and the run history refutes it:**

| Run | Branch | Result | Wall |
|---|---|---|---|
| `33551104884` | `NEGATIVE-CONTROL-expected-red-axiom-audit` | failure (expected) | 1m48s |
| `33817055657` | `NEGATIVE-CONTROL-expected-red-test-driver` | failure (expected) | 1m30s |
| `33817046570` | **`main`** | failure (**genuine breakage**) | **1m45s** |
| `33920018865` | `main` | success | 44m09s |
| `33848574291` | `main` | success | 44m22s |

The genuine `main` breakage — the lakefile glob resolving locally and failing in CI with
`error: no such file or directory` — failed in **1m45s**, squarely inside the "diagnostic"
window. Timing does not separate an expected red from a real one.

The reason the asymmetry looked meaningful: **`docgen-action` is skipped on every failed run and
runs on every successful one**, and docgen is the ~40 minutes. So the wall clock separates
*red from green*, which the subject line already tells you, and says nothing about *which kind
of red*. All three failures above also fail at the same composite step (`lean-action@v1`), so
step name does not discriminate either.

**What actually discriminates is the branch name**, which is why it appears in the failure-email
subject and why the branches are named to be read there. Rules for triage:

- Branch name contains `NEGATIVE-CONTROL` → **expected red. This is a pass.** Do nothing.
- Branch is `main` and the run is red → **genuine breakage**, regardless of how fast it was.

---

## Known detector gap (2026-09-04) — do not infer test-driver coverage

`Maya.size` is **noncomputable**: `wt` decides set membership through `Classical.propDecidable`,
and `#guard` *compiles* its argument. The `Maya` section of `TworowD4KernelTests.lean` therefore
cannot use `#guard` at all. Those checks are statement-pinning `example`s instead — each
restates the numeral a library theorem claims and discharges it *by that theorem*.

This is a strictly weaker detector, and it is labelled as such in the test file: **it detects a
changed statement, not a changed value.** The affected declarations are `Maya.size_nil`,
`Maya.size_onebox`, `Maya.size_addRibbon_above`, `Maya.size_addRibbon_below` and
`Maya.exists_size_addRibbon_ne_of_mem`.

Consequently the two controls added on 2026-09-04 are checked by `lake build` and are **not**
shadowed by any `#guard`. A reader must not infer test-driver coverage for them. Neither
negative-control branch exercises this path, so **there is currently no live negative control
for the `Maya` size theorems** — a wrong numeral there would be caught only if the corresponding
`example` were updated to match, which is precisely the failure mode an `example`-based pin
cannot see.

---

## Branch rename (2026-09-05)

The branches were renamed from `ci-negative-control` and `ci-test-negative-control` so that the
discriminator is unmissable in the failure-email subject, which has the form
`Run failed: Lean Action CI - <branch> (<sha>)`:

- `ci-negative-control` → `NEGATIVE-CONTROL-expected-red-axiom-audit`
- `ci-test-negative-control` → `NEGATIVE-CONTROL-expected-red-test-driver`

Commit SHAs are unchanged; the old remote refs are deleted. The rename itself triggers one
fresh red run per branch, and those two reds are expected.
