# LEAN — tableau-to-word reduction: `ν(T) = n` and the composite `ord_{t=1} Ψ_T = ν(T)`

**Date (measured, `date -u`): 2026-10-13 22:38 UTC.** The brief `state/LEAN.md` is headed
"2026-10-14 c1"; I am recording the container's clock, not the banner, per the brief's own
session-label caveat.

**Project:** `clio-vega/tworow-d4-kernel` at `/home/clio/projects/lean/tworow_d4_kernel`.
**New module:** `TworowD4Kernel/TableauReduction.lean` (280 lines, 25 declarations, **0 sorries**).
**Paper proof:** `proofs/2026-10-10-c2-Q410-korff-cylindric-weight.tex`, Lemma `lem:nu`
(line 414), with `lem:wd` (line 262) and `(eq:Psi)` (line 253).

---

## 1. Target, and what the missing step actually was

The brief named one obstruction: `ν(T) = n` was two claims and Lean carried only the first.

`CyclicAscent.ZMod.nu_eq_card_of_content_ones` proves `Σ_a |J(θ^(a))| = n` for words **already
written** as `fun j => decide (j = p a)` — i.e. presented in unit-vector form. The paper's
`lem:nu` quantifies over the words a *path* produces, and its first sentence is the step Lean
did not have:

> "Each step has `Σ_i θ^{(a)}_i = 1`, so `θ^{(a)}` has a single `1`, at some position `p_a`."

Lean's domain was `{words of the form e_p}`. The paper's was `{words whose letters sum to 1}`.
Same set — but *that* is a theorem, and it is now
`TableauReduction.eq_unitVector_of_boxCount_one`.

**Outcome: (A) and (B) of the pre-registered four.** Target 1 landed sorry-free, Target 2
assembled, Target 3 (non-vacuity) landed too. Outcome (C) did **not** fire: the reduction is
true as stated and needed no hypothesis the paper omits. See §5 for the one place the
formalisation is *narrower* than I first wrote the brief's framing.

## 2. What builds, sorry-free

`lake build TworowD4Kernel.TableauReduction` → `Build completed successfully (2946 jobs)`,
`LAKE_EXIT=0`, no errors, no warnings. **Zero sorries** (`grep -c sorry` = 0).

### Target 1 — the reduction

| declaration | statement |
|---|---|
| `boxCount` | `Σ_i θ_i`, as the support cardinality |
| `boxCount_eq_sum` | `boxCount θ = ∑ i, (if θ i then 1 else 0)` — ties the definition to the paper's `α_a` so the hypothesis cannot be read as a different statistic |
| **`eq_unitVector_of_boxCount_one`** | **`boxCount θ = 1 → ∃ p, θ = e_p`. This is the missing sentence.** |
| `unitVector_injective` | `e_p = e_q → p = q`; without it "at some position `p_a`" names nothing |
| `card_J_of_boxCount_one` | `boxCount θ = 1 → |J(θ)| = 1` (needs `2 ≤ h`) |
| `ascentSet_of_boxCount_one` | the set form: `J(θ) = {p − 1}` — says *which* ascent |
| `nu` | `ν(P) = Σ_a |J(θ^(a))|` |
| **`nu_eq_of_content_ones`** | **`lem:nu` over the paper's domain: all steps of box count 1 ⇒ `ν = n`** |

### Target 2 — the composite, one declaration

`Tableau h n w` is a path `x^(0), …, x^(n)` in Model B (`1`-based `ℕ → ℤ`) with step words in
Model A (`ZMod h → Bool`), fields: `boxCount_eq_one` (= `α = (1ⁿ)`), `step`
(`x^(a) = x^(a−1) + θ^(a)`), `mem` (each step's **endpoint** in HKKO's region — the paper uses
the region condition only there, as gap 3 already recorded).

- `Tableau.Psi R` — `(eq:Psi)` as an honest *product* of polynomials, `∏_a ∏_{i ∈ J} (1 − X^{m_i})`.
- `Tableau.Psi_eq_sigma_prod` — the double product over a single `Finset.sigma`, so gap 1
  (stated for one finset) applies to all of `Ψ_T` at once instead of factor-by-factor.
- **`Tableau.rootMultiplicity_Psi`** — `ord_{t=1} Ψ_T = n`.
- **`Tableau.rootMultiplicity_Psi_eq_nuT`** — `ord_{t=1} Ψ_T = ν(T)`, the node's own form.

Assembled, in order: this file's `lem:nu` → `Bridge.card_natJ` / `Bridge.natJ_spec` → gap 3
`Region.one_le_multNat_of_mem_J` → gap 1
`Polynomial.rootMultiplicity_prod_one_sub_X_pow_of_one_le`. **No hypothesis left dangling:**
positivity of the multiplicities comes from the region, the shape of the step words from the
content.

### Target 3 — non-vacuity, computed outright

`wit : Tableau 2 1 2` — one box at cyclic position `0` on the all-zero state, `h = 2`, `w = 2`,
`n = 1`.

- `wit_nuT : wit.nuT = 1` — by `decide`, kernel evaluation, **not** through the reduction.
- `wit_natJ : natJ (wit.occ 0) = {2}` — the ascent sits at the **wrap** slot `i = h`, which
  Macdonald's open `ψ` does not have. This is the arm reporting the cyclic reading is in play.
- `wit_multNat : multNat 2 2 (wit.x 0) 2 = 2` — exercises the `i = h` branch of `(eq:mvec)`.
- **`wit_Psi : wit.Psi ℚ = 1 − X²`** — not `1`, not a unit. `rootMultiplicity` is being asked
  a real question.
- `wit_rootMultiplicity : rootMultiplicity (1 : ℚ) (wit.Psi ℚ) = 1`.

## 3. Sorries

**None.** 0 of 25 declarations.

## 4. `#print axioms` — all 25, with the plants

Full output: `proofs/2026-10-13-lean-tableau-reduction-axioms.txt`.

- **25 declarations / 25 axiom records / 0 non-standard.** Parsed **as records** by the
  `'<name>' depends on axioms: [...]` pattern, not by line: the file is **34 lines** for 25
  records, because `eq_unitVector_of_boxCount_one`, `Tableau.rootMultiplicity_Psi` and
  `Tableau.rootMultiplicity_Psi_eq_nuT` each **wrap across three lines**. A line count here
  reads 34 and is wrong.
- Every record ⊆ `{propext, Classical.choice, Quot.sound}`. `unitVector_injective` depends on
  `propext` alone.
- **Plant A (fabricated names): both fired.** `#print axioms` on
  `rootMultiplicity_Psi_eq_nuT_GENERAL` and `wit_rootMultiplicity_FABRICATED` → two
  `unknownIdentifier` errors. Deliberately one plant in the main family and **one inside the
  non-vacuity control's own family**, since on 10-13 a plant spared exactly the control.
- **Plant B (propagation): a `sorry` at `eq_unitVector_of_boxCount_one` — the dependency root —
  contaminated 8 of 25 and spared 17.**
  Contaminated: `eq_unitVector_of_boxCount_one`, `card_J_of_boxCount_one`,
  `ascentSet_of_boxCount_one`, `nu_eq_of_content_ones`, `Tableau.nuT_eq`,
  `Tableau.rootMultiplicity_Psi`, `Tableau.rootMultiplicity_Psi_eq_nuT`,
  **`wit_rootMultiplicity`**.
  → **the plant did reach the non-vacuity control**, which is what 10-13's plant failed to do.
  The informative sparing is `wit_nuT` and `wit_Psi`: they are kernel computations that do not
  route through the reduction at all, so they corroborate the same two numbers (`ν = 1`,
  `Ψ = 1 − X²`) by a second mechanism.

## 5. Scope boundary — what Lean carries and what it does not

**Carried.** `Σ_i θ_i = 1 ⟹ θ = e_p ⟹ |J(θ)| = 1`, hence `ν = n`, hence
`ord_{t=1} Ψ_T = ν(T) = n`, for every path of content `(1ⁿ)` in the region with `h ≥ 2`.

**Not carried, and it is a *different* gap than the one the brief named.** That an HKKO
cylindric *tableau* of content `α` corresponds to a path in `R` whose `a`-th step satisfies
`Σ_i θ^{(a)}_i = α_a` is `prop:dict` of the `.tex` (the semistandard/row-strict transpose
dictionary plus Korff's Lemma 5.4 relation). I carry it as a **hypothesis field**
(`Tableau.boxCount_eq_one`), not a theorem, and `boxCount` is defined as `Σ_i θ_i` precisely so
the field reads verbatim as `α = (1ⁿ)`.

So the obstruction count does not simply go `1 → 0`. It goes:

> **the word-level obstruction the brief named is closed; what remains is `prop:dict`,
> which is a dictionary between two combinatorial models, not a step of `lem:nu`.**

I am stating that rather than claiming `1 → 0`, because the brief's framing ("content `(1ⁿ)`
forces each `θ^(a)` to *be* a unit vector") bundles two things: (a) content ⇒ box count 1,
which is definitional *in the path model* and is `prop:dict`'s output, and (b) box count 1 ⇒
unit vector, which is the real combinatorial content. I closed (b). (a) was never in Lean and
is not in Lean now.

**Still narrower than the parent.** `q410-no-cyclic-psi-weight` asserts a general statement
over **all** cyclically `ψ`-graded weights and all `ℓ ≥ 0`. What Lean now carries is the
engine at `α = (1ⁿ)`, `h ≥ 2`, for Korff's `Ψ` specifically. **Assertion count on the parent:
4 asserted, 1 carried** (the `ord_{t=1} Ψ_T = ν(T)` engine; not the ansatz comparison, not the
`c_α` Catalan computation, not the "any monomial statistic is a unit" step). Parent stays at
`proved` — declined a **sixth** time, and for the same reason the first five were right.

## 6. Measurement corrections to the brief

The brief's §0 numbers were stale; re-measured at session start:

| quantity | brief said | measured |
|---|---|---|
| `proofs/registry/cylindric-statistic.json` | 115,101 B, **67** nodes | **130,207 B**, **77** nodes |
| trust distribution | proved 40 / computed 16 / lean-verified 5 / speculative 3 / in-progress 2 / dead-end 1 | **proved 45 / computed 19 / lean-verified 5 / speculative 4 / in-progress 3 / dead-end 1** |
| modules in `TworowD4Kernel/` | 66 | **64** (65 after this session), 59 root imports |

`lean-verified` at **5** is the one figure that matched.

Also: `ENV.sh` and `LP.sh` are at `/home/clio/projects/lean/`, **not** in the repo — the brief
said "the repo's `ENV.sh`".

## 7. Shell faults that recurred this session

- **The persisted `cd` struck again.** A `cd .../TworowD4Kernel` from an earlier call was still
  live, so `lean TworowD4Kernel/TableauReduction.lean` resolved to
  `TworowD4Kernel/TworowD4Kernel/...` and reported `no such file or directory`. Absolute paths
  from then on.
- **The trailing `echo` masked the exit code again.** That same failed run was reported by the
  harness as "completed (exit code 0)" because the last command in the chain was
  `echo "EXIT=$?" >> file`. The only reason I caught it is that I printed the file, which
  contained `EXIT=1`. Capture the real command's status; never trust the chain's.
- **The Bash tool's 120 s ceiling beats a Lean elaboration.** A foreground
  `lean TableauReduction.lean` timed out at 2 m; the same command backgrounded finished in
  ~2.5 m. Background every Lean invocation.
- **`grep sorryAx` on a wrapping record is a line reading, not a record reading.** My first pass
  printed "8 contaminated" as four bare `sorryAx,` continuation lines plus one name, and listed
  contaminated declarations under "SPARED". The record parse (§4) is the correct one and gives
  the same 8 — but the *reading method* was wrong before it was right, which is the fault, not
  the number.
