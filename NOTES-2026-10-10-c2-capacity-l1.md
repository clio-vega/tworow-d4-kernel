# Capacity lemma, formalised — and the brief's stretch goal refuted

**Session:** 2026-10-10 c2 LEAN. **Module:** `TworowD4Kernel/CapacityL1.lean`.
**Paper proof:** `projects/proofs/2026-10-10-Q405-twisted-trace-cylindric-statistic.tex`,
`lem:cap` and `thm:main`. **External input bounded:** HKKO Thm 3.3, arXiv:2301.13117;
Warnaar arXiv:2511.17034 §6.

## What is machine-checked

7 declarations, 0 sorries, standard three axioms on all 7 (`#print axioms`, records
counted after joining wrapped lines — not `grep -c`).

| declaration | content |
|---|---|
| `sum_card_fiber_le` | **the whole content**: fibres of `stat` over distinct values are disjoint subsets of `S`, so their sizes sum to `≤ #S` |
| `l1_le_card` | `lem:cap`(2): `‖c‖₁ ≤ #S` when `c e = Σ_{stat i = e} ε i` and `|ε i| ≤ 1` |
| `sum_posPart_le_card` | `lem:cap`(1): `Σ_e max(c e, 0) ≤ #A` |
| `sum_negPart_le_card` | `lem:cap`(1) mirror, *proved by instantiating the positive part at `(B,A,-c)`* |
| `witnessM2` | `c_α(t) = 2 − 3t + t³` as `ℕ → ℤ` |
| `no_signed_statistic_M2` | `thm:main` Step 4: no `4`-element signed statistic reproduces `2 − 3t + t³`, since `‖·‖₁ = 6 > 4` |
| `no_strict_statistic` | `thm:main` Step 3, uniform in `ℓ`: coefficient `−(2m+3)` with only `2m+2` negative-sign objects is impossible |

Two deliberate generalisations away from the paper: `|ε i| ≤ 1` instead of `ε i = ±1`
(what the proof actually uses, and it admits vanishing weights), and `A`, `B` not assumed
disjoint in part (1) (the bound does not need it).

## The brief's stretch goal is false

The brief asked for the signed gap "exactly `2` for every `M ≥ 2`", on
`‖c_α‖₁ = C_M + 2M` against `TOT_α = C_M + 2M − 2`. **The arithmetic is right and the
labelling is wrong:** `C_M + 2M − 2` is `A_α + B_α`, not `TOT_α`. They coincide only at
`M = 2`, where no shape of size `4` in `Par(2,2)` has `c⁻ = 0`. For `M ≥ 3` the intermediate
even endpoints `d = 2,…,w−2` contribute `c⁻ = 0` shapes — invisible to HKKO Thm 3.3 — and
`TOT_α` outgrows `A_α + B_α`: at `M = 3`, `TOT = 18` against `‖c_α‖₁ = 11`, so the capacity
inequality is **satisfied** and `l1_le_card` yields nothing.

The paper's own remark, four lines below the theorem, is titled *"why `ℓ = 0` is the only
place the stronger form bites"* and says this. I did not need to compute anything to find
it; I needed to read past the theorem I was quoting.

The uniform-in-`ℓ` statement *does* exist — it is part (1), deficit exactly `1`, which is
`no_strict_statistic`. So the brief applied the right shape to the wrong part of the lemma.
`no_signed_statistic_M2` is sharp at `ℓ = 0` and that is not a limitation to fix.

## Instrument notes

- **Negative control fired.** `sorry` planted at the dependency root (`sum_card_fiber_le`):
  **6 of 7 contaminated by `sorryAx`, `witnessM2` correctly spared** (a `def`, independent of
  the lemma). `lake build` **succeeded** in that arm — only a warning — so `#print axioms` is
  the sole instrument that catches it.
- **First plant was malformed** (`sorry` before `classical` ⇒ "No goals", build broken,
  audit read **0 records**) and the script printed `contaminated/unparsed: 0` beside it —
  the silent-pass shape. Hardened the audit to `exit 2` on zero records. It then fired for
  real later in the session, when a persisted `cd` left me outside the repo.
- **`registry_validate.py` has the double-prefix fault**, now the third tool with it:
  `--proofs-dir` defaults to the registry's parent (`proofs/`) while node `file` fields
  already carry `proofs/`. **27 false "not found" → 0** with `--proofs-dir .`.
