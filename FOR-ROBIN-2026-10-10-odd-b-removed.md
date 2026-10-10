# For Robin — 2026-10-10 LEAN: `Odd b` removed, and the brief was wrong about how

Commit `ab2f3c0` on `clio-vega/tworow-d4-kernel`, verified an ancestor of `origin/main`.
Full snapshot: `NOTES-2026-10-10-unit-circle-obstruction.md` in this repo.
Source: `TworowD4Kernel/UnitCircleObstruction.lean` — **15 declarations, 0 sorries, 15/15 on
`[propext, Classical.choice, Quot.sound]`.**

## What you asked for

For **every** `b ≥ 3` (even `b` included), `D_b(t) = t^b − t^{b−1} + 1` is not of the shape
`z^c ∏_i (f_i z)^{e_i}`:

```lean
theorem TworowD4Kernel.UnitCircle.not_exists_abstract_product_form_all_b
    (b : ℕ) (hb : 3 ≤ b) :
    ¬ ∃ (c : ℕ) (f : Multiset ((ℂ → ℂ) × ℤ)),
      (∀ p ∈ f, ∀ z : ℂ, ‖z‖ ≠ 1 → p.1 z ≠ 0) ∧
      ∀ z : ℂ, z ^ b - z ^ (b - 1) + 1 = z ^ c * (f.map (fun p => (p.1 z) ^ p.2)).prod
```

## Two things you should know, because both contradict the brief

**1. The brief's literal target is false, so I proved the counterexample instead.**

The brief asked for the old statement "with the parity hypothesis dropped" — keeping the *real*
factor class, admissible when nonvanishing on `(−1,0)`. That is false for even `b`, and it is now
a theorem in the file (`exists_abstract_product_form_real_of_even`): for even `b`, `D_b` has no
real root at all, so **`D_b` is itself an admissible factor** — take `c = 0`, one factor,
exponent `+1`. Widening the *factors* cannot repair the loss of the *evaluation point*.

So the class had to move: `ℂ`, with admissibility = **nonvanishing off the unit circle**. That is
not a convenience — it is the condition the paper's own factors `1 − t^{d_i}` actually satisfy,
since their zeros are roots of unity. I formalised that too
(`one_sub_pow_ne_zero_of_norm_ne_one`) and transported the concrete statement
(`not_signed_product_form_all_b`), so the generalisation provably contains the thing it generalises.

The brief's step 5 already said "some root lies off the unit circle ⇒ the nonvanishing hypothesis
fails" — but the hypothesis it was pointing at lives on `(−1,0)`. Two different factor classes,
identified inside one sentence. Worth a look at the paper's phrasing for the same slip.

**2. The finish is shorter than the paper's, and it drops a premise.**

The paper goes: `re α = 1/2` ⇒ `α = e^{±iπ/3}` ⇒ `α − 1 = α²` ⇒ `α^{b+1} = −1` ⇒ `b ≡ 2 (mod 6)`,
then `deg D_b = b > 2` forces a root off the circle — which additionally needs the roots of `D_b`
to be **simple** (registry `lem-D-roots-simple`).

The Lean proof stops at `re α = 1/2` and never names the two points. Every on-circle root has
`normSq(−1 − α) = normSq α + 2 re α + 1 = 3`, so if all `b` roots were on the circle then
evaluating the monic root factorisation at `t = −1` gives `normSq(D_b(−1)) = 3^b`. But
`D_b(−1) = (−1)^b − (−1)^{b−1} + 1` is `3` or `−1`, so `normSq ≤ 9 < 27 ≤ 3^b`.

Consequences worth keeping:
- **No case split on the parity of `b` anywhere.** Both possible values of `D_b(−1)` have
  `normSq ≤ 9`, so the two parities never separate. The hypothesis the whole session was about
  isn't a case in the proof either.
- **`3 ≤ b` is consumed exactly once**, as `3^b > 9`. It is not a degree bound in disguise.
- **Simplicity of the roots is not used.** `lem-D-roots-simple` stays `proved` and unformalised,
  correctly — the route doesn't need it. If you want the paper tightened, that premise can come
  out of Theorem D′ as well.

Also, your "two unit circles meet in two points" is not plane geometry: `‖α‖ = 1` is
`α·conj α = 1`, `‖α − 1‖ = 1` expands to `normSq α − 2 re α + 1 = 1`, the ones cancel, `re α = 1/2`.
Four lines of `normSq`, no square roots. That is `re_eq_half_of_normSq`, and it's the dependency
root of the whole file.

## Instrument findings, for the toolchain rather than the mathematics

- `code/registry_validate.py` reports **72 problems** by default and **3** with
  `--proofs-dir /home/clio/projects`. Its default base is `dirname(dirname(registry))` =
  `…/projects/proofs`, while node `file` fields already carry the `proofs/` prefix — so
  `os.path.join` yields `proofs/proofs/…` and **69 are phantom**. This is the *same* double-prefix
  fault I already had recorded for `trustcheck.py --files-dir`, now in a second tool.
- `registry_validate.py` rejects `trust: peer-claimed`, which `trustcheck.py` accepts and which
  one node legitimately uses — a stale enum in one of two tools that are supposed to agree. I did
  **not** repair it: a Lean session is the wrong place, and it needs a decision about which enum is
  canonical. Flagging it for you.
- Smaller, but it nearly cost me the headline number: `grep -c` on raw `#print axioms` output read
  **12 of 15** clean, because Lean's pretty-printer **wraps** the axiom list across lines for long
  declaration names. The three "missing" declarations were clean all along. A line count is not a
  declaration count when the output is formatted.

## What this does not claim

`Y^λ_ρ`, `P_λ`, Kostka–Foulkes and charge still have **no Lean definitions** in this project;
`t^b − t^{b−1} + 1` is simply written down. This is the **polynomial obstruction**, not Theorem D's
combinatorial content, and `thm-D`'s `proved` grade is untouched. `Φ₆ | D_b ⟺ b ≡ 2 (mod 6)` and
the companion family `E_b = t^b − t^{b−1} + 2` were offered as stretch targets; the route above
doesn't pass through either, so taking them would have been a second target instead of this one
finished.

— Clio
