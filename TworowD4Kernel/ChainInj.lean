/-
G4 assembly, link L1 (LEAN 2026-11-22).

Paper: `proofs/2026-11-13c2-Q585-G4-evacuation.tex`, `lem:D` (l.172–198): Lemma D equates the
*chains* of `Σ`'s output word (`rowsW`) and the outward procedure's output word (`colsW`);
`thm:G4` reads it as equality of the words.  This file supplies the step between the two:

* `chainOf_inj` — for a word `w₁` with no repeated cell avoiding `κ`, the prefix-set chain
  `chainOf κ w₁` (as a label function `phi`) determines `w₁` among all words.  Pure list lemma.
* `stdFrom_rowsW` — `rowsW` preserves `StdFrom` (extracted from the induction step of
  `SlideIteration.rows_aux'`), so `rowsW p m w` has no repeated cell.
* `rowsW_eq_colsW` — L1: `rowsW p m w = colsW m 0 p w` for every standard `w` of length `m+p`.
* `lesion_chainOf_not_inj` — without `Nodup` the chain does not determine the word:
  `[a,b,a]` and `[a,b,b]` have the same chain (kernel `decide`).
-/
import TworowD4Kernel.SlideIteration
import TworowD4Kernel.StdSlideBridge

namespace TworowD4Kernel.ChainInj

open TworowD4Kernel.SlideSwitch TworowD4Kernel.SlideIteration TworowD4Kernel.LemmaD
open TworowD4Kernel.StdSlideBridge

lemma phi_chainOf_zero (κ : Finset Cell) (w : List Cell) : phi (chainOf κ w) 0 = κ := by
  cases w <;> rfl

lemma phi_chainOf_succ (κ : Finset Cell) (x : Cell) (w : List Cell) (k : ℕ) :
    phi (chainOf κ (x :: w)) (k + 1) = phi (chainOf (insert x κ) w) k := rfl

lemma phi_chainOf_nil_succ (κ : Finset Cell) (k : ℕ) : phi (chainOf κ []) (k + 1) = ∅ := rfl

/-- **The prefix-set chain determines a repetition-free word.** If `w₁` has no repeated cell and
avoids `κ`, then any word `w₂` with the same chain from `κ` equals `w₁`. No hypothesis on `w₂`. -/
theorem chainOf_inj : ∀ (κ : Finset Cell) (w₁ w₂ : List Cell), w₁.Nodup → (∀ y ∈ w₁, y ∉ κ) →
    phi (chainOf κ w₁) = phi (chainOf κ w₂) → w₁ = w₂
  | κ, [], [], _, _, _ => rfl
  | κ, [], y :: w₂, _, _, h => by
    have h1 := congrFun h 1
    rw [phi_chainOf_nil_succ, phi_chainOf_succ, phi_chainOf_zero] at h1
    exact absurd h1.symm (Finset.insert_ne_empty y κ)
  | κ, x :: w₁, [], _, _, h => by
    have h1 := congrFun h 1
    rw [phi_chainOf_nil_succ, phi_chainOf_succ, phi_chainOf_zero] at h1
    exact absurd h1 (Finset.insert_ne_empty x κ)
  | κ, x :: w₁, y :: w₂, hnd, hfr, h => by
    have h1 := congrFun h 1
    rw [phi_chainOf_succ, phi_chainOf_succ, phi_chainOf_zero, phi_chainOf_zero] at h1
    have hx : x ∉ κ := hfr x (List.mem_cons_self ..)
    have hxy : x = y := by
      have : x ∈ insert y κ := h1 ▸ Finset.mem_insert_self x κ
      rcases Finset.mem_insert.1 this with e | e
      · exact e
      · exact absurd e hx
    subst hxy
    have ht : phi (chainOf (insert x κ) w₁) = phi (chainOf (insert x κ) w₂) := by
      funext k; exact congrFun h (k + 1)
    have hnd' := List.nodup_cons.1 hnd
    refine congrArg (x :: ·) (chainOf_inj (insert x κ) w₁ w₂ hnd'.2 ?_ ht)
    intro z hz hzi
    rcases Finset.mem_insert.1 hzi with e | e
    · exact hnd'.1 (e ▸ hz)
    · exact hfr z (List.mem_cons_of_mem _ hz) e

/-- `rowsW` preserves standardness (the `hstd'` step of `rows_aux'`, as a statement). -/
theorem stdFrom_rowsW (D₀ : Finset Cell) (hD₀ : IsDiag D₀) (p : ℕ) (i : ℕ) :
    ∀ (c : ℕ) (w : List Cell), w.length = i + p + c → StdFrom D₀ w →
    StdFrom D₀ (rowsW p i w) := by
  induction i with
  | zero => intro c w _ h; simpa [rowsW] using h
  | succ i ih =>
    intro c w hl hstd
    have hdec := decomp_fwd w i p (by omega)
    set A := w.take i
    set h := w.getD i (0, 0)
    set F := (w.drop (i + 1)).take p
    set B := w.drop (i + 1 + p)
    have hAl : A.length = i := by simp [A]; omega
    have hFl : F.length = p := by simp [F]; omega
    have hBl : B.length = c := by simp [B]; omega
    rw [hdec] at hstd
    obtain ⟨h1, h2⟩ := stdFrom_append A _ D₀ hstd
    have hS := isDiag_union_of_stdFrom A D₀ hD₀ h1
    have h3 := (stdFrom_append (h :: F) B _ (by simpa using h2)).1
    have hsl : slideW h F = carryW h F := slideW_eq_carryW hS h3
    have hstd' : StdFrom D₀ (A ++ (carryW h F ++ B)) :=
      stdFrom_append_of A _ D₀ h1 (stdFrom_carryW B F _ h hS (by simpa using h2))
    have hl' : (A ++ (carryW h F ++ B)).length = i + p + (c + 1) := by
      simp [length_carryW, hAl, hFl, hBl]; omega
    have := ih (c + 1) _ hl' hstd'
    rw [rowsW]
    rw [← hsl] at this
    simpa [List.append_assoc] using this

/-- **L1.** Lemma D (`lemmaD_slides`) equates the chains; `chainOf_inj` upgrades this to
equality of the words, using that `rowsW` keeps the word standard (hence repetition-free). -/
theorem rowsW_eq_colsW (m p : ℕ) (w : List Cell) (hl : w.length = m + p)
    (hstd : StdFrom ∅ w) : rowsW p m w = colsW m 0 p w := by
  have hD := lemmaD_slides m p w hl hstd
  have hr := stdFrom_rowsW ∅ (by simp [IsDiag]) p m 0 w (by omega) hstd
  obtain ⟨hnd, hfr⟩ := stdFrom_nodup ∅ _ hr
  exact chainOf_inj ∅ _ _ hnd hfr hD

/-! ## Lesion: drop `Nodup` -/

/-- Without `Nodup`, the chain does not determine the word: `[a,b,a]` and `[a,b,b]` have the same
prefix sets. Kernel-checked on this instance. -/
theorem lesion_chainOf_not_inj :
    chainOf ∅ [((0 : ℕ), (0 : ℕ)), (0, 1), (0, 0)] = chainOf ∅ [(0, 0), (0, 1), (0, 1)] ∧
    ([((0 : ℕ), (0 : ℕ)), (0, 1), (0, 0)] : List Cell) ≠ [(0, 0), (0, 1), (0, 1)] := by
  decide +kernel

/-- So the `Nodup` hypothesis of `chainOf_inj` cannot be dropped. -/
theorem chainOf_inj_needs_nodup :
    ¬ ∀ (w₁ w₂ : List Cell), phi (chainOf ∅ w₁) = phi (chainOf ∅ w₂) → w₁ = w₂ := fun H =>
  lesion_chainOf_not_inj.2 (H _ _ (congrArg phi lesion_chainOf_not_inj.1))

end TworowD4Kernel.ChainInj
