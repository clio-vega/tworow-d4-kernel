/-
G4 gap G6, step core (LEAN 2026-11-24 c2): the reverse jdt rule `revRule` (= `revChoice`: the
hole takes the larger of south `(r-1,c)` / west `(r,c-1)`, tie → south) preserves the SAME
invariant `FwdInv` as the forward rule (`FwdInv.lean`). The invariant is symmetric under the
180° rotation of the box with values `K - X`, which exchanges `revChoice` and `fwdChoice`
(`#eval`, scratch `proofs/code-1124c2-lean-G4-G6/RevSweep.lean`: the symmetry holds at all 1615
step states of the hokR run on the 310 `phiData33` instances; `FwdInv` holds at all of them;
tie → west breaks it on 47/310 runs). This file proves the mirror directly, with no transport.

Paper: Fulton, *Young Tableaux* §1.2 (reverse slides preserve semistandardness), RECALLED in
the tex `lem:A` proof; no arXiv locator.
-/
import TworowD4Kernel.G5Run

namespace TworowD4Kernel.RevInv

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.SkewColInj
open TworowD4Kernel.FwdInv TworowD4Kernel.G5Run Finset

/-- What `revChoice` returns, for a hole outside the support (so the `ℕ`-subtraction border
"neighbour" `h` itself is never chosen). -/
lemma rev_cases {S : Finset Cell} {X : Cell → ℕ} {r c : ℕ} {y : Cell} (hh : (r, c) ∉ S)
    (hc : revChoice S X (r, c) = some y) :
    (∃ i, r = i + 1 ∧ y = (i, c) ∧ y ∈ S ∧ (∀ w ∈ S, (w.1, w.2 + 1) = (r, c) → X w ≤ X y)) ∨
    (∃ j, c = j + 1 ∧ y = (r, j) ∧ y ∈ S ∧ (∀ s ∈ S, (s.1 + 1, s.2) = (r, c) → X s < X y)) := by
  unfold revChoice nS nW at hc
  simp only at hc
  split_ifs at hc with h1 h2 h3 h3 <;> simp only [Option.some.injEq] at hc <;> subst hc
  · rcases r with _ | i; · exact absurd h1 hh
    refine Or.inl ⟨i, rfl, rfl, h1, ?_⟩
    rintro ⟨a, b⟩ hw e; simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ : a = i + 1 ∧ b = c - 1 := ⟨e.1, by omega⟩
    simpa using h3
  · rcases c with _ | j; · exact absurd h2 hh
    refine Or.inr ⟨j, rfl, rfl, h2, ?_⟩
    rintro ⟨a, b⟩ hs e; simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ : a = r - 1 ∧ b = j + 1 := ⟨by omega, e.2⟩
    simpa using lt_of_not_ge h3
  · rcases r with _ | i; · exact absurd h1 hh
    refine Or.inl ⟨i, rfl, rfl, h1, ?_⟩
    rintro ⟨a, b⟩ hw e; simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ : a = i + 1 ∧ b = c - 1 := ⟨e.1, by omega⟩
    exact absurd hw h2
  · rcases c with _ | j; · exact absurd h3 hh
    refine Or.inr ⟨j, rfl, rfl, h3, ?_⟩
    rintro ⟨a, b⟩ hs e; simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ : a = r - 1 ∧ b = j + 1 := ⟨by omega, e.2⟩
    exact absurd hs h1

/-- **G6 core (Fulton 1.2, reverse).** One reverse move keeps `FwdInv`. -/
theorem rev_step (S : Finset Cell) (X : Cell → ℕ) (h y : Cell) (hi : FwdInv S X h)
    (hc : revChoice S X h = some y) : FwdInv (moveS S h y) (moveX X h y) y := by
  obtain ⟨hh, hsk, ⟨hR, hC⟩, hW, hS⟩ := hi
  obtain ⟨r, c⟩ := h
  have hyS : y ∈ S := revRule.mem S X _ y hc
  have hyh : y ≠ (r, c) := fun e => hh (e ▸ hyS)
  have between : ∀ a ∈ S, ∀ b ∈ S, ∀ z : Cell, a.1 ≤ z.1 → a.2 ≤ z.2 → z.1 ≤ b.1 → z.2 ≤ b.2 →
      z ≠ (r, c) → z ∈ S := by
    intro a ha b hb z h1 h2 h3 h4 hz
    have := hsk a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) z h1 h2 h3 h4
    simpa [hz] using this
  refine ⟨by simp [mem_moveS, hyh], ins_move hyS ▸ hsk, ⟨?_, ?_⟩, ?_, ?_⟩
  all_goals simp only [mem_moveS, moveX_apply]
  · -- rows
    rintro ⟨a, b⟩ ha hb
    rcases rev_cases hh hc with ⟨i, rfl, rfl, -, htie⟩ | ⟨j, rfl, rfl, -, htie⟩
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : a = i + 1 ∧ b = c
      · obtain ⟨rfl, rfl⟩ : a = i + 1 ∧ c = b := ⟨e1.1, e1.2.symm⟩
        rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
        rcases hb with hb | ⟨-, hb⟩; · omega
        have hm := between (i, c) hyS (i + 1, c + 1) hb (i, c + 1) (by simp) (by simp)
          (by simp) (by simp) (by simp)
        have := hR (i, c) hyS hm
        have := hC (i, c + 1) hm hb
        simp only [] at *; omega
      · by_cases e2 : a = i + 1 ∧ b + 1 = c
        · obtain ⟨rfl, rfl⟩ := e2
          rw [if_neg (by omega), if_pos ⟨rfl, rfl⟩]
          rcases ha with ha | ⟨-, ha⟩; · omega
          exact htie (i + 1, b) ha rfl
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hR (a, b) ha hb
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : a = r ∧ b = j + 1
      · obtain ⟨rfl, rfl⟩ := e1
        rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
        rcases hb with hb | ⟨-, hb⟩; · omega
        simpa using hW (a, j) hyS rfl hb
      · by_cases e2 : a = r ∧ b + 1 = j + 1
        · obtain ⟨rfl, e⟩ := e2
          obtain rfl : b = j := by omega
          rcases ha with ⟨-, ha⟩ | ⟨ha, -⟩
          · omega
          · exact absurd rfl ha
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hR (a, b) ha hb
  · -- columns
    rintro ⟨a, b⟩ ha hb
    rcases rev_cases hh hc with ⟨i, rfl, rfl, -, htie⟩ | ⟨j, rfl, rfl, -, htie⟩
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : a = i + 1 ∧ b = c
      · obtain ⟨rfl, rfl⟩ : a = i + 1 ∧ c = b := ⟨e1.1, e1.2.symm⟩
        rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
        rcases hb with hb | ⟨-, hb⟩; · omega
        simpa using hS (i, c) hyS rfl hb
      · by_cases e2 : a + 1 = i + 1 ∧ b = c
        · obtain ⟨e, rfl⟩ := e2
          obtain rfl : a = i := by omega
          rcases ha with ⟨ha, -⟩ | ⟨ha, -⟩
          · omega
          · exact absurd rfl ha
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hC (a, b) ha hb
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : a = r ∧ b = j + 1
      · obtain ⟨rfl, rfl⟩ := e1
        rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
        rcases hb with hb | ⟨-, hb⟩; · omega
        have hm := between (a, j) hyS (a + 1, j + 1) hb (a + 1, j) (by simp) (by simp)
          (by simp) (by simp) (by simp)
        have := hC (a, j) hyS hm
        have := hR (a + 1, j) hm hb
        simp only [] at *; omega
      · by_cases e2 : a + 1 = r ∧ b = j + 1
        · obtain ⟨rfl, rfl⟩ := e2
          rw [if_neg (by omega), if_pos ⟨rfl, rfl⟩]
          rcases ha with ha | ⟨-, ha⟩; · omega
          exact htie (a, j + 1) ha rfl
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hC (a, b) ha hb
  · -- HoleOK at the new hole, west/east clause
    rintro ⟨a, b⟩ ha e hb
    rcases rev_cases hh hc with ⟨i, rfl, rfl, -, -⟩ | ⟨j, rfl, rfl, -, -⟩
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : a = i ∧ b + 1 = c := ⟨e.1, e.2⟩
      rcases ha with ha | ⟨-, ha⟩; · omega
      rcases hb with hb | ⟨-, hb⟩; · omega
      rw [if_neg (by omega), if_neg (by omega)]
      have := hR (a, b) ha hyS
      have := hR (a, b + 1) hyS hb
      simp only [] at *; omega
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : a = r ∧ b + 1 = j := ⟨e.1, e.2⟩
      rcases ha with ha | ⟨-, ha⟩; · omega
      rw [if_neg (by omega), if_pos (by simp)]
      exact hR (a, b) ha hyS
  · -- HoleOK at the new hole, south/north clause
    rintro ⟨a, b⟩ ha e hb
    rcases rev_cases hh hc with ⟨i, rfl, rfl, -, -⟩ | ⟨j, rfl, rfl, -, -⟩
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : a + 1 = i ∧ b = c := ⟨e.1, e.2⟩
      rcases ha with ha | ⟨-, ha⟩; · omega
      rw [if_neg (by omega), if_pos (by simp)]
      exact hC (a, b) ha hyS
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : a + 1 = r ∧ b = j := ⟨e.1, e.2⟩
      rcases ha with ha | ⟨-, ha⟩; · omega
      rcases hb with hb | ⟨-, hb⟩; · omega
      rw [if_neg (by omega), if_neg (by omega)]
      have := hC (a, b) ha hyS
      have := hC (a + 1, b) hyS hb
      simp only [] at *; omega

/-- **G4 (reverse).** From the invariant, the reverse slide succeeds for any fuel. -/
theorem slideOK_rev : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), FwdInv S X h →
    SlideOK revRule k S X h
  | 0, _, _, _, hi => colInj_of_fwdInv hi
  | k + 1, S, X, h, hi => by
    refine ⟨colInj_of_fwdInv hi, ?_⟩
    rcases hc : revRule.ch S X h with _ | y
    · trivial
    · exact slideOK_rev k _ _ y (rev_step S X h y hi hc)

/-- The invariant at every start hole of a run of reverse slides. -/
def StartsOKR (k : ℕ) : Finset Cell → (Cell → ℕ) → List Cell → Prop
  | _, _, [] => True
  | S, X, h :: hs =>
      FwdInv S X h ∧ StartsOKR k (slide revRule k S X h).1 (slide revRule k S X h).2.1 hs

theorem slidesOK_of_startsR (k : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    StartsOKR k S X hs → SlidesOK revRule k S X hs
  | [], _, _, _ => trivial
  | h :: hs, S, X, ⟨hi, hr⟩ => ⟨hi.1, slideOK_rev k S X h hi, slidesOK_of_startsR k hs _ _ hr⟩

/-- The invariant holds at the end of every reverse slide (any fuel). -/
theorem revInv_slide : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), FwdInv S X h →
    FwdInv (slide revRule k S X h).1 (slide revRule k S X h).2.1 (slide revRule k S X h).2.2.1
  | 0, _, _, _, hi => hi
  | k + 1, S, X, h, hi => by
    simp only [slide]
    rcases hc : revRule.ch S X h with _ | y
    · exact hi
    · exact revInv_slide k _ _ y (rev_step S X h y hi hc)

end TworowD4Kernel.RevInv
