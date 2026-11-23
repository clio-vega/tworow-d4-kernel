/-
G4 gaps G1 + G2 (LEAN 2026-11-23 c2): Fulton's "semistandard with a hole" invariant for the
forward jdt rule `fwdRule` (= `fwdChoice`: hole takes the smaller of north `(r+1,c)` / east
`(r,c+1)`, tie → north), and one move preserves it.

Paper: Fulton, *Young Tableaux* §1.2 (jdt slides preserve semistandardness), RECALLED in the tex
`lem:A` proof; no arXiv locator. The invariant below is read off `fwdChoice` (StdSlide.lean:91),
not Fulton's prose. Coordinates are French: north = row + 1.

`#eval` control (scratch `proofs/code-1123c2-lean-G4-fulton/FwdInvSweep.lean`): FwdInv holds at
all 1569 step states of the hokF run on the 310 `phiData33` instances; with the tie sent EAST it
fails on 87/310 runs.
-/
import TworowD4Kernel.SkewColInj

namespace TworowD4Kernel.FwdInv

open TworowD4Kernel.SlideSwitch TworowD4Kernel.StdSlide TworowD4Kernel.SkewColInj Finset

/-- Across the hole `h`: west ≤ east (row weak), south < north (column strict). The two
diagonal inequalities are NOT included: they follow from `Skew (insert h S)` + `SSOn S X`. -/
def HoleOK (S : Finset Cell) (X : Cell → ℕ) (h : Cell) : Prop :=
  (∀ w ∈ S, (w.1, w.2 + 1) = h → (h.1, h.2 + 1) ∈ S → X w ≤ X (h.1, h.2 + 1)) ∧
  (∀ s ∈ S, (s.1 + 1, s.2) = h → (h.1 + 1, h.2) ∈ S → X s < X (h.1 + 1, h.2))

/-- The forward-slide invariant. -/
def FwdInv (S : Finset Cell) (X : Cell → ℕ) (h : Cell) : Prop :=
  h ∉ S ∧ Skew (insert h S) ∧ SSOn S X ∧ HoleOK S X h

lemma mem_moveS {S : Finset Cell} {h y a : Cell} :
    a ∈ moveS S h y ↔ a = h ∨ (a ≠ y ∧ a ∈ S) := by
  simp [moveS, and_comm]

lemma moveX_apply {X : Cell → ℕ} {h y a : Cell} :
    moveX X h y a = if a = h then X y else X a := by
  unfold moveX Function.update; split_ifs with e <;> simp_all

/-- What `fwdChoice` returns. -/
lemma fwd_cases {S : Finset Cell} {X : Cell → ℕ} {h y : Cell}
    (hc : fwdChoice S X h = some y) :
    (y = (h.1 + 1, h.2) ∧ y ∈ S ∧ ((h.1, h.2 + 1) ∈ S → X y ≤ X (h.1, h.2 + 1))) ∨
    (y = (h.1, h.2 + 1) ∧ y ∈ S ∧ ((h.1 + 1, h.2) ∈ S → X y < X (h.1 + 1, h.2))) := by
  unfold fwdChoice nN nE at hc
  split_ifs at hc with h1 h2 h3 h3 <;> simp only [Option.some.injEq] at hc <;> subst hc
  · exact Or.inl ⟨rfl, h1, fun _ => h3⟩
  · exact Or.inr ⟨rfl, h2, fun _ => lt_of_not_ge h3⟩
  · exact Or.inl ⟨rfl, h1, fun e => absurd e h2⟩
  · exact Or.inr ⟨rfl, h3, fun e => absurd e h1⟩

/-- **G2 (Fulton 1.2 core, forward).** One move keeps the invariant. -/
theorem fwd_step (S : Finset Cell) (X : Cell → ℕ) (h y : Cell) (hi : FwdInv S X h)
    (hc : fwdChoice S X h = some y) : FwdInv (moveS S h y) (moveX X h y) y := by
  obtain ⟨hh, hsk, ⟨hR, hC⟩, hW, hS⟩ := hi
  obtain ⟨r, c⟩ := h
  have hyS : y ∈ S := by rcases fwd_cases hc with ⟨_, h, _⟩ | ⟨_, h, _⟩ <;> exact h
  have hyh : y ≠ (r, c) := fun e => hh (e ▸ hyS)
  -- convexity, specialised: a cell between two cells of S, other than the hole, is in S
  have between : ∀ a ∈ S, ∀ b ∈ S, ∀ z : Cell, a.1 ≤ z.1 → a.2 ≤ z.2 → z.1 ≤ b.1 → z.2 ≤ b.2 →
      z ≠ (r, c) → z ∈ S := by
    intro a ha b hb z h1 h2 h3 h4 hz
    have := hsk a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) z h1 h2 h3 h4
    simpa [hz] using this
  have hins : insert y (moveS S (r, c) y) = insert (r, c) S := by
    ext a; simp only [mem_insert, mem_moveS]; by_cases e : a = y <;> simp_all
  refine ⟨by simp [mem_moveS, hyh], hins ▸ hsk, ⟨?_, ?_⟩, ?_, ?_⟩
  all_goals simp only [mem_moveS, moveX_apply]
  · -- rows
    rintro ⟨i, j⟩ ha hb
    rcases fwd_cases hc with ⟨rfl, -, htie⟩ | ⟨rfl, -, htie⟩
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : i = r ∧ j = c
      · obtain ⟨rfl, rfl⟩ := e1
        rcases hb with hb | ⟨-, hb⟩; · omega
        simpa using htie hb
      · by_cases e2 : i = r ∧ j + 1 = c
        · obtain ⟨rfl, rfl⟩ := e2
          rcases ha with ha | ⟨-, ha⟩; · omega
          rw [if_neg (by simp)]
          have hm := between (i, j) ha (i + 1, j + 1) hyS (i + 1, j) (by simp) (by simp)
            (by simp) (by simp) (by simp)
          have := hC (i, j) ha hm
          have := hR (i + 1, j) hm hyS
          rw [if_pos ⟨rfl, rfl⟩]; simp only [] at *; omega
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hR (i, j) ha hb
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : i = r ∧ j = c
      · obtain ⟨rfl, rfl⟩ := e1
        rcases hb with hb | ⟨hb, -⟩ <;> simp_all
      · by_cases e2 : i = r ∧ j + 1 = c
        · obtain ⟨rfl, rfl⟩ := e2
          rcases ha with ha | ⟨-, ha⟩; · omega
          rw [if_neg (by simp)]
          simpa using hW (i, j) ha rfl hyS
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hR (i, j) ha hb
  · -- columns
    rintro ⟨i, j⟩ ha hb
    rcases fwd_cases hc with ⟨rfl, -, htie⟩ | ⟨rfl, -, htie⟩
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : i = r ∧ j = c
      · obtain ⟨rfl, rfl⟩ := e1
        rcases hb with hb | ⟨hb, -⟩ <;> simp_all
      · by_cases e2 : i + 1 = r ∧ j = c
        · obtain ⟨rfl, rfl⟩ := e2
          rcases ha with ha | ⟨-, ha⟩; · omega
          rw [if_neg (by simp)]
          simpa using hS (i, j) ha rfl hyS
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hC (i, j) ha hb
    · simp only [Prod.mk.injEq] at ha hb ⊢
      by_cases e1 : i = r ∧ j = c
      · obtain ⟨rfl, rfl⟩ := e1
        rcases hb with hb | ⟨-, hb⟩; · omega
        simpa using htie hb
      · by_cases e2 : i + 1 = r ∧ j = c
        · obtain ⟨rfl, rfl⟩ := e2
          rcases ha with ha | ⟨-, ha⟩; · omega
          rw [if_neg (by simp)]
          have hm := between (i, j) ha (i + 1, j + 1) hyS (i, j + 1) (by simp) (by simp)
            (by simp) (by simp) (by simp)
          have := hR (i, j) ha hm
          have := hC (i, j + 1) hm hyS
          rw [if_pos ⟨rfl, rfl⟩]; simp only [] at *; omega
        · rw [if_neg e1, if_neg (by omega)]
          rcases ha with ha | ⟨-, ha⟩; · omega
          rcases hb with hb | ⟨-, hb⟩; · omega
          exact hC (i, j) ha hb
  · -- HoleOK at the new hole, west/east clause
    rintro ⟨i, j⟩ ha e hb
    rcases fwd_cases hc with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : i = r + 1 ∧ j + 1 = c := ⟨e.1, e.2⟩
      rcases ha with ha | ⟨-, ha⟩; · omega
      rcases hb with hb | ⟨-, hb⟩; · omega
      rw [if_neg (by omega), if_neg (by omega)]
      have := hR (r + 1, j) ha hyS
      have := hR (r + 1, j + 1) hyS hb
      simp only [] at *; omega
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : i = r ∧ j = c := ⟨e.1, by omega⟩
      rcases hb with hb | ⟨-, hb⟩; · omega
      rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
      exact hR (i, j + 1) hyS hb
  · -- HoleOK at the new hole, south/north clause
    rintro ⟨i, j⟩ ha e hb
    rcases fwd_cases hc with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : i = r ∧ j = c := ⟨by omega, e.2⟩
      rcases hb with hb | ⟨-, hb⟩; · omega
      rw [if_pos ⟨rfl, rfl⟩, if_neg (by omega)]
      exact hC (i + 1, j) hyS hb
    · simp only [Prod.mk.injEq] at ha hb e ⊢
      obtain ⟨rfl, rfl⟩ : i + 1 = r ∧ j = c + 1 := ⟨e.1, e.2⟩
      rcases ha with ha | ⟨-, ha⟩; · omega
      rcases hb with hb | ⟨-, hb⟩; · omega
      rw [if_neg (by omega), if_neg (by omega)]
      have := hC (i, c + 1) ha hyS
      have := hC (i + 1, c + 1) hyS hb
      simp only [] at *; omega

/-- Column-injectivity under the invariant. `S` itself need not be convex (the hole is a gap),
so G3 does not apply directly: the jump across the hole is the south/north clause of `HoleOK`. -/
theorem colInj_of_fwdInv {S : Finset Cell} {X : Cell → ℕ} {h : Cell} (hi : FwdInv S X h) :
    ColInj S X := by
  obtain ⟨hh, hsk, ⟨-, hC⟩, -, hS⟩ := hi
  have inT : ∀ a ∈ S, ∀ b ∈ S, ∀ z : Cell, a.1 ≤ z.1 → a.2 ≤ z.2 → z.1 ≤ b.1 → z.2 ≤ b.2 →
      z = h ∨ z ∈ S := by
    intro a ha b hb z h1 h2 h3 h4
    simpa using hsk a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) z h1 h2 h3 h4
  have P : ∀ d, ∀ a ∈ S, (a.1 + (d + 1), a.2) ∈ S → X a < X (a.1 + (d + 1), a.2) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro a ha hb
      rcases inT a ha _ hb (a.1 + 1, a.2) (by simp) le_rfl (by simp) le_rfl with hm | hm
      · -- the cell above `a` is the hole: jump across it
        rcases d with _ | d
        · exact absurd (hm ▸ hb) hh
        have hn : (a.1 + 2, a.2) ∈ S := by
          rcases inT a ha _ hb (a.1 + 2, a.2) (by simp) le_rfl (by simp) le_rfl with e | e
          · rw [← hm] at e; simp at e
          · exact e
        have h1 : X a < X (a.1 + 2, a.2) := by
          have := hS a ha hm (by rw [← hm]; exact hn); rwa [← hm] at this
        rcases d with _ | d
        · simpa using h1
        have e : ((a.1 + 2, a.2).1 + (d + 1), (a.1 + 2, a.2).2) = (a.1 + (d + 1 + 1 + 1), a.2) := by
          exact Prod.ext (by dsimp only; omega) rfl
        have := ih d (by omega) (a.1 + 2, a.2) hn (by rw [e]; exact hb)
        rw [e] at this; omega
      · have h1 := hC a ha hm
        rcases d with _ | d
        · simpa using h1
        have e : ((a.1 + 1, a.2).1 + (d + 1), (a.1 + 1, a.2).2) = (a.1 + (d + 1 + 1), a.2) := by
          exact Prod.ext (by dsimp only; omega) rfl
        have := ih d (by omega) (a.1 + 1, a.2) hm (by rw [e]; exact hb)
        rw [e] at this; omega
  have key : ∀ a ∈ S, ∀ b ∈ S, a.2 = b.2 → a.1 < b.1 → X a < X b := by
    intro a ha b hb hc hlt
    obtain ⟨d, hd⟩ : ∃ d, b.1 = a.1 + (d + 1) := ⟨b.1 - a.1 - 1, by omega⟩
    have hbeq : b = (a.1 + (d + 1), a.2) := Prod.ext hd hc.symm
    subst hbeq
    exact P d a ha hb
  intro a ha b hb hc hv
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact absurd hv (key a ha b hb hc h).ne
  · exact Prod.ext h hc
  · exact absurd hv (key b hb a ha hc.symm h).ne'

/-- **G4 (forward).** From the invariant, the slide succeeds for any fuel: every filling met
is column-injective. -/
theorem slideOK_fwd : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), FwdInv S X h →
    SlideOK fwdRule k S X h
  | 0, _, _, _, hi => colInj_of_fwdInv hi
  | k + 1, S, X, h, hi => by
    refine ⟨colInj_of_fwdInv hi, ?_⟩
    rcases hc : fwdRule.ch S X h with _ | y
    · trivial
    · exact slideOK_fwd k _ _ y (fwd_step S X h y hi hc)

/-- The invariant at every start hole of a run of forward slides (fuel `k` each). -/
def StartsOK (k : ℕ) : Finset Cell → (Cell → ℕ) → List Cell → Prop
  | _, _, [] => True
  | S, X, h :: hs =>
      FwdInv S X h ∧ StartsOK k (slide fwdRule k S X h).1 (slide fwdRule k S X h).2.1 hs

/-- **G4, iterated.** `SlidesOK` for the forward rule reduces to the invariant at each START
hole; inside a slide, `fwd_step` carries it. This is what `hokF` now needs (gap G5). -/
theorem slidesOK_of_starts (k : ℕ) : ∀ (hs : List Cell) (S : Finset Cell) (X : Cell → ℕ),
    StartsOK k S X hs → SlidesOK fwdRule k S X hs
  | [], _, _, _ => trivial
  | h :: hs, S, X, ⟨hi, hr⟩ => ⟨hi.1, slideOK_fwd k S X h hi, slidesOK_of_starts k hs _ _ hr⟩

/-- The invariant holds at the end of every slide (any fuel). -/
theorem fwdInv_slide : ∀ (k : ℕ) (S : Finset Cell) (X : Cell → ℕ) (h : Cell), FwdInv S X h →
    FwdInv (slide fwdRule k S X h).1 (slide fwdRule k S X h).2.1 (slide fwdRule k S X h).2.2.1
  | 0, _, _, _, hi => hi
  | k + 1, S, X, h, hi => by
    simp only [slide]
    rcases hc : fwdRule.ch S X h with _ | y
    · exact hi
    · exact fwdInv_slide k _ _ y (fwd_step S X h y hi hc)

/-- When the slide stops (no north/east neighbour), the hole is a maximal cell of the convex
`insert h S`, so the final support is convex and semistandard: a skew SSYT again. -/
theorem fwd_end {S : Finset Cell} {X : Cell → ℕ} {h : Cell} (hi : FwdInv S X h)
    (hc : fwdChoice S X h = none) : Skew S ∧ SSOn S X := by
  obtain ⟨hh, hsk, hss, -⟩ := hi
  have hN : (h.1 + 1, h.2) ∉ S := by
    intro e; unfold fwdChoice nN nE at hc; split_ifs at hc
  have hE : (h.1, h.2 + 1) ∉ S := by
    intro e; unfold fwdChoice nN nE at hc; split_ifs at hc
  refine ⟨fun a ha b hb z h1 h2 h3 h4 => ?_, hss⟩
  have hz := hsk a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) z h1 h2 h3 h4
  rcases mem_insert.1 hz with rfl | hz
  · -- `z = h ≤ b`, `b ≠ h`: a north or east neighbour of `h` lies between `h` and `b`
    exfalso
    have hbh : b ≠ z := fun e => hh (e ▸ hb)
    by_cases e1 : z.1 < b.1
    · have := hsk z (mem_insert_self _ _) b (mem_insert_of_mem hb) (z.1 + 1, z.2)
        (by simp) le_rfl (by simpa using e1) h4
      rcases mem_insert.1 this with e | e
      · simp [Prod.ext_iff] at e
      · exact hN e
    · have e2 : z.2 < b.2 := by
        by_contra e2; exact hbh (Prod.ext (by omega) (by omega))
      have := hsk z (mem_insert_self _ _) b (mem_insert_of_mem hb) (z.1, z.2 + 1)
        le_rfl (by simp) h3 (by simpa using e2)
      rcases mem_insert.1 this with e | e
      · simp [Prod.ext_iff] at e
      · exact hN.elim (absurd e hE)
  · exact hz

/-! ## Lesion: the tie-break is load-bearing

Hole `(0,0)`, north `(1,0)` and east `(0,1)` both `1` (a tie). `fwdRule` takes north; moving
EAST instead (the tie → east rule) leaves `1` under `1` in column 0, so `SSOn` fails. The
`#eval` sweep: tie → east breaks `FwdInv` on 87/310 `phiData33` runs. -/

theorem lesion_tie_east :
    SSOn {(1, 0), (0, 1)} (fun _ => 1) ∧
    fwdChoice ({(1, 0), (0, 1)} : Finset Cell) (fun _ => 1) (0, 0) = some (1, 0) ∧
    SSOn (moveS {(1, 0), (0, 1)} (0, 0) (1, 0)) (moveX (fun _ => 1) (0, 0) (1, 0)) ∧
    ¬ SSOn (moveS {(1, 0), (0, 1)} (0, 0) (0, 1)) (moveX (fun _ => 1) (0, 0) (0, 1)) := by
  decide

end TworowD4Kernel.FwdInv
