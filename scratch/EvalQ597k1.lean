import TworowD4Kernel.Q597G1k1
/-! #eval control for `Q597G1k1` (2026-11-26 c2 LEAN). Data: all KT puzzles of size ≤ 3,
emitted by `projects/scratch/q597_k1_emit.py` (2, 5, 14 — matches the c1 census). -/
namespace Q597G1
open Ori Cls Lbl
def puzzles : List (ℕ × List ((ℤ × ℤ × ℕ) × Lbl)) := [
  (1, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0)]),
  (1, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1)]),
  (2, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0)]),
  (2, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l10), ((0,1,1),l1), ((0,1,2),l0), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1)]),
  (2, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((1,0,0),l0), ((1,0,1),l10), ((1,0,2),l1)]),
  (2, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1)]),
  (2, [((0,0,0),l1), ((0,0,1),l0), ((0,0,2),l10), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0)]),
  (3, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((0,2,0),l0), ((0,2,1),l0), ((0,2,2),l0), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0), ((1,1,0),l0), ((1,1,1),l0), ((1,1,2),l0), ((2,0,0),l0), ((2,0,1),l0), ((2,0,2),l0)]),
  (3, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((0,2,0),l10), ((0,2,1),l1), ((0,2,2),l0), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0), ((1,1,0),l10), ((1,1,1),l1), ((1,1,2),l0), ((2,0,0),l1), ((2,0,1),l1), ((2,0,2),l1)]),
  (3, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((0,2,0),l10), ((0,2,1),l1), ((0,2,2),l0), ((1,0,0),l1), ((1,0,1),l0), ((1,0,2),l10), ((1,1,0),l1), ((1,1,1),l1), ((1,1,2),l1), ((2,0,0),l0), ((2,0,1),l0), ((2,0,2),l0)]),
  (3, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l10), ((0,1,1),l1), ((0,1,2),l0), ((0,2,0),l0), ((0,2,1),l0), ((0,2,2),l0), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1), ((1,1,0),l0), ((1,1,1),l0), ((1,1,2),l0), ((2,0,0),l0), ((2,0,1),l10), ((2,0,2),l1)]),
  (3, [((0,0,0),l0), ((0,0,1),l0), ((0,0,2),l0), ((0,1,0),l10), ((0,1,1),l1), ((0,1,2),l0), ((0,2,0),l10), ((0,2,1),l1), ((0,2,2),l0), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1), ((1,1,0),l1), ((1,1,1),l1), ((1,1,2),l1), ((2,0,0),l1), ((2,0,1),l1), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((0,2,0),l0), ((0,2,1),l0), ((0,2,2),l0), ((1,0,0),l0), ((1,0,1),l10), ((1,0,2),l1), ((1,1,0),l0), ((1,1,1),l0), ((1,1,2),l0), ((2,0,0),l0), ((2,0,1),l10), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l0), ((0,1,1),l0), ((0,1,2),l0), ((0,2,0),l10), ((0,2,1),l1), ((0,2,2),l0), ((1,0,0),l0), ((1,0,1),l10), ((1,0,2),l1), ((1,1,0),l1), ((1,1,1),l1), ((1,1,2),l1), ((2,0,0),l1), ((2,0,1),l1), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((0,2,0),l0), ((0,2,1),l0), ((0,2,2),l0), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1), ((1,1,0),l0), ((1,1,1),l10), ((1,1,2),l1), ((2,0,0),l0), ((2,0,1),l10), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((0,2,0),l1), ((0,2,1),l1), ((0,2,2),l1), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1), ((1,1,0),l1), ((1,1,1),l1), ((1,1,2),l1), ((2,0,0),l1), ((2,0,1),l1), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l1), ((0,0,2),l1), ((0,1,0),l1), ((0,1,1),l0), ((0,1,2),l10), ((0,2,0),l1), ((0,2,1),l1), ((0,2,2),l1), ((1,0,0),l1), ((1,0,1),l1), ((1,0,2),l1), ((1,1,0),l0), ((1,1,1),l0), ((1,1,2),l0), ((2,0,0),l0), ((2,0,1),l10), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l0), ((0,0,2),l10), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((0,2,0),l0), ((0,2,1),l0), ((0,2,2),l0), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0), ((1,1,0),l0), ((1,1,1),l10), ((1,1,2),l1), ((2,0,0),l0), ((2,0,1),l0), ((2,0,2),l0)]),
  (3, [((0,0,0),l1), ((0,0,1),l0), ((0,0,2),l10), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((0,2,0),l1), ((0,2,1),l1), ((0,2,2),l1), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0), ((1,1,0),l10), ((1,1,1),l1), ((1,1,2),l0), ((2,0,0),l1), ((2,0,1),l1), ((2,0,2),l1)]),
  (3, [((0,0,0),l1), ((0,0,1),l0), ((0,0,2),l10), ((0,1,0),l1), ((0,1,1),l1), ((0,1,2),l1), ((0,2,0),l1), ((0,2,1),l1), ((0,2,2),l1), ((1,0,0),l1), ((1,0,1),l0), ((1,0,2),l10), ((1,1,0),l1), ((1,1,1),l1), ((1,1,2),l1), ((2,0,0),l0), ((2,0,1),l0), ((2,0,2),l0)]),
  (3, [((0,0,0),l1), ((0,0,1),l0), ((0,0,2),l10), ((0,1,0),l1), ((0,1,1),l0), ((0,1,2),l10), ((0,2,0),l1), ((0,2,1),l1), ((0,2,2),l1), ((1,0,0),l0), ((1,0,1),l0), ((1,0,2),l0), ((1,1,0),l0), ((1,1,1),l0), ((1,1,2),l0), ((2,0,0),l0), ((2,0,1),l0), ((2,0,2),l0)])
]

def clsIdx : Cls → ℕ | c0 => 0 | c1 => 1 | c2 => 2

def labOf (L : List ((ℤ × ℤ × ℕ) × Lbl)) (e : Edge) : Lbl :=
  ((L.find? fun p => p.1 = (e.a, e.b, clsIdx e.k)).map Prod.snd).getD l10

/-- Independent coding of the tex's Λ₁-cochain (Lemma D, §2): a `1`-edge gets its vector, a
`0`-edge `0`, a `10`-edge in ccw orientation gets `-d₁` (the ccw vector of the triangle's
`1`-edge). `ccw` lists (edge, sign of ref vs ccw orientation). -/
def texC1 (lab : Edge → Lbl) (ccw : List (Edge × ℤ)) (e : Edge) : Option V :=
  match lab e with
  | l1 => some e.vec
  | l0 => some 0
  | l10 =>
    let se := ((ccw.find? fun p => p.1 = e).map Prod.snd).getD 0
    match ccw.find? fun p => lab p.1 = l1 with
    | some (e1, s1) => some (se • (-(s1 • e1.vec)))
    | none => none

def upCcw (a b : ℤ) : List (Edge × ℤ) := [(⟨a, b, c0⟩, 1), (⟨a, b, c2⟩, 1), (⟨a, b, c1⟩, -1)]
def dnCcw (a b : ℤ) : List (Edge × ℤ) :=
  [(⟨a + 1, b, c1⟩, 1), (⟨a, b + 1, c0⟩, -1), (⟨a, b, c2⟩, -1)]

def edgesT (n : ℕ) : List Edge :=
  (List.range n).flatMap fun a => (List.range (n - a)).flatMap fun b =>
    [⟨a, b, c0⟩, ⟨a, b, c1⟩, ⟨a, b, c2⟩]
def upsT (n : ℕ) : List Tri :=
  (List.range n).flatMap fun a => (List.range (n - a)).map fun b => ⟨a, b, up⟩
def dnsT (n : ℕ) : List Tri :=
  (List.range n).flatMap fun a => (List.range (n - a - 1)).map fun b => ⟨a, b, down⟩

def check (n : ℕ) (L : List ((ℤ × ℤ × ℕ) × Lbl)) : Bool :=
  let lab := labOf L
  let f := integ (coch (swapLab lab))
  -- (1) f₁ differences = tex Λ₁ cochain, read from the up-triangle and (interior) down-triangle
  let c1 := (edgesT n).all fun e => some (f e.head - f e.tail) = texC1 lab (upCcw e.a e.b) e
  let c2 := (dnsT n).all fun t => (dnCcw t.a t.b).all fun (e, _) =>
    some (f e.head - f e.tail) = texC1 lab (dnCcw t.a t.b) e
  -- (2) LiftOK1 on every edge
  let c3 := (edgesT n).all fun e =>
    (lab e != l1 || f e.head == f e.tail + e.vec) && (lab e != l0 || f e.head == f e.tail)
  -- (3) m = number of 1s on the bottom side
  let d := f ((n : ℤ), 0) - f (0, 0)
  let m : ℤ := ((List.range n).filter fun i => lab ⟨i, 0, c0⟩ = l1).length
  let c4 := d = (m, 0)
  -- (4) N₁ = [Δ₁] on a box around f(0,0)
  let tris := (upsT n ++ dnsT n).filter fun t => decide (Is111 lab t)
  let p := f (0, 0)
  let box := (List.range (2 * n + 5)).flatMap fun i => (List.range (2 * n + 5)).flatMap fun j =>
    [(⟨p.1 + i - n - 2, p.2 + j - n - 2, up⟩ : Tri), ⟨p.1 + i - n - 2, p.2 + j - n - 2, down⟩]
  let c5 := box.all fun t =>
    ((tris.filter fun τ => imgTri f τ = t).length = if inDelta p m.toNat t then 1 else 0)
  -- (5) k = 1 on ℓ = k = 0 on swap ℓ (the 111-triangles of ℓ are the 000-triangles of swap ℓ)
  let c6 := (upsT n ++ dnsT n).all fun t =>
    decide (Is111 lab t) = decide (Is000 (swapLab lab) t)
  c1 && c2 && c3 && c4 && c5 && c6 && tris.length = m.toNat ^ 2

#eval (puzzles.map fun (n, L) => check n L)
#eval (puzzles.filter fun (n, L) => check n L).length

/-! Lesion: the *unswapped* KT cochain `coch ℓ` is not a k = 1 lift (`LiftOK1` fails) on
puzzles with both letters — so the swap, not the KT cochain, is what builds `f₁`. -/
def lesion (n : ℕ) (L : List ((ℤ × ℤ × ℕ) × Lbl)) : Bool :=
  let lab := labOf L
  let f := integ (coch lab)
  (edgesT n).all fun e =>
    (lab e != l1 || f e.head == f e.tail + e.vec) && (lab e != l0 || f e.head == f e.tail)
#eval (puzzles.filter fun (n, L) => lesion n L).length

/-! Instrument control: the same box comparison against `Δ(f(0,0), m+1)` must fail. -/
def boxCheckShift (n : ℕ) (L : List ((ℤ × ℤ × ℕ) × Lbl)) : Bool :=
  let lab := labOf L
  let f := integ (coch (swapLab lab))
  let m : ℕ := ((List.range n).filter fun i => lab ⟨i, 0, c0⟩ = l1).length
  let tris := (upsT n ++ dnsT n).filter fun t => decide (Is111 lab t)
  let p := f (0, 0)
  let box := (List.range (2 * n + 5)).flatMap fun i => (List.range (2 * n + 5)).flatMap fun j =>
    [(⟨p.1 + i - n - 2, p.2 + j - n - 2, up⟩ : Tri), ⟨p.1 + i - n - 2, p.2 + j - n - 2, down⟩]
  box.all fun t =>
    ((tris.filter fun τ => imgTri f τ = t).length = if inDelta p (m + 1) t then 1 else 0)
#eval (puzzles.filter fun (n, L) => boxCheckShift n L).length
end Q597G1
