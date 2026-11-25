import TworowD4Kernel.Q597G1Lift
/-! #eval controls for `Q597G1Lift` (not in the library build). Computable mirror:
labellings as association lists, lift by propagation along 0/1-edges, `N₀` by counting. -/
open Q597G1 Q597G1.Lbl Q597G1.Ori Q597G1.Cls

deriving instance BEq for Edge
deriving instance BEq for Lbl

def trisOf (n : ℕ) : List Tri :=
  ((List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    (if a + b + 1 ≤ n then [⟨a, b, up⟩] else []) ++ (if a + b + 2 ≤ n then [⟨a, b, down⟩] else []))

def edgesOf (n : ℕ) : List Edge := ((trisOf n).flatMap triEdges).eraseDups

def isBdry (n : ℕ) (e : Edge) : Bool :=
  (e.k == c0 && e.b == 0) || (e.k == c1 && e.a == 0) || (e.k == c2 && e.a + e.b + 1 == n)

/-- counterclockwise labels of a triangle -/
def ccw (lab : Edge → Lbl) (t : Tri) : List Lbl :=
  match t.o with
  | up => [lab ⟨t.a, t.b, c0⟩, lab ⟨t.a, t.b, c2⟩, lab ⟨t.a, t.b, c1⟩]
  | down => [lab ⟨t.a + 1, t.b, c1⟩, lab ⟨t.a, t.b + 1, c0⟩, lab ⟨t.a, t.b, c2⟩]

def rots (l : List Lbl) : List (List Lbl) := [l, l.rotate 1, l.rotate 2]
/-- KT pieces (tex chirality: ccw `10,0,1`); `mirror` also admits ccw `10,1,0`. -/
def pieceOK (mirror : Bool) (l : List Lbl) : Bool :=
  l == [l0, l0, l0] || l == [l1, l1, l1] || (rots [l10, l0, l1]).contains l ||
    (mirror && (rots [l10, l1, l0]).contains l)

def look (as : List (Edge × Lbl)) (e : Edge) : Lbl := (as.lookup e).getD l10

/-- enumerate labellings, pruning on completed triangles. `bd10`: allow `10` on the boundary. -/
partial def enum (n : ℕ) (mirror bd10 : Bool) : List (List (Edge × Lbl)) :=
  let es := edgesOf n
  let ts := trisOf n
  let rec go (rest : List Edge) (as : List (Edge × Lbl)) : List (List (Edge × Lbl)) :=
    match rest with
    | [] => [as]
    | e :: rest' =>
      ([l0, l1, l10].filter fun l => bd10 || !(isBdry n e && l == l10)).flatMap fun l =>
        let as' := (e, l) :: as
        let ok := ts.all fun t => !((triEdges t).all fun e' => (as'.lookup e').isSome) ||
          pieceOK mirror (ccw (look as') t)
        if ok then go rest' as' else []
  go es []

def verts (n : ℕ) : List V := ((edgesOf n).flatMap fun e => [e.tail, e.head]).eraseDups

/-- the lift by propagation along 0/1 edges from `(0,0) ↦ (0,0)`; `none` if inconsistent. -/
def lift (n : ℕ) (as : List (Edge × Lbl)) : Option (V → V) := Id.run do
  let es := edgesOf n
  let mut F : List (V × V) := [((0, 0), (0, 0))]
  for _ in verts n do
    for e in es do
      match look as e, F.lookup e.tail, F.lookup e.head with
      | l0, some x, none => F := (e.head, x + e.vec) :: F
      | l0, none, some y => F := (e.tail, y - e.vec) :: F
      | l1, some x, none => F := (e.head, x) :: F
      | l1, none, some y => F := (e.tail, y) :: F
      | _, _, _ => pure ()
  let f : V → V := fun v => (F.lookup v).getD (1000, 1000)
  let ok := es.all fun e => match look as e with
    | l0 => f e.head == f e.tail + e.vec
    | l1 => f e.head == f e.tail
    | l10 => true
  return if ok && (verts n).all (fun v => (F.lookup v).isSome) then some f else none

/-- `N₀ = [Δ₀]` checked on a box of target triangles. -/
def g1holds (n : ℕ) (as : List (Edge × Lbl)) (f : V → V) : Bool :=
  let p := f (0, 0)
  let d := f ((n : ℤ), 0) - p
  let m := d.1.toNat
  let box : List Tri := ((List.range (4 * n + 4)).flatMap fun i => (List.range (4 * n + 4)).flatMap
    fun j => [⟨p.1 + i - 2 * n - 2, p.2 + j - 2 * n - 2, up⟩, ⟨p.1 + i - 2 * n - 2, p.2 + j - 2 * n - 2, down⟩])
  let lab := look as
  d.2 == 0 && 0 ≤ d.1 && box.all fun t =>
    ((trisOf n).filter fun τ => decide (Is000 lab τ) && imgTri f τ == t).length ==
      (if inDelta p m t then 1 else 0)

/-- (#puzzles, #with lift, #G1 holds) -/
def census (n : ℕ) (mirror bd10 : Bool) : ℕ × ℕ × ℕ :=
  let ps := enum n mirror bd10
  let ls := ps.filterMap fun as => (lift n as).map fun f => (as, f)
  (ps.length, ls.length, (ls.filter fun (as, f) => g1holds n as f).length)

#eval [1, 2, 3].map fun n => census n false false   -- KT puzzles
#eval [1, 2, 3].map fun n => census n true false    -- lesion: mirror pieces allowed
#eval [1, 2, 3].map fun n => census n false true    -- lesion: 10 allowed on the boundary
