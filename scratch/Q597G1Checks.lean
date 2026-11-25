import TworowD4Kernel.Q597G1

open Q597G1 Ori Cls

set_option linter.hashCommand false

/-- Indicator chain on a finite list of triangles (computable, for `#eval`). -/
def ind (L : List Tri) : Tri → ℤ := fun t => if t ∈ L then 1 else 0

/-- Edges in a window with nonzero boundary value. -/
def nz (c : Tri → ℤ) (r : ℤ) : List (Edge × ℤ) := Id.run do
  let mut out := []
  for a in List.range (2 * r.toNat + 1) do
    for b in List.range (2 * r.toNat + 1) do
      for k in [c0, c1, c2] do
        let e : Edge := ⟨(a : ℤ) - r, (b : ℤ) - r, k⟩
        if bdryFun c e ≠ 0 then out := out ++ [(e, bdryFun c e)]
  return out

-- one up-triangle: exactly its 3 edges, signs +,+,-
#eval nz (ind [⟨0, 0, up⟩]) 3
-- one down-triangle
#eval nz (ind [⟨0, 0, down⟩]) 3
-- size-2 triangle T_2 = 3 up + 1 down: 6 outer edges, the 3 inner ones cancel
#eval nz (ind [⟨0, 0, up⟩, ⟨1, 0, up⟩, ⟨0, 1, up⟩, ⟨0, 0, down⟩]) 3
#guard (nz (ind [⟨0, 0, up⟩, ⟨1, 0, up⟩, ⟨0, 1, up⟩, ⟨0, 0, down⟩]) 3).length = 6
-- the inDelta indicator for p=(0,0), m=2 is the same chain
#guard (nz (fun t => if inDelta (0, 0) 2 t then 1 else 0) 3).length = 6
#guard (List.range 9).all fun i => (List.range 9).all fun j =>
  [up, down].all fun o =>
    let t : Tri := ⟨(i : ℤ) - 4, (j : ℤ) - 4, o⟩
    (if inDelta (0, 0) 2 t then (1 : ℤ) else 0) ==
      ind [⟨0, 0, up⟩, ⟨1, 0, up⟩, ⟨0, 1, up⟩, ⟨0, 0, down⟩] t
-- the incidence formula vs the two-term formula, on a window
#guard (List.range 5).all fun i => (List.range 5).all fun j =>
  [up, down].all fun o => [c0, c1, c2].all fun k =>
  (List.range 5).all fun i' => (List.range 5).all fun j' =>
    let t : Tri := ⟨(i : ℤ) - 2, (j : ℤ) - 2, o⟩
    let e : Edge := ⟨(i' : ℤ) - 2, (j' : ℤ) - 2, k⟩
    inc t e == bdryFun (fun s => if s = t then 1 else 0) e

theorem sorry_control : (0 : ℤ) = 1 := sorry

#print axioms Q597G1.inc_eq
#print axioms Q597G1.bdry_eq_bdryFun
#print axioms Q597G1.eq_zero_of_bdry_eq_zero
#print axioms Q597G1.eq_of_bdry_eq
#print axioms Q597G1.G1_of_signedEdgeCount
#print axioms Q597G1.lesion_allOnes
#print axioms sorry_control
