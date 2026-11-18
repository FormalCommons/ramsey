module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.LawfulXor.Basic

/-!
# R(3,3,3) = 17: the lower half

This file gives the lower half of the milestone *R(3,3,3) = 17*: a colouring of the edges of the
complete graph on 16 vertices with 3 colours that has no monochromatic triangle.

The vertices are `Fin 16`, read as the vectors of `(ℤ/2)^4` written in binary, so that the sum of
two vertices is their bitwise exclusive or `x ^^^ y`. The 15 nonzero vectors are split into
`C₁ = {1, 8, 10, 12, 15}`, `C₂ = {2, 3, 7, 11, 13}` and `C₃ = {4, 5, 6, 9, 14}`, the colours
`0, 1, 2 : Fin 3`, and the edge `{x, y}` gets the colour `i` with `x ^^^ y ∈ Cᵢ`.

A triangle `x, y, z` of colour `i` would have `x ^^^ y` and `y ^^^ z` in `Cᵢ`, and also their sum
`x ^^^ z`. So it is enough to check that no `Cᵢ` contains `a` and `b` with `a ^^^ b ∈ Cᵢ`, which
is `3 × 25` small checks rather than a check of all triples of vertices.

## Main definitions and results

* `Ramsey.r333Part`: the three sets `C₁, C₂, C₃`.
* `Ramsey.r333Coloring`: the colouring of the edges of the complete graph on `Fin 16`.
* `Ramsey.cliqueFree_labelGraph_r333Coloring`: it has no monochromatic triangle.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Dynamic Survey DS1, §6 and §6.1.
-/

public section

namespace Ramsey

open SimpleGraph

/-- The three sets `C₁ = {1, 8, 10, 12, 15}`, `C₂ = {2, 3, 7, 11, 13}` and
`C₃ = {4, 5, 6, 9, 14}` of nonzero vectors of `(ℤ/2)^4`, written in binary, that define the
colouring `r333Coloring`; they are the colours `0, 1, 2 : Fin 3`. -/
def r333Part : Fin 3 → Finset (Fin 16) :=
  ![{1, 8, 10, 12, 15}, {2, 3, 7, 11, 13}, {4, 5, 6, 9, 14}]

/-- The colour of a nonzero vector `a` of `(ℤ/2)^4`: the `i` with `a ∈ r333Part i`. (The zero
vector, which is the sum of no edge, gets the colour `2`.) -/
def r333Colour (a : Fin 16) : Fin 3 :=
  if a ∈ r333Part 0 then 0 else if a ∈ r333Part 1 then 1 else 2

/-- Every nonzero vector lies in the set of its colour. -/
theorem mem_r333Part_r333Colour : ∀ a : Fin 16, a ≠ 0 → a ∈ r333Part (r333Colour a) := by
  decide

/-- No set `Cᵢ` contains `a` and `b` together with their sum `a ^^^ b`. -/
theorem xor_notMem_r333Part :
    ∀ i : Fin 3, ∀ a ∈ r333Part i, ∀ b ∈ r333Part i, a ^^^ b ∉ r333Part i := by
  decide

/-- The 3-colouring of the edges of the complete graph on 16 vertices that colours `{x, y}` by
the `i` with `x ^^^ y ∈ Cᵢ`, where `C₁, C₂, C₃` are the sets `r333Part 0, 1, 2`. -/
def r333Coloring : TopEdgeLabeling (Fin 16) (Fin 3) :=
  EdgeLabeling.mk (fun x y _ => r333Colour (x ^^^ y)) fun x y _ => by rw [Fin.xor_comm]

private theorem xor_assoc16 (a b c : Fin 16) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) :=
  Fin.xor_assoc (n := 4) rfl a b c

private theorem xor_xor_cancel (x y z : Fin 16) : (x ^^^ y) ^^^ (y ^^^ z) = x ^^^ z := by
  rw [xor_assoc16, ← xor_assoc16 y, Fin.xor_self, Fin.xor_comm 0, Fin.xor_zero]

private theorem xor_ne_zero {x y : Fin 16} (h : x ≠ y) : x ^^^ y ≠ 0 := by
  intro h'
  apply h
  rw [← Fin.xor_zero x, ← h', ← xor_assoc16, Fin.xor_self, Fin.xor_comm, Fin.xor_zero]

private theorem mem_r333Part_of_adj {i : Fin 3} {x y : Fin 16}
    (h : (r333Coloring.labelGraph i).Adj x y) : x ^^^ y ∈ r333Part i := by
  obtain ⟨hxy, rfl⟩ := (TopEdgeLabeling.labelGraph_adj x y).1 h
  exact mem_r333Part_r333Colour _ (xor_ne_zero hxy)

/-- The lower half of the milestone *R(3,3,3) = 17*: the colouring `r333Coloring` of the edges of
the complete graph on 16 vertices with 3 colours has no monochromatic triangle, that is, no
clique of size 3 in the graph of the edges of any colour `i`. -/
theorem cliqueFree_labelGraph_r333Coloring (i : Fin 3) :
    (r333Coloring.labelGraph i).CliqueFree 3 := by
  intro s hs
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := is3Clique_iff.1 hs
  have h := xor_notMem_r333Part i _ (mem_r333Part_of_adj hxy) _ (mem_r333Part_of_adj hyz)
  apply h
  rw [xor_xor_cancel]
  exact mem_r333Part_of_adj hxz

end Ramsey

end
