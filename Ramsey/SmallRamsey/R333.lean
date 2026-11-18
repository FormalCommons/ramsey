module

public import Mathlib.Combinatorics.Pigeonhole
public import Ramsey.SmallRamsey.R33
public import Ramsey.SmallRamsey.R333Lower

/-!
# R(3,3,3) = 17

This file formalizes the milestone *R(3,3,3) = 17* of the plan's page on small Ramsey numbers:
every colouring of the edges of the complete graph on at least 17 vertices with 3 colours has a
monochromatic triangle, and the colouring `Ramsey.r333Coloring` of the complete graph on 16
vertices has none.

## Main results

* `Ramsey.exists_not_cliqueFreeOn_labelGraph_three_of_seventeen_le_card`: the upper half for a
  `Finset` of at least 17 vertices.
* `Ramsey.exists_not_cliqueFree_labelGraph_three`: the upper half for a vertex type with at least
  17 elements.
* `Ramsey.ramsey_three_three_three`: both halves together, the milestone. The lower half is
  `Ramsey.cliqueFree_labelGraph_r333Coloring`, in `Ramsey.SmallRamsey.R333Lower`.

The upper half is proved by the argument of the plan, using the upper half of *R(3,3) = 6*. A
vertex `v` has 16 edges, so at least 6 of one colour `i`. If two of their far ends are joined by
an edge of colour `i`, they form a triangle of colour `i` with `v`. Otherwise every edge among
those far ends has one of the two other colours `j` and `k`, and *R(3,3) = 6*, applied to the
graph of colour `j` on the far ends, gives a triangle of colour `j`, or three far ends with no
edge of colour `j` among them, which is a triangle of colour `k`.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §6 and
  §6.1.
-/

public section

namespace Ramsey

open SimpleGraph Finset

variable {V : Type*}

/-- For every colour `i : Fin 3` there are colours `j` and `k` such that every colour is `i`, `j`
or `k`. -/
private lemma exists_other_colours (i : Fin 3) : ∃ j k : Fin 3, ∀ c, c = i ∨ c = j ∨ c = k := by
  revert i
  decide

/-- The upper half of the milestone *R(3,3,3) = 17*, for sets of vertices: for every colouring of
the edges of the complete graph with 3 colours, every set of at least 17 vertices contains a
monochromatic triangle. -/
theorem exists_not_cliqueFreeOn_labelGraph_three_of_seventeen_le_card
    (C : TopEdgeLabeling V (Fin 3)) {s : Finset V} (hs : 17 ≤ #s) :
    ∃ i, ¬ (C.labelGraph i).CliqueFreeOn s 3 := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by omega)
  -- The colour of the edge from `v` to `w`.
  let c : V → Fin 3 := fun w ↦ if h : v ≠ w then C.get v w h else 0
  -- Some colour `i` is the colour of at least 6 of the 16 edges at `v`.
  obtain ⟨i, -, hi⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to (t := univ) (n := 5)
    (s := s.erase v) (f := c) (fun _ _ ↦ mem_univ _)
    (by rw [card_erase_of_mem hv, card_univ, Fintype.card_fin]; omega)
  set u := (s.erase v).filter (c · = i)
  have hus : u ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
  have hvu : ∀ w ∈ u, (C.labelGraph i).Adj v w := by
    intro w hw
    obtain ⟨hw, hcw⟩ := mem_filter.1 hw
    have hvw : v ≠ w := (ne_of_mem_erase hw).symm
    simp only [c, hvw, ne_eq, not_false_eq_true, dite_true] at hcw
    exact (TopEdgeLabeling.labelGraph_adj v w).2 ⟨hvw, hcw⟩
  -- Two far ends joined by an edge of colour `i` give a triangle of colour `i` with `v`.
  by_cases hred : ∃ x ∈ u, ∃ y ∈ u, (C.labelGraph i).Adj x y
  · obtain ⟨x, hx, y, hy, hxy⟩ := hred
    refine ⟨i, fun hfree ↦ hfree (t := {v, x, y}) ?_
      (is3Clique_triple_iff.2 ⟨hvu x hx, hvu y hy, hxy⟩)⟩
    simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff,
      mem_coe]
    exact ⟨hv, hus hx, hus hy⟩
  push Not at hred
  -- Otherwise, the upper half of `R(3,3) = 6` on the far ends, in the graph of colour `j`.
  obtain ⟨j, k, hc⟩ := exists_other_colours i
  rcases not_cliqueFreeOn_or_not_indepSetFreeOn_three_of_six_le_card (C.labelGraph j)
    (s := u) (by omega) with h | h
  · exact ⟨j, fun hfree ↦ h fun t ht ↦ hfree (ht.trans (by simpa using hus))⟩
  · refine ⟨k, fun hfree ↦ h fun t ht hind ↦ hfree (ht.trans (by simpa using hus)) ?_⟩
    refine ⟨fun x hx y hy hxy ↦ ?_, hind.card_eq⟩
    have hjxy : ¬ (C.labelGraph j).Adj x y := hind.isIndepSet hx hy hxy
    have hixy := hred x (ht hx) y (ht hy)
    rw [TopEdgeLabeling.labelGraph_adj] at hjxy hixy ⊢
    push Not at hjxy hixy
    refine ⟨hxy, ?_⟩
    rcases hc (C.get x y hxy) with h' | h' | h'
    exacts [absurd h' (hixy hxy), absurd h' (hjxy hxy), h']

/-- The upper half of the milestone *R(3,3,3) = 17*: every colouring of the edges of the complete
graph on at least 17 vertices with 3 colours has a monochromatic triangle. -/
theorem exists_not_cliqueFree_labelGraph_three [Fintype V] (C : TopEdgeLabeling V (Fin 3))
    (hV : 17 ≤ Fintype.card V) : ∃ i, ¬ (C.labelGraph i).CliqueFree 3 := by
  obtain ⟨i, hi⟩ := exists_not_cliqueFreeOn_labelGraph_three_of_seventeen_le_card C
    (s := univ) (by simpa using hV)
  exact ⟨i, by simpa using hi⟩

/-- The milestone *R(3,3,3) = 17*: every colouring of the edges of the complete graph on at least
17 vertices with 3 colours has a monochromatic triangle, and the colouring `r333Coloring` of the
edges of the complete graph on 16 vertices has none. -/
theorem ramsey_three_three_three :
    (∀ (V : Type*) [Fintype V] (C : TopEdgeLabeling V (Fin 3)), 17 ≤ Fintype.card V →
      ∃ i, ¬ (C.labelGraph i).CliqueFree 3) ∧
    ∀ i, (r333Coloring.labelGraph i).CliqueFree 3 :=
  ⟨fun _ _ C hV ↦ exists_not_cliqueFree_labelGraph_three C hV,
    cliqueFree_labelGraph_r333Coloring⟩

end Ramsey

end
