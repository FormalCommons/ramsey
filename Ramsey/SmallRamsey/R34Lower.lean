module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ZMod.Defs

/-!
# The lower half of R(3,4) = 9

The Wagner graph is the circulant graph on `ZMod 8` with connection set `{1, 4, 7}`: the
8-cycle together with its four long diagonals. This file shows that it has no triangle and no
independent set of 4 vertices, which is the lower half of the milestone *R(3,4) = 9* of the
plan's page on small Ramsey numbers.

## Main results

* `Ramsey.wagnerGraph_cliqueFree_three`: the Wagner graph has no triangle.
* `Ramsey.wagnerGraph_indepSetFree_four`: the Wagner graph has no independent set of 4
  vertices.

## Proof

Translations are automorphisms of a circulant graph (`SimpleGraph.circulantGraph_adj_translate`),
so a triangle, or an independent set of 4, can be moved to contain `0`. That leaves small finite
checks over the other vertices, which `decide` does: no two neighbours of `0` (that is, of
`1, 4, 7`) are adjacent, and no three of the non-neighbours `2, 3, 5, 6` of `0` are pairwise
non-adjacent.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §2.1.
-/

public section

namespace Ramsey

open SimpleGraph

/-- The Wagner graph: the circulant graph on `ZMod 8` with connection set `{1, 4, 7}`. -/
abbrev wagnerGraph : SimpleGraph (ZMod 8) :=
  circulantGraph ({1, 4, 7} : Set (ZMod 8))

/-- Moving the vertex `a` to `0` preserves adjacency in the Wagner graph. -/
private lemma adj_sub_iff {u v a : ZMod 8} :
    wagnerGraph.Adj (u - a) (v - a) ↔ wagnerGraph.Adj u v := by
  simpa only [sub_eq_add_neg] using circulantGraph_adj_translate (d := -a)

/-- No two neighbours of `0` are adjacent. -/
private lemma no_triangle_at_zero :
    ∀ b c : ZMod 8, wagnerGraph.Adj 0 b → wagnerGraph.Adj 0 c → ¬wagnerGraph.Adj b c := by
  decide

/-- The vertices other than `0` that are not adjacent to `0` are `2, 3, 5, 6`. -/
private lemma mem_of_not_adj_zero :
    ∀ b : ZMod 8, b ≠ 0 → ¬wagnerGraph.Adj 0 b → b ∈ ({2, 3, 5, 6} : Finset (ZMod 8)) := by
  decide

/-- No three distinct vertices among `2, 3, 5, 6` are pairwise non-adjacent. -/
private lemma no_indepSet_three_of_mem :
    ∀ b ∈ ({2, 3, 5, 6} : Finset (ZMod 8)), ∀ c ∈ ({2, 3, 5, 6} : Finset (ZMod 8)),
      ∀ d ∈ ({2, 3, 5, 6} : Finset (ZMod 8)), b ≠ c → b ≠ d → c ≠ d →
        ¬wagnerGraph.Adj b c → ¬wagnerGraph.Adj b d → wagnerGraph.Adj c d := by
  decide

/-- The Wagner graph, the circulant graph on `ZMod 8` with connection set `{1, 4, 7}`, has no
triangle. This is part of the lower half of the milestone *R(3,4) = 9*. -/
theorem wagnerGraph_cliqueFree_three :
    (circulantGraph ({1, 4, 7} : Set (ZMod 8))).CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
  refine no_triangle_at_zero (b - a) (c - a) ?_ ?_ (adj_sub_iff.2 hbc)
  · simpa using (adj_sub_iff (u := a) (v := b) (a := a)).2 hab
  · simpa using (adj_sub_iff (u := a) (v := c) (a := a)).2 hac

/-- The Wagner graph, the circulant graph on `ZMod 8` with connection set `{1, 4, 7}`, has no
independent set of 4 vertices. This is part of the lower half of the milestone *R(3,4) = 9*. -/
theorem wagnerGraph_indepSetFree_four :
    (circulantGraph ({1, 4, 7} : Set (ZMod 8))).IndepSetFree 4 := by
  intro t ⟨hind, hcard⟩
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, rfl⟩ := Finset.card_eq_four.1 hcard
  have h : ∀ u v : ZMod 8, u ∈ ({a, b, c, d} : Finset (ZMod 8)) →
      v ∈ ({a, b, c, d} : Finset (ZMod 8)) → u ≠ v → ¬wagnerGraph.Adj (u - a) (v - a) :=
    fun u v hu hv huv ↦ adj_sub_iff.not.2 (hind (by simpa using hu) (by simpa using hv) huv)
  have h0 : ∀ v : ZMod 8, v ∈ ({a, b, c, d} : Finset (ZMod 8)) → a ≠ v →
      ¬wagnerGraph.Adj 0 (v - a) := fun v hv hav ↦ by
    simpa using h a v (by simp) hv hav
  have hS : ∀ v : ZMod 8, v ∈ ({a, b, c, d} : Finset (ZMod 8)) → a ≠ v →
      v - a ∈ ({2, 3, 5, 6} : Finset (ZMod 8)) := fun v hv hav ↦
    mem_of_not_adj_zero _ (sub_ne_zero.2 hav.symm) (h0 v hv hav)
  exact h c d (by simp) (by simp) hcd <| no_indepSet_three_of_mem
    (b - a) (hS b (by simp) hab) (c - a) (hS c (by simp) hac) (d - a) (hS d (by simp) had)
    (sub_left_injective.ne hbc) (sub_left_injective.ne hbd) (sub_left_injective.ne hcd)
    (h b c (by simp) (by simp) hbc) (h b d (by simp) (by simp) hbd)

end Ramsey

end
