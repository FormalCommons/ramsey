module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Ramsey.SmallRamsey.R33
public import Ramsey.SmallRamsey.R34Lower

/-!
# R(3,4) = 9

This file formalizes the milestone *R(3,4) = 9* of the plan's page on small Ramsey numbers:
every graph on at least 9 vertices has a triangle or an independent set of 4 vertices, and the
Wagner graph, a graph on 8 vertices, has neither.

## Main results

* `Ramsey.not_cliqueFreeOn_three_or_not_indepSetFreeOn_four_of_nine_le_card`: the upper half for
  a `Finset` of at least 9 vertices, the form that later upper halves apply to neighbourhoods.
* `Ramsey.not_cliqueFreeOn_four_or_not_indepSetFreeOn_three_of_nine_le_card`: its complement
  form, *R(4,3) = 9*: a clique of 4 or an independent set of 3.
* `Ramsey.not_cliqueFree_three_or_not_indepSetFree_four`,
  `Ramsey.not_cliqueFree_four_or_not_indepSetFree_three`: the same for a vertex type with at
  least 9 elements.
* `Ramsey.ramsey_three_four`: both halves together, the milestone.

## Proof of the upper half

It is enough to consider exactly 9 vertices. Suppose a graph on 9 vertices has no triangle and
no independent set of 4. The neighbours of a vertex are pairwise non-adjacent, so there are at
most 3 of them. Its non-neighbours contain no triangle, and no independent set of 3, which with
the vertex would be one of 4; by the upper half of *R(3,3) = 6* there are at most 5 of them. So
every vertex has degree 3, and the degrees sum to 27, which is odd, against the handshake lemma
`SimpleGraph.sum_degrees_eq_twice_card_edges`.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §2.1.
-/

public section

namespace Ramsey

open SimpleGraph Finset

variable {V : Type*}

/-- The upper half for a graph on exactly 9 vertices, on its vertex type. -/
private lemma not_cliqueFree_three_or_not_indepSetFree_four_of_card_eq_nine {W : Type*}
    [Fintype W] (H : SimpleGraph W) (hW : Fintype.card W = 9) :
    ¬ H.CliqueFree 3 ∨ ¬ H.IndepSetFree 4 := by
  classical
  by_contra! h
  obtain ⟨hT, hI⟩ := h
  -- Every vertex has at most 3 neighbours.
  have hle (v : W) : H.degree v ≤ 3 := by
    by_contra! hv
    rw [← card_neighborFinset_eq_degree] at hv
    obtain ⟨u, hu, hu4⟩ := exists_subset_card_eq (s := H.neighborFinset v) (n := 4) hv
    refine hI u ⟨fun a ha b hb hab hadj ↦ hT {v, a, b} ?_, hu4⟩
    rw [is3Clique_triple_iff]
    exact ⟨(mem_neighborFinset _ _ _).1 (hu ha), (mem_neighborFinset _ _ _).1 (hu hb), hadj⟩
  -- Every vertex has at least 3 neighbours.
  have hge (v : W) : 3 ≤ H.degree v := by
    by_contra! hv
    set N := (univ.erase v).filter (¬ H.Adj v ·) with hN
    have hsub : univ.erase v ⊆ H.neighborFinset v ∪ N := fun w hw ↦ by
      by_cases hvw : H.Adj v w
      · exact mem_union_left _ ((mem_neighborFinset _ _ _).2 hvw)
      · exact mem_union_right _ (mem_filter.2 ⟨hw, hvw⟩)
    have h8 := (card_le_card hsub).trans (card_union_le _ _)
    rw [card_erase_of_mem (mem_univ v), card_univ, hW, card_neighborFinset_eq_degree] at h8
    rcases not_cliqueFreeOn_or_not_indepSetFreeOn_three_of_six_le_card H (s := N) (by omega)
      with h3 | h3
    · exact h3 hT.cliqueFreeOn
    · refine h3 fun t ht hind ↦ hI (insert v t) ?_
      rw [← isNClique_compl] at hind ⊢
      refine hind.insert fun b hb ↦ ?_
      obtain ⟨hb, hvb⟩ := mem_filter.1 (ht hb)
      exact (compl_adj H v b).2 ⟨(ne_of_mem_erase hb).symm, hvb⟩
  -- So the degrees sum to 27, which is odd.
  have hsum := H.sum_degrees_eq_twice_card_edges
  rw [sum_congr rfl fun v _ ↦ le_antisymm (hle v) (hge v), sum_const, card_univ, hW, smul_eq_mul] at hsum
  omega

/-- The complement of the graph induced on `s` is the graph that the complement induces. -/
private lemma compl_induce (G : SimpleGraph V) (s : Set V) : (G.induce s)ᶜ = Gᶜ.induce s := by
  ext a b
  simp [Subtype.ext_iff]

/-- The upper half of the milestone *R(3,4) = 9*, for sets of vertices: every set of at least 9
vertices of a graph contains a triangle or an independent set of 4 vertices. -/
theorem not_cliqueFreeOn_three_or_not_indepSetFreeOn_four_of_nine_le_card (G : SimpleGraph V)
    {s : Finset V} (hs : 9 ≤ #s) :
    ¬ G.CliqueFreeOn s 3 ∨ ¬ G.IndepSetFreeOn s 4 := by
  classical
  obtain ⟨t, hts, ht⟩ := exists_subset_card_eq hs
  have := not_cliqueFree_three_or_not_indepSetFree_four_of_card_eq_nine (G.induce (t : Set V))
    (by simpa using ht)
  rw [← cliqueFree_compl, compl_induce, cliqueFree_induce_iff, cliqueFree_induce_iff] at this
  have hsub : (t : Set V) ⊆ s := coe_subset.2 hts
  exact this.imp (fun h h' ↦ h fun u hu ↦ h' (hu.trans hsub))
    fun h h' ↦ h fun u hu hind ↦ h' (hu.trans hsub) ((isNClique_compl G).1 hind)

/-- The complement form of the upper half of the milestone *R(3,4) = 9*, that is *R(4,3) = 9*:
every set of at least 9 vertices of a graph contains a clique of 4 vertices or an independent set
of 3 vertices. -/
theorem not_cliqueFreeOn_four_or_not_indepSetFreeOn_three_of_nine_le_card (G : SimpleGraph V)
    {s : Finset V} (hs : 9 ≤ #s) :
    ¬ G.CliqueFreeOn s 4 ∨ ¬ G.IndepSetFreeOn s 3 := by
  have key : ∀ (H : SimpleGraph V) (n : ℕ), Hᶜ.CliqueFreeOn s n ↔ H.IndepSetFreeOn s n :=
    fun H n ↦ by simp [CliqueFreeOn, IndepSetFreeOn]
  have := not_cliqueFreeOn_three_or_not_indepSetFreeOn_four_of_nine_le_card Gᶜ hs
  rwa [key, ← key Gᶜ, compl_compl, or_comm] at this

/-- The upper half of the milestone *R(3,4) = 9*: every graph on at least 9 vertices has a
triangle or an independent set of 4 vertices. -/
theorem not_cliqueFree_three_or_not_indepSetFree_four [Fintype V] (G : SimpleGraph V)
    (hV : 9 ≤ Fintype.card V) :
    ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 4 := by
  have := not_cliqueFreeOn_three_or_not_indepSetFreeOn_four_of_nine_le_card G (s := univ)
    (by simpa using hV)
  simp only [coe_univ, cliqueFreeOn_univ] at this
  exact this.imp_right fun h hfree ↦ h fun t _ ↦ hfree t

/-- The complement form of the upper half of the milestone *R(3,4) = 9*, that is *R(4,3) = 9*:
every graph on at least 9 vertices has a clique of 4 vertices or an independent set of 3
vertices. -/
theorem not_cliqueFree_four_or_not_indepSetFree_three [Fintype V] (G : SimpleGraph V)
    (hV : 9 ≤ Fintype.card V) :
    ¬ G.CliqueFree 4 ∨ ¬ G.IndepSetFree 3 := by
  have := not_cliqueFree_three_or_not_indepSetFree_four Gᶜ hV
  rwa [cliqueFree_compl, indepSetFree_compl, or_comm] at this

/-- The milestone *R(3,4) = 9*: every graph on at least 9 vertices has a triangle or an
independent set of 4 vertices, and the Wagner graph, the circulant graph on `ZMod 8` with
connection set `{1, 4, 7}`, a graph on 8 vertices, has neither. -/
theorem ramsey_three_four :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V), 9 ≤ Fintype.card V →
      ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 4) ∧
    (circulantGraph ({1, 4, 7} : Set (ZMod 8))).CliqueFree 3 ∧
    (circulantGraph ({1, 4, 7} : Set (ZMod 8))).IndepSetFree 4 :=
  ⟨fun _ _ G hV ↦ not_cliqueFree_three_or_not_indepSetFree_four G hV,
    wagnerGraph_cliqueFree_three, wagnerGraph_indepSetFree_four⟩

end Ramsey

end
