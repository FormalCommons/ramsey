module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-!
# R(3,3) = 6

This file formalizes the milestone *R(3,3) = 6* of the plan's page on small Ramsey numbers:
every graph on at least 6 vertices has a triangle or an independent set of 3 vertices, and the
5-cycle has neither.

## Main results

* `Ramsey.not_cliqueFreeOn_or_not_indepSetFreeOn_three_of_six_le_card`: the upper half for a
  `Finset` of at least 6 vertices, the form that later upper halves apply to neighbourhoods.
* `Ramsey.not_cliqueFree_three_or_not_indepSetFree_three`: the upper half for a vertex type with at
  least 6 elements.
* `Ramsey.cliqueFree_three_cycleGraph_five`, `Ramsey.indepSetFree_three_cycleGraph_five`: the lower
  half, for `SimpleGraph.cycleGraph 5`.
* `Ramsey.ramsey_three_three`: both halves together, the milestone.

The upper half is proved by the degree argument: a vertex has at least three neighbours or at
least three non-neighbours among the five others. Among three neighbours, either two are adjacent
and form a triangle with the vertex, or the three are independent; the case of non-neighbours is
the same argument in the complement.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §2.1.
-/

public section

namespace Ramsey

open SimpleGraph Finset

variable {V : Type*}

/-- The complement of `G` has no clique of size `n` in `s` if and only if `G` has no independent
set of size `n` in `s`. -/
private lemma cliqueFreeOn_compl_iff {G : SimpleGraph V} {s : Set V} {n : ℕ} :
    Gᶜ.CliqueFreeOn s n ↔ G.IndepSetFreeOn s n := by
  simp [CliqueFreeOn, IndepSetFreeOn]

/-- If a vertex `v` of `s` has three neighbours in `s`, then `s` contains a triangle or an
independent set of size 3. -/
private lemma of_three_le_card_neighbours (G : SimpleGraph V) {s t : Finset V} {v : V}
    (hv : v ∈ s) (hts : t ⊆ s) (hvt : ∀ w ∈ t, G.Adj v w) (ht : 3 ≤ #t) :
    ¬ G.CliqueFreeOn s 3 ∨ ¬ G.IndepSetFreeOn s 3 := by
  classical
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := two_lt_card_iff.1 ht
  have triangle : ∀ x ∈ t, ∀ y ∈ t, G.Adj x y → ¬ G.CliqueFreeOn s 3 := by
    intro x hx y hy hxy hfree
    refine hfree ?_ (is3Clique_triple_iff.2 ⟨hvt x hx, hvt y hy, hxy⟩)
    simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff,
      mem_coe]
    exact ⟨hv, hts hx, hts hy⟩
  by_cases h₁ : G.Adj a b
  · exact .inl (triangle a ha b hb h₁)
  by_cases h₂ : G.Adj a c
  · exact .inl (triangle a ha c hc h₂)
  by_cases h₃ : G.Adj b c
  · exact .inl (triangle b hb c hc h₃)
  refine .inr fun hfree ↦ hfree (t := {a, b, c}) ?_ ?_
  · simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff,
      mem_coe]
    exact ⟨hts ha, hts hb, hts hc⟩
  · rw [← isNClique_compl, is3Clique_triple_iff]
    simp [hab, hac, hbc, h₁, h₂, h₃]

/-- The upper half of the milestone *R(3,3) = 6*, for sets of vertices: every set of at least 6
vertices of a graph contains a triangle or an independent set of 3 vertices. -/
theorem not_cliqueFreeOn_or_not_indepSetFreeOn_three_of_six_le_card (G : SimpleGraph V)
    {s : Finset V} (hs : 6 ≤ #s) :
    ¬ G.CliqueFreeOn s 3 ∨ ¬ G.IndepSetFreeOn s 3 := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by omega)
  have hcard := card_filter_add_card_filter_not (s := s.erase v) (G.Adj v)
  rw [card_erase_of_mem hv] at hcard
  by_cases h : 3 ≤ #((s.erase v).filter (G.Adj v))
  · exact of_three_le_card_neighbours G hv ((filter_subset _ _).trans (erase_subset _ _))
      (fun w hw ↦ (mem_filter.1 hw).2) h
  · -- At least three non-neighbours: the same argument in the complement.
    have := of_three_le_card_neighbours Gᶜ (t := (s.erase v).filter (¬ G.Adj v ·)) hv
      ((filter_subset _ _).trans (erase_subset _ _)) (fun w hw ↦ ?_) (by omega)
    · rwa [← cliqueFreeOn_compl_iff (G := Gᶜ), compl_compl, cliqueFreeOn_compl_iff,
        or_comm] at this
    obtain ⟨hw, hvw⟩ := mem_filter.1 hw
    exact (compl_adj G v w).2 ⟨(ne_of_mem_erase hw).symm, hvw⟩

/-- The upper half of the milestone *R(3,3) = 6*: every graph on at least 6 vertices has a
triangle or an independent set of 3 vertices. -/
theorem not_cliqueFree_three_or_not_indepSetFree_three [Fintype V] (G : SimpleGraph V)
    (hV : 6 ≤ Fintype.card V) :
    ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 3 := by
  have := not_cliqueFreeOn_or_not_indepSetFreeOn_three_of_six_le_card G (s := univ)
    (by simpa using hV)
  simp only [coe_univ, cliqueFreeOn_univ] at this
  exact this.imp_right fun h hfree ↦ h fun t _ ↦ hfree t

/-- The 5-cycle has no triangle. This is part of the lower half of the milestone
*R(3,3) = 6*. -/
theorem cliqueFree_three_cycleGraph_five : (cycleGraph 5).CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
  revert a b c
  decide

/-- The 5-cycle has no independent set of 3 vertices. This is part of the lower half of the
milestone *R(3,3) = 6*. -/
theorem indepSetFree_three_cycleGraph_five : (cycleGraph 5).IndepSetFree 3 := by
  intro t ht
  rw [← isNClique_compl] at ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
  revert a b c
  decide

/-- The milestone *R(3,3) = 6*: every graph on at least 6 vertices has a triangle or an
independent set of 3 vertices, and the 5-cycle, a graph on 5 vertices, has neither. -/
theorem ramsey_three_three :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V), 6 ≤ Fintype.card V →
      ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 3) ∧
    (cycleGraph 5).CliqueFree 3 ∧ (cycleGraph 5).IndepSetFree 3 :=
  ⟨fun _ _ G hV ↦ not_cliqueFree_three_or_not_indepSetFree_three G hV,
    cliqueFree_three_cycleGraph_five, indepSetFree_three_cycleGraph_five⟩

end Ramsey

end
