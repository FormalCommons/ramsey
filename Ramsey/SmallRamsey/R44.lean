module

public import Ramsey.SmallRamsey.R34
public import Ramsey.SmallRamsey.R44Lower

/-!
# R(4,4) = 18

This file formalizes the milestone *R(4,4) = 18* of the plan's page on small Ramsey numbers:
every graph on at least 18 vertices has a clique of 4 vertices or an independent set of 4
vertices, and the Paley graph on `ZMod 17`, a graph on 17 vertices, has neither.

## Main results

* `Ramsey.not_cliqueFreeOn_or_not_indepSetFreeOn_four_of_eighteen_le_card`: the upper half for a
  `Finset` of at least 18 vertices, the form that later upper halves apply to neighbourhoods.
* `Ramsey.not_cliqueFree_four_or_not_indepSetFree_four`: the upper half for a vertex type with
  at least 18 elements.
* `Ramsey.ramsey_four_four`: both halves together, the milestone.

## Proof of the upper half

Take a vertex `v` of a set `s` of at least 18 vertices. The other vertices of `s`, at least 17,
are neighbours or non-neighbours of `v`, so there are at least 9 of one kind. If there are 9
neighbours, by the upper half of *R(3,4) = 9* they contain a triangle, which with `v` is a clique
of 4, or an independent set of 4. If there are 9 non-neighbours, by its complement form
*R(4,3) = 9* they contain a clique of 4, or an independent set of 3, which with `v` is an
independent set of 4. The lower half is `Ramsey.paley17_cliqueFree` and
`Ramsey.paley17_indepSetFree`.

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
private lemma cliqueFreeOn_compl_iff' {G : SimpleGraph V} {s : Set V} {n : ℕ} :
    Gᶜ.CliqueFreeOn s n ↔ G.IndepSetFreeOn s n := by
  simp [CliqueFreeOn, IndepSetFreeOn]

/-- If all vertices of `t ⊆ s` are adjacent to a vertex `v` of `s`, and `t` contains a clique of
`n` vertices, then `s` contains a clique of `n + 1` vertices. -/
private lemma not_cliqueFreeOn_succ_of_neighbours (G : SimpleGraph V) {s t : Finset V} {v : V}
    {n : ℕ} (hv : v ∈ s) (hts : t ⊆ s) (hvt : ∀ w ∈ t, G.Adj v w)
    (h : ¬ G.CliqueFreeOn t n) : ¬ G.CliqueFreeOn s (n + 1) := by
  classical
  intro hfree
  refine h fun u hu hc ↦ hfree ?_ (hc.insert fun b hb ↦ hvt b (hu hb))
  rw [coe_insert, Set.insert_subset_iff]
  exact ⟨hv, hu.trans (coe_subset.2 hts)⟩

/-- The upper half of the milestone *R(4,4) = 18*, for sets of vertices: every set of at least 18
vertices of a graph contains a clique of 4 vertices or an independent set of 4 vertices. -/
theorem not_cliqueFreeOn_or_not_indepSetFreeOn_four_of_eighteen_le_card (G : SimpleGraph V)
    {s : Finset V} (hs : 18 ≤ #s) :
    ¬ G.CliqueFreeOn s 4 ∨ ¬ G.IndepSetFreeOn s 4 := by
  classical
  obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by omega)
  have hcard := card_filter_add_card_filter_not (s := s.erase v) (G.Adj v)
  rw [card_erase_of_mem hv] at hcard
  have hsub : ∀ p : V → Prop, ∀ _ : DecidablePred p, (s.erase v).filter p ⊆ s :=
    fun _ _ ↦ (filter_subset _ _).trans (erase_subset _ _)
  by_cases h : 9 ≤ #((s.erase v).filter (G.Adj v))
  · -- At least 9 neighbours.
    rcases not_cliqueFreeOn_three_or_not_indepSetFreeOn_four_of_nine_le_card G h with h3 | h4
    · exact .inl (not_cliqueFreeOn_succ_of_neighbours G hv (hsub _ _)
        (fun w hw ↦ (mem_filter.1 hw).2) h3)
    · exact .inr fun h' ↦ h4 fun u hu ↦ h' (hu.trans (coe_subset.2 (hsub _ _)))
  · -- At least 9 non-neighbours.
    rcases not_cliqueFreeOn_four_or_not_indepSetFreeOn_three_of_nine_le_card G
      (s := (s.erase v).filter (¬ G.Adj v ·)) (by omega) with h4 | h3
    · exact .inl fun h' ↦ h4 fun u hu ↦ h' (hu.trans (coe_subset.2 (hsub _ _)))
    · rw [← cliqueFreeOn_compl_iff'] at h3 ⊢
      refine .inr (not_cliqueFreeOn_succ_of_neighbours Gᶜ hv (hsub _ _) (fun w hw ↦ ?_) h3)
      obtain ⟨hw, hvw⟩ := mem_filter.1 hw
      exact (compl_adj G v w).2 ⟨(ne_of_mem_erase hw).symm, hvw⟩

/-- The upper half of the milestone *R(4,4) = 18*: every graph on at least 18 vertices has a
clique of 4 vertices or an independent set of 4 vertices. -/
theorem not_cliqueFree_four_or_not_indepSetFree_four [Fintype V] (G : SimpleGraph V)
    (hV : 18 ≤ Fintype.card V) :
    ¬ G.CliqueFree 4 ∨ ¬ G.IndepSetFree 4 := by
  have := not_cliqueFreeOn_or_not_indepSetFreeOn_four_of_eighteen_le_card G (s := univ)
    (by simpa using hV)
  simp only [coe_univ, cliqueFreeOn_univ] at this
  exact this.imp_right fun h hfree ↦ h fun t _ ↦ hfree t

/-- The milestone *R(4,4) = 18*: every graph on at least 18 vertices has a clique of 4 vertices
or an independent set of 4 vertices, and the Paley graph on `ZMod 17`, a graph on 17 vertices,
has neither. -/
theorem ramsey_four_four :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V), 18 ≤ Fintype.card V →
      ¬ G.CliqueFree 4 ∨ ¬ G.IndepSetFree 4) ∧
    paley17.CliqueFree 4 ∧ paley17.IndepSetFree 4 :=
  ⟨fun _ _ G hV ↦ not_cliqueFree_four_or_not_indepSetFree_four G hV,
    paley17_cliqueFree, paley17_indepSetFree⟩

end Ramsey

end
