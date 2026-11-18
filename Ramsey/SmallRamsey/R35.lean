module

public import Ramsey.SmallRamsey.R34
public import Ramsey.SmallRamsey.R35Lower

/-!
# R(3,5) = 14

This file formalizes the milestone *R(3,5) = 14* of the plan's page on small Ramsey numbers:
every graph on at least 14 vertices has a triangle or an independent set of 5 vertices, and the
circulant graph on `ZMod 13` whose connection set is the nonzero cubes `{1, 5, 8, 12}`, a graph
on 13 vertices, has neither.

## Main results

* `Ramsey.not_cliqueFreeOn_three_or_not_indepSetFreeOn_five_of_fourteen_le_card`: the upper half
  for a `Finset` of at least 14 vertices, the form that later upper halves apply to
  neighbourhoods.
* `Ramsey.not_cliqueFreeOn_five_or_not_indepSetFreeOn_three_of_fourteen_le_card`: its complement
  form, *R(5,3) = 14*: a clique of 5 or an independent set of 3.
* `Ramsey.not_cliqueFree_three_or_not_indepSetFree_five`,
  `Ramsey.not_cliqueFree_five_or_not_indepSetFree_three`: the same for a vertex type with at
  least 14 elements.
* `Ramsey.ramsey_three_five`: both halves together, the milestone.

## Proof of the upper half

Suppose a set `s` of at least 14 vertices has no triangle and no independent set of 5, and pick
a vertex `v` of `s`. The neighbours of `v` in `s` are pairwise non-adjacent, so there are at most
4 of them. Its non-neighbours in `s` contain no triangle, and no independent set of 4, which with
`v` would be one of 5; by the upper half of *R(3,4) = 9* there are at most 8 of them. So `s` has
at most `1 + 4 + 8 = 13` vertices, a contradiction.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §2.1.
-/

public section

namespace Ramsey

open SimpleGraph Finset

variable {V : Type*}

/-- The upper half of the milestone *R(3,5) = 14*, for sets of vertices: every set of at least 14
vertices of a graph contains a triangle or an independent set of 5 vertices. -/
theorem not_cliqueFreeOn_three_or_not_indepSetFreeOn_five_of_fourteen_le_card
    (G : SimpleGraph V) {s : Finset V} (hs : 14 ≤ #s) :
    ¬ G.CliqueFreeOn s 3 ∨ ¬ G.IndepSetFreeOn s 5 := by
  classical
  by_contra! h
  obtain ⟨hT, hI⟩ := h
  obtain ⟨v, hv⟩ : s.Nonempty := card_pos.1 (by omega)
  have hcard := card_filter_add_card_filter_not (s := s.erase v) (G.Adj v)
  rw [card_erase_of_mem hv] at hcard
  -- At most 4 neighbours of `v` in `s`.
  have hN : #((s.erase v).filter (G.Adj v)) ≤ 4 := by
    by_contra! hN
    obtain ⟨u, hu, hu5⟩ := exists_subset_card_eq (n := 5) hN
    have hus : u ⊆ s := hu.trans ((filter_subset _ _).trans (erase_subset _ _))
    have hadj : ∀ w ∈ u, G.Adj v w := fun w hw ↦ (mem_filter.1 (hu hw)).2
    refine hI (coe_subset.2 hus) ⟨fun a ha b hb _ hab ↦ hT (t := {v, a, b}) ?_ ?_, hu5⟩
    · simp only [coe_insert, coe_singleton, Set.insert_subset_iff, Set.singleton_subset_iff,
        mem_coe]
      exact ⟨hv, hus ha, hus hb⟩
    · exact is3Clique_triple_iff.2 ⟨hadj a ha, hadj b hb, hab⟩
  -- At most 8 non-neighbours of `v` in `s`.
  set M := (s.erase v).filter (¬ G.Adj v ·)
  have hMs : M ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
  have hMle : #M ≤ 8 := by
    by_contra! hMle
    rcases not_cliqueFreeOn_three_or_not_indepSetFreeOn_four_of_nine_le_card G (s := M)
      (by omega) with h3 | h4
    · exact h3 fun t ht ↦ hT (ht.trans (coe_subset.2 hMs))
    · refine h4 fun t ht hind ↦ hI (t := insert v t) ?_ ?_
      · rw [coe_insert]
        exact Set.insert_subset (mem_coe.2 hv) (ht.trans (coe_subset.2 hMs))
      · rw [← isNClique_compl] at hind ⊢
        refine hind.insert fun b hb ↦ ?_
        obtain ⟨hb, hvb⟩ := mem_filter.1 (ht hb)
        exact (compl_adj G v b).2 ⟨(ne_of_mem_erase hb).symm, hvb⟩
  omega

/-- The complement form of the upper half of the milestone *R(3,5) = 14*, that is
*R(5,3) = 14*: every set of at least 14 vertices of a graph contains a clique of 5 vertices or an
independent set of 3 vertices. -/
theorem not_cliqueFreeOn_five_or_not_indepSetFreeOn_three_of_fourteen_le_card
    (G : SimpleGraph V) {s : Finset V} (hs : 14 ≤ #s) :
    ¬ G.CliqueFreeOn s 5 ∨ ¬ G.IndepSetFreeOn s 3 := by
  have key : ∀ (H : SimpleGraph V) (n : ℕ), Hᶜ.CliqueFreeOn s n ↔ H.IndepSetFreeOn s n :=
    fun H n ↦ by simp [CliqueFreeOn, IndepSetFreeOn]
  have := not_cliqueFreeOn_three_or_not_indepSetFreeOn_five_of_fourteen_le_card Gᶜ hs
  rwa [key, ← key Gᶜ, compl_compl, or_comm] at this

/-- The upper half of the milestone *R(3,5) = 14*: every graph on at least 14 vertices has a
triangle or an independent set of 5 vertices. -/
theorem not_cliqueFree_three_or_not_indepSetFree_five [Fintype V] (G : SimpleGraph V)
    (hV : 14 ≤ Fintype.card V) :
    ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 5 := by
  have := not_cliqueFreeOn_three_or_not_indepSetFreeOn_five_of_fourteen_le_card G (s := univ)
    (by simpa using hV)
  simp only [coe_univ, cliqueFreeOn_univ] at this
  exact this.imp_right fun h hfree ↦ h fun t _ ↦ hfree t

/-- The complement form of the upper half of the milestone *R(3,5) = 14*, that is
*R(5,3) = 14*: every graph on at least 14 vertices has a clique of 5 vertices or an independent
set of 3 vertices. -/
theorem not_cliqueFree_five_or_not_indepSetFree_three [Fintype V] (G : SimpleGraph V)
    (hV : 14 ≤ Fintype.card V) :
    ¬ G.CliqueFree 5 ∨ ¬ G.IndepSetFree 3 := by
  have := not_cliqueFree_three_or_not_indepSetFree_five Gᶜ hV
  rwa [cliqueFree_compl, indepSetFree_compl, or_comm] at this

/-- The milestone *R(3,5) = 14*: every graph on at least 14 vertices has a triangle or an
independent set of 5 vertices, and the circulant graph on `ZMod 13` with connection set
`{1, 5, 8, 12}`, the nonzero cubes modulo 13, a graph on 13 vertices, has neither. -/
theorem ramsey_three_five :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V), 14 ≤ Fintype.card V →
      ¬ G.CliqueFree 3 ∨ ¬ G.IndepSetFree 5) ∧
    (circulantGraph ({1, 5, 8, 12} : Set (ZMod 13))).CliqueFree 3 ∧
    (circulantGraph ({1, 5, 8, 12} : Set (ZMod 13))).IndepSetFree 5 :=
  ⟨fun _ _ G hV ↦ not_cliqueFree_three_or_not_indepSetFree_five G hV,
    cliqueFree_three_circulantGraph_cubes_mod_thirteen,
    indepSetFree_five_circulantGraph_cubes_mod_thirteen⟩

end Ramsey

end
