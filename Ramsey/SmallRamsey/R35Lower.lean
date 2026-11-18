module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ZMod.Defs

/-!
# The lower half of R(3,5) = 14

The circulant graph on `ZMod 13` with connection set `{1, 5, 8, 12}`, the nonzero cubes
modulo 13, has no triangle and no independent set of 5 vertices.

## Main results

* `Ramsey.cliqueFree_three_circulantGraph_cubes_mod_thirteen`: the graph has no triangle.
* `Ramsey.indepSetFree_five_circulantGraph_cubes_mod_thirteen`: the graph has no independent set
  of 5 vertices.

## Proof

No three elements of `{1, 5, 8, 12}`, repetitions allowed, sum to `0` modulo 13, so there is no
triangle. An independent set of 5 vertices, translated so that it contains `0`, would have four
other vertices that are pairwise non-adjacent non-cubes; a finite check of the four-element sets
of non-cubes shows that there are none. The check is a single `decide` whose quantifiers are nested
so that it only extends partial independent sets.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey 1, §2.1.
-/

public section

namespace Ramsey

open SimpleGraph

/-- `d` is a nonzero cube modulo 13, that is, one of `1, 5, 8, 12`. -/
private abbrev IsCube (d : ZMod 13) : Prop := d = 1 ∨ d = 5 ∨ d = 8 ∨ d = 12

/-- Adjacency in the circulant graph of the cubes modulo 13: since the set of cubes is closed
under negation and does not contain `0`, `x` and `y` are adjacent exactly when `x - y` is a
cube. -/
private lemma adj_iff {x y : ZMod 13} :
    (circulantGraph ({1, 5, 8, 12} : Set (ZMod 13))).Adj x y ↔ IsCube (x - y) := by
  have key : ∀ d : ZMod 13, (d ≠ 0 ∧ (IsCube d ∨ IsCube (-d))) ↔ IsCube d := by decide
  rw [← key, circulantGraph_adj, ne_eq, sub_eq_zero, neg_sub]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

/-- The circulant graph on `ZMod 13` with the nonzero cubes `{1, 5, 8, 12}` as connection set
has no triangle. This is part of the lower half of the milestone *R(3,5) = 14*. -/
theorem cliqueFree_three_circulantGraph_cubes_mod_thirteen :
    (circulantGraph ({1, 5, 8, 12} : Set (ZMod 13))).CliqueFree 3 := by
  intro t ht
  obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
  rw [adj_iff] at hab hac hbc
  have key : ∀ d e : ZMod 13, IsCube d → IsCube e → ¬IsCube (d + e) := by decide
  exact key _ _ hab hbc (by rwa [sub_add_sub_cancel])

/-- Two distinct vertices that do not differ by a cube. -/
private abbrev NonAdj (x y : ZMod 13) : Prop := x ≠ y ∧ ¬IsCube (x - y)

-- The nested quantifiers below make a large `Decidable` instance term.
set_option synthInstance.maxSize 1024 in
/-- There are no four pairwise non-adjacent non-neighbours of `0`: among any four non-cubes
modulo 13, two differ by a cube. The quantifiers are nested so that `decide` only visits
partial independent sets. -/
private lemma no_indep_five_through_zero :
    ∀ b : ZMod 13, NonAdj b 0 →
    ∀ c : ZMod 13, NonAdj c 0 → NonAdj c b →
    ∀ d : ZMod 13, NonAdj d 0 → NonAdj d b → NonAdj d c →
    ∀ e : ZMod 13, NonAdj e 0 → NonAdj e b → NonAdj e c → NonAdj e d → False := by
  decide

/-- The circulant graph on `ZMod 13` with the nonzero cubes `{1, 5, 8, 12}` as connection set
has no independent set of 5 vertices. This is part of the lower half of the milestone
*R(3,5) = 14*. -/
theorem indepSetFree_five_circulantGraph_cubes_mod_thirteen :
    (circulantGraph ({1, 5, 8, 12} : Set (ZMod 13))).IndepSetFree 5 := by
  intro t ht
  have na : ∀ x ∈ t, ∀ y ∈ t, x ≠ y → NonAdj (x - y) 0 := fun x hx y hy hxy =>
    ⟨by rwa [ne_eq, sub_eq_zero], by rw [sub_zero, ← adj_iff]; exact ht.isIndepSet hx hy hxy⟩
  have na' : ∀ x ∈ t, ∀ y ∈ t, ∀ a, x ≠ y → NonAdj (x - a) (y - a) := fun x hx y hy a hxy =>
    ⟨by rwa [ne_eq, sub_left_inj],
      by rw [sub_sub_sub_cancel_right, ← adj_iff]; exact ht.isIndepSet hx hy hxy⟩
  obtain ⟨a, ha⟩ : t.Nonempty := Finset.card_pos.1 (by rw [ht.card_eq]; decide)
  have h4 : (t.erase a).card = 4 := by rw [Finset.card_erase_of_mem ha, ht.card_eq]
  obtain ⟨b, hb⟩ : (t.erase a).Nonempty := Finset.card_pos.1 (by rw [h4]; decide)
  have h3 : ((t.erase a).erase b).card = 3 := by rw [Finset.card_erase_of_mem hb, h4]
  obtain ⟨c, d, e, hcd, hce, hde, hcde⟩ := Finset.card_eq_three.1 h3
  have hc : c ∈ (t.erase a).erase b := by simp [hcde]
  have hd : d ∈ (t.erase a).erase b := by simp [hcde]
  have he : e ∈ (t.erase a).erase b := by simp [hcde]
  simp only [Finset.mem_erase] at hb hc hd he
  exact no_indep_five_through_zero _ (na b hb.2 a ha hb.1)
    _ (na c hc.2.2 a ha hc.2.1) (na' c hc.2.2 b hb.2 a hc.1)
    _ (na d hd.2.2 a ha hd.2.1) (na' d hd.2.2 b hb.2 a hd.1) (na' d hd.2.2 c hc.2.2 a hcd.symm)
    _ (na e he.2.2 a ha he.2.1) (na' e he.2.2 b hb.2 a he.1) (na' e he.2.2 c hc.2.2 a hce.symm)
      (na' e he.2.2 d hd.2.2 a hde.symm)

end Ramsey

end
