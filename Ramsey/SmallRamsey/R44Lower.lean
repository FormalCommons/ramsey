module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Algebra.Group.Even
public import Mathlib.Tactic.LinearCombination

/-!
# R(4,4) = 18: the lower half

The Paley graph on `ZMod 17` is the circulant graph whose connection set is the set
`{1, 2, 4, 8, 9, 13, 15, 16}` of nonzero squares modulo 17. This file shows that it has no
clique of 4 vertices and no independent set of 4 vertices, the lower half of the milestone
*R(4,4) = 18* of the plan's page on small Ramsey numbers.

The proof follows the plan's route. Multiplication by a nonzero square and translations are
automorphisms, so a clique of 4 can be moved to one containing `0` and `1`; the common
neighbours of `0` and `1` are `2`, `9` and `16`, no two of which are adjacent. Multiplication by
`3`, a non-square, maps the complement into the graph, so the graph has no independent set of
4 vertices either.

## Main results

* `Ramsey.paleySquares17`: the nonzero squares modulo 17.
* `Ramsey.paley17`: the Paley graph on `ZMod 17`.
* `Ramsey.paley17_cliqueFree`: it has no clique of 4 vertices.
* `Ramsey.paley17_indepSetFree`: it has no independent set of 4 vertices.

## References

* R. E. Greenwood and A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
-/

@[expose] public section

namespace Ramsey

open SimpleGraph Finset

/-- The nonzero squares modulo 17: `{1, 2, 4, 8, 9, 13, 15, 16}`. -/
def paleySquares17 : Finset (ZMod 17) := {1, 2, 4, 8, 9, 13, 15, 16}

/-- The elements of `paleySquares17` are exactly the nonzero squares modulo 17. -/
theorem mem_paleySquares17_iff (x : ZMod 17) : x ∈ paleySquares17 ↔ x ≠ 0 ∧ IsSquare x := by
  show _ ↔ _ ∧ ∃ r, x = r * r
  revert x; decide

/-- The Paley graph on `ZMod 17`: `x` and `y` are adjacent when `x - y` is a nonzero square. -/
def paley17 : SimpleGraph (ZMod 17) := circulantGraph (paleySquares17 : Set (ZMod 17))

instance : DecidableRel paley17.Adj :=
  inferInstanceAs (DecidableRel (circulantGraph (paleySquares17 : Set (ZMod 17))).Adj)

end Ramsey

end

namespace Ramsey

open SimpleGraph Finset

/-- Since `-1` is a square, adjacency in `paley17` is just membership of the difference. -/
public theorem paley17_adj_iff (x y : ZMod 17) : paley17.Adj x y ↔ x - y ∈ paleySquares17 := by
  show (circulantGraph _).Adj x y ↔ _
  revert x y; decide

/-- The nonzero squares are closed under multiplication. -/
private theorem mul_mem (c d : ZMod 17) (hc : c ∈ paleySquares17) (hd : d ∈ paleySquares17) :
    c * d ∈ paleySquares17 := by
  revert c d; decide

/-- Every nonzero square has an inverse that is a nonzero square. -/
private theorem exists_inv_mem (d : ZMod 17) (hd : d ∈ paleySquares17) :
    ∃ c ∈ paleySquares17, c * d = 1 := by
  revert d; decide

/-- Multiplication by `3` maps non-zero non-squares to squares. -/
private theorem three_mul_mem (d : ZMod 17) (h0 : d ≠ 0) (hd : d ∉ paleySquares17) :
    3 * d ∈ paleySquares17 := by
  revert d; decide

/-- The common neighbours of `0` and `1` are pairwise non-adjacent. -/
private theorem no_clique_zero_one (u v : ZMod 17) (hu0 : paley17.Adj u 0) (hu1 : paley17.Adj u 1)
    (hv0 : paley17.Adj v 0) (hv1 : paley17.Adj v 1) : ¬ paley17.Adj u v := by
  revert u v; decide

/-- An injective map that sends adjacent vertices of `H` to adjacent vertices of `G` sends
`n`-cliques to `n`-cliques. -/
private theorem isNClique_map {α : Type*} {H G : SimpleGraph α} {n : ℕ} {s : Finset α}
    (f : α ↪ α) (hf : ∀ x y, H.Adj x y → G.Adj (f x) (f y)) (hs : H.IsNClique n s) :
    G.IsNClique n (s.map f) := by
  refine ⟨?_, (card_map _).trans hs.2⟩
  intro x hx y hy hxy
  simp only [coe_map, Set.mem_image, mem_coe] at hx hy
  obtain ⟨x, hx, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := hy
  exact hf x y (hs.1 hx hy fun h => hxy (h ▸ rfl))

/-- A clique of 4 vertices that contains `0` and `1` does not exist. -/
private theorem not_isNClique_zero_one (s : Finset (ZMod 17)) (hs : paley17.IsNClique 4 s)
    (h0 : 0 ∈ s) (h1 : 1 ∈ s) : False := by
  have hcard : 1 < ((s.erase 0).erase 1).card := by
    rw [card_erase_of_mem (mem_erase.2 ⟨by decide, h1⟩), card_erase_of_mem h0, hs.2]
    decide
  obtain ⟨u, hu, v, hv, huv⟩ := one_lt_card.1 hcard
  simp only [mem_erase] at hu hv
  exact no_clique_zero_one u v (hs.1 hu.2.2 h0 hu.2.1) (hs.1 hu.2.2 h1 hu.1)
    (hs.1 hv.2.2 h0 hv.2.1) (hs.1 hv.2.2 h1 hv.1) (hs.1 hu.2.2 hv.2.2 huv)

/-- The Paley graph on `ZMod 17` has no clique of 4 vertices. Part of the milestone
*R(4,4) = 18* (its lower half). -/
public theorem paley17_cliqueFree : paley17.CliqueFree 4 := by
  intro s hs
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 (hs.2.symm ▸ (by decide : 1 < 4))
  have hba : paley17.Adj b a := hs.1 hb ha (Ne.symm hab)
  rw [paley17_adj_iff] at hba
  obtain ⟨c, hc, hcd⟩ := exists_inv_mem _ hba
  -- the affine map `x ↦ c * (x - a)` is an automorphism sending `a` to `0` and `b` to `1`
  let f : ZMod 17 ↪ ZMod 17 :=
    ⟨fun x => c * (x - a), fun x y hxy => by
      simp only at hxy
      exact sub_eq_zero.1 (by linear_combination (b - a) * hxy + (y - x) * hcd)⟩
  have hf : ∀ x y, paley17.Adj x y → paley17.Adj (f x) (f y) := by
    intro x y hxy
    rw [paley17_adj_iff] at hxy ⊢
    have : f x - f y = c * (x - y) := by show c * (x - a) - c * (y - a) = _; rw [← mul_sub, sub_sub_sub_cancel_right]
    rw [this]
    exact mul_mem _ _ hc hxy
  refine not_isNClique_zero_one _ (isNClique_map f hf hs) ?_ ?_
  · exact mem_map.2 ⟨a, ha, show c * (a - a) = 0 by rw [sub_self, mul_zero]⟩
  · exact mem_map.2 ⟨b, hb, hcd⟩

/-- The Paley graph on `ZMod 17` has no independent set of 4 vertices. Part of the milestone
*R(4,4) = 18* (its lower half). -/
public theorem paley17_indepSetFree : paley17.IndepSetFree 4 := by
  rw [← cliqueFree_compl]
  intro s hs
  let f : ZMod 17 ↪ ZMod 17 :=
    ⟨fun x => 3 * x, fun x y hxy => by
      have : 6 * (3 * x) = 6 * (3 * y) := by simp only at hxy; rw [hxy]
      rwa [← mul_assoc, ← mul_assoc, (by decide : (6 : ZMod 17) * 3 = 1), one_mul, one_mul]
        at this⟩
  have hf : ∀ x y, paley17ᶜ.Adj x y → paley17.Adj (f x) (f y) := by
    intro x y hxy
    rw [compl_adj, paley17_adj_iff] at hxy
    rw [paley17_adj_iff]
    have : f x - f y = 3 * (x - y) := by exact (mul_sub 3 x y).symm
    rw [this]
    exact three_mul_mem _ (sub_ne_zero.2 hxy.1) hxy.2
  exact paley17_cliqueFree _ (isNClique_map f hf hs)

end Ramsey
