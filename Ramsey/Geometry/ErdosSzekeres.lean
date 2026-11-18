module

public import Ramsey.Geometry.FivePoints
public import Ramsey.Hypergraph
public import Mathlib.Analysis.Convex.Caratheodory

/-!
# The Erdős–Szekeres theorem on convex polygons

This file formalizes the milestone *The Erdős–Szekeres theorem* of the plan's page on geometry:
for every `n` there is an `N` such that among any `N` points of the plane in general position,
there are `n` in convex position. Points, general position and convex position are encoded as in
`Ramsey.Geometry.FivePoints`: a family `p : ι → ℝ × ℝ`, `¬ Collinear ℝ {p i, p j, p k}` for
distinct `i`, `j`, `k`, and `ConvexIndependent ℝ` of the family restricted to the chosen indices.

## Main results

* `Ramsey.convexIndependent_finset_iff`: a family restricted to a finite set of indices is convex
  independent if and only if none of its points is in the convex hull of the others.
* `Ramsey.exists_card_eq_convexIndependent_of_le_card`: the milestone, for a finite type of
  indices with at least `N` elements.
* `Ramsey.exists_card_eq_convexIndependent`: the milestone, for `N` points indexed by `Fin N`.

## Proof

This is Erdős and Szekeres's first proof, the plan's first route. Colour each set of four indices
by whether its points are in convex position. By Ramsey's theorem for hypergraphs
(`Ramsey.hypergraph_ramsey_finset` with `r = 4` and two colours), there is a set `S` of
`max n 5` indices all of whose four-element subsets have the same colour. They cannot all be
not in convex position, by *Five points in convex position*
(`Ramsey.exists_card_eq_four_convexIndependent`) applied to five points of `S`. So every four
points of `S` are in convex position, and then all of `S` is: if a point of `S` were in the convex
hull of the others, then by Carathéodory's theorem (`convexHull_eq_union`) it would be in the
convex hull of at most three of them, which with it would be four points of `S` not in convex
position.

## References

* P. Erdős and G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935).
-/

public section

namespace Ramsey

open Finset

/-- A family of points restricted to a finite set `s` of indices is convex independent if and only
if no point `p i` with `i ∈ s` is in the convex hull of the points of the other indices of `s`. -/
theorem convexIndependent_finset_iff {ι E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq ι]
    {p : ι → E} {s : Finset ι} :
    ConvexIndependent ℝ (fun i : s => p i) ↔
      ∀ i ∈ s, p i ∉ convexHull ℝ (p '' ↑(s.erase i)) := by
  constructor
  · intro h i hi hmem
    have himg : (fun j : s => p j) '' {j : s | (j : ι) ≠ i} = p '' ↑(s.erase i) := by
      ext x
      simp only [Set.mem_image, Set.mem_ofPred_eq, Finset.coe_erase, Set.mem_sdiff,
        Finset.mem_coe, Set.mem_singleton_iff, Subtype.exists]
      constructor
      · rintro ⟨j, hj, hji, rfl⟩
        exact ⟨j, ⟨hj, hji⟩, rfl⟩
      · rintro ⟨j, ⟨hj, hji⟩, rfl⟩
        exact ⟨j, hj, hji, rfl⟩
    have := h {j : s | (j : ι) ≠ i} ⟨i, hi⟩ (by rw [himg]; exact hmem)
    exact this rfl
  · intro h
    rw [convexIndependent_iff_notMem_convexHull_sdiff]
    intro i t hi
    refine h i i.2 (convexHull_mono ?_ hi)
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨j, ?_, rfl⟩
    have hji : j ≠ i := hj.2
    exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun e => hji (Subtype.ext e), j.2⟩)

/-- Convex independence passes to a subset of the indices. -/
private theorem ConvexIndependent.finset_mono {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    [DecidableEq ι] {p : ι → E} {s t : Finset ι} (hst : s ⊆ t)
    (ht : ConvexIndependent ℝ (fun i : t => p i)) : ConvexIndependent ℝ (fun i : s => p i) := by
  rw [convexIndependent_finset_iff] at ht ⊢
  exact fun i hi hmem => ht i (hst hi)
    (convexHull_mono (Set.image_mono (Finset.coe_subset.2 (Finset.erase_subset_erase i hst))) hmem)

/-- Convex independence of a family restricted to `s` is that of its composite with an embedding
`e`, restricted to a set whose image is `s`. -/
private theorem ConvexIndependent.finset_map {ι κ E : Type*} [AddCommGroup E] [Module ℝ E]
    [DecidableEq ι] [DecidableEq κ] {p : ι → E} (e : κ ↪ ι) {s : Finset κ}
    (hs : ConvexIndependent ℝ (fun i : s => p (e i))) :
    ConvexIndependent ℝ (fun i : s.map e => p i) := by
  rw [convexIndependent_finset_iff (p := fun j => p (e j))] at hs
  rw [convexIndependent_finset_iff]
  intro i hi hmem
  obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
  refine hs j hj ?_
  rwa [← Finset.map_erase, Finset.coe_map, Set.image_image] at hmem

/-- If every four of the points of indices in `S` are in convex position, all of them are, by
Carathéodory's theorem in the plane. -/
private theorem convexIndependent_of_forall_four {ι : Type*} [DecidableEq ι] {p : ι → ℝ × ℝ}
    {S : Finset ι} (hinj : Set.InjOn p S) (h4 : 4 ≤ S.card)
    (hS : ∀ T ∈ S.powersetCard 4, ConvexIndependent ℝ (fun i : T => p i)) :
    ConvexIndependent ℝ (fun i : S => p i) := by
  classical
  rw [convexIndependent_finset_iff]
  intro x hx hmem
  -- Carathéodory: `p x` is in the convex hull of an affinely independent set `t` of the others
  rw [convexHull_eq_union] at hmem
  simp only [Set.mem_iUnion, exists_prop] at hmem
  obtain ⟨t, hts, hti, hxt⟩ := hmem
  -- which has at most three points
  have ht3 : t.card ≤ 3 := by
    have := hti.card_le_finrank_succ
    have h2 : Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → ℝ × ℝ))) ≤ 2 :=
      (Submodule.finrank_le _).trans (by simp)
    simp only [Fintype.card_coe] at this
    omega
  -- the indices of the points of `t`
  have hts' : ↑t ⊆ p '' ↑(S.erase x) := hts
  obtain ⟨W, hWS, hWt⟩ := Finset.subset_set_image_iff.1 hts'
  have hW3 : W.card ≤ 3 := by
    rw [← hWt, Finset.card_image_of_injOn] at ht3
    · exact ht3
    · exact hinj.mono (fun y hy => Finset.mem_of_mem_erase (hWS hy))
  obtain ⟨W', hWW', hW'S, hW'⟩ := Finset.exists_subsuperset_card_eq (n := 3)
    (Finset.coe_subset.1 hWS) hW3 (by rw [Finset.card_erase_of_mem hx]; omega)
  have hxW' : x ∉ W' := fun h => by simpa using hW'S h
  have hT : insert x W' ∈ S.powersetCard 4 := by
    rw [Finset.mem_powersetCard, Finset.card_insert_of_notMem hxW', hW']
    exact ⟨Finset.insert_subset hx (hW'S.trans (Finset.erase_subset x S)), rfl⟩
  refine (convexIndependent_finset_iff.1 (hS _ hT)) x (Finset.mem_insert_self x W') ?_
  rw [Finset.erase_insert hxW']
  refine convexHull_mono ?_ hxt
  rw [← hWt, Finset.coe_image]
  exact Set.image_mono (Finset.coe_subset.2 hWW')

/-- **The Erdős–Szekeres theorem**, for a finite type of indices: for every `n` there is an `N`
such that for every family of at least `N` points of the plane in general position, no three on a
line, there are `n` of them in convex position.

This is the milestone *The Erdős–Szekeres theorem*. The plan states it for `n ≥ 3`; it holds for
all `n`. -/
theorem exists_card_eq_convexIndependent_of_le_card (n : ℕ) :
    ∃ N, ∀ {ι : Type*} [Fintype ι] (p : ι → ℝ × ℝ), N ≤ Fintype.card ι →
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {p i, p j, p k}) →
      ∃ s : Finset ι, s.card = n ∧ ConvexIndependent ℝ (fun i : s => p i) := by
  classical
  obtain ⟨N, hN⟩ := hypergraph_ramsey_finset 4 2 (max n 5)
  refine ⟨max N 3, fun {ι} _ p hcard hp => ?_⟩
  -- the colouring of the sets of four indices
  let c : Finset ι → Fin 2 := fun T => if ConvexIndependent ℝ (fun i : T => p i) then 1 else 0
  obtain ⟨S, -, hS, i, hSc⟩ := hN Finset.univ (by simp; omega) c
  -- general position makes `p` injective
  have hinj : Function.Injective p := by
    intro a b hab
    by_contra hne
    obtain ⟨k, hka, hkb⟩ : ∃ k, k ≠ a ∧ k ≠ b := by
      by_contra! h
      have : (Finset.univ : Finset ι) ⊆ {a, b} := fun k _ => by
        by_cases hka : k = a
        · simp [hka]
        · simp [h k hka]
      have := (Finset.card_le_card this).trans (Finset.card_le_two (a := a) (b := b))
      simp at this
      omega
    refine hp a b k hne (Ne.symm hka) (Ne.symm hkb) ?_
    rw [hab, Set.insert_eq_of_mem (Set.mem_insert _ _)]
    exact collinear_pair ℝ _ _
  have hall : ∀ T ∈ S.powersetCard 4, ConvexIndependent ℝ (fun i : T => p i) := by
    rcases Fin.exists_fin_two.1 ⟨i, rfl⟩ with rfl | rfl
    · -- colour `0`: impossible, by *Five points in convex position*
      exfalso
      obtain ⟨e₀⟩ : Nonempty (Fin 5 ↪ S) :=
        Function.Embedding.nonempty_of_card_le (by simp; omega)
      let e : Fin 5 ↪ ι := e₀.trans (Function.Embedding.subtype _)
      obtain ⟨s', hs', hs'ci⟩ := exists_card_eq_four_convexIndependent (fun j => p (e j))
        (fun a b k hab hak hbk => hp _ _ _ (e.injective.ne hab) (e.injective.ne hak)
          (e.injective.ne hbk))
      have hT : s'.map e ∈ S.powersetCard 4 := by
        refine Finset.mem_powersetCard.2 ⟨fun y hy => ?_, by rw [Finset.card_map, hs']⟩
        obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hy
        exact (e₀ j).2
      have := hSc _ hT
      simp only [c, ConvexIndependent.finset_map e hs'ci, ite_true] at this
      exact absurd this (by decide)
    · intro T hT
      have := hSc T hT
      simp only [c] at this
      split_ifs at this with h
      · exact h
      · exact absurd this (by decide)
  have hSci := convexIndependent_of_forall_four hinj.injOn (by omega) hall
  obtain ⟨U, hUS, hU⟩ := Finset.exists_subset_card_eq (s := S) (n := n) (by omega)
  exact ⟨U, hU, ConvexIndependent.finset_mono hUS hSci⟩

/-- **The Erdős–Szekeres theorem**: for every `n` there is an `N` such that among any `N` points of
the plane in general position, no three on a line, there are `n` in convex position.

This is the milestone *The Erdős–Szekeres theorem*. The plan states it for `n ≥ 3`; it holds for
all `n`. -/
theorem exists_card_eq_convexIndependent (n : ℕ) :
    ∃ N, ∀ p : Fin N → ℝ × ℝ,
      (∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {p i, p j, p k}) →
      ∃ s : Finset (Fin N), s.card = n ∧ ConvexIndependent ℝ (fun i : s => p i) := by
  obtain ⟨N, hN⟩ := exists_card_eq_convexIndependent_of_le_card.{0} n
  exact ⟨N, fun p hp => hN p (by simp) hp⟩

end Ramsey

end
