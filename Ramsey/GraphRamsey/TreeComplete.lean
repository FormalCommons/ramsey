module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Ramsey numbers of trees versus complete graphs

For a tree `T` on `n ≥ 1` vertices and `m ≥ 1`, Chvátal's theorem says
`R(T, K_m) = (n - 1)(m - 1) + 1`. This file proves both halves.

## Main results

* `Ramsey.isContained_of_le_card_filter_adj`: a forest `T` on `n` vertices is contained in
  every graph that has a nonempty set `S` of vertices each with at least `n - 1` neighbours in
  `S`. This is step 1 of the plan's route; for trees, it says that a nonempty graph of minimum
  degree at least `n - 1` contains every tree on `n` vertices.
* `Ramsey.isContained_or_not_indepSetFree`: the upper half. Every graph on
  `(n - 1)(m - 1) + 1` vertices contains `T` or has an independent set of `m` vertices.
* `Ramsey.not_isContained_disjointCompleteGraphs` and
  `Ramsey.indepSetFree_disjointCompleteGraphs`: the lower half. The disjoint union
  `disjointCompleteGraphs (m - 1) (n - 1)` of `m - 1` copies of `K_{n-1}` contains no copy of
  `T` and no independent set of `m` vertices.
* `Ramsey.ramsey_tree_complete`: the milestone, both halves together.

## Sources

* V. Chvátal, *Tree-complete graph Ramsey numbers*, J. Graph Theory 1 (1977), 93.
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §5.10.

The upper half follows the plan's route, except that instead of colouring `G` with `n - 1`
colours, it builds the large independent set greedily: a vertex with fewer than `n - 1`
neighbours, together with its neighbours, removes at most `n - 1` vertices.
-/

public section

namespace Ramsey

open Finset SimpleGraph

universe u

variable {α V : Type*}

/-- A nonempty finite set of vertices of a forest contains a vertex with at most one neighbour
in the set. -/
theorem exists_le_one_card_filter_adj {T : SimpleGraph α} (hT : T.IsAcyclic) [DecidableRel T.Adj]
    {A : Finset α} (hA : A.Nonempty) : ∃ v ∈ A, #{w ∈ A | T.Adj v w} ≤ 1 := by
  classical
  set H := T.induce (A : Set α)
  have hH : H.IsAcyclic := hT.induce _
  have : Nonempty (A : Set α) := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  have h1 := hH.ncard_edgeSet_add_one_le_card
  have h2 := H.sum_degrees_eq_twice_card_edges
  by_contra! h
  have hdeg : ∀ x : (A : Set α), 2 ≤ H.degree x := by
    intro x
    rw [← card_neighborFinset_eq_degree]
    calc 2 ≤ #{w ∈ A | T.Adj x.1 w} := h x.1 x.2
      _ ≤ #(H.neighborFinset x) := by
        refine card_le_card_of_injOn (fun w => if hw : w ∈ A then ⟨w, hw⟩ else x) ?_ ?_
        · intro w hw
          simp only [coe_filter, Set.mem_ofPred_eq] at hw
          simp [hw.1, H, hw.2]
        · intro a ha b hb hab
          simp only [coe_filter, Set.mem_ofPred_eq] at ha hb
          simpa [ha.1, hb.1] using hab
  have : 2 * Fintype.card (A : Set α) ≤ ∑ x, H.degree x := by
    simpa [mul_comm] using Finset.sum_le_sum (fun x (_ : x ∈ univ) => hdeg x)
  rw [h2] at this
  rw [← coe_edgeFinset, Set.ncard_coe_finset, Nat.card_eq_fintype_card] at h1
  omega

/-- The induction behind `isContained_of_le_card_filter_adj`: every finite set `A` of vertices
of the forest `T` embeds into `S`, preserving the edges of `T` inside `A`. -/
private theorem exists_embedding_finset [Fintype α] {T : SimpleGraph α} (hT : T.IsAcyclic)
    [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} (hS : S.Nonempty)
    (hdeg : ∀ v ∈ S, Fintype.card α - 1 ≤ #{w ∈ S | G.Adj v w}) (A : Finset α) :
    ∃ f : α → V, (∀ a ∈ A, f a ∈ S) ∧ Set.InjOn f A ∧
      ∀ a ∈ A, ∀ b ∈ A, T.Adj a b → G.Adj (f a) (f b) := by
  classical
  induction A using Finset.strongInduction with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hA
  · exact ⟨fun _ => hS.choose, by simp, by simp, by simp⟩
  obtain ⟨v, hvA, hv⟩ := exists_le_one_card_filter_adj hT hA
  obtain ⟨f, hfS, hfinj, hfadj⟩ := ih (A.erase v) (erase_ssubset hvA)
  set A' := A.erase v with hA'def
  have hcardA : #A ≤ Fintype.card α := card_le_univ A
  have hA' : #A' + 1 = #A := card_erase_add_one hvA
  obtain ⟨w, hwS, hwf, hwadj⟩ :
      ∃ w ∈ S, w ∉ A'.image f ∧ ∀ u ∈ A', T.Adj v u → G.Adj (f u) w := by
    by_cases hu : ∃ u ∈ A', T.Adj v u
    · obtain ⟨u, huA', hvu⟩ := hu
      have huniq : ∀ u' ∈ A', T.Adj v u' → u' = u := by
        intro u' hu' hvu'
        by_contra hne
        have hsub : ({u, u'} : Finset α) ⊆ {w ∈ A | T.Adj v w} := by
          intro x hx
          simp only [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          · exact mem_filter.2 ⟨mem_of_mem_erase huA', hvu⟩
          · exact mem_filter.2 ⟨mem_of_mem_erase hu', hvu'⟩
        have := card_le_card hsub
        rw [card_pair (Ne.symm hne)] at this
        omega
      set N := {w ∈ S | G.Adj (f u) w} with hN
      have hNcard : #A' ≤ #N := by
        have : Fintype.card α - 1 ≤ #N := hdeg (f u) (hfS u huA')
        omega
      have hsub : A'.image f ∩ N ⊆ (A'.erase u).image f := by
        intro x hx
        simp only [hN, mem_inter, mem_image, mem_filter] at hx
        obtain ⟨⟨a, haA', rfl⟩, -, hadj⟩ := hx
        exact mem_image_of_mem f (mem_erase.2 ⟨by rintro rfl; exact G.irrefl hadj, haA'⟩)
      have hlt : #(A'.image f ∩ N) < #N :=
        calc _ ≤ #((A'.erase u).image f) := card_le_card hsub
          _ ≤ #(A'.erase u) := card_image_le
          _ < #A' := card_erase_lt_of_mem huA'
          _ ≤ #N := hNcard
      obtain ⟨w, hwN, hw⟩ := exists_mem_notMem_of_card_lt_card hlt
      have hwN' := mem_filter.1 hwN
      refine ⟨w, hwN'.1, fun h => hw (mem_inter.2 ⟨h, hwN⟩), ?_⟩
      intro u' hu' hvu'
      rw [huniq u' hu' hvu']
      exact hwN'.2
    · push Not at hu
      obtain ⟨s, hs⟩ := hS
      have hSc : #A' < #S := by
        have h1 := hdeg s hs
        have h2 : #{w ∈ S | G.Adj s w} < #S :=
          card_lt_card (filter_ssubset.2 ⟨s, hs, G.irrefl⟩)
        omega
      obtain ⟨w, hwS, hw⟩ := exists_mem_notMem_of_card_lt_card (card_image_le.trans_lt hSc)
      exact ⟨w, hwS, hw, fun u hu' h => absurd h (hu u hu')⟩
  have hfw : ∀ a ∈ A', f a ≠ w := fun a ha h => hwf (h ▸ mem_image_of_mem f ha)
  refine ⟨Function.update f v w, ?_, ?_, ?_⟩
  · intro a ha
    by_cases hav : a = v
    · subst hav
      simpa using hwS
    · rw [Function.update_of_ne hav]
      exact hfS a (mem_erase.2 ⟨hav, ha⟩)
  · intro a ha b hb hab
    simp only [mem_coe] at ha hb
    by_cases hav : a = v <;> by_cases hbv : b = v
    · rw [hav, hbv]
    · subst hav
      rw [Function.update_self, Function.update_of_ne hbv] at hab
      exact absurd hab.symm (hfw b (mem_erase.2 ⟨hbv, hb⟩))
    · subst hbv
      rw [Function.update_self, Function.update_of_ne hav] at hab
      exact absurd hab (hfw a (mem_erase.2 ⟨hav, ha⟩))
    · rw [Function.update_of_ne hav, Function.update_of_ne hbv] at hab
      exact hfinj (mem_erase.2 ⟨hav, ha⟩) (mem_erase.2 ⟨hbv, hb⟩) hab
  · intro a ha b hb hab
    by_cases hav : a = v <;> by_cases hbv : b = v
    · subst hav hbv
      exact absurd hab T.irrefl
    · subst hav
      rw [Function.update_self, Function.update_of_ne hbv]
      exact (hwadj b (mem_erase.2 ⟨hbv, hb⟩) hab).symm
    · subst hbv
      rw [Function.update_self, Function.update_of_ne hav]
      exact hwadj a (mem_erase.2 ⟨hav, ha⟩) hab.symm
    · rw [Function.update_of_ne hav, Function.update_of_ne hbv]
      exact hfadj a (mem_erase.2 ⟨hav, ha⟩) b (mem_erase.2 ⟨hbv, hb⟩) hab

/-- A forest `T` on `n` vertices is contained in every graph `G` with a nonempty finite set `S`
of vertices, each of which has at least `n - 1` neighbours in `S`. Applied to `S = univ`, it
says that a nonempty graph of minimum degree at least `n - 1` contains every tree on `n`
vertices: step 1 of the milestone *Trees versus complete graphs*. -/
theorem isContained_of_le_card_filter_adj [Fintype α] {T : SimpleGraph α} (hT : T.IsAcyclic)
    {G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} (hS : S.Nonempty)
    (hdeg : ∀ v ∈ S, Fintype.card α - 1 ≤ #{w ∈ S | G.Adj v w}) : T ⊑ G := by
  classical
  obtain ⟨f, -, hinj, hadj⟩ := exists_embedding_finset hT hS hdeg univ
  exact ⟨⟨⟨f, fun {a b} h => hadj a (mem_univ _) b (mem_univ _) h⟩,
    fun a b h => hinj (by simp) (by simp) h⟩⟩

/-- Greedy independent sets: a finite set `S` of more than `(n - 1) k` vertices either contains
a nonempty set `S'` in which each vertex has at least `n - 1` neighbours, or an independent set
of `k + 1` vertices. -/
theorem exists_le_card_filter_adj_or_exists_isNIndepSet [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (n : ℕ) :
    ∀ (k : ℕ) (S : Finset V), (n - 1) * k < #S →
      (∃ S' ⊆ S, S'.Nonempty ∧ ∀ v ∈ S', n - 1 ≤ #{w ∈ S' | G.Adj v w}) ∨
        ∃ I ⊆ S, G.IsNIndepSet (k + 1) I := by
  intro k
  induction k with
  | zero =>
    intro S hS
    obtain ⟨s, hs⟩ := card_pos.1 (by simpa using hS)
    exact Or.inr ⟨{s}, by simpa using hs, ⟨by simp, by simp⟩⟩
  | succ k ih =>
    intro S hS
    by_cases h : ∀ v ∈ S, n - 1 ≤ #{w ∈ S | G.Adj v w}
    · exact Or.inl ⟨S, subset_refl _, card_pos.1 (by omega), h⟩
    push Not at h
    obtain ⟨v, hvS, hv⟩ := h
    set S' := S \ insert v {w ∈ S | G.Adj v w} with hS'
    have hS'card : (n - 1) * k < #S' := by
      have h1 : #S - #(insert v {w ∈ S | G.Adj v w}) ≤ #S' := le_card_sdiff _ _
      have h2 := card_insert_le v {w ∈ S | G.Adj v w}
      rw [Nat.mul_succ] at hS
      omega
    rcases ih S' hS'card with ⟨S'', hS'', hne, hdeg⟩ | ⟨I, hI, hIind⟩
    · exact Or.inl ⟨S'', hS''.trans sdiff_subset, hne, hdeg⟩
    · have hvI : v ∉ I := fun h => by simpa [hS'] using hI h
      refine Or.inr ⟨insert v I, insert_subset hvS (hI.trans sdiff_subset), ?_, ?_⟩
      · rw [coe_insert]
        refine hIind.isIndepSet.insert fun w hw _ => ?_
        have hw' := mem_sdiff.1 (hI hw)
        exact ⟨fun h => hw'.2 (mem_insert_of_mem (mem_filter.2 ⟨hw'.1, h⟩)),
          fun h => hw'.2 (mem_insert_of_mem (mem_filter.2 ⟨hw'.1, h.symm⟩))⟩
      · rw [card_insert_of_notMem hvI, hIind.card_eq]

/-- The upper half of the milestone *Trees versus complete graphs*: for a tree `T` on `n`
vertices, every graph on `(n - 1)(m - 1) + 1` vertices contains a copy of `T` or has an
independent set of `m` vertices. (The plan's hypotheses `n ≥ 1` and `m ≥ 1` are not needed.) -/
theorem isContained_or_not_indepSetFree [Fintype α] {T : SimpleGraph α} (hT : T.IsTree)
    [Fintype V] (G : SimpleGraph V) {n m : ℕ} (hn : Fintype.card α = n)
    (hV : Fintype.card V = (n - 1) * (m - 1) + 1) : T ⊑ G ∨ ¬ G.IndepSetFree m := by
  classical
  rcases exists_le_card_filter_adj_or_exists_isNIndepSet G n (m - 1) univ
      (by rw [card_univ, hV]; omega) with ⟨S, -, hne, hdeg⟩ | ⟨I, -, hI⟩
  · exact Or.inl (isContained_of_le_card_filter_adj hT.isAcyclic hne (hn ▸ hdeg))
  · refine Or.inr fun h => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact h ∅ ⟨by simp, rfl⟩
    · exact h I (by rwa [Nat.sub_add_cancel hm] at hI)

/-- The disjoint union of `k` copies of the complete graph `K_l`, on `Fin k × Fin l`: two
vertices are adjacent when they are different and in the same copy. -/
@[expose] def disjointCompleteGraphs (k l : ℕ) : SimpleGraph (Fin k × Fin l) :=
  (⊥ : SimpleGraph (Fin k)) □ (⊤ : SimpleGraph (Fin l))

theorem disjointCompleteGraphs_adj {k l : ℕ} {x y : Fin k × Fin l} :
    (disjointCompleteGraphs k l).Adj x y ↔ x.1 = y.1 ∧ x ≠ y := by
  simp only [disjointCompleteGraphs, boxProd_adj, bot_adj, false_and, top_adj, false_or, ne_eq,
    Prod.ext_iff]
  tauto

/-- Part of the lower half of the milestone *Trees versus complete graphs*: a disjoint union of
copies of `K_{n-1}` contains no copy of a tree `T` on `n` vertices. -/
theorem not_isContained_disjointCompleteGraphs [Fintype α] {T : SimpleGraph α} (hT : T.IsTree)
    {n : ℕ} (hn : Fintype.card α = n) (k : ℕ) : ¬ T ⊑ disjointCompleteGraphs k (n - 1) := by
  rintro ⟨f⟩
  have hconst : ∀ a b, (f a).1 = (f b).1 := by
    intro a b
    obtain ⟨p⟩ := hT.connected.preconnected a b
    induction p with
    | nil => rfl
    | cons h _ ih => exact ((disjointCompleteGraphs_adj.1 (f.toHom.map_adj h)).1).trans ih
  have hinj : Function.Injective fun a => (f a).2 := by
    intro a b h
    exact f.injective (Prod.ext (hconst a b) h)
  have := Fintype.card_le_of_injective _ hinj
  have : 0 < Fintype.card α := Fintype.card_pos_iff.2 hT.connected.nonempty
  simp only [Fintype.card_fin] at *
  omega

/-- Part of the lower half of the milestone *Trees versus complete graphs*: for `m ≥ 1`, the
disjoint union of `m - 1` copies of a complete graph has no independent set of `m` vertices. -/
theorem indepSetFree_disjointCompleteGraphs {m : ℕ} (hm : 1 ≤ m) (l : ℕ) :
    (disjointCompleteGraphs (m - 1) l).IndepSetFree m := by
  intro s hs
  have hinj : Set.InjOn Prod.fst (s : Set (Fin (m - 1) × Fin l)) := by
    intro x hx y hy hxy
    by_contra hne
    exact hs.isIndepSet hx hy hne (disjointCompleteGraphs_adj.2 ⟨hxy, hne⟩)
  have := card_le_card_of_injOn Prod.fst (fun _ _ => mem_univ _) hinj
  rw [card_univ, Fintype.card_fin, hs.card_eq] at this
  omega

/-- The milestone *Trees versus complete graphs*: for a tree `T` on `n ≥ 1` vertices and
`m ≥ 1`, `R(T, K_m) = (n - 1)(m - 1) + 1`. Every graph on `(n - 1)(m - 1) + 1` vertices
contains a copy of `T` or has an independent set of `m` vertices, and the disjoint union of
`m - 1` copies of `K_{n-1}`, a graph on `(n - 1)(m - 1)` vertices, does neither. -/
theorem ramsey_tree_complete [Fintype α] {T : SimpleGraph α} (hT : T.IsTree) {n m : ℕ}
    (hn : Fintype.card α = n) (_hn1 : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ (V : Type u) [Fintype V] (G : SimpleGraph V),
        Fintype.card V = (n - 1) * (m - 1) + 1 → T ⊑ G ∨ ¬ G.IndepSetFree m) ∧
      Fintype.card (Fin (m - 1) × Fin (n - 1)) = (n - 1) * (m - 1) ∧
      ¬ T ⊑ disjointCompleteGraphs (m - 1) (n - 1) ∧
      (disjointCompleteGraphs (m - 1) (n - 1)).IndepSetFree m :=
  ⟨fun _ _ G hV => isContained_or_not_indepSetFree hT G hn hV,
    by simp [mul_comm], not_isContained_disjointCompleteGraphs hT hn _,
    indepSetFree_disjointCompleteGraphs hm _⟩

end Ramsey

end
