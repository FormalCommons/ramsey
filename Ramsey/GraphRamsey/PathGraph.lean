module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
# Copies of path graphs

This file proves that a simple graph contains the path graph `pathGraph k` on `k > 0` vertices
if and only if it has a path with `k` vertices. This is the first lemma that the formalization
notes of the milestone *Paths* of the plan call for.

The direction from a path to a copy is `SimpleGraph.Walk.IsPath.isContained_pathGraph` in
Mathlib; this file proves the other direction.

## Main results

* `Ramsey.exists_walk_support_eq_ofFn`: a sequence of vertices in which consecutive ones are
  adjacent is the support of a walk.
* `Ramsey.Copy.adj_castSucc_succ`: in a copy of `pathGraph (n + 1)`, consecutive vertices are
  adjacent.
* `Ramsey.exists_isPath_of_copy_pathGraph`: a copy of `pathGraph (n + 1)` gives a path with
  `n + 1` vertices.
* `Ramsey.pathGraph_isContained_iff`: for `0 < k`, `pathGraph k ⊑ G` if and only if `G` has a
  path with `k` vertices.
* `Ramsey.pathGraph_isContained_pathGraph`, `Ramsey.IsContained.pathGraph_mono`: monotonicity of
  containing a path graph in the number of vertices.
-/

public section

namespace Ramsey

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A sequence `f 0, …, f n` of vertices in which consecutive ones are adjacent is the support
of a walk from `f 0` to `f n`. -/
theorem exists_walk_support_eq_ofFn :
    ∀ (n : ℕ) (f : Fin (n + 1) → V), (∀ i : Fin n, G.Adj (f i.castSucc) (f i.succ)) →
      ∃ p : G.Walk (f 0) (f (Fin.last n)), p.support = List.ofFn f
  | 0, f, _ => ⟨Walk.nil, by simp⟩
  | n + 1, f, h => by
    obtain ⟨p, hp⟩ := exists_walk_support_eq_ofFn n (fun i ↦ f i.succ)
      (fun i ↦ by rw [Fin.succ_castSucc]; exact h i.succ)
    have h0 : G.Adj (f 0) (f (Fin.succ 0)) := h 0
    refine ⟨(Walk.cons h0 p).copy rfl (congrArg f (Fin.succ_last n)), ?_⟩
    rw [Walk.support_copy, Walk.support_cons, hp]
    exact (List.ofFn_succ (f := f)).symm

/-- In a copy of `pathGraph (n + 1)` in `G`, consecutive vertices are adjacent. -/
theorem Copy.adj_castSucc_succ {n : ℕ} (f : Copy (pathGraph (n + 1)) G) (i : Fin n) :
    G.Adj (f i.castSucc) (f i.succ) :=
  f.toHom.map_adj (by simp [pathGraph_adj])

/-- A copy of `pathGraph (n + 1)` in `G` gives a path in `G` whose vertices are
`f 0, …, f n`, in this order. -/
theorem exists_isPath_of_copy_pathGraph {n : ℕ} (f : Copy (pathGraph (n + 1)) G) :
    ∃ p : G.Walk (f 0) (f (Fin.last n)), p.IsPath ∧ p.support = List.ofFn f := by
  obtain ⟨p, hp⟩ := exists_walk_support_eq_ofFn n f (Copy.adj_castSucc_succ f)
  exact ⟨p, Walk.isPath_def _ |>.mpr (hp ▸ List.nodup_ofFn.mpr f.injective), hp⟩

/-- For `0 < k`, a simple graph contains the path graph on `k` vertices if and only if it has a
path with `k` vertices. -/
theorem pathGraph_isContained_iff {k : ℕ} (hk : 0 < k) :
    pathGraph k ⊑ G ↔ ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.support.length = k := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hk.ne'
    obtain ⟨p, hp, hs⟩ := exists_isPath_of_copy_pathGraph f
    exact ⟨_, _, p, hp, by simp [hs]⟩
  · rintro ⟨u, v, p, hp, rfl⟩
    rw [Walk.length_support]
    exact hp.isContained_pathGraph

/-- The same as `pathGraph_isContained_iff`, counting the edges of the path instead of its
vertices. -/
theorem pathGraph_isContained_iff_length {k : ℕ} (hk : 0 < k) :
    pathGraph k ⊑ G ↔ ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length + 1 = k := by
  simp [pathGraph_isContained_iff hk, Walk.length_support]

/-- The path graph on `j` vertices is contained in the path graph on `k ≥ j` vertices. -/
theorem pathGraph_isContained_pathGraph {j k : ℕ} (h : j ≤ k) : pathGraph j ⊑ pathGraph k :=
  ⟨⟨⟨Fin.castLE h, fun hab ↦ by simpa [pathGraph_adj] using hab⟩, Fin.castLE_injective h⟩⟩

/-- If `G` contains the path graph on `k` vertices, it contains the path graph on `j ≤ k`
vertices. -/
theorem IsContained.pathGraph_mono {j k : ℕ} (hG : pathGraph k ⊑ G) (h : j ≤ k) :
    pathGraph j ⊑ G :=
  (pathGraph_isContained_pathGraph h).trans hG

end Ramsey

end
