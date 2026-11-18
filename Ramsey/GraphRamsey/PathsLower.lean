module

public import Ramsey.GraphRamsey.PathGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Paths: the lower half

For `n ≥ m ≥ 2`, `R(P_n, P_m) = n + ⌊m/2⌋ - 1`, where `P_k = SimpleGraph.pathGraph k`. This
file proves the lower half, part of the milestone *Paths*: some graph on `n + ⌊m/2⌋ - 2`
vertices contains no `P_n`, and its complement contains no `P_m`.

## Main results

* `Ramsey.pathsLowerGraph`: the graph on `Fin a ⊕ Fin b` that is complete on `Fin a` and in
  which the vertices of `Fin b` are isolated.
* `Ramsey.not_pathGraph_isContained_pathsLowerGraph`: it contains no `P_k` for `k > a ≥ 1`.
* `Ramsey.not_pathGraph_isContained_compl_pathsLowerGraph`: its complement contains no `P_k`
  for `k / 2 > b`.
* `Ramsey.pathGraph_ramsey_lower`: the lower half of `R(P_n, P_m) = n + ⌊m/2⌋ - 1`.

## Proof

Take `a = n - 1` and `b = ⌊m/2⌋ - 1`. Every edge of the graph lies in `Fin a`, so a copy of
`P_n` would put `n` distinct vertices in `Fin a`. In the complement, `Fin a` is independent,
so of the vertices `2j` and `2j + 1` of a copy of `P_m`, for `j < ⌊m/2⌋`, one lies in `Fin b`;
this gives `⌊m/2⌋` distinct vertices in `Fin b`.

## References

* L. Gerencsér, A. Gyárfás, *On Ramsey-type problems*, Ann. Univ. Sci. Budapest. Eötvös Sect.
  Math. 10 (1967), 167–170.
-/

public section

namespace Ramsey

open SimpleGraph

/-- The graph on `Fin a ⊕ Fin b` that is complete on `Fin a`, with the vertices of `Fin b`
isolated. It witnesses the lower half of `R(P_n, P_m) = n + ⌊m/2⌋ - 1`. -/
def pathsLowerGraph (a b : ℕ) : SimpleGraph (Fin a ⊕ Fin b) where
  Adj x y := x ≠ y ∧ x.isLeft ∧ y.isLeft
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h ↦ h.1 rfl⟩

/-- Two vertices are adjacent in `pathsLowerGraph a b` if and only if they are distinct and both
lie in `Fin a`. -/
theorem pathsLowerGraph_adj {a b : ℕ} {x y : Fin a ⊕ Fin b} :
    (pathsLowerGraph a b).Adj x y ↔ x ≠ y ∧ x.isLeft ∧ y.isLeft := Iff.rfl

/-- For `a ≥ 1`, `pathsLowerGraph a b` contains no path graph on more than `a` vertices. -/
theorem not_pathGraph_isContained_pathsLowerGraph {a b k : ℕ} (ha : 0 < a) (hk : a < k) :
    ¬ pathGraph k ⊑ pathsLowerGraph a b := by
  rintro ⟨f⟩
  have hl : ∀ i : Fin k, ∃ c, f i = Sum.inl c := by
    intro i
    -- every vertex of `P_k` has a neighbour, since `k ≥ 2`
    obtain ⟨j, hj⟩ : ∃ j : Fin k, (pathGraph k).Adj i j := by
      by_cases hi : i.val + 1 < k
      · exact ⟨⟨i.val + 1, hi⟩, pathGraph_adj.mpr (Or.inl rfl)⟩
      · exact ⟨⟨i.val - 1, by omega⟩, pathGraph_adj.mpr (Or.inr (by simp; omega))⟩
    exact Sum.isLeft_iff.mp (f.toHom.map_adj hj).2.1
  choose g hg using hl
  have hinj : Function.Injective g := fun i j hij ↦
    f.injective ((hg i).trans ((congrArg Sum.inl hij).trans (hg j).symm))
  have := Fintype.card_le_of_injective g hinj
  simp only [Fintype.card_fin] at this
  omega

/-- The complement of `pathsLowerGraph a b` contains no path graph on `k` vertices with
`b < ⌊k/2⌋`. -/
theorem not_pathGraph_isContained_compl_pathsLowerGraph {a b k : ℕ} (hk : b < k / 2) :
    ¬ pathGraph k ⊑ (pathsLowerGraph a b)ᶜ := by
  rintro ⟨f⟩
  have hr : ∀ j : Fin (k / 2), ∃ i : Fin k, i.val / 2 = j.val ∧ ∃ c, f i = Sum.inr c := by
    intro j
    have hj := j.isLt
    let p : Fin k := ⟨2 * j.val, by omega⟩
    let q : Fin k := ⟨2 * j.val + 1, by omega⟩
    have hpq : (pathGraph k).Adj p q := pathGraph_adj.mpr (Or.inl rfl)
    have h := f.toHom.map_adj hpq
    rw [compl_adj, pathsLowerGraph_adj] at h
    by_cases hp : (f p).isLeft
    · have hq : ¬ (f q).isLeft := fun hq ↦ h.2 ⟨h.1, hp, hq⟩
      exact ⟨q, by simp only [q]; omega, Sum.isRight_iff.mp (by simpa using hq)⟩
    · exact ⟨p, by simp only [p]; omega, Sum.isRight_iff.mp (by simpa using hp)⟩
  choose i hi c hc using hr
  have hinj : Function.Injective c := by
    intro j j' hjj'
    have : i j = i j' :=
      f.injective ((hc j).trans ((congrArg Sum.inr hjj').trans (hc j').symm))
    exact Fin.ext (by rw [← hi j, ← hi j', this])
  have := Fintype.card_le_of_injective c hinj
  simp only [Fintype.card_fin] at this
  omega

/-- The lower half of the milestone *Paths*: for `n ≥ m ≥ 2`, some graph on
`n + ⌊m/2⌋ - 2` vertices contains no path graph on `n` vertices, and its complement contains
no path graph on `m` vertices. So `R(P_n, P_m) ≥ n + ⌊m/2⌋ - 1`. -/
theorem pathGraph_ramsey_lower {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    ∃ G : SimpleGraph (Fin (n + m / 2 - 2)),
      ¬ pathGraph n ⊑ G ∧ ¬ pathGraph m ⊑ Gᶜ := by
  have h2 : 1 ≤ m / 2 := by omega
  let e : Fin (n + m / 2 - 2) ≃ Fin (n - 1) ⊕ Fin (m / 2 - 1) :=
    (finCongr (by omega : n + m / 2 - 2 = n - 1 + (m / 2 - 1))).trans finSumFinEquiv.symm
  let H := pathsLowerGraph (n - 1) (m / 2 - 1)
  refine ⟨H.comap e, fun h ↦ ?_, fun h ↦ ?_⟩
  · exact not_pathGraph_isContained_pathsLowerGraph (by omega) (by omega)
      (h.trans ⟨(Embedding.comap e.toEmbedding H).toCopy⟩)
  · have hc : (H.comap e)ᶜ = Hᶜ.comap e := by
      ext x y; simp [compl_adj, e.injective.ne_iff]
    rw [hc] at h
    exact not_pathGraph_isContained_compl_pathsLowerGraph (by omega)
      (h.trans ⟨(Embedding.comap e.toEmbedding Hᶜ).toCopy⟩)

end Ramsey

end
