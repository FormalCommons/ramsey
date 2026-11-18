module

public import Ramsey.GraphRamsey.PathsLower
public import Ramsey.GraphRamsey.PathRamseyUpper

/-!
# Ramsey numbers of paths

Let `P_k` be the path on `k` vertices, `SimpleGraph.pathGraph k`. For `n ≥ m ≥ 2`,
`R(P_n, P_m) = n + ⌊m/2⌋ - 1`.

## Main results

* `Ramsey.paths`: the milestone *Paths*, with both halves.

## Proof

The upper half is `Ramsey.pathGraph_ramsey_upper` (Gerencsér–Gyárfás), and the lower half is
`Ramsey.pathGraph_ramsey_lower`: the complete graph on `n - 1` vertices together with
`⌊m/2⌋ - 1` isolated vertices.

## References

* L. Gerencsér, A. Gyárfás, *On Ramsey-type problems*, Ann. Univ. Sci. Budapest. Eötvös Sect.
  Math. 10 (1967), 167–170.
-/

public section

namespace Ramsey

open SimpleGraph

/-- The milestone *Paths*: for `n ≥ m ≥ 2`, `R(P_n, P_m) = n + ⌊m/2⌋ - 1`, where
`P_k = SimpleGraph.pathGraph k`. That is, every graph on `n + ⌊m/2⌋ - 1` vertices contains `P_n`
or its complement contains `P_m`, and some graph on `n + ⌊m/2⌋ - 2` vertices does neither. -/
theorem paths {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) :
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n + m / 2 - 1 → pathGraph n ⊑ G ∨ pathGraph m ⊑ Gᶜ) ∧
    ∃ G : SimpleGraph (Fin (n + m / 2 - 2)), ¬ pathGraph n ⊑ G ∧ ¬ pathGraph m ⊑ Gᶜ :=
  ⟨fun G hV ↦ pathGraph_ramsey_upper hm hmn hV G, pathGraph_ramsey_lower hm hmn⟩

end Ramsey

end
