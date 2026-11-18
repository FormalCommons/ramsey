module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Powerset

/-!
# Ramsey's theorem for hypergraphs

For all `r`, `k` and `s` there is an `n` such that for every colouring with `k` colours of the
`r`-element subsets of a set of at least `n` elements, there is a set of `s` elements all of whose
`r`-element subsets have the same colour.

## Main results

* `Ramsey.hypergraph_ramsey_of_targets`: the version with a target size `s i` for each colour `i`
  of a finite type of colours `κ`.
* `Ramsey.hypergraph_ramsey_finset`: the milestone, for colourings of the subsets of a `Finset`.
* `Ramsey.hypergraph_ramsey`: the milestone, for colourings of the subsets of a `Fintype`.

Colourings are functions `Finset α → κ`; only their values on sets of card `r` matter.

## Proof

By induction on `r`, and, for each `r`, on the sum of the target sizes. For `r = 0` the colour of
`∅` decides. For `r + 1`, pick a point `x` of a large set `X` and colour each `r`-subset `T` of
`X \ {x}` by the colour of `T ∪ {x}`. By the case `r`, there is a colour `i` and a large set
`Y ⊆ X \ {x}` all of whose `r`-subsets get colour `i`. By induction on the targets, `Y` contains
a homogeneous set of size `s j` in a colour `j ≠ i`, which is what we want, or one `Z` of size
`s i - 1` in colour `i`, and then `Z ∪ {x}` is homogeneous of size `s i` in colour `i`.
This avoids ordering the points.

## References

* F. P. Ramsey, *On a problem of formal logic*, 1930, Theorem B.
* R. L. Graham, B. L. Rothschild, J. H. Spencer, *Ramsey Theory*, 1990, Chapter 1.
-/

public section

namespace Ramsey

universe u

open Finset

/-- The case `r = 0` of `hypergraph_ramsey_of_targets`: the colour of `∅` decides. -/
private theorem hypergraph_ramsey_zero {κ : Type*} [Fintype κ] (s : κ → ℕ) :
    ∃ n, ∀ {α : Type u} (X : Finset α), n ≤ X.card → ∀ c : Finset α → κ,
      ∃ i, ∃ S ⊆ X, S.card = s i ∧ ∀ T ⊆ S, T.card = 0 → c T = i := by
  refine ⟨∑ i, s i, fun X hX c => ⟨c ∅, ?_⟩⟩
  obtain ⟨S, hSX, hS⟩ := Finset.exists_subset_card_eq
    ((Finset.single_le_sum (fun i _ => Nat.zero_le (s i)) (Finset.mem_univ (c ∅))).trans hX)
  refine ⟨S, hSX, hS, fun T _ hT => ?_⟩
  rw [Finset.card_eq_zero.mp hT]

/-- The step from `r` to `r + 1` of `hypergraph_ramsey_of_targets`, by strong induction on the
sum of the targets. -/
private theorem hypergraph_ramsey_succ {κ : Type*} [Fintype κ] (r : ℕ)
    (ih : ∀ s : κ → ℕ, ∃ n, ∀ {α : Type u} (X : Finset α), n ≤ X.card → ∀ c : Finset α → κ,
      ∃ i, ∃ S ⊆ X, S.card = s i ∧ ∀ T ⊆ S, T.card = r → c T = i)
    (m : ℕ) : ∀ s : κ → ℕ, ∑ i, s i = m →
      ∃ n, ∀ {α : Type u} (X : Finset α), n ≤ X.card → ∀ c : Finset α → κ,
        ∃ i, ∃ S ⊆ X, S.card = s i ∧ ∀ T ⊆ S, T.card = r + 1 → c T = i := by
  classical
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro s hsm
  by_cases h0 : ∃ i, s i = 0
  · obtain ⟨i, hi⟩ := h0
    refine ⟨0, fun X _ c => ⟨i, ∅, Finset.empty_subset _, by simp [hi], fun T hT hTc => ?_⟩⟩
    rw [Finset.subset_empty.mp hT] at hTc
    simp at hTc
  push Not at h0
  -- For each colour `i`, the targets with `s i` lowered by one.
  set s' : κ → κ → ℕ := fun i => Function.update s i (s i - 1) with hs'
  have hlt : ∀ i, ∑ j, s' i j < m := fun i => by
    rw [← hsm]
    refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
    · rcases eq_or_ne j i with rfl | hji
      · simp [hs']
      · simp [hs', Function.update_of_ne hji]
    · have := h0 i
      simp [hs']
      omega
  choose N hN using fun i => ihm _ (hlt i) (s' i) rfl
  obtain ⟨n₀, hn₀⟩ := ih N
  refine ⟨n₀ + 1, fun {α} X hX c => ?_⟩
  obtain ⟨x, hx⟩ : X.Nonempty := Finset.card_pos.mp (by omega)
  have hX' : n₀ ≤ (X.erase x).card := by rw [Finset.card_erase_of_mem hx]; omega
  obtain ⟨i, Y, hYX, hY, hYc⟩ := hn₀ (X.erase x) hX' (fun T => c (insert x T))
  obtain ⟨j, Z, hZY, hZ, hZc⟩ := hN i Y hY.ge c
  rcases eq_or_ne j i with rfl | hji
  · -- `Z` is homogeneous of size `s j - 1` in colour `j`; add `x`.
    have hxZ : x ∉ Z := fun h => by simpa using hYX (hZY h)
    refine ⟨j, insert x Z, Finset.insert_subset hx (hZY.trans (hYX.trans
      (Finset.erase_subset x X))), ?_, fun T hT hTc => ?_⟩
    · rw [Finset.card_insert_of_notMem hxZ, hZ]
      have := h0 j
      simp [hs']
      omega
    · by_cases hxT : x ∈ T
      · rw [← Finset.insert_erase hxT]
        refine hYc _ (fun y hy => hZY ?_) ?_
        · have hy' := hT (Finset.mem_of_mem_erase hy)
          rcases Finset.mem_insert.mp hy' with rfl | hy'
          · simp at hy
          · exact hy'
        · rw [Finset.card_erase_of_mem hxT, hTc]; rfl
      · exact hZc T (fun y hy => by
          rcases Finset.mem_insert.mp (hT hy) with rfl | hy'
          · exact absurd hy hxT
          · exact hy') hTc
  · -- `Z` is homogeneous of size `s j` in another colour `j`.
    refine ⟨j, Z, hZY.trans (hYX.trans (Finset.erase_subset x X)), ?_, hZc⟩
    rw [hZ]
    simp [hs', Function.update_of_ne hji]

/-- **Ramsey's theorem for hypergraphs**, with a target size for each colour: for every finite
type of colours `κ`, every `r` and all target sizes `s : κ → ℕ`, there is an `n` such that for
every colouring `c` of the subsets of a set `X` of at least `n` elements, there are a colour `i`
and a set `S ⊆ X` of `s i` elements all of whose `r`-element subsets have colour `i`. -/
theorem hypergraph_ramsey_of_targets {κ : Type*} [Fintype κ] (r : ℕ) (s : κ → ℕ) :
    ∃ n, ∀ {α : Type u} (X : Finset α), n ≤ X.card → ∀ c : Finset α → κ,
      ∃ i, ∃ S ⊆ X, S.card = s i ∧ ∀ T ∈ S.powersetCard r, c T = i := by
  suffices h : ∀ s : κ → ℕ, ∃ n, ∀ {α : Type u} (X : Finset α), n ≤ X.card →
      ∀ c : Finset α → κ, ∃ i, ∃ S ⊆ X, S.card = s i ∧ ∀ T ⊆ S, T.card = r → c T = i by
    obtain ⟨n, hn⟩ := h s
    refine ⟨n, fun X hX c => ?_⟩
    obtain ⟨i, S, hSX, hS, hSc⟩ := hn X hX c
    exact ⟨i, S, hSX, hS, fun T hT => hSc T (Finset.mem_powersetCard.mp hT).1
      (Finset.mem_powersetCard.mp hT).2⟩
  induction r with
  | zero => exact hypergraph_ramsey_zero
  | succ r ih => exact fun s => hypergraph_ramsey_succ r ih _ s rfl

/-- **Ramsey's theorem for hypergraphs**, for subsets of a `Finset`: for all `r`, `k` and `s`
there is an `n` such that for every colouring with `k` colours of the `r`-element subsets of a
set `X` of at least `n` elements, there is a set `S ⊆ X` of `s` elements all of whose `r`-element
subsets have the same colour.

This is the milestone *Ramsey's theorem for hypergraphs*. It holds for all `r`, `k` and `s`, not
only for positive ones. -/
theorem hypergraph_ramsey_finset (r k s : ℕ) :
    ∃ n, ∀ {α : Type u} (X : Finset α), n ≤ X.card → ∀ c : Finset α → Fin k,
      ∃ S ⊆ X, S.card = s ∧ ∃ i, ∀ T ∈ S.powersetCard r, c T = i := by
  obtain ⟨n, hn⟩ := hypergraph_ramsey_of_targets (κ := Fin k) r (fun _ => s)
  refine ⟨n, fun X hX c => ?_⟩
  obtain ⟨i, S, hSX, hS, hSc⟩ := hn X hX c
  exact ⟨S, hSX, hS, i, hSc⟩

/-- **Ramsey's theorem for hypergraphs**, for subsets of a `Fintype`: for all `r`, `k` and `s`
there is an `n` such that for every finite type `V` with at least `n` elements and every
colouring with `k` colours of the `r`-element subsets of `V`, there is a set of `s` elements all
of whose `r`-element subsets have the same colour.

This is the milestone *Ramsey's theorem for hypergraphs*. It holds for all `r`, `k` and `s`, not
only for positive ones. -/
theorem hypergraph_ramsey (r k s : ℕ) :
    ∃ n, ∀ (V : Type u) [Fintype V], n ≤ Fintype.card V → ∀ c : Finset V → Fin k,
      ∃ S : Finset V, S.card = s ∧ ∃ i, ∀ T ∈ S.powersetCard r, c T = i := by
  obtain ⟨n, hn⟩ := hypergraph_ramsey_finset.{u} r k s
  refine ⟨n, fun V _ hV c => ?_⟩
  obtain ⟨S, -, hS, hSc⟩ := hn (Finset.univ : Finset V) (by simpa using hV) c
  exact ⟨S, hS, hSc⟩

end Ramsey

end
