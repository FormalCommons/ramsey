module

public import Mathlib.Order.Interval.Finset.Nat

/-!
# Small Schur numbers

A set `A` of natural numbers is *sum-free* if there are no `x, y, z ∈ A` with `x + y = z`
(`x = y` allowed). The Schur number `S(k)` is the largest `n` such that `[n] = {1, …, n}` is
the union of `k` sum-free sets. This file proves `S(2) = 4` and `S(3) ≥ 13`.

## Main definitions

* `Ramsey.IsSumFree`: a finite set `A ⊆ ℕ` is sum-free.

## Main results

* `Ramsey.schur_two_lower`: `[4] = {1, 4} ∪ {2, 3}`, both sum-free.
* `Ramsey.schur_two_upper`: `[5]` is not the union of two sum-free sets.
* `Ramsey.schur_two_upper_colouring`: every colouring of `[5]` with two colours has a
  monochromatic solution of `x + y = z`.
* `Ramsey.schur_three_lower`: `[13] = {1, 4, 10, 13} ∪ {2, 3, 11, 12} ∪ {5, 6, 7, 8, 9}`,
  all three sum-free.

Together these are the milestone *Small Schur numbers*. The upper bound `S(3) ≤ 13` is out of
scope.

## Proof

The constructions are checked by `decide`. For `[5]`: if `1 ∈ A`, then `2 ∈ B` (as
`1 + 1 = 2`), so `4 ∈ A` (as `2 + 2 = 4`), so `3 ∈ B` (as `1 + 3 = 4`), and `5` is neither in
`A` (as `1 + 4 = 5`) nor in `B` (as `2 + 3 = 5`).

## References

* B. M. Landman, A. Robertson, *Ramsey Theory on the Integers*, 2nd ed., 2014, Chapter 8.
-/

@[expose] public section

namespace Ramsey

/-- A finite set `A` of natural numbers is *sum-free* if there are no `x, y ∈ A` with
`x + y ∈ A`; `x = y` is allowed. -/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, x + y ∉ A

instance (A : Finset ℕ) : Decidable (IsSumFree A) := by
  unfold IsSumFree; infer_instance

/-- `[4]` is the union of the two sum-free sets `{1, 4}` and `{2, 3}`, so `S(2) ≥ 4`.
This is part (1) of the milestone *Small Schur numbers*. -/
theorem schur_two_lower :
    IsSumFree {1, 4} ∧ IsSumFree {2, 3} ∧ ({1, 4} ∪ {2, 3} : Finset ℕ) = Finset.Icc 1 4 := by
  decide

/-- If `A` and `B` are sum-free, cover `[5]` and `1 ∈ A`, we have a contradiction. -/
private lemma schur_two_upper_aux {A B : Finset ℕ} (hA : IsSumFree A) (hB : IsSumFree B)
    (hcover : ∀ n, 1 ≤ n → n ≤ 5 → n ∈ A ∨ n ∈ B) (h1 : 1 ∈ A) : False := by
  have h2 : 2 ∈ B := (hcover 2 (by decide) (by decide)).resolve_left (hA 1 h1 1 h1)
  have h4 : 4 ∈ A := (hcover 4 (by decide) (by decide)).resolve_right (hB 2 h2 2 h2)
  have h3 : 3 ∈ B := (hcover 3 (by decide) (by decide)).resolve_left
    fun h3 => hA 1 h1 3 h3 h4
  rcases hcover 5 (by decide) (by decide) with h5 | h5
  · exact hA 1 h1 4 h4 h5
  · exact hB 2 h2 3 h3 h5

/-- `[5]` is not the union of two sum-free sets, so `S(2) ≤ 4`.
This is part (1) of the milestone *Small Schur numbers*. -/
theorem schur_two_upper :
    ¬ ∃ A B : Finset ℕ, IsSumFree A ∧ IsSumFree B ∧ A ∪ B = Finset.Icc 1 5 := by
  rintro ⟨A, B, hA, hB, hAB⟩
  have hcover : ∀ n, 1 ≤ n → n ≤ 5 → n ∈ A ∨ n ∈ B := fun n h1 h5 => by
    rw [← Finset.mem_union, hAB, Finset.mem_Icc]; exact ⟨h1, h5⟩
  rcases hcover 1 le_rfl (by decide) with h1 | h1
  · exact schur_two_upper_aux hA hB hcover h1
  · exact schur_two_upper_aux hB hA (fun n h1 h5 => (hcover n h1 h5).symm) h1

/-- Every colouring of `[5]` with two colours has `x` and `y` such that `x`, `y` and
`x + y` lie in `[5]` and have the same colour (`x = y` allowed). This is the colouring form of
`schur_two_upper`, part (1) of the milestone *Small Schur numbers*. -/
theorem schur_two_upper_colouring (c : ℕ → Fin 2) :
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ 5 ∧ c x = c (x + y) ∧ c y = c (x + y) := by
  by_contra hc
  push Not at hc
  refine schur_two_upper ⟨(Finset.Icc 1 5).filter (c · = 0),
    (Finset.Icc 1 5).filter (c · = 1), ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy hxy
    exact hc x y hx.1.1 hy.1.1 hxy.1.2 (hx.2.trans hxy.2.symm) (hy.2.trans hxy.2.symm)
  · intro x hx y hy hxy
    simp only [Finset.mem_filter, Finset.mem_Icc] at hx hy hxy
    exact hc x y hx.1.1 hy.1.1 hxy.1.2 (hx.2.trans hxy.2.symm) (hy.2.trans hxy.2.symm)
  · ext n
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases Fin.exists_fin_two.mp ⟨c n, rfl⟩ with h0 | h0
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h0⟩

/-- `[13]` is the union of the three sum-free sets `{1, 4, 10, 13}`, `{2, 3, 11, 12}` and
`{5, 6, 7, 8, 9}`, so `S(3) ≥ 13`. This is part (2) of the milestone *Small Schur numbers*. -/
theorem schur_three_lower :
    IsSumFree {1, 4, 10, 13} ∧ IsSumFree {2, 3, 11, 12} ∧ IsSumFree {5, 6, 7, 8, 9} ∧
      ({1, 4, 10, 13} ∪ {2, 3, 11, 12} ∪ {5, 6, 7, 8, 9} : Finset ℕ) = Finset.Icc 1 13 := by
  decide

end Ramsey

end
