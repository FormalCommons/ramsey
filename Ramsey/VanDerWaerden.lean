module

public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Van der Waerden's theorem

This file formalizes the milestone *Van der Waerden's theorem* of the plan's page on the integers:
for all `k` and `r` there is a `W` such that every colouring of `[W] = {1, …, W}` with `r` colours
has a monochromatic arithmetic progression `a, a + d, …, a + (k - 1) d` with `d ≥ 1` inside `[W]`.

A colouring of `[W]` is stated as a function `ℕ → κ`, of which only the values on
`Finset.Icc 1 W` matter.

## Main results

* `Ramsey.exists_mono_arithProg_of_finite`: the theorem for any finite type `κ` of colours.
* `Ramsey.exists_mono_arithProg`: the milestone, for `r` colours `Fin r`.

## Proof

We follow the proof of Mathlib's `Combinatorics.exists_mono_homothetic_copy`, keeping track of
the bound. By the Hales–Jewett theorem `Combinatorics.Line.exists_mono_in_high_dimension` there is
a finite type `ι` such that every `κ`-colouring of `ι → Fin k` has a monochromatic combinatorial
line. Colour a word `v` by the colour of `1 + ∑ i, v i ∈ [W]`, where `W = (k - 1) |ι| + 1`.
Along a line `l`, the word `l x` has sum `b + x d`, where `d ≥ 1` is the number of moving
coordinates of `l` and `b` the sum of its fixed ones; so a monochromatic line gives the
progression `1 + b + x d`, `x < k`.

## References

* B. L. van der Waerden, *Beweis einer Baudetschen Vermutung* (1927).
* R. L. Graham, B. L. Rothschild and J. H. Spencer, *Ramsey Theory*, 2nd ed. (1990), Ch. 2.
-/

public section

namespace Ramsey

open Combinatorics Finset

/-- The sum of the coordinates of a point `l x` of a combinatorial line `l` in `ι → Fin k` is
`b + x * d`, where `b` is the sum of the fixed coordinates of `l` and `d` the number of its moving
coordinates. -/
private lemma sum_line_apply {ι : Type*} [Fintype ι] {k : ℕ} (l : Line (Fin k) ι) (x : Fin k) :
    ∑ i, (l x i : ℕ) = ∑ i, ((l.idxFun i).map (fun y : Fin k ↦ (y : ℕ))).getD 0 +
      x * ∑ i, if l.idxFun i = none then 1 else 0 := by
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [Line.coe_apply]
  cases l.idxFun i <;> simp

/-- **Van der Waerden's theorem**, for any finite type of colours: for every `k` there is a `W`
such that every colouring of `[W] = {1, …, W}` with colours in a finite type `κ` has a
monochromatic arithmetic progression `a + i * d`, `i < k`, with `d ≥ 1`, inside `[W]`. -/
theorem exists_mono_arithProg_of_finite (k : ℕ) (κ : Type*) [Finite κ] :
    ∃ W : ℕ, ∀ C : ℕ → κ, ∃ a d : ℕ, 0 < d ∧ ∃ c : κ,
      ∀ i < k, a + i * d ∈ Finset.Icc 1 W ∧ C (a + i * d) = c := by
  classical
  obtain ⟨ι, _, hι⟩ := Line.exists_mono_in_high_dimension (Fin k) κ
  refine ⟨(k - 1) * Fintype.card ι + 1, fun C ↦ ?_⟩
  obtain ⟨l, c, hl⟩ := hι fun v ↦ C (1 + ∑ i, (v i : ℕ))
  refine ⟨1 + ∑ i, ((l.idxFun i).map (fun y : Fin k ↦ (y : ℕ))).getD 0,
    ∑ i, if l.idxFun i = none then 1 else 0, ?_, c, fun i hi ↦ ?_⟩
  · obtain ⟨j, hj⟩ := l.proper
    exact lt_of_lt_of_le (by simp [hj])
      (single_le_sum (f := fun i ↦ if l.idxFun i = none then 1 else 0)
        (fun _ _ ↦ Nat.zero_le _) (mem_univ j))
  have h := sum_line_apply l ⟨i, hi⟩
  simp only at h
  rw [add_assoc, ← h]
  refine ⟨mem_Icc.2 ⟨Nat.le_add_right _ _, ?_⟩, hl ⟨i, hi⟩⟩
  rw [add_comm 1, add_le_add_iff_right, mul_comm]
  calc ∑ j, (l ⟨i, hi⟩ j : ℕ) ≤ ∑ _j : ι, (k - 1) :=
        sum_le_sum fun j _ ↦ Nat.le_sub_one_of_lt (l ⟨i, hi⟩ j).isLt
    _ = Fintype.card ι * (k - 1) := by simp

/-- **Van der Waerden's theorem**: for all `k` and `r` there is a `W` such that every colouring of
`[W] = {1, …, W}` with `r` colours has a monochromatic arithmetic progression
`a, a + d, …, a + (k - 1) d` with `d ≥ 1` inside `[W]`. The colouring is a function `ℕ → Fin r`,
of which only the values on `[W]` matter.

This is the milestone *Van der Waerden's theorem*. -/
theorem exists_mono_arithProg (k r : ℕ) :
    ∃ W : ℕ, ∀ C : ℕ → Fin r, ∃ a d : ℕ, 0 < d ∧ ∃ c : Fin r,
      ∀ i < k, a + i * d ∈ Finset.Icc 1 W ∧ C (a + i * d) = c :=
  exists_mono_arithProg_of_finite k (Fin r)

end Ramsey

end
