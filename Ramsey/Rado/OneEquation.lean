module

public import Ramsey.Rado.Basic
public import Ramsey.Rado.StrongVdW
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination

/-!
# Rado's theorem for one equation

This file proves the "if" direction of Rado's theorem for one equation, and the theorem itself:
for nonzero integer coefficients `a i`, `n ≥ 1`, the equation `∑ i, a i * x i = 0` is partition
regular if and only if some nonempty subset of the coefficients sums to zero.

## Main results

* `Ramsey.partitionRegular_of_exists_subset_sum_eq_zero`: the "if" direction.
* `Ramsey.partitionRegular_iff`: Rado's theorem for one equation.

## Proof

Let `I` be nonempty with `∑ i ∈ I, a i = 0`, fix `i₀ ∈ I`, let `A = ∑ j ∉ I, a j` and
`s = |a i₀|`. Choose `λ i₀ = |A| ∓ A` (with the sign of `a i₀`) and `λ i = |A|` for the other
`i ∈ I`, so that `0 ≤ λ i ≤ 2 |A|` and, since `∑ i ∈ I, a i = 0`,
`∑ i ∈ I, a i * λ i = -s * A`. The strengthened van der Waerden theorem with `l = 2 |A|` gives
`a, a + d, …, a + l d` and `s d` of one colour, and `x i = a + λ i * d` for `i ∈ I`,
`x j = s d` for `j ∉ I` is a monochromatic solution. (The plan takes `s` to be the gcd of the
`a i`, `i ∈ I`; any nonzero multiple of it works, and `|a i₀|` avoids Bézout.)

## References

* B. M. Landman, A. Robertson, *Ramsey Theory on the Integers*, 2nd ed., 2014, Chapter 9.
* R. Rado, *Studien zur Kombinatorik*, Math. Z. 36 (1933), 424–470.
-/

public section

namespace Ramsey

open Finset

/-- **Rado's theorem for one equation, "if" direction.** If the coefficients `a i` are nonzero
and some nonempty subset of them sums to zero, then the equation `∑ i, a i * x i = 0` is
partition regular. (Without `ha` this fails: `0 * x₀ + x₁ = 0` has no positive solution.) -/
theorem partitionRegular_of_exists_subset_sum_eq_zero {n : ℕ} {a : Fin n → ℤ}
    (ha : ∀ i, a i ≠ 0) (h : ∃ I : Finset (Fin n), I.Nonempty ∧ ∑ i ∈ I, a i = 0) :
    PartitionRegular a := by
  classical
  obtain ⟨I, ⟨i₀, hi₀⟩, hI⟩ := h
  intro r C
  set A : ℤ := ∑ j ∈ Iᶜ, a j with hA
  set s : ℕ := (a i₀).natAbs with hs
  set m : ℤ := if 0 < a i₀ then -A else A with hm
  have ham : a i₀ * m = -(s * A) := by
    rw [hs, Int.natCast_natAbs, hm]
    split_ifs with h0
    · rw [abs_of_pos h0]; ring
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp h0) (ha i₀))]; ring
  have hmA : -|A| ≤ m ∧ m ≤ |A| := by
    rw [hm]; split_ifs
    · constructor <;> linarith [neg_abs_le A, le_abs_self A]
    · exact ⟨neg_abs_le A, le_abs_self A⟩
  set μ : Fin n → ℕ := fun i => if i = i₀ then (|A| + m).toNat else |A|.toNat with hμdef
  have hμ : ∀ i, (μ i : ℤ) = |A| + if i = i₀ then m else 0 := by
    intro i
    simp only [hμdef]
    split_ifs
    · exact Int.toNat_of_nonneg (by linarith [hmA.1])
    · simp
  set l : ℕ := 2 * |A|.toNat with hl
  have hμl : ∀ i, μ i ≤ l := by
    intro i
    have h1 := hμ i
    have h2 : (|A|.toNat : ℤ) = |A| := Int.toNat_of_nonneg (abs_nonneg A)
    have : (μ i : ℤ) ≤ l := by
      rw [h1, hl]; push_cast; rw [h2]
      split_ifs <;> linarith [hmA.2, abs_nonneg A]
    exact_mod_cast this
  have hs0 : 0 < s := Int.natAbs_pos.mpr (ha i₀)
  obtain ⟨N, hN⟩ := exists_mono_arithProg_and_mul r l s hs0
  obtain ⟨b, d, -, c, hprog, hsd, hc⟩ := hN C
  refine ⟨fun i => if i ∈ I then b + μ i * d else s * d, fun i => ?_, ⟨c, fun i => ?_⟩, ?_⟩
  · dsimp only
    split_ifs
    · exact (Finset.mem_Icc.mp (hprog _ (hμl i)).1).1
    · exact (Finset.mem_Icc.mp hsd).1
  · dsimp only
    split_ifs
    · exact (hprog _ (hμl i)).2
    · exact hc
  · rw [← Finset.sum_add_sum_compl I]
    have h1 : ∑ i ∈ I, a i * ((if i ∈ I then b + μ i * d else s * d : ℕ) : ℤ) =
        (b + |A| * d) * ∑ i ∈ I, a i + d * ∑ i ∈ I, a i * (if i = i₀ then m else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ite_eq_left hi]; push_cast; rw [hμ i]; ring
    have h2 : ∑ i ∈ Iᶜ, a i * ((if i ∈ I then b + μ i * d else s * d : ℕ) : ℤ) =
        (s * d : ℤ) * A := by
      rw [hA, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [ite_eq_right (Finset.mem_compl.mp hi)]; push_cast; ring
    rw [h1, h2, hI]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', ite_eq_left hi₀]
    linear_combination (d : ℤ) * ham

/-- **Rado's theorem for one equation.** For `n ≥ 1` and nonzero integer coefficients `a i`, the
equation `∑ i, a i * x i = 0` is partition regular if and only if some nonempty subset of the
coefficients sums to zero.

This is the milestone *Rado's theorem for one equation*. -/
theorem partitionRegular_iff {n : ℕ} {a : Fin n → ℤ} (hn : 0 < n) (ha : ∀ i, a i ≠ 0) :
    PartitionRegular a ↔ ∃ I : Finset (Fin n), I.Nonempty ∧ ∑ i ∈ I, a i = 0 :=
  ⟨exists_subset_sum_eq_zero_of_partitionRegular hn ha,
    partitionRegular_of_exists_subset_sum_eq_zero ha⟩

end Ramsey

end
