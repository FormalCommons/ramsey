module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring

/-!
# Partition regularity of a linear equation

A linear equation `∑ i, a i * x i = 0` with integer coefficients is *partition regular* if every
colouring of the positive integers with finitely many colours has a monochromatic solution in
positive integers. Rado's theorem for one equation says that, for nonzero coefficients, this
holds if and only if some nonempty subset of the coefficients sums to zero. This file defines
partition regularity and proves the "only if" direction.

## Main definitions

* `Ramsey.PartitionRegular`: the equation `∑ i, a i * x i = 0` is partition regular.

## Main results

* `Ramsey.exists_subset_sum_eq_zero_of_partitionRegular`: if `n ≥ 1`, all `a i` are nonzero
  and the equation is partition regular, then some nonempty subset of the `a i` sums to zero.

## Proof

Take a prime `p > ∑ |a i|` and colour a positive integer `m = p ^ v * y`, with `p ∤ y`, by
`y % p`, its last nonzero digit in base `p`. In a monochromatic solution `x i = p ^ (v i) * y i`
of colour `c ≠ 0`, let `e` be the least `v i` and `I = {i | v i = e}`. Dividing the equation by
`p ^ e` and reducing modulo `p` gives `c * ∑ i ∈ I, a i ≡ 0`, so `p ∣ ∑ i ∈ I, a i`, and since
`|∑ i ∈ I, a i| < p` this sum is `0`.

## References

* B. M. Landman, A. Robertson, *Ramsey Theory on the Integers*, 2nd ed., 2014, Chapter 9.
* R. Rado, *Studien zur Kombinatorik*, Math. Z. 36 (1933), 424–470.
-/

@[expose] public section

namespace Ramsey

/-- The equation `∑ i, a i * x i = 0` is partition regular: every colouring of the positive
integers with finitely many colours has a monochromatic solution in positive integers. -/
def PartitionRegular {n : ℕ} (a : Fin n → ℤ) : Prop :=
  ∀ (r : ℕ) (C : ℕ → Fin r), ∃ x : Fin n → ℕ, (∀ i, 0 < x i) ∧
    (∃ c, ∀ i, C (x i) = c) ∧ ∑ i, a i * (x i : ℤ) = 0

end Ramsey

end

public section

namespace Ramsey

open Finset

/-- **Rado's theorem for one equation, "only if" direction.** If `n ≥ 1`, the coefficients
`a i` are nonzero and the equation `∑ i, a i * x i = 0` is partition regular, then some
nonempty subset of the coefficients sums to zero. The hypothesis `_ha` is part of the statement
of Rado's theorem but is not needed for this direction. -/
theorem exists_subset_sum_eq_zero_of_partitionRegular {n : ℕ} {a : Fin n → ℤ}
    (hn : 0 < n) (_ha : ∀ i, a i ≠ 0) (h : PartitionRegular a) :
    ∃ I : Finset (Fin n), I.Nonempty ∧ ∑ i ∈ I, a i = 0 := by
  obtain ⟨p, hpgt, hp⟩ := Nat.exists_infinite_primes ((∑ i, |a i|).toNat + 1)
  have : Fact p.Prime := ⟨hp⟩
  have hp0 : 0 < p := hp.pos
  obtain ⟨x, hxpos, ⟨c, hc⟩, hsum⟩ :=
    h p fun m => ⟨ordCompl[p] m % p, Nat.mod_lt _ hp0⟩
  -- the valuations and the parts prime to `p`
  set v : Fin n → ℕ := fun i => (x i).factorization p with hv
  set y : Fin n → ℕ := fun i => ordCompl[p] (x i) with hy
  have hxy : ∀ i, x i = p ^ v i * y i := fun i =>
    (Nat.ordProj_mul_ordCompl_eq_self (x i) p).symm
  have hyp : ∀ i, ¬p ∣ y i := fun i => Nat.not_dvd_ordCompl hp (hxpos i).ne'
  -- all `y i` are congruent modulo `p`
  have hyc : ∀ i, (y i : ZMod p) = (c.val : ZMod p) := by
    intro i
    have := congrArg Fin.val (hc i)
    simp only at this
    rw [← this, ZMod.natCast_mod]
  have hc0 : (c.val : ZMod p) ≠ 0 := by
    rw [← hyc ⟨0, hn⟩, Ne, ZMod.natCast_eq_zero_iff]
    exact hyp _
  -- the least valuation
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_min_image Finset.univ v ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  set e := v i₀
  have hve : ∀ i, e ≤ v i := fun i => hi₀ i (Finset.mem_univ _)
  set I : Finset (Fin n) := Finset.univ.filter fun i => v i = e with hI
  refine ⟨I, ⟨i₀, by simp [hI, e]⟩, ?_⟩
  -- divide by `p ^ e`
  have hS : ∑ i, a i * ((p : ℤ) ^ (v i - e) * (y i : ℤ)) = 0 := by
    have hpe : ((p : ℤ) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp0.ne')
    refine (mul_eq_zero.mp ?_).resolve_left hpe
    rw [Finset.mul_sum, ← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hxy i, Nat.cast_mul, Nat.cast_pow, ← Nat.sub_add_cancel (hve i), pow_add,
      Nat.add_sub_cancel]
    ring
  -- reduce modulo `p`
  have hmod : (c.val : ZMod p) * ((∑ i ∈ I, a i : ℤ) : ZMod p) = 0 := by
    have := congrArg (fun z : ℤ => (z : ZMod p)) hS
    simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.natCast_self,
      Int.cast_zero, hyc] at this
    rw [← this, hI, Finset.sum_filter, Int.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hi
    · simp [hi]; ring
    · have : v i - e ≠ 0 := by have := hve i; omega
      simp [zero_pow this]
  have hdvd : (p : ℤ) ∣ ∑ i ∈ I, a i :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ((mul_eq_zero.mp hmod).resolve_left hc0)
  refine Int.eq_zero_of_abs_lt_dvd hdvd ?_
  calc |∑ i ∈ I, a i| ≤ ∑ i ∈ I, |a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        fun i _ _ => abs_nonneg _
    _ ≤ ((∑ i, |a i|).toNat : ℤ) := Int.self_le_toNat _
    _ < p := by omega

end Ramsey

end
