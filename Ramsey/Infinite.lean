module

public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Order.Interval.Set.Infinite
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Lattice.Nat

/-!
# The infinite Ramsey theorem

For every `r ≥ 1` and every colouring of the `r`-element subsets of `ℕ` with finitely many
colours, there is an infinite set `A ⊆ ℕ` all of whose `r`-element subsets have the same colour.

## Main results

* `Ramsey.exists_infinite_subset_monochromatic`: the theorem relative to an infinite set
  `S ⊆ ℕ`, for every `r`, including `r = 0`.
* `Ramsey.infinite_ramsey`: the milestone *The infinite Ramsey theorem*.

## Proof

Induction on `r`. For `r + 1`, starting from `X₀ = S`, let `xⱼ = min Xⱼ` and let `Xⱼ₊₁` be an
infinite subset of `Xⱼ ∩ (xⱼ, ∞)` on which `T ↦ c (insert xⱼ T)` is constant on `r`-sets, given
by the case `r`. Then the colour of an `(r + 1)`-subset of `{x₀, x₁, …}` depends only on its
least element, and the infinite pigeonhole principle `Finite.exists_infinite_fiber` gives
infinitely many `xⱼ` of one colour.

## References

* F. P. Ramsey, *On a problem of formal logic*, 1930, Theorem A.
* R. L. Graham, B. L. Rothschild, J. H. Spencer, *Ramsey Theory*, 1990, Chapter 1.
-/

public section

namespace Ramsey

/-- The infinite Ramsey theorem inside an infinite set `S ⊆ ℕ`: for every `r` and every
colouring `c` of the finite subsets of `ℕ` with finitely many colours, there is an infinite
`A ⊆ S` and a colour `i` such that every `r`-element subset of `A` has colour `i`. -/
theorem exists_infinite_subset_monochromatic {κ : Type*} [Finite κ] (r : ℕ) :
    ∀ (c : Finset ℕ → κ) (S : Set ℕ), S.Infinite →
      ∃ A ⊆ S, A.Infinite ∧ ∃ i : κ, ∀ T : Finset ℕ, T.card = r → ↑T ⊆ A → c T = i := by
  induction r with
  | zero =>
    intro c S hS
    refine ⟨S, subset_rfl, hS, c ∅, fun T hT _ => ?_⟩
    rw [Finset.card_eq_zero.mp hT]
  | succ r ih =>
    intro c S hS
    choose F hFsub hFinf col hcol using ih
    -- One step of the construction: from `X`, pass to an infinite subset of the elements of
    -- `X` above `sInf X` on which `T ↦ c (insert (sInf X) T)` is constant on `r`-sets.
    let step : {X : Set ℕ // X.Infinite} → {X : Set ℕ // X.Infinite} := fun X =>
      ⟨F (fun T => c (insert (sInf X.1) T)) (X.1 \ Set.Iic (sInf X.1))
          (X.2.sdiff (Set.finite_Iic _)),
        hFinf _ _ _⟩
    let X : ℕ → {X : Set ℕ // X.Infinite} := fun n => step^[n] ⟨S, hS⟩
    let x : ℕ → ℕ := fun n => sInf (X n).1
    let k : ℕ → κ := fun n => col (fun T => c (insert (x n) T)) ((X n).1 \ Set.Iic (x n))
      ((X n).2.sdiff (Set.finite_Iic _))
    have hXsucc (n : ℕ) : (X (n + 1)).1 ⊆ (X n).1 \ Set.Iic (x n) := by
      change (step^[n + 1] ⟨S, hS⟩).1 ⊆ _
      rw [Function.iterate_succ_apply']
      exact hFsub _ _ _
    have hXanti : Antitone fun n => (X n).1 :=
      antitone_nat_of_succ_le fun n => (hXsucc n).trans Set.sdiff_subset
    have hxmem (n : ℕ) : x n ∈ (X n).1 := Nat.sInf_mem (X n).2.nonempty
    have hxlt {m n : ℕ} (h : m < n) : x m < x n := by
      have := (hXanti (Nat.succ_le_of_lt h)) (hxmem n)
      simpa using (hXsucc m this).2
    have hxinj : Function.Injective x :=
      (strictMono_nat_of_lt_succ fun n => hxlt n.lt_succ_self).injective
    have hcolour (n : ℕ) (T : Finset ℕ) (hT : T.card = r) (hTX : ↑T ⊆ (X (n + 1)).1) :
        c (insert (x n) T) = k n := by
      have h := hcol (fun T => c (insert (x n) T)) ((X n).1 \ Set.Iic (x n))
        ((X n).2.sdiff (Set.finite_Iic _)) T hT
      apply h
      change ↑T ⊆ (step (X n)).1
      have : X (n + 1) = step (X n) := Function.iterate_succ_apply' _ _ _
      rwa [← this]
    obtain ⟨i, hi⟩ := Finite.exists_infinite_fiber k
    have hfib : (k ⁻¹' {i}).Infinite := Set.infinite_coe_iff.mp hi
    refine ⟨x '' (k ⁻¹' {i}), ?_, hfib.image hxinj.injOn, i, fun T hT hTA => ?_⟩
    · rintro _ ⟨n, -, rfl⟩
      exact hXanti (Nat.zero_le n) (hxmem n)
    · have hne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨n, hn, hxn⟩ := hTA (T.min'_mem hne)
      have hTeq : insert (x n) (T.erase (x n)) = T := by
        rw [hxn]; exact Finset.insert_erase (T.min'_mem hne)
      rw [← hTeq, hcolour n _ (by rw [Finset.card_erase_of_mem (hxn ▸ T.min'_mem hne)]; omega)]
      · exact hn
      · intro y hy
        rw [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe] at hy
        obtain ⟨m, -, rfl⟩ := hTA hy.1
        have hle : x n ≤ x m := hxn ▸ T.min'_le _ hy.1
        have hnm : n < m := by
          rcases lt_trichotomy n m with h | rfl | h
          · exact h
          · exact absurd rfl hy.2
          · exact absurd (hxlt h) (not_lt.mpr hle)
        exact hXanti (Nat.succ_le_of_lt hnm) (hxmem m)

/-- **The infinite Ramsey theorem.** For every `r ≥ 1` and every colouring `c` of the finite
subsets of `ℕ` with finitely many colours, there is an infinite set `A ⊆ ℕ` and a colour `i`
such that every `r`-element subset of `A` has colour `i`.

This is the milestone *The infinite Ramsey theorem*. -/
theorem infinite_ramsey {κ : Type*} [Finite κ] (r : ℕ) (_hr : 1 ≤ r) (c : Finset ℕ → κ) :
    ∃ A : Set ℕ, A.Infinite ∧ ∃ i : κ, ∀ T : Finset ℕ, T.card = r → ↑T ⊆ A → c T = i := by
  obtain ⟨A, -, hA, i, hi⟩ :=
    exists_infinite_subset_monochromatic r c Set.univ Set.infinite_univ
  exact ⟨A, hA, i, hi⟩

end Ramsey

end
