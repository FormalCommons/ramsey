module

public import Ramsey.VanDerWaerden
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The strengthened van der Waerden theorem

This file proves the strengthened van der Waerden theorem used in the "if" direction of
*Rado's theorem for one equation* on the plan's page on the integers: for all `r`, `l` and
`s ≥ 1` there is an `N` such that every colouring of `[N] = {1, …, N}` with `r` colours has
`a, a + d, …, a + l d` and `s d` all of one colour, with `d ≥ 1` and all these numbers in `[N]`.

## Main results

* `Ramsey.exists_mono_arithProg_and_mul_of_finite`: the theorem for any finite type of colours.
* `Ramsey.exists_mono_arithProg_and_mul`: the theorem for `r` colours `Fin r`.

## Proof

We prove, for every finite set `S` of colours, that there is an `N` such that every colouring
of `[N]` with values in `S` has the required configuration, by strong induction on `S`. Let `n`
bound the numbers given by the induction hypothesis for the sets `S.erase c`, `c ∈ S`, and take a
monochromatic progression `a + i d`, `i ≤ l n + 1`, of colour `c` in `[W]` by van der Waerden's
theorem. If some `s j d` with `1 ≤ j ≤ n` has colour `c`, then `a + i (j d)`, `i ≤ l`, and
`s (j d)` work. Otherwise `j ↦ C (s d j)` colours `[n]` with colours in `S.erase c`, and the
configuration it has, scaled by `s d`, works for `C`.

## References

* R. Rado, *Studien zur Kombinatorik* (1933).
* R. L. Graham, B. L. Rothschild and J. H. Spencer, *Ramsey Theory*, 2nd ed. (1990), Ch. 3.
-/

public section

namespace Ramsey

open Finset

/-- The colouring `C` of `[N]` has `a + i d`, `i ≤ l`, and `s d` all of one colour, with `d ≥ 1`
and all these numbers in `[N]`. -/
private def HasConfig {κ : Type*} (l s N : ℕ) (C : ℕ → κ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∃ c : κ,
    (∀ i ≤ l, a + i * d ∈ Finset.Icc 1 N ∧ C (a + i * d) = c) ∧
      s * d ∈ Finset.Icc 1 N ∧ C (s * d) = c

private lemma HasConfig.mono {κ : Type*} {l s N N' : ℕ} {C : ℕ → κ} (h : HasConfig l s N C)
    (hN : N ≤ N') : HasConfig l s N' C := by
  obtain ⟨a, d, hd, c, hp, hsd, hc⟩ := h
  have hsub : Finset.Icc 1 N ⊆ Finset.Icc 1 N' := Finset.Icc_subset_Icc le_rfl hN
  exact ⟨a, d, hd, c, fun i hi ↦ ⟨hsub (hp i hi).1, (hp i hi).2⟩, hsub hsd, hc⟩

/-- The strengthened van der Waerden theorem for colourings with values in a finite set `S`. -/
private lemma exists_hasConfig_of_finset {κ : Type*} [Finite κ] (l s : ℕ) (hs : 0 < s)
    (S : Finset κ) :
    ∃ N : ℕ, ∀ C : ℕ → κ, (∀ x ∈ Finset.Icc 1 N, C x ∈ S) → HasConfig l s N C := by
  classical
  induction S using Finset.strongInduction with
  | H S ih => ?_
  have h : ∀ c ∈ S, ∃ N : ℕ,
      ∀ C : ℕ → κ, (∀ x ∈ Finset.Icc 1 N, C x ∈ S.erase c) → HasConfig l s N C :=
    fun c hc ↦ ih _ (Finset.erase_ssubset hc)
  choose! M hM using h
  set n := S.sup M
  obtain ⟨W, hW⟩ := exists_mono_arithProg_of_finite (l * n + 2) κ
  refine ⟨W + s * n * W, fun C hC ↦ ?_⟩
  obtain ⟨a, d, hd, c, hp⟩ := hW C
  have hWN : Finset.Icc 1 W ⊆ Finset.Icc 1 (W + s * n * W) :=
    Finset.Icc_subset_Icc le_rfl (Nat.le_add_right _ _)
  have ha : a ∈ Finset.Icc 1 W := by simpa using (hp 0 (by omega)).1
  have hcS : c ∈ S := (hp 0 (by omega)).2 ▸ by simpa using hC a (hWN ha)
  -- `d ≤ W`, since `a + (l n + 1) d ∈ [W]`.
  have hdW : d ≤ W := by
    have := (Finset.mem_Icc.1 (hp (l * n + 1) (by omega)).1).2
    have : d ≤ (l * n + 1) * d := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- `s d j ∈ [N]` for `1 ≤ j ≤ n`.
  have hsdj : ∀ j ∈ Finset.Icc 1 n, s * d * j ∈ Finset.Icc 1 (W + s * n * W) := by
    intro j hj
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hj
    refine Finset.mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.2 (by positivity), ?_⟩
    calc s * d * j ≤ s * W * n := Nat.mul_le_mul (Nat.mul_le_mul_left _ hdW) hjn
      _ = s * n * W := by ring
      _ ≤ W + s * n * W := Nat.le_add_left _ _
  unfold HasConfig
  by_cases hj : ∃ j ∈ Finset.Icc 1 n, C (s * d * j) = c
  · obtain ⟨j, hjI, hjc⟩ := hj
    obtain ⟨hj1, hjn⟩ := Finset.mem_Icc.1 hjI
    refine ⟨a, j * d, by positivity, c, fun i hi ↦ ?_, ?_, ?_⟩
    · have hij : i * j < l * n + 2 := by
        have := Nat.mul_le_mul hi hjn
        omega
      have := hp (i * j) hij
      rw [← mul_assoc]
      exact ⟨hWN this.1, this.2⟩
    · rw [show s * (j * d) = s * d * j by ring]
      exact hsdj j hjI
    · rw [show s * (j * d) = s * d * j by ring]
      exact hjc
  · push Not at hj
    have hC' : ∀ x ∈ Finset.Icc 1 (M c), (fun j ↦ C (s * d * j)) x ∈ S.erase c := by
      intro x hx
      have hxn : x ∈ Finset.Icc 1 n :=
        Finset.Icc_subset_Icc le_rfl (Finset.le_sup (f := M) hcS) hx
      exact Finset.mem_erase.2 ⟨hj x hxn, hC _ (hsdj x hxn)⟩
    obtain ⟨a', d', hd', c', hp', hsd', hc'⟩ :=
      (hM c hcS _ hC').mono (Finset.le_sup (f := M) hcS)
    refine ⟨s * d * a', s * d * d', by positivity, c', fun i hi ↦ ?_, ?_, ?_⟩
    · have := hp' i hi
      rw [show s * d * a' + i * (s * d * d') = s * d * (a' + i * d') by ring]
      exact ⟨hsdj _ this.1, this.2⟩
    · rw [show s * (s * d * d') = s * d * (s * d') by ring]
      exact hsdj _ hsd'
    · rw [show s * (s * d * d') = s * d * (s * d') by ring]
      exact hc'

/-- **The strengthened van der Waerden theorem**, for any finite type of colours: for all `l` and
`s ≥ 1` there is an `N` such that every colouring of `[N] = {1, …, N}` with colours in a finite
type `κ` has `a, a + d, …, a + l d` and `s d` all of one colour, with `d ≥ 1` and all these
numbers in `[N]`. -/
theorem exists_mono_arithProg_and_mul_of_finite (l s : ℕ) (hs : 0 < s) (κ : Type*) [Finite κ] :
    ∃ N : ℕ, ∀ C : ℕ → κ, ∃ a d : ℕ, 0 < d ∧ ∃ c : κ,
      (∀ i ≤ l, a + i * d ∈ Finset.Icc 1 N ∧ C (a + i * d) = c) ∧
        s * d ∈ Finset.Icc 1 N ∧ C (s * d) = c := by
  have := Fintype.ofFinite κ
  obtain ⟨N, hN⟩ := exists_hasConfig_of_finset l s hs (Finset.univ : Finset κ)
  exact ⟨N, fun C ↦ hN C fun _ _ ↦ Finset.mem_univ _⟩

/-- **The strengthened van der Waerden theorem**: for all `r`, `l` and `s ≥ 1` there is an `N`
such that every colouring of `[N] = {1, …, N}` with `r` colours has `a, a + d, …, a + l d` and
`s d` all of one colour, with `d ≥ 1` and all these numbers in `[N]`. The colouring is a function
`ℕ → Fin r`, of which only the values on `[N]` matter.

This is the strengthened van der Waerden step of the milestone *Rado's theorem for one
equation*. -/
theorem exists_mono_arithProg_and_mul (r l s : ℕ) (hs : 0 < s) :
    ∃ N : ℕ, ∀ C : ℕ → Fin r, ∃ a d : ℕ, 0 < d ∧ ∃ c : Fin r,
      (∀ i ≤ l, a + i * d ∈ Finset.Icc 1 N ∧ C (a + i * d) = c) ∧
        s * d ∈ Finset.Icc 1 N ∧ C (s * d) = c :=
  exists_mono_arithProg_and_mul_of_finite l s hs (Fin r)

end Ramsey

end
