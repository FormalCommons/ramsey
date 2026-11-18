module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases

/-!
# W(3;2) = 9

This file formalizes the milestone *W(3;2) = 9* of the plan's page on the integers: every colouring
of `[9] = {1, …, 9}` with 2 colours has a monochromatic arithmetic progression of length 3, and the
colouring red, red, blue, blue, red, red, blue, blue of `[8]` has none.

A colouring of `[n]` with 2 colours is a function `ℕ → Fin 2`, of which only the values at
`1, …, n` matter.

## Main definitions

* `Ramsey.HasMonoThreeAP c n`: the colouring `c` has a monochromatic arithmetic progression
  `a, a + d, a + 2d` with `d ≥ 1` in `[n]`.
* `Ramsey.rrbbColouring`: the colouring red, red, blue, blue, … with period 4.

## Main results

* `Ramsey.hasMonoThreeAP_nine`: the upper half.
* `Ramsey.not_hasMonoThreeAP_rrbbColouring_eight`: the lower half.
* `Ramsey.vanDerWaerden_three_two`: both halves together, the milestone.

The upper half is a check of all `2^9 = 512` colourings of `[9]`, done by `decide` on a Boolean
function of nine Booleans; the kernel evaluates it in well under a second.

## References

* B. M. Landman and A. Robertson, *Ramsey Theory on the Integers*, 2nd ed. (2014), Ch. 2.
-/

public section

namespace Ramsey

/-- The colouring `c` of the positive integers has a monochromatic arithmetic progression of
length 3 in `[n] = {1, …, n}`: there are `a ≥ 1` and `d ≥ 1` with `a + 2d ≤ n` such that `a`,
`a + d` and `a + 2d` have the same colour. -/
def HasMonoThreeAP {α : Type*} (c : ℕ → α) (n : ℕ) : Prop :=
  ∃ a d, 1 ≤ a ∧ 1 ≤ d ∧ a + 2 * d ≤ n ∧ c a = c (a + d) ∧ c (a + d) = c (a + 2 * d)

/-- The colouring red, red, blue, blue, red, red, blue, blue, … of the positive integers, with red
`0` and blue `1`: `i` is red when `i % 4` is `1` or `2`. -/
def rrbbColouring (i : ℕ) : Fin 2 :=
  if i % 4 = 1 ∨ i % 4 = 2 then 0 else 1

/-- Whether the colours `x₁, …, x₉` of `1, …, 9` contain a monochromatic arithmetic progression of
length 3: one disjunct for each of the 16 progressions in `[9]`. -/
private def monoThreeAPNine (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : Bool) : Bool :=
  (x₁ == x₂ && x₂ == x₃) || (x₂ == x₃ && x₃ == x₄) || (x₃ == x₄ && x₄ == x₅) ||
  (x₄ == x₅ && x₅ == x₆) || (x₅ == x₆ && x₆ == x₇) || (x₆ == x₇ && x₇ == x₈) ||
  (x₇ == x₈ && x₈ == x₉) || (x₁ == x₃ && x₃ == x₅) || (x₂ == x₄ && x₄ == x₆) ||
  (x₃ == x₅ && x₅ == x₇) || (x₄ == x₆ && x₆ == x₈) || (x₅ == x₇ && x₇ == x₉) ||
  (x₁ == x₄ && x₄ == x₇) || (x₂ == x₅ && x₅ == x₈) || (x₃ == x₆ && x₆ == x₉) ||
  (x₁ == x₅ && x₅ == x₉)

/-- Every 2-colouring of `[9]` has a monochromatic progression of length 3, as a Boolean check of
all 512 colourings. -/
private lemma monoThreeAPNine_eq_true :
    ∀ x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : Bool, monoThreeAPNine x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ = true := by
  decide

/-- Two colours in `Fin 2` are equal if and only if they agree on being `0`. -/
private lemma fin_two_eq_iff {x y : Fin 2} : x = y ↔ decide (x = 0) = decide (y = 0) := by
  fin_cases x <;> fin_cases y <;> decide

/-- The upper half of the milestone *W(3;2) = 9*: every colouring of `[9]` with 2 colours has a
monochromatic arithmetic progression of length 3. -/
theorem hasMonoThreeAP_nine (c : ℕ → Fin 2) : HasMonoThreeAP c 9 := by
  have h := monoThreeAPNine_eq_true (c 1 = 0) (c 2 = 0) (c 3 = 0) (c 4 = 0) (c 5 = 0) (c 6 = 0)
    (c 7 = 0) (c 8 = 0) (c 9 = 0)
  simp only [monoThreeAPNine, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    ← fin_two_eq_iff, or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨1, 1, le_rfl, le_rfl, by decide, h⟩
  · exact ⟨2, 1, by decide, le_rfl, by decide, h⟩
  · exact ⟨3, 1, by decide, le_rfl, by decide, h⟩
  · exact ⟨4, 1, by decide, le_rfl, by decide, h⟩
  · exact ⟨5, 1, by decide, le_rfl, by decide, h⟩
  · exact ⟨6, 1, by decide, le_rfl, by decide, h⟩
  · exact ⟨7, 1, by decide, le_rfl, by decide, h⟩
  · exact ⟨1, 2, le_rfl, by decide, by decide, h⟩
  · exact ⟨2, 2, by decide, by decide, by decide, h⟩
  · exact ⟨3, 2, by decide, by decide, by decide, h⟩
  · exact ⟨4, 2, by decide, by decide, by decide, h⟩
  · exact ⟨5, 2, by decide, by decide, by decide, h⟩
  · exact ⟨1, 3, le_rfl, by decide, by decide, h⟩
  · exact ⟨2, 3, by decide, by decide, by decide, h⟩
  · exact ⟨3, 3, by decide, by decide, by decide, h⟩
  · exact ⟨1, 4, le_rfl, by decide, by decide, h⟩

/-- The lower half of the milestone *W(3;2) = 9*: the colouring red, red, blue, blue, red, red,
blue, blue of `[8]` has no monochromatic arithmetic progression of length 3. -/
theorem not_hasMonoThreeAP_rrbbColouring_eight : ¬ HasMonoThreeAP rrbbColouring 8 := by
  rintro ⟨a, d, ha, hd, hn, h₁, h₂⟩
  have hd' : d ≤ 3 := by omega
  have ha' : a ≤ 6 := by omega
  interval_cases d <;> interval_cases a <;> simp_all [rrbbColouring]

/-- The milestone *W(3;2) = 9*: every colouring of `[9]` with 2 colours has a monochromatic
arithmetic progression of length 3, and the colouring red, red, blue, blue, red, red, blue, blue
of `[8]` has none. -/
theorem vanDerWaerden_three_two :
    (∀ c : ℕ → Fin 2, HasMonoThreeAP c 9) ∧ ¬ HasMonoThreeAP rrbbColouring 8 :=
  ⟨hasMonoThreeAP_nine, not_hasMonoThreeAP_rrbbColouring_eight⟩

end Ramsey

end
