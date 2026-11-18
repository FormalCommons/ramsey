module

public import Mathlib.Tactic.Ring

/-!
# An example

A placeholder that shows the conventions of `AGENTS.md`. Delete it once the library has files
of its own.

## Main definitions

* `Project.double n`: twice the natural number `n`.

## Main results

* `Project.double_add`: `double` is additive.
-/

@[expose] public section

namespace Project

/-- Twice a natural number. -/
def double (n : ℕ) : ℕ := 2 * n

/-- `double` is additive. -/
theorem double_add (m n : ℕ) : double (m + n) = double m + double n := by
  unfold double
  ring

end Project

end
