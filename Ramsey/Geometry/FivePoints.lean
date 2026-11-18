module

public import Ramsey.Geometry.Orientation

/-!
# Five points in convex position

This file formalizes the milestone *Five points in convex position* of the plan's page on
geometry: among any five points of the plane in general position, there are four in convex
position. Erdős and Szekeres credit it to Esther Klein.

## Main results

* `Ramsey.exists_card_eq_four_convexIndependent`: the milestone.

## Proof

Among the first four points, either none is in the convex hull of the other three, and these four
are in convex position, or one of them, `d`, is in the triangle `a b c` of the other three. Let
`e` be the fifth point; the proof locates it with the signs of orientations.

* If `e` is beyond exactly one edge of the triangle `a b c`, then `a`, `b`, `c` and `e` are in
  convex position.
* If `e` is inside the triangle, then the line `d e` has two of `a`, `b`, `c` on the same side,
  and those two together with `d` and `e` are in convex position.
* Otherwise `e` is beyond a vertex of the triangle, say `a`, so `a` is in the triangle `e b c`.
  The line `a d` separates `b` from `c`, and `e` is on the side of one of them; that one, with
  `a`, `d` and `e`, is in convex position.

In each case the four points are shown to be in convex position by
`Ramsey.convexIndependent_of_diagonals_cross`: the diagonals of the quadrilateral they form cross.

## References

* P. Erdős and G. Szekeres, *A combinatorial problem in geometry*, Compositio Math. 2 (1935).
-/

public section

namespace Ramsey

variable {p : Fin 5 → ℝ × ℝ}

/-- Four distinct indices whose points form a quadrilateral with crossing diagonals give four
points in convex position. -/
private theorem exists_of_cross {i j k l : Fin 5} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (h₁ : orient (p j) (p l) (p i) * orient (p j) (p l) (p k) < 0)
    (h₂ : orient (p i) (p k) (p j) * orient (p i) (p k) (p l) < 0) :
    ∃ s : Finset (Fin 5), s.card = 4 ∧ ConvexIndependent ℝ (fun i : s => p i) :=
  ⟨{i, j, k, l}, by simp [Finset.card_insert_of_notMem, *],
    convexIndependent_of_diagonals_cross h₁ h₂⟩

/-- Closes a goal `0 < a * b` or `a * b < 0` from hypotheses on the signs of `a` and `b`. -/
local macro "sign" : tactic =>
  `(tactic| first
    | exact mul_pos ‹_› ‹_› | exact mul_neg_of_pos_of_neg ‹_› ‹_›
    | exact mul_neg_of_neg_of_pos ‹_› ‹_› | exact mul_pos_of_neg_of_neg ‹_› ‹_›)

set_option hygiene false in
/-- Applies `exists_of_cross` to the quadrilateral of the four given indices, in this order, in
the proof of `exists_of_mem_convexHull_of_pos`. -/
local macro "quad " i:term:max j:term:max k:term:max l:term:max : tactic =>
  `(tactic| exact exists_of_cross (i := $i) (j := $j) (k := $k) (l := $l)
    (by first | assumption | exact Ne.symm ‹_›) (by first | assumption | exact Ne.symm ‹_›)
    (by first | assumption | exact Ne.symm ‹_›) (by first | assumption | exact Ne.symm ‹_›)
    (by first | assumption | exact Ne.symm ‹_›) (by first | assumption | exact Ne.symm ‹_›)
    (by simp only [*, neg_mul, mul_neg, neg_neg, neg_lt_zero]; sign)
    (by simp only [*, neg_mul, mul_neg, neg_neg, neg_lt_zero]; sign))

/-- The case analysis, when `p d` is in the triangle `p a p b p c`, which turns counterclockwise. -/
private theorem exists_of_mem_convexHull_of_pos {a b c d e : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hp : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → orient (p i) (p j) (p k) ≠ 0)
    (hΔ : 0 < orient (p a) (p b) (p c)) (hd : p d ∈ convexHull ℝ {p a, p b, p c}) :
    ∃ s : Finset (Fin 5), s.card = 4 ∧ ConvexIndependent ℝ (fun i : s => p i) := by
  obtain ⟨hG, hA, hB⟩ := orient_mul_orient_nonneg_of_mem_convexHull hd
  set Δ := orient (p a) (p b) (p c) with hΔdef
  -- the barycentric coordinates of `p d`, times `Δ`
  set A := orient (p b) (p c) (p d) with hAdef
  set B := orient (p c) (p a) (p d) with hBdef
  set G := orient (p a) (p b) (p d) with hGdef
  -- the barycentric coordinates of `p e`, times `Δ`
  set x := orient (p b) (p c) (p e) with hxdef
  set y := orient (p c) (p a) (p e) with hydef
  set z := orient (p a) (p b) (p e) with hzdef
  -- the sides of the line `p d p e` on which `p a`, `p b`, `p c` are
  set u := orient (p a) (p d) (p e) with hudef
  set v := orient (p b) (p d) (p e) with hvdef
  set w := orient (p c) (p d) (p e) with hwdef
  have hA0 : 0 < A := pos_of_mul_pos_left (lt_of_le_of_ne hA
    (mul_ne_zero (hp b c d hbc hbd hcd) hΔ.ne').symm) hΔ.le
  have hB0 : 0 < B := pos_of_mul_pos_left (lt_of_le_of_ne hB
    (mul_ne_zero (hp c a d hac.symm hcd had) hΔ.ne').symm) hΔ.le
  have hG0 : 0 < G := pos_of_mul_pos_left (lt_of_le_of_ne hG
    (mul_ne_zero (hp a b d hab had hbd) hΔ.ne').symm) hΔ.le
  have hx0 : x ≠ 0 := hp b c e hbc hbe hce
  have hy0 : y ≠ 0 := hp c a e hac.symm hce hae
  have hz0 : z ≠ 0 := hp a b e hab hae hbe
  have hu0 : u ≠ 0 := hp a d e had hae hde
  have hv0 : v ≠ 0 := hp b d e hbd hbe hde
  have hw0 : w ≠ 0 := hp c d e hcd hce hde
  have hsum : x + y + z = Δ := by simp only [hxdef, hydef, hzdef, hΔdef, orient]; ring
  have hu' : Δ * u = B * z - G * y := by
    simp only [hudef, hBdef, hzdef, hGdef, hydef, hΔdef, orient]; ring
  have hv' : Δ * v = G * x - A * z := by
    simp only [hvdef, hGdef, hxdef, hAdef, hzdef, hΔdef, orient]; ring
  have hw' : Δ * w = A * y - B * x := by
    simp only [hwdef, hAdef, hydef, hBdef, hxdef, hΔdef, orient]; ring
  -- every orientation of three of the points, as one of the ten above or its negation, for `quad`
  have r : ∀ {i j k : Fin 5} {t : ℝ}, orient (p i) (p j) (p k) = t →
      orient (p j) (p k) (p i) = t ∧ orient (p j) (p i) (p k) = -t := fun h =>
    ⟨(orient_rotate _ _ _).trans h, (orient_swap _ _ _).trans (congrArg _ h)⟩
  have r6 : ∀ {i j k : Fin 5} {t : ℝ}, orient (p i) (p j) (p k) = t →
      orient (p i) (p j) (p k) = t ∧ orient (p j) (p k) (p i) = t ∧
      orient (p k) (p i) (p j) = t ∧ orient (p j) (p i) (p k) = -t ∧
      orient (p k) (p j) (p i) = -t ∧ orient (p i) (p k) (p j) = -t := fun h =>
    ⟨h, (r h).1, (r (r h).1).1, (r h).2, (r (r h).1).2, (r (r (r h).1).1).2⟩
  obtain ⟨rΔ₀, rΔ₁, rΔ₂, rΔ₃, rΔ₄, rΔ₅⟩ := r6 hΔdef.symm
  obtain ⟨rA₀, rA₁, rA₂, rA₃, rA₄, rA₅⟩ := r6 hAdef.symm
  obtain ⟨rB₀, rB₁, rB₂, rB₃, rB₄, rB₅⟩ := r6 hBdef.symm
  obtain ⟨rG₀, rG₁, rG₂, rG₃, rG₄, rG₅⟩ := r6 hGdef.symm
  obtain ⟨rx₀, rx₁, rx₂, rx₃, rx₄, rx₅⟩ := r6 hxdef.symm
  obtain ⟨ry₀, ry₁, ry₂, ry₃, ry₄, ry₅⟩ := r6 hydef.symm
  obtain ⟨rz₀, rz₁, rz₂, rz₃, rz₄, rz₅⟩ := r6 hzdef.symm
  obtain ⟨ru₀, ru₁, ru₂, ru₃, ru₄, ru₅⟩ := r6 hudef.symm
  obtain ⟨rv₀, rv₁, rv₂, rv₃, rv₄, rv₅⟩ := r6 hvdef.symm
  obtain ⟨rw₀, rw₁, rw₂, rw₃, rw₄, rw₅⟩ := r6 hwdef.symm
  clear_value Δ A B G x y z u v w
  clear r r6 hd hΔdef hAdef hBdef hGdef hxdef hydef hzdef hudef hvdef hwdef
  rcases hx0.lt_or_gt with hx | hx <;> rcases hy0.lt_or_gt with hy | hy <;>
    rcases hz0.lt_or_gt with hz | hz
  · -- `e` is beyond no edge and no vertex: impossible
    linarith only [hsum, hx, hy, hz, hΔ]
  · -- `e` is beyond the vertex `c`
    have hv : v < 0 :=
      neg_of_mul_neg_right (by
        rw [hv']; linarith only [mul_neg_of_pos_of_neg hG0 hx, mul_pos hA0 hz]) hΔ.le
    have hu : 0 < u :=
      pos_of_mul_pos_right (by
        rw [hu']; linarith only [mul_pos hB0 hz, mul_neg_of_pos_of_neg hG0 hy]) hΔ.le
    rcases hw0.lt_or_gt with hw | hw
    · quad c d a e
    · quad b d c e
  · -- `e` is beyond the vertex `b`
    have hu : u < 0 :=
      neg_of_mul_neg_right (by
        rw [hu']; linarith only [mul_neg_of_pos_of_neg hB0 hz, mul_pos hG0 hy]) hΔ.le
    have hw : 0 < w :=
      pos_of_mul_pos_right (by
        rw [hw']; linarith only [mul_pos hA0 hy, mul_neg_of_pos_of_neg hB0 hx]) hΔ.le
    rcases hv0.lt_or_gt with hv | hv
    · quad b d c e
    · quad a d b e
  · -- `e` is beyond the edge `b c`
    quad b e c a
  · -- `e` is beyond the vertex `a`
    have hw : w < 0 :=
      neg_of_mul_neg_right (by
        rw [hw']; linarith only [mul_neg_of_pos_of_neg hA0 hy, mul_pos hB0 hx]) hΔ.le
    have hv : 0 < v :=
      pos_of_mul_pos_right (by
        rw [hv']; linarith only [mul_pos hG0 hx, mul_neg_of_pos_of_neg hA0 hz]) hΔ.le
    rcases hu0.lt_or_gt with hu | hu
    · quad a d b e
    · quad c d a e
  · -- `e` is beyond the edge `c a`
    quad c e a b
  · -- `e` is beyond the edge `a b`
    quad a e b c
  · -- `e` is inside the triangle: two of `a`, `b`, `c` are on the same side of the line `d e`
    rcases hu0.lt_or_gt with hu | hu <;> rcases hv0.lt_or_gt with hv | hv <;>
      rcases hw0.lt_or_gt with hw | hw
    · quad a b e d
    · quad a b e d
    · quad c a e d
    · quad b c d e
    · quad b c e d
    · quad c a d e
    · quad a b d e
    · quad a b d e

/-- If one of five points in general position is in the triangle of three others, four of the
five points are in convex position. -/
private theorem exists_of_mem_convexHull {a b c d e : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d)
    (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hp : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → orient (p i) (p j) (p k) ≠ 0)
    (hd : p d ∈ convexHull ℝ {p a, p b, p c}) :
    ∃ s : Finset (Fin 5), s.card = 4 ∧ ConvexIndependent ℝ (fun i : s => p i) := by
  rcases (hp a b c hab hac hbc).lt_or_gt with hΔ | hΔ
  · refine exists_of_mem_convexHull_of_pos hac hab had hae hbc.symm hcd hce hbd hbe hde hp ?_ ?_
    · have : orient (p a) (p c) (p b) = -orient (p a) (p b) (p c) := by unfold orient; ring
      linarith
    · rwa [Set.pair_comm]
  · exact exists_of_mem_convexHull_of_pos hab hac had hae hbc hbd hbe hcd hce hde hp hΔ hd

/-- **Five points in convex position** (Esther Klein): among five points of the plane in general
position, no three on a line, there are four in convex position.

This is the milestone *Five points in convex position*. -/
theorem exists_card_eq_four_convexIndependent (p : Fin 5 → ℝ × ℝ)
    (hp : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {p i, p j, p k}) :
    ∃ s : Finset (Fin 5), s.card = 4 ∧ ConvexIndependent ℝ (fun i : s => p i) := by
  have hp' : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → orient (p i) (p j) (p k) ≠ 0 :=
    fun i j k hij hik hjk => orient_ne_zero_of_not_collinear (hp i j k hij hik hjk)
  by_cases h3 : p 3 ∈ convexHull ℝ {p 0, p 1, p 2}
  · exact exists_of_mem_convexHull (d := 3) (e := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hp' h3
  by_cases h2 : p 2 ∈ convexHull ℝ {p 0, p 1, p 3}
  · exact exists_of_mem_convexHull (d := 2) (e := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hp' h2
  by_cases h1 : p 1 ∈ convexHull ℝ {p 0, p 2, p 3}
  · exact exists_of_mem_convexHull (d := 1) (e := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hp' h1
  by_cases h0 : p 0 ∈ convexHull ℝ {p 1, p 2, p 3}
  · exact exists_of_mem_convexHull (d := 0) (e := 4) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hp' h0
  exact ⟨{0, 1, 2, 3}, rfl, convexIndependent_of_notMem_convexHull h0 h1 h2 h3⟩

end Ramsey

end
