module

public import Mathlib.Analysis.Convex.Independent
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

/-!
# Orientation of three points in the plane

For points `p`, `q`, `r` of `ℝ × ℝ`, `Ramsey.orient p q r` is the determinant
`det (q - p, r - p)`, twice the signed area of the triangle `p q r`: it is positive when the
triangle turns counterclockwise, negative when it turns clockwise, and zero when the three points
are on a line. This file relates it to Mathlib's language of collinearity and convexity, as the
plan's page on geometry suggests, for the milestones *Five points in convex position* and
*The Erdős–Szekeres theorem*.

## Main results

* `Ramsey.collinear_iff_orient_eq_zero`: three points are collinear if and only if their
  orientation is zero.
* `Ramsey.orient_mul_orient_nonneg_of_mem_convexHull`: a point in the convex hull of a triangle is
  weakly on the inner side of each of its edges.
* `Ramsey.notMem_convexHull_of_diagonals_cross`: if the diagonals `p r` and `q s` of a
  quadrilateral `p q r s` cross, none of its four vertices is in the convex hull of the other
  three.
* `Ramsey.convexIndependent_of_notMem_convexHull`, `Ramsey.convexIndependent_of_diagonals_cross`:
  the same, as convex independence of four points of a family.
-/

public section

namespace Ramsey

/-- The orientation of three points of the plane: the determinant of `q - p` and `r - p`. -/
@[expose] def orient (p q r : ℝ × ℝ) : ℝ :=
  (q.1 - p.1) * (r.2 - p.2) - (q.2 - p.2) * (r.1 - p.1)

/-- The orientation is invariant under cyclic permutations. -/
theorem orient_rotate (p q r : ℝ × ℝ) : orient q r p = orient p q r := by
  unfold orient; ring

/-- Swapping two points changes the sign of the orientation. -/
theorem orient_swap (p q r : ℝ × ℝ) : orient q p r = -orient p q r := by
  unfold orient; ring

/-- The orientation vanishes when the first two points are equal. -/
theorem orient_self_left (p q : ℝ × ℝ) : orient p p q = 0 := by
  unfold orient; ring

/-- The orientation vanishes when the last two points are equal. -/
theorem orient_self_right (p q : ℝ × ℝ) : orient p q q = 0 := by
  unfold orient; ring

/-- The orientation is affine in its last argument. -/
theorem orient_add_smul (p q x y : ℝ × ℝ) {s t : ℝ} (h : s + t = 1) :
    orient p q (s • x + t • y) = s * orient p q x + t * orient p q y := by
  obtain rfl : s = 1 - t := by linarith
  simp only [orient, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- Three points of the plane are collinear if and only if their orientation is zero. -/
theorem collinear_iff_orient_eq_zero (p q r : ℝ × ℝ) :
    Collinear ℝ {p, q, r} ↔ orient p q r = 0 := by
  rw [collinear_iff_of_mem (p₀ := p) (by simp)]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨a, rfl⟩ := hv q (by simp)
    obtain ⟨b, rfl⟩ := hv r (by simp)
    simp only [orient, vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]
    ring
  · intro h
    simp only [orient] at h
    have key : ∀ v : ℝ × ℝ, ∀ x ∈ ({p, q, r} : Set (ℝ × ℝ)),
        (∃ t : ℝ, q = t • v +ᵥ p) → (∃ t : ℝ, r = t • v +ᵥ p) → ∃ t : ℝ, x = t • v +ᵥ p := by
      rintro v x hx hq hr
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact hq
      · exact hr
    by_cases hpq : q = p
    · subst hpq
      exact ⟨r - q, fun x hx => key _ x hx ⟨0, by simp⟩ ⟨1, by simp⟩⟩
    refine ⟨q - p, fun x hx => key _ x hx ⟨1, by simp⟩ ?_⟩
    have hne : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
      by_contra! hc
      exact hpq (Prod.ext (by linarith [hc.1]) (by linarith [hc.2]))
    rcases hne with h1 | h2
    · refine ⟨(r.1 - p.1) / (q.1 - p.1), Prod.ext ?_ ?_⟩ <;>
        simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, Prod.fst_sub, Prod.snd_sub] <;>
        field_simp <;> linarith
    · refine ⟨(r.2 - p.2) / (q.2 - p.2), Prod.ext ?_ ?_⟩ <;>
        simp only [vadd_eq_add, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, Prod.fst_sub, Prod.snd_sub] <;>
        field_simp <;> linarith

/-- Three points of the plane that are not collinear have nonzero orientation. -/
theorem orient_ne_zero_of_not_collinear {p q r : ℝ × ℝ} (h : ¬ Collinear ℝ {p, q, r}) :
    orient p q r ≠ 0 :=
  fun h' => h ((collinear_iff_orient_eq_zero p q r).2 h')

/-- A point in the convex hull of the triangle `a b c` is weakly on the same side of each edge
as the opposite vertex. -/
theorem orient_mul_orient_nonneg_of_mem_convexHull {a b c x : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ {a, b, c}) :
    0 ≤ orient a b x * orient a b c ∧ 0 ≤ orient b c x * orient a b c ∧
      0 ≤ orient c a x * orient a b c := by
  refine convexHull_min (t := {x | 0 ≤ orient a b x * orient a b c ∧
    0 ≤ orient b c x * orient a b c ∧ 0 ≤ orient c a x * orient a b c}) ?_ ?_ hx
  · intro y hy
    have h1 : orient b c a = orient a b c := orient_rotate a b c
    have h2 : orient c a b = orient a b c := by unfold orient; ring
    have h3 : orient a b a = 0 := by unfold orient; ring
    have h4 : orient c a c = 0 := by unfold orient; ring
    have h5 : orient b c b = 0 := by unfold orient; ring
    rcases hy with rfl | rfl | rfl <;>
      simp only [Set.mem_ofPred_eq, orient_self_right, zero_mul, le_refl,
        true_and, and_true, h1, h2, h3, h4, h5] <;> exact mul_self_nonneg _
  · intro x hx y hy s t hs ht hst
    simp only [Set.mem_ofPred_eq, orient_add_smul _ _ _ _ hst, add_mul, mul_assoc] at hx hy ⊢
    exact ⟨add_nonneg (mul_nonneg hs hx.1) (mul_nonneg ht hy.1),
      add_nonneg (mul_nonneg hs hx.2.1) (mul_nonneg ht hy.2.1),
      add_nonneg (mul_nonneg hs hx.2.2) (mul_nonneg ht hy.2.2)⟩


/-- If the diagonals `p r` and `q s` of the quadrilateral `p q r s` cross, that is, if `p` and `r`
are strictly on opposite sides of the line `q s`, and `q` and `s` strictly on opposite sides of
the line `p r`, then none of the four points is in the convex hull of the other three. -/
theorem notMem_convexHull_of_diagonals_cross {p q r s : ℝ × ℝ}
    (h₁ : orient q s p * orient q s r < 0) (h₂ : orient p r q * orient p r s < 0) :
    p ∉ convexHull ℝ {q, r, s} ∧ q ∉ convexHull ℝ {p, r, s} ∧ r ∉ convexHull ℝ {p, q, s} ∧
      s ∉ convexHull ℝ {p, q, r} := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := (orient_mul_orient_nonneg_of_mem_convexHull h).2.2
    have e : orient s q p * orient q r s = orient q s p * orient q s r := by unfold orient; ring
    linarith
  · have := (orient_mul_orient_nonneg_of_mem_convexHull h).1
    linarith
  · have := (orient_mul_orient_nonneg_of_mem_convexHull h).2.1
    have e : orient q s r * orient p q s = orient q s p * orient q s r := by unfold orient; ring
    linarith
  · have := (orient_mul_orient_nonneg_of_mem_convexHull h).2.2
    have e : orient r p s * orient p q r = orient p r q * orient p r s := by unfold orient; ring
    linarith

/-- A finite family of points is convex independent if none of them is in the convex hull of the
others. -/
theorem convexIndependent_of_forall_notMem_convexHull_erase {ι : Type*} [DecidableEq ι]
    {p : ι → ℝ × ℝ} {s : Finset ι} (h : ∀ i ∈ s, p i ∉ convexHull ℝ (p '' ↑(s.erase i))) :
    ConvexIndependent ℝ (fun i : s => p i) := by
  rw [convexIndependent_iff_notMem_convexHull_sdiff]
  intro i t hi
  refine h i i.2 (convexHull_mono ?_ hi)
  rintro _ ⟨j, hj, rfl⟩
  refine ⟨j, ?_, rfl⟩
  have hji : j ≠ i := hj.2
  exact Finset.mem_coe.2 (Finset.mem_erase.2 ⟨fun e => hji (Subtype.ext e), j.2⟩)

/-- Four points `p i`, `p j`, `p k`, `p l` of the plane, none of which is in the convex hull of the
other three, are in convex position. -/
theorem convexIndependent_of_notMem_convexHull {ι : Type*} [DecidableEq ι] {p : ι → ℝ × ℝ}
    {i j k l : ι} (hi : p i ∉ convexHull ℝ {p j, p k, p l})
    (hj : p j ∉ convexHull ℝ {p i, p k, p l}) (hk : p k ∉ convexHull ℝ {p i, p j, p l})
    (hl : p l ∉ convexHull ℝ {p i, p j, p k}) :
    ConvexIndependent ℝ (fun x : ({i, j, k, l} : Finset ι) => p x) := by
  apply convexIndependent_of_forall_notMem_convexHull_erase
  intro x hx hmem
  have hsub : ∀ t : Set (ℝ × ℝ), (∀ y ∈ ({i, j, k, l} : Finset ι), y ≠ x → p y ∈ t) →
      p '' ↑(({i, j, k, l} : Finset ι).erase x) ⊆ t := by
    rintro t ht _ ⟨y, hy, rfl⟩
    rw [Finset.mem_coe, Finset.mem_erase] at hy
    exact ht y hy.2 hy.1
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · refine hi (convexHull_mono (hsub _ fun y hy hyx => ?_) hmem)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hyx | simp
  · refine hj (convexHull_mono (hsub _ fun y hy hyx => ?_) hmem)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hyx | simp
  · refine hk (convexHull_mono (hsub _ fun y hy hyx => ?_) hmem)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hyx | simp
  · refine hl (convexHull_mono (hsub _ fun y hy hyx => ?_) hmem)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hyx | simp

/-- Four points `p i`, `p j`, `p k`, `p l` of the plane, the vertices of a quadrilateral whose
diagonals `p i p k` and `p j p l` cross, are in convex position. -/
theorem convexIndependent_of_diagonals_cross {ι : Type*} [DecidableEq ι] {p : ι → ℝ × ℝ}
    {i j k l : ι} (h₁ : orient (p j) (p l) (p i) * orient (p j) (p l) (p k) < 0)
    (h₂ : orient (p i) (p k) (p j) * orient (p i) (p k) (p l) < 0) :
    ConvexIndependent ℝ (fun x : ({i, j, k, l} : Finset ι) => p x) :=
  have h := notMem_convexHull_of_diagonals_cross h₁ h₂
  convexIndependent_of_notMem_convexHull h.1 h.2.1 h.2.2.1 h.2.2.2

end Ramsey

end
