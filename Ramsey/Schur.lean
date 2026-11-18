module

public import Ramsey.ManyColours
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Nat.Dist

/-!
# Schur's theorem

This file formalizes the milestone *Schur's theorem* of the plan (`integers.md` in
`FormalCommons/ramsey-plan`).

`[N] = {1, …, N}` is encoded as the natural numbers `n` with `1 ≤ n ≤ N`, or as the finset
`Finset.Icc 1 N`. A colouring of `[N]` with `k` colours is a function `c : ℕ → Fin k`, of which
only the values on `[N]` matter. A monochromatic solution of `x + y = z` in `[N]` is a pair `x`,
`y` with `1 ≤ x`, `1 ≤ y`, `x + y ≤ N` and `c x = c (x + y)`, `c y = c (x + y)`; `x = y` is
allowed.

## Main results

* `Ramsey.schur_of_arrows`: if every colouring of the edges of the complete graph on `N + 1`
  vertices with `k` colours has a monochromatic triangle, then every colouring of `[N]` with `k`
  colours has a monochromatic solution of `x + y = z`.
* `Ramsey.schur_multiRamseyNumber`: one can take `N = R_k(3) - 1`.
* `Ramsey.exists_schur`: Schur's theorem.
* `Ramsey.schur_not_sumFree`, `Ramsey.schur_not_union_sumFree`: the form with sum-free sets:
  `[N]` is not the union of `k` sum-free sets, for `N = R_k(3) - 1`.

## Proof

Given a colouring `c` of `[N]`, colour the edge `{i, j}` of the complete graph on
`Fin (N + 1)`, that is on `{0, …, N}`, by `c |i - j|`. A monochromatic triangle `a < b < d`
gives `x = b - a`, `y = d - b` and `x + y = d - a` of one colour.

## References

* I. Schur, *Über die Kongruenz x^m + y^m ≡ z^m (mod p)* (1916).
* R. L. Graham, B. L. Rothschild, J. H. Spencer, *Ramsey Theory*, Ch. 3.
* B. M. Landman, A. Robertson, *Ramsey Theory on the Integers*, 2nd ed., 2014, Ch. 8.
-/

public section

open SimpleGraph Finset

namespace Ramsey

variable {k : ℕ}

/-- The colouring of the edges of the complete graph on `Fin n` that gives the edge `{i, j}`
the colour `c |i - j|`. -/
def distColouring (n : ℕ) (c : ℕ → Fin k) : TopEdgeLabeling (Fin n) (Fin k) :=
  EdgeLabeling.mk (fun i j _ ↦ c (Nat.dist i j)) fun i j _ ↦ by rw [Nat.dist_comm]

theorem distColouring_labelGraph_adj {n : ℕ} {c : ℕ → Fin k} {l : Fin k} {i j : Fin n} :
    ((distColouring n c).labelGraph l).Adj i j ↔ i ≠ j ∧ c (Nat.dist i j) = l := by
  rw [TopEdgeLabeling.labelGraph_adj]
  exact ⟨fun ⟨H, h⟩ ↦ ⟨H, h⟩, fun ⟨H, h⟩ ↦ ⟨H, h⟩⟩

/-- Three numbers `a < b < d ≤ N` whose pairwise distances have one colour give a
monochromatic solution of `x + y = z` in `[N]`. -/
private lemma schur_of_lt {N : ℕ} {c : ℕ → Fin k} {l : Fin k} {a b d : ℕ}
    (hab : a < b) (hbd : b < d) (hd : d ≤ N) (h₁ : c (Nat.dist a b) = l)
    (h₂ : c (Nat.dist b d) = l) (h₃ : c (Nat.dist a d) = l) :
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ N ∧ c x = c (x + y) ∧ c y = c (x + y) := by
  rw [Nat.dist_eq_sub_of_le hab.le] at h₁
  rw [Nat.dist_eq_sub_of_le hbd.le] at h₂
  rw [Nat.dist_eq_sub_of_le (hab.trans hbd).le] at h₃
  refine ⟨b - a, d - b, by omega, by omega, by omega, ?_, ?_⟩
  · rwa [show b - a + (d - b) = d - a by omega, h₃]
  · rwa [show b - a + (d - b) = d - a by omega, h₃]

/-- If every colouring of the edges of the complete graph on `N + 1` vertices with `k` colours
has a monochromatic triangle, then every colouring of `[N] = {1, …, N}` with `k` colours has
`x`, `y` and `x + y` in `[N]` of one colour. -/
theorem schur_of_arrows {N : ℕ} (hN : Arrows (N + 1) fun _ : Fin k ↦ 3) (c : ℕ → Fin k) :
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ N ∧ c x = c (x + y) ∧ c y = c (x + y) := by
  obtain ⟨l, hl⟩ := hN.hasMonoClique (by simp) (distColouring (N + 1) c)
  simp only [CliqueFree, not_forall, not_not, is3Clique_iff] at hl
  obtain ⟨_, a, b, d, hab, had, hbd, -⟩ := hl
  rw [distColouring_labelGraph_adj] at hab had hbd
  have ha := a.is_lt
  have hb := b.is_lt
  have hd := d.is_lt
  have hab' : (a : ℕ) ≠ b := Fin.val_ne_of_ne hab.1
  have had' : (a : ℕ) ≠ d := Fin.val_ne_of_ne had.1
  have hbd' : (b : ℕ) ≠ d := Fin.val_ne_of_ne hbd.1
  have h₁ := hab.2
  have h₂ := had.2
  have h₃ := hbd.2
  have h₁' := Nat.dist_comm (a : ℕ) b ▸ h₁
  have h₂' := Nat.dist_comm (a : ℕ) d ▸ h₂
  have h₃' := Nat.dist_comm (b : ℕ) d ▸ h₃
  rcases Nat.lt_or_gt_of_ne hab' with h | h <;> rcases Nat.lt_or_gt_of_ne had' with h' | h' <;>
    rcases Nat.lt_or_gt_of_ne hbd' with h'' | h''
  all_goals first
    | omega
    | exact schur_of_lt (a := a) (b := b) (d := d) (by omega) (by omega) (by omega)
        (by assumption) (by assumption) (by assumption)
    | exact schur_of_lt (a := a) (b := d) (d := b) (by omega) (by omega) (by omega)
        (by assumption) (by assumption) (by assumption)
    | exact schur_of_lt (a := b) (b := a) (d := d) (by omega) (by omega) (by omega)
        (by assumption) (by assumption) (by assumption)
    | exact schur_of_lt (a := b) (b := d) (d := a) (by omega) (by omega) (by omega)
        (by assumption) (by assumption) (by assumption)
    | exact schur_of_lt (a := d) (b := a) (d := b) (by omega) (by omega) (by omega)
        (by assumption) (by assumption) (by assumption)
    | exact schur_of_lt (a := d) (b := b) (d := a) (by omega) (by omega) (by omega)
        (by assumption) (by assumption) (by assumption)

/-- `R_k(3) ≥ 2`: a colouring of the complete graph on one vertex has no triangle. -/
theorem two_le_multiRamseyNumber_three : 2 ≤ multiRamseyNumber (fun _ : Fin k ↦ 3) := by
  by_contra! h
  have h1 : Arrows 1 fun _ : Fin k ↦ 3 := (arrows_multiRamseyNumber _).mono (by omega)
  let C : TopEdgeLabeling (Fin 1) (Fin k) :=
    EdgeLabeling.mk (fun x y H ↦ absurd (Subsingleton.elim x y) H) fun x y H ↦
      absurd (Subsingleton.elim x y) H
  obtain ⟨i, hi⟩ := h1.hasMonoClique (by simp) C
  refine hi fun t ht ↦ ?_
  have := ht.card_eq ▸ card_le_univ t
  simp at this

/-- Every colouring of `[N] = {1, …, N}` with `k` colours, for `N = R_k(3) - 1`, has `x`, `y` and
`x + y` in `[N]` of one colour (`x = y` allowed). Here `R_k(3) = R(3, …, 3)` with `k` threes is
`multiRamseyNumber fun _ : Fin k ↦ 3`, and a colouring of `[N]` is a function `ℕ → Fin k`.

This is the bound of the milestone *Schur's theorem*. -/
theorem schur_multiRamseyNumber (c : ℕ → Fin k) :
    ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ multiRamseyNumber (fun _ : Fin k ↦ 3) - 1 ∧
      c x = c (x + y) ∧ c y = c (x + y) :=
  schur_of_arrows ((arrows_multiRamseyNumber _).mono (by omega)) c

/-- **Schur's theorem**: for every `k` there is an `N` such that every colouring of
`[N] = {1, …, N}` with `k` colours, a function `ℕ → Fin k`, has `x`, `y` and `x + y` in `[N]`
of one colour (`x = y` allowed). The plan assumes `k ≥ 1`; this is not needed, as there is no
colouring with no colours. One can take `N = R_k(3) - 1` (`schur_multiRamseyNumber`).

This is the milestone *Schur's theorem*. -/
theorem exists_schur (k : ℕ) :
    ∃ N, ∀ c : ℕ → Fin k,
      ∃ x y, 1 ≤ x ∧ 1 ≤ y ∧ x + y ≤ N ∧ c x = c (x + y) ∧ c y = c (x + y) :=
  ⟨_, schur_multiRamseyNumber⟩

/-- For `N = R_k(3) - 1`, if `k` finite sets of natural numbers `A i` cover
`[N] = Finset.Icc 1 N`, then one of them is not sum-free: it contains `x`, `y` and `x + y`,
all in `[N]` (`x = y` allowed).

This is the sum-free form of the milestone *Schur's theorem*. -/
theorem schur_not_sumFree (A : Fin k → Finset ℕ)
    (hA : Icc 1 (multiRamseyNumber (fun _ : Fin k ↦ 3) - 1) ⊆ univ.biUnion A) :
    ∃ i, ∃ x ∈ A i, ∃ y ∈ A i, x + y ∈ A i ∧ 1 ≤ x ∧ 1 ≤ y ∧
      x + y ≤ multiRamseyNumber (fun _ : Fin k ↦ 3) - 1 := by
  classical
  set N := multiRamseyNumber (fun _ : Fin k ↦ 3) - 1
  have hmem : ∀ n, 1 ≤ n → n ≤ N → ∃ i, n ∈ A i := fun n h1 hN ↦ by
    simpa using hA (mem_Icc.mpr ⟨h1, hN⟩)
  have hN : 1 ≤ N := by
    have := two_le_multiRamseyNumber_three (k := k)
    omega
  obtain ⟨i₀, -⟩ := hmem 1 le_rfl hN
  let c : ℕ → Fin k := fun n ↦ if h : 1 ≤ n ∧ n ≤ N then (hmem n h.1 h.2).choose else i₀
  have hc : ∀ n (h : 1 ≤ n ∧ n ≤ N), n ∈ A (c n) := fun n h ↦ by
    simp only [c, h, and_self, dite_true]
    exact (hmem n h.1 h.2).choose_spec
  obtain ⟨x, y, hx, hy, hxy, h₁, h₂⟩ := schur_multiRamseyNumber c
  refine ⟨c (x + y), x, ?_, y, ?_, hc _ ⟨by omega, hxy⟩, hx, hy, hxy⟩
  · rw [← h₁]; exact hc x ⟨hx, by omega⟩
  · rw [← h₂]; exact hc y ⟨hy, by omega⟩

/-- For `N = R_k(3) - 1`, `[N] = Finset.Icc 1 N` is not the union of `k` sum-free sets: if it is
the union of `k` finite sets `A i`, one of them contains `x`, `y` and `x + y` (`x = y`
allowed).

This is the sum-free form of the milestone *Schur's theorem*. -/
theorem schur_not_union_sumFree (A : Fin k → Finset ℕ)
    (hA : univ.biUnion A = Icc 1 (multiRamseyNumber (fun _ : Fin k ↦ 3) - 1)) :
    ∃ i, ∃ x ∈ A i, ∃ y ∈ A i, x + y ∈ A i := by
  obtain ⟨i, x, hx, y, hy, hxy, -⟩ := schur_not_sumFree A hA.ge
  exact ⟨i, x, hx, y, hy, hxy⟩

end Ramsey

end
