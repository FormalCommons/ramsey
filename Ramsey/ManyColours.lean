module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Coloring.EdgeLabeling
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Ramsey's theorem for many colours

This file formalizes the milestone *Ramsey's theorem for many colours* of the plan
(`ramsey-theorem.md` in `FormalCommons/ramsey-plan`).

A colouring of the edges of the complete graph on `V` with `k` colours is a
`SimpleGraph.TopEdgeLabeling V (Fin k)`, and a monochromatic `K_m` in colour `i` is a clique of
size `m` in `C.labelGraph i`.

## Main definitions

* `Ramsey.HasMonoClique C s`: for some colour `i`, the colouring `C` has a monochromatic
  `K_{s i}` in colour `i`.
* `Ramsey.Arrows n s`: every colouring of the edges of the complete graph on `Fin n` with
  colours `Fin k` has, for some `i`, a monochromatic `K_{s i}` in colour `i`.
* `Ramsey.multiRamseyNumber s`: the Ramsey number `R(s₁, …, s_k)`, the least such `n`.

## Main results

* `Ramsey.exists_ramsey_manyColours`: Ramsey's theorem for many colours.
* `Ramsey.multiRamseyNumber_add_le`: for `s i ≥ 2`,
  `R(s) ≤ 2 - k + ∑ i, R(s with s i lowered by 1)`, stated without subtraction.
* `Ramsey.multiRamseyNumber_three_le`: `R_k(3) ≤ k (R_{k-1}(3) - 1) + 2` for `k ≥ 2`.
* `Ramsey.forall_labelGraph_fin_two_iff`, `Ramsey.isLeast_multiRamseyNumber_fin_two`: for
  two colours, the statement agrees with the one for graphs, through
  `SimpleGraph.toTopEdgeLabeling`.

## References

* R. L. Graham, B. L. Rothschild, J. H. Spencer, *Ramsey Theory*, Ch. 1.
* R. E. Greenwood, A. M. Gleason, *Combinatorial relations and chromatic graphs* (1955).
-/

public section

open SimpleGraph Finset

namespace Ramsey

universe u

variable {V V' : Type*} {K : Type*} {k : ℕ}

/-- The graph of colour `i` of a colouring pulled back along an injection `f`, mapped forward
along `f`, is contained in the graph of colour `i` of the original colouring. -/
theorem labelGraph_pullback_map_le (C : TopEdgeLabeling V K) (f : V' ↪ V) (i : K) :
    ((C.pullback f).labelGraph i).map f ≤ C.labelGraph i := by
  intro x y h
  obtain ⟨a, b, hab, rfl, rfl⟩ := (map_adj _ _ _ _).mp h
  rw [TopEdgeLabeling.labelGraph_adj] at hab ⊢
  obtain ⟨H, hH⟩ := hab
  exact ⟨f.injective.ne H, hH⟩

/-- A monochromatic clique of a colouring pulled back along an injection gives one of the same
size and colour in the original colouring. -/
theorem not_cliqueFree_of_pullback {C : TopEdgeLabeling V K} {f : V' ↪ V} {i : K} {m : ℕ}
    (h : ¬((C.pullback f).labelGraph i).CliqueFree m) : ¬(C.labelGraph i).CliqueFree m := by
  intro hC
  apply h
  intro t ht
  exact hC (t.map f) (ht.map.mono (labelGraph_pullback_map_le C f i))

/-- The colouring `C` has, for some colour `i`, a monochromatic `K_{s i}` in colour `i`. -/
def HasMonoClique (C : TopEdgeLabeling V (Fin k)) (s : Fin k → ℕ) : Prop :=
  ∃ i, ¬(C.labelGraph i).CliqueFree (s i)

/-- `Arrows n s`: every colouring of the edges of the complete graph on `Fin n` with colours
`Fin k` has, for some `i`, a monochromatic `K_{s i}` in colour `i`. -/
def Arrows (n : ℕ) (s : Fin k → ℕ) : Prop :=
  ∀ C : TopEdgeLabeling (Fin n) (Fin k), HasMonoClique C s

/-- If `Arrows n s`, then every colouring of the edges of the complete graph on a vertex type
with at least `n` elements has a monochromatic `K_{s i}` in some colour `i`. -/
theorem Arrows.hasMonoClique [Fintype V] {n : ℕ} {s : Fin k → ℕ} (h : Arrows n s)
    (hn : n ≤ Fintype.card V) (C : TopEdgeLabeling V (Fin k)) : HasMonoClique C s := by
  obtain ⟨f⟩ : Nonempty (Fin n ↪ V) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hn)
  obtain ⟨i, hi⟩ := h (C.pullback f)
  exact ⟨i, not_cliqueFree_of_pullback hi⟩

/-- `Arrows n s` holds if and only if every colouring of the edges of the complete graph on
any vertex type with `n` elements has a monochromatic `K_{s i}` in some colour `i`. -/
theorem arrows_iff {n : ℕ} {s : Fin k → ℕ} :
    Arrows n s ↔ ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ C : TopEdgeLabeling V (Fin k), HasMonoClique C s := by
  refine ⟨fun h V _ hV C ↦ h.hasMonoClique hV.ge C, fun h C ↦ ?_⟩
  have := h (ULift (Fin n)) (by simp) (C.pullback Equiv.ulift.toEmbedding)
  obtain ⟨i, hi⟩ := this
  exact ⟨i, not_cliqueFree_of_pullback hi⟩

theorem Arrows.mono {m n : ℕ} {s : Fin k → ℕ} (h : Arrows m s) (hmn : m ≤ n) : Arrows n s :=
  fun C ↦ h.hasMonoClique (by simpa using hmn) C

/-- If some `s i ≤ 1`, every colouring on a nonempty vertex set has a monochromatic `K_{s i}`
in colour `i`. -/
theorem arrows_one_of_le_one {s : Fin k → ℕ} {i : Fin k} (hi : s i ≤ 1) : Arrows 1 s := by
  intro C
  refine ⟨i, fun hC ↦ ?_⟩
  have h1 : (C.labelGraph i).CliqueFree 1 := hC.mono hi
  rw [cliqueFree_one] at h1
  exact h1.false 0

/-- No colouring of the empty graph has a monochromatic clique of positive size. -/
theorem not_arrows_zero {s : Fin k → ℕ} (hs : ∀ i, 1 ≤ s i) : ¬Arrows 0 s := by
  intro h
  obtain ⟨i, hi⟩ := h (Classical.arbitrary _)
  exact hi ((cliqueFree_one.mpr inferInstance).mono (hs i))

/-- The inductive step of Ramsey's theorem for many colours: if `Arrows (n i) s⁽ⁱ⁾` for every
`i`, where `s⁽ⁱ⁾` is `s` with `s i` lowered by one, then `Arrows (∑ i, (n i - 1) + 2) s`. -/
theorem arrows_step {s : Fin k → ℕ} (hs : ∀ i, 1 ≤ s i) {n : Fin k → ℕ}
    (hn : ∀ i, Arrows (n i) (Function.update s i (s i - 1))) :
    Arrows (∑ i, (n i - 1) + 2) s := by
  classical
  generalize hN : ∑ i, (n i - 1) + 2 = N
  intro C
  let v : Fin N := ⟨0, by omega⟩
  have hsum : ∑ i, #((C.labelGraph i).neighborFinset v) = N - 1 := by
    rw [← card_biUnion]
    · have : (univ : Finset (Fin k)).biUnion (fun i ↦ (C.labelGraph i).neighborFinset v) =
          univ.erase v := by
        ext w
        simp [eq_comm (a := w)]
      rw [this, card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]
    · intro i _ j _ hij
      rw [Function.onFun, Finset.disjoint_left]
      intro w hi hj
      rw [mem_neighborFinset, TopEdgeLabeling.labelGraph_adj] at hi hj
      obtain ⟨_, rfl⟩ := hi
      obtain ⟨_, rfl⟩ := hj
      exact hij rfl
  obtain ⟨i, hi⟩ : ∃ i, n i ≤ #((C.labelGraph i).neighborFinset v) := by
    by_contra! h
    have : ∑ i, #((C.labelGraph i).neighborFinset v) ≤ ∑ i, (n i - 1) :=
      sum_le_sum fun i _ ↦ by have := h i; omega
    omega
  let U := {w // w ∈ (C.labelGraph i).neighborFinset v}
  have hU : n i ≤ Fintype.card U := by simpa only [U, Fintype.card_coe] using hi
  let f : U ↪ Fin N := Function.Embedding.subtype _
  obtain ⟨j, hj⟩ := (hn i).hasMonoClique hU (C.pullback f)
  by_cases hji : j = i
  · subst hji
    rw [Function.update_self] at hj
    simp only [CliqueFree, not_forall, not_not] at hj
    obtain ⟨t, ht⟩ := hj
    have ht' := ht.map.mono (labelGraph_pullback_map_le C f j)
    refine ⟨j, fun hC ↦ hC (insert v (t.map f)) ?_⟩
    have := ht'.insert (a := v) (by
      intro b hb
      obtain ⟨b, -, rfl⟩ := mem_map.mp hb
      exact (mem_neighborFinset _ _ _).mp b.2)
    rwa [Nat.sub_add_cancel (hs j)] at this
  · refine ⟨j, ?_⟩
    rw [Function.update_of_ne hji] at hj
    exact not_cliqueFree_of_pullback hj

/-- **Ramsey's theorem for many colours**: for all `s : Fin k → ℕ` there is an `n` such that
every colouring of the edges of the complete graph on `n` vertices with colours `Fin k` has, for
some `i`, a monochromatic `K_{s i}` in colour `i`. The plan assumes `k ≥ 1` and all `s i ≥ 1`;
neither is needed (for `k = 0` there is no colouring of a graph with an edge).

This is the milestone *Ramsey's theorem for many colours*. -/
theorem exists_ramsey_manyColours (s : Fin k → ℕ) :
    ∃ n, ∀ (V : Type u) [Fintype V], Fintype.card V = n →
      ∀ C : TopEdgeLabeling V (Fin k), ∃ i, ¬(C.labelGraph i).CliqueFree (s i) := by
  suffices ∃ n, Arrows n s from this.imp fun _ h ↦ arrows_iff.mp h
  induction hm : ∑ i, s i using Nat.strong_induction_on generalizing s with
  | _ m ih =>
    by_cases h : ∃ i, s i ≤ 1
    · obtain ⟨i, hi⟩ := h
      exact ⟨1, arrows_one_of_le_one hi⟩
    push Not at h
    have hn : ∀ i, ∃ n, Arrows n (Function.update s i (s i - 1)) := by
      intro i
      refine ih _ ?_ _ rfl
      rw [← hm]
      refine sum_lt_sum (fun j _ ↦ ?_) ⟨i, mem_univ _, by simp; have := h i; omega⟩
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    choose n hn using hn
    exact ⟨_, arrows_step (fun i ↦ (h i).le) hn⟩

/-- The Ramsey number `R(s₁, …, s_k)`: the least `n` such that every colouring of the edges of
the complete graph on `n` vertices with colours `Fin k` has, for some `i`, a monochromatic
`K_{s i}` in colour `i`. -/
noncomputable def multiRamseyNumber (s : Fin k → ℕ) : ℕ :=
  sInf {n | Arrows n s}

theorem exists_arrows (s : Fin k → ℕ) : ∃ n, Arrows n s :=
  (exists_ramsey_manyColours.{0} s).imp fun _ h ↦ arrows_iff.mpr h

theorem arrows_multiRamseyNumber (s : Fin k → ℕ) : Arrows (multiRamseyNumber s) s :=
  @Nat.sInf_mem {n | Arrows n s} (exists_arrows s)

theorem multiRamseyNumber_le {n : ℕ} {s : Fin k → ℕ} (h : Arrows n s) :
    multiRamseyNumber s ≤ n :=
  Nat.sInf_le h

/-- `Arrows n s` holds exactly from the Ramsey number on. -/
theorem arrows_iff_multiRamseyNumber_le {n : ℕ} {s : Fin k → ℕ} :
    Arrows n s ↔ multiRamseyNumber s ≤ n :=
  ⟨multiRamseyNumber_le, (arrows_multiRamseyNumber s).mono⟩

theorem one_le_multiRamseyNumber {s : Fin k → ℕ} (hs : ∀ i, 1 ≤ s i) :
    1 ≤ multiRamseyNumber s := by
  by_contra! h
  exact not_arrows_zero hs (Nat.lt_one_iff.mp h ▸ arrows_multiRamseyNumber s)

/-- The bound of the milestone *Ramsey's theorem for many colours*: if all `s i ≥ 2`, then
`R(s) ≤ 2 - k + ∑ i, R(s₁, …, s i - 1, …, s_k)`, stated with `k` moved to the left so that no
subtraction is truncated. -/
theorem multiRamseyNumber_add_le {s : Fin k → ℕ} (hs : ∀ i, 2 ≤ s i) :
    multiRamseyNumber s + k ≤
      ∑ i, multiRamseyNumber (Function.update s i (s i - 1)) + 2 := by
  have hR : ∀ i, 1 ≤ multiRamseyNumber (Function.update s i (s i - 1)) := fun i ↦
    one_le_multiRamseyNumber fun j ↦ by
      by_cases hji : j = i
      · subst hji; simp; have := hs j; omega
      · simp [hji]; have := hs j; omega
  have := multiRamseyNumber_le
    (arrows_step (fun i ↦ (hs i).trans' (by norm_num)) fun i ↦ arrows_multiRamseyNumber _)
  have hsub : ∑ i, (multiRamseyNumber (Function.update s i (s i - 1)) - 1) + k =
      ∑ i, multiRamseyNumber (Function.update s i (s i - 1)) := by
    conv_rhs => rw [← sum_congr rfl fun i _ ↦ Nat.sub_add_cancel (hR i)]
    simp [sum_add_distrib]
  omega


/-- The bound of the milestone *Ramsey's theorem for many colours*, in the integers: if all
`s i ≥ 2`, then `R(s) ≤ 2 - k + ∑ i, R(s₁, …, s i - 1, …, s_k)`. -/
theorem multiRamseyNumber_le_sum {s : Fin k → ℕ} (hs : ∀ i, 2 ≤ s i) :
    (multiRamseyNumber s : ℤ) ≤
      2 - k + ∑ i, (multiRamseyNumber (Function.update s i (s i - 1)) : ℤ) := by
  have := (Nat.cast_le (α := ℤ)).mpr (multiRamseyNumber_add_le hs)
  push_cast at this
  linarith

/-- `R(3, …, 3, 2, 3, …, 3) ≤ R(3, …, 3)`, with one colour fewer on the right. -/
theorem multiRamseyNumber_update_two_le {m : ℕ} (hm : 0 < m) (i : Fin (m + 1)) :
    multiRamseyNumber (Function.update (fun _ : Fin (m + 1) ↦ 3) i 2) ≤
      multiRamseyNumber (fun _ : Fin m ↦ 3) := by
  apply multiRamseyNumber_le
  intro C
  by_cases hi : ∃ x y : Fin (multiRamseyNumber fun _ : Fin m ↦ 3),
      (C.labelGraph i).Adj x y
  · obtain ⟨x, y, hxy⟩ := hi
    refine ⟨i, fun hC ↦ ?_⟩
    rw [Function.update_self] at hC
    exact hC {x, y} (by simpa [isNClique_iff, hxy.ne] using hxy)
  push Not at hi
  let g : Fin (m + 1) → Fin m := fun c ↦ (finSuccEquiv' i c).getD ⟨0, hm⟩
  obtain ⟨j, hj⟩ := arrows_multiRamseyNumber (fun _ : Fin m ↦ 3)
    (EdgeLabeling.compRight C g)
  refine ⟨i.succAbove j, ?_⟩
  rw [Function.update_of_ne (Fin.succAbove_ne i j)]
  refine fun hC ↦ hj fun t ht ↦ hC t (ht.mono ?_)
  intro x y hxy
  rw [TopEdgeLabeling.labelGraph_adj] at hxy ⊢
  obtain ⟨H, hH⟩ := hxy
  refine ⟨H, ?_⟩
  have hne : C.get x y H ≠ i := fun h ↦
    hi x y ((TopEdgeLabeling.labelGraph_adj x y).mpr ⟨H, h⟩)
  obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hne
  rw [EdgeLabeling.compRight_get, ← hc] at hH
  rw [← hc]
  simp [g, finSuccEquiv'_succAbove] at hH
  rw [hH]

/-- The corollary of the milestone *Ramsey's theorem for many colours*: for `k ≥ 2`,
`R_k(3) ≤ k (R_{k-1}(3) - 1) + 2`, where `R_k(3) = R(3, …, 3)` with `k` threes. -/
theorem multiRamseyNumber_three_le (hk : 2 ≤ k) :
    multiRamseyNumber (fun _ : Fin k ↦ 3) ≤
      k * (multiRamseyNumber (fun _ : Fin (k - 1) ↦ 3) - 1) + 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm : 0 < m := by omega
  rw [Nat.add_sub_cancel]
  have h := multiRamseyNumber_add_le (s := fun _ : Fin (m + 1) ↦ 3) (fun _ ↦ by norm_num)
  have h2 : ∑ i : Fin (m + 1), multiRamseyNumber (Function.update (fun _ ↦ 3) i (3 - 1)) ≤
      (m + 1) * multiRamseyNumber (fun _ : Fin m ↦ 3) := by
    calc _ ≤ ∑ _i : Fin (m + 1), multiRamseyNumber (fun _ : Fin m ↦ 3) :=
          sum_le_sum fun i _ ↦ multiRamseyNumber_update_two_le hm i
      _ = _ := by simp
  have h1 := one_le_multiRamseyNumber (s := fun _ : Fin m ↦ 3) fun _ ↦ by norm_num
  obtain ⟨r, hr⟩ : ∃ r, multiRamseyNumber (fun _ : Fin m ↦ 3) = r + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos h1).symm⟩
  rw [hr] at h2 ⊢
  simp only [Nat.add_sub_cancel]
  nlinarith

/-! ### Two colours -/
/-! ### Two colours -/

/-- With two colours, `HasMonoClique C ![t, s]` says that `C` has a `K_t` in colour `0` or a
`K_s` in colour `1`. -/
theorem hasMonoClique_fin_two_iff (C : TopEdgeLabeling V (Fin 2)) (s t : ℕ) :
    HasMonoClique C ![t, s] ↔
      ¬(C.labelGraph 0).CliqueFree t ∨ ¬(C.labelGraph 1).CliqueFree s :=
  ⟨fun ⟨i, hi⟩ ↦ by fin_cases i <;> simp_all, fun h ↦ h.elim (⟨0, ·⟩) (⟨1, ·⟩)⟩

/-- For two colours, the statement for colourings agrees with the one for graphs, through
`SimpleGraph.toTopEdgeLabeling` (label `1` is `G`, label `0` is `Gᶜ`): every colouring has a
`K_t` in colour `0` or a `K_s` in colour `1` if and only if every graph has a clique of size `s`
or an independent set of size `t`. -/
theorem forall_labelGraph_fin_two_iff [Fintype V] (s t : ℕ) :
    (∀ C : TopEdgeLabeling V (Fin 2),
      ¬(C.labelGraph 0).CliqueFree t ∨ ¬(C.labelGraph 1).CliqueFree s) ↔
      ∀ G : SimpleGraph V, ¬G.CliqueFree s ∨ ¬G.IndepSetFree t := by
  classical
  constructor
  · intro h G
    have := h G.toTopEdgeLabeling
    rw [toTopEdgeLabeling_labelGraph, toTopEdgeLabeling_labelGraph_compl, cliqueFree_compl]
      at this
    exact this.symm
  · intro h C
    have := h (C.labelGraph 1)
    rw [← C.labelGraph_toTopEdgeLabeling, toTopEdgeLabeling_labelGraph,
      toTopEdgeLabeling_labelGraph_compl, cliqueFree_compl]
    exact this.symm

/-- `Arrows n ![t, s]` holds if and only if every graph on `n` vertices has a clique of size `s`
or an independent set of size `t`. -/
theorem arrows_fin_two_iff (n s t : ℕ) :
    Arrows n ![t, s] ↔ ∀ G : SimpleGraph (Fin n), ¬G.CliqueFree s ∨ ¬G.IndepSetFree t := by
  simp only [Arrows, hasMonoClique_fin_two_iff]
  exact forall_labelGraph_fin_two_iff s t

/-- For two colours, `R(t, s)` in the sense of colourings is the least `n` such that every graph
on `n` vertices has a clique of size `s` or an independent set of size `t`. -/
theorem isLeast_multiRamseyNumber_fin_two (s t : ℕ) :
    IsLeast {n | ∀ G : SimpleGraph (Fin n), ¬G.CliqueFree s ∨ ¬G.IndepSetFree t}
      (multiRamseyNumber ![t, s]) :=
  ⟨(arrows_fin_two_iff _ s t).mp (arrows_multiRamseyNumber _),
    fun n hn ↦ multiRamseyNumber_le ((arrows_fin_two_iff n s t).mpr hn)⟩

end Ramsey

end
