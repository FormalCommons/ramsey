module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

/-!
# Erdős's lower bound for the diagonal Ramsey numbers

This file proves the milestone *Erdős's lower bound* of the plan: for every `k ≥ 3`,
`R(k, k) > 2^{k/2}`. More precisely:

* `Ramsey.exists_cliqueFree_indepSetFree_of_two_mul_choose_lt`: if
  `2 * n.choose k < 2 ^ k.choose 2` (that is, `C(n, k) 2^{1 - C(k, 2)} < 1`), then some graph on
  `Fin n` has no clique of size `k` and no independent set of size `k`.
* `Ramsey.exists_cliqueFree_indepSetFree_of_sq_le`: for `k ≥ 3` and `n ^ 2 ≤ 2 ^ k` (so for
  `n = ⌊2^{k/2}⌋`), some graph on `Fin n` has neither.

The proof counts. A graph on `Fin n` is given by its set of edges, a subset of the set `P` of
two-element subsets of `Fin n`, so there are `2 ^ C(n, 2)` of them. For a set `s` of `k`
vertices, at most `2 ^ (C(n, 2) - C(k, 2))` of them make `s` a clique, and as many make it an
independent set. By the union bound (`Finset.card_biUnion_le`) over the `C(n, k)` sets `s`,
fewer than `2 ^ C(n, 2)` graphs have a clique or an independent set of size `k`.

## References

* [P. Erdős, *Some remarks on the theory of graphs*][Erdos1947]
* [N. Alon and J. H. Spencer, *The Probabilistic Method*, Proposition 1.1.1][AlonSpencer2008]
-/

public section

namespace Ramsey

open Finset

variable {V : Type*} [DecidableEq V]

/-- The graph whose edges are the two-element sets in `T`. -/
private def graphOfPairs (T : Finset (Finset V)) : SimpleGraph V :=
  SimpleGraph.fromRel fun i j => {i, j} ∈ T

private lemma graphOfPairs_adj {T : Finset (Finset V)} {i j : V} :
    (graphOfPairs T).Adj i j ↔ i ≠ j ∧ {i, j} ∈ T := by
  simp [graphOfPairs, Finset.pair_comm j i]

/-- The two-element subsets of `s` are the edges of `graphOfPairs T` inside `s`. -/
private lemma mem_of_isClique {T : Finset (Finset V)} {s : Finset V}
    (hs : (graphOfPairs T).IsClique (s : Set V)) : s.powersetCard 2 ⊆ T := by
  intro t ht
  obtain ⟨hts, htc⟩ := mem_powersetCard.1 ht
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 htc
  exact (graphOfPairs_adj.1 (hs (hts (by simp)) (hts (by simp)) hij)).2

private lemma disjoint_of_isIndepSet {T : Finset (Finset V)} {s : Finset V}
    (hs : (graphOfPairs T).IsIndepSet (s : Set V)) : Disjoint (s.powersetCard 2) T := by
  rw [disjoint_left]
  intro t ht htT
  obtain ⟨hts, htc⟩ := mem_powersetCard.1 ht
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 htc
  exact hs (hts (by simp)) (hts (by simp)) hij (graphOfPairs_adj.2 ⟨hij, htT⟩)

/-- The number of subsets of `P` that contain `Q ⊆ P`. -/
private lemma card_filter_superset_le {P Q : Finset (Finset V)} (hQ : Q ⊆ P) :
    #(P.powerset.filter (Q ⊆ ·)) ≤ 2 ^ (#P - #Q) := by
  calc #(P.powerset.filter (Q ⊆ ·))
      ≤ #((P \ Q).powerset.image (· ∪ Q)) := by
        refine card_le_card fun T hT => ?_
        obtain ⟨hTP, hQT⟩ := mem_filter.1 hT
        refine mem_image.2 ⟨T \ Q, mem_powerset.2 (sdiff_subset_sdiff (mem_powerset.1 hTP)
          subset_rfl), sdiff_union_of_subset hQT⟩
    _ ≤ #(P \ Q).powerset := card_image_le
    _ = 2 ^ (#P - #Q) := by rw [card_powerset, card_sdiff_of_subset hQ]

/-- The number of subsets of `P` that are disjoint from `Q ⊆ P`. -/
private lemma card_filter_disjoint_le {P Q : Finset (Finset V)} (hQ : Q ⊆ P) :
    #(P.powerset.filter (Disjoint Q ·)) ≤ 2 ^ (#P - #Q) := by
  calc #(P.powerset.filter (Disjoint Q ·))
      ≤ #(P \ Q).powerset := by
        refine card_le_card fun T hT => ?_
        obtain ⟨hTP, hQT⟩ := mem_filter.1 hT
        exact mem_powerset.2 (subset_sdiff.2 ⟨mem_powerset.1 hTP, hQT.symm⟩)
    _ = 2 ^ (#P - #Q) := by rw [card_powerset, card_sdiff_of_subset hQ]

/-- **Erdős's lower bound**, counting form: if `2 * C(n, k) < 2 ^ C(k, 2)`, that is
`C(n, k) 2^{1 - C(k, 2)} < 1`, then some graph on `n` vertices has no clique of size `k` and no
independent set of size `k`.

This is the milestone *Erdős's lower bound*, in its precise form. -/
theorem exists_cliqueFree_indepSetFree_of_two_mul_choose_lt {n k : ℕ}
    (h : 2 * n.choose k < 2 ^ k.choose 2) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ G.IndepSetFree k := by
  classical
  -- `P` is the set of possible edges, `Q s` the possible edges inside `s`.
  set P : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard 2 with hP
  let Q : Finset (Fin n) → Finset (Finset (Fin n)) := fun s => s.powersetCard 2
  have hQP : ∀ s, Q s ⊆ P := fun s => powersetCard_mono (subset_univ s)
  -- The edge sets that make some `k`-set a clique or an independent set.
  let bad : Finset (Finset (Finset (Fin n))) :=
    ((univ : Finset (Fin n)).powersetCard k).biUnion fun s =>
      P.powerset.filter (Q s ⊆ ·) ∪ P.powerset.filter (Disjoint (Q s) ·)
  have hbad : #bad < #P.powerset := by
    have hcard : ∀ s ∈ (univ : Finset (Fin n)).powersetCard k,
        #(P.powerset.filter (Q s ⊆ ·) ∪ P.powerset.filter (Disjoint (Q s) ·)) ≤
          2 * 2 ^ (n.choose 2 - k.choose 2) := by
      intro s hs
      have hQ : #(Q s) = k.choose 2 := by
        simp [Q, card_powersetCard, (mem_powersetCard.1 hs).2]
      have hPc : #P = n.choose 2 := by simp [hP, card_powersetCard]
      calc _ ≤ #(P.powerset.filter (Q s ⊆ ·)) + #(P.powerset.filter (Disjoint (Q s) ·)) :=
            card_union_le _ _
        _ ≤ 2 ^ (#P - #(Q s)) + 2 ^ (#P - #(Q s)) :=
            add_le_add (card_filter_superset_le (hQP s)) (card_filter_disjoint_le (hQP s))
        _ = 2 * 2 ^ (n.choose 2 - k.choose 2) := by rw [hQ, hPc, two_mul]
    calc #bad ≤ ∑ s ∈ (univ : Finset (Fin n)).powersetCard k,
          #(P.powerset.filter (Q s ⊆ ·) ∪ P.powerset.filter (Disjoint (Q s) ·)) :=
          card_biUnion_le
      _ ≤ ∑ _s ∈ (univ : Finset (Fin n)).powersetCard k, 2 * 2 ^ (n.choose 2 - k.choose 2) :=
          sum_le_sum hcard
      _ = 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2) := by
          simp only [sum_const, card_powersetCard, card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ < 2 ^ n.choose 2 := by
          rcases le_or_gt k n with hkn | hkn
          · calc 2 * n.choose k * 2 ^ (n.choose 2 - k.choose 2)
                < 2 ^ k.choose 2 * 2 ^ (n.choose 2 - k.choose 2) :=
                  Nat.mul_lt_mul_of_pos_right h (by positivity)
              _ = 2 ^ n.choose 2 := by
                  rw [← pow_add, Nat.add_sub_cancel' (Nat.choose_le_choose 2 hkn)]
          · simp [Nat.choose_eq_zero_of_lt hkn]
      _ = #P.powerset := by simp [hP, card_powersetCard]
  obtain ⟨T, hT, hTbad⟩ := exists_mem_notMem_of_card_lt_card hbad
  refine ⟨graphOfPairs T, fun s hs => hTbad ?_, fun s hs => hTbad ?_⟩
  · refine mem_biUnion.2 ⟨s, mem_powersetCard.2 ⟨subset_univ s, hs.2⟩, mem_union_left _ ?_⟩
    exact mem_filter.2 ⟨hT, mem_of_isClique hs.1⟩
  · refine mem_biUnion.2 ⟨s, mem_powersetCard.2 ⟨subset_univ s, hs.2⟩,
      mem_union_right _ ?_⟩
    exact mem_filter.2 ⟨hT, disjoint_of_isIndepSet hs.1⟩

/-- `2 ^ (k + 2) < (k !) ^ 2` for `k ≥ 3`. -/
private lemma two_pow_add_two_lt_factorial_sq {k : ℕ} (hk : 3 ≤ k) :
    2 ^ (k + 2) < k.factorial ^ 2 := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ, mul_pow, pow_succ]
    calc 2 ^ (k + 2) * 2 < k.factorial ^ 2 * 2 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ k.factorial ^ 2 * (k + 1) ^ 2 := by
          gcongr
          nlinarith
      _ = (k + 1) ^ 2 * k.factorial ^ 2 := mul_comm _ _

/-- For `k ≥ 3` and `n ^ 2 ≤ 2 ^ k`, `2 * C(n, k) < 2 ^ C(k, 2)`. -/
lemma two_mul_choose_lt_of_sq_le {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    2 * n.choose k < 2 ^ k.choose 2 := by
  have hchoose : 2 * k.choose 2 = k * (k - 1) := by
    rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self k).two_dvd]
  have hkk : k * (k - 1) + k = k * k := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega)]
  have hfac : k.factorial * n.choose k ≤ n ^ k := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact Nat.descFactorial_le_pow n k
  refine lt_of_pow_lt_pow_left₀ 2 (by positivity)
    (Nat.lt_of_mul_lt_mul_right (a := k.factorial ^ 2) ?_)
  calc (2 * n.choose k) ^ 2 * k.factorial ^ 2 = 4 * (k.factorial * n.choose k) ^ 2 := by ring
    _ ≤ 4 * (n ^ k) ^ 2 := by gcongr
    _ = 4 * (n ^ 2) ^ k := by ring
    _ ≤ 4 * (2 ^ k) ^ k := by gcongr
    _ = 2 ^ (k * (k - 1)) * 2 ^ (k + 2) := by
        rw [← pow_mul, ← pow_add, show k * (k - 1) + (k + 2) = k * k + 2 by omega, pow_add]
        ring
    _ < 2 ^ (k * (k - 1)) * k.factorial ^ 2 :=
        Nat.mul_lt_mul_of_pos_left (two_pow_add_two_lt_factorial_sq hk) (by positivity)
    _ = (2 ^ k.choose 2) ^ 2 * k.factorial ^ 2 := by rw [← pow_mul, mul_comm _ 2, hchoose]

/-- **Erdős's lower bound**: for `k ≥ 3`, `R(k, k) > 2^{k/2}`. For every `n` with
`n ^ 2 ≤ 2 ^ k`, in particular for `n = ⌊2^{k/2}⌋`, some graph on `n` vertices has no
clique of size `k` and no independent set of size `k`.

This is the milestone *Erdős's lower bound*. -/
theorem exists_cliqueFree_indepSetFree_of_sq_le {n k : ℕ} (hk : 3 ≤ k) (hn : n ^ 2 ≤ 2 ^ k) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ G.IndepSetFree k :=
  exists_cliqueFree_indepSetFree_of_two_mul_choose_lt (two_mul_choose_lt_of_sq_le hk hn)

end Ramsey

end
