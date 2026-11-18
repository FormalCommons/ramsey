module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Ramsey's theorem for graphs

This file proves Ramsey's theorem for graphs: for all `s` and `t` there is an `n` such that
every graph on `n` vertices has a clique of size `s` or an independent set of size `t`. It
defines the Ramsey number `R(s, t)` as the least such `n`, and proves its basic properties.

## Main definitions

* `Ramsey.IsRamsey s t n`: every graph on `Fin n` has a clique of size `s` or an independent set
  of size `t`.
* `Ramsey.ramseyNumber s t`: the Ramsey number `R(s, t)`, the least `n` with `IsRamsey s t n`.

## Main results

* `Ramsey.ramsey_graph`: Ramsey's theorem for graphs, on any `Fintype` vertex type.
* `Ramsey.ramseyNumber_comm`, `Ramsey.ramseyNumber_one_left`, `Ramsey.ramseyNumber_two_left`:
  `R(s, t) = R(t, s)`, `R(1, t) = 1` and `R(2, t) = t`.
* `Ramsey.ramseyNumber_le_add`, `Ramsey.ramseyNumber_lt_add`: the recurrence
  `R(s, t) ≤ R(s - 1, t) + R(s, t - 1)` of Greenwood and Gleason, and its strict form.
* `Ramsey.ramseyNumber_le_choose`: the bound `R(s, t) ≤ (s + t - 2).choose (s - 1)` of Erdős and
  Szekeres.
* `Ramsey.ramseyNumber_eq_of`: an upper half and a lower half give the value of `R(s, t)`.

These form the milestone *Ramsey's theorem for graphs* of the plan
(`atlas/ramsey-theorem.md` in FormalCommons/ramsey-plan).

## References

* R. L. Graham, B. L. Rothschild, J. H. Spencer, *Ramsey Theory*, Ch. 1.
* R. E. Greenwood, A. M. Gleason, *Combinatorial relations and chromatic graphs*, 1955.
* P. Erdős, G. Szekeres, *A combinatorial problem in geometry*, 1935.
-/

@[expose] public section

namespace Ramsey

/-- `IsRamsey s t n` says that every graph on `n` vertices, here on `Fin n`, has a clique of size
`s` or an independent set of size `t`. By `Ramsey.IsRamsey.of_le_card` it then holds for graphs on
any `Fintype` with at least `n` elements. -/
def IsRamsey (s t n : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t

end Ramsey

end

public section

namespace Ramsey

open SimpleGraph Finset Fintype

universe u

private lemma compl_comap {V W : Type*} (f : V ↪ W) (G : SimpleGraph W) :
    (G.comap f)ᶜ = Gᶜ.comap f := by
  ext a b
  simp [f.injective.ne_iff]

private lemma of_comap {s t : ℕ} {V W : Type*} (f : V ↪ W) (G : SimpleGraph W)
    (h : ¬ (G.comap f).CliqueFree s ∨ ¬ (G.comap f).IndepSetFree t) :
    ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t := by
  have hc : G.comap f ⊑ G := (Embedding.comap f G).isContained
  have hc' : (G.comap f)ᶜ ⊑ Gᶜ := by
    rw [compl_comap]; exact (Embedding.comap f Gᶜ).isContained
  rcases h with h | h
  · exact .inl fun hG => h (hG.comap hc)
  · refine .inr fun hG => h ?_
    rw [← cliqueFree_compl] at hG ⊢
    exact hG.comap hc'

/-- If every graph on `n` vertices has a clique of size `s` or an independent set of size `t`, so
does every graph on a vertex type with at least `n` elements. -/
theorem IsRamsey.of_le_card {s t n : ℕ} (h : IsRamsey s t n) {V : Type u} [Fintype V]
    (hV : n ≤ card V) (G : SimpleGraph V) : ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t :=
  of_comap ((Fin.castLEEmb hV).trans (Fintype.equivFin V).symm.toEmbedding) G (h _)

/-- `IsRamsey s t n` says the same about graphs on any `Fintype` with `n` elements. -/
theorem isRamsey_iff {s t n : ℕ} :
    IsRamsey s t n ↔ ∀ (V : Type u) [Fintype V], card V = n →
      ∀ G : SimpleGraph V, ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t :=
  ⟨fun h V _ hV G => h.of_le_card hV.ge G, fun h G =>
    of_comap (Equiv.ulift.{u} (α := Fin n)).toEmbedding G (h _ (by simp) _)⟩

/-- `IsRamsey s t n` is monotone in `n`. -/
theorem IsRamsey.mono {s t n m : ℕ} (h : IsRamsey s t n) (hnm : n ≤ m) : IsRamsey s t m :=
  fun G => h.of_le_card (by simpa using hnm) G

/-- Taking complements swaps cliques and independent sets. -/
theorem IsRamsey.symm {s t n : ℕ} (h : IsRamsey s t n) : IsRamsey t s n := fun G => by
  rcases h Gᶜ with h | h
  · exact .inr (by simpa using h)
  · exact .inl (by simpa using h)

/-- `IsRamsey s t n` is symmetric in `s` and `t`. -/
theorem isRamsey_comm {s t n : ℕ} : IsRamsey s t n ↔ IsRamsey t s n :=
  ⟨IsRamsey.symm, IsRamsey.symm⟩

/-- Every graph has a clique of size `0`, the empty set. -/
theorem isRamsey_zero_left (t n : ℕ) : IsRamsey 0 t n := fun _ => .inl not_cliqueFree_zero

/-- Every graph has an independent set of size `0`, the empty set. -/
theorem isRamsey_zero_right (s n : ℕ) : IsRamsey s 0 n := (isRamsey_zero_left s n).symm

/-- A graph on fewer than `s` vertices has no clique of size `s` and no independent set of size
`s`. -/
private lemma cliqueFree_and_indepSetFree_of_card_lt {V : Type*} [Fintype V] (G : SimpleGraph V)
    {s : ℕ} (h : card V < s) : G.CliqueFree s ∧ G.IndepSetFree s :=
  ⟨cliqueFree_of_card_lt h, by rw [← cliqueFree_compl]; exact cliqueFree_of_card_lt h⟩

/-- For `s, t ≥ 1`, the graph on no vertices has neither a clique of size `s` nor an
independent set of size `t`. -/
theorem not_isRamsey_zero {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : ¬ IsRamsey s t 0 := by
  intro h
  rcases h ⊥ with h | h
  · exact h (cliqueFree_of_card_lt (by simp; omega))
  · exact h ((cliqueFree_and_indepSetFree_of_card_lt ⊥ (by simp; omega)).2)

/-- In a graph with no clique of size `s + 1` and no independent set of size `t + 1`, every vertex
has fewer than `a` neighbours, if every graph on `a` vertices has a clique of size `s` or an
independent set of size `t + 1`. -/
private lemma degree_lt {s t a : ℕ} (h : IsRamsey s (t + 1) a) {V : Type*} [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hs : G.CliqueFree (s + 1))
    (ht : G.IndepSetFree (t + 1)) (v : V) : G.degree v < a := by
  by_contra hv
  push Not at hv
  have hcard : a ≤ card (G.neighborSet v) := by rw [card_neighborSet_eq_degree]; exact hv
  let f : G.neighborSet v ↪ V := Function.Embedding.subtype _
  rcases h.of_le_card hcard (G.comap f) with h | h
  · rw [CliqueFree] at h
    push Not at h
    obtain ⟨u, hu⟩ := h
    refine hs _ ((hu.map (f := f)).mono (map_comap_le f G) |>.insert (a := v) ?_)
    simp only [mem_map]
    rintro _ ⟨w, -, rfl⟩
    exact w.2
  · refine h fun u hu => ht (u.map f) ?_
    rw [← isNClique_compl] at hu ⊢
    rw [compl_comap] at hu
    exact (hu.map (f := f)).mono (map_comap_le f Gᶜ)

/-- The recurrence of Greenwood and Gleason, for `IsRamsey`: a vertex has at least `a` neighbours
or at least `b` non-neighbours. -/
theorem IsRamsey.add {s t a b : ℕ} (h₁ : IsRamsey s (t + 1) a) (h₂ : IsRamsey (s + 1) t b)
    (hab : 0 < a + b) : IsRamsey (s + 1) (t + 1) (a + b) := by
  intro G
  by_contra! hG
  classical
  have d₁ := degree_lt h₁ G hG.1 hG.2 ⟨0, hab⟩
  have d₂ := degree_lt h₂.symm Gᶜ (by simpa using hG.2) (by simpa using hG.1) ⟨0, hab⟩
  have hc := degree_compl G (v := ⟨0, hab⟩)
  simp only [Fintype.card_fin] at hc
  omega

/-- The strict form of the recurrence, for `IsRamsey`: when `a` and `b` are even, a graph on
`a + b - 1` vertices with neither would have all degrees equal to the odd number `a - 1`, against
the handshake lemma. -/
theorem IsRamsey.add_sub_one {s t a b : ℕ} (h₁ : IsRamsey s (t + 1) a)
    (h₂ : IsRamsey (s + 1) t b) (ha : Even a) (hb : Even b) (ha₀ : 0 < a) (hb₀ : 0 < b) :
    IsRamsey (s + 1) (t + 1) (a + b - 1) := by
  intro G
  by_contra! hG
  classical
  have hdeg : ∀ v, G.degree v = a - 1 := by
    intro v
    have d₁ := degree_lt h₁ G hG.1 hG.2 v
    have d₂ := degree_lt h₂.symm Gᶜ (by simpa using hG.2) (by simpa using hG.1) v
    have hc := degree_compl G (v := v)
    simp only [Fintype.card_fin] at hc
    omega
  have hsum := G.sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  have h₃ : ¬ Even (a - 1) := by
    rw [← Nat.even_add_one, Nat.sub_add_cancel ha₀]; exact ha
  have h₄ : ¬ Even (a + b - 1) := by
    rw [← Nat.even_add_one, Nat.sub_add_cancel (by omega)]; exact ha.add hb
  have : Even ((a + b - 1) * (a - 1)) := ⟨#G.edgeFinset, by omega⟩
  rw [Nat.even_mul] at this
  tauto

/-- Ramsey's theorem for graphs on `Fin n`. -/
theorem exists_isRamsey (s t : ℕ) : ∃ n, IsRamsey s t n := by
  induction s generalizing t with
  | zero => exact ⟨0, isRamsey_zero_left t 0⟩
  | succ s ihs =>
    induction t with
    | zero => exact ⟨0, isRamsey_zero_right _ 0⟩
    | succ t iht =>
      obtain ⟨a, ha⟩ := ihs (t + 1)
      obtain ⟨b, hb⟩ := iht
      exact ⟨a + 1 + b, (ha.mono (Nat.le_succ a)).add hb (by omega)⟩

/-- **Ramsey's theorem for graphs**: for all `s` and `t` there is an `n` such that every graph on
`n` vertices has a clique of size `s` or an independent set of size `t`.

This is the existence statement of the milestone *Ramsey's theorem for graphs*. -/
theorem ramsey_graph (s t : ℕ) : ∃ n, ∀ (V : Type u) [Fintype V], card V = n →
    ∀ G : SimpleGraph V, ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t :=
  (exists_isRamsey s t).imp fun _ h => isRamsey_iff.1 h

open Classical in
/-- The Ramsey number `R(s, t)`: the least `n` such that every graph on `n` vertices has a clique
of size `s` or an independent set of size `t`. -/
noncomputable def ramseyNumber (s t : ℕ) : ℕ := Nat.find (exists_isRamsey s t)

/-- Every graph on `R(s, t)` vertices has a clique of size `s` or an independent set of size `t`. -/
theorem isRamsey_ramseyNumber (s t : ℕ) : IsRamsey s t (ramseyNumber s t) := by
  classical exact Nat.find_spec (exists_isRamsey s t)

/-- `R(s, t)` is at most every `n` with `IsRamsey s t n`. -/
theorem ramseyNumber_le {s t n : ℕ} (h : IsRamsey s t n) : ramseyNumber s t ≤ n := by
  classical exact Nat.find_min' (exists_isRamsey s t) h

/-- `IsRamsey s t n` holds exactly for `n ≥ R(s, t)`. -/
theorem isRamsey_iff_ramseyNumber_le {s t n : ℕ} : IsRamsey s t n ↔ ramseyNumber s t ≤ n :=
  ⟨ramseyNumber_le, (isRamsey_ramseyNumber s t).mono⟩

/-- Every graph on a vertex type with at least `R(s, t)` elements has a clique of size `s` or an
independent set of size `t`. -/
theorem ramseyNumber_spec {s t : ℕ} {V : Type u} [Fintype V] (hV : ramseyNumber s t ≤ card V)
    (G : SimpleGraph V) : ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t :=
  (isRamsey_ramseyNumber s t).of_le_card hV G

/-- If every graph on `N` vertices has a clique of size `s` or an independent set of size `t`
(the upper half), and some graph on `N - 1` vertices has neither (the lower half), then
`R(s, t) = N`.

This is part (4) of the milestone *Ramsey's theorem for graphs*. -/
theorem ramseyNumber_eq_of {s t N : ℕ}
    (hup : ∀ G : SimpleGraph (Fin N), ¬ G.CliqueFree s ∨ ¬ G.IndepSetFree t)
    {V : Type u} [Fintype V] (hV : card V = N - 1) (G : SimpleGraph V) (hs : G.CliqueFree s)
    (ht : G.IndepSetFree t) : ramseyNumber s t = N := by
  refine le_antisymm (ramseyNumber_le hup) ?_
  by_contra! hlt
  rcases ramseyNumber_spec (s := s) (t := t) (by omega) G with h | h <;> contradiction

/-- `R(s, t) = R(t, s)`. This is part of (1) of the milestone *Ramsey's theorem for graphs*. -/
theorem ramseyNumber_comm (s t : ℕ) : ramseyNumber s t = ramseyNumber t s :=
  le_antisymm (ramseyNumber_le (isRamsey_ramseyNumber t s).symm)
    (ramseyNumber_le (isRamsey_ramseyNumber s t).symm)

/-- `R(s, t) ≥ 1` for `s, t ≥ 1`. -/
theorem ramseyNumber_pos {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 < ramseyNumber s t := by
  by_contra! h
  exact not_isRamsey_zero hs ht (isRamsey_iff_ramseyNumber_le.2 h)

/-- `R(1, t) = 1` for `t ≥ 1`. This is part of (1) of the milestone *Ramsey's theorem for
graphs*. -/
theorem ramseyNumber_one_left {t : ℕ} (ht : 1 ≤ t) : ramseyNumber 1 t = 1 := by
  refine ramseyNumber_eq_of (fun G => .inl ?_) (V := Fin 0) rfl ⊥
    (cliqueFree_of_card_lt (by simp))
    (cliqueFree_and_indepSetFree_of_card_lt ⊥ (by simp; omega)).2
  rw [cliqueFree_one, not_isEmpty_iff]
  exact ⟨0⟩

/-- `R(s, 1) = 1` for `s ≥ 1`. -/
theorem ramseyNumber_one_right {s : ℕ} (hs : 1 ≤ s) : ramseyNumber s 1 = 1 := by
  rw [ramseyNumber_comm, ramseyNumber_one_left hs]

/-- `R(2, t) = t`. This is part of (1) of the milestone *Ramsey's theorem for graphs*. -/
theorem ramseyNumber_two_left (t : ℕ) : ramseyNumber 2 t = t := by
  have hup : IsRamsey 2 t t := fun G => by
    by_cases hG : G = ⊥
    · subst hG
      refine .inr fun h => h univ ?_
      rw [← isNClique_compl, compl_bot]
      exact ⟨by simp [isClique_iff, Set.Pairwise], by simp⟩
    · exact .inl (by rwa [cliqueFree_two])
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · exact le_antisymm (ramseyNumber_le hup) (Nat.zero_le _)
  exact ramseyNumber_eq_of hup (V := Fin (t - 1)) (by simp) ⊥ (cliqueFree_bot le_rfl)
    (cliqueFree_and_indepSetFree_of_card_lt ⊥ (by simp; omega)).2

/-- `R(s, 2) = s`. -/
theorem ramseyNumber_two_right (s : ℕ) : ramseyNumber s 2 = s := by
  rw [ramseyNumber_comm, ramseyNumber_two_left]

/-- `R(s, t) ≤ R(s - 1, t) + R(s, t - 1)` for `s, t ≥ 2`.

This is part (2) of the milestone *Ramsey's theorem for graphs*, without its strict form, which is
`Ramsey.ramseyNumber_lt_add`. -/
theorem ramseyNumber_le_add {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ramseyNumber s t ≤ ramseyNumber (s - 1) t + ramseyNumber s (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  exact ramseyNumber_le ((isRamsey_ramseyNumber _ _).add (isRamsey_ramseyNumber _ _)
    (Nat.add_pos_left (ramseyNumber_pos (by omega) (by omega)) _))

/-- `R(s, t) < R(s - 1, t) + R(s, t - 1)` for `s, t ≥ 2` when `R(s - 1, t)` and `R(s, t - 1)` are
both even.

This is the strict form in part (2) of the milestone *Ramsey's theorem for graphs*. -/
theorem ramseyNumber_lt_add {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t)
    (h₁ : Even (ramseyNumber (s - 1) t)) (h₂ : Even (ramseyNumber s (t - 1))) :
    ramseyNumber s t < ramseyNumber (s - 1) t + ramseyNumber s (t - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h₁ h₂ ⊢
  have p₁ := ramseyNumber_pos (s := s) (t := t + 1) (by omega) (by omega)
  have p₂ := ramseyNumber_pos (s := s + 1) (t := t) (by omega) (by omega)
  have := ramseyNumber_le ((isRamsey_ramseyNumber _ _).add_sub_one (isRamsey_ramseyNumber _ _)
    h₁ h₂ p₁ p₂)
  omega

/-- `R(s, t) ≤ (s + t - 2).choose (s - 1)` for `s, t ≥ 1`.

This is part (3) of the milestone *Ramsey's theorem for graphs*. -/
theorem ramseyNumber_le_choose {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) :
    ramseyNumber s t ≤ (s + t - 2).choose (s - 1) := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [show s + 1 + (t + 1) - 2 = s + t by omega, Nat.add_sub_cancel]
  clear hs ht
  induction s generalizing t with
  | zero => simp [ramseyNumber_one_left]
  | succ s ihs =>
    induction t with
    | zero => simp [ramseyNumber_one_right]
    | succ t iht =>
      calc ramseyNumber (s + 2) (t + 2)
          ≤ ramseyNumber (s + 1) (t + 2) + ramseyNumber (s + 2) (t + 1) :=
            ramseyNumber_le_add (by omega) (by omega)
        _ ≤ (s + (t + 1)).choose s + (s + 1 + t).choose (s + 1) := add_le_add (ihs _) iht
        _ = (s + 1 + (t + 1)).choose (s + 1) := by
          rw [show s + 1 + (t + 1) = (s + t + 1) + 1 by omega, Nat.choose_succ_succ]
          congr 2; omega

end Ramsey

end
