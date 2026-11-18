module

public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Star
public import Mathlib.Data.ZMod.Basic

/-!
# Ramsey numbers of stars

Let `K_{1,n}` be the star with `n` edges, here `SimpleGraph.starGraph (0 : Fin (n + 1))`.
For `n, m ≥ 1`, `R(K_{1,n}, K_{1,m}) = n + m - ε`, where `ε = 1` if `n` and `m` are both even
and `ε = 0` otherwise.

## Main results

* `Ramsey.starGraph_isContained_iff`: a graph contains `K_{1,n}` if and only if some vertex has
  degree at least `n`.
* `Ramsey.exists_isRegularOfDegree`: for `d < N` with `d * N` even, there is a `d`-regular
  graph on `ZMod N`, a circulant graph or the complement of one.
* `Ramsey.stars`: the milestone *Stars*, with both halves.

## Proof

Every vertex has degree `N - 1` in `G` and its complement together. If `N = n + m`, some vertex
has degree at least `n` in `G` or at least `m` in `Gᶜ`. If `n` and `m` are both even and
`N = n + m - 1`, a graph with neither would be `(n - 1)`-regular, with `n - 1` and `N` odd,
against the handshake lemma. For the lower half, an `(n - 1)`-regular graph on
`n + m - ε - 1` vertices has an `(m - 1 - ε)`-regular complement.

## References

* F. Harary, *Recent results on generalized Ramsey theory for graphs*, 1972.
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §5.5.
-/

public section

namespace Ramsey

open SimpleGraph Finset

/-- A graph contains the star `K_{1,n}` if and only if some vertex has degree at least `n`. -/
theorem starGraph_isContained_iff {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    starGraph (0 : Fin (n + 1)) ⊑ G ↔ ∃ v, n ≤ G.degree v := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f 0, ?_⟩
    have := f.degree_le 0
    rwa [degree_starGraph_center, Fintype.card_fin, Nat.add_sub_cancel] at this
  · rintro ⟨v, hv⟩
    obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hv
    let e : Fin n ≃ s := (s.equivFinOfCardEq hcard).symm
    let f : Fin (n + 1) → V := Fin.cases v (fun i => (e i : V))
    have hadj : ∀ i : Fin n, G.Adj v (f i.succ) := fun i => by
      simpa [f] using hs (e i).2
    have hinj : Function.Injective f := by
      intro a b hab
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ j => exact absurd hab (hadj j).ne
      | succ i =>
        cases b using Fin.cases with
        | zero => exact absurd hab.symm (hadj i).ne
        | succ j =>
          have : (e i : V) = e j := hab
          rw [e.injective (Subtype.ext this)]
    refine isContained_iff_exists_le_comap.mpr ⟨⟨f, hinj⟩, fun a b hab => ?_⟩
    rw [starGraph_adj] at hab
    obtain ⟨hne, rfl | rfl⟩ := hab
    · cases b using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j => exact hadj j
    · cases a using Fin.cases with
      | zero => exact absurd rfl hne
      | succ j => exact (hadj j).symm

/-- In a circulant graph on a finite abelian group whose set of jumps `t` is symmetric and does
not contain `0`, every vertex has degree `#t`. -/
theorem degree_circulantGraph {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (t : Finset A) (h0 : (0 : A) ∉ t) (hneg : ∀ x ∈ t, -x ∈ t) (v : A) :
    (circulantGraph (t : Set A)).degree v = #t := by
  rw [← card_neighborFinset_eq_degree]
  have : (circulantGraph (t : Set A)).neighborFinset v = t.image (v + ·) := by
    ext w
    simp only [mem_neighborFinset, circulantGraph_adj, mem_coe, mem_image]
    constructor
    · rintro ⟨-, h | h⟩
      · exact ⟨w - v, by simpa using hneg _ h, add_sub_cancel v w⟩
      · exact ⟨w - v, h, add_sub_cancel v w⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨fun h => h0 ?_, Or.inr (by simpa using hx)⟩
      have hx0 : x = 0 := by simpa using congrArg (· - v) h.symm
      simpa [hx0] using hx
  rw [this, card_image_of_injective _ (add_right_injective v)]

/-- For `1 ≤ a`, the circulant graph on `ZMod N` with jumps `a, a + 1, …, N - a` is
`(N + 1 - 2a)`-regular. -/
theorem isRegularOfDegree_circulantGraph_Icc (N a : ℕ) [NeZero N] (ha : 1 ≤ a) :
    (circulantGraph ((((Icc a (N - a)).image (Nat.cast : ℕ → ZMod N)) : Finset (ZMod N)) :
      Set (ZMod N))).IsRegularOfDegree (N - a + 1 - a) := by
  intro v
  have hlt : ∀ x ∈ Icc a (N - a), x < N := fun x hx => by
    simp only [mem_Icc] at hx
    have := NeZero.pos N
    omega
  rw [degree_circulantGraph]
  · rw [card_image_of_injOn, Nat.card_Icc]
    intro x hx y hy hxy
    have := congrArg ZMod.val hxy
    simpa [ZMod.val_cast_of_lt (hlt x hx), ZMod.val_cast_of_lt (hlt y hy)] using this
  · simp only [mem_image, not_exists, not_and]
    intro x hx h
    rw [ZMod.natCast_eq_zero_iff] at h
    have := Nat.eq_zero_of_dvd_of_lt h (hlt x hx)
    simp only [mem_Icc] at hx
    omega
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro x hx
    have hxN := (hlt x hx).le
    refine ⟨N - x, ?_, ?_⟩
    · simp only [mem_Icc] at hx ⊢
      omega
    · rw [Nat.cast_sub hxN, ZMod.natCast_self, zero_sub]

/-- For `d < N` with `d * N` even, there is a `d`-regular graph on `ZMod N`. -/
theorem exists_isRegularOfDegree (N d : ℕ) [NeZero N] (hd : d < N) (hpar : Even (d * N)) :
    ∃ (G : SimpleGraph (ZMod N)) (_ : DecidableRel G.Adj), G.IsRegularOfDegree d := by
  classical
  rcases Nat.even_or_odd (d + N) with h | h
  · -- `d` and `N` are both even: complement a circulant graph of odd degree `N - 1 - d`.
    have hN : Even N := by
      rcases Nat.even_mul.mp hpar with hd' | hN
      · exact (Nat.even_add.mp h).mp hd'
      · exact hN
    obtain ⟨k, hk⟩ := hN
    obtain ⟨j, hj⟩ := (Nat.even_add.mp h).mpr ⟨k, hk⟩
    have := (isRegularOfDegree_circulantGraph_Icc N (j + 1) (by omega)).compl
    have e : d = Fintype.card (ZMod N) - 1 - (N - (j + 1) + 1 - (j + 1)) := by
      rw [ZMod.card]
      omega
    rw [e]
    exact ⟨_, _, this⟩
  · obtain ⟨k, hk⟩ := h
    have := isRegularOfDegree_circulantGraph_Icc N (k + 1 - d) (by omega)
    have e : d = N - (k + 1 - d) + 1 - (k + 1 - d) := by omega
    rw [e]
    exact ⟨_, _, this⟩

/-- The upper half of the milestone *Stars*: for `n, m ≥ 1`, every graph on `n + m - ε`
vertices contains `K_{1,n}` or its complement contains `K_{1,m}`, where `ε = 1` if `n` and `m`
are both even and `ε = 0` otherwise. -/
theorem stars_upper {V : Type*} [Fintype V] {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m)
    (G : SimpleGraph V) (hV : Fintype.card V = n + m - if Even n ∧ Even m then 1 else 0) :
    starGraph (0 : Fin (n + 1)) ⊑ G ∨ starGraph (0 : Fin (m + 1)) ⊑ Gᶜ := by
  classical
  rw [starGraph_isContained_iff, starGraph_isContained_iff]
  by_contra! h
  obtain ⟨h1, h2⟩ := h
  -- Every vertex has degree at most `n - 1` in `G` and at most `m - 1` in `Gᶜ`.
  have hdeg : ∀ v, n - (if Even n ∧ Even m then 1 else 0) ≤ G.degree v ∧ G.degree v ≤ n - 1 := by
    intro v
    have hv1 := h1 v
    have hv2 := h2 v
    rw [degree_compl, hV] at hv2
    omega
  have hne : Nonempty V := Fintype.card_pos_iff.mp (by split_ifs at hV <;> omega)
  obtain ⟨v₀⟩ := hne
  split_ifs at hV hdeg with hev
  · -- `G` is `(n - 1)`-regular on an odd number of vertices, with `n - 1` odd.
    have hreg : ∀ v, G.degree v = n - 1 := fun v => by
      have := hdeg v
      omega
    obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := hev
    have hsum := G.sum_degrees_eq_twice_card_edges
    simp only [hreg, sum_const, card_univ, smul_eq_mul, hV] at hsum
    have hodd : Odd ((a + a + (b + b) - 1) * (a + a - 1)) :=
      Nat.odd_mul.mpr ⟨⟨a + b - 1, by omega⟩, ⟨a - 1, by omega⟩⟩
    rw [hsum] at hodd
    exact (Nat.not_odd_iff_even.mpr (even_two_mul _)) hodd
  · have := hdeg v₀
    omega
/-- The lower half of the milestone *Stars*: for `n, m ≥ 1`, some graph on `n + m - ε - 1`
vertices does not contain `K_{1,n}`, and neither does its complement contain `K_{1,m}`, where
`ε = 1` if `n` and `m` are both even and `ε = 0` otherwise. -/
theorem stars_lower {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    ∃ G : SimpleGraph (Fin (n + m - (if Even n ∧ Even m then 1 else 0) - 1)),
      ¬ starGraph (0 : Fin (n + 1)) ⊑ G ∧ ¬ starGraph (0 : Fin (m + 1)) ⊑ Gᶜ := by
  classical
  set N := n + m - (if Even n ∧ Even m then 1 else 0) - 1 with hN
  have hN1 : 1 ≤ N := by
    split_ifs at hN with h
    · obtain ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩ := h
      omega
    · rcases Nat.even_or_odd n with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;> omega
  have : NeZero N := ⟨by omega⟩
  have hpar : Even ((n - 1) * N) := by
    split_ifs at hN with h
    · obtain ⟨-, ⟨b, rfl⟩⟩ := h
      rcases Nat.even_or_odd n with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact Nat.even_mul.mpr (Or.inr ⟨a + b - 1, by omega⟩)
      · exact Nat.even_mul.mpr (Or.inl ⟨a, by omega⟩)
    · rcases Nat.even_or_odd n with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · have hm' : Odd m := Nat.not_even_iff_odd.mp fun hm' => h ⟨⟨a, rfl⟩, hm'⟩
        obtain ⟨b, rfl⟩ := hm'
        exact Nat.even_mul.mpr (Or.inr ⟨a + b, by omega⟩)
      · exact Nat.even_mul.mpr (Or.inl ⟨a, by omega⟩)
  have hlt : n - 1 < N := by
    split_ifs at hN with h
    · obtain ⟨-, ⟨b, rfl⟩⟩ := h
      omega
    · omega
  obtain ⟨H, _, hH⟩ := exists_isRegularOfDegree N (n - 1) hlt hpar
  let e : Fin N ≃ ZMod N := Fintype.equivOfCardEq (by simp [ZMod.card])
  have hcompl : (H.comap e)ᶜ = Hᶜ.comap e := by
    ext a b
    simp [e.injective.eq_iff]
  refine ⟨H.comap e, ?_, ?_⟩
  · rw [isContained_congr_right (Iso.comap e H), starGraph_isContained_iff]
    push Not
    intro v
    rw [hH v]
    omega
  · rw [hcompl, isContained_congr_right (Iso.comap e Hᶜ), starGraph_isContained_iff]
    push Not
    intro v
    rw [degree_compl, hH v, ZMod.card]
    split_ifs at hN with h
    · obtain ⟨-, ⟨b, rfl⟩⟩ := h
      omega
    · omega

/-- The milestone *Stars*: for `n, m ≥ 1`, `R(K_{1,n}, K_{1,m}) = n + m - ε`, where `ε = 1` if
`n` and `m` are both even and `ε = 0` otherwise. That is, every graph on `n + m - ε` vertices
contains `K_{1,n}` or its complement contains `K_{1,m}`, and some graph on `n + m - ε - 1`
vertices does neither. -/
theorem stars {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
      Fintype.card V = n + m - (if Even n ∧ Even m then 1 else 0) →
        starGraph (0 : Fin (n + 1)) ⊑ G ∨ starGraph (0 : Fin (m + 1)) ⊑ Gᶜ) ∧
    ∃ G : SimpleGraph (Fin (n + m - (if Even n ∧ Even m then 1 else 0) - 1)),
      ¬ starGraph (0 : Fin (n + 1)) ⊑ G ∧ ¬ starGraph (0 : Fin (m + 1)) ⊑ Gᶜ :=
  ⟨fun G hV => stars_upper hn hm G hV, stars_lower hn hm⟩

end Ramsey

end
