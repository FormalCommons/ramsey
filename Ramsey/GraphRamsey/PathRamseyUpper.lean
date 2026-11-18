module

public import Ramsey.GraphRamsey.PathGraph

/-!
# The upper half of the Ramsey numbers of paths

Let `P_k` be the path on `k` vertices, `SimpleGraph.pathGraph k`. For `n ≥ m ≥ 2`, every graph
on `n + ⌊m/2⌋ - 1` vertices contains `P_n`, or its complement contains `P_m`. This is the upper
half of the milestone *Paths*, `R(P_n, P_m) = n + ⌊m/2⌋ - 1`.

## Main results

* `Ramsey.pathGraph_isContained_of_list`: a list of distinct vertices in which consecutive ones
  are adjacent gives a copy of the path graph on at most as many vertices.
* `Ramsey.pathGraph_ramsey_upper`: the upper half of the milestone *Paths*.

## Proof

We follow Gerencsér and Gyárfás, and call the edges of `G` red and those of `Gᶜ` blue. The proof
is by induction on `n`. The induction gives a red path `u₀, u₁, …, u_{n-2}` on `n - 1`
vertices: for `m < n` from the case `(n - 1, m)`, and for `m = n` from the case
`(n - 1, n - 1)`, after swapping the colours if that gives a blue path, which is allowed since
the statement is then symmetric. We may assume that there is no red path on `n` vertices. Let
`X` be the set of the other `t = ⌊m/2⌋` vertices. Every `x ∈ X` is blue to `u₀` and `u_{n-2}`,
since otherwise it would extend the red path, and it is blue to `u_j` or `u_{j+1}` for every
`j`, since otherwise it could be inserted between them.

Group the interior vertices `u₁, …, u_{n-3}` into disjoint consecutive pairs. For each pair, and
any three vertices of `X`, one vertex of the pair is blue to two of the three. Using one pair
for each vertex of `X` after the first two, we build greedily two disjoint blue paths that
alternate between `X` and the pairs, start and end in `X`, and together cover `X`. Each step
adds a vertex `x` of `X`, and a vertex `w` of the next pair that is blue to two of `x` and the
last vertices `a`, `c` of the two paths: it appends `w, x` to one path, or, if `w` is blue to
`a` and `c`, joins the two paths through `w` and starts a new path at `x`. The two paths and
`u₀`, `u_{n-2}` make a blue path `u₀, …, u_{n-2}, …` on `2t` vertices. If `m` is odd, there is a
spare pair, and one of its vertices is blue to the last vertex of this path, which gives
`2t + 1 = m` vertices.

## References

* L. Gerencsér, A. Gyárfás, *On Ramsey-type problems*, Ann. Univ. Sci. Budapest. Eötvös Sect.
  Math. 10 (1967), 167–170.
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §5.1.
-/

public section

namespace Ramsey

open SimpleGraph

variable {V : Type*}

/-- A list of distinct vertices, in which consecutive ones are adjacent in `H`, with at least
`k` entries gives a copy of the path graph on `k` vertices in `H`. -/
theorem pathGraph_isContained_of_list {H : SimpleGraph V} {l : List V} {k : ℕ} (hn : l.Nodup)
    (hc : l.IsChain H.Adj) (hk : k ≤ l.length) : pathGraph k ⊑ H := by
  refine ⟨⟨⟨fun i ↦ l[i.val], fun {i j} hij ↦ ?_⟩, fun i j hij ↦ ?_⟩⟩
  · rcases pathGraph_adj.mp hij with h | h
    · have := hc.getElem i.val (by omega)
      simp only [h] at this
      exact this
    · have := hc.getElem j.val (by omega)
      simp only [h] at this
      exact this.symm
  · exact Fin.ext ((hn.getElem_inj_iff).mp hij)

/-- A list of distinct vertices of `s`, with consecutive ones adjacent in `H`, and with at least
`k` entries. -/
private def HasPath (H : SimpleGraph V) (s : Finset V) (k : ℕ) : Prop :=
  ∃ l : List V, l.Nodup ∧ l.IsChain H.Adj ∧ (∀ x ∈ l, x ∈ s) ∧ k ≤ l.length

private theorem HasPath.mono {H : SimpleGraph V} {s s' : Finset V} {k : ℕ} (h : HasPath H s k)
    (hs : s ⊆ s') : HasPath H s' k := by
  obtain ⟨l, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨l, h₁, h₂, fun x hx ↦ hs (h₃ x hx), h₄⟩

/-- `pairs [x₁, x₂, x₃, x₄, …] = [(x₁, x₂), (x₃, x₄), …]`. -/
private def pairs : List V → List (V × V)
  | x :: y :: l => (x, y) :: pairs l
  | _ => []

private theorem length_pairs : ∀ l : List V, (pairs l).length = l.length / 2
  | [] => by simp [pairs]
  | [_] => by simp [pairs]
  | _ :: _ :: l => by simp [pairs, length_pairs l]; omega

private theorem exists_eq_of_mem_pairs :
    ∀ {l : List V} {p : V × V}, p ∈ pairs l → ∃ l₁ l₂, l = l₁ ++ p.1 :: p.2 :: l₂
  | [], _, h => by simp [pairs] at h
  | [_], _, h => by simp [pairs] at h
  | x :: y :: l, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨[], l, rfl⟩
    · obtain ⟨l₁, l₂, hl⟩ := exists_eq_of_mem_pairs h
      exact ⟨x :: y :: l₁, l₂, by simp [hl]⟩

/-- The entries of a list of pairs, in order. -/
private def flat (ps : List (V × V)) : List V := ps.flatMap fun p ↦ [p.1, p.2]

private theorem flat_append (ps qs : List (V × V)) : flat (ps ++ qs) = flat ps ++ flat qs := by
  simp [flat]

private theorem flat_cons (p : V × V) (ps : List (V × V)) :
    flat (p :: ps) = p.1 :: p.2 :: flat ps := by
  simp [flat]

private theorem flat_pairs_sublist : ∀ l : List V, (flat (pairs l)).Sublist l
  | [] => by simp [pairs, flat]
  | [_] => by simp [pairs, flat]
  | x :: y :: l => by
    rw [pairs, flat_cons]
    exact ((flat_pairs_sublist l).cons_cons y).cons_cons x

private theorem nodup_cons_append_singleton {a b : V} {l : List V} (h : (a :: (l ++ [b])).Nodup) :
    a ∉ l ∧ b ∉ l ∧ a ≠ b ∧ l.Nodup := by
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons,
    List.not_mem_nil] at h
  grind

private theorem nodup_cons_append_cons {a b : V} {d₁ d₂ : List V} (h : (d₁ ++ d₂).Nodup)
    (h₁ : ∀ y ∈ d₁ ++ d₂, y ≠ a ∧ y ≠ b) (h₂ : a ≠ b) : (a :: (d₁ ++ b :: d₂)).Nodup := by
  simp only [List.nodup_cons, List.nodup_append, List.mem_append, List.mem_cons] at h h₁ ⊢
  grind

/-- `c` is nonempty, and its first and last entries are in `X`. -/
private def GoodEnds (X : Set V) (c : List V) : Prop :=
  c ≠ [] ∧ (∀ x ∈ c.head?, x ∈ X) ∧ ∀ x ∈ c.getLast?, x ∈ X

/-- The greedy step of the proof: given two disjoint `B`-paths that start and end in `X`, a
list `xs` of further vertices of `X`, and as many pairs, such that every vertex of `X` is
adjacent in `B` to a vertex of each pair, there are two disjoint `B`-paths that start and end in
`X`, use only these vertices, and have `2 * xs.length` more vertices in total. -/
private theorem greedy (B : SimpleGraph V) (X : Set V) :
    ∀ (xs : List V) (ps : List (V × V)) (c₁ c₂ : List V),
    xs.length = ps.length →
    (∀ p ∈ ps, ∀ x ∈ X, B.Adj x p.1 ∨ B.Adj x p.2) →
    (∀ x ∈ xs, x ∈ X) → (c₁ ++ c₂ ++ xs ++ flat ps).Nodup →
    c₁.IsChain B.Adj → c₂.IsChain B.Adj → GoodEnds X c₁ → GoodEnds X c₂ →
    ∃ d₁ d₂ : List V, d₁.IsChain B.Adj ∧ d₂.IsChain B.Adj ∧ GoodEnds X d₁ ∧ GoodEnds X d₂ ∧
      (d₁ ++ d₂).Nodup ∧ (∀ y ∈ d₁ ++ d₂, y ∈ c₁ ++ c₂ ++ xs ++ flat ps) ∧
      (d₁ ++ d₂).length = (c₁ ++ c₂).length + 2 * xs.length
  | [], _, c₁, c₂, _, _, _, hn, h₁, h₂, he₁, he₂ =>
    ⟨c₁, c₂, h₁, h₂, he₁, he₂, hn.sublist (by simp),
      fun _ hy ↦ List.mem_append_left _ (List.mem_append_left _ hy), by simp⟩
  | _ :: _, [], _, _, hl, _, _, _, _, _, _, _ => by simp at hl
  | x :: xs, p :: ps, c₁, c₂, hl, hp, hX, hn, h₁, h₂, he₁, he₂ => by
    obtain ⟨hne₁, hh₁, hl₁⟩ := he₁
    obtain ⟨hne₂, hh₂, hl₂⟩ := he₂
    obtain ⟨a, ha⟩ : ∃ a, c₁.getLast? = some a :=
      Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne₁)
    obtain ⟨c, hc⟩ : ∃ c, c₂.getLast? = some c :=
      Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne₂)
    have haX : a ∈ X := hl₁ a ha
    have hcX : c ∈ X := hl₂ c hc
    have hxX : x ∈ X := hX x (by simp)
    have hl' : xs.length = ps.length := by simpa using hl
    have hp' : ∀ q ∈ ps, ∀ y ∈ X, B.Adj y q.1 ∨ B.Adj y q.2 :=
      fun q hq ↦ hp q (by simp [hq])
    have hX' : ∀ y ∈ xs, y ∈ X := fun y hy ↦ hX y (by simp [hy])
    rw [flat_cons] at hn ⊢
    -- one vertex `w` of the pair is adjacent to two of `a`, `c`, `x`
    have key : ∃ w, (w = p.1 ∨ w = p.2) ∧
        ((B.Adj a w ∧ B.Adj x w) ∨ (B.Adj c w ∧ B.Adj x w) ∨ (B.Adj a w ∧ B.Adj c w)) := by
      rcases hp p (by simp) a haX with h | h <;> rcases hp p (by simp) c hcX with h' | h' <;>
        rcases hp p (by simp) x hxX with h'' | h'' <;>
        first
        | exact ⟨p.1, Or.inl rfl, by tauto⟩
        | exact ⟨p.2, Or.inr rfl, by tauto⟩
    obtain ⟨w, hw, hcase⟩ := key
    rcases hcase with ⟨haw, hxw⟩ | ⟨hcw, hxw⟩ | ⟨haw, hcw⟩
    · -- append `w, x` to the first path
      obtain ⟨d₁, d₂, r₁, r₂, r₃, r₄, r₅, r₆, r₇⟩ :=
        greedy B X xs ps (c₁ ++ [w, x]) c₂ hl' hp' hX'
          (by
            rcases hw with rfl | rfl <;>
            · simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons,
                List.not_mem_nil] at hn ⊢
              grind)
          (List.isChain_append.mpr ⟨h₁, List.isChain_pair.mpr hxw.symm, by simp [ha, haw]⟩)
          h₂
          ⟨by simp, fun y hy ↦ hh₁ y (by rwa [List.head?_append_of_ne_nil _ hne₁] at hy),
            by simp [hxX]⟩
          ⟨hne₂, hh₂, hl₂⟩
      refine ⟨d₁, d₂, r₁, r₂, r₃, r₄, r₅, fun y hy ↦ ?_, by rw [r₇]; simp; omega⟩
      have := r₆ y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      rcases hw with rfl | rfl <;> tauto
    · -- append `w, x` to the second path
      obtain ⟨d₁, d₂, r₁, r₂, r₃, r₄, r₅, r₆, r₇⟩ :=
        greedy B X xs ps c₁ (c₂ ++ [w, x]) hl' hp' hX'
          (by
            rcases hw with rfl | rfl <;>
            · simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons,
                List.not_mem_nil] at hn ⊢
              grind)
          h₁
          (List.isChain_append.mpr ⟨h₂, List.isChain_pair.mpr hxw.symm, by simp [hc, hcw]⟩)
          ⟨hne₁, hh₁, hl₁⟩
          ⟨by simp, fun y hy ↦ hh₂ y (by rwa [List.head?_append_of_ne_nil _ hne₂] at hy),
            by simp [hxX]⟩
      refine ⟨d₁, d₂, r₁, r₂, r₃, r₄, r₅, fun y hy ↦ ?_, by rw [r₇]; simp; omega⟩
      have := r₆ y hy
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this ⊢
      rcases hw with rfl | rfl <;> tauto
    · -- join the two paths through `w`, and start a new path at `x`
      obtain ⟨d₁, d₂, r₁, r₂, r₃, r₄, r₅, r₆, r₇⟩ :=
        greedy B X xs ps (c₁ ++ w :: c₂.reverse) [x] hl' hp' hX'
          (by
            rcases hw with rfl | rfl <;>
            · simp only [List.nodup_append, List.nodup_cons, List.mem_append, List.mem_cons,
                List.not_mem_nil, List.nodup_reverse, List.mem_reverse] at hn ⊢
              grind)
          (List.isChain_append.mpr ⟨h₁,
            List.isChain_cons.mpr ⟨by simp [List.head?_reverse, hc, hcw.symm],
              List.isChain_reverse.mpr (h₂.imp fun _ _ h ↦ h.symm)⟩,
            by simp [ha, haw]⟩)
          (List.isChain_singleton x)
          ⟨by simp, fun y hy ↦ hh₁ y (by rwa [List.head?_append_of_ne_nil _ hne₁] at hy),
            by
              obtain ⟨b, hb⟩ : ∃ b, c₂.head? = some b :=
                Option.isSome_iff_exists.mp (List.isSome_head?.mpr hne₂)
              have hlast : (c₁ ++ w :: c₂.reverse).getLast? = some b := by
                rw [show c₁ ++ w :: c₂.reverse = (c₂ ++ w :: c₁.reverse).reverse by simp,
                  List.getLast?_reverse]
                simp [List.head?_append, hb]
              intro y hy
              rw [hlast, Option.mem_def, Option.some.injEq] at hy
              exact hy ▸ hh₂ b hb⟩
          ⟨by simp, by simp [hxX], by simp [hxX]⟩
      refine ⟨d₁, d₂, r₁, r₂, r₃, r₄, r₅, fun y hy ↦ ?_, by rw [r₇]; simp; omega⟩
      have := r₆ y hy
      simp only [List.mem_append, List.mem_cons, List.mem_reverse,
        List.not_mem_nil, or_false] at this ⊢
      rcases hw with rfl | rfl <;> tauto

/-- The inductive step of the proof: if `s` has `n + ⌊m/2⌋` vertices, with `2 ≤ n` and
`m ≤ n + 1`, and `G` has a path on `n` vertices of `s`, then `G` has a path on `n + 1` vertices
of `s`, or `Gᶜ` has one on `m` vertices of `s`. -/
private theorem step (G : SimpleGraph V) (s : Finset V) {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hmn : m ≤ n + 1) (u : List V) (hu : u.Nodup) (huc : u.IsChain G.Adj) (hul : u.length = n)
    (hus : ∀ x ∈ u, x ∈ s) (hs : s.card = n + m / 2) :
    HasPath G s (n + 1) ∨ HasPath Gᶜ s m := by
  classical
  refine or_iff_not_imp_left.mpr fun hno ↦ ?_
  have red : ∀ l : List V, l.Nodup → l.IsChain G.Adj → (∀ y ∈ l, y ∈ s) → l.length = n + 1 →
      False := fun l h₁ h₂ h₃ h₄ ↦ hno ⟨l, h₁, h₂, h₃, h₄.ge⟩
  obtain ⟨u₀, mid, ue, rfl⟩ : ∃ u₀ mid ue, u = u₀ :: (mid ++ [ue]) := by
    match u, hul with
    | [], hl => simp at hl; omega
    | u₀ :: rest, hl =>
      rcases List.eq_nil_or_concat rest with rfl | ⟨L, b, rfl⟩
      · simp at hl; omega
      · exact ⟨u₀, L, b, by simp⟩
  have hmid : mid.length = n - 2 := by simp at hul; omega
  set U := u₀ :: (mid ++ [ue]) with hU
  set X : Set V := {v | v ∈ s ∧ v ∉ U} with hX
  -- every vertex of `X` is adjacent in `Gᶜ` to both ends of the path
  have h₀ : ∀ v ∈ X, Gᶜ.Adj v u₀ := by
    rintro v ⟨hvs, hvu⟩
    refine (compl_adj G v u₀).mpr ⟨fun h ↦ hvu (h ▸ by simp [U]), fun h ↦ red (v :: U)
      (List.nodup_cons.mpr ⟨hvu, hu⟩) (List.isChain_cons_cons.mpr ⟨h, huc⟩) ?_ ?_⟩
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      exacts [hvs, hus y hy]
    · simp only [List.length_cons]; omega
  have hₑ : ∀ v ∈ X, Gᶜ.Adj v ue := by
    rintro v ⟨hvs, hvu⟩
    refine (compl_adj G v ue).mpr ⟨fun h ↦ hvu (h ▸ by simp [U]), fun h ↦ red (U ++ [v])
      ?_ (List.isChain_append.mpr ⟨huc, List.isChain_singleton v,
        by rw [hU, ← List.cons_append, List.getLast?_concat]; simpa using h.symm⟩) ?_ ?_⟩
    · rw [List.nodup_append]
      refine ⟨hu, List.nodup_singleton v, ?_⟩
      intro a ha b hb
      rw [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hvu ha
    · intro y hy
      rcases List.mem_append.mp hy with hy | hy
      · exact hus y hy
      · rw [List.mem_singleton] at hy
        exact hy ▸ hvs
    · simp only [List.length_append, List.length_singleton]; omega
  -- every vertex of `X` is adjacent in `Gᶜ` to one of any two consecutive vertices of the path
  have hins : ∀ v ∈ X, ∀ (l₁ l₂ : List V) (x y : V), U = l₁ ++ x :: y :: l₂ →
      Gᶜ.Adj v x ∨ Gᶜ.Adj v y := by
    rintro v ⟨hvs, hvu⟩ l₁ l₂ x y hl
    rw [hl] at hvu hus huc hu hul
    have hvx : v ≠ x := by rintro rfl; simp at hvu
    have hvy : v ≠ y := by rintro rfl; simp at hvu
    by_contra! hc
    simp only [compl_adj, not_and, not_not] at hc
    apply red (l₁ ++ x :: v :: y :: l₂)
    · have hp : (l₁ ++ x :: v :: y :: l₂).Perm (v :: (l₁ ++ x :: y :: l₂)) := by
        rw [show l₁ ++ x :: v :: y :: l₂ = (l₁ ++ [x]) ++ v :: (y :: l₂) by simp]
        exact List.perm_middle.trans (by simp)
      exact hp.nodup_iff.mpr (List.nodup_cons.mpr ⟨hvu, hu⟩)
    · rw [List.isChain_append_cons_cons] at huc
      obtain ⟨c₁, -, c₃⟩ := huc
      rw [List.isChain_append_cons_cons]
      exact ⟨c₁, (hc.1 hvx).symm, List.isChain_cons_cons.mpr ⟨hc.2 hvy, c₃⟩⟩
    · intro z hz
      simp only [List.mem_append, List.mem_cons] at hz
      rcases hz with hz | rfl | rfl | rfl | hz
      exacts [hus _ (by simp [hz]), hus _ (by simp), hvs, hus _ (by simp),
        hus _ (by simp [hz])]
    · simp only [List.length_append, List.length_cons] at hul ⊢; omega
  have hpairs : ∀ p ∈ pairs mid, ∀ v ∈ X, Gᶜ.Adj v p.1 ∨ Gᶜ.Adj v p.2 := by
    intro p hp v hv
    obtain ⟨l₁, l₂, hl⟩ := exists_eq_of_mem_pairs hp
    exact hins v hv (u₀ :: l₁) (l₂ ++ [ue]) p.1 p.2 (by simp [U, hl])
  -- the vertices off the path
  set W := s \ U.toFinset with hW
  have hWc : W.card = m / 2 := by
    rw [hW, Finset.card_sdiff_of_subset (fun y hy ↦ hus y (List.mem_toFinset.mp hy)),
      List.toFinset_card_of_nodup hu, hul, hs]
    omega
  have hWX : ∀ y ∈ W.toList, y ∈ X := by
    intro y hy
    simpa [hW, X] using hy
  have hWnd : W.toList.Nodup := W.nodup_toList
  have hWl : W.toList.length = m / 2 := by rw [Finset.length_toList, hWc]
  have huU : u₀ ∈ U := by simp [U]
  have heU : ue ∈ U := by simp [U]
  have hu₀s : u₀ ∈ s := hus u₀ huU
  have hes : ue ∈ s := hus ue heU
  have hXs : ∀ y ∈ X, y ∈ s := fun y hy ↦ hy.1
  have hXU : ∀ y ∈ X, y ∉ U := fun y hy ↦ hy.2
  have hmidU : ∀ y ∈ mid, y ∈ U := fun y hy ↦ by simp [U, hy]
  have hu' : u₀ ∉ mid ∧ ue ∉ mid ∧ u₀ ≠ ue ∧ mid.Nodup := nodup_cons_append_singleton hu
  rcases hxs : W.toList with _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩
  · rw [hxs] at hWl; simp at hWl; omega
  · -- `⌊m/2⌋ = 1`: the path `u₀, x₁, ue`
    rw [hxs] at hWl hWX
    have hx₁ : x₁ ∈ X := hWX x₁ (by simp)
    have := hXU x₁ hx₁
    refine ⟨[u₀, x₁, ue], ?_, List.isChain_cons_cons.mpr ⟨(h₀ x₁ hx₁).symm,
      List.isChain_pair.mpr (hₑ x₁ hx₁)⟩, ?_, ?_⟩
    · exact nodup_cons_append_cons (d₁ := [x₁]) (d₂ := []) (by simp)
        (by simpa using ⟨fun h ↦ this (h ▸ huU), fun h ↦ this (h ▸ heU)⟩) hu'.2.2.1
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl
      exacts [hu₀s, hXs _ hx₁, hes]
    · simp at hWl ⊢; omega
  · -- `⌊m/2⌋ ≥ 2`: use `⌊m/2⌋ - 2` pairs for the greedy construction
    rw [hxs] at hWl hWX hWnd
    simp only [List.length_cons] at hWl
    set all := pairs mid with hall
    have hallL : all.length = (n - 2) / 2 := by rw [hall, length_pairs, hmid]
    set ps := all.take (m / 2 - 2) with hps
    have hpsL : rest.length = ps.length := by
      rw [hps, List.length_take, hallL]; omega
    have hflat : flat ps ++ flat (all.drop (m / 2 - 2)) = flat all := by
      rw [← flat_append, List.take_append_drop]
    have hsub : (flat ps ++ flat (all.drop (m / 2 - 2))).Sublist mid :=
      hflat ▸ flat_pairs_sublist mid
    have hfnd : (flat ps ++ flat (all.drop (m / 2 - 2))).Nodup := hu'.2.2.2.sublist hsub
    have hfmid : ∀ y ∈ flat ps ++ flat (all.drop (m / 2 - 2)), y ∈ mid := fun y hy ↦ hsub.subset hy
    have hpool : ((x₁ :: x₂ :: rest) ++ (flat ps ++ flat (all.drop (m / 2 - 2)))).Nodup := by
      rw [List.nodup_append]
      refine ⟨hWnd, hfnd, ?_⟩
      intro a ha b hb
      rintro rfl
      exact hXU a (hWX a ha) (hmidU a (hfmid a hb))
    have hpool' : ([x₁] ++ [x₂] ++ rest ++ flat ps).Nodup :=
      hpool.sublist (by simp)
    have hx₁ : x₁ ∈ X := hWX x₁ (by simp)
    have hx₂ : x₂ ∈ X := hWX x₂ (by simp)
    obtain ⟨d₁, d₂, r₁, r₂, ⟨hne₁, hh₁, hl₁⟩, ⟨hne₂, hh₂, hl₂⟩, r₅, r₆, r₇⟩ :=
      greedy Gᶜ X rest ps [x₁] [x₂] hpsL
        (fun p hp ↦ hpairs p (List.mem_of_mem_take hp))
        (fun y hy ↦ hWX y (by simp [hy])) hpool' (List.isChain_singleton _)
        (List.isChain_singleton _) ⟨by simp, by simp [hx₁], by simp [hx₁]⟩
        ⟨by simp, by simp [hx₂], by simp [hx₂]⟩
    -- every vertex of the two paths is in `X` or in `mid`
    have hd : ∀ y ∈ d₁ ++ d₂, (y ∈ X ∨ y ∈ flat ps) := by
      intro y hy
      have := r₆ y hy
      simp only [List.mem_append, List.mem_singleton] at this
      rcases this with ((rfl | rfl) | h) | h
      · exact Or.inl hx₁
      · exact Or.inl hx₂
      · exact Or.inl (hWX y (by simp [h]))
      · exact Or.inr h
    have hdU : ∀ y ∈ d₁ ++ d₂, y ≠ u₀ ∧ y ≠ ue := by
      intro y hy
      rcases hd y hy with h | h
      · exact ⟨fun e ↦ hXU y h (e ▸ huU), fun e ↦ hXU y h (e ▸ heU)⟩
      · have hm' := hfmid y (List.mem_append_left _ h)
        exact ⟨fun e ↦ hu'.1 (e ▸ hm'), fun e ↦ hu'.2.1 (e ▸ hm')⟩
    have hds : ∀ y ∈ d₁ ++ d₂, y ∈ s := by
      intro y hy
      rcases hd y hy with h | h
      · exact hXs y h
      · exact hus y (hmidU y (hfmid y (List.mem_append_left _ h)))
    obtain ⟨b₁, hb₁⟩ : ∃ b, d₁.head? = some b :=
      Option.isSome_iff_exists.mp (List.isSome_head?.mpr hne₁)
    obtain ⟨a₁, ha₁⟩ : ∃ a, d₁.getLast? = some a :=
      Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne₁)
    obtain ⟨b₂, hb₂⟩ : ∃ b, d₂.head? = some b :=
      Option.isSome_iff_exists.mp (List.isSome_head?.mpr hne₂)
    obtain ⟨z, hz⟩ : ∃ z, d₂.getLast? = some z :=
      Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne₂)
    -- the blue path `u₀, d₁, ue, d₂` on `2 * ⌊m/2⌋` vertices
    set L := u₀ :: (d₁ ++ ue :: d₂) with hL
    have hLnd : L.Nodup := nodup_cons_append_cons r₅ hdU hu'.2.2.1
    have hLc : L.IsChain Gᶜ.Adj := by
      refine List.isChain_cons.mpr ⟨?_, List.isChain_append.mpr ⟨r₁,
        List.isChain_cons.mpr ⟨?_, r₂⟩, ?_⟩⟩
      · intro y hy
        rw [List.head?_append_of_ne_nil _ hne₁, hb₁, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact (h₀ _ (hh₁ _ hb₁)).symm
      · intro y hy
        rw [hb₂, Option.mem_def, Option.some.injEq] at hy
        subst hy
        exact (hₑ _ (hh₂ _ hb₂)).symm
      · intro y hy y' hy'
        rw [ha₁, Option.mem_def, Option.some.injEq] at hy
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hy'
        subst hy hy'
        exact hₑ _ (hl₁ _ ha₁)
    have hLs : ∀ y ∈ L, y ∈ s := by
      intro y hy
      simp only [hL, List.mem_cons, List.mem_append] at hy
      rcases hy with rfl | hy | rfl | hy
      · exact hu₀s
      · exact hds y (List.mem_append_left _ hy)
      · exact hes
      · exact hds y (List.mem_append_right _ hy)
    have hLl : L.length = 2 * (m / 2) := by
      simp [hL] at r₇ ⊢
      omega
    by_cases hextra : m / 2 - 1 ≤ (n - 2) / 2
    · -- a spare pair, one of whose vertices extends the path
      obtain ⟨e, es, he⟩ := List.exists_cons_of_ne_nil (l := all.drop (m / 2 - 2))
        (by rw [← List.length_pos_iff, List.length_drop, hallL]; omega)
      have heall : e ∈ all := List.mem_of_mem_drop (he ▸ List.mem_cons_self)
      have hzX : z ∈ X := hl₂ z hz
      rw [he, flat_cons] at hfnd hfmid
      obtain ⟨w, hw, hzw⟩ : ∃ w, (w = e.1 ∨ w = e.2) ∧ Gᶜ.Adj z w := by
        rcases hpairs e heall z hzX with h | h
        exacts [⟨_, Or.inl rfl, h⟩, ⟨_, Or.inr rfl, h⟩]
      have hwmid : w ∈ mid := hfmid w (by rcases hw with rfl | rfl <;> simp)
      have hwps : w ∉ flat ps := by
        intro h
        rw [List.nodup_append] at hfnd
        exact hfnd.2.2 w h w (by rcases hw with rfl | rfl <;> simp) rfl
      have hwL : w ∉ L := by
        intro h
        simp only [hL, List.mem_cons, List.mem_append] at h
        rcases h with rfl | h | rfl | h
        · exact hu'.1 hwmid
        · rcases hd w (List.mem_append_left _ h) with h' | h'
          exacts [hXU w h' (hmidU w hwmid), hwps h']
        · exact hu'.2.1 hwmid
        · rcases hd w (List.mem_append_right _ h) with h' | h'
          exacts [hXU w h' (hmidU w hwmid), hwps h']
      refine ⟨L ++ [w], ?_, ?_, ?_, ?_⟩
      · rw [List.nodup_append]
        refine ⟨hLnd, List.nodup_singleton w, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hwL ha
      · refine List.isChain_append.mpr ⟨hLc, List.isChain_singleton w, ?_⟩
        have : L.getLast? = some z := by
          rw [hL, ← List.cons_append, List.getLast?_append, ← List.reverse_reverse (ue :: d₂),
            List.getLast?_reverse]
          simp [hz]
        simp only [this, Option.mem_def, Option.some.injEq, List.head?_cons]
        rintro y rfl _ rfl
        exact hzw
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hLs y hy
        · rw [List.mem_singleton] at hy
          exact hy ▸ hus w (hmidU w hwmid)
      · rw [List.length_append, hLl, List.length_singleton]; omega
    · exact ⟨L, hLnd, hLc, hLs, by omega⟩

/-- The upper half of the milestone, for the vertices of a finset, with paths as lists. -/
private theorem hasPath_or_hasPath : ∀ (n : ℕ) (G : SimpleGraph V) (m : ℕ), 2 ≤ m → m ≤ n →
    ∀ s : Finset V, s.card = n + m / 2 - 1 → HasPath G s n ∨ HasPath Gᶜ s m := by
  classical
  intro n
  induction n with
  | zero => intro G m hm hmn; omega
  | succ n ih =>
    intro G m hm hmn s hs
    rcases Nat.lt_or_ge n 2 with hn | hn
    · have hm2 : m = 2 := by omega
      have hn1 : n = 1 := by omega
      subst hm2 hn1
      obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp (by simpa using hs)
      by_cases h : G.Adj x y
      · exact Or.inl ⟨[x, y], by simp [hxy], List.isChain_pair.mpr h, by simp, by simp⟩
      · exact Or.inr ⟨[x, y], by simp [hxy],
          List.isChain_pair.mpr ((compl_adj G x y).mpr ⟨hxy, h⟩), by simp, by simp⟩
    · have hs' : s.card = n + m / 2 := by omega
      -- a path on `n` vertices of `s`, in `G`, gives the result by `step`
      have key : ∀ (H : SimpleGraph V) (s' : Finset V), s' ⊆ s → HasPath H s' n →
          HasPath H s (n + 1) ∨ HasPath Hᶜ s m := by
        rintro H s' hss ⟨u, h₁, h₂, h₃, h₄⟩
        exact step H s hn hm hmn (u.take n) (h₁.sublist (List.take_sublist _ _)) (h₂.take n)
          (by simp; omega) (fun y hy ↦ hss (h₃ y (List.mem_of_mem_take hy))) hs'
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · obtain ⟨x, hx⟩ : s.Nonempty := Finset.card_pos.mp (by omega)
        rcases ih G m hm (by omega) (s.erase x)
            (by rw [Finset.card_erase_of_mem hx]; omega) with h | h
        · exact key G _ (Finset.erase_subset x s) h
        · exact Or.inr (h.mono (Finset.erase_subset x s))
      · have hmn' : m = n + 1 := by omega
        obtain ⟨s', hs's, hs'c⟩ := Finset.exists_subset_card_eq (s := s) (n := n + n / 2 - 1)
          (by omega)
        rcases ih G n hn le_rfl s' hs'c with h | h
        · exact key G s' hs's h
        · rcases key Gᶜ s' hs's h with h' | h'
          · exact Or.inr (hmn' ▸ h')
          · rw [compl_compl] at h'
            obtain ⟨l, h₁, h₂, h₃, h₄⟩ := h'
            exact Or.inl ⟨l, h₁, h₂, h₃, by omega⟩

/-- **Gerencsér–Gyárfás.** For `n ≥ m ≥ 2`, every graph on `n + ⌊m/2⌋ - 1` vertices contains the
path on `n` vertices, or its complement contains the path on `m` vertices.

This is the upper half of the milestone *Paths*, `R(P_n, P_m) = n + ⌊m/2⌋ - 1`. -/
theorem pathGraph_ramsey_upper {V : Type*} [Fintype V] {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n)
    (hV : Fintype.card V = n + m / 2 - 1) (G : SimpleGraph V) :
    pathGraph n ⊑ G ∨ pathGraph m ⊑ Gᶜ := by
  rcases hasPath_or_hasPath n G m hm hmn Finset.univ (by rw [Finset.card_univ, hV]) with
    ⟨l, h₁, h₂, -, h₄⟩ | ⟨l, h₁, h₂, -, h₄⟩
  · exact Or.inl (pathGraph_isContained_of_list h₁ h₂ h₄)
  · exact Or.inr (pathGraph_isContained_of_list h₁ h₂ h₄)

end Ramsey

end
