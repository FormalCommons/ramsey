module

public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Ramsey.SmallRamsey.R33

/-!
# Four-cycles: R(C₄, C₄) = 6

This file formalizes the milestone *Four-cycles* of the plan's page on Ramsey numbers of graphs:
every graph on at least 6 vertices contains a 4-cycle `C₄ = SimpleGraph.cycleGraph 4`, or its
complement does, and the 5-cycle, whose complement is again a 5-cycle, contains none.

## Main results

* `Ramsey.cycleGraph_four_isContained_iff`: a graph contains `C₄` if and only if it has four
  distinct vertices `p ∼ q ∼ r ∼ s ∼ p`.
* `Ramsey.cycleGraph_four_isContained_or_compl`: the upper half.
* `Ramsey.not_cycleGraph_four_isContained_cycleGraph_five`,
  `Ramsey.not_cycleGraph_four_isContained_compl_cycleGraph_five`: the lower half.
* `Ramsey.ramsey_cycleGraph_four`: both halves together, the milestone.

The upper half uses the upper half of `R(3,3) = 6`. If neither `G` nor `Gᶜ` contains `C₄`, then,
replacing `G` by `Gᶜ` if needed, `G` has a triangle `abc`; take three more vertices `x, y, z`.
Each of them has at most one neighbour among `a, b, c`, else there is a 4-cycle in `G`, and two of
them cannot share two non-neighbours there, else there is a 4-cycle in `Gᶜ`. So `x, y, z` are
joined to different vertices of the triangle. Then an edge among `x, y, z` closes a 4-cycle in
`G`, and otherwise they close one in `Gᶜ`.

## References

* V. Chvátal and F. Harary, *Generalized Ramsey theory for graphs. III. Small off-diagonal
  numbers* (1972).
* S. P. Radziszowski, *Small Ramsey numbers*, Electron. J. Combin., Dynamic Survey DS1, §4.1.
-/

public section

namespace Ramsey

open SimpleGraph Finset

variable {V : Type*}

/-- A graph contains a 4-cycle if and only if it has vertices `p ∼ q ∼ r ∼ s ∼ p` with `p ≠ r` and
`q ≠ s`, that is, four distinct vertices, since adjacent vertices are distinct. -/
theorem cycleGraph_four_isContained_iff {G : SimpleGraph V} :
    cycleGraph 4 ⊑ G ↔
      ∃ p q r s, p ≠ r ∧ q ≠ s ∧ G.Adj p q ∧ G.Adj q r ∧ G.Adj r s ∧ G.Adj s p := by
  constructor
  · rintro ⟨f⟩
    refine ⟨f 0, f 1, f 2, f 3, f.injective.ne (by decide), f.injective.ne (by decide),
      f.toHom.map_adj (by decide), f.toHom.map_adj (by decide), f.toHom.map_adj (by decide),
      f.toHom.map_adj (by decide)⟩
  · rintro ⟨p, q, r, s, hpr, hqs, hpq, hqr, hrs, hsp⟩
    refine ⟨⟨⟨![p, q, r, s], fun {i j} h ↦ ?_⟩, fun i j h ↦ ?_⟩⟩
    · fin_cases i <;> fin_cases j <;> first
        | exact absurd h (by decide)
        | simp [hpq, hqr, hrs, hsp, hpq.symm, hqr.symm, hrs.symm, hsp.symm]
    · fin_cases i <;> fin_cases j <;> simp_all [hpq.ne, hqr.ne, hrs.ne, hsp.ne, hpr.symm, hqs.symm,
        hpq.ne.symm, hqr.ne.symm, hrs.ne.symm, hsp.ne.symm]

/-- The core of the upper half: if neither `G` nor `Gᶜ` has a 4-cycle, then no triangle `abc` of
`G` and three further distinct vertices `x, y, z` exist. -/
private lemma core (G : SimpleGraph V)
    (hG : ∀ p q r s, p ≠ r → q ≠ s → G.Adj p q → G.Adj q r → G.Adj r s → G.Adj s p → False)
    (hGc : ∀ p q r s, p ≠ r → q ≠ s → p ≠ q → q ≠ r → r ≠ s → s ≠ p →
      ¬ G.Adj p q → ¬ G.Adj q r → ¬ G.Adj r s → ¬ G.Adj s p → False)
    {a b c x y z : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hya : y ≠ a) (hyb : y ≠ b)
    (hyc : y ≠ c) (hza : z ≠ a) (hzb : z ≠ b) (hzc : z ≠ c)
    (gab : G.Adj a b) (gbc : G.Adj b c) (gca : G.Adj c a) : False := by
  -- Each vertex outside the triangle has at most one neighbour in it.
  have pat : ∀ w, w ≠ a → w ≠ b → w ≠ c →
      (G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c) ∨ (¬ G.Adj w a ∧ G.Adj w b ∧ ¬ G.Adj w c) ∨
      (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ G.Adj w c) ∨ (¬ G.Adj w a ∧ ¬ G.Adj w b ∧ ¬ G.Adj w c) := by
    intro w hwa hwb hwc
    have h₁ : G.Adj w a → ¬ G.Adj w b := fun h h' ↦ hG w a c b hwc hab h gca.symm gbc.symm h'.symm
    have h₂ : G.Adj w a → ¬ G.Adj w c := fun h h' ↦ hG w a b c hwb hac h gab gbc h'.symm
    have h₃ : G.Adj w b → ¬ G.Adj w c := fun h h' ↦ hG w b a c hwa hbc h gab.symm gca.symm h'.symm
    by_cases ha : G.Adj w a
    · exact .inl ⟨ha, h₁ ha, h₂ ha⟩
    by_cases hb : G.Adj w b
    · exact .inr (.inl ⟨ha, hb, h₃ hb⟩)
    by_cases hc : G.Adj w c
    · exact .inr (.inr (.inl ⟨ha, hb, hc⟩))
    · exact .inr (.inr (.inr ⟨ha, hb, hc⟩))
  -- Two vertices outside the triangle share at most one non-neighbour in it.
  have share : ∀ u v p q, u ≠ v → p ≠ q → u ≠ p → u ≠ q → v ≠ p → v ≠ q →
      ¬ G.Adj u p → ¬ G.Adj v p → ¬ G.Adj u q → ¬ G.Adj v q → False :=
    fun u v p q huv hpq hup huq hvp hvq h₁ h₂ h₃ h₄ ↦ hGc u p v q huv hpq hup hvp.symm hvq huq.symm
      h₁ (fun h ↦ h₂ h.symm) h₄ (fun h ↦ h₃ h.symm)
  -- If the three vertices outside are joined to different vertices of the triangle, then any edge
  -- between two of them closes a 4-cycle in `G`, and otherwise they close one in `Gᶜ`.
  have fin : ∀ x y z p q r : V, x ≠ y → x ≠ z → y ≠ z → x ≠ p → x ≠ q → x ≠ r → y ≠ p →
      y ≠ q → y ≠ r → z ≠ p → z ≠ q → z ≠ r → G.Adj x p → G.Adj y q → G.Adj z r → G.Adj p q →
      G.Adj q r → G.Adj r p → ¬ G.Adj y p → ¬ G.Adj z p → False := by
    intro x y z p q r hxy hxz hyz hxp hxq hxr hyp hyq hyr hzp hzq hzr gxp gyq gzr gpq gqr grp
      hyp' hzp'
    have h₁ : ¬ G.Adj x y := fun h ↦ hG x y q p hxq hyp h gyq gpq.symm gxp.symm
    have h₂ : ¬ G.Adj y z := fun h ↦ hG y z r q hyr hzq h gzr gqr.symm gyq.symm
    have h₃ : ¬ G.Adj z x := fun h ↦ hG x z r p hxr hzp h.symm gzr grp gxp.symm
    exact hGc x y p z hxp hyz hxy hyp hzp.symm hxz.symm h₁ hyp' (fun h ↦ hzp' h.symm) h₃
  have gba := gab.symm
  have gcb := gbc.symm
  have gac := gca.symm
  rcases pat x hxa hxb hxc with ⟨x₁, x₂, x₃⟩ | ⟨x₁, x₂, x₃⟩ | ⟨x₁, x₂, x₃⟩ | ⟨x₁, x₂, x₃⟩ <;>
  rcases pat y hya hyb hyc with ⟨y₁, y₂, y₃⟩ | ⟨y₁, y₂, y₃⟩ | ⟨y₁, y₂, y₃⟩ | ⟨y₁, y₂, y₃⟩ <;>
  rcases pat z hza hzb hzc with ⟨z₁, z₂, z₃⟩ | ⟨z₁, z₂, z₃⟩ | ⟨z₁, z₂, z₃⟩ | ⟨z₁, z₂, z₃⟩
  all_goals first
    | exact share x y a b hxy hab hxa hxb hya hyb ‹_› ‹_› ‹_› ‹_›
    | exact share x y a c hxy hac hxa hxc hya hyc ‹_› ‹_› ‹_› ‹_›
    | exact share x y b c hxy hbc hxb hxc hyb hyc ‹_› ‹_› ‹_› ‹_›
    | exact share x z a b hxz hab hxa hxb hza hzb ‹_› ‹_› ‹_› ‹_›
    | exact share x z a c hxz hac hxa hxc hza hzc ‹_› ‹_› ‹_› ‹_›
    | exact share x z b c hxz hbc hxb hxc hzb hzc ‹_› ‹_› ‹_› ‹_›
    | exact share y z a b hyz hab hya hyb hza hzb ‹_› ‹_› ‹_› ‹_›
    | exact share y z a c hyz hac hya hyc hza hzc ‹_› ‹_› ‹_› ‹_›
    | exact share y z b c hyz hbc hyb hyc hzb hzc ‹_› ‹_› ‹_› ‹_›
    | exact fin x y z a b c hxy hxz hyz hxa hxb hxc hya hyb hyc hza hzb hzc ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_›
    | exact fin x y z a c b hxy hxz hyz hxa hxc hxb hya hyc hyb hza hzc hzb ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_›
    | exact fin x y z b a c hxy hxz hyz hxb hxa hxc hyb hya hyc hzb hza hzc ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_›
    | exact fin x y z b c a hxy hxz hyz hxb hxc hxa hyb hyc hya hzb hzc hza ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_›
    | exact fin x y z c a b hxy hxz hyz hxc hxa hxb hyc hya hyb hzc hza hzb ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_›
    | exact fin x y z c b a hxy hxz hyz hxc hxb hxa hyc hyb hya hzc hzb hza ‹_› ‹_› ‹_› ‹_› ‹_›
        ‹_› ‹_› ‹_›

/-- If neither `G` nor `Gᶜ` contains a 4-cycle, then `G` has no triangle, as soon as there are at
least 6 vertices. -/
private lemma false_of_triangle [Fintype V] {G : SimpleGraph V} (hV : 6 ≤ Fintype.card V)
    (h₁ : ¬ cycleGraph 4 ⊑ G) (h₂ : ¬ cycleGraph 4 ⊑ Gᶜ) {a b c : V} (gab : G.Adj a b)
    (gbc : G.Adj b c) (gca : G.Adj c a) : False := by
  classical
  rw [cycleGraph_four_isContained_iff] at h₁ h₂
  have hG : ∀ p q r s, p ≠ r → q ≠ s → G.Adj p q → G.Adj q r → G.Adj r s → G.Adj s p → False :=
    fun p q r s h₁' h₂' h₃ h₄ h₅ h₆ ↦ h₁ ⟨p, q, r, s, h₁', h₂', h₃, h₄, h₅, h₆⟩
  have hGc : ∀ p q r s, p ≠ r → q ≠ s → p ≠ q → q ≠ r → r ≠ s → s ≠ p →
      ¬ G.Adj p q → ¬ G.Adj q r → ¬ G.Adj r s → ¬ G.Adj s p → False :=
    fun p q r s hpr hqs hpq hqr hrs hsp h₃ h₄ h₅ h₆ ↦
      h₂ ⟨p, q, r, s, hpr, hqs, ⟨hpq, h₃⟩, ⟨hqr, h₄⟩, ⟨hrs, h₅⟩, ⟨hsp, h₆⟩⟩
  have hcard : 2 < #(univ \ {a, b, c}) := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have := card_le_three (a := a) (b := b) (c := c)
    omega
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := two_lt_card_iff.1 hcard
  simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or] at hx hy hz
  exact core G hG hGc gab.ne gca.ne.symm gbc.ne hxy hxz hyz hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2
    hz.1 hz.2.1 hz.2.2 gab gbc gca

/-- The upper half of the milestone *Four-cycles*: every graph on at least 6 vertices contains a
4-cycle, or its complement does. -/
theorem cycleGraph_four_isContained_or_compl [Fintype V] (G : SimpleGraph V)
    (hV : 6 ≤ Fintype.card V) : cycleGraph 4 ⊑ G ∨ cycleGraph 4 ⊑ Gᶜ := by
  classical
  by_contra h
  obtain ⟨h₁, h₂⟩ := not_or.1 h
  rcases not_cliqueFree_three_or_not_indepSetFree_three G hV with h | h
  · obtain ⟨t, ht⟩ : ∃ t, G.IsNClique 3 t := by simpa [CliqueFree] using h
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
    exact false_of_triangle hV h₁ h₂ hab hbc hac.symm
  · obtain ⟨t, ht⟩ : ∃ t, G.IsNIndepSet 3 t := by simpa [IndepSetFree] using h
    rw [← isNClique_compl] at ht
    obtain ⟨a, b, c, hab, hac, hbc, -⟩ := is3Clique_iff.1 ht
    exact false_of_triangle hV h₂ (by rwa [compl_compl]) hab hbc hac.symm

/-- The 5-cycle contains no 4-cycle. This is part of the lower half of the milestone
*Four-cycles*. -/
theorem not_cycleGraph_four_isContained_cycleGraph_five : ¬ cycleGraph 4 ⊑ cycleGraph 5 := by
  rw [cycleGraph_four_isContained_iff]
  rintro ⟨p, q, r, s, h⟩
  revert p q r s
  decide

/-- The complement of the 5-cycle contains no 4-cycle. This is part of the lower half of the
milestone *Four-cycles*. -/
theorem not_cycleGraph_four_isContained_compl_cycleGraph_five :
    ¬ cycleGraph 4 ⊑ (cycleGraph 5)ᶜ := by
  rw [cycleGraph_four_isContained_iff]
  rintro ⟨p, q, r, s, h⟩
  revert p q r s
  decide

/-- The milestone *Four-cycles*, `R(C₄, C₄) = 6`: every graph on at least 6 vertices contains a
4-cycle or its complement does, and the 5-cycle, a graph on 5 vertices, and its complement
contain none. -/
theorem ramsey_cycleGraph_four :
    (∀ (V : Type*) [Fintype V] (G : SimpleGraph V), 6 ≤ Fintype.card V →
      cycleGraph 4 ⊑ G ∨ cycleGraph 4 ⊑ Gᶜ) ∧
    ¬ cycleGraph 4 ⊑ cycleGraph 5 ∧ ¬ cycleGraph 4 ⊑ (cycleGraph 5)ᶜ :=
  ⟨fun _ _ G hV ↦ cycleGraph_four_isContained_or_compl G hV,
    not_cycleGraph_four_isContained_cycleGraph_five,
    not_cycleGraph_four_isContained_compl_cycleGraph_five⟩

end Ramsey

end
