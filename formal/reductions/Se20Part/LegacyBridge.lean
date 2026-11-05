import Se20Part.Legacy.High20Packing
import Se20Part.PackingCases

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} (G : SimpleGraph V)

/-- The copied proofs use distance at most two in the line graph. This is
equivalent to this project's endpoint definition, with witnesses in all of G. -/
theorem legacy_conflict_iff (e f : G.edgeSet) : Legacy.StrongConflict G e f ↔ (L2 G).Adj e f := by
  constructor
  · rintro ⟨hne,h | ⟨g,heg,hgf⟩⟩
    · obtain ⟨_,a,ha,haf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp h
      exact ⟨hne,a,ha,a,haf,Or.inl rfl⟩
    · obtain ⟨_,a,ha,hag⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp heg
      obtain ⟨_,b,hbg,hbf⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hgf
      refine ⟨hne,a,ha,b,hbf,?_⟩
      by_cases he : a = b
      · exact Or.inl he
      · exact Or.inr (G.mem_edgeSet.mp ((Sym2.mem_and_mem_iff he).mp ⟨hag,hbg⟩ ▸ g.prop))
  · rintro ⟨hne,a,ha,b,hb,he | hab⟩
    · subst b
      exact ⟨hne,Or.inl (SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne,a,ha,hb⟩)⟩
    · let g : G.edgeSet := ⟨s(a,b),hab⟩
      by_cases heg : e = g
      · exact ⟨hne,Or.inl (SimpleGraph.lineGraph_adj_iff_exists.mpr
          ⟨hne,b,heg ▸ Sym2.mem_mk_right a b,hb⟩)⟩
      by_cases hgf : g = f
      · exact ⟨hne,Or.inl (SimpleGraph.lineGraph_adj_iff_exists.mpr
          ⟨hne,a,ha,hgf ▸ Sym2.mem_mk_left a b⟩)⟩
      exact ⟨hne,Or.inr ⟨g,
        SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨heg,a,ha,Sym2.mem_mk_left a b⟩,
        SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hgf,b,Sym2.mem_mk_right a b,hb⟩⟩⟩

theorem legacy_conflictGraph_eq : Legacy.conflictGraph G = L2 G := by
  ext e f
  exact legacy_conflict_iff G e f

variable [Fintype V]

/-- The unconditional ambient 20-packing theorem, rebuilt from local copies. -/
theorem ambient_packing_twenty (hΔ : MaxDegreeFour G) (F : Finset G.edgeSet) :
    ∃ M ⊆ F, Independent (L2 G) M ∧ F.card ≤ 20 * M.card := by
  obtain ⟨M,hMF,hM,hcard⟩ := Legacy.induced_matching_packing20 G hΔ F
  refine ⟨M,hMF,?_,hcard⟩
  intro e he f hf hadj
  exact hM he hf hadj.1 ((legacy_conflict_iff G e f).mpr hadj)

/-- G06: every set of at least 41 edges contains an ambient induced matching
of exactly three edges. No critical-complement theorem is assumed. -/
theorem fortyOne_edges_independent_triple (hΔ : MaxDegreeFour G)
    (F : Finset G.edgeSet) (hF : 41 ≤ F.card) :
    ∃ T ⊆ F, T.card = 3 ∧ Independent (L2 G) T := by
  obtain ⟨M,hMF,hM,hcard⟩ := ambient_packing_twenty G hΔ F
  have hthree : 3 ≤ M.card := by omega
  obtain ⟨T,hTM,hT⟩ := Finset.exists_subset_card_eq hthree
  exact ⟨T,Finset.Subset.trans hTM hMF,hT,fun e he f hf => hM e (hTM he) f (hTM hf)⟩

theorem rank_two_card_le_forty (hΔ : MaxDegreeFour G)
    (F : Finset G.edgeSet) (hr : packingRank (L2 G) F ≤ 2) : F.card ≤ 40 := by
  obtain ⟨M,hMF,hM,hcard⟩ := ambient_packing_twenty G hΔ F
  have hh := independent_le_packingRank (L2 G) F M hMF hM
  omega

end Se20Part
