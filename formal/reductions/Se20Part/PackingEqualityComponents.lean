import Se20Part.PackingAdditivity

noncomputable section
open scoped Classical BigOperators
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem tauG_component_zero (C : G.ConnectedComponent) (hC : C ∉ tightComponents G) :
    tauG G (componentEdges G C) = 0 := by
  unfold tauG Packing.tau
  apply Finset.sum_eq_zero
  intro B hB
  obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hB
  have hd := componentEdges_disjoint G (show C ≠ D from fun he => hC (he.symm ▸ hD))
  letI : DecidableEq G.edgeSet := fun a b => Classical.propDecidable (a=b)
  rw [Finset.disjoint_iff_inter_eq_empty.mp hd]
  simp

theorem circulant_component_equality (C : G.ConnectedComponent)
    (hC : Nonempty (C.toSimpleGraph ≃g NineCirculant)) :
    (componentEdges G C).card = 18 ∧
      packingRank (L2 G) (componentEdges G C) = 1 ∧ tauG G (componentEdges G C) = 0 := by
  obtain ⟨f⟩ := hC
  change (G.induce C.supp) ≃g NineCirculant at f
  have hcard : (componentEdges G C).card = 18 := by
    rw [card_componentEdges,SimpleGraph.card_edgeSet,
      SimpleGraph.Iso.card_edgeFinset_eq f,← SimpleGraph.card_edgeSet]
    exact nineCirculant_eighteen_edges
  have hcl : (L2 G).IsClique (componentEdges G C : Set G.edgeSet) := by
    intro e he g hg hne
    obtain ⟨e',he'⟩ := exists_edge_induce G C.supp e ((mem_componentEdges G C e).mp he)
    obtain ⟨g',hg'⟩ := exists_edge_induce G C.supp g ((mem_componentEdges G C g).mp hg)
    rw [← he',← hg',L2_embedding_adj_iff]
    apply (L2_embedding_adj_iff f.toEmbedding e' g').mp
    rw [nineCirculant_conflict_complete]
    intro hh
    have h' := SimpleGraph.Hom.mapEdgeSet.injective f.toHom f.injective hh
    exact hne (he'.symm.trans ((congrArg (inducedEmbedding G C.supp).mapEdgeSet h').trans hg'))
  have hle := (packingRank_le_one_iff (L2 G) (componentEdges G C)).mpr hcl
  have hn : packingRank (L2 G) (componentEdges G C) ≠ 0 := by
    intro hh
    have he := (packingRank_eq_zero_iff _ _).mp hh
    rw [he] at hcard
    simp at hcard
  refine ⟨hcard,by omega,tauG_component_zero G C ?_⟩
  intro hC
  have hh := tight_component_edges_card G hC
  omega

theorem packing_equality_biUnion {I : Type*} [DecidableEq I] (A : Finset I)
    (F : I → Finset G.edgeSet)
    (hd : (A : Set I).PairwiseDisjoint F)
    (hs : ∀ i ∈ A, ∀ j ∈ A, i ≠ j → ∀ e ∈ F i, ∀ f ∈ F j, ¬ (L2 G).Adj e f)
    (heq : ∀ i ∈ A, (F i).card = 18 * packingRank (L2 G) (F i) + tauG G (F i)) :
    (A.biUnion F).card = 18 * packingRank (L2 G) (A.biUnion F) + tauG G (A.biUnion F) := by
  induction A using Finset.induction_on with
  | empty => simp [packingRank,tauG,Packing.tau]
  | @insert i A hi ih =>
    have hdA : (A : Set I).PairwiseDisjoint F := fun a ha b hb hab =>
      hd (Finset.mem_insert_of_mem ha) (Finset.mem_insert_of_mem hb) hab
    have hsA := fun a (ha : a ∈ A) b (hb : b ∈ A) =>
      hs a (Finset.mem_insert_of_mem ha) b (Finset.mem_insert_of_mem hb)
    have heA := fun a (ha : a ∈ A) => heq a (Finset.mem_insert_of_mem ha)
    rw [Finset.biUnion_insert]
    apply packing_equality_union G _ _
    · apply Finset.disjoint_left.mpr
      intro e hei heA
      obtain ⟨j,hj,hej⟩ := Finset.mem_biUnion.mp heA
      exact Finset.disjoint_left.mp
        (hd (show i ∈ insert i A from by simp) (Finset.mem_insert_of_mem hj)
          (show i ≠ j from fun he => hi (he ▸ hj))) hei hej
    · intro e hei f hf
      obtain ⟨j,hj,hfj⟩ := Finset.mem_biUnion.mp hf
      exact hs i (by simp) j (Finset.mem_insert_of_mem hj) (fun he => hi (he ▸ hj)) e hei f hfj
    · exact heq i (by simp)
    · exact ih hdA hsA heA

end Se20Part
