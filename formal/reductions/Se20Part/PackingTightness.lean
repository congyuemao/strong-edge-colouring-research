import Se20Part.PackingCases

noncomputable section
open scoped Classical BigOperators
namespace Se20Part

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def NineCirculant : SimpleGraph (Fin 9) where
  Adj a b := (a.val+1)%9 = b.val ∨ (b.val+1)%9 = a.val ∨
    (a.val+3)%9 = b.val ∨ (b.val+3)%9 = a.val
  symm := ⟨by intros; tauto⟩
  loopless := ⟨by intro a; have := a.isLt; omega⟩

theorem nineCirculant_degree_four : FourRegular NineCirculant := by
  letI : DecidableRel NineCirculant.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
  intro v
  rw [← SimpleGraph.card_neighborSet_eq_degree, Fintype.card_eq_nat_card,
    ← Fintype.card_eq_nat_card, SimpleGraph.card_neighborSet_eq_degree]
  have hh : ∀ x, NineCirculant.degree x = 4 := by decide +kernel
  exact hh v

theorem nineCirculant_eighteen_edges : Fintype.card NineCirculant.edgeSet = 18 := by
  rw [Fintype.card_eq_nat_card]
  letI : DecidableRel NineCirculant.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))
  rw [← Fintype.card_eq_nat_card, SimpleGraph.card_edgeSet]
  decide +kernel

theorem conflict_complete_of_endpoint_witness {V : Type*} (G : SimpleGraph V)
    (h : ∀ a b c d, G.Adj a b → G.Adj c d →
      ∃ x ∈ s(a,b), ∃ y ∈ s(c,d), x = y ∨ G.Adj x y) : L2 G = ⊤ := by
  ext e f
  change (_ ∧ _) ↔ e ≠ f
  refine ⟨And.left,fun hne => ⟨hne,?_⟩⟩
  obtain ⟨a,b,he⟩ : ∃ a b, e.val = s(a,b) := Sym2.ind (fun a b => ⟨a,b,rfl⟩) e.val
  obtain ⟨c,d,hf⟩ : ∃ c d, f.val = s(c,d) := Sym2.ind (fun c d => ⟨c,d,rfl⟩) f.val
  rw [he,hf]
  exact h a b c d (G.mem_edgeSet.mp (he ▸ e.prop)) (G.mem_edgeSet.mp (hf ▸ f.prop))

theorem nineCirculant_conflict_complete : L2 NineCirculant = ⊤ := by
  apply conflict_complete_of_endpoint_witness
  unfold NineCirculant
  decide +kernel

theorem pentagonDouble_conflict_complete : L2 PentagonDouble = ⊤ := by
  apply conflict_complete_of_endpoint_witness
  unfold PentagonDouble SimpleGraph.comap
  decide +kernel

theorem no_tight_component_of_card_lt_ten {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hn : Fintype.card V < 10) : tightComponents G = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro C hC
  obtain ⟨f⟩ := (Finset.mem_filter.mp hC).2
  have hc := Fintype.card_congr f.toEquiv
  have hb := Fintype.card_subtype_le (· ∈ C.supp)
  change Fintype.card C.supp = Fintype.card (Fin 5 × Fin 2) at hc
  simp only [Fintype.card_prod,Fintype.card_fin] at hc
  simp only [Fintype.card_eq_nat_card] at hc hb hn
  change Nat.card C.supp ≤ Nat.card V at hb
  omega

theorem nineCirculant_tight :
    Fintype.card NineCirculant.edgeSet = 18 ∧
      packingRank (L2 NineCirculant) Finset.univ = 1 ∧
      tauG NineCirculant Finset.univ = 0 := by
  refine ⟨nineCirculant_eighteen_edges,?_,?_⟩
  · have hle : packingRank (L2 NineCirculant) Finset.univ ≤ 1 :=
      (packingRank_le_one_iff _ _).mpr (by simp [nineCirculant_conflict_complete])
    have hn : packingRank (L2 NineCirculant) Finset.univ ≠ 0 := by
      intro h
      have he := (packingRank_eq_zero_iff _ _).mp h
      have hc := congrArg Finset.card he
      simp only [Finset.card_univ, Finset.card_empty] at hc
      have hh := nineCirculant_eighteen_edges
      simp only [Fintype.card_eq_nat_card] at hc hh
      omega
    omega
  · rw [tauG_univ, no_tight_component_of_card_lt_ten NineCirculant (by decide)]
    simp

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

theorem tight_component_clique (C : G.ConnectedComponent) (hC : C ∈ tightComponents G) :
    (L2 G).IsClique (componentEdges G C : Set G.edgeSet) := by
  obtain ⟨f⟩ := (Finset.mem_filter.mp hC).2
  intro e he g hg hne
  obtain ⟨e',he'⟩ := exists_edge_induce G C.supp e ((mem_componentEdges G C e).mp he)
  obtain ⟨g',hg'⟩ := exists_edge_induce G C.supp g ((mem_componentEdges G C g).mp hg)
  rw [← he',← hg',L2_embedding_adj_iff]
  apply (L2_embedding_adj_iff f.toEmbedding e' g').mp
  rw [pentagonDouble_conflict_complete]
  intro hh
  have h' := SimpleGraph.Hom.mapEdgeSet.injective f.toHom f.injective hh
  exact hne (he'.symm.trans ((congrArg (inducedEmbedding G C.supp).mapEdgeSet h').trans hg'))

theorem tight_component_subset_equality (F : Finset G.edgeSet) (C : G.ConnectedComponent)
    (hC : C ∈ tightComponents G) (hF : F ⊆ componentEdges G C) (hlarge : 18 ≤ F.card) :
    packingRank (L2 G) F = 1 ∧ F.card = 18 * packingRank (L2 G) F + tauG G F := by
  have hle : packingRank (L2 G) F ≤ 1 :=
    (packingRank_le_one_iff _ _).mpr (fun e he f hf hne =>
      tight_component_clique G C hC (hF he) (hF hf) hne)
  have hn : packingRank (L2 G) F ≠ 0 := by
    intro h
    have := (packingRank_eq_zero_iff _ _).mp h
    simp [this] at hlarge
  have he : packingRank (L2 G) F = 1 := by omega
  refine ⟨he,?_⟩
  rw [he,tauG_of_subset_tight G F C hC hF]
  omega

end Se20Part
