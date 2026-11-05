import Se20Part.Packing
import Se20Part.CycleLength

noncomputable section
open scoped Classical
namespace Se20Part

theorem pentagonDouble_twenty_edges : Fintype.card PentagonDouble.edgeSet = 20 := by
  rw [Fintype.card_eq_nat_card]
  letI : DecidableRel PentagonDouble.Adj := fun x y =>
    inferInstanceAs (Decidable ((SimpleGraph.cycleGraph 5).Adj x.1 y.1))
  rw [← Fintype.card_eq_nat_card, SimpleGraph.card_edgeSet]
  decide +kernel

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

def componentEdges (C : G.ConnectedComponent) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => ∀ v ∈ e.val, v ∈ C.supp)

theorem mem_componentEdges (C : G.ConnectedComponent) (e : G.edgeSet) :
    e ∈ componentEdges G C ↔ ∀ v ∈ e.val, v ∈ C.supp := by simp [componentEdges]

theorem componentEdges_disjoint {C D : G.ConnectedComponent} (hne : C ≠ D) :
    Disjoint (componentEdges G C) (componentEdges G D) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨a,b,h⟩ : ∃ a b, e.val = s(a,b) := Sym2.ind (fun a b => ⟨a,b,rfl⟩) e.val
  have ha : a ∈ e.val := h ▸ Sym2.mem_mk_left a b
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex
    ((mem_componentEdges G C e).mp he a ha) ((mem_componentEdges G D e).mp hf a ha))

theorem componentEdges_separated {C D : G.ConnectedComponent} (hne : C ≠ D)
    {e f : G.edgeSet} (he : e ∈ componentEdges G C) (hf : f ∈ componentEdges G D) :
    ¬ (L2 G).Adj e f := by
  rintro ⟨_,a,ha,b,hb,hab⟩
  have haC := (mem_componentEdges G C e).mp he a ha
  have hbD := (mem_componentEdges G D f).mp hf b hb
  have hbC : b ∈ C.supp := by
    rcases hab with rfl | hab
    · exact haC
    · exact C.mem_supp_of_adj_mem_supp haC hab
  exact hne (SimpleGraph.ConnectedComponent.eq_of_common_vertex hbC hbD)

theorem card_componentEdges (C : G.ConnectedComponent) :
    (componentEdges G C).card = Fintype.card (G.induce C.supp).edgeSet := by
  let f := (inducedEmbedding G C.supp).mapEdgeSet
  have hinj : Function.Injective f :=
    SimpleGraph.Hom.mapEdgeSet.injective _ (inducedEmbedding G C.supp).injective
  have heq : Finset.univ.image f = componentEdges G C := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and, mem_componentEdges]
    constructor
    · rintro ⟨e',rfl⟩ v hv
      obtain ⟨v',_,rfl⟩ := Sym2.mem_map.mp hv
      exact v'.prop
    · intro he
      exact exists_edge_induce G C.supp e he
  rw [← heq, Finset.card_image_of_injective _ hinj, Finset.card_univ]

def tightComponents : Finset G.ConnectedComponent :=
  Finset.univ.filter (fun C => Nonempty ((G.induce C.supp) ≃g PentagonDouble))

theorem tight_component_edges_card {C : G.ConnectedComponent} (hC : C ∈ tightComponents G) :
    (componentEdges G C).card = 20 := by
  obtain ⟨f⟩ := (Finset.mem_filter.mp hC).2
  rw [card_componentEdges, SimpleGraph.card_edgeSet,
    SimpleGraph.Iso.card_edgeFinset_eq f, ← SimpleGraph.card_edgeSet]
  exact pentagonDouble_twenty_edges

/-- The blocks here are exactly the edge sets of C₅[2] components of G. -/
def tightBlocks : Packing.TwentyBlocks (L2 G) where
  blocks := (tightComponents G).image (componentEdges G)
  card_twenty := by
    intro B hB
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
    exact tight_component_edges_card G hC
  disjoint := by
    intro B hB D hD hne
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
    exact componentEdges_disjoint G (fun h => hne (congrArg (componentEdges G) h))
  separated := by
    intro B hB D hD hne e he f hf
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hB
    obtain ⟨E,hE,rfl⟩ := Finset.mem_image.mp hD
    exact componentEdges_separated G (fun h => hne (congrArg (componentEdges G) h)) he hf

def tauG (F : Finset G.edgeSet) : ℕ := Packing.tau (L2 G) F (tightBlocks G)
def fullTightCount (F : Finset G.edgeSet) : ℕ := Packing.fullCount (L2 G) F (tightBlocks G)

/-- Item 5.7, with the actual C₅[2] component correction from the manuscript. -/
theorem packing18_implies19 (F : Finset G.edgeSet)
    (h18 : F.card ≤ 18 * packingRank (L2 G) F + tauG G F) :
    F.card ≤ 19 * packingRank (L2 G) F + fullTightCount G F :=
  Packing.eighteen_implies_nineteen (L2 G) F (tightBlocks G) h18

end Se20Part
