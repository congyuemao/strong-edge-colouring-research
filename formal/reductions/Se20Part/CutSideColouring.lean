import Se20Part.CutGeometry
import Se20Part.CycleLength

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance cutSideColouringDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Colouring an induced original-graph side is equivalent to colouring
its actual edges with all conflicts evaluated in the original graph. -/
theorem side_colourable_iff (A : Finset V) :
    StrongColourable (G.induce (A : Set V)) 20 ↔
      Nonempty (PartialColouring (L2 G) (sideEdges G A)) := by
  let f := (inducedEmbedding G (A : Set V)).mapEdgeSet
  have hf : Function.Injective f :=
    SimpleGraph.Hom.mapEdgeSet.injective _ Subtype.val_injective
  have hmem : ∀ e, f e ∈ sideEdges G A := by
    intro e
    apply (mem_sideEdges G A _).mpr
    intro v hv
    obtain ⟨w,_,hw⟩ := Sym2.mem_map.mp hv
    exact hw ▸ w.prop
  have hex : ∀ e ∈ sideEdges G A, ∃ d, f d = e := by
    intro e he
    exact exists_edge_induce G (A : Set V) e ((mem_sideEdges G A e).mp he)
  constructor
  · rintro ⟨c⟩
    let col : G.edgeSet → Colour := fun e =>
      if he : e ∈ sideEdges G A then c (hex e he).choose else 0
    refine ⟨⟨col,?_⟩⟩
    intro e d he hd hed
    have hconf := (L2_induce_adj_iff G (A : Set V)
      (hex e he).choose (hex d hd).choose).mp
      (by
        change (L2 G).Adj (f (hex e he).choose) (f (hex d hd).choose)
        rw [(hex e he).choose_spec,(hex d hd).choose_spec]
        exact hed)
    simpa only [col,dif_pos he,dif_pos hd] using c.valid hconf
  · rintro ⟨c⟩
    exact ⟨SimpleGraph.Coloring.mk (fun e => c.colour (f e))
      (fun {e d} hed => c.proper (hmem e) (hmem d)
        ((L2_induce_adj_iff G (A : Set V) e d).mpr hed))⟩

end Se20Part
