import Se20Insertion.ShellCover
import Se20Insertion.TwoStepSaturation

namespace Se20Insertion.SeventhPassExamples

def hexagon : SimpleGraph (Fin 6) := SimpleGraph.fromEdgeSet
  ({s(0,1),s(1,2),s(2,3),s(3,4),s(4,5),s(5,0)} : Finset (Sym2 (Fin 6)))

instance : DecidableRel hexagon.Adj := by unfold hexagon; infer_instance

/-- The old predicate only tests triangles and squares through the hole. -/
theorem hexagon_locallyTreeAt : LocallyTreeAt hexagon 0 1 := by unfold LocallyTreeAt; decide

def farLeft : hexagon.edgeSet := ⟨s(5,4),by rw [SimpleGraph.mem_edgeSet]; decide⟩
def farRight : hexagon.edgeSet := ⟨s(2,3),by rw [SimpleGraph.mem_edgeSet]; decide⟩

/-- Opposite far branches can conflict under that predicate: the edge 4--3
closes a six-cycle. Thus it cannot justify the tree-pattern adjacency rule. -/
theorem hexagon_opposite_far_conflict :
    hexagon.Adj 0 5 ∧ hexagon.Adj 1 2 ∧ (L2 hexagon).Adj farLeft farRight := by
  refine ⟨by decide,by decide,?_,4,by decide,3,by decide,Or.inr (by decide)⟩
  decide

def oneEdge : SimpleGraph (Fin 2) := ⊤

def oneColoured : PartialColouring oneEdge ({1} : Finset (Fin 2)) where
  colour _ := 0
  proper := by
    intro x y hx hy hxy
    simp only [Finset.mem_singleton] at hx hy
    subst x; subst y
    exact (hxy.ne rfl).elim

theorem raw_P4_needs_obstruction :
    oneColoured.Single 0 0 1 ∧ oneColoured.Free 1 1 := by
  constructor
  · exact ⟨⟨by simp,by change (0 : Fin 2) ≠ 1; decide,rfl⟩,fun x hx => by simpa using hx.1⟩
  · rintro ⟨x,hx⟩
    have h : (0 : Colour) = 1 := hx.2.2
    exact (by decide : (0 : Colour) ≠ 1) h

end Se20Insertion.SeventhPassExamples
