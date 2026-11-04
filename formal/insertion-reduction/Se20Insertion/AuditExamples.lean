import Se20Insertion.Triangle

namespace Se20Insertion.AuditExamples

/-- Explicit counterexample to the manuscript's claim that `Z` misses `N(e)`.
All 20 edges other than `01` conflict with `01`; give them 20 distinct colours. -/
def triangleExampleEdges : Finset (Sym2 (Fin 20)) :=
  {s(0,1), s(0,2), s(1,2), s(0,3), s(0,4), s(1,5), s(1,6), s(2,7), s(2,8),
   s(3,9), s(3,10), s(3,11), s(4,12), s(4,13), s(4,14),
   s(5,7), s(5,15), s(5,16), s(6,17), s(6,18), s(6,19)}

def triangleExample : SimpleGraph (Fin 20) := SimpleGraph.fromEdgeSet triangleExampleEdges

instance : DecidableRel triangleExample.Adj := by
  unfold triangleExample
  infer_instance

def exampleE : triangleExample.edgeSet := ⟨s(0,1), by rw [SimpleGraph.mem_edgeSet]; decide⟩
def exampleUW : triangleExample.edgeSet := ⟨s(0,2), by rw [SimpleGraph.mem_edgeSet]; decide⟩
def exampleOverlap : triangleExample.edgeSet := ⟨s(5,7), by rw [SimpleGraph.mem_edgeSet]; decide⟩

theorem example_overlap_conflicts_e : (L2 triangleExample).Adj exampleE exampleOverlap := by
  refine ⟨by decide, 1, by decide, 5, by decide, Or.inr ?_⟩
  decide

theorem example_overlap_conflicts_uw : (L2 triangleExample).Adj exampleUW exampleOverlap := by
  refine ⟨by decide, 2, by decide, 7, by decide, Or.inr ?_⟩
  decide

/-- The overlapping edge is one of the edges at `z₁ = 7` other than `wz₁`. -/
theorem example_overlap_in_Z :
    triangleExample.Adj 2 7 ∧ (7 : Fin 20) ∈ exampleOverlap.val ∧
      (2 : Fin 20) ∉ exampleOverlap.val := by decide

end Se20Insertion.AuditExamples
