import Se20Part.PetersenSupport
import Se20Part.GirthDegree

namespace Se20Part

/-- The original ten-vertex Petersen graph with the edge 12--34 removed. -/
def PetersenMinusGraph : SimpleGraph (Fin 10) where
  Adj u v := PetersenGraph.Adj u v ∧ ¬ ((u = 0 ∧ v = 7) ∨ (u = 7 ∧ v = 0))
  symm := ⟨by intro u v h; exact ⟨h.1.symm,by tauto⟩⟩
  loopless := ⟨by intro u h; exact h.1.ne rfl⟩

instance : DecidableRel PetersenMinusGraph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ ¬ (_ ∨ _)))

def petersenMinusEnds (i : Fin 14) : Fin 10 × Fin 10 :=
  ![(0,8),(0,9),(3,7),(6,7),(1,6),(3,4),(2,6),(3,5),
    (1,9),(2,8),(4,9),(5,8),(1,5),(2,4)] i

theorem petersenMinusEnds_adj : ∀ i,
    PetersenMinusGraph.Adj (petersenMinusEnds i).1 (petersenMinusEnds i).2 := by
  decide +kernel

def petersenMinusEdge (i : Fin 14) : PetersenMinusGraph.edgeSet :=
  ⟨s((petersenMinusEnds i).1,(petersenMinusEnds i).2),
    PetersenMinusGraph.mem_edgeSet.mpr (petersenMinusEnds_adj i)⟩

theorem petersenMinusEdge_injective : Function.Injective petersenMinusEdge := by
  decide +kernel

theorem petersenMinus_fourteen_edges : Fintype.card PetersenMinusGraph.edgeSet = 14 := by
  rw [SimpleGraph.card_edgeSet]
  decide +kernel

instance : DecidableRel (L2 PetersenMinusGraph).Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ _ ∧ ∃ a ∈ _, ∃ b ∈ _, a = b ∨ PetersenMinusGraph.Adj a b))

instance petersenMinusConflictDecidableAdj : DecidableRel PetersenMinusConflict.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ ∧ ¬ (_ ∨ _)))

set_option maxRecDepth 10000 in
theorem petersenMinusEdge_conflict : ∀ i j,
    (L2 PetersenMinusGraph).Adj (petersenMinusEdge i) (petersenMinusEdge j) ↔
      PetersenMinusConflict.Adj i j := by
  decide +kernel

/-- This identifies G15's labelled conflict graph with actual original
edges. It does not evaluate or assume a polynomial coefficient. -/
noncomputable def petersenMinusConflictIso : PetersenMinusConflict ≃g L2 PetersenMinusGraph where
  toEquiv := Equiv.ofBijective petersenMinusEdge
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨petersenMinusEdge_injective,by rw [petersenMinus_fourteen_edges]; decide⟩)
  map_rel_iff' := petersenMinusEdge_conflict _ _

theorem petersenMinus_degree_bounds :
    (∀ v, 2 ≤ PetersenMinusGraph.degree v) ∧ PetersenMinusGraph.degree 1 = 3 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- Every nonedge except the removed edge has an explicit path of length
two or three, checked over the ten original vertices. -/
theorem petersenMinus_short_paths : ∀ a b : Fin 10, a ≠ b →
    ¬ PetersenMinusGraph.Adj a b → ¬ ((a = 0 ∧ b = 7) ∨ (a = 7 ∧ b = 0)) →
    (∃ c, PetersenMinusGraph.Adj a c ∧ PetersenMinusGraph.Adj c b) ∨
      ∃ c d, a ≠ d ∧ c ≠ b ∧ PetersenMinusGraph.Adj a c ∧
        PetersenMinusGraph.Adj c d ∧ PetersenMinusGraph.Adj d b := by
  decide +kernel

noncomputable section
open scoped Classical
local instance petersenMinusKernelDecEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- No further chord is possible in ambient girth at least five. -/
theorem petersenMinus_only_missing_chord {V : Type*} {G : SimpleGraph V}
    (hg : 5 ≤ G.egirth) (f : PetersenMinusGraph →g G) (hf : Function.Injective f)
    {a b : Fin 10} (hab : G.Adj (f a) (f b)) :
    PetersenMinusGraph.Adj a b ∨ (a = 0 ∧ b = 7) ∨ (a = 7 ∧ b = 0) := by
  by_contra hn
  have hab' : a ≠ b := fun h => hab.ne (congrArg f h)
  have hnP : ¬ PetersenMinusGraph.Adj a b := fun h => hn (Or.inl h)
  have hnE : ¬ ((a = 0 ∧ b = 7) ∨ (a = 7 ∧ b = 0)) := fun h => hn (Or.inr h)
  rcases petersenMinus_short_paths a b hab' hnP hnE with ⟨c,hac,hcb⟩ | ⟨c,d,had,hcb,hac,hcd,hdb⟩
  · exact GirthFive.no_triangle hg (f.map_adj hac) (f.map_adj hcb) hab.symm
  · rcases GirthFive.square_backtrack hg (f.map_adj hac) (f.map_adj hcd)
      (f.map_adj hdb) hab.symm with h | h
    · exact had (hf h)
    · exact hcb (hf h)

def petersenMinusInternalEdges {V : Type*} {G : SimpleGraph V}
    (f : PetersenMinusGraph ↪g G) : Finset G.edgeSet := Finset.univ.image f.mapEdgeSet

theorem induced_petersenMinus_extension {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hG15 : PetersenMinusListTheoremG15) (hΔ : MaxDegreeFour G)
    (f : PetersenMinusGraph ↪g G) (A : Finset G.edgeSet)
    (hdis : Disjoint A (petersenMinusInternalEdges f)) (φ : PartialColouring (L2 G) A) :
    ∃ θ : PartialColouring (L2 G) (A ∪ petersenMinusInternalEdges f),
      ∀ a ∈ A, θ.colour a = φ.colour a := by
  have hi := embeddingOnFinsetIso (conflictEmbedding f) (petersenMinusInternalEdges f)
    (by intro e; simp only [petersenMinusInternalEdges,Finset.mem_image,Finset.mem_univ,true_and]; rfl)
  exact petersenMinus_block_extension (L2 G) hG15 (conflict_degree_le_twentyFour G hΔ)
    A _ hdis (petersenMinusConflictIso.trans hi) φ

theorem critical21_disjoint_induced_petersenMinus {V : Type*} [Fintype V]
    (G : SimpleGraph V) (hG15 : PetersenMinusListTheoremG15) (hΔ : MaxDegreeFour G)
    (f : PetersenMinusGraph ↪g G) {F : Finset G.edgeSet} (hF : Critical21 G F) :
    Disjoint F (petersenMinusInternalEdges f) := by
  apply critical21_disjoint_of_extension G _ _ hF
  intro A hA φ
  obtain ⟨θ,_⟩ := induced_petersenMinus_extension G hG15 hΔ f A hA φ
  exact ⟨θ⟩

end
end Se20Part
