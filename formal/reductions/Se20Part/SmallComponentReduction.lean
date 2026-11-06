import Se20Part.PetersenExtension
import Se20Part.G05FiniteReduction
import Se20Part.PackingCases

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance smallComponentDecEq1 : DecidableEq G.edgeSet := Classical.decEq _

theorem componentEdges_closed (C : G.ConnectedComponent) {e f : G.edgeSet}
    (he : e ∈ componentEdges G C) (hef : (L2 G).Adj e f) : f ∈ componentEdges G C := by
  obtain ⟨_,a,ha,b,hb,hab⟩ := hef
  have haC := (mem_componentEdges G C e).mp he a ha
  have hbC : b ∈ C.supp := by
    rcases hab with rfl | hab
    · exact haC
    · exact C.mem_supp_of_adj_mem_supp haC hab
  obtain ⟨b',hf⟩ := Sym2.mem_iff_exists.mp hb
  have hbb' : G.Adj b b' := G.mem_edgeSet.mp (hf ▸ f.prop)
  apply (mem_componentEdges G C f).mpr
  intro z hz
  rw [hf,Sym2.mem_iff] at hz
  rcases hz with rfl | rfl
  · exact hbC
  · exact C.mem_supp_of_adj_mem_supp hbC hbb'

theorem componentEdges_card_le_twice (hΔ : MaxDegreeFour G) (C : G.ConnectedComponent) :
    (componentEdges G C).card ≤ 2 * Fintype.card C.supp := by
  rw [card_componentEdges]
  have hd : MaxDegreeFour (G.induce C.supp) := by
    intro v
    exact (embedding_degree_le (inducedEmbedding G C.supp) v).trans (hΔ v.val)
  exact (edge_bound_remove_isolates _ hd).trans (Nat.mul_le_mul_left 2 (Nat.sub_le _ _))

/-- The colouring step of G07's closed-support reduction. The three G05
checks remain explicit; no geometric finite check is silently supplied. -/
theorem critical21_disjoint_small_closed
    (hSmall : G05SmallAbstractCheck) (hMiddle : G05MiddleAbstractCheck)
    (hBoundary : G05BoundaryAbstractCheck) (hΔ : MaxDegreeFour G)
    (B : Finset G.edgeSet) (hB : B.card ≤ 41)
    (hclosed : ∀ e ∈ B, ∀ f, (L2 G).Adj e f → f ∈ B)
    {F : Finset G.edgeSet} (hF : Critical21 G F) : Disjoint F B := by
  apply critical21_disjoint_of_extension G B _ hF
  intro A hdis φ
  obtain ⟨ψ⟩ := (partialColouring_iff_colourable (L2 G) B).mpr
    (small_edge_set_twenty_of_finite_checks G hSmall hMiddle hBoundary hΔ B hB)
  obtain ⟨θ,_,_⟩ := merge_partial_palette (L2 G) A B hdis φ ψ (Equiv.refl _) (by
    intro a ha b hb hab
    exact (Finset.disjoint_left.mp hdis ha (hclosed b hb a hab.symm)).elim)
  exact ⟨θ⟩

/-- In particular, the at-most-sixteen-vertex component returned by G07's
geometric search cannot contain a critical edge: it has at most 32 edges. -/
theorem critical21_disjoint_component_sixteen
    (hSmall : G05SmallAbstractCheck) (hMiddle : G05MiddleAbstractCheck)
    (hBoundary : G05BoundaryAbstractCheck) (hΔ : MaxDegreeFour G)
    (C : G.ConnectedComponent) (hC : Fintype.card C.supp ≤ 16)
    {F : Finset G.edgeSet} (hF : Critical21 G F) : Disjoint F (componentEdges G C) := by
  apply critical21_disjoint_small_closed G hSmall hMiddle hBoundary hΔ _ _ _ hF
  · have hh := componentEdges_card_le_twice G hΔ C; omega
  · intro e he f hef; exact componentEdges_closed G C he hef

end Se20Part
