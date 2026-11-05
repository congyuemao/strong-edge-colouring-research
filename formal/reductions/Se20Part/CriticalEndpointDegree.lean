import Se20Part.Critical

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- An auxiliary step for G12: every endpoint of a critical edge has degree
at least three in the original graph. No minimal-counterexample convention
or cut-gluing theorem is assumed here. -/
theorem critical21_endpoint_degree (hΔ : MaxDegreeFour G)
    {F : Finset G.edgeSet} (hF : Critical21 G F) {e : G.edgeSet} (he : e ∈ F)
    {u : V} (hu : u ∈ e.val) : 3 ≤ G.degree u := by
  by_contra hn
  obtain ⟨v,hev⟩ := Sym2.mem_iff_exists.mp hu
  have huv : G.Adj u v := G.mem_edgeSet.mp (hev ▸ e.prop)
  have h1 := Finset.card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have h2 := Finset.card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h1 h2
  have h3 := Finset.card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hd := hΔ v
  have hr : (rim G u v).card ≤ 4 := by unfold rim; omega
  have hc := card_conflicts_le_mul_rim G hΔ e hev
  have hmin := critical21_min_degree G hF he
  have hsub : F.filter ((L2 G).Adj e) ⊆ conflicts G e := by
    intro f hf
    exact (mem_conflicts G e f).mpr (Finset.mem_filter.mp hf).2
  have hh := Finset.card_le_card hsub
  omega

end Se20Part
