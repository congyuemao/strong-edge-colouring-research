module

public import Se20Part.Legacy.Bounds.High23Local

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high22_cover_card_eq_six
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h22 : 22 ≤ (conflictGraph G).degree e) :
    (endpointNeighbourCover G u v).card = 6 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := endpointNeighbourCover_card_le_six G huv hΔ
  have hd := conflict_degree_le_incidence_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem high22_endpoints_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h22 : 22 ≤ (conflictGraph G).degree e) :
    G.degree u = 4 ∧ G.degree v = 4 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := high22_cover_card_eq_six G hΔ e he h22
  have hu := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv := card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hc := card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  dsimp [endpointNeighbourCover] at hcard
  omega

theorem high22_other_neighbor_sets_disjoint
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h22 : 22 ≤ (conflictGraph G).degree e) :
    Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := high22_cover_card_eq_six G hΔ e he h22
  have hu := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv := card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hc := card_union_add_card_inter ((G.neighborFinset u).erase v)
    ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  apply disjoint_iff_inter_eq_empty.mpr
  apply card_eq_zero.mp
  dsimp [endpointNeighbourCover] at hcard
  omega

theorem high22_no_triangle_on_edge
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h22 : 22 ≤ (conflictGraph G).degree e)
    {w : V} (huw : G.Adj u w) : ¬ G.Adj v w := by
  intro hvw
  exact disjoint_left.mp (high22_other_neighbor_sets_disjoint G hΔ e he h22)
    (mem_erase.mpr ⟨hvw.ne.symm, (G.mem_neighborFinset u w).mpr huw⟩)
    (mem_erase.mpr ⟨huw.ne.symm, (G.mem_neighborFinset v w).mpr hvw⟩)

/-- At most two original edges lie wholly within the six-vertex cover.
This follows from an exact incidence identity, not a girth assumption. -/
theorem high22_cover_inside_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h22 : 22 ≤ (conflictGraph G).degree e) :
    (edgesInside G univ (endpointNeighbourCover G u v)).card ≤ 2 := by
  have hc := conflict_degree_add_inside_le_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  have hcard := high22_cover_card_eq_six G hΔ e he h22
  simp only [sum_const, smul_eq_mul, hcard] at hs
  omega

theorem high22_at_most_two_four_cycles_on_edge
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h22 : 22 ≤ (conflictGraph G).degree e) :
    (fourCycleOpposites G u v).card ≤ 2 := by
  classical
  have hc : (fourCycleOpposites G u v).card ≤
      (edgesInside G univ (endpointNeighbourCover G u v)).card := by
    apply card_le_via_relation _ _ (fun p f => f.val = s(p.1, p.2))
    · intro p hp
      obtain ⟨hp, hpAdj⟩ := mem_filter.mp hp
      obtain ⟨hx, hy⟩ := mem_product.mp hp
      refine ⟨⟨s(p.1, p.2), hpAdj⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact Sym2.forall_mem_pair.mpr ⟨mem_union_left _ hx, mem_union_right _ hy⟩
    · intro p hp q hq f hpf hqf
      obtain ⟨hp, _⟩ := mem_filter.mp hp
      obtain ⟨hq, _⟩ := mem_filter.mp hq
      obtain ⟨hxp, hyp⟩ := mem_product.mp hp
      obtain ⟨hxq, hyq⟩ := mem_product.mp hq
      rcases Sym2.eq_iff.mp (hpf.symm.trans hqf) with h | h
      · exact Prod.ext h.1 h.2
      · exact (disjoint_left.mp (high22_other_neighbor_sets_disjoint G hΔ e he h22)
          hxp (h.1.symm ▸ hyq)).elim
  exact hc.trans (high22_cover_inside_card_le_two G hΔ e he h22)

end Se20Part.Legacy
