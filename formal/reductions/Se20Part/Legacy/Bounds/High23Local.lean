module

public import Se20Part.Legacy.Bounds.EdgeCounting

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high23_cover_card_eq_six
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e) :
    (endpointNeighbourCover G u v).card = 6 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hc := endpointNeighbourCover_card_le_six G huv hΔ
  have hd := conflict_degree_le_incidence_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem high23_endpoints_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e) :
    G.degree u = 4 ∧ G.degree v = 4 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := high23_cover_card_eq_six G hΔ e he h23
  have hu := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv := card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hc := card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  dsimp [endpointNeighbourCover] at hcard
  omega

theorem high23_other_neighbor_sets_disjoint
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e) :
    Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := high23_cover_card_eq_six G hΔ e he h23
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

theorem high23_no_triangle_on_edge
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e)
    {w : V} (huw : G.Adj u w) : ¬ G.Adj v w := by
  intro hvw
  exact disjoint_left.mp (high23_other_neighbor_sets_disjoint G hΔ e he h23)
    (mem_erase.mpr ⟨hvw.ne.symm, (G.mem_neighborFinset u w).mpr huw⟩)
    (mem_erase.mpr ⟨huw.ne.symm, (G.mem_neighborFinset v w).mpr hvw⟩)

/-- At most one original edge lies wholly within the six-vertex cover.
This follows from an exact incidence identity, not a girth assumption. -/
theorem high23_cover_inside_card_le_one
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e) :
    (edgesInside G univ (endpointNeighbourCover G u v)).card ≤ 1 := by
  have hc := conflict_degree_add_inside_le_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  have hcard := high23_cover_card_eq_six G hΔ e he h23
  simp only [sum_const, smul_eq_mul, hcard] at hs
  omega

/-- Two four-cycles through the fixed high23 edge have the same ordered
opposite edge. The order records which endpoint is on each side. -/
theorem high23_cross_edges_unique
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e)
    {x y x' y' : V}
    (hx : x ∈ (G.neighborFinset u).erase v)
    (hy : y ∈ (G.neighborFinset v).erase u)
    (hx' : x' ∈ (G.neighborFinset u).erase v)
    (hy' : y' ∈ (G.neighborFinset v).erase u)
    (hxy : G.Adj x y) (hxy' : G.Adj x' y') : x = x' ∧ y = y' := by
  classical
  let f : G.edgeSet := ⟨s(x, y), hxy⟩
  let f' : G.edgeSet := ⟨s(x', y'), hxy'⟩
  have hf : f ∈ edgesInside G univ (endpointNeighbourCover G u v) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact Sym2.forall_mem_pair.mpr ⟨mem_union_left _ hx, mem_union_right _ hy⟩
  have hf' : f' ∈ edgesInside G univ (endpointNeighbourCover G u v) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    exact Sym2.forall_mem_pair.mpr ⟨mem_union_left _ hx', mem_union_right _ hy'⟩
  have heq := card_le_one.mp (high23_cover_inside_card_le_one G hΔ e he h23) f hf f' hf'
  have hp : s(x, y) = s(x', y') := congrArg Subtype.val heq
  rcases Sym2.eq_iff.mp hp with h | h
  · exact h
  · exact (disjoint_left.mp (high23_other_neighbor_sets_disjoint G hΔ e he h23)
      hx (h.1.symm ▸ hy')).elim

/-- A four-cycle through an oriented edge `u-v` is represented by its
ordered opposite edge `(x,y)`, with `x` on the `u` side and `y` on the `v` side. -/
def fourCycleOpposites (u v : V) : Finset (V × V) :=
  (((G.neighborFinset u).erase v) ×ˢ ((G.neighborFinset v).erase u)).filter
    (fun p => G.Adj p.1 p.2)

theorem high23_at_most_one_four_cycle_on_edge
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h23 : 23 ≤ (conflictGraph G).degree e) :
    (fourCycleOpposites G u v).card ≤ 1 := by
  apply card_le_one.mpr
  intro p hp q hq
  obtain ⟨hp, hpAdj⟩ := mem_filter.mp hp
  obtain ⟨hq, hqAdj⟩ := mem_filter.mp hq
  obtain ⟨hxp, hyp⟩ := mem_product.mp hp
  obtain ⟨hxq, hyq⟩ := mem_product.mp hq
  exact Prod.ext_iff.mpr (high23_cross_edges_unique G hΔ e he h23 hxp hyp hxq hyq hpAdj hqAdj)

end Se20Part.Legacy
