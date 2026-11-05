module

public import Se20Part.Legacy.Bounds.ConflictDegree

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem endpointNeighbourCover_card_eq_six_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24) :
    (endpointNeighbourCover G u v).card = 6 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := endpointNeighbourCover_card_le_six G huv hΔ
  have hc := conflict_degree_le_incidence_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem endpoint_degrees_eq_four_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24) :
    G.degree u = 4 ∧ G.degree v = 4 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := endpointNeighbourCover_card_eq_six_of_degree_eq_24 G hΔ e he h24
  have hu : ((G.neighborFinset u).erase v).card + 1 = G.degree u :=
    card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv : ((G.neighborFinset v).erase u).card + 1 = G.degree v :=
    card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hc := card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  dsimp [endpointNeighbourCover] at hcard
  omega

theorem cover_degree_eq_four_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24)
    {w : V} (hw : w ∈ endpointNeighbourCover G u v) : G.degree w = 4 := by
  have hcard := endpointNeighbourCover_card_eq_six_of_degree_eq_24 G hΔ e he h24
  have hc := conflict_degree_le_incidence_sum G e he
  have hwd := hΔ w
  by_contra hne
  have hlt : G.degree w < 4 := by omega
  have hs := sum_lt_sum (s := endpointNeighbourCover G u v)
    (fun x _ => hΔ x) ⟨w, hw, hlt⟩
  simp only [sum_const, smul_eq_mul, hcard] at hs
  omega

/-- Equality at 24 forces all six other endpoint-neighbours to be mutually
nonadjacent in the original graph. This is a local structural result, not a
global girth assumption. -/
theorem cover_independent_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24) :
    G.IsIndepSet (endpointNeighbourCover G u v : Set V) := by
  classical
  let S := endpointNeighbourCover G u v
  let I := fun w => G.incidenceFinset w
  have hc : 24 ≤ (S.biUnion I).card := by
    simpa only [h24] using conflict_degree_le_incidence_cover_card G e he
  have hcard := endpointNeighbourCover_card_eq_six_of_degree_eq_24 G hΔ e he h24
  have hsum : (∑ w ∈ S, (I w).card) ≤ 24 := by
    have hs := sum_le_sum (s := S) (fun w _ => hΔ w)
    simpa only [I, S, SimpleGraph.card_incidenceFinset_eq_degree, sum_const,
      smul_eq_mul, hcard] using hs
  intro x hx y hy hxy hAdj
  have hxS : x ∈ S := hx
  have hyS : y ∈ S := hy
  have hxI : s(x, y) ∈ I x := G.mem_incidenceFinset.mpr ⟨hAdj, Sym2.mem_mk_left x y⟩
  have hyI : s(x, y) ∈ I y := G.mem_incidenceFinset.mpr ⟨hAdj, Sym2.mem_mk_right x y⟩
  let R := (S.erase x).biUnion I
  have hR : s(x, y) ∈ R := mem_biUnion.mpr ⟨y, mem_erase.mpr ⟨hxy.symm, hyS⟩, hyI⟩
  have hpos : 0 < ((I x) ∩ R).card := card_pos.mpr ⟨s(x, y), mem_inter.mpr ⟨hxI, hR⟩⟩
  have hU : S.biUnion I = I x ∪ R := by
    conv_lhs => rw [← insert_erase hxS, biUnion_insert]
  have hUnion := card_union_add_card_inter (I x) R
  have hRest : R.card ≤ ∑ w ∈ S.erase x, (I w).card := card_biUnion_le
  have hSum := sum_erase_add S (fun w => (I w).card) hxS
  rw [hU] at hc
  omega

theorem other_neighbor_sets_disjoint_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24) :
    Disjoint ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u) := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.property)
  have hcard := endpointNeighbourCover_card_eq_six_of_degree_eq_24 G hΔ e he h24
  obtain ⟨hdu, hdv⟩ := endpoint_degrees_eq_four_of_degree_eq_24 G hΔ e he h24
  have hu : ((G.neighborFinset u).erase v).card + 1 = G.degree u :=
    card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv : ((G.neighborFinset v).erase u).card + 1 = G.degree v :=
    card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hc := card_union_add_card_inter ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hz : (((G.neighborFinset u).erase v) ∩ ((G.neighborFinset v).erase u)).card = 0 := by
    dsimp [endpointNeighbourCover] at hcard
    omega
  exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hz)

theorem endpoint_neighbor_sets_disjoint_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24) :
    Disjoint (G.neighborFinset u) (G.neighborFinset v) := by
  have hd := other_neighbor_sets_disjoint_of_degree_eq_24 G hΔ e he h24
  apply disjoint_left.mpr
  intro w hwu hwv
  have huw := (G.mem_neighborFinset u w).mp hwu
  have hvw := (G.mem_neighborFinset v w).mp hwv
  exact disjoint_left.mp hd (mem_erase.mpr ⟨hvw.ne.symm, hwu⟩)
    (mem_erase.mpr ⟨huw.ne.symm, hwv⟩)

/-- Neither endpoint of a degree-24 edge lies in a triangle. The theorem is
stated for the first endpoint; the same result applies after swapping endpoints. -/
theorem endpoint_neighborhood_independent_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24) :
    G.IsIndepSet (G.neighborSet u) := by
  have hd := endpoint_neighbor_sets_disjoint_of_degree_eq_24 G hΔ e he h24
  have hI := cover_independent_of_degree_eq_24 G hΔ e he h24
  intro x hx y hy hxy hAdj
  change G.Adj u x at hx
  change G.Adj u y at hy
  by_cases hxv : x = v
  · have hvy : G.Adj v y := hxv ▸ hAdj
    exact disjoint_left.mp hd ((G.mem_neighborFinset u y).mpr hy)
      ((G.mem_neighborFinset v y).mpr hvy)
  by_cases hyv : y = v
  · have hvx : G.Adj v x := hyv ▸ hAdj.symm
    exact disjoint_left.mp hd ((G.mem_neighborFinset u x).mpr hx)
      ((G.mem_neighborFinset v x).mpr hvx)
  exact hI (mem_union_left _ (mem_erase.mpr ⟨hxv, (G.mem_neighborFinset u x).mpr hx⟩))
    (mem_union_left _ (mem_erase.mpr ⟨hyv, (G.mem_neighborFinset u y).mpr hy⟩)) hxy hAdj

/-- The two sets of other neighbours have no connecting edge, so the fixed edge
cannot be part of a four-cycle. -/
theorem no_cross_edge_of_degree_eq_24
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h24 : (conflictGraph G).degree e = 24)
    {x y : V} (hx : x ∈ (G.neighborFinset u).erase v)
    (hy : y ∈ (G.neighborFinset v).erase u) : ¬ G.Adj x y := by
  by_cases hxy : x = y
  · subst y
    exact G.loopless.irrefl x
  exact cover_independent_of_degree_eq_24 G hΔ e he h24
    (mem_union_left _ hx) (mem_union_right _ hy) hxy

end Se20Part.Legacy
