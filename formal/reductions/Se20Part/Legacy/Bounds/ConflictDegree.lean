module

public import Se20Part.Legacy.Conflict
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The other neighbours of the endpoints of an original edge. -/
def endpointNeighbourCover (u v : V) : Finset V :=
  (G.neighborFinset u).erase v ∪ (G.neighborFinset v).erase u

theorem endpointNeighbourCover_comm (u v : V) :
    endpointNeighbourCover G v u = endpointNeighbourCover G u v := by
  exact union_comm _ _

/-- An edge through one endpoint, different from the fixed edge, has its other
endpoint in the cover. -/
theorem incident_edge_meets_cover {u v : V} {f : G.edgeSet}
    (hne : f.val ≠ s(u, v)) (hu : u ∈ f.val) :
    ∃ w ∈ endpointNeighbourCover G u v, w ∈ f.val := by
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hu
  have hadj : G.Adj u w := by
    have hf := f.property
    rw [hw] at hf
    exact hf
  have hwv : w ≠ v := by
    intro h
    apply hne
    simpa only [h] using hw
  refine ⟨w, mem_union_left _ (mem_erase.mpr ⟨hwv, ?_⟩), ?_⟩
  · exact (G.mem_neighborFinset u w).mpr hadj
  · rw [hw]
    exact Sym2.mem_mk_right u w

theorem lineGraph_adj_meets_cover {u v : V} {e f : G.edgeSet}
    (he : e.val = s(u, v)) (h : G.lineGraph.Adj e f) :
    ∃ w ∈ endpointNeighbourCover G u v, w ∈ f.val := by
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp h with ⟨hne, x, hx, hxf⟩
  have hfe : f.val ≠ s(u, v) := by
    intro hf
    exact hne (Subtype.ext (he.trans hf.symm))
  rw [he, Sym2.mem_iff] at hx
  rcases hx with hxu | hxv
  · exact incident_edge_meets_cover G hfe (hxu ▸ hxf)
  · have hfv : f.val ≠ s(v, u) := by simpa only [Sym2.eq_swap] using hfe
    simpa only [endpointNeighbourCover_comm G u v] using
      incident_edge_meets_cover G hfv (hxv ▸ hxf)

@[simp] theorem left_notMem_endpointNeighbourCover (u v : V) :
    u ∉ endpointNeighbourCover G u v := by
  simp [endpointNeighbourCover]

@[simp] theorem right_notMem_endpointNeighbourCover (u v : V) :
    v ∉ endpointNeighbourCover G u v := by
  simp [endpointNeighbourCover]

/-- This cover uses all original edges, including connecting edges outside any
candidate set. No triangle or four-cycle restriction is imposed. -/
theorem strongConflict_meets_cover {u v : V} {e f : G.edgeSet}
    (he : e.val = s(u, v)) (h : StrongConflict G e f) :
    ∃ w ∈ endpointNeighbourCover G u v, w ∈ f.val := by
  rcases h with ⟨hne, h | ⟨g, heg, hgf⟩⟩
  · exact lineGraph_adj_meets_cover G he h
  · obtain ⟨w, hw, hwg⟩ := lineGraph_adj_meets_cover G he heg
    rcases SimpleGraph.lineGraph_adj_iff_exists.mp heg with ⟨_, z, hze, hzg⟩
    rcases SimpleGraph.lineGraph_adj_iff_exists.mp hgf with ⟨_, x, hxg, hxf⟩
    have hzw : z ≠ w := by
      intro hzw
      subst z
      rw [he, Sym2.mem_iff] at hze
      rcases hze with hwu | hwv
      · exact left_notMem_endpointNeighbourCover G u v (hwu ▸ hw)
      · exact right_notMem_endpointNeighbourCover G u v (hwv ▸ hw)
    have hg : g.val = s(z, w) := (Sym2.mem_and_mem_iff hzw).mp ⟨hzg, hwg⟩
    rw [hg, Sym2.mem_iff] at hxg
    rcases hxg with hxz | hxw
    · apply lineGraph_adj_meets_cover G he
      exact SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hne, z, hze, hxz ▸ hxf⟩
    · exact ⟨w, hw, hxw ▸ hxf⟩

/-- Every full-conflict neighbour is covered by an incidence set. -/
theorem conflict_neighbors_subset_incidence_cover
    [DecidableRel (conflictGraph G).Adj] {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) :
    ((conflictGraph G).neighborFinset e).map (Function.Embedding.subtype _) ⊆
      (endpointNeighbourCover G u v).biUnion (fun w => G.incidenceFinset w) := by
  classical
  intro f hf
  obtain ⟨f, hfn, rfl⟩ := mem_map.mp hf
  have hconf : StrongConflict G e f := ((conflictGraph G).mem_neighborFinset e f).mp hfn
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he hconf
  exact mem_biUnion.mpr ⟨w, hw, G.mem_incidenceFinset.mpr ⟨f.property, hwf⟩⟩

theorem conflict_degree_le_incidence_cover_card
    [DecidableRel (conflictGraph G).Adj] {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) :
    (conflictGraph G).degree e ≤
      ((endpointNeighbourCover G u v).biUnion (fun w => G.incidenceFinset w)).card := by
  have hc := card_le_card (conflict_neighbors_subset_incidence_cover G e he)
  simpa only [card_map, SimpleGraph.card_neighborFinset_eq_degree] using hc

/-- The finite incidence cover bounds the full conflict degree. -/
theorem conflict_degree_le_incidence_sum
    [DecidableRel (conflictGraph G).Adj] {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) :
    (conflictGraph G).degree e ≤ ∑ w ∈ endpointNeighbourCover G u v, G.degree w := by
  have hc := (conflict_degree_le_incidence_cover_card G e he).trans
    (card_biUnion_le (s := endpointNeighbourCover G u v) (t := fun w => G.incidenceFinset w))
  simpa only [SimpleGraph.card_incidenceFinset_eq_degree] using hc

theorem endpointNeighbourCover_card_le_six {u v : V} (huv : G.Adj u v)
    (hΔ : ∀ x, G.degree x ≤ 4) : (endpointNeighbourCover G u v).card ≤ 6 := by
  have hu : ((G.neighborFinset u).erase v).card + 1 = G.degree u := by
    exact card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv : ((G.neighborFinset v).erase u).card + 1 = G.degree v := by
    exact card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hc := card_union_le ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hdu := hΔ u
  have hdv := hΔ v
  dsimp [endpointNeighbourCover]
  omega

/-- In every finite simple graph of maximum degree at most four, every original
edge has at most 24 conflicts, measured in the full original graph. -/
theorem conflict_degree_le_24 [DecidableRel (conflictGraph G).Adj]
    (hΔ : ∀ x, G.degree x ≤ 4) (e : G.edgeSet) :
    (conflictGraph G).degree e ≤ 24 := by
  classical
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ a : Sym2 V, a = e.val from ⟨e.val, rfl⟩)
  have he' : e.val = s(u, v) := he.symm
  have huv : G.Adj u v := G.mem_edgeSet.mp (he' ▸ e.property)
  have hcount := conflict_degree_le_incidence_sum G e he'
  have hsum := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  have hcard := endpointNeighbourCover_card_le_six G huv hΔ
  simp only [sum_const, smul_eq_mul] at hsum
  omega

end Se20Part.Legacy
