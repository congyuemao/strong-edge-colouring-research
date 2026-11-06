module

public import Se20Part.Legacy.Bounds.High23

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- With all four root labels selected, both endpoints of an outer edge have
two selected root labels. Each is therefore incident to every outer edge. -/
theorem high23_outer_edges_card_le_one_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    (outerEdges G Q r).card ≤ 1 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hincident (p : V) (hpr : p ≠ r) (hp : 2 ≤ (rootType G r p).card)
      (f : G.edgeSet) (hf : f ∈ outerEdges G Q r) : p ∈ f.val := by
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < (rootType G r p).card by omega)
    have haR : a ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ ha
    have hbR : b ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ hb
    exact high23_outer_edges_incident_double_root G hΔ Q hQ h23 r (by omega)
      hpr haR hbR hab ha hb f hf
  apply card_le_one.mpr
  intro e he f hf
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hends := outerEdges_endpoints G Q r e hev.symm he
  have hu := high23_root_type_card_le_two G hΔ Q h23 r (by omega) hends.2.1
  have hv := high23_root_type_card_le_two G hΔ Q h23 r (by omega) hends.2.2.1
  have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm he)).trans
    (card_union_le _ _)
  have huv : u ≠ v := (G.mem_edgeSet.mp (hev ▸ e.property)).ne
  exact Subtype.ext (Sym2.eq_of_ne_mem huv
    (hev ▸ Sym2.mem_mk_left u v) (hev ▸ Sym2.mem_mk_right u v)
    (hincident u hends.2.1 (by omega) f hf) (hincident v hends.2.2.1 (by omega) f hf))

theorem high23_clique_card_le_fifteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 15 := by
  have hc := selected_edges_card_le_meeting_add_outer G Q r
  have hm := high23_meeting_card_le_fourteen_of_root_four G hΔ Q hQ h23 r hR
  have ho := high23_outer_edges_card_le_one_of_root_four G hΔ Q hQ h23 r hR
  omega

/-- Unconditional high23 improvement, with conflict degree in the full G. -/
theorem high23_clique_card_le_fifteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e) : Q.card ≤ 15 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high23_clique_card_le_fifteen_of_root_four G hΔ Q hQ h23 r
      (by rw [rootLabels_card G Q r]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  by_cases htwo : ∀ x, (edgeIncidences G Q x).card ≤ 2
  · exact (clique_card_le_thirteen_of_support_degree_le_two G hΔ Q hQ htwo).trans (by omega)
  obtain ⟨r, hr⟩ := not_forall.mp htwo
  have hR : 3 ≤ (rootLabels G Q r).card := by rw [rootLabels_card]; omega
  exact (high23_clique_card_le_fourteen_of_support_degree_le_three G hΔ Q hQ h23 hthree r hR).trans
    (by omega)

end Se20Part.Legacy
