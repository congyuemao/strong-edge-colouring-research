module

public import Se20Part.Legacy.Bounds.High23Four

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem meeting_edges_subset_root_single_double (Q : Finset G.edgeSet) (r : V) :
    edgesMeeting G Q (G.neighborFinset r) ⊆
      edgeIncidences G Q r ∪ (singleRootEdges G Q r ∪ doubleRootEdges G Q r) := by
  classical
  intro e he
  obtain ⟨heQ, a, haN, hae⟩ := mem_filter.mp he
  by_cases hre : r ∈ e.val
  · exact mem_union_left _ (mem_filter.mpr ⟨heQ, hre⟩)
  obtain ⟨x, hex⟩ := Sym2.mem_iff_exists.mp hae
  have hxr : x ≠ r := by
    intro h
    apply hre
    rw [hex, h]
    exact Sym2.mem_mk_right _ _
  have hax : G.Adj a x := G.mem_edgeSet.mp (hex ▸ e.property)
  have haT : a ∈ rootType G r x := (mem_rootType G r x a).mpr
    ⟨(G.mem_neighborFinset r a).mp haN, hax.symm⟩
  by_cases hsmall : (rootType G r x).card ≤ 1
  · have hx : rootType G r x = {a} := eq_singleton_iff_unique_mem.mpr
      ⟨haT, fun b hb => card_le_one.mp hsmall b hb a haT⟩
    exact mem_union_right _ (mem_union_left _
      (mem_filter.mpr ⟨heQ, a, x, haN, hxr, hex, hx⟩))
  · exact mem_union_right _ (mem_union_right _
      (mem_filter.mpr ⟨heQ, a, x, haN, hxr, hex, by omega⟩))

variable [DecidableRel (conflictGraph G).Adj]

theorem high23_meeting_card_le_fourteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    (edgesMeeting G Q (G.neighborFinset r)).card ≤ 14 := by
  have hfull : rootLabels G Q r = G.neighborFinset r := by
    apply eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
    simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r
  have hstar : (edgeIncidences G Q r).card = 4 := by
    rw [← rootLabels_card G Q r, hR]
  have hsingle := (singleRootEdges_card_le_singleTips G Q r).trans
    (high23_singleTips_card_le_six G hΔ Q hQ h23 r (by omega))
  have hdouble := high23_doubleRootEdges_card_le_four G hΔ Q h23 r hfull
  have hc := card_le_card (meeting_edges_subset_root_single_double G Q r)
  have h1 := card_union_le (edgeIncidences G Q r)
    (singleRootEdges G Q r ∪ doubleRootEdges G Q r)
  have h2 := card_union_le (singleRootEdges G Q r) (doubleRootEdges G Q r)
  omega

theorem high23_clique_card_le_sixteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 16 := by
  have hc := selected_edges_card_le_meeting_add_outer G Q r
  have hm := high23_meeting_card_le_fourteen_of_root_four G hΔ Q hQ h23 r hR
  have ho := high23_outer_edges_card_le_two G hΔ Q hQ h23 r (by omega)
  omega

/-- Universal high23 clique bound in the full original conflict graph.
Only the original maximum degree, clique condition, and full-degree lower
bound are mathematical assumptions. -/
theorem high23_clique_card_le_sixteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e) : Q.card ≤ 16 := by
  classical
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high23_clique_card_le_sixteen_of_root_four G hΔ Q hQ h23 r
      (by rw [rootLabels_card G Q r]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  by_cases htwo : ∀ x, (edgeIncidences G Q x).card ≤ 2
  · exact (clique_card_le_thirteen_of_support_degree_le_two G hΔ Q hQ htwo).trans (by omega)
  obtain ⟨r, hr⟩ := not_forall.mp htwo
  have hR : 3 ≤ (rootLabels G Q r).card := by
    rw [rootLabels_card G Q r]
    omega
  exact (high23_clique_card_le_fourteen_of_support_degree_le_three G hΔ Q hQ h23 hthree r hR).trans
    (by omega)

end Se20Part.Legacy
