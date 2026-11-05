module

public import Se20Part.Legacy.Bounds.High22Heavy

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem root_outer_incidence_add_le (Q : Finset G.edgeSet) (r x : V) :
    (edgeIncidences G (rootEdges G Q r) x).card +
      (edgeIncidences G (outerEdges G Q r) x).card ≤ (edgeIncidences G Q x).card := by
  have hs : edgeIncidences G (rootEdges G Q r) x ∪ edgeIncidences G (outerEdges G Q r) x ⊆
      edgeIncidences G Q x := by
    intro e he
    rcases mem_union.mp he with he | he
    · obtain ⟨her, hxe⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp her).1).1, hxe⟩
    · obtain ⟨heo, hxe⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_filter.mp heo).1, hxe⟩
  have hd : Disjoint (edgeIncidences G (rootEdges G Q r) x) (edgeIncidences G (outerEdges G Q r) x) := by
    apply disjoint_left.mpr
    intro e her heo
    obtain ⟨_, a, haN, hae⟩ := mem_filter.mp (mem_filter.mp (mem_filter.mp her).1).1
    exact (mem_filter.mp (mem_filter.mp heo).1).2.2 a hae ((G.mem_neighborFinset r a).mp haN)
  have hc := card_le_card hs
  rwa [card_union_of_disjoint hd] at hc

theorem root_incidence_at_tip_le_type
    (Q : Finset G.edgeSet) (r : V) (hN : G.IsIndepSet (G.neighborSet r))
    {x : V} (hx : x ∈ rootTips G Q r) :
    (edgeIncidences G (rootEdges G Q r) x).card ≤ (rootType G r x).card := by
  obtain ⟨_, _, b, hbN, f, _, hf⟩ := mem_filter.mp hx
  have hnx := root_edge_tip_not_neighbor G hN ((G.mem_neighborFinset r b).mp hbN) f hf
  apply card_le_via_relation _ _ (fun e y => e.val = s(x, y))
  · intro e he
    obtain ⟨her, hxe⟩ := mem_filter.mp he
    obtain ⟨_, a, haN, hae⟩ := mem_filter.mp (mem_filter.mp her).1
    obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
    have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
    have hay : a = y := by
      rw [hey, Sym2.mem_iff] at hae
      rcases hae with h | h
      · exact (hnx (h ▸ (G.mem_neighborFinset r a).mp haN)).elim
      · exact h
    exact ⟨y, (mem_rootType G r x y).mpr ⟨hay ▸ (G.mem_neighborFinset r a).mp haN, hxy⟩, hey⟩
  · intro e he f hf y hey hfy
    exact Subtype.ext (hey.trans hfy.symm)

theorem rootEdges_card_le_tips_of_incidence_le_one
    (Q : Finset G.edgeSet) (r : V)
    (hd : ∀ x ∈ rootTips G Q r, (edgeIncidences G (rootEdges G Q r) x).card ≤ 1) :
    (rootEdges G Q r).card ≤ (rootTips G Q r).card := by
  apply card_le_via_relation _ _ (fun e x => x ∈ rootTips G Q r ∧ x ∈ e.val)
  · intro e he
    obtain ⟨hem, hr⟩ := mem_filter.mp he
    obtain ⟨heQ, a, ha, hae⟩ := mem_filter.mp hem
    obtain ⟨x, hex⟩ := Sym2.mem_iff_exists.mp hae
    have hxr : x ≠ r := by
      intro h
      exact hr (hex.symm ▸ h ▸ Sym2.mem_mk_right a x)
    have hx : x ∈ rootTips G Q r := mem_filter.mpr ⟨mem_univ _, hxr, a, ha, e, heQ, hex⟩
    exact ⟨x, hx, hx, hex.symm ▸ Sym2.mem_mk_right a x⟩
  · intro e he f hf x hxe hxf
    exact card_le_one.mp (hd x hxe.1) e (mem_filter.mpr ⟨he, hxe.2⟩)
      f (mem_filter.mpr ⟨hf, hxf.2⟩)

theorem rootTips_subset_multiple_of_no_single
    (Q : Finset G.edgeSet) (r : V) (hn : ¬ (singleTips G Q r).Nonempty) :
    rootTips G Q r ⊆ multipleTips G r := by
  intro x hx
  obtain ⟨_, hxr, a, haN, e, heQ, he⟩ := mem_filter.mp hx
  apply mem_filter.mpr
  refine ⟨mem_univ _, hxr, ?_⟩
  by_contra hncard
  have haT : a ∈ rootType G r x := (mem_rootType G r x a).mpr
    ⟨(G.mem_neighborFinset r a).mp haN, (G.mem_edgeSet.mp (he ▸ e.property)).symm⟩
  have hxT : rootType G r x = {a} := eq_singleton_iff_unique_mem.mpr
    ⟨haT, fun b hb => card_le_one.mp (by omega) b hb a haT⟩
  exact hn ⟨x, mem_filter.mpr ⟨mem_univ _, hxr, a, haN, hxT, e, heQ, he⟩⟩

variable [DecidableRel (conflictGraph G).Adj]

theorem high22_clique_card_le_seventeen_of_support_degree_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 3) : Q.card ≤ 17 := by
  by_cases htwo : ∀ x, (edgeIncidences G Q x).card ≤ 2
  · exact (clique_card_le_thirteen_of_support_degree_le_two G hΔ Q hQ htwo).trans (by omega)
  obtain ⟨r, hr⟩ := not_forall.mp htwo
  have hstar : (edgeIncidences G Q r).card = 3 := by have := hQdeg r; omega
  have hR : (rootLabels G Q r).card = 3 := by rw [rootLabels_card, hstar]
  have hN := high22_root_neighborhood_independent G hΔ Q h22 r (by omega)
  by_contra hn
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r) (fun x _ => hQdeg x)
  have hdr := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have hcover := selected_edges_card_le_meeting_add_outer G Q r
  have hob := high22_outer_card_le_six_of_root_three G hΔ Q hQ h22 r hR
  have ho : (outerEdges G Q r).card = 6 := by omega
  obtain ⟨hp, hpd⟩ := high22_heavy_card_and_degree_of_outer_six G hΔ Q hQ h22 r hR ho
  have hmh := high22_multiple_subset_heavy_of_three G hΔ Q h22 r hR hp
  have hrd : ∀ x ∈ rootTips G Q r, (edgeIncidences G (rootEdges G Q r) x).card ≤ 1 := by
    intro x hx
    by_cases hxm : x ∈ multipleTips G r
    · have hd := hpd x (hmh hxm)
      have hi := root_outer_incidence_add_le G Q r x
      have hq := hQdeg x
      omega
    · have hxr := (mem_filter.mp hx).2.1
      have hsmall : (rootType G r x).card ≤ 1 := by
        have hh : ¬ 2 ≤ (rootType G r x).card := fun h => hxm (mem_filter.mpr ⟨mem_univ _, hxr, h⟩)
        omega
      exact (root_incidence_at_tip_le_type G Q r hN hx).trans hsmall
  have hroot := rootEdges_card_le_tips_of_incidence_le_one G Q r hrd
  have hc := clique_card_le_star_root_outer G Q r
  by_cases hs : (singleTips G Q r).Nonempty
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
    have ht := rootTips_card_le_six_of_single G hΔ Q hQ hN ((G.mem_neighborFinset r a).mp haN)
      hxT e heQ he
    omega
  · have ht := card_le_card ((rootTips_subset_multiple_of_no_single G Q r hs).trans hmh)
    omega

end Se20Part.Legacy
