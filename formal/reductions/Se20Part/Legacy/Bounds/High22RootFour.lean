module

public import Se20Part.Legacy.Bounds.High22Support
public import Se20Part.Legacy.Bounds.RootCounting

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high22_clique_card_le_seventeen_of_root_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) : Q.card ≤ 17 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hs : outerEdges G Q r ⊆ edgeIncidences G (outerEdges G Q r) x := by
    intro e heo
    obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hends := outerEdges_endpoints G Q r e he.symm heo
    have hcov := outer_edge_types_cover_root_labels G Q hQ r e he.symm heo
    have hc := (card_le_card hcov).trans (card_union_le _ _)
    have hp : u ∈ multipleTips G r ∨ v ∈ multipleTips G r := by
      by_cases hu : 2 ≤ (rootType G r u).card
      · exact Or.inl (mem_filter.mpr ⟨mem_univ _, hends.2.1, hu⟩)
      · exact Or.inr (mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩)
    apply mem_filter.mpr
    refine ⟨heo, ?_⟩
    rcases hp with hp | hp
    · have heq := high22_multipleTips_eq_of_triple G hΔ Q h22 r hfull hxr hx hp
      rw [← he, ← heq]
      exact Sym2.mem_mk_left _ _
    · have heq := high22_multipleTips_eq_of_triple G hΔ Q h22 r hfull hxr hx hp
      rw [← he, ← heq]
      exact Sym2.mem_mk_right _ _
  have ho := card_le_card hs
  have hi := outer_incidence_add_type_card_le_degree G Q r x
  have hd := hΔ x
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun y _ => (edgeIncidences_card_le_degree G Q y).trans (hΔ y))
  have hdr := hΔ r
  have hq := selected_edges_card_le_meeting_add_outer G Q r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem outer_endpoints_multiple_of_root_four
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2)
    (e : G.edgeSet) (heo : e ∈ outerEdges G Q r) :
    ∀ x ∈ e.val, x ∈ multipleTips G r := by
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hends := outerEdges_endpoints G Q r e he.symm heo
  have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e he.symm heo)).trans
    (card_union_le _ _)
  have hu := ht u hends.2.1
  have hv := ht v hends.2.2.1
  rw [← he, Sym2.forall_mem_pair]
  exact ⟨mem_filter.mpr ⟨mem_univ _, hends.2.1, by omega⟩,
    mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩⟩

omit [DecidableRel (conflictGraph G).Adj] in
theorem outer_incidence_sum_eq_twice
    (Q : Finset G.edgeSet) (r : V) (P : Finset V)
    (hp : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P) :
    (∑ x ∈ P, (edgeIncidences G (outerEdges G Q r) x).card) =
      2 * (outerEdges G Q r).card := by
  have hi : edgesInside G (outerEdges G Q r) P = outerEdges G Q r := by
    apply filter_eq_self.mpr
    exact hp
  have hm : edgesMeeting G (outerEdges G Q r) P = outerEdges G Q r := by
    apply filter_eq_self.mpr
    intro e he
    obtain ⟨u, v, huv⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hu : u ∈ e.val := huv ▸ Sym2.mem_mk_left u v
    exact ⟨u, hp e he u hu, hu⟩
  have hc := incidence_sum_eq_meeting_add_inside G (outerEdges G Q r) P
  rw [hi, hm] at hc
  omega

theorem high22_outer_card_le_four_of_root_types_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) :
    (outerEdges G Q r).card ≤ 4 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hp := high22_multipleTips_card_le_four G hΔ Q h22 r hfull
  have hi := outer_incidence_sum_eq_twice G Q r (multipleTips G r)
    (outer_endpoints_multiple_of_root_four G Q hQ r hR ht)
  have hs : ∀ x ∈ multipleTips G r, (edgeIncidences G (outerEdges G Q r) x).card ≤ 2 := by
    intro x hx
    have hb := outer_incidence_add_type_card_le_degree G Q r x
    have hd := hΔ x
    have hc := (mem_filter.mp hx).2.2
    omega
  have hsum := sum_le_sum hs
  simp only [sum_const, smul_eq_mul] at hsum
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem rootEdges_card_le_tips_add_multiple
    (Q : Finset G.edgeSet) (r : V)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) :
    (rootEdges G Q r).card ≤ (rootTips G Q r).card +
      ((rootTips G Q r).filter (fun x => x ∈ multipleTips G r)).card := by
  have hs : ∀ x ∈ rootTips G Q r, (rootType G r x).card ≤
      1 + if x ∈ multipleTips G r then 1 else 0 := by
    intro x hx
    have hxr := (mem_filter.mp hx).2.1
    have hc := ht x hxr
    by_cases hp : x ∈ multipleTips G r
    · simp only [hp, ite_true]; omega
    · have hn : ¬ 2 ≤ (rootType G r x).card := fun h => hp (mem_filter.mpr ⟨mem_univ _, hxr, h⟩)
      simp only [hp, ite_false]; omega
  have hc := (rootEdges_card_le_tip_weight G Q r).trans (sum_le_sum hs)
  simpa only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, ← sum_filter, ← card_eq_sum_ones] using hc

omit [DecidableRel (conflictGraph G).Adj] in
theorem rootEdges_card_le_twice_multiple_of_no_single
    (Q : Finset G.edgeSet) (r : V)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2)
    (hn : ¬ (singleTips G Q r).Nonempty) :
    (rootEdges G Q r).card ≤ 2 * (multipleTips G r).card := by
  have hs : rootTips G Q r ⊆ multipleTips G r := by
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
  have hc := card_le_card hs
  have hsum := sum_le_sum (s := rootTips G Q r)
    (fun x hx => ht x (mem_filter.mp hx).2.1)
  have he := rootEdges_card_le_tip_weight G Q r
  simp only [sum_const, smul_eq_mul] at hsum
  omega

theorem high22_outer_degree_eq_two_of_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2)
    (ho : (outerEdges G Q r).card = 4) {y : V} (hy : y ∈ multipleTips G r) :
    (edgeIncidences G (outerEdges G Q r) y).card = 2 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hp := high22_multipleTips_card_le_four G hΔ Q h22 r hfull
  have hi := outer_incidence_sum_eq_twice G Q r (multipleTips G r)
    (outer_endpoints_multiple_of_root_four G Q hQ r hR ht)
  have hbound : ∀ x ∈ multipleTips G r, (edgeIncidences G (outerEdges G Q r) x).card ≤ 2 := by
    intro x hx
    have hb := outer_incidence_add_type_card_le_degree G Q r x
    have hd := hΔ x
    have hc := (mem_filter.mp hx).2.2
    omega
  have hyb := hbound y hy
  have he := sum_erase_add (multipleTips G r)
    (fun x => (edgeIncidences G (outerEdges G Q r) x).card) hy
  have hce := card_erase_add_one hy
  have hsum := sum_le_sum (s := (multipleTips G r).erase y)
    (fun x hx => hbound x (mem_erase.mp hx).2)
  simp only [sum_const, smul_eq_mul] at hsum
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem outer_saturated_neighbors
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V) (P : Finset V)
    (hp : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P)
    {y : V} (hsat : 4 ≤ (edgeIncidences G (outerEdges G Q r) y).card + (rootType G r y).card)
    {x : V} (hxy : G.Adj y x) : G.Adj r x ∨ x ∈ P := by
  have hsub : rootLabels G (outerEdges G Q r) y ∪ rootType G r y ⊆ G.neighborFinset y := by
    apply union_subset (rootLabels_subset_neighbors G _ y)
    intro a ha
    exact (G.mem_neighborFinset y a).mpr ((mem_rootType G r y a).mp ha).2
  have hdis : Disjoint (rootLabels G (outerEdges G Q r) y) (rootType G r y) := by
    apply disjoint_left.mpr
    intro a ha ht
    obtain ⟨_, e, heo, he⟩ := mem_filter.mp ha
    exact (mem_filter.mp heo).2.2 a (he.symm ▸ Sym2.mem_mk_right y a)
      ((mem_rootType G r y a).mp ht).1
  have heq : rootLabels G (outerEdges G Q r) y ∪ rootType G r y = G.neighborFinset y := by
    apply eq_of_subset_of_card_le hsub
    rw [card_union_of_disjoint hdis, rootLabels_card, SimpleGraph.card_neighborFinset_eq_degree]
    exact (hΔ y).trans hsat
  have hx : x ∈ rootLabels G (outerEdges G Q r) y ∪ rootType G r y :=
    heq.symm ▸ (G.mem_neighborFinset y x).mpr hxy
  rcases mem_union.mp hx with hx | hx
  · obtain ⟨_, e, heo, he⟩ := mem_filter.mp hx
    exact Or.inr (hp e heo x (he.symm ▸ Sym2.mem_mk_right y x))
  · exact Or.inl ((mem_rootType G r y x).mp hx).1

theorem high22_active_multiple_card_le_two_of_outer_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2)
    (ho : (outerEdges G Q r).card = 4)
    {a x : V} (ha : G.Adj r a) (hxT : rootType G r x = {a})
    (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(a, x)) :
    ((rootTips G Q r).filter (fun y => y ∈ multipleTips G r)).card ≤ 2 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high22_root_neighborhood_independent G hΔ Q h22 r (by omega)
  have hnx := root_edge_tip_not_neighbor G hN ha e he
  have hxp : x ∉ multipleTips G r := by
    intro hp
    have hc := (mem_filter.mp hp).2.2
    simp only [hxT, card_singleton] at hc
    omega
  have hs : (rootTips G Q r).filter (fun y => y ∈ multipleTips G r) ⊆
      (multipleTips G r).filter (fun y => a ∈ rootType G r y) := by
    intro y hy
    obtain ⟨hyt, hyp⟩ := mem_filter.mp hy
    apply mem_filter.mpr
    refine ⟨hyp, ?_⟩
    by_contra hna
    have hxy := rootTips_adj_of_single G Q hQ hN ha hxT e heQ he hyt hna
    have hdy := high22_outer_degree_eq_two_of_four G hΔ Q hQ h22 r hR ht ho hyp
    have hty := (mem_filter.mp hyp).2.2
    have hres := outer_saturated_neighbors G hΔ Q r (multipleTips G r)
      (outer_endpoints_multiple_of_root_four G Q hQ r hR ht) (by omega) hxy.symm
    exact hres.elim hnx hxp
  exact (card_le_card hs).trans (high22_root_label_multiple_card_le_two G hΔ Q h22
    (hfull.symm ▸ (G.mem_neighborFinset r a).mpr ha))

theorem high22_clique_card_le_seventeen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 17 := by
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    exact high22_clique_card_le_seventeen_of_root_triple G hΔ Q hQ h22 r hR hxr hx
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
    intro x hxr
    have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
    omega
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hp := high22_multipleTips_card_le_four G hΔ Q h22 r hfull
  have ho := high22_outer_card_le_four_of_root_types_le_two G hΔ Q hQ h22 r hR ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card G Q r, hR]
  have hc := clique_card_le_star_root_outer G Q r
  by_cases hsingle : (singleTips G Q r).Nonempty
  · obtain ⟨x, hx⟩ := hsingle
    obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
    have ha := (G.mem_neighborFinset r a).mp haN
    have hN := high22_root_neighborhood_independent G hΔ Q h22 r (by omega)
    have htip := rootTips_card_le_six_of_single G hΔ Q hQ hN ha hxT e heQ he
    have hroot := rootEdges_card_le_tips_add_multiple G Q r ht
    have hsub : (rootTips G Q r).filter (fun y => y ∈ multipleTips G r) ⊆ multipleTips G r := by
      intro y hy
      exact (mem_filter.mp hy).2
    have hact := card_le_card hsub
    by_contra hn
    have hfour : (outerEdges G Q r).card = 4 := by omega
    have htwo := high22_active_multiple_card_le_two_of_outer_four G hΔ Q hQ h22 r hR ht hfour
      ha hxT e heQ he
    omega
  · have hroot := rootEdges_card_le_twice_multiple_of_no_single G Q r ht hsingle
    omega

end Se20Part.Legacy
