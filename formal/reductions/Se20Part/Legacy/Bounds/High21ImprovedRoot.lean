module

public import Se20Part.Legacy.Bounds.High20Improved

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

omit [DecidableRel (conflictGraph G).Adj] in
/-- At four fully selected double tips, every neighbour outside the root
neighbourhood is another fully selected tip. This is saturation in the full G. -/
theorem fullDoubleTips_saturated_of_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hfour : (fullDoubleTips G Q r).card = 4)
    {x : V} (hx : x ∈ fullDoubleTips G Q r) :
    G.neighborFinset x \ G.neighborFinset r ⊆ fullDoubleTips G Q r := by
  let P := fullDoubleTips G Q r
  let E := P.filter (fun y => rootType G r y = rootType G r x)
  let D := P.filter (fun y => rootType G r y ≠ rootType G r x)
  have hcx := (mem_filter.mp hx).2.2.1
  have hnotN : ∀ y ∈ P, y ∉ G.neighborFinset r := by
    intro y hy hn
    obtain ⟨_, hyr, hcy, _⟩ := mem_filter.mp hy
    exact multipleTips_not_neighbor G hN
      (mem_filter.mpr ⟨mem_univ _, hyr, by omega⟩)
      ((G.mem_neighborFinset r y).mp hn)
  have hE3 : E.card ≤ 3 := by
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r x).card by omega)
    have hs : E ⊆ (G.neighborFinset a).erase r := by
      intro y hy
      obtain ⟨hyP, heq⟩ := mem_filter.mp hy
      have hay := (mem_rootType G r y a).mp (heq.symm ▸ ha)
      exact mem_erase.mpr ⟨(mem_filter.mp hyP).2.1,
        (G.mem_neighborFinset a y).mpr hay.2.symm⟩
    have hc := card_le_card hs
    have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr
      ((mem_rootType G r x a).mp ha).1.symm)
    have hd := hΔ a
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at he
    omega
  have hpart : E.card + D.card = 4 := by
    simpa only [E, D, P, hfour] using
      card_filter_add_card_filter_not (s := P) (p := fun y => rootType G r y = rootType G r x)
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < D.card by omega)
  obtain ⟨hzP, hzx⟩ := mem_filter.mp hz
  have hE2 : E.card ≤ 2 := by
    have hs : E ⊆ G.neighborFinset z \ G.neighborFinset r := by
      intro y hy
      obtain ⟨hyP, hyx⟩ := mem_filter.mp hy
      exact mem_sdiff.mpr ⟨(G.mem_neighborFinset z y).mpr
        (fullDoubleTips_adj_of_types_ne G Q hQ hN hzP hyP (by rwa [hyx])),
        hnotN y hyP⟩
    have hc := card_le_card hs
    have hr := residual_neighbors_add_type_card G r z
    have hd := hΔ z
    have ht := (mem_filter.mp hzP).2.2.1
    omega
  have hs : D ⊆ G.neighborFinset x \ G.neighborFinset r := by
    intro y hy
    obtain ⟨hyP, hyx⟩ := mem_filter.mp hy
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset x y).mpr
      (fullDoubleTips_adj_of_types_ne G Q hQ hN hx hyP (Ne.symm hyx)),
      hnotN y hyP⟩
  have hr := residual_neighbors_add_type_card G r x
  have hd := hΔ x
  have heq : D = G.neighborFinset x \ G.neighborFinset r :=
    eq_of_subset_of_card_le hs (by omega)
  exact heq ▸ filter_subset _ _

omit [DecidableRel (conflictGraph G).Adj] in
/-- Four fully selected double tips leave no room for any further selected
root tip of type at most two. -/
theorem rootTips_subset_fullDoubleTips_of_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2)
    (hfour : (fullDoubleTips G Q r).card = 4) :
    rootTips G Q r ⊆ fullDoubleTips G Q r := by
  intro y hy
  obtain ⟨_, hyr, a, haN, e, heQ, he⟩ := mem_filter.mp hy
  have ha := (G.mem_neighborFinset r a).mp haN
  have hya : a ∈ rootType G r y := (mem_rootType G r y a).mpr
    ⟨ha, (G.mem_edgeSet.mp (he ▸ e.property)).symm⟩
  have hex : ∃ x ∈ fullDoubleTips G Q r, a ∉ rootType G r x := by
    by_contra hn
    have hs : fullDoubleTips G Q r ⊆ (G.neighborFinset a).erase r := by
      intro x hx
      have hax : a ∈ rootType G r x := by
        by_contra h; exact hn ⟨x, hx, h⟩
      exact mem_erase.mpr ⟨(mem_filter.mp hx).2.1,
        (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
    have hc := card_le_card hs
    have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr ha.symm)
    have hd := hΔ a
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at he
    omega
  obtain ⟨x, hx, hxa⟩ := hex
  have hnsub : ¬ rootType G r x ⊆ rootType G r y := by
    intro hs
    have hs' : rootType G r x ⊆ (rootType G r y).erase a :=
      fun b hb => mem_erase.mpr ⟨fun h => hxa (h ▸ hb), hs hb⟩
    have hc := card_le_card hs'
    have hec := card_erase_add_one hya
    have hcx := (mem_filter.mp hx).2.2.1
    have hcy := ht y hyr
    omega
  obtain ⟨b, hbx, hby⟩ := not_subset.mp hnsub
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp ((mem_filter.mp hx).2.2.2 hbx)
  have hxy := root_selected_edges_force_adj G Q hQ hN ha
    ((mem_rootType G r x b).mp hbx).1 hby hxa e f heQ hfQ he (hf.trans Sym2.eq_swap)
  apply fullDoubleTips_saturated_of_four G hΔ Q hQ hN hfour hx
  exact mem_sdiff.mpr ⟨(G.mem_neighborFinset x y).mpr hxy.symm,
    fun h => root_edge_tip_not_neighbor G hN ha e he ((G.mem_neighborFinset r y).mp h)⟩

theorem high21_clique_card_le_seventeen_of_root_types_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) : Q.card ≤ 17 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high21_root_neighborhood_independent G hΔ Q h21 r (by omega)
  have hp := high21_multipleTips_card_le_six G hΔ Q h21 r hfull
  have htip : (rootTips G Q r).card ≤ 6 := by
    by_cases hs : (singleTips G Q r).Nonempty
    · obtain ⟨x, hx⟩ := hs
      obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
      exact rootTips_card_le_six_of_single G hΔ Q hQ hN
        ((G.mem_neighborFinset r a).mp haN) hxT e heQ he
    · exact (card_le_card (rootTips_subset_multiple_of_no_single G Q r hs)).trans hp
  have hfd := fullDoubleTips_card_le_four G hΔ Q hQ hN
  have hroot := rootEdges_card_le_tips_add_fullDoubleTips G Q r hN ht
  have ho := outer_card_le_four_of_double_types G hΔ Q hQ r hR hN ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  by_cases hf : (fullDoubleTips G Q r).card = 4
  · have hs := card_le_card
      (rootTips_subset_fullDoubleTips_of_four G hΔ Q hQ hN ht hf)
    omega
  · omega

/-- The old high21 outer bound combines with the newer high20 slot argument.
The resulting triple-type branch is stronger than the required seventeen. -/
theorem high21_clique_card_le_sixteen_of_root_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) : Q.card ≤ 16 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high21_root_neighborhood_independent G hΔ Q h21 r (by omega)
  have ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 :=
    fun y hyr hyx => high21_other_type_le_two_of_triple G hΔ Q h21 r hfull hxr hx hyr hyx
  have ho := high21_outer_card_le_two_of_root_triple G hΔ Q hQ h21 r hR hxr hx
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  by_cases hx4 : 4 ≤ (rootType G r x).card
  · have hm : multipleTips G r ⊆ {x} := by
      intro y hy
      exact mem_singleton.mpr (high21_multipleTips_eq_of_type_four G hΔ Q h21 r hfull hxr hx4 hy)
    have hs : outerEdges G Q r ⊆ edgeIncidences G (outerEdges G Q r) x := by
      intro e heo
      obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
      have hends := outerEdges_endpoints G Q r e hev.symm heo
      have hcov := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
        (card_union_le _ _)
      apply mem_filter.mpr
      refine ⟨heo, ?_⟩
      by_cases hu : 2 ≤ (rootType G r u).card
      · have heq := mem_singleton.mp (hm (mem_filter.mpr ⟨mem_univ _, hends.2.1, hu⟩))
        exact heq ▸ (hev ▸ Sym2.mem_mk_left u v)
      · have heq := mem_singleton.mp (hm (mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩))
        exact heq ▸ (hev ▸ Sym2.mem_mk_right u v)
    have hoi := card_le_card hs
    have hi := outer_incidence_add_type_card_le_degree G Q r x
    have hd := hΔ x
    have hr := root_card_add_missing_type_le_twelve G hΔ Q r hR x
    omega
  · have hr := root_card_le_ten_of_unique_triple G hΔ Q hQ hN hR (by omega) ht
    omega

/-- The four-selected-star branch of the stronger high21 bound is complete. -/
theorem high21_clique_card_le_seventeen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 17 := by
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    exact (high21_clique_card_le_sixteen_of_root_triple G hΔ Q hQ h21 r hR hxr hx).trans (by omega)
  apply high21_clique_card_le_seventeen_of_root_types_le_two G hΔ Q hQ h21 r hR
  intro x hxr
  have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
  omega

end Se20Part.Legacy
