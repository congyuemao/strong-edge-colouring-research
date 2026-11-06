module

public import Se20Part.Legacy.Packing195Thresholds

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Restricting the support to vertices outside the root neighbourhood removes
the need to assume that neighbourhood is independent. -/
theorem outer_card_le_four_of_external_double_types
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → ¬ G.Adj r x → (rootType G r x).card ≤ 2) :
    (outerEdges G Q r).card ≤ 4 := by
  let P := univ.filter (fun x => x ≠ r ∧ ¬ G.Adj r x ∧ 2 ≤ (rootType G r x).card)
  have hP : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P := by
    intro e heo
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have he := outerEdges_endpoints G Q r e hev.symm heo
    have hu := ht u he.2.1 he.2.2.2.1
    have hv := ht v he.2.2.1 he.2.2.2.2
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
      (card_union_le _ _)
    rw [← hev, Sym2.forall_mem_pair]
    exact ⟨mem_filter.mpr ⟨mem_univ _, he.2.1, he.2.2.2.1, by omega⟩,
      mem_filter.mpr ⟨mem_univ _, he.2.2.1, he.2.2.2.2, by omega⟩⟩
  have hd : ∀ x ∈ P, (G.neighborFinset x ∩ P).card ≤ 2 := by
    intro x hx
    have hs : G.neighborFinset x ∩ P ⊆ G.neighborFinset x \ G.neighborFinset r := by
      intro y hy
      obtain ⟨hyN, hyP⟩ := mem_inter.mp hy
      exact mem_sdiff.mpr ⟨hyN, fun h => (mem_filter.mp hyP).2.2.1
        ((G.mem_neighborFinset r y).mp h)⟩
    have hc := card_le_card hs
    have hi := residual_neighbors_add_type_card G r x
    have hd := hΔ x
    have ht := (mem_filter.mp hx).2.2.2
    omega
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootLabels G Q r).card by omega)
  let L := P.filter (fun x => a ∈ rootType G r x)
  apply degree_two_clique_card_le_four_of_selected_bipartition G (outerEdges G Q r)
    (fun e he f hf hef => hQ (mem_filter.mp he).1 (mem_filter.mp hf).1 hef) P hP hd L
  intro e heo
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huP := hP e heo u (hev ▸ Sym2.mem_mk_left u v)
  have hvP := hP e heo v (hev ▸ Sym2.mem_mk_right u v)
  have hu := ht u (mem_filter.mp huP).2.1 (mem_filter.mp huP).2.2.1
  have hv := ht v (mem_filter.mp hvP).2.1 (mem_filter.mp hvP).2.2.1
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo
  have hc := card_le_card hcov
  have hi := card_union_add_card_inter (rootType G r u) (rootType G r v)
  have hdis : Disjoint (rootType G r u) (rootType G r v) := by
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    omega
  have hex : ∃ w ∈ L, w ∈ e.val := by
    rcases mem_union.mp (hcov ha) with hau | hav
    · exact ⟨u, mem_filter.mpr ⟨huP, hau⟩, hev ▸ Sym2.mem_mk_left u v⟩
    · exact ⟨v, mem_filter.mpr ⟨hvP, hav⟩, hev ▸ Sym2.mem_mk_right u v⟩
  have hn : ¬ ∀ w ∈ e.val, w ∈ L := by
    intro hall
    have huL := hall u (hev ▸ Sym2.mem_mk_left u v)
    have hvL := hall v (hev ▸ Sym2.mem_mk_right u v)
    exact disjoint_left.mp hdis (mem_filter.mp huL).2 (mem_filter.mp hvL).2
  rw [edge_endpoint_count]
  simp only [hex, hn, ite_true, ite_false, add_zero]

variable [DecidableRel (conflictGraph G).Adj]

theorem clique_card_le_conflict_degree_add_one
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {e : G.edgeSet} (he : e ∈ Q) : Q.card ≤ (conflictGraph G).degree e + 1 := by
  have hs : Q.erase e ⊆ (conflictGraph G).neighborFinset e := by
    intro f hf
    exact ((conflictGraph G).mem_neighborFinset e f).mpr
      (hQ he (mem_erase.mp hf).2 (mem_erase.mp hf).1.symm)
  have hc := card_le_card hs
  have hec := card_erase_add_one he
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

theorem high19_triangle_cover_inside_card_le_one
    (hΔ : ∀ x, G.degree x ≤ 4) {u v w : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h19 : 19 ≤ (conflictGraph G).degree e)
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    (edgesInside G univ (endpointNeighbourCover G u v)).card ≤ 1 := by
  have hc := conflict_degree_add_inside_le_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun z _ => hΔ z)
  have hcard := endpointNeighbourCover_card_le_five_of_triangle G hΔ
    (G.mem_edgeSet.mp (he ▸ e.property)) huw hvw
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem high19_triangle_root_type_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) {r a b x : V} (e : G.edgeSet)
    (he : e.val = s(r, a)) (h19 : 19 ≤ (conflictGraph G).degree e)
    (hrb : G.Adj r b) (hab : G.Adj a b) (hxr : x ≠ r)
    (hax : a ∈ rootType G r x) : (rootType G r x).card ≤ 2 := by
  have hs : ((rootType G r x).erase a).card ≤
      (edgesInside G univ (endpointNeighbourCover G r a)).card := by
    apply card_le_via_relation _ _ (fun c f => f.val = s(c, x))
    · intro c hc
      obtain ⟨hca, hcT⟩ := mem_erase.mp hc
      have hcx := (mem_rootType G r x c).mp hcT
      have hxa := (mem_rootType G r x a).mp hax
      refine ⟨⟨s(c, x), hcx.2.symm⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact Sym2.forall_mem_pair.mpr
        ⟨mem_union_left _ (mem_erase.mpr ⟨hca, (G.mem_neighborFinset r c).mpr hcx.1⟩),
         mem_union_right _ (mem_erase.mpr ⟨hxr, (G.mem_neighborFinset a x).mpr hxa.2.symm⟩)⟩
    · intro c hc d hd f hcf hdf
      rcases Sym2.eq_iff.mp (hcf.symm.trans hdf) with h | h
      · exact h.1
      · exact h.1.trans h.2
  have hb := high19_triangle_cover_inside_card_le_one G hΔ e he h19 hrb hab
  have hec := card_erase_add_one hax
  omega

/-- A twenty-clique has an independent original neighbourhood at every
vertex incident with four selected edges. No degree threshold is assumed. -/
theorem twenty_clique_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb _ hab
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  obtain ⟨_, ea, heaQ, hea⟩ := mem_filter.mp (hfull.symm ▸ (G.mem_neighborFinset r a).mpr ha)
  obtain ⟨_, eb, hebQ, heb⟩ := mem_filter.mp (hfull.symm ▸ (G.mem_neighborFinset r b).mpr hb)
  have h19a : 19 ≤ (conflictGraph G).degree ea := by
    have hc := clique_card_le_conflict_degree_add_one G Q hQ heaQ
    omega
  have h19b : 19 ≤ (conflictGraph G).degree eb := by
    have hc := clique_card_le_conflict_degree_add_one G Q hQ hebQ
    omega
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
    intro x hxr
    by_cases hax : a ∈ rootType G r x
    · exact high19_triangle_root_type_card_le_two G hΔ ea hea h19a hb hab hxr hax
    by_cases hbx : b ∈ rootType G r x
    · exact high19_triangle_root_type_card_le_two G hΔ eb heb h19b ha hab.symm hxr hbx
    have hs : rootType G r x ⊆ ((G.neighborFinset r).erase a).erase b := by
      intro c hc
      exact mem_erase.mpr ⟨fun h => hbx (h ▸ hc), mem_erase.mpr
        ⟨fun h => hax (h ▸ hc), filter_subset _ _ hc⟩⟩
    have hc := card_le_card hs
    have hca := card_erase_add_one ((G.mem_neighborFinset r a).mpr ha)
    have hcb := card_erase_add_one (mem_erase.mpr
      ⟨hab.ne.symm, (G.mem_neighborFinset r b).mpr hb⟩)
    have hd := hΔ r
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
    omega
  have ho := outer_card_le_four_of_external_double_types G hΔ Q hQ r hR
    (fun x hxr _ => ht x hxr)
  let f : G.edgeSet := ⟨s(a, b), hab⟩
  have hf : f ∈ edgesInside G univ (G.neighborFinset r) := mem_filter.mpr
    ⟨mem_univ _, Sym2.forall_mem_pair.mpr
      ⟨(G.mem_neighborFinset r a).mpr ha, (G.mem_neighborFinset r b).mpr hb⟩⟩
  have hi := card_pos.mpr ⟨f, hf⟩
  have hm := incidence_sum_eq_meeting_add_inside G univ (G.neighborFinset r)
  simp only [edgeIncidences_univ_card] at hm
  have hs := sum_le_sum (s := G.neighborFinset r) (fun x _ => hΔ x)
  have hsub : edgesMeeting G Q (G.neighborFinset r) ⊆ edgesMeeting G univ (G.neighborFinset r) :=
    fun _ he => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp he).2⟩
  have hc := card_le_card hsub
  have hqbound := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem twenty_clique_exists_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card) :
    ∃ r, (rootLabels G Q r).card = 4 := by
  by_contra hn
  have hd : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hx : (edgeIncidences G Q x).card ≠ 4 := fun h =>
      hn ⟨x, by rw [rootLabels_card]; exact h⟩
    omega
  have hc := clique_card_le_seventeen_of_support_degree_le_three G hΔ Q hQ hd
  omega

end Se20Part.Legacy
