module

public import Se20Part.Legacy.Bounds.High21Double
public import Se20Part.Legacy.Bounds.High21LargeType

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem outer_card_le_four_of_double_types
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) :
    (outerEdges G Q r).card ≤ 4 := by
  have hP := outer_endpoints_multiple_of_root_four G Q hQ r hR ht
  have hd : ∀ x ∈ multipleTips G r, (G.neighborFinset x ∩ multipleTips G r).card ≤ 2 := by
    intro x hx
    have hs : G.neighborFinset x ∩ multipleTips G r ⊆ G.neighborFinset x \ G.neighborFinset r := by
      intro y hy
      obtain ⟨hyN, hyP⟩ := mem_inter.mp hy
      exact mem_sdiff.mpr ⟨hyN, fun h => multipleTips_not_neighbor G hN hyP
        ((G.mem_neighborFinset r y).mp h)⟩
    have hc := card_le_card hs
    have hi := residual_neighbors_add_type_card G r x
    have hd := hΔ x
    have ht := (mem_filter.mp hx).2.2
    omega
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootLabels G Q r).card by omega)
  let L := (multipleTips G r).filter (fun x => a ∈ rootType G r x)
  apply degree_two_clique_card_le_four_of_selected_bipartition G (outerEdges G Q r)
    (fun e he f hf hef => hQ (mem_filter.mp he).1 (mem_filter.mp hf).1 hef)
    (multipleTips G r) hP hd L
  intro e heo
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huP := hP e heo u (hev ▸ Sym2.mem_mk_left u v)
  have hvP := hP e heo v (hev ▸ Sym2.mem_mk_right u v)
  have hu := ht u (mem_filter.mp huP).2.1
  have hv := ht v (mem_filter.mp hvP).2.1
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

theorem rootLabels_rootEdges_at_tip_subset_type
    (Q : Finset G.edgeSet) {r x : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hx : x ∈ rootTips G Q r) : rootLabels G (rootEdges G Q r) x ⊆ rootType G r x := by
  obtain ⟨_, _, a, haN, f, _, hf⟩ := mem_filter.mp hx
  have hnx := root_edge_tip_not_neighbor G hN ((G.mem_neighborFinset r a).mp haN) f hf
  intro b hb
  obtain ⟨hbN, e, her, he⟩ := mem_filter.mp hb
  obtain ⟨_, c, hcN, hce⟩ := mem_filter.mp (mem_filter.mp her).1
  have hcb : c = b := by
    rw [he, Sym2.mem_iff] at hce
    exact hce.elim (fun h => (hnx (h ▸ (G.mem_neighborFinset r c).mp hcN)).elim) id
  exact (mem_rootType G r x b).mpr
    ⟨hcb ▸ (G.mem_neighborFinset r c).mp hcN, (G.mem_neighborFinset x b).mp hbN⟩

theorem root_incidence_two_mem_fullDoubleTips
    (Q : Finset G.edgeSet) {r x : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ht : (rootType G r x).card ≤ 2) (hx : x ∈ rootTips G Q r)
    (hd : (edgeIncidences G (rootEdges G Q r) x).card = 2) :
    x ∈ fullDoubleTips G Q r := by
  have hs := rootLabels_rootEdges_at_tip_subset_type G Q hN hx
  have hc : (rootLabels G (rootEdges G Q r) x).card = 2 := by rw [rootLabels_card, hd]
  have heq : rootLabels G (rootEdges G Q r) x = rootType G r x :=
    eq_of_subset_of_card_le hs (by omega)
  apply mem_filter.mpr
  refine ⟨mem_univ _, (mem_filter.mp hx).2.1, ?_, ?_⟩
  · rw [← heq, hc]
  · intro a ha
    obtain ⟨haN, e, he, hea⟩ := mem_filter.mp (heq.symm ▸ ha)
    exact mem_filter.mpr ⟨haN, e, (mem_filter.mp (mem_filter.mp he).1).1, hea⟩

theorem rootEdges_card_le_tips_add_fullDoubleTips
    (Q : Finset G.edgeSet) (r : V) (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) :
    (rootEdges G Q r).card ≤ (rootTips G Q r).card + (fullDoubleTips G Q r).card := by
  have hm : edgesMeeting G (rootEdges G Q r) (rootTips G Q r) = rootEdges G Q r := by
    apply filter_eq_self.mpr
    intro e he
    obtain ⟨hem, hr⟩ := mem_filter.mp he
    obtain ⟨heQ, a, ha, hae⟩ := mem_filter.mp hem
    obtain ⟨x, hex⟩ := Sym2.mem_iff_exists.mp hae
    have hxr : x ≠ r := fun h => hr (hex.symm ▸ h ▸ Sym2.mem_mk_right a x)
    exact ⟨x, mem_filter.mpr ⟨mem_univ _, hxr, a, ha, e, heQ, hex⟩,
      hex.symm ▸ Sym2.mem_mk_right a x⟩
  have hi := incidence_sum_eq_meeting_add_inside G (rootEdges G Q r) (rootTips G Q r)
  rw [hm] at hi
  have hs : ∀ x ∈ rootTips G Q r, (edgeIncidences G (rootEdges G Q r) x).card ≤
      1 + if x ∈ fullDoubleTips G Q r then 1 else 0 := by
    intro x hx
    have ht2 := ht x (mem_filter.mp hx).2.1
    have hd := (root_incidence_at_tip_le_type G Q r hN hx).trans ht2
    by_cases hf : x ∈ fullDoubleTips G Q r
    · simp only [hf, ite_true]; omega
    · have hn : (edgeIncidences G (rootEdges G Q r) x).card ≠ 2 :=
        fun h => hf (root_incidence_two_mem_fullDoubleTips G Q hN ht2 hx h)
      simp only [hf, ite_false]; omega
  have hsum := sum_le_sum hs
  simp only [sum_add_distrib, sum_const, smul_eq_mul, mul_one, ← sum_filter] at hsum
  have hsub : (rootTips G Q r).filter (fun x => x ∈ fullDoubleTips G Q r) ⊆ fullDoubleTips G Q r :=
    fun _ hx => (mem_filter.mp hx).2
  have hc := card_le_card hsub
  omega

variable [DecidableRel (conflictGraph G).Adj]

theorem high21_clique_card_le_eighteen_of_root_types_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) : Q.card ≤ 18 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high21_root_neighborhood_independent G hΔ Q h21 r (by omega)
  have hp := high21_multipleTips_card_le_six G hΔ Q h21 r hfull
  have htip : (rootTips G Q r).card ≤ 6 := by
    by_cases hsingle : (singleTips G Q r).Nonempty
    · obtain ⟨x, hx⟩ := hsingle
      obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
      exact rootTips_card_le_six_of_single G hΔ Q hQ hN ((G.mem_neighborFinset r a).mp haN)
        hxT e heQ he
    · exact (card_le_card (rootTips_subset_multiple_of_no_single G Q r hsingle)).trans hp
  have hfd := fullDoubleTips_card_le_four G hΔ Q hQ hN
  have hroot := rootEdges_card_le_tips_add_fullDoubleTips G Q r hN ht
  have ho := outer_card_le_four_of_double_types G hΔ Q hQ r hR hN ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card G Q r, hR]
  have hc := clique_card_le_star_root_outer G Q r
  omega

theorem high21_clique_card_le_eighteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 18 := by
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    exact high21_clique_card_le_eighteen_of_root_triple G hΔ Q hQ h21 r hR hxr hx
  apply high21_clique_card_le_eighteen_of_root_types_le_two G hΔ Q hQ h21 r hR
  intro x hxr
  have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
  omega

end Se20Part.Legacy
