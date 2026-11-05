module

public import Se20Part.Legacy.Bounds.High21

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem endpointNeighbourCover_card_le_five_of_triangle
    (hΔ : ∀ x, G.degree x ≤ 4) {u v w : V}
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    (endpointNeighbourCover G u v).card ≤ 5 := by
  have hu := card_erase_add_one ((G.mem_neighborFinset u v).mpr huv)
  have hv := card_erase_add_one ((G.mem_neighborFinset v u).mpr huv.symm)
  have hi := card_union_add_card_inter ((G.neighborFinset u).erase v) ((G.neighborFinset v).erase u)
  have hw : w ∈ (G.neighborFinset u).erase v ∩ (G.neighborFinset v).erase u :=
    mem_inter.mpr ⟨mem_erase.mpr ⟨hvw.ne.symm, (G.mem_neighborFinset u w).mpr huw⟩,
      mem_erase.mpr ⟨huw.ne.symm, (G.mem_neighborFinset v w).mpr hvw⟩⟩
  have hp := card_pos.mpr ⟨w, hw⟩
  have hdu := hΔ u
  have hdv := hΔ v
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  dsimp [endpointNeighbourCover]
  omega

theorem root_label_multiple_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) {r a : V} (ha : G.Adj r a) :
    ((multipleTips G r).filter (fun x => a ∈ rootType G r x)).card ≤ 3 := by
  have hs : (multipleTips G r).filter (fun x => a ∈ rootType G r x) ⊆ (G.neighborFinset a).erase r := by
    intro x hx
    obtain ⟨hxm, hax⟩ := mem_filter.mp hx
    exact mem_erase.mpr ⟨(mem_filter.mp hxm).2.1,
      (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hc := card_le_card hs
  have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr ha.symm)
  have hd := hΔ a
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at he
  omega

theorem multipleTips_type_sum_le_twelve
    (hΔ : ∀ x, G.degree x ≤ 4) (r : V) :
    (∑ x ∈ multipleTips G r, (rootType G r x).card) ≤ 12 := by
  rw [root_type_card_sum_eq_label_sum]
  have hs := sum_le_sum (s := G.neighborFinset r) (fun a ha =>
    root_label_multiple_card_le_three G hΔ ((G.mem_neighborFinset r a).mp ha))
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  omega

theorem multipleTips_card_le_six
    (hΔ : ∀ x, G.degree x ≤ 4) (r : V) : (multipleTips G r).card ≤ 6 := by
  have hs := sum_le_sum (s := multipleTips G r) (fun x hx => (mem_filter.mp hx).2.2)
  have hb := multipleTips_type_sum_le_twelve G hΔ r
  simp only [sum_const, smul_eq_mul] at hs
  omega

variable [DecidableRel (conflictGraph G).Adj]

theorem high20_cover_inside_card_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) {u v : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h20 : 20 ≤ (conflictGraph G).degree e) :
    (edgesInside G univ (endpointNeighbourCover G u v)).card ≤ 4 := by
  have hc := conflict_degree_add_inside_le_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun w _ => hΔ w)
  have hcard := endpointNeighbourCover_card_le_six G (G.mem_edgeSet.mp (he ▸ e.property)) hΔ
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem high20_triangle_cover_inside_empty
    (hΔ : ∀ x, G.degree x ≤ 4) {u v w : V} (e : G.edgeSet)
    (he : e.val = s(u, v)) (h20 : 20 ≤ (conflictGraph G).degree e)
    (huw : G.Adj u w) (hvw : G.Adj v w) :
    edgesInside G univ (endpointNeighbourCover G u v) = ∅ := by
  have hc := conflict_degree_add_inside_le_sum G e he
  have hs := sum_le_sum (s := endpointNeighbourCover G u v) (fun z _ => hΔ z)
  have hcard := endpointNeighbourCover_card_le_five_of_triangle G hΔ
    (G.mem_edgeSet.mp (he ▸ e.property)) huw hvw
  simp only [sum_const, smul_eq_mul] at hs
  apply card_eq_zero.mp
  omega

theorem high20_triangle_root_type_singleton
    (hΔ : ∀ x, G.degree x ≤ 4) {r a b x : V} (e : G.edgeSet)
    (he : e.val = s(r, a)) (h20 : 20 ≤ (conflictGraph G).degree e)
    (hrb : G.Adj r b) (hab : G.Adj a b) (hxr : x ≠ r)
    (hax : a ∈ rootType G r x) : rootType G r x = {a} := by
  apply eq_singleton_iff_unique_mem.mpr
  refine ⟨hax, ?_⟩
  intro c hc
  by_contra hca
  have hcx := (mem_rootType G r x c).mp hc
  have hxa := (mem_rootType G r x a).mp hax
  let f : G.edgeSet := ⟨s(c, x), hcx.2.symm⟩
  have hf : f ∈ edgesInside G univ (endpointNeighbourCover G r a) := by
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    change ∀ v ∈ s(c, x), v ∈ endpointNeighbourCover G r a
    exact Sym2.forall_mem_pair.mpr
      ⟨mem_union_left _ (mem_erase.mpr ⟨hca, (G.mem_neighborFinset r c).mpr hcx.1⟩),
       mem_union_right _ (mem_erase.mpr ⟨hxr, (G.mem_neighborFinset a x).mpr hxa.2.symm⟩)⟩
  rw [high20_triangle_cover_inside_empty G hΔ e he h20 hrb hab] at hf
  exact notMem_empty _ hf

theorem high20_root_triangle_outer_empty
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {a b : V} (hra : G.Adj r a) (hrb : G.Adj r b) (hab : G.Adj a b) :
    outerEdges G Q r = ∅ := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  obtain ⟨_, ea, heaQ, hea⟩ := mem_filter.mp (hfull.symm ▸ (G.mem_neighborFinset r a).mpr hra)
  obtain ⟨_, eb, hebQ, heb⟩ := mem_filter.mp (hfull.symm ▸ (G.mem_neighborFinset r b).mpr hrb)
  have hsinglea {x : V} (hxr : x ≠ r) (hx : a ∈ rootType G r x) :=
    high20_triangle_root_type_singleton G hΔ ea hea (h20 ea heaQ) hrb hab hxr hx
  have hsingleb {x : V} (hxr : x ≠ r) (hx : b ∈ rootType G r x) :=
    high20_triangle_root_type_singleton G hΔ eb heb (h20 eb hebQ) hra hab.symm hxr hx
  apply eq_empty_iff_forall_notMem.mpr
  intro e heo
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hends := outerEdges_endpoints G Q r e he.symm heo
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e he.symm heo
  have hc := (card_le_card hcov).trans (card_union_le _ _)
  have haR := hfull.symm ▸ (G.mem_neighborFinset r a).mpr hra
  have hbR := hfull.symm ▸ (G.mem_neighborFinset r b).mpr hrb
  rcases mem_union.mp (hcov haR) with hau | hav
  · have hu := hsinglea hends.2.1 hau
    have hbv : b ∈ rootType G r v := by
      rcases mem_union.mp (hcov hbR) with hbu | hbv
      · have hba : b = a := by simpa only [hu, mem_singleton] using hbu
        exact (hab.ne hba.symm).elim
      · exact hbv
    have hv := hsingleb hends.2.2.1 hbv
    simp only [hu, hv, card_singleton, hR] at hc
    omega
  · have hv := hsinglea hends.2.2.1 hav
    have hbu : b ∈ rootType G r u := by
      rcases mem_union.mp (hcov hbR) with hbu | hbv
      · exact hbu
      · have hba : b = a := by simpa only [hv, mem_singleton] using hbv
        exact (hab.ne hba.symm).elim
    have hu := hsingleb hends.2.1 hbu
    simp only [hu, hv, card_singleton, hR] at hc
    omega

/-- Triangle exclusion is derived for a large high20 clique, not assumed
from the full-degree threshold alone. -/
theorem high20_large_clique_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) (hlarge : 17 ≤ Q.card)
    (r : V) (hR : (rootLabels G Q r).card = 4) : G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb _ hab
  have ho := high20_root_triangle_outer_empty G hΔ Q hQ h20 r hR ha hb hab
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hs := sum_le_sum (s := G.neighborFinset r)
    (fun x _ => (edgeIncidences_card_le_degree G Q x).trans (hΔ x))
  have hc := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  simp only [ho, card_empty] at hc
  omega

theorem high20_root_label_budget_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r a : V} (hN : G.IsIndepSet (G.neighborSet r)) (ha : a ∈ rootLabels G Q r) :
    (∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card) ≤ 4 := by
  obtain ⟨haN, e, heQ, he⟩ := mem_filter.mp ha
  have hra := (G.mem_neighborFinset r a).mp haN
  have hdis : Disjoint ((G.neighborFinset r).erase a) ((G.neighborFinset a).erase r) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hN hra ((G.mem_neighborFinset r x).mp (mem_erase.mp hx).2) (mem_erase.mp hx).1.symm
      ((G.mem_neighborFinset a x).mp (mem_erase.mp hy).2)
  rw [← fourCycleOpposites_card_eq_root_load]
  have hc : (fourCycleOpposites G r a).card ≤ (edgesInside G univ (endpointNeighbourCover G r a)).card := by
    apply card_le_via_relation _ _ (fun p f => f.val = s(p.1, p.2))
    · intro p hp
      obtain ⟨hp, hpAdj⟩ := mem_filter.mp hp
      obtain ⟨hx, hy⟩ := mem_product.mp hp
      refine ⟨⟨s(p.1, p.2), hpAdj⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact Sym2.forall_mem_pair.mpr ⟨mem_union_left _ hx, mem_union_right _ hy⟩
    · intro p hp q hq f hpf hqf
      obtain ⟨hp, _⟩ := mem_filter.mp hp
      obtain ⟨hq, _⟩ := mem_filter.mp hq
      obtain ⟨hxp, _⟩ := mem_product.mp hp
      obtain ⟨_, hyq⟩ := mem_product.mp hq
      rcases Sym2.eq_iff.mp (hpf.symm.trans hqf) with h | h
      · exact Prod.ext h.1 h.2
      · exact (disjoint_left.mp hdis hxp (h.1.symm ▸ hyq)).elim
  exact hc.trans (high20_cover_inside_card_le_four G hΔ e he (h20 e heQ))

theorem high20_shared_root_types_card_le_six
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r a x y : V} (hN : G.IsIndepSet (G.neighborSet r)) (ha : a ∈ rootLabels G Q r)
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hax : a ∈ rootType G r x) (hay : a ∈ rootType G r y) :
    (rootType G r x).card + (rootType G r y).card ≤ 6 := by
  have hx : x ∈ (G.neighborFinset a).erase r := mem_erase.mpr
    ⟨hxr, (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hy : y ∈ (G.neighborFinset a).erase r := mem_erase.mpr
    ⟨hyr, (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
  have hs : ({x, y} : Finset V) ⊆ (G.neighborFinset a).erase r := by
    intro z hz
    rcases mem_insert.mp hz with h | h
    · exact h ▸ hx
    · exact (mem_singleton.mp h) ▸ hy
  have hc := sum_le_sum_of_subset_of_nonneg (f := fun z => ((rootType G r z).erase a).card)
    hs (fun _ _ _ => Nat.zero_le _)
  simp only [sum_pair hxy] at hc
  have hb := high20_root_label_budget_four G hΔ Q h20 hN ha
  have hxcard := card_erase_add_one hax
  have hycard := card_erase_add_one hay
  omega

end Se20Part.Legacy
