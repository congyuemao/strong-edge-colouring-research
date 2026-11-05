module

public import Se20Part.Legacy.Bounds.High20Local

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high20_other_type_single_at_shared_triple_label
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r a x y z : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ha : a ∈ rootLabels G Q r)
    (hxr : x ≠ r) (hyr : y ≠ r) (hzr : z ≠ r)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card)
    (hax : a ∈ rootType G r x) (hay : a ∈ rootType G r y)
    (haz : a ∈ rootType G r z) : rootType G r z = {a} := by
  have hs : ({x, y, z} : Finset V) ⊆ (G.neighborFinset a).erase r := by
    intro w hw
    have hwr : w ≠ r := by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    have haw : a ∈ rootType G r w := by
      simp only [mem_insert, mem_singleton] at hw
      rcases hw with rfl | rfl | rfl <;> assumption
    exact mem_erase.mpr ⟨hwr,
      (G.mem_neighborFinset a w).mpr ((mem_rootType G r w a).mp haw).2.symm⟩
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun w => ((rootType G r w).erase a).card)
    hs (fun _ _ _ => Nat.zero_le _)
  have hxn : x ∉ ({y, z} : Finset V) := by simp [hxy, hzx.symm]
  rw [sum_insert hxn, sum_pair hzy.symm] at hsum
  have hb := high20_root_label_budget_four G hΔ Q h20 hN ha
  have hcx := card_erase_add_one hax
  have hcy := card_erase_add_one hay
  have hcz := card_erase_add_one haz
  exact eq_of_subset_of_card_le (singleton_subset_iff.mpr haz) (by simp only [card_singleton]; omega) |>.symm

theorem high20_outer_meets_two_triples
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x y : V} (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card)
    (e : G.edgeSet) (heo : e ∈ outerEdges G Q r) : x ∈ e.val ∨ y ∈ e.val := by
  by_contra hn
  have hxe : x ∉ e.val := fun h => hn (Or.inl h)
  have hye : y ∉ e.val := fun h => hn (Or.inr h)
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hi := card_union_add_card_inter (rootType G r x) (rootType G r y)
  have hu := card_le_card (union_subset (filter_subset (G.Adj x) (G.neighborFinset r))
    (filter_subset (G.Adj y) (G.neighborFinset r)))
  change (rootType G r x ∪ rootType G r y).card ≤ (G.neighborFinset r).card at hu
  have hdr := hΔ r
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu
  have hab : 1 < (rootType G r x ∩ rootType G r y).card := by omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hab
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ (mem_inter.mp ha).1
  have hbR : b ∈ rootLabels G Q r := hfull.symm ▸ filter_subset _ _ (mem_inter.mp hb).1
  obtain ⟨u, v, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have heuv : e.val = s(u, v) := he.symm
  have hends := outerEdges_endpoints G Q r e heuv heo
  have hux : u ≠ x := fun h => hxe (he ▸ h ▸ Sym2.mem_mk_left u v)
  have hvx : v ≠ x := fun h => hxe (he ▸ h ▸ Sym2.mem_mk_right u v)
  have huy : u ≠ y := fun h => hye (he ▸ h ▸ Sym2.mem_mk_left u v)
  have hvy : v ≠ y := fun h => hye (he ▸ h ▸ Sym2.mem_mk_right u v)
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e heuv heo
  have hcard := (card_le_card hcov).trans (card_union_le _ _)
  have hsingle {c w : V} (hc : c ∈ rootType G r x ∩ rootType G r y)
      (hcR : c ∈ rootLabels G Q r) (hwr : w ≠ r) (hwx : w ≠ x) (hwy : w ≠ y)
      (hcw : c ∈ rootType G r w) : rootType G r w = {c} :=
    high20_other_type_single_at_shared_triple_label G hΔ Q h20 hN hcR hxr hyr hwr hxy hwx hwy
      hx hy (mem_inter.mp hc).1 (mem_inter.mp hc).2 hcw
  rcases mem_union.mp (hcov haR) with hau | hav
  · have huT := hsingle ha haR hends.2.1 hux huy hau
    have hbv : b ∈ rootType G r v := by
      rcases mem_union.mp (hcov hbR) with hbu | hbv
      · have hba : b = a := by simpa only [huT, mem_singleton] using hbu
        exact (hab hba.symm).elim
      · exact hbv
    have hvT := hsingle hb hbR hends.2.2.1 hvx hvy hbv
    simp only [huT, hvT, card_singleton, hR] at hcard
    omega
  · have hvT := hsingle ha haR hends.2.2.1 hvx hvy hav
    have hbu : b ∈ rootType G r u := by
      rcases mem_union.mp (hcov hbR) with hbu | hbv
      · exact hbu
      · have hba : b = a := by simpa only [hvT, mem_singleton] using hbv
        exact (hab hba.symm).elim
    have huT := hsingle hb hbR hends.2.1 hux huy hbu
    simp only [huT, hvT, card_singleton, hR] at hcard
    omega

theorem high20_clique_card_le_eighteen_of_two_triples
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x y : V} (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card) : Q.card ≤ 18 := by
  have hs : outerEdges G Q r ⊆ edgeIncidences G (outerEdges G Q r) x ∪
      edgeIncidences G (outerEdges G Q r) y := by
    intro e he
    rcases high20_outer_meets_two_triples G hΔ Q hQ h20 hN hR hxr hyr hxy hx hy e he with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨he, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨he, h⟩)
  have ho := (card_le_card hs).trans (card_union_le _ _)
  have hix := outer_incidence_add_type_card_le_degree G Q r x
  have hiy := outer_incidence_add_type_card_le_degree G Q r y
  have hdx := hΔ x
  have hdy := hΔ y
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun z _ => (edgeIncidences_card_le_degree G Q z).trans (hΔ z))
  have hdr := hΔ r
  have hq := selected_edges_card_le_meeting_add_outer G Q r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  omega

end Se20Part.Legacy
