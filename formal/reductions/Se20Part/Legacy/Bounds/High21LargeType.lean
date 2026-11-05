module

public import Se20Part.Legacy.Bounds.High21Support
public import Se20Part.Legacy.Bounds.High22Heavy

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

omit [DecidableRel (conflictGraph G).Adj] in
theorem high21_large_types_share_label
    (hΔ : ∀ x, G.degree x ≤ 4) {r x y : V}
    (hx : 3 ≤ (rootType G r x).card) (hy : 2 ≤ (rootType G r y).card) :
    (rootType G r x ∩ rootType G r y).Nonempty := by
  have hc := card_union_add_card_inter (rootType G r x) (rootType G r y)
  have hu := card_le_card (union_subset (filter_subset (G.Adj x) (G.neighborFinset r))
    (filter_subset (G.Adj y) (G.neighborFinset r)))
  change (rootType G r x ∪ rootType G r y).card ≤ (G.neighborFinset r).card at hu
  have hd := hΔ r
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu
  apply card_pos.mp
  omega

theorem high21_multipleTips_eq_of_type_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hfull : rootLabels G Q r = G.neighborFinset r)
    {x : V} (hxr : x ≠ r) (hx : 4 ≤ (rootType G r x).card)
    {y : V} (hy : y ∈ multipleTips G r) : y = x := by
  by_contra hyx
  obtain ⟨_, hyr, hycard⟩ := mem_filter.mp hy
  obtain ⟨a, ha⟩ := high21_large_types_share_label G hΔ (r := r) (x := x) (y := y) (by omega) hycard
  obtain ⟨hax, hay⟩ := mem_inter.mp ha
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ (filter_subset _ _ hax)
  have hb := high21_shared_root_types_card_le_five G hΔ Q h21 haR hxr hyr (Ne.symm hyx) hax hay
  omega

theorem high21_other_type_le_two_of_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hfull : rootLabels G Q r = G.neighborFinset r)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card)
    {y : V} (hyr : y ≠ r) (hyx : y ≠ x) : (rootType G r y).card ≤ 2 := by
  by_contra hn
  obtain ⟨a, ha⟩ := high21_large_types_share_label G hΔ (y := y) hx (by omega)
  obtain ⟨hax, hay⟩ := mem_inter.mp ha
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ (filter_subset _ _ hax)
  have hb := high21_shared_root_types_card_le_five G hΔ Q h21 haR hxr hyr hyx.symm hax hay
  omega

/-- Once a triple type uses two units at a label, two other multiple types
cannot both use that label. The sum includes all original neighbours. -/
theorem high21_multiple_unique_at_triple_label
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r a x y z : V} (ha : a ∈ rootLabels G Q r)
    (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card)
    (hy : y ∈ multipleTips G r) (hz : z ∈ multipleTips G r)
    (hyx : y ≠ x) (hzx : z ≠ x)
    (hax : a ∈ rootType G r x) (hay : a ∈ rootType G r y)
    (haz : a ∈ rootType G r z) : y = z := by
  by_contra hyz
  let N := (G.neighborFinset a).erase r
  have hxN : x ∈ N := mem_erase.mpr ⟨hxr,
    (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hyN : y ∈ N := mem_erase.mpr ⟨(mem_filter.mp hy).2.1,
    (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
  have hzN : z ∈ N := mem_erase.mpr ⟨(mem_filter.mp hz).2.1,
    (G.mem_neighborFinset a z).mpr ((mem_rootType G r z a).mp haz).2.symm⟩
  have hs : ({x, y, z} : Finset V) ⊆ N := by
    intro w hw
    simp only [mem_insert, mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> assumption
  have hsum := sum_le_sum_of_subset_of_nonneg (f := fun w => ((rootType G r w).erase a).card)
    hs (fun _ _ _ => Nat.zero_le _)
  have hxn : x ∉ ({y, z} : Finset V) := by simp [Ne.symm hyx, Ne.symm hzx]
  rw [sum_insert hxn, sum_pair hyz] at hsum
  have hb := high21_root_label_budget_three G hΔ Q h21 ha
  have hcx := card_erase_add_one hax
  have hcy := card_erase_add_one hay
  have hcz := card_erase_add_one haz
  have hdy := (mem_filter.mp hy).2.2
  have hdz := (mem_filter.mp hz).2.2
  change _ ≤ ∑ w ∈ (G.neighborFinset a).erase r, _ at hsum
  omega

theorem high21_multipleTips_subset_triple_outer_endpoints
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card)
    {u v : V} (e : G.edgeSet) (heo : e ∈ outerEdges G Q r)
    (he : e.val = s(u, v)) (hxe : x ∉ e.val) :
    multipleTips G r ⊆ {x, u, v} := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hends := outerEdges_endpoints G Q r e he heo
  have hux : u ≠ x := fun h => hxe (he.symm ▸ h ▸ Sym2.mem_mk_left u v)
  have hvx : v ≠ x := fun h => hxe (he.symm ▸ h ▸ Sym2.mem_mk_right u v)
  have hu := high21_other_type_le_two_of_triple G hΔ Q h21 r hfull hxr hx hends.2.1 hux
  have hv := high21_other_type_le_two_of_triple G hΔ Q h21 r hfull hxr hx hends.2.2.1 hvx
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e he heo
  have hc := (card_le_card hcov).trans (card_union_le _ _)
  have hum : u ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hends.2.1, by omega⟩
  have hvm : v ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩
  intro y hy
  by_cases hyx : y = x
  · simp [hyx]
  obtain ⟨a, ha⟩ := high21_large_types_share_label G hΔ hx (mem_filter.mp hy).2.2
  obtain ⟨hax, hay⟩ := mem_inter.mp ha
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ (filter_subset _ _ hax)
  rcases mem_union.mp (hcov haR) with hau | hav
  · have heq := high21_multiple_unique_at_triple_label G hΔ Q h21 haR hxr hx hy hum hyx hux
      hax hay hau
    simp [heq]
  · have heq := high21_multiple_unique_at_triple_label G hΔ Q h21 haR hxr hx hy hvm hyx hvx
      hax hay hav
    simp [heq]

theorem high21_outer_card_le_two_of_root_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) :
    (outerEdges G Q r).card ≤ 2 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  let O := (outerEdges G Q r).filter (fun e => x ∉ e.val)
  have hO : O.card ≤ 1 := by
    apply card_le_one.mpr
    intro e he f hf
    obtain ⟨heo, hxe⟩ := mem_filter.mp he
    obtain ⟨hfo, hxf⟩ := mem_filter.mp hf
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    obtain ⟨p, q, hfq⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = f.val from ⟨f.val, rfl⟩)
    have hs := high21_multipleTips_subset_triple_outer_endpoints G hΔ Q hQ h21 r hR hxr hx
      e heo hev.symm hxe
    have hends := outerEdges_endpoints G Q r f hfq.symm hfo
    have hpx : p ≠ x := fun h => hxf (hfq ▸ h ▸ Sym2.mem_mk_left p q)
    have hqx : q ≠ x := fun h => hxf (hfq ▸ h ▸ Sym2.mem_mk_right p q)
    have hp := high21_other_type_le_two_of_triple G hΔ Q h21 r hfull hxr hx hends.2.1 hpx
    have hq := high21_other_type_le_two_of_triple G hΔ Q h21 r hfull hxr hx hends.2.2.1 hqx
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r f hfq.symm hfo)).trans
      (card_union_le _ _)
    have hpm := hs (mem_filter.mpr ⟨mem_univ _, hends.2.1, by omega⟩)
    have hqm := hs (mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩)
    simp only [mem_insert, mem_singleton, hpx, hqx, false_or] at hpm hqm
    have hpq : p ≠ q := (G.mem_edgeSet.mp (hfq ▸ f.property)).ne
    apply Subtype.ext
    rw [← hev, ← hfq]
    rcases hpm with rfl | rfl <;> rcases hqm with rfl | rfl
    · exact (hpq rfl).elim
    · rfl
    · exact Sym2.eq_swap
    · exact (hpq rfl).elim
  have hpart : (outerEdges G Q r).card = (edgeIncidences G (outerEdges G Q r) x).card + O.card := by
    exact (card_filter_add_card_filter_not (s := outerEdges G Q r) (p := fun e => x ∈ e.val)).symm
  have hi := outer_incidence_add_type_card_le_degree G Q r x
  have hd := hΔ x
  omega

theorem high21_clique_card_le_eighteen_of_root_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) : Q.card ≤ 18 := by
  have ho := high21_outer_card_le_two_of_root_triple G hΔ Q hQ h21 r hR hxr hx
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun y _ => (edgeIncidences_card_le_degree G Q y).trans (hΔ y))
  have hdr := hΔ r
  have hq := selected_edges_card_le_meeting_add_outer G Q r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  omega

end Se20Part.Legacy
