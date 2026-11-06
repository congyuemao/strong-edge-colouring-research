module

public import Se20Part.Legacy.Bounds.High20

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A triple type uses one extra slot beyond the two required by a multiple
tip. The other multiple tips therefore number at most four. -/
theorem multipleTips_erase_card_le_four_of_triple
    (hΔ : ∀ x, G.degree x ≤ 4) {r x : V} (hxr : x ≠ r)
    (hx : 3 ≤ (rootType G r x).card) : ((multipleTips G r).erase x).card ≤ 4 := by
  have hxp : x ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩
  have hs := sum_le_sum (s := (multipleTips G r).erase x)
    (fun y hy => (mem_filter.mp (mem_erase.mp hy).2).2.2)
  have he := sum_erase_add (multipleTips G r) (fun y => (rootType G r y).card) hxp
  have hb := multipleTips_type_sum_le_twelve G hΔ r
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem outerEdges_eq_self_of_subset
    (Q R : Finset G.edgeSet) (r : V) (hs : R ⊆ outerEdges G Q r) :
    outerEdges G R r = R := by
  apply filter_eq_self.mpr
  intro e he
  exact (mem_filter.mp (hs he)).2

/-- Four outer edges supported on at most four multiple tips saturate every
tip. All original neighbours are retained in the degree bound. -/
theorem four_outer_edges_saturate_multiple_support
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V)
    (P : Finset V) (hP : P ⊆ multipleTips G r) (hcard : P.card ≤ 4)
    (hp : ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ P)
    (ho : (outerEdges G Q r).card = 4) {y : V} (hy : y ∈ P) :
    (edgeIncidences G (outerEdges G Q r) y).card = 2 := by
  have hi := outer_incidence_sum_eq_twice G Q r P hp
  have hb : ∀ z ∈ P, (edgeIncidences G (outerEdges G Q r) z).card ≤ 2 := by
    intro z hz
    have ht := (mem_filter.mp (hP hz)).2.2
    have hd := hΔ z
    have hr := outer_incidence_add_type_card_le_degree G Q r z
    omega
  have hyb := hb y hy
  have he := sum_erase_add P (fun z => (edgeIncidences G (outerEdges G Q r) z).card) hy
  have hc := card_erase_add_one hy
  have hs := sum_le_sum (s := P.erase y) (fun z hz => hb z (mem_erase.mp hz).2)
  simp only [sum_const, smul_eq_mul] at hs
  omega

/-- With exactly one triple type, a fifth outer edge would have to meet the
triple tip, while the other four edges saturate all their endpoints. The fifth
edge then has no conflict witness to those four edges. -/
theorem outer_card_le_four_of_unique_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : (rootType G r x).card = 3)
    (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2) :
    (outerEdges G Q r).card ≤ 4 := by
  by_contra hn
  let O := (outerEdges G Q r).filter (fun e => x ∉ e.val)
  let P := (multipleTips G r).erase x
  have hOsub : O ⊆ outerEdges G Q r := filter_subset _ _
  have hOeq : outerEdges G O r = O := outerEdges_eq_self_of_subset G Q O r hOsub
  have havoid := outer_avoiding_card_le_four_of_other_types_le_two G hΔ Q hQ r hR hN x ht
  have hpart := card_filter_add_card_filter_not (s := outerEdges G Q r) (p := fun e => x ∈ e.val)
  have hi := outer_incidence_add_type_card_le_degree G Q r x
  have hd := hΔ x
  change (edgeIncidences G (outerEdges G Q r) x).card + O.card = _ at hpart
  have hfour : O.card = 4 := by change O.card ≤ 4 at havoid; omega
  have hone : (edgeIncidences G (outerEdges G Q r) x).card = 1 := by omega
  have hPc : P.card ≤ 4 := multipleTips_erase_card_le_four_of_triple G hΔ hxr (by omega)
  have hPsub : P ⊆ multipleTips G r := erase_subset _ _
  have hsupport : ∀ e ∈ O, ∀ y ∈ e.val, y ∈ P := by
    intro e he y hye
    obtain ⟨heo, hxe⟩ := mem_filter.mp he
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hends := outerEdges_endpoints G Q r e hev.symm heo
    have hux : u ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_left u v)
    have hvx : v ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_right u v)
    have hu := ht u hends.2.1 hux
    have hv := ht v hends.2.2.1 hvx
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
      (card_union_le _ _)
    rw [← hev, Sym2.mem_iff] at hye
    rcases hye with rfl | rfl
    · exact mem_erase.mpr ⟨hux, mem_filter.mpr ⟨mem_univ _, hends.2.1, by omega⟩⟩
    · exact mem_erase.mpr ⟨hvx, mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩⟩
  have hsupport' : ∀ e ∈ outerEdges G O r, ∀ y ∈ e.val, y ∈ P := by
    simpa only [hOeq] using hsupport
  have hsat : ∀ y ∈ P, 4 ≤ (edgeIncidences G (outerEdges G O r) y).card +
      (rootType G r y).card := by
    intro y hy
    have htwo := four_outer_edges_saturate_multiple_support G hΔ O r P hPsub hPc
      hsupport' (by simpa only [hOeq] using hfour) hy
    have htype := (mem_filter.mp (hPsub hy)).2.2
    omega
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (edgeIncidences G (outerEdges G Q r) x).card by omega)
  obtain ⟨heo, hxe⟩ := mem_filter.mp he
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have hends := outerEdges_endpoints G Q r e hey heo
  have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
  have hxp : x ∉ P := notMem_erase _ _
  have hyp : y ∉ P := by
    intro hy
    have hres := outer_saturated_neighbors G hΔ O r P hsupport' (hsat y hy) hxy.symm
    exact hres.elim hends.2.2.2.1 hxp
  obtain ⟨f, hf⟩ := card_pos.mp (show 0 < O.card by omega)
  have hfQ : f ∈ Q := (mem_filter.mp (hOsub hf)).1
  have hef : e ≠ f := fun h => (mem_filter.mp hf).2 (h ▸ hxe)
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G hey (hQ hends.1 hfQ hef)
  have hwP := hsupport f hf w hwf
  rcases mem_union.mp hw with hw | hw
  · have hxw := (G.mem_neighborFinset x w).mp (mem_erase.mp hw).2
    have hres := outer_saturated_neighbors G hΔ O r P hsupport' (hsat w hwP) hxw.symm
    exact hres.elim hends.2.2.2.1 hxp
  · have hyw := (G.mem_neighborFinset y w).mp (mem_erase.mp hw).2
    have hres := outer_saturated_neighbors G hΔ O r P hsupport' (hsat w hwP) hyw.symm
    exact hres.elim hends.2.2.2.2 hyp

theorem clique_card_le_eighteen_of_unique_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hxr : x ≠ r) (hx : (rootType G r x).card = 3)
    (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2) : Q.card ≤ 18 := by
  have hroot := root_card_le_ten_of_unique_triple G hΔ Q hQ hN hR hx ht
  have ho := outer_card_le_four_of_unique_triple G hΔ Q hQ hN hR hxr hx ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  omega

variable [DecidableRel (conflictGraph G).Adj]

theorem high20_clique_card_le_eighteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 18 := by
  by_contra hn
  have hN := high20_large_clique_root_neighborhood_independent G hΔ Q hQ h20 (by omega) r hR
  by_cases hlarge : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := hlarge
    by_cases hx4 : 4 ≤ (rootType G r x).card
    · exact hn (high20_clique_card_le_eighteen_of_root_type_four G hΔ Q hQ h20 hN hR hxr hx4)
    by_cases htwo : ∃ y, y ≠ r ∧ y ≠ x ∧ 3 ≤ (rootType G r y).card
    · obtain ⟨y, hyr, hyx, hy⟩ := htwo
      exact hn (high20_clique_card_le_eighteen_of_two_triples G hΔ Q hQ h20 hN hR hxr hyr hyx.symm hx hy)
    have ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
      intro y hyr hyx
      have hn : ¬ 3 ≤ (rootType G r y).card := fun h => htwo ⟨y, hyr, hyx, h⟩
      omega
    exact hn (clique_card_le_eighteen_of_unique_triple G hΔ Q hQ hN hR hxr (by omega) ht)
  · have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
      intro x hxr
      have hn : ¬ 3 ≤ (rootType G r x).card := fun h => hlarge ⟨x, hxr, h⟩
      omega
    exact hn (clique_card_le_eighteen_of_independent_root_types_le_two G hΔ Q hQ r hR hN ht)

/-- The first unconditional stronger threshold for PACKING19.5. The support
degree-three branch needs only the previously verified bound eighteen. -/
theorem high20_clique_card_le_eighteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) : Q.card ≤ 18 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high20_clique_card_le_eighteen_of_root_four G hΔ Q hQ h20 r
      (by rw [rootLabels_card G Q r]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  exact clique_card_le_eighteen_of_support_degree_le_three G hΔ Q hQ hthree

end Se20Part.Legacy
