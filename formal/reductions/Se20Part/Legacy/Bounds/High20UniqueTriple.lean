module

public import Se20Part.Legacy.Bounds.High20Slots
public import Se20Part.Legacy.Bounds.High20Outer

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem root_missing_label_selected_degree_le_two_of_unique_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hx : (rootType G r x).card = 3)
    (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2)
    (hsel : 2 ≤ (rootType G r x ∩ rootLabels G Q x).card)
    {o : V} (ho : G.Adj r o) (hox : o ∉ rootType G r x) :
    (edgeIncidences G Q o).card ≤ 2 := by
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hro : r ∈ rootLabels G Q o := root_label_mem_symm G Q
    (hfull.symm ▸ (G.mem_neighborFinset r o).mpr ho)
  have hs : (rootLabels G Q o).erase r ⊆ G.neighborFinset x \ G.neighborFinset r := by
    intro y hy
    obtain ⟨hyr, hyl⟩ := mem_erase.mp hy
    obtain ⟨hyN, f, hfQ, hf⟩ := mem_filter.mp hyl
    have hoy := (G.mem_neighborFinset o y).mp hyN
    have hyx : y ≠ x := fun h => hox ((mem_rootType G r x o).mpr ⟨ho, h ▸ hoy.symm⟩)
    have hy2 := ht y hyr hyx
    have hot : o ∈ rootType G r y := (mem_rootType G r y o).mpr ⟨ho, hoy.symm⟩
    have hnsub : ¬ rootType G r x ∩ rootLabels G Q x ⊆ rootType G r y := by
      intro hsub
      have hsub' : rootType G r x ∩ rootLabels G Q x ⊆ (rootType G r y).erase o := by
        intro a ha
        exact mem_erase.mpr ⟨fun h => hox (h ▸ (mem_inter.mp ha).1), hsub ha⟩
      have hc := card_le_card hsub'
      have he := card_erase_add_one hot
      omega
    obtain ⟨a, ha, hay⟩ := not_subset.mp hnsub
    obtain ⟨hat, hal⟩ := mem_inter.mp ha
    obtain ⟨_, e, heQ, he⟩ := mem_filter.mp hal
    have hxy := root_selected_edges_force_adj G Q hQ hN ((mem_rootType G r x a).mp hat).1 ho
      hox hay e f heQ hfQ (he.trans Sym2.eq_swap) hf
    have hny := root_edge_tip_not_neighbor G hN ho f hf
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset x y).mpr hxy,
      fun h => hny ((G.mem_neighborFinset r y).mp h)⟩
  have hc := card_le_card hs
  have hres := residual_neighbors_add_type_card G r x
  have hdx := hΔ x
  have he := card_erase_add_one hro
  rw [rootLabels_card] at he
  omega

theorem root_card_le_ten_of_unique_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hx : (rootType G r x).card = 3)
    (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2) :
    (rootEdges G Q r).card ≤ 10 := by
  by_cases hsel : 2 ≤ (rootType G r x ∩ rootLabels G Q x).card
  · have hnsub : ¬ G.neighborFinset r ⊆ rootType G r x := by
      intro hs
      have hc := (card_le_card (rootLabels_subset_neighbors G Q r)).trans (card_le_card hs)
      omega
    obtain ⟨o, hoN, hox⟩ := not_subset.mp hnsub
    have ho := (G.mem_neighborFinset r o).mp hoN
    exact root_card_le_ten_of_label_selected_degree_le_two G hΔ Q r hR ho
      (root_missing_label_selected_degree_le_two_of_unique_triple G hΔ Q hQ hN hR hx ht hsel ho hox)
  · have hmissing := root_card_add_missing_type_le_twelve G hΔ Q r hR x
    have hp := card_sdiff_add_card_inter (rootType G r x) (rootLabels G Q x)
    omega

theorem clique_card_le_nineteen_of_unique_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) (hR : (rootLabels G Q r).card = 4)
    {x : V} (hx : (rootType G r x).card = 3)
    (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2) : Q.card ≤ 19 := by
  have hroot := root_card_le_ten_of_unique_triple G hΔ Q hQ hN hR hx ht
  have ho := outer_avoiding_card_le_four_of_other_types_le_two G hΔ Q hQ r hR hN x ht
  have hp := card_filter_add_card_filter_not (s := outerEdges G Q r) (p := fun e => x ∈ e.val)
  have hi := outer_incidence_add_type_card_le_degree G Q r x
  have hdx := hΔ x
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  change (edgeIncidences G (outerEdges G Q r) x).card + _ = _ at hp
  omega

end Se20Part.Legacy
