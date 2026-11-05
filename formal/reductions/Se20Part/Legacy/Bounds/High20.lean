module

public import Se20Part.Legacy.Bounds.High20Four
public import Se20Part.Legacy.Bounds.High20TwoTriples
public import Se20Part.Legacy.Bounds.High20UniqueTriple

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem clique_card_le_eighteen_of_independent_root_types_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (hN : G.IsIndepSet (G.neighborSet r))
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2) : Q.card ≤ 18 := by
  have hp := multipleTips_card_le_six G hΔ r
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

variable [DecidableRel (conflictGraph G).Adj]

theorem high20_clique_card_le_nineteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 19 := by
  by_contra hn
  have hN := high20_large_clique_root_neighborhood_independent G hΔ Q hQ h20 (by omega) r hR
  by_cases hlarge : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := hlarge
    by_cases hx4 : 4 ≤ (rootType G r x).card
    · have hb := high20_clique_card_le_eighteen_of_root_type_four G hΔ Q hQ h20 hN hR hxr hx4
      omega
    by_cases htwo : ∃ y, y ≠ r ∧ y ≠ x ∧ 3 ≤ (rootType G r y).card
    · obtain ⟨y, hyr, hyx, hy⟩ := htwo
      have hb := high20_clique_card_le_eighteen_of_two_triples G hΔ Q hQ h20 hN hR hxr hyr hyx.symm hx hy
      omega
    have ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
      intro y hyr hyx
      have hn : ¬ 3 ≤ (rootType G r y).card := fun h => htwo ⟨y, hyr, hyx, h⟩
      omega
    exact hn (clique_card_le_nineteen_of_unique_triple G hΔ Q hQ hN hR (by omega) ht)
  · have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
      intro x hxr
      have hn : ¬ 3 ≤ (rootType G r x).card := fun h => hlarge ⟨x, hxr, h⟩
      omega
    have hb := clique_card_le_eighteen_of_independent_root_types_le_two G hΔ Q hQ r hR hN ht
    omega

/-- Universal high20 bound in the complete original conflict graph. -/
theorem high20_clique_card_le_nineteen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h20 : ∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) : Q.card ≤ 19 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high20_clique_card_le_nineteen_of_root_four G hΔ Q hQ h20 r
      (by rw [rootLabels_card G Q r]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  exact (clique_card_le_eighteen_of_support_degree_le_three G hΔ Q hQ hthree).trans (by omega)

end Se20Part.Legacy

