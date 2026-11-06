module

public import Se20Part.Legacy.Bounds.High21ImprovedRoot

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The stronger full-double saturation bound also closes the high22
four-selected-star branch, including selected and unselected external edges. -/
theorem high22_clique_card_le_sixteen_of_root_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 4) : Q.card ≤ 16 := by
  have h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e := fun e he => (by have := h22 e he; omega)
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    exact high21_clique_card_le_sixteen_of_root_triple G hΔ Q hQ h21 r hR hxr hx
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
    intro x hxr
    have hn : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
    omega
  have hfull : rootLabels G Q r = G.neighborFinset r :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q r)
      (by simpa only [hR, SimpleGraph.card_neighborFinset_eq_degree] using hΔ r)
  have hN := high22_root_neighborhood_independent G hΔ Q h22 r (by omega)
  have hp := high22_multipleTips_card_le_four G hΔ Q h22 r hfull
  have ho := high22_outer_card_le_four_of_root_types_le_two G hΔ Q hQ h22 r hR ht
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hc := clique_card_le_star_root_outer G Q r
  by_cases hs : (singleTips G Q r).Nonempty
  · obtain ⟨x, hx⟩ := hs
    obtain ⟨_, _, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
    have ha := (G.mem_neighborFinset r a).mp haN
    have htip := rootTips_card_le_six_of_single G hΔ Q hQ hN ha hxT e heQ he
    have hfd := fullDoubleTips_card_le_four G hΔ Q hQ hN
    have hr := rootEdges_card_le_tips_add_fullDoubleTips G Q r hN ht
    by_cases hf : (fullDoubleTips G Q r).card = 4
    · have htc := card_le_card (rootTips_subset_fullDoubleTips_of_four G hΔ Q hQ hN ht hf)
      omega
    by_cases hfour : (outerEdges G Q r).card = 4
    · have htwo := high22_active_multiple_card_le_two_of_outer_four G hΔ Q hQ h22 r hR ht hfour
        ha hxT e heQ he
      have hr' := rootEdges_card_le_tips_add_multiple G Q r ht
      omega
    · omega
  · have hr := rootEdges_card_le_twice_multiple_of_no_single G Q r ht hs
    omega

end Se20Part.Legacy
