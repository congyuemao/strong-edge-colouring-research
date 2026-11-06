module

public import Se20Part.Legacy.Bounds.SubcubicSeventeen

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- Unconditional stronger high21 threshold, in the complete original graph. -/
theorem high21_clique_card_le_seventeen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e) : Q.card ≤ 17 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high21_clique_card_le_seventeen_of_root_four G hΔ Q hQ h21 r
      (by rw [rootLabels_card]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  exact clique_card_le_seventeen_of_support_degree_le_three G hΔ Q hQ hthree

end Se20Part.Legacy
