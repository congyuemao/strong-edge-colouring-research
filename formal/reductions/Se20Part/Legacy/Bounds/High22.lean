module

public import Se20Part.Legacy.Bounds.High22Subcubic

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- Universal high22 bound, retaining all original edges as conflict witnesses. -/
theorem high22_clique_card_le_seventeen
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) : Q.card ≤ 17 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high22_clique_card_le_seventeen_of_root_four G hΔ Q hQ h22 r
      (by rw [rootLabels_card G Q r]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  exact high22_clique_card_le_seventeen_of_support_degree_le_three G hΔ Q hQ h22 hthree

end Se20Part.Legacy
