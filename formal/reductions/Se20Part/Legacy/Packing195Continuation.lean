module

public import Se20Part.Legacy.Packing195
public import Se20Part.Legacy.Bounds.High21Improved

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- The remaining high22 boundary case, stated explicitly as an exclusion.
It is a definition of an obligation, not an asserted theorem. -/
def High22SubcubicSeventeenExcluded : Prop :=
  ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
    (∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) →
    (∀ x, (edgeIncidences G Q x).card ≤ 3) → Q.card = 17 → False

theorem high22_clique_card_le_sixteen_of_subcubic_exclusion
    (hΔ : ∀ x, G.degree x ≤ 4) (hsub : High22SubcubicSeventeenExcluded G)
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) : Q.card ≤ 16 := by
  by_cases hfour : ∃ r, (edgeIncidences G Q r).card = 4
  · obtain ⟨r, hr⟩ := hfour
    exact high22_clique_card_le_sixteen_of_root_four G hΔ Q hQ h22 r
      (by rw [rootLabels_card]; exact hr)
  have hthree : ∀ x, (edgeIncidences G Q x).card ≤ 3 := by
    intro x
    have hc := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
    have hn : (edgeIncidences G Q x).card ≠ 4 := fun h => hfour ⟨x, h⟩
    omega
  have hc := clique_card_le_seventeen_of_support_degree_le_three G hΔ Q hQ hthree
  by_contra hn
  exact hsub Q hQ h22 hthree (by omega)

/-- All other threshold obligations, including high21, are discharged. -/
theorem cliqueBounds195_of_subcubic_high22
    (hΔ : ∀ x, G.degree x ≤ 4) (hsub : High22SubcubicSeventeenExcluded G) :
    CliqueBounds195 (conflictGraph G) :=
  cliqueBounds195_of_two_improvements G hΔ (high21_clique_card_le_seventeen G hΔ)
    (high22_clique_card_le_sixteen_of_subcubic_exclusion G hΔ hsub)

/-- The current 19.5 endpoint exposes exactly the remaining high22 boundary
obligation and the candidate twenty-clique exclusion. Component correction
and classification are still separate, unproved tasks. -/
theorem induced_matching_packing195_of_subcubic_high22
    (hΔ : ∀ x, G.degree x ≤ 4) (hsub : High22SubcubicSeventeenExcluded G)
    (F : Finset G.edgeSet)
    (no20 : ∀ Q : Finset G.edgeSet, Q ⊆ F →
      (conflictGraph G).IsClique (Q : Set G.edgeSet) → Q.card ≤ 19) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      2 * F.card ≤ 39 * M.card :=
  induced_matching_packing195_of_clique_bounds G hΔ
    (cliqueBounds195_of_subcubic_high22 G hΔ hsub) F no20

end Se20Part.Legacy
