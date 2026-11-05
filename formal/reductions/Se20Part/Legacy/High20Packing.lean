module

public import Se20Part.Legacy.Bounds.High20
public import Se20Part.Legacy.High21Packing

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- All five clique thresholds follow from the original degree-four bound. -/
theorem minimalCliqueBounds20_of_maxDegree_four
    (hΔ : ∀ x, G.degree x ≤ 4) : MinimalCliqueBounds20 (conflictGraph G) :=
  minimalCliqueBounds20_of_high20 G hΔ (high20_clique_card_le_nineteen G hΔ)

/-- Every original candidate edge set admits induced-matching 20-packing. -/
theorem induced_matching_packing20
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card :=
  induced_matching_packing20_of_minimal_clique_bounds G hΔ
    (minimalCliqueBounds20_of_maxDegree_four G hΔ) F

end Se20Part.Legacy
