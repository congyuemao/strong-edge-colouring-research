module

public import Se20Part.Legacy.Bounds.High21
public import Se20Part.Legacy.High22Packing

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (hΔ : ∀ x, G.degree x ≤ 4)
variable
  (high20 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
    (∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) → Q.card ≤ 19)

include hΔ high20

/-- All higher thresholds are proved; only high20 remains explicit. -/
theorem minimalCliqueBounds20_of_high20 :
    MinimalCliqueBounds20 (conflictGraph G) :=
  minimalCliqueBounds20_of_high20_high21 G hΔ high20
    (high21_clique_card_le_eighteen G hΔ)

/-- Conditional 20-packing for every candidate set in the complete original graph. -/
theorem induced_matching_packing20_of_high20
    (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card :=
  induced_matching_packing20_of_minimal_clique_bounds G hΔ
    (minimalCliqueBounds20_of_high20 G hΔ high20) F

end Se20Part.Legacy
