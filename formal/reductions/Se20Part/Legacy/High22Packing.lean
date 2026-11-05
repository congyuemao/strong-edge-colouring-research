module

public import Se20Part.Legacy.Bounds.High22
public import Se20Part.Legacy.High23Packing

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]
variable (hΔ : ∀ x, G.degree x ≤ 4)
variable
  (high20 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
    (∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) → Q.card ≤ 19)
  (high21 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
    (∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e) → Q.card ≤ 18)

include hΔ high20 high21

/-- The three highest thresholds are proved; high20 and high21 remain explicit. -/
theorem minimalCliqueBounds20_of_high20_high21 :
    MinimalCliqueBounds20 (conflictGraph G) :=
  minimalCliqueBounds20_of_high20_high21_high22 G hΔ high20 high21
    (high22_clique_card_le_seventeen G hΔ)

/-- Conditional 20-packing for every candidate set in the complete original graph. -/
theorem induced_matching_packing20_of_high20_high21
    (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card :=
  induced_matching_packing20_of_minimal_clique_bounds G hΔ
    (minimalCliqueBounds20_of_high20_high21 G hΔ high20 high21) F

end Se20Part.Legacy
