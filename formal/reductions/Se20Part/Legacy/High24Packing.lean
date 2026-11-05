module

public import Se20Part.Legacy.Bounds.High24
public import Se20Part.Legacy.MinimalPacking

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
  (high22 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
    (∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) → Q.card ≤ 17)
  (high23 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
    (∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e) → Q.card ≤ 16)

include hΔ high20 high21 high22 high23

/-- The original maximum-degree bound supplies high24; exactly the four lower
thresholds remain explicit mathematical parameters. -/
theorem minimalCliqueBounds20_of_high20_high21_high22_high23 :
    MinimalCliqueBounds20 (conflictGraph G) where
  high20 := high20
  high21 := high21
  high22 := high22
  high23 := high23
  high24 := high24_clique_card_le_fifteen G hΔ

/-- Conditional 20-packing after discharging C4 and high24. Conflicts and
induced matching are still measured in the full original graph. -/
theorem induced_matching_packing20_of_high20_high21_high22_high23
    (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card :=
  induced_matching_packing20_of_minimal_clique_bounds G hΔ
    (minimalCliqueBounds20_of_high20_high21_high22_high23 G hΔ high20 high21 high22 high23) F

end Se20Part.Legacy
