module

public import Se20Part.Legacy.Bounds.High23
public import Se20Part.Legacy.High24Packing

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

include hΔ high20 high21 high22

/-- High23 and high24 are supplied by proved original-graph theorems.
Exactly high20, high21, and high22 remain explicit clique-bound parameters. -/
theorem minimalCliqueBounds20_of_high20_high21_high22 :
    MinimalCliqueBounds20 (conflictGraph G) where
  high20 := high20
  high21 := high21
  high22 := high22
  high23 := high23_clique_card_le_sixteen G hΔ
  high24 := high24_clique_card_le_fifteen G hΔ

/-- Conditional 20-packing after discharging C4, high24, and high23. -/
theorem induced_matching_packing20_of_high20_high21_high22
    (F : Finset G.edgeSet) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      F.card ≤ 20 * M.card :=
  induced_matching_packing20_of_minimal_clique_bounds G hΔ
    (minimalCliqueBounds20_of_high20_high21_high22 G hΔ high20 high21 high22) F

end Se20Part.Legacy
