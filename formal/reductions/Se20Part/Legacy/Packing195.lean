module

public import Se20Part.Legacy.MinimalPacking195
public import Se20Part.Legacy.Bounds.High24
public import Se20Part.Legacy.Bounds.High20Improved
public import Se20Part.Legacy.Bounds.High23Improved

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- Only four stronger structural bounds remain to construct the threshold
record: the old, unconditional high24 bound already suffices. -/
theorem cliqueBounds195_of_four_improvements
    (hΔ : ∀ x, G.degree x ≤ 4)
    (h20 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 20 ≤ (conflictGraph G).degree e) → Q.card ≤ 18)
    (h21 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e) → Q.card ≤ 17)
    (h22 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) → Q.card ≤ 16)
    (h23 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e) → Q.card ≤ 15) :
    CliqueBounds195 (conflictGraph G) where
  high20 := h20
  high21 := h21
  high22 := h22
  high23 := h23
  high24 Q hc hd := (high24_clique_card_le_thirteen G hΔ Q hc hd).trans (by omega)

/-- The high20 and high23 improvements are now proved. Only high21 and high22
remain explicit structural hypotheses in this constructor. -/
theorem cliqueBounds195_of_two_improvements
    (hΔ : ∀ x, G.degree x ≤ 4)
    (h21 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e) → Q.card ≤ 17)
    (h22 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) → Q.card ≤ 16) :
    CliqueBounds195 (conflictGraph G) :=
  cliqueBounds195_of_four_improvements G hΔ (high20_clique_card_le_eighteen G hΔ)
    h21 h22 (high23_clique_card_le_fifteen G hΔ)

/-- Current conditional endpoint. The two missing threshold bounds and the
candidate twenty-clique exclusion are visible in the theorem's full type.
No statement about isolated C5[2] components is assumed or asserted here. -/
theorem induced_matching_packing195_of_two_improvements
    (hΔ : ∀ x, G.degree x ≤ 4)
    (h21 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e) → Q.card ≤ 17)
    (h22 : ∀ Q : Finset G.edgeSet, (conflictGraph G).IsClique (Q : Set G.edgeSet) →
      (∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e) → Q.card ≤ 16)
    (F : Finset G.edgeSet)
    (no20 : ∀ Q : Finset G.edgeSet, Q ⊆ F →
      (conflictGraph G).IsClique (Q : Set G.edgeSet) → Q.card ≤ 19) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      2 * F.card ≤ 39 * M.card :=
  induced_matching_packing195_of_clique_bounds G hΔ
    (cliqueBounds195_of_two_improvements G hΔ h21 h22) F no20

end Se20Part.Legacy
