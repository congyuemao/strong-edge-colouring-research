module

public import Se20Part.Legacy.Packing195Continuation
public import Se20Part.Legacy.Bounds.High22Improved

@[expose] public section

namespace Se20Part.Legacy

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

/-- All five stronger thresholds now follow from maximum original degree four. -/
theorem cliqueBounds195_of_degree_le_four (hΔ : ∀ x, G.degree x ≤ 4) :
    CliqueBounds195 (conflictGraph G) where
  high20 := high20_clique_card_le_eighteen G hΔ
  high21 := high21_clique_card_le_seventeen G hΔ
  high22 := high22_clique_card_le_sixteen G hΔ
  high23 := high23_clique_card_le_fifteen G hΔ
  high24 Q hQ hd := (high24_clique_card_le_thirteen G hΔ Q hQ hd).trans (by omega)

/-- The structural high22 obligation in the previous interface is discharged. -/
theorem high22SubcubicSeventeenExcluded_of_degree_le_four (hΔ : ∀ x, G.degree x ≤ 4) :
    High22SubcubicSeventeenExcluded G :=
  fun Q hQ h22 hd h17 => high22_subcubic_seventeen_impossible G hΔ Q hQ h22 hd h17

/-- 19.5 for candidates excluding twenty-cliques; no extra threshold bounds
remain. Classification and correction for full tight components come later. -/
theorem induced_matching_packing195_of_no_twenty_clique
    (hΔ : ∀ x, G.degree x ≤ 4) (F : Finset G.edgeSet)
    (no20 : ∀ Q : Finset G.edgeSet, Q ⊆ F →
      (conflictGraph G).IsClique (Q : Set G.edgeSet) → Q.card ≤ 19) :
    ∃ M : Finset G.edgeSet, M ⊆ F ∧ IsInducedMatching G (M : Set G.edgeSet) ∧
      2 * F.card ≤ 39 * M.card :=
  induced_matching_packing195_of_clique_bounds G hΔ (cliqueBounds195_of_degree_le_four G hΔ) F no20

end Se20Part.Legacy
