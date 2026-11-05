module

public import Se20Part.Legacy.Basic

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {W : Type*} [Fintype W] [DecidableEq W]
variable (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The secondary objective uses degrees in the entire current graph. -/
def degreeSum (M : Finset W) : ℕ := ∑ v ∈ M, H.degree v

/-- A maximum independent set minimizing its sum of ambient degrees. -/
def IsOptimal (M : Finset W) : Prop :=
  H.IsMaximumIndepSet M ∧
    ∀ T : Finset W, H.IsMaximumIndepSet T → degreeSum H M ≤ degreeSum H T

omit [DecidableEq W] in
theorem optimal_exists : ∃ M : Finset W, IsOptimal H M := by
  classical
  let S : Finset (Finset W) := univ.filter (fun M => H.IsMaximumIndepSet M)
  obtain ⟨M₀, hM₀⟩ := H.maximumIndepSet_exists
  have hS : S.Nonempty := ⟨M₀, by simp [S, hM₀]⟩
  obtain ⟨M, hM, hmin⟩ := S.exists_min_image (degreeSum H) hS
  refine ⟨M, (mem_filter.mp hM).2, ?_⟩
  intro T hT
  exact hmin T (by simp [S, hT])

omit [Fintype W] [DecidableRel H.Adj] in
/-- Replacing a centre by one of its private vertices preserves independence. -/
theorem private_swap_independent (M : Finset W) {v x : W}
    (hM : H.IsIndepSet (M : Set W)) (hx : IsPrivate H M v x) :
    H.IsIndepSet (↑(insert x (M.erase v)) : Set W) := by
  intro a ha b hb hab
  change a ∈ insert x (M.erase v) at ha
  change b ∈ insert x (M.erase v) at hb
  simp only [mem_insert, mem_erase] at ha hb
  rcases ha with rfl | ⟨hav, haM⟩
  · rcases hb with rfl | ⟨hbv, hbM⟩
    · exact (hab rfl).elim
    · exact (hx.2 b hbM hbv).2
  · rcases hb with rfl | ⟨hbv, hbM⟩
    · intro hax
      exact (hx.2 a haM hav).2 (H.adj_symm hax)
    · exact hM haM hbM hab

/-- Every private vertex has at least the ambient degree of its centre. -/
theorem private_degree_mono (M : Finset W) (hM : IsOptimal H M)
    {v x : W} (hv : v ∈ M) (hx : IsPrivate H M v x) :
    H.degree v ≤ H.degree x := by
  classical
  by_cases hxv : x = v
  · subst x
    exact le_rfl
  have hxout : x ∉ M := fun h => (hx.2 x h hxv).1 rfl
  have hxerase : x ∉ M.erase v := fun h => hxout (mem_erase.mp h).2
  let T := insert x (M.erase v)
  have hcard : T.card = M.card := by
    dsimp [T]
    rw [card_insert_of_notMem hxerase, card_erase_add_one hv]
  have hT : H.IsMaximumIndepSet T := by
    refine ⟨private_swap_independent H M hM.1.isIndepSet hx, ?_⟩
    intro U hU
    rw [hcard]
    exact hM.1.maximum U hU
  have hmin := hM.2 T hT
  have hsumT : degreeSum H T = degreeSum H (M.erase v) + H.degree x := by
    simp [degreeSum, T, hxerase, add_comm]
  have hsumM : degreeSum H (M.erase v) + H.degree v = degreeSum H M := by
    exact sum_erase_add _ _ hv
  omega

end Se20Part.Legacy
