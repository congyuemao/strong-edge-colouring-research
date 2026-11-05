import Se20Part.Recolour
import Se20Part.ConflictBounds

noncomputable section
open scoped Classical
namespace Se20Part

/-- Equality in the finite union bound forces disjointness. -/
theorem disjoint_of_card_biUnion_eq_sum {I X : Type*} [DecidableEq X]
    (s : Finset I) (t : I → Finset X)
    (heq : (s.biUnion t).card = ∑ i ∈ s, (t i).card) :
    (s : Set I).PairwiseDisjoint t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha] at heq
    have hle : (s.biUnion t).card ≤ ∑ i ∈ s, (t i).card := Finset.card_biUnion_le
    have hcu := Finset.card_union_add_card_inter (t a) (s.biUnion t)
    have hinter : (t a ∩ s.biUnion t).card = 0 := by omega
    have hrest : (s.biUnion t).card = ∑ i ∈ s, (t i).card := by omega
    have hdisj : Disjoint (t a) (s.biUnion t) := Finset.disjoint_iff_inter_eq_empty.mpr
      (Finset.card_eq_zero.mp hinter)
    intro i hi j hj hij
    rcases Finset.mem_insert.mp hi with rfl | his
    · have hjs : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hij.symm
      exact hdisj.mono_right (Finset.subset_biUnion_of_mem (s := s) t hjs)
    · rcases Finset.mem_insert.mp hj with rfl | hjs
      · exact (hdisj.mono_right (Finset.subset_biUnion_of_mem (s := s) t his)).symm
      · exact ih hrest his hjs hij

namespace PartialColouring
variable {W : Type*} {H : SimpleGraph W} {F : Finset W}

/-- If at most 20 neighbours cover 20 colours, all are coloured and distinct. -/
theorem saturated_twenty (φ : PartialColouring H F) (N : Finset W) (e : W)
    (hN : ∀ x, x ∈ N ↔ H.Adj e x) (hcard : N.card ≤ 20)
    (hblocked : ∀ c, ∃ x, φ.Neighbour e c x) :
    N.card = 20 ∧ (∀ x ∈ N, x ∈ F) ∧ Set.InjOn φ.colour N := by
  let S := N.filter (· ∈ F)
  have himage : S.image φ.colour = Finset.univ := by
    ext c
    simp only [Finset.mem_univ, iff_true]
    obtain ⟨x, hx, hex, hxc⟩ := hblocked c
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨(hN x).mpr hex, hx⟩, hxc⟩
  have hS : 20 ≤ S.card := by
    have := Finset.card_image_le (s := S) (f := φ.colour)
    simpa [himage] using this
  have hSN : S = N := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (hcard.trans hS)
  have hNcard : N.card = 20 := by rw [hSN] at hS; omega
  refine ⟨hNcard, ?_, ?_⟩
  · intro x hx
    rw [← hSN] at hx
    exact (Finset.mem_filter.mp hx).2
  · apply Finset.card_image_iff.mp
    rw [hSN] at himage
    simp [himage, hNcard]


end PartialColouring
end Se20Part
