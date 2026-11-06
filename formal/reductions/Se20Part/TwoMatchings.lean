import Se20Part.Residual
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part

private theorem cycle_degree_two (n : ℕ) (hn : 3 ≤ n) (i : Fin n) :
    (SimpleGraph.cycleGraph n).degree i = 2 := by
  match n with
  | 0 | 1 | 2 => omega
  | n+3 => exact SimpleGraph.cycleGraph_degree_three_le

/-- A connected union of two matchings is a path or an even cycle.
Shared matching edges are allowed. -/
theorem connected_union_two_matchings_colourable {W : Type*} [Fintype W]
    (H A B : SimpleGraph W) (hc : H.Connected)
    (hcover : ∀ x y, H.Adj x y ↔ A.Adj x y ∨ B.Adj x y)
    (hA : ∀ x, A.degree x ≤ 1) (hB : ∀ x, B.degree x ≤ 1) : H.Colorable 2 := by
  have hbound : ∀ x, H.degree x ≤ A.degree x + B.degree x := by
    intro x
    have heq : H.neighborFinset x = A.neighborFinset x ∪ B.neighborFinset x := by
      ext y
      simpa only [SimpleGraph.mem_neighborFinset,Finset.mem_union] using hcover x y
    have hh := Finset.card_union_le (A.neighborFinset x) (B.neighborFinset x)
    rw [← heq] at hh
    simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hh
  have hΔ : ∀ x, H.degree x ≤ 2 := by
    intro x
    have := hbound x
    have := hA x
    have := hB x
    omega
  obtain ⟨P⟩ := exists_pathCycleOrder H hc hΔ
  by_contra hn
  obtain ⟨hp,ho⟩ := P.nonbipartite_closed_odd hn
  have hreg : ∀ x, H.degree x = 2 := by
    intro x
    have hh := (P.cycleIso hp).symm.degree_eq x
    have hc' := cycle_degree_two P.size (P.closed_size hp) ((P.cycleIso hp).symm x)
    simp only [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hh hc' ⊢
    exact hh.symm.trans hc'
  have hAone : ∀ x, A.degree x = 1 := by
    intro x
    have := hbound x
    have := hA x
    have := hB x
    have := hreg x
    omega
  have heven : Even (Fintype.card W) := by
    have hh := A.even_card_odd_degree_vertices
    have heq : Finset.univ.filter (fun v => Odd (A.degree v)) = (Finset.univ : Finset W) := by
      ext v
      norm_num [hAone]
    rw [heq,Finset.card_univ] at hh
    exact hh
  rw [P.card_size] at heven
  exact (Nat.not_even_iff_odd.mpr ho) heven

/-- The simultaneous assignment engine of S17. It proves the abstract
two-matching step; the geometric O9/thirteen-vertex partner relations must
still be shown to satisfy its hypotheses. -/
theorem union_two_matchings_colourable {W : Type*} [Fintype W]
    (A B : SimpleGraph W) (hA : ∀ x, A.degree x ≤ 1) (hB : ∀ x, B.degree x ≤ 1) :
    (A ⊔ B).Colorable 2 := by
  let H := A ⊔ B
  apply colourable_of_separated_fibres H H.connectedComponentMk 2
  · intro x y hxy
    exact SimpleGraph.ConnectedComponent.sound hxy.reachable
  · intro K
    have hc : K.toSimpleGraph.Colorable 2 :=
      connected_union_two_matchings_colourable K.toSimpleGraph (A.induce K.supp) (B.induce K.supp)
        K.connected_toSimpleGraph (fun _ _ => Iff.rfl)
        (fun x => (degree_induce_le A K.supp x).trans (hA x.val))
        (fun x => (degree_induce_le B K.supp x).trans (hB x.val))
    let f : H.induce {x | H.connectedComponentMk x = K} →g K.toSimpleGraph :=
      { toFun := fun x => ⟨x.val,(K.mem_supp_iff _).mpr x.prop⟩
        map_rel' := fun h => h }
    exact ⟨hc.some.comap f⟩

theorem two_matchings_simultaneous_assignment {W : Type*} [Fintype W]
    (A B : SimpleGraph W) (hA : ∀ x, A.degree x ≤ 1) (hB : ∀ x, B.degree x ≤ 1) :
    ∃ p : W → Fin 2,
      (∀ x y, A.Adj x y → ¬ (p x = 0 ∧ p y = 0)) ∧
      (∀ x y, B.Adj x y → ¬ (p x = 1 ∧ p y = 1)) := by
  obtain ⟨c⟩ := union_two_matchings_colourable A B hA hB
  exact ⟨c,(fun _ _ h hh => c.valid (Or.inl h) (hh.1.trans hh.2.symm)),
    fun _ _ h hh => c.valid (Or.inr h) (hh.1.trans hh.2.symm)⟩

end Se20Part
