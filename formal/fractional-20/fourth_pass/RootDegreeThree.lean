import third_pass.FiniteReduction14

namespace Se20Fractional.FourthPass
open Finset DReduction ThirdPass
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem tip_sum_le_three_degree (hΔ : ∀ v, G.degree v ≤ 4) (r : V)
    (U : Finset V) (hr : r ∉ U) :
    ∑ x ∈ U, (tip G r x).card ≤ 3 * G.degree r := by
  have heq : ∑ x ∈ U, (tip G r x).card =
      ∑ a ∈ G.neighborFinset r, (U.filter (fun x => G.Adj a x)).card := by
    have ht (x : V) : (tip G r x).card =
        ∑ a ∈ G.neighborFinset r, if G.Adj a x then 1 else 0 := by
      rw [← card_filter]
      congr 1
      ext a
      simp [tip, G.adj_comm, and_comm]
    simp_rw [ht, card_filter]
    exact sum_comm
  rw [heq]
  have hb : ∀ a ∈ G.neighborFinset r, (U.filter (fun x => G.Adj a x)).card ≤ 3 := by
    intro a ha
    have hs : U.filter (fun x => G.Adj a x) ⊆ (G.neighborFinset a).erase r := by
      intro x hx
      obtain ⟨hxU,hax⟩ := mem_filter.mp hx
      exact mem_erase.mpr ⟨fun h => hr (h ▸ hxU), (G.mem_neighborFinset a x).mpr hax⟩
    have hc := card_le_card hs
    have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr
      ((G.mem_neighborFinset r a).mp ha).symm)
    have hd := hΔ a
    rw [SimpleGraph.card_neighborFinset_eq_degree] at he
    omega
  have hs := sum_le_sum hb
  simpa only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree,
    Nat.mul_comm] using hs

theorem type_budget_degree (hΔ : ∀ v, G.degree v ≤ 4) (Q : Finset G.edgeSet) (r : V) :
    (outerSupport Q r).card + excess Q r ≤ 3 * G.degree r + (zeroTips Q r).card := by
  have hi := type_identity Q r
  have hr : r ∉ outerSupport Q r := by simp [outerSupport]
  have ht := tip_sum_le_three_degree hΔ r (outerSupport Q r) hr
  omega

/-- A degree-three root with at least three selected edges has at most six
outer endpoints when its neighbourhood is independent. No local assumption. -/
theorem degree_three_independent_outer_le_six (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hq : 16 ≤ Q.card)
    {r : V} (hs : 3 ≤ (labels Q r).card) (hd : G.degree r = 3)
    (hA : ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b) :
    (outerSupport Q r).card ≤ 6 := by
  have hp := root_partition_bound Q r hA
  have ht := type_budget_degree hΔ Q r
  have htr := triple_budget Q r
  have hz := zero_le_triple hΔ Q hQ hs
  have ho := outer_budget hΔ Q hQ hs
  have hsl : (labels Q r).card ≤ 3 :=
    (card_le_card (filter_subset _ _)).trans (by simpa [hd])
  by_cases hsingle : ∃ x ∈ selectedTips Q r, (tip G r x).card = 1
  · obtain ⟨x,hx,hxt⟩ := hsingle
    have hb := single_tip_bound hΔ Q hQ hA hx hxt
    have hk := cross_budget Q r
    omega
  · have hk := cross_budget_no_single Q r (by
      intro x hx hxt
      exact hsingle ⟨x,hx,hxt⟩)
    omega

theorem degree_three_independent_endpoint_le_ten (hΔ : ∀ v, G.degree v ≤ 4)
    (Q : Finset G.edgeSet) (hQ : Clique (L2 G) Q) (hq : 16 ≤ Q.card)
    {r : V} (hs : 3 ≤ (labels Q r).card) (hd : G.degree r = 3)
    (hA : ∀ a b, G.Adj r a → G.Adj r b → ¬ G.Adj a b) :
    (endpoints Q).card ≤ 10 := by
  have ho := degree_three_independent_outer_le_six hΔ Q hQ hq hs hd hA
  have hc := card_sdiff_add_card_inter (endpoints Q) (insert r (G.neighborFinset r))
  have hi := card_le_card (inter_subset_right :
    endpoints Q ∩ insert r (G.neighborFinset r) ⊆ insert r (G.neighborFinset r))
  have hn := card_insert_le r (G.neighborFinset r)
  rw [SimpleGraph.card_neighborFinset_eq_degree, hd] at hn
  change (endpoints Q \ insert r (G.neighborFinset r)).card ≤ 6 at ho
  omega

#print axioms degree_three_independent_endpoint_le_ten
end Se20Fractional.FourthPass
