module

public import Se20Part.Legacy.Bounds.High21Local
public import Se20Part.Legacy.Bounds.High22Support
public import Se20Part.Legacy.Bounds.High23Four

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high21_root_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).Nonempty) : G.degree r = 4 := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨_, e, heQ, hea⟩ := mem_filter.mp ha
  exact (high21_endpoints_degree_four G hΔ e hea (h21 e heQ)).1

theorem high21_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) :
    G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb hab hAdj
  change G.Adj r a at ha
  change G.Adj r b at hb
  have hnot (x : V) (hx : x ∈ rootLabels G Q r) : x ≠ a ∧ x ≠ b := by
    obtain ⟨_, e, heQ, hex⟩ := mem_filter.mp hx
    constructor
    · intro hxa
      exact high21_no_triangle_on_edge G hΔ e (by simpa only [hxa] using hex)
        (h21 e heQ) hb hAdj
    · intro hxb
      exact high21_no_triangle_on_edge G hΔ e (by simpa only [hxb] using hex)
        (h21 e heQ) ha hAdj.symm
  have hs : rootLabels G Q r ⊆ ((G.neighborFinset r).erase a).erase b := by
    intro x hx
    exact mem_erase.mpr ⟨(hnot x hx).2, mem_erase.mpr ⟨(hnot x hx).1,
      rootLabels_subset_neighbors G Q r hx⟩⟩
  have hc := card_le_card hs
  have hca := card_erase_add_one ((G.mem_neighborFinset r a).mpr ha)
  have hcb := card_erase_add_one (mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset r b).mpr hb⟩)
  have hd := hΔ r
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
  omega

/-- The cross-edge part of the three-loss budget at a selected root label.
Every original neighbour of the label is included, even outside Q's support. -/
theorem high21_root_label_budget_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r a : V} (ha : a ∈ rootLabels G Q r) :
    (∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card) ≤ 3 := by
  obtain ⟨_, e, heQ, he⟩ := mem_filter.mp ha
  rw [← fourCycleOpposites_card_eq_root_load]
  exact high21_at_most_three_four_cycles_on_edge G hΔ e he (h21 e heQ)

theorem high21_root_type_erase_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r a x : V} (ha : a ∈ rootLabels G Q r) (hxr : x ≠ r)
    (hax : a ∈ rootType G r x) : ((rootType G r x).erase a).card ≤ 3 := by
  have hx : x ∈ (G.neighborFinset a).erase r := mem_erase.mpr
    ⟨hxr, (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  exact (single_le_sum (fun y _ => Nat.zero_le _) hx).trans
    (high21_root_label_budget_three G hΔ Q h21 ha)

theorem high21_root_label_multiple_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r a : V} (ha : a ∈ rootLabels G Q r) :
    ((multipleTips G r).filter (fun x => a ∈ rootType G r x)).card ≤ 3 := by
  classical
  let S := (multipleTips G r).filter (fun x => a ∈ rootType G r x)
  have hs : S ⊆ (G.neighborFinset a).erase r := by
    intro x hx
    obtain ⟨hxP, hax⟩ := mem_filter.mp hx
    exact mem_erase.mpr ⟨(mem_filter.mp hxP).2.1,
      (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hle : S.card ≤ ∑ x ∈ S, ((rootType G r x).erase a).card := by
    calc
      S.card = ∑ _x ∈ S, 1 := card_eq_sum_ones S
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        obtain ⟨hxP, hax⟩ := mem_filter.mp hx
        have ht := (mem_filter.mp hxP).2.2
        have hc := card_erase_add_one hax
        omega
  exact hle.trans ((sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)).trans
    (high21_root_label_budget_three G hΔ Q h21 ha))

theorem high21_shared_root_types_card_le_five
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r a x y : V} (ha : a ∈ rootLabels G Q r)
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hax : a ∈ rootType G r x) (hay : a ∈ rootType G r y) :
    (rootType G r x).card + (rootType G r y).card ≤ 5 := by
  have hx : x ∈ (G.neighborFinset a).erase r := mem_erase.mpr
    ⟨hxr, (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  have hy : y ∈ (G.neighborFinset a).erase r := mem_erase.mpr
    ⟨hyr, (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
  have hs : ({x, y} : Finset V) ⊆ (G.neighborFinset a).erase r := by
    intro z hz
    rcases mem_insert.mp hz with h | h
    · exact h ▸ hx
    · exact (mem_singleton.mp h) ▸ hy
  have hc := sum_le_sum_of_subset_of_nonneg (f := fun z => ((rootType G r z).erase a).card)
    hs (fun _ _ _ => Nat.zero_le _)
  simp only [sum_pair hxy] at hc
  have hb := high21_root_label_budget_three G hΔ Q h21 ha
  have hxcard := card_erase_add_one hax
  have hycard := card_erase_add_one hay
  omega

theorem high21_multipleTips_card_le_six
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    (r : V) (hfull : rootLabels G Q r = G.neighborFinset r) :
    (multipleTips G r).card ≤ 6 := by
  have hl := sum_le_sum (s := multipleTips G r)
    (fun x hx => (mem_filter.mp hx).2.2)
  have hu := sum_le_sum (s := G.neighborFinset r) (fun a ha =>
    high21_root_label_multiple_card_le_three G hΔ Q h21 (hfull.symm ▸ ha))
  have hi := root_type_card_sum_eq_label_sum G (multipleTips G r) r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hl hu
  omega

end Se20Part.Legacy
