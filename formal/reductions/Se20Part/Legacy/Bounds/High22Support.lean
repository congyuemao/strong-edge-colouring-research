module

public import Se20Part.Legacy.Bounds.High22Local
public import Se20Part.Legacy.Bounds.High23Four

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable [DecidableRel (conflictGraph G).Adj]

theorem high22_root_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).Nonempty) : G.degree r = 4 := by
  obtain ⟨a, ha⟩ := hR
  obtain ⟨_, e, heQ, hea⟩ := mem_filter.mp ha
  exact (high22_endpoints_degree_four G hΔ e hea (h22 e heQ)).1

theorem high22_root_neighborhood_independent
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) :
    G.IsIndepSet (G.neighborSet r) := by
  intro a ha b hb hab hAdj
  change G.Adj r a at ha
  change G.Adj r b at hb
  have hnot (x : V) (hx : x ∈ rootLabels G Q r) : x ≠ a ∧ x ≠ b := by
    obtain ⟨_, e, heQ, hex⟩ := mem_filter.mp hx
    constructor
    · intro hxa
      exact high22_no_triangle_on_edge G hΔ e (by simpa only [hxa] using hex)
        (h22 e heQ) hb hAdj
    · intro hxb
      exact high22_no_triangle_on_edge G hΔ e (by simpa only [hxb] using hex)
        (h22 e heQ) ha hAdj.symm
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

omit [DecidableRel (conflictGraph G).Adj] in
theorem fourCycleOpposites_card_eq_root_load (r a : V) :
    (fourCycleOpposites G r a).card =
      ∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card := by
  have ht (x : V) : (rootType G r x).erase a =
      ((G.neighborFinset r).erase a).filter (G.Adj x) := by
    ext b
    simp [rootType, and_assoc]
  simp only [fourCycleOpposites, ht, card_eq_sum_ones, sum_filter, sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro b hb
  simp only [G.adj_comm b x]

/-- The cross-edge part of the two-loss budget at a selected root label.
Every original neighbour of the label is included, even outside Q's support. -/
theorem high22_root_label_budget_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    {r a : V} (ha : a ∈ rootLabels G Q r) :
    (∑ x ∈ (G.neighborFinset a).erase r, ((rootType G r x).erase a).card) ≤ 2 := by
  obtain ⟨_, e, heQ, he⟩ := mem_filter.mp ha
  rw [← fourCycleOpposites_card_eq_root_load]
  exact high22_at_most_two_four_cycles_on_edge G hΔ e he (h22 e heQ)

theorem high22_root_type_erase_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    {r a x : V} (ha : a ∈ rootLabels G Q r) (hxr : x ≠ r)
    (hax : a ∈ rootType G r x) : ((rootType G r x).erase a).card ≤ 2 := by
  have hx : x ∈ (G.neighborFinset a).erase r := mem_erase.mpr
    ⟨hxr, (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
  exact (single_le_sum (fun y _ => Nat.zero_le _) hx).trans
    (high22_root_label_budget_two G hΔ Q h22 ha)

theorem high22_root_type_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card)
    {x : V} (hxr : x ≠ r) : (rootType G r x).card ≤ 3 := by
  by_contra hn
  obtain ⟨a, ha⟩ := high23_type_meets_root_labels G hΔ Q r x hR (by omega)
  have hcard := card_erase_add_one (mem_inter.mp ha).1
  have hbudget := high22_root_type_erase_card_le_two G hΔ Q h22 (mem_inter.mp ha).2 hxr
    (mem_inter.mp ha).1
  omega

omit [DecidableRel (conflictGraph G).Adj] in
def multipleTips (r : V) : Finset V :=
  univ.filter (fun x => x ≠ r ∧ 2 ≤ (rootType G r x).card)

theorem high22_root_label_multiple_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    {r a : V} (ha : a ∈ rootLabels G Q r) :
    ((multipleTips G r).filter (fun x => a ∈ rootType G r x)).card ≤ 2 := by
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
    (high22_root_label_budget_two G hΔ Q h22 ha))

theorem high22_shared_root_types_card_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    {r a x y : V} (ha : a ∈ rootLabels G Q r)
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hax : a ∈ rootType G r x) (hay : a ∈ rootType G r y) :
    (rootType G r x).card + (rootType G r y).card ≤ 4 := by
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
  have hb := high22_root_label_budget_two G hΔ Q h22 ha
  have hxcard := card_erase_add_one hax
  have hycard := card_erase_add_one hay
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem root_type_card_sum_eq_label_sum (P : Finset V) (r : V) :
    (∑ x ∈ P, (rootType G r x).card) =
      ∑ a ∈ G.neighborFinset r, (P.filter (fun x => a ∈ rootType G r x)).card := by
  classical
  calc
    _ = ∑ x ∈ P, ∑ a ∈ G.neighborFinset r, if G.Adj x a then 1 else 0 := by
      apply sum_congr rfl
      intro x hx
      simp only [rootType, card_eq_sum_ones, sum_filter]
    _ = ∑ a ∈ G.neighborFinset r, ∑ x ∈ P, if G.Adj x a then 1 else 0 := sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      simp only [card_eq_sum_ones, sum_filter]
      apply sum_congr rfl
      intro x hx
      simp only [mem_rootType, (G.mem_neighborFinset r a).mp ha, true_and]

theorem high22_multipleTips_card_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hfull : rootLabels G Q r = G.neighborFinset r) :
    (multipleTips G r).card ≤ 4 := by
  have hl := sum_le_sum (s := multipleTips G r)
    (fun x hx => (mem_filter.mp hx).2.2)
  have hu := sum_le_sum (s := G.neighborFinset r) (fun a ha =>
    high22_root_label_multiple_card_le_two G hΔ Q h22 (hfull.symm ▸ ha))
  have hi := root_type_card_sum_eq_label_sum G (multipleTips G r) r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hl hu
  omega

theorem high22_multipleTips_eq_of_triple
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hfull : rootLabels G Q r = G.neighborFinset r)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card)
    {y : V} (hy : y ∈ multipleTips G r) : y = x := by
  by_contra hxy
  obtain ⟨_, hyr, hycard⟩ := mem_filter.mp hy
  have hc := card_union_add_card_inter (rootType G r x) (rootType G r y)
  have hu := card_le_card (union_subset (filter_subset (G.Adj x) (G.neighborFinset r))
    (filter_subset (G.Adj y) (G.neighborFinset r)))
  change (rootType G r x ∪ rootType G r y).card ≤ (G.neighborFinset r).card at hu
  have hd := hΔ r
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hu
  have hpos : 0 < (rootType G r x ∩ rootType G r y).card := by omega
  obtain ⟨a, ha⟩ := card_pos.mp hpos
  obtain ⟨hax, hay⟩ := mem_inter.mp ha
  have haR : a ∈ rootLabels G Q r := hfull.symm ▸ (filter_subset _ _ hax)
  have hb := high22_shared_root_types_card_le_four G hΔ Q h22 haR hxr hyr (Ne.symm hxy) hax hay
  omega

end Se20Part.Legacy

