module

public import Se20Part.Legacy.Bounds.High22RootFour

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def labelHeavyTips (Q : Finset G.edgeSet) (r : V) : Finset V :=
  univ.filter (fun x => x ≠ r ∧ 2 ≤ (rootType G r x ∩ rootLabels G Q r).card)

theorem labelHeavyTips_subset_multiple (Q : Finset G.edgeSet) (r : V) :
    labelHeavyTips G Q r ⊆ multipleTips G r := by
  intro x hx
  obtain ⟨_, hxr, hc⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨mem_univ _, hxr, hc.trans (card_le_card inter_subset_left)⟩

theorem root_type_inter_card_sum (P R : Finset V) (r : V) :
    (∑ x ∈ P, (rootType G r x ∩ R).card) =
      ∑ a ∈ R, (P.filter (fun x => a ∈ rootType G r x)).card := by
  classical
  have he (x : V) : rootType G r x ∩ R = R.filter (fun a => a ∈ rootType G r x) := by
    ext a
    simp only [mem_inter, mem_filter, and_comm]
  simp only [he, card_eq_sum_ones, sum_filter]
  exact sum_comm

theorem outerEdges_meet_labelHeavyTips
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card)
    (e : G.edgeSet) (heo : e ∈ outerEdges G Q r) :
    ∃ x ∈ labelHeavyTips G Q r, x ∈ e.val := by
  obtain ⟨x, y, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hends := outerEdges_endpoints G Q r e he.symm heo
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e he.symm heo
  have hs : rootLabels G Q r ⊆ (rootType G r x ∩ rootLabels G Q r) ∪
      (rootType G r y ∩ rootLabels G Q r) := by
    intro a ha
    rcases mem_union.mp (hcov ha) with hx | hy
    · exact mem_union_left _ (mem_inter.mpr ⟨hx, ha⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hy, ha⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  by_cases hx : 2 ≤ (rootType G r x ∩ rootLabels G Q r).card
  · exact ⟨x, mem_filter.mpr ⟨mem_univ _, hends.2.1, hx⟩, he ▸ Sym2.mem_mk_left x y⟩
  · exact ⟨y, mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩, he ▸ Sym2.mem_mk_right x y⟩

variable [DecidableRel (conflictGraph G).Adj]

theorem high22_heavy_label_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    {r a : V} (ha : a ∈ rootLabels G Q r) :
    ((labelHeavyTips G Q r).filter (fun x => a ∈ rootType G r x)).card ≤ 2 := by
  have hs : (labelHeavyTips G Q r).filter (fun x => a ∈ rootType G r x) ⊆
      (multipleTips G r).filter (fun x => a ∈ rootType G r x) := by
    intro x hx
    obtain ⟨hxp, hax⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨labelHeavyTips_subset_multiple G Q r hxp, hax⟩
  exact (card_le_card hs).trans (high22_root_label_multiple_card_le_two G hΔ Q h22 ha)

theorem high22_labelHeavyTips_card_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 3) :
    (labelHeavyTips G Q r).card ≤ 3 := by
  have hlo := sum_le_sum (s := labelHeavyTips G Q r) (fun x hx => (mem_filter.mp hx).2.2)
  have hup := sum_le_sum (s := rootLabels G Q r)
    (fun a ha => high22_heavy_label_card_le_two G hΔ Q h22 ha)
  have heq := root_type_inter_card_sum G (labelHeavyTips G Q r) (rootLabels G Q r) r
  simp only [sum_const, smul_eq_mul, hR] at hlo hup
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem high22_outer_incidence_le_two_at_heavy
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V)
    {x : V} (hx : x ∈ labelHeavyTips G Q r) :
    (edgeIncidences G (outerEdges G Q r) x).card ≤ 2 := by
  have hm := labelHeavyTips_subset_multiple G Q r hx
  have hc := (mem_filter.mp hm).2.2
  have hi := outer_incidence_add_type_card_le_degree G Q r x
  have hd := hΔ x
  omega

theorem high22_outer_card_le_six_of_root_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 3) :
    (outerEdges G Q r).card ≤ 6 := by
  have hm : edgesMeeting G (outerEdges G Q r) (labelHeavyTips G Q r) = outerEdges G Q r := by
    apply filter_eq_self.mpr
    exact outerEdges_meet_labelHeavyTips G Q hQ r (by omega)
  have hi := incidence_sum_eq_meeting_add_inside G (outerEdges G Q r) (labelHeavyTips G Q r)
  rw [hm] at hi
  have hs := sum_le_sum (s := labelHeavyTips G Q r)
    (fun x hx => high22_outer_incidence_le_two_at_heavy G hΔ Q r hx)
  have hc := high22_labelHeavyTips_card_le_three G hΔ Q h22 r hR
  simp only [sum_const, smul_eq_mul] at hs
  omega

theorem high22_heavy_card_and_degree_of_outer_six
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 3)
    (ho : (outerEdges G Q r).card = 6) :
    (labelHeavyTips G Q r).card = 3 ∧
      ∀ x ∈ labelHeavyTips G Q r, (edgeIncidences G (outerEdges G Q r) x).card = 2 := by
  have hm : edgesMeeting G (outerEdges G Q r) (labelHeavyTips G Q r) = outerEdges G Q r := by
    apply filter_eq_self.mpr
    exact outerEdges_meet_labelHeavyTips G Q hQ r (by omega)
  have hi := incidence_sum_eq_meeting_add_inside G (outerEdges G Q r) (labelHeavyTips G Q r)
  rw [hm] at hi
  have hs := sum_le_sum (s := labelHeavyTips G Q r)
    (fun x hx => high22_outer_incidence_le_two_at_heavy G hΔ Q r hx)
  have hc := high22_labelHeavyTips_card_le_three G hΔ Q h22 r hR
  simp only [sum_const, smul_eq_mul] at hs
  refine ⟨by omega, ?_⟩
  intro x hx
  have hxc := high22_outer_incidence_le_two_at_heavy G hΔ Q r hx
  have he := sum_erase_add (labelHeavyTips G Q r)
    (fun y => (edgeIncidences G (outerEdges G Q r) y).card) hx
  have hce := card_erase_add_one hx
  have hse := sum_le_sum (s := (labelHeavyTips G Q r).erase x)
    (fun y hy => high22_outer_incidence_le_two_at_heavy G hΔ Q r (mem_erase.mp hy).2)
  simp only [sum_const, smul_eq_mul] at hse
  omega

theorem high22_heavy_label_card_eq_two_of_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 3)
    (hp : (labelHeavyTips G Q r).card = 3)
    {a : V} (ha : a ∈ rootLabels G Q r) :
    ((labelHeavyTips G Q r).filter (fun x => a ∈ rootType G r x)).card = 2 := by
  have hlo := sum_le_sum (s := labelHeavyTips G Q r) (fun x hx => (mem_filter.mp hx).2.2)
  have heq := root_type_inter_card_sum G (labelHeavyTips G Q r) (rootLabels G Q r) r
  have hb := high22_heavy_label_card_le_two G hΔ Q h22 ha
  have he := sum_erase_add (rootLabels G Q r)
    (fun b => ((labelHeavyTips G Q r).filter (fun x => b ∈ rootType G r x)).card) ha
  have hce := card_erase_add_one ha
  have hse := sum_le_sum (s := (rootLabels G Q r).erase a)
    (fun b hb => high22_heavy_label_card_le_two G hΔ Q h22 (mem_erase.mp hb).2)
  simp only [sum_const, smul_eq_mul, hp] at hlo hse
  omega

theorem high22_multiple_subset_heavy_of_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h22 : ∀ e ∈ Q, 22 ≤ (conflictGraph G).degree e)
    (r : V) (hR : (rootLabels G Q r).card = 3)
    (hp : (labelHeavyTips G Q r).card = 3) :
    multipleTips G r ⊆ labelHeavyTips G Q r := by
  intro x hx
  obtain ⟨a, ha⟩ := high23_type_meets_root_labels G hΔ Q r x (by omega) (mem_filter.mp hx).2.2
  obtain ⟨haT, haR⟩ := mem_inter.mp ha
  have heq : (labelHeavyTips G Q r).filter (fun y => a ∈ rootType G r y) =
      (multipleTips G r).filter (fun y => a ∈ rootType G r y) := by
    apply eq_of_subset_of_card_le
    · intro y hy
      obtain ⟨hyp, hay⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨labelHeavyTips_subset_multiple G Q r hyp, hay⟩
    · rw [high22_heavy_label_card_eq_two_of_three G hΔ Q h22 r hR hp haR]
      exact high22_root_label_multiple_card_le_two G hΔ Q h22 haR
  exact (mem_filter.mp (heq.symm ▸ mem_filter.mpr ⟨hx, haT⟩)).1

end Se20Part.Legacy
