module

public import Se20Part.Legacy.Bounds.High23Support

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Selected edges entirely outside the closed neighbourhood of the root. -/
def outerEdges (Q : Finset G.edgeSet) (r : V) : Finset G.edgeSet :=
  Q.filter (fun e => r ∉ e.val ∧ ∀ w ∈ e.val, ¬ G.Adj r w)

theorem outerEdges_endpoints (Q : Finset G.edgeSet) (r : V)
    {x y : V} (e : G.edgeSet) (he : e.val = s(x, y))
    (h : e ∈ outerEdges G Q r) :
    e ∈ Q ∧ x ≠ r ∧ y ≠ r ∧ ¬ G.Adj r x ∧ ¬ G.Adj r y := by
  obtain ⟨hQ, hr, hn⟩ := mem_filter.mp h
  rw [he, Sym2.mem_iff, not_or] at hr
  rw [he, Sym2.forall_mem_pair] at hn
  exact ⟨hQ, Ne.symm hr.1, Ne.symm hr.2, hn.1, hn.2⟩

theorem outer_edge_types_cover_root_labels
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) {x y : V} (e : G.edgeSet) (he : e.val = s(x, y))
    (heo : e ∈ outerEdges G Q r) :
    rootLabels G Q r ⊆ rootType G r x ∪ rootType G r y := by
  obtain ⟨heQ, hr, hout⟩ := mem_filter.mp heo
  intro a ha
  obtain ⟨haN, f, hfQ, hf⟩ := mem_filter.mp ha
  have hfe : f ≠ e := by
    intro h
    apply hr
    rw [← h, hf]
    exact Sym2.mem_mk_left _ _
  obtain ⟨w, hw, hwe⟩ := strongConflict_meets_cover G hf (hQ hfQ heQ hfe)
  have haw : G.Adj a w := by
    rcases mem_union.mp hw with h | h
    · exact (hout w hwe ((G.mem_neighborFinset r w).mp (mem_erase.mp h).2)).elim
    · exact (G.mem_neighborFinset a w).mp (mem_erase.mp h).2
  have hra := (G.mem_neighborFinset r a).mp haN
  rw [he, Sym2.mem_iff] at hwe
  rcases hwe with h | h
  · exact mem_union_left _ ((mem_rootType G r x a).mpr ⟨hra, (h ▸ haw).symm⟩)
  · exact mem_union_right _ ((mem_rootType G r y a).mpr ⟨hra, (h ▸ haw).symm⟩)

variable [DecidableRel (conflictGraph G).Adj]

/-- A vertex with two root Q labels is incident to every outer Q edge. -/
theorem high23_outer_edges_incident_double_root
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card)
    {p a b : V} (hpr : p ≠ r)
    (ha : a ∈ rootLabels G Q r) (hb : b ∈ rootLabels G Q r) (hab : a ≠ b)
    (hpa : a ∈ rootType G r p) (hpb : b ∈ rootType G r p)
    (f : G.edgeSet) (hfo : f ∈ outerEdges G Q r) : p ∈ f.val := by
  by_contra hpf
  obtain ⟨x, y, hf⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = f.val from ⟨f.val, rfl⟩)
  have hends := outerEdges_endpoints G Q r f hf.symm hfo
  have hcov := outer_edge_types_cover_root_labels G Q hQ r f hf.symm hfo
  have hpx : p ≠ x := by
    intro h
    apply hpf
    rw [← hf, h]
    exact Sym2.mem_mk_left _ _
  have hpy : p ≠ y := by
    intro h
    apply hpf
    rw [← hf, h]
    exact Sym2.mem_mk_right _ _
  have hp2 : 2 ≤ (rootType G r p).card := by
    have := one_lt_card.mpr ⟨a, hpa, b, hpb, hab⟩
    omega
  have impossible {X Y : Finset V} (hX : X = {a}) (hY : Y = {b})
      (hc : rootLabels G Q r ⊆ X ∪ Y) : False := by
    have hcard := card_le_card hc
    have hu := card_union_le X Y
    simp only [hX, hY, card_singleton] at hu hcard
    omega
  rcases mem_union.mp (hcov ha) with hax | hay
  · have hx := high23_type_singleton_of_sharing_double G hΔ Q h23 ha hpr hends.2.1 hpx hpa hax hp2
    have hby : b ∈ rootType G r y := by
      rcases mem_union.mp (hcov hb) with hbx | hby
      · have hba : b = a := by simpa only [hx, mem_singleton] using hbx
        exact (hab hba.symm).elim
      · exact hby
    have hy := high23_type_singleton_of_sharing_double G hΔ Q h23 hb hpr hends.2.2.1 hpy hpb hby hp2
    exact impossible hx hy hcov
  · have hy := high23_type_singleton_of_sharing_double G hΔ Q h23 ha hpr hends.2.2.1 hpy hpa hay hp2
    have hbx : b ∈ rootType G r x := by
      rcases mem_union.mp (hcov hb) with hbx | hby
      · exact hbx
      · have hba : b = a := by simpa only [hy, mem_singleton] using hby
        exact (hab hba.symm).elim
    have hx := high23_type_singleton_of_sharing_double G hΔ Q h23 hb hpr hends.2.1 hpx hpb hbx hp2
    exact impossible hy hx (by simpa only [union_comm] using hcov)

theorem high23_outer_card_le_two_of_double_root_type
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card)
    {p : V} (hpr : p ≠ r)
    (hp : 2 ≤ (rootType G r p ∩ rootLabels G Q r).card) :
    (outerEdges G Q r).card ≤ 2 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp
    (show 1 < (rootType G r p ∩ rootLabels G Q r).card by omega)
  obtain ⟨hpa, haR⟩ := mem_inter.mp ha
  obtain ⟨hpb, hbR⟩ := mem_inter.mp hb
  have hpa' := (mem_rootType G r p a).mp hpa
  have hpb' := (mem_rootType G r p b).mp hpb
  have hcard : (outerEdges G Q r).card ≤ ((G.neighborFinset p).erase a |>.erase b).card := by
    apply card_le_via_relation _ _ (fun f y => f.val = s(p, y))
    · intro f hf
      have hpf := high23_outer_edges_incident_double_root G hΔ Q hQ h23 r hR hpr haR hbR hab hpa hpb f hf
      obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hpf
      have hpy : G.Adj p y := G.mem_edgeSet.mp (hy ▸ f.property)
      have hry : ¬ G.Adj r y := (mem_filter.mp hf).2.2 y (hy.symm ▸ Sym2.mem_mk_right p y)
      have hya : y ≠ a := fun h => hry (h.symm ▸ hpa'.1)
      have hyb : y ≠ b := fun h => hry (h.symm ▸ hpb'.1)
      exact ⟨y, mem_erase.mpr ⟨hyb, mem_erase.mpr ⟨hya, (G.mem_neighborFinset p y).mpr hpy⟩⟩, hy⟩
    · intro f hf f' hf' y hfy hf'y
      exact Subtype.ext (hfy.trans hf'y.symm)
  have hca := card_erase_add_one ((G.mem_neighborFinset p a).mpr hpa'.2)
  have hcb := card_erase_add_one (mem_erase.mpr ⟨hab.symm, (G.mem_neighborFinset p b).mpr hpb'.2⟩)
  have hd := hΔ p
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
  omega

theorem high23_outer_edges_card_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) :
    (outerEdges G Q r).card ≤ 2 := by
  by_cases ho : outerEdges G Q r = ∅
  · simp [ho]
  obtain ⟨e, heo⟩ := nonempty_iff_ne_empty.mpr ho
  obtain ⟨x, y, he⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have hends := outerEdges_endpoints G Q r e he.symm heo
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e he.symm heo
  have hs : rootLabels G Q r ⊆
      (rootType G r x ∩ rootLabels G Q r) ∪ (rootType G r y ∩ rootLabels G Q r) := by
    intro a ha
    rcases mem_union.mp (hcov ha) with hx | hy
    · exact mem_union_left _ (mem_inter.mpr ⟨hx, ha⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hy, ha⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  by_cases hx : 2 ≤ (rootType G r x ∩ rootLabels G Q r).card
  · exact high23_outer_card_le_two_of_double_root_type G hΔ Q hQ h23 r hR hends.2.1 hx
  · exact high23_outer_card_le_two_of_double_root_type G hΔ Q hQ h23 r hR hends.2.2.1 (by omega)

omit [DecidableRel (conflictGraph G).Adj] in
theorem selected_edges_card_le_meeting_add_outer (Q : Finset G.edgeSet) (r : V) :
    Q.card ≤ (edgesMeeting G Q (G.neighborFinset r)).card + (outerEdges G Q r).card := by
  classical
  have hs : Q ⊆ edgesMeeting G Q (G.neighborFinset r) ∪ outerEdges G Q r := by
    intro e heQ
    by_cases hm : ∃ a ∈ G.neighborFinset r, a ∈ e.val
    · exact mem_union_left _ (mem_filter.mpr ⟨heQ, hm⟩)
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨heQ, ?_, ?_⟩
      · intro hr
        obtain ⟨a, hea⟩ := Sym2.mem_iff_exists.mp hr
        have hra : G.Adj r a := G.mem_edgeSet.mp (hea ▸ e.property)
        exact hm ⟨a, (G.mem_neighborFinset r a).mpr hra, hea.symm ▸ Sym2.mem_mk_right r a⟩
      · intro a ha hra
        exact hm ⟨a, (G.mem_neighborFinset r a).mpr hra, ha⟩
  exact (card_le_card hs).trans (card_union_le _ _)

theorem high23_clique_card_le_fourteen_of_support_degree_le_three
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (hQdeg : ∀ x, (edgeIncidences G Q x).card ≤ 3)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) : Q.card ≤ 14 := by
  have hc := selected_edges_card_le_meeting_add_outer G Q r
  have ho := high23_outer_edges_card_le_two G hΔ Q hQ h23 r hR
  have hi := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hs := sum_le_sum (s := G.neighborFinset r) (fun x _ => hQdeg x)
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  omega

end Se20Part.Legacy
