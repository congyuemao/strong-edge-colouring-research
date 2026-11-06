module

public import Se20Part.Legacy.Bounds.TwentyCliqueSaturation

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rootLabels_eq_neighbors_of_selected_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) {x : V}
    (hx : (edgeIncidences G Q x).card = 4) : rootLabels G Q x = G.neighborFinset x :=
  eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q x) (by
    rw [rootLabels_card, hx, SimpleGraph.card_neighborFinset_eq_degree]
    exact hΔ x)

theorem incident_edge_mem_of_selected_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) {x : V}
    (hx : (edgeIncidences G Q x).card = 4) (e : G.edgeSet) (hxe : x ∈ e.val) : e ∈ Q := by
  obtain ⟨y, he⟩ := Sym2.mem_iff_exists.mp hxe
  have hy : y ∈ rootLabels G Q x := by
    rw [rootLabels_eq_neighbors_of_selected_degree_four G hΔ Q hx]
    exact (G.mem_neighborFinset x y).mpr (G.mem_edgeSet.mp (he ▸ e.property))
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp hy
  have hef : e = f := Subtype.ext (he.trans hf.symm)
  exact hef.symm ▸ hfQ

theorem support_closed_of_selected_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hd : ∀ x ∈ selectedSupport G Q, (edgeIncidences G Q x).card = 4) :
    ∀ x ∈ selectedSupport G Q, G.neighborFinset x ⊆ selectedSupport G Q := by
  intro x hx y hy
  let e : G.edgeSet := ⟨s(x, y), (G.mem_neighborFinset x y).mp hy⟩
  have heQ := incident_edge_mem_of_selected_degree_four G hΔ Q (hd x hx) e (Sym2.mem_mk_left x y)
  exact mem_filter.mpr ⟨mem_univ _, card_pos.mpr
    ⟨e, mem_filter.mpr ⟨heQ, Sym2.mem_mk_right x y⟩⟩⟩

theorem twenty_clique_quad_support_subset
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4) (hzr : z ≠ r)
    (hz : (rootType G r z).card = 4) :
    selectedSupport G Q ⊆ insert r (insert z (G.neighborFinset r ∪ fullDoubleTips G Q r)) := by
  have htip := (twenty_clique_quad_double_tips G hΔ Q hQ hq hR hzr hz).2.2
  have houter := twenty_clique_quad_outer_supported_on_double_tips G hΔ Q hQ hq hR hzr hz
  intro x hx
  by_cases hxr : x = r
  · simp [hxr]
  by_cases hxz : x = z
  · simp [hxz]
  by_cases hxN : x ∈ G.neighborFinset r
  · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ hxN))
  apply mem_insert_of_mem
  apply mem_insert_of_mem
  apply mem_union_right
  obtain ⟨e, he⟩ := card_pos.mp (mem_filter.mp hx).2
  obtain ⟨heQ, hxe⟩ := mem_filter.mp he
  obtain ⟨y, hey⟩ := Sym2.mem_iff_exists.mp hxe
  have hxy : G.Adj x y := G.mem_edgeSet.mp (hey ▸ e.property)
  by_cases hyN : y ∈ G.neighborFinset r
  · apply htip x hxr hxz
    exact card_pos.mpr ⟨y, (mem_rootType G r x y).mpr
      ⟨(G.mem_neighborFinset r y).mp hyN, hxy⟩⟩
  have hyr : y ≠ r := by
    intro h
    exact hxN ((G.mem_neighborFinset r x).mpr (h ▸ hxy.symm))
  have heo : e ∈ outerEdges G Q r := by
    apply mem_filter.mpr
    refine ⟨heQ, ?_, ?_⟩
    · rw [hey, Sym2.mem_iff]
      tauto
    · rw [hey, Sym2.forall_mem_pair]
      exact ⟨fun h => hxN ((G.mem_neighborFinset r x).mpr h),
        fun h => hyN ((G.mem_neighborFinset r y).mpr h)⟩
  exact houter e heo x hxe

theorem twenty_clique_quad_support_selected_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4) (hzr : z ≠ r)
    (hz : (rootType G r z).card = 4) :
    ∀ x ∈ selectedSupport G Q, (edgeIncidences G Q x).card = 4 := by
  have ho := (twenty_clique_quad_counts G hΔ Q hQ hq hR hzr hz).2.1
  obtain ⟨hA, hfull⟩ := twenty_clique_labels_saturated_of_outer_le_four G hΔ Q hq r hR (by omega)
  have hD := twenty_clique_quad_double_tips_selected_degree_four G hΔ Q hQ hq hR hzr hz
  intro x hx
  have hs := twenty_clique_quad_support_subset G hΔ Q hQ hq hR hzr hz hx
  rcases mem_insert.mp hs with h | hs
  · subst x
    rwa [rootLabels_card] at hR
  rcases mem_insert.mp hs with h | hs
  · subst x
    have hc := card_le_card (hfull z)
    have hd := (edgeIncidences_card_le_degree G Q z).trans (hΔ z)
    rw [rootLabels_card] at hc
    omega
  rcases mem_union.mp hs with h | h
  · exact hA x h
  · exact hD x h

variable [DecidableRel (conflictGraph G).Adj]

/-- A twenty-clique uses all four incident edges at each of its endpoints. -/
theorem twenty_clique_support_selected_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20) :
    ∀ x ∈ selectedSupport G Q, (edgeIncidences G Q x).card = 4 := by
  obtain ⟨r, hR⟩ := twenty_clique_exists_root_four G hΔ Q hQ (by omega)
  obtain ⟨z, hzr, hz⟩ := twenty_clique_exists_type_four G hΔ Q hQ (by omega) r hR
  exact twenty_clique_quad_support_selected_degree_four G hΔ Q hQ (by omega) hR hzr hz

theorem twenty_clique_support_card_ten
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20) :
    (selectedSupport G Q).card = 10 := by
  have hd := twenty_clique_support_selected_degree_four G hΔ Q hQ hq
  have hs := selectedSupport_incidence_sum G Q
  have he : (∑ x ∈ selectedSupport G Q, (edgeIncidences G Q x).card) =
      ∑ _x ∈ selectedSupport G Q, 4 := sum_congr rfl hd
  simp only [sum_const, smul_eq_mul] at he
  omega

theorem twenty_clique_support_closed_regular
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20) :
    ∀ x ∈ selectedSupport G Q, G.degree x = 4 ∧ G.neighborFinset x ⊆ selectedSupport G Q := by
  have hd := twenty_clique_support_selected_degree_four G hΔ Q hQ hq
  have hc := support_closed_of_selected_degree_four G hΔ Q hd
  intro x hx
  refine ⟨?_, hc x hx⟩
  have hl := edgeIncidences_card_le_degree G Q x
  have hu := hΔ x
  have he := hd x hx
  omega

/-- No edge outside a twenty-clique has a conflict with it in the full G. -/
theorem twenty_clique_conflict_closed
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20)
    {e f : G.edgeSet} (heQ : e ∈ Q) (hef : (conflictGraph G).Adj e f) : f ∈ Q := by
  have hd := twenty_clique_support_selected_degree_four G hΔ Q hQ hq
  have hc := support_closed_of_selected_degree_four G hΔ Q hd
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huS : u ∈ selectedSupport G Q := mem_filter.mpr ⟨mem_univ _, card_pos.mpr
    ⟨e, mem_filter.mpr ⟨heQ, hev ▸ Sym2.mem_mk_left u v⟩⟩⟩
  have hvS : v ∈ selectedSupport G Q := mem_filter.mpr ⟨mem_univ _, card_pos.mpr
    ⟨e, mem_filter.mpr ⟨heQ, hev ▸ Sym2.mem_mk_right u v⟩⟩⟩
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G hev.symm hef
  have hwS : w ∈ selectedSupport G Q := by
    rcases mem_union.mp hw with h | h
    · exact hc u huS (mem_erase.mp h).2
    · exact hc v hvS (mem_erase.mp h).2
  exact incident_edge_mem_of_selected_degree_four G hΔ Q (hd w hwS) f hwf

theorem twenty_cliques_eq_or_disjoint
    (hΔ : ∀ x, G.degree x ≤ 4) (Q R : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20)
    (hR : (conflictGraph G).IsClique (R : Set G.edgeSet)) (hr : R.card = 20) :
    Q = R ∨ Disjoint Q R := by
  by_cases hd : Disjoint Q R
  · exact Or.inr hd
  left
  obtain ⟨e, heQ, heR⟩ := not_disjoint_iff.mp hd
  have hs : R ⊆ Q := by
    intro f hf
    by_cases hef : e = f
    · exact hef ▸ heQ
    exact twenty_clique_conflict_closed G hΔ Q hQ hq heQ (hR heR hf hef)
  exact (eq_of_subset_of_card_le hs (by omega)).symm

end Se20Part.Legacy
