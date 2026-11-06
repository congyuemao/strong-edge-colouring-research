module

public import Se20Part.Legacy.Bounds.TwentyCliqueTypes

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem twenty_clique_quad_counts
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4) (hzr : z ≠ r)
    (hz : (rootType G r z).card = 4) :
    Q.card = 20 ∧ (outerEdges G Q r).card = 4 ∧ (multipleTips G r).card = 5 ∧
      (∑ x ∈ multipleTips G r, (rootType G r x).card) = 12 := by
  let P := multipleTips G r
  have hzP : z ∈ P := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
  have hs := sum_le_sum (s := P.erase z)
    (fun x hx => (mem_filter.mp (mem_erase.mp hx).2).2.2)
  have he := sum_erase_add P (fun x => (rootType G r x).card) hzP
  have hc := card_erase_add_one hzP
  have hb := multipleTips_type_sum_le_twelve G hΔ r
  have ho := outer_card_add_quad_tips_le_multipleTips G hΔ Q hQ r hR {z} (by
    intro x hx
    have h : x = z := mem_singleton.mp hx
    subst x
    exact ⟨hzr, by omega⟩)
  simp only [card_singleton] at ho
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun a _ => (edgeIncidences_card_le_degree G Q a).trans (hΔ a))
  have htotal := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul] at hs
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  change (∑ x ∈ P, (rootType G r x).card) ≤ 12 at hb
  change _ + 1 ≤ P.card at ho
  change _ ∧ _ ∧ P.card = 5 ∧ (∑ x ∈ P, (rootType G r x).card) = 12
  omega

theorem twenty_clique_quad_double_tips
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4) (hzr : z ≠ r)
    (hz : (rootType G r z).card = 4) :
    fullDoubleTips G Q r = (multipleTips G r).erase z ∧
      (fullDoubleTips G Q r).card = 4 ∧
      ∀ x, x ≠ r → x ≠ z → 0 < (rootType G r x).card → x ∈ fullDoubleTips G Q r := by
  obtain ⟨_, ho, hPc, hsum⟩ := twenty_clique_quad_counts G hΔ Q hQ hq hR hzr hz
  obtain ⟨_, hfull⟩ := twenty_clique_labels_saturated_of_outer_le_four G hΔ Q hq r hR (by omega)
  let P := multipleTips G r
  have hzP : z ∈ P := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
  have hc := card_erase_add_one hzP
  have htwo : ∀ x ∈ P.erase z, (rootType G r x).card = 2 := by
    intro x hx
    have hcx := card_erase_add_one hx
    have he1 := sum_erase_add P (fun x => (rootType G r x).card) hzP
    have he2 := sum_erase_add (P.erase z) (fun x => (rootType G r x).card) hx
    have hs := sum_le_sum (s := (P.erase z).erase x)
      (fun y hy => (mem_filter.mp (mem_erase.mp (mem_erase.mp hy).2).2).2.2)
    have hx2 := (mem_filter.mp (mem_erase.mp hx).2).2.2
    simp only [sum_const, smul_eq_mul] at hs
    change P.card = 5 at hPc
    change (∑ x ∈ P, (rootType G r x).card) = 12 at hsum
    omega
  have heq : fullDoubleTips G Q r = P.erase z := by
    ext x
    constructor
    · intro hx
      obtain ⟨_, hxr, ht, _⟩ := mem_filter.mp hx
      have hxz : x ≠ z := by intro h; subst x; omega
      exact mem_erase.mpr ⟨hxz, mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩⟩
    · intro hx
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp (mem_erase.mp hx).2).2.1,
        htwo x hx, hfull x⟩
  refine ⟨heq, ?_, ?_⟩
  · rw [heq]
    change P.card = 5 at hPc
    omega
  · intro x hxr hxz hxpos
    rw [heq]
    apply mem_erase.mpr
    refine ⟨hxz, ?_⟩
    by_contra hxp
    have hr : r ∉ insert x P := by
      simp only [mem_insert, P, multipleTips, mem_filter, mem_univ, true_and]
      tauto
    have hb := root_type_sum_le_twelve G hΔ r (insert x P) hr
    rw [sum_insert hxp] at hb
    change (∑ x ∈ P, (rootType G r x).card) = 12 at hsum
    omega

theorem twenty_clique_quad_outer_supported_on_double_tips
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4) (hzr : z ≠ r)
    (hz : (rootType G r z).card = 4) :
    ∀ e ∈ outerEdges G Q r, ∀ x ∈ e.val, x ∈ fullDoubleTips G Q r := by
  have htip := (twenty_clique_quad_double_tips G hΔ Q hQ hq hR hzr hz).2.2
  intro e heo
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ w : Sym2 V, w = e.val from ⟨e.val, rfl⟩)
  have he := outerEdges_endpoints G Q r e hev.symm heo
  have hcov := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
    (card_union_le _ _)
  have hu0 : 0 < (edgeIncidences G (outerEdges G Q r) u).card := card_pos.mpr
    ⟨e, mem_filter.mpr ⟨heo, hev ▸ Sym2.mem_mk_left u v⟩⟩
  have hv0 : 0 < (edgeIncidences G (outerEdges G Q r) v).card := card_pos.mpr
    ⟨e, mem_filter.mpr ⟨heo, hev ▸ Sym2.mem_mk_right u v⟩⟩
  have hu := outer_incidence_add_type_card_le_degree G Q r u
  have hv := outer_incidence_add_type_card_le_degree G Q r v
  have hdu := hΔ u
  have hdv := hΔ v
  have huz : u ≠ z := by intro h; subst u; omega
  have hvz : v ≠ z := by intro h; subst v; omega
  rw [← hev, Sym2.forall_mem_pair]
  exact ⟨htip u he.2.1 huz (by omega), htip v he.2.2.1 hvz (by omega)⟩

theorem outer_incidence_add_selected_type_le_selected_degree
    (Q : Finset G.edgeSet) (r x : V) (hfull : rootType G r x ⊆ rootLabels G Q x) :
    (edgeIncidences G (outerEdges G Q r) x).card + (rootType G r x).card ≤
      (edgeIncidences G Q x).card := by
  have hs : rootLabels G (outerEdges G Q r) x ∪ rootType G r x ⊆ rootLabels G Q x := by
    apply union_subset _ hfull
    intro a ha
    obtain ⟨haN, e, heo, he⟩ := mem_filter.mp ha
    exact mem_filter.mpr ⟨haN, e, (mem_filter.mp heo).1, he⟩
  have hdis : Disjoint (rootLabels G (outerEdges G Q r) x) (rootType G r x) := by
    apply disjoint_left.mpr
    intro a ha ht
    obtain ⟨_, e, heo, he⟩ := mem_filter.mp ha
    exact (mem_filter.mp heo).2.2 a (he.symm ▸ Sym2.mem_mk_right x a)
      ((mem_rootType G r x a).mp ht).1
  have hc := card_le_card hs
  simpa only [card_union_of_disjoint hdis, rootLabels_card] using hc

theorem twenty_clique_quad_double_tips_selected_degree_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    {r z : V} (hR : (rootLabels G Q r).card = 4) (hzr : z ≠ r)
    (hz : (rootType G r z).card = 4) :
    ∀ x ∈ fullDoubleTips G Q r, (edgeIncidences G Q x).card = 4 := by
  have ho := (twenty_clique_quad_counts G hΔ Q hQ hq hR hzr hz).2.1
  have hD := (twenty_clique_quad_double_tips G hΔ Q hQ hq hR hzr hz).2.1
  have hp := twenty_clique_quad_outer_supported_on_double_tips G hΔ Q hQ hq hR hzr hz
  have hsub : fullDoubleTips G Q r ⊆ multipleTips G r := by
    intro x hx
    obtain ⟨_, hxr, hxt, _⟩ := mem_filter.mp hx
    exact mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩
  intro x hx
  have htwo := four_outer_edges_saturate_multiple_support G hΔ Q r (fullDoubleTips G Q r)
    hsub (by omega) hp ho hx
  obtain ⟨_, _, hxt, hfull⟩ := mem_filter.mp hx
  have hb := outer_incidence_add_selected_type_le_selected_degree G Q r x hfull
  have hd := (edgeIncidences_card_le_degree G Q x).trans (hΔ x)
  omega

variable [DecidableRel (conflictGraph G).Adj]

theorem clique_card_le_twenty
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) : Q.card ≤ 20 := by
  by_cases hq : 20 ≤ Q.card
  · obtain ⟨r, hR⟩ := twenty_clique_exists_root_four G hΔ Q hQ hq
    obtain ⟨z, hzr, hz⟩ := twenty_clique_exists_type_four G hΔ Q hQ hq r hR
    exact (twenty_clique_quad_counts G hΔ Q hQ hq hR hzr hz).1.le
  · omega

end Se20Part.Legacy
