module

public import Se20Part.Legacy.Bounds.TwentyCliqueCounting

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem twenty_clique_labels_saturated_of_outer_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hq : 20 ≤ Q.card) (r : V) (_hR : (rootLabels G Q r).card = 4)
    (ho : (outerEdges G Q r).card ≤ 4) :
    (∀ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card = 4) ∧
      ∀ x, rootType G r x ⊆ rootLabels G Q x := by
  have hsum := sum_le_sum (s := G.neighborFinset r)
    (fun a _ => (edgeIncidences_card_le_degree G Q a).trans (hΔ a))
  have hm := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  have hc := selected_edges_card_le_meeting_add_outer G Q r
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have hA : ∀ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card = 4 := by
    intro a ha
    have he := sum_erase_add (G.neighborFinset r) (fun a => (edgeIncidences G Q a).card) ha
    have hca := card_erase_add_one ha
    have hs := sum_le_sum (s := (G.neighborFinset r).erase a)
      (fun b _ => (edgeIncidences_card_le_degree G Q b).trans (hΔ b))
    have hda := (edgeIncidences_card_le_degree G Q a).trans (hΔ a)
    simp only [sum_const, smul_eq_mul] at hs
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
    omega
  refine ⟨hA, ?_⟩
  intro x a ha
  have haN := filter_subset _ _ ha
  have hfull : rootLabels G Q a = G.neighborFinset a :=
    eq_of_subset_of_card_le (rootLabels_subset_neighbors G Q a) (by
      rw [rootLabels_card, hA a haN, SimpleGraph.card_neighborFinset_eq_degree]
      exact hΔ a)
  apply root_label_mem_symm G Q
  rw [hfull]
  exact (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp ha).2.symm

/-- Full selection at the root labels makes intersecting types nested. -/
theorem full_root_types_nested_or_disjoint
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hA : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a))
    (hfull : ∀ x, rootType G r x ⊆ rootLabels G Q x) (x y : V) :
    rootType G r x ⊆ rootType G r y ∨ rootType G r y ⊆ rootType G r x ∨
      Disjoint (rootType G r x) (rootType G r y) := by
  by_cases hxy : rootType G r x ⊆ rootType G r y
  · exact Or.inl hxy
  by_cases hyx : rootType G r y ⊆ rootType G r x
  · exact Or.inr (Or.inl hyx)
  right; right
  apply disjoint_left.mpr
  intro c hcx hcy
  obtain ⟨a, hax, hna⟩ := not_subset.mp hxy
  obtain ⟨b, hby, hnb⟩ := not_subset.mp hyx
  obtain ⟨_, e, heQ, he⟩ := mem_filter.mp (hfull x hax)
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp (hfull y hby)
  have hadj := root_selected_edges_force_adj G Q hQ hN
    ((mem_rootType G r x a).mp hax).1 ((mem_rootType G r y b).mp hby).1
    hnb hna e f heQ hfQ (he.trans Sym2.eq_swap) (hf.trans Sym2.eq_swap)
  exact hA c (filter_subset _ _ hcx) ((mem_rootType G r x c).mp hcx).2.symm
    ((mem_rootType G r y c).mp hcy).2.symm hadj.ne hadj

theorem multipleTips_card_le_three_of_full_root_triple_no_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hR : (rootLabels G Q r).card = 4)
    (hN : G.IsIndepSet (G.neighborSet r))
    (hA : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a))
    (hdA : ∀ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card = 4)
    (hfull : ∀ x, rootType G r x ⊆ rootLabels G Q x)
    (ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 3)
    {x : V} (hxr : x ≠ r) (hx : 3 ≤ (rootType G r x).card) :
    (multipleTips G r).card ≤ 3 := by
  have hsub : ∀ y ∈ multipleTips G r, rootType G r y ⊆ rootType G r x := by
    intro y hy
    obtain ⟨_, hyr, hcy⟩ := mem_filter.mp hy
    rcases full_root_types_nested_or_disjoint G Q hQ hN hA hfull x y with h | h | h
    · exact (eq_of_subset_of_card_le h (by have hb := ht y hyr; omega)).symm.subset
    · exact h
    · obtain ⟨a, ha⟩ := high21_large_types_share_label G hΔ hx hcy
      exact (disjoint_left.mp h (mem_inter.mp ha).1 (mem_inter.mp ha).2).elim
  have hx3 : (rootType G r x).card = 3 := by have hc := ht x hxr; omega
  have hNr : (G.neighborFinset r).card = 4 := by
    have hc := card_le_card (rootLabels_subset_neighbors G Q r)
    have hd := hΔ r
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc ⊢
    omega
  have hmissing : ¬ G.neighborFinset r ⊆ rootType G r x := by
    intro h
    have hc := card_le_card h
    omega
  obtain ⟨b, hbN, hbx⟩ := not_subset.mp hmissing
  have hdb := hdA b hbN
  have hlabels : 1 < (rootLabels G Q b).card := by rw [rootLabels_card, hdb]; omega
  obtain ⟨z, hz, hzr⟩ := exists_mem_ne hlabels r
  obtain ⟨hzN, e, heQ, he⟩ := mem_filter.mp hz
  have hbz : b ∈ rootType G r z := (mem_rootType G r z b).mpr
    ⟨(G.mem_neighborFinset r b).mp hbN, ((G.mem_neighborFinset b z).mp hzN).symm⟩
  have hzsmall : (rootType G r z).card ≤ 1 := by
    by_contra hn
    have hzP : z ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
    exact hbx (hsub z hzP hbz)
  have hzT : rootType G r z = {b} :=
    (eq_of_subset_of_card_le (singleton_subset_iff.mpr hbz) (by simpa using hzsmall)).symm
  have hsupport : multipleTips G r ⊆ (G.neighborFinset z).erase b := by
    intro y hy
    have hby : b ∉ rootType G r y := fun h => hbx (hsub y hy h)
    have hcy := (mem_filter.mp hy).2.2
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r y).card by omega)
    have hab : a ≠ b := fun h => hby (h ▸ ha)
    have haz : a ∉ rootType G r z := by simpa only [hzT, mem_singleton] using hab
    obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp (hfull y ha)
    have hzy := root_selected_edges_force_adj G Q hQ hN
      ((G.mem_neighborFinset r b).mp hbN) ((mem_rootType G r y a).mp ha).1
      haz hby e f heQ hfQ he (hf.trans Sym2.eq_swap)
    have hyb : y ≠ b := fun h => multipleTips_not_neighbor G hN hy
      (h.symm ▸ (G.mem_neighborFinset r b).mp hbN)
    exact mem_erase.mpr ⟨hyb, (G.mem_neighborFinset z y).mpr hzy⟩
  have hc := card_le_card hsupport
  have hec := card_erase_add_one ((G.mem_neighborFinset z b).mpr
    ((G.mem_neighborFinset b z).mp hzN).symm)
  have hd := hΔ z
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hec
  omega

variable [DecidableRel (conflictGraph G).Adj]

/-- A twenty-clique must contain a second vertex with the entire four-element
root neighbourhood as its type. -/
theorem twenty_clique_exists_type_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : 20 ≤ Q.card)
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    ∃ x, x ≠ r ∧ (rootType G r x).card = 4 := by
  by_contra hn
  have hN := twenty_clique_root_neighborhood_independent G hΔ Q hQ hq r hR
  have ht : ∀ x, x ≠ r → (rootType G r x).card ≤ 3 := by
    intro x hxr
    have hc := card_le_card (filter_subset (G.Adj x) (G.neighborFinset r))
    have hd := hΔ r
    have hne : (rootType G r x).card ≠ 4 := fun h => hn ⟨x, hxr, h⟩
    change (rootType G r x).card ≤ (G.neighborFinset r).card at hc
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
    omega
  by_cases htr : ∃ x, x ≠ r ∧ 3 ≤ (rootType G r x).card
  · obtain ⟨x, hxr, hx⟩ := htr
    by_cases htwo : ∃ y, y ≠ r ∧ y ≠ x ∧ 3 ≤ (rootType G r y).card
    · obtain ⟨y, hyr, hyx, hy⟩ := htwo
      have ho := outer_card_le_four_of_two_triples G hΔ Q hQ hR hxr hyr hyx.symm hx hy
      obtain ⟨hdA, hfull⟩ := twenty_clique_labels_saturated_of_outer_le_four G hΔ Q hq r hR ho
      have hA : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a) := by
        intro a ha
        apply twenty_clique_root_neighborhood_independent G hΔ Q hQ hq a
        rw [rootLabels_card, hdA a ha]
      have hP := multipleTips_card_le_three_of_full_root_triple_no_four G hΔ Q hQ hR
        hN hA hdA hfull ht hxr hx
      have houter := outer_card_le_multipleTips G hΔ Q hQ r hR
      have hc := selected_edges_card_le_meeting_add_outer G Q r
      have hi := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
      have hs := sum_le_sum (s := G.neighborFinset r)
        (fun a _ => (edgeIncidences_card_le_degree G Q a).trans (hΔ a))
      have hd := hΔ r
      simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
      omega
    · have hsmall : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2 := by
        intro y hyr hyx
        have hn3 : ¬ 3 ≤ (rootType G r y).card := fun h => htwo ⟨y, hyr, hyx, h⟩
        omega
      have hc := clique_card_le_eighteen_of_unique_triple G hΔ Q hQ hN hR hxr
        (by have hb := ht x hxr; omega) hsmall
      omega
  · have hsmall : ∀ x, x ≠ r → (rootType G r x).card ≤ 2 := by
      intro x hxr
      have hn3 : ¬ 3 ≤ (rootType G r x).card := fun h => htr ⟨x, hxr, h⟩
      omega
    have hc := clique_card_le_eighteen_of_independent_root_types_le_two G hΔ Q hQ r hR hN hsmall
    omega

end Se20Part.Legacy
