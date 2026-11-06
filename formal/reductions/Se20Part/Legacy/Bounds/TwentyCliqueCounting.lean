module

public import Se20Part.Legacy.Bounds.TwentyCliqueRoot

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The twelve non-root neighbour slots include every original vertex. -/
theorem root_type_sum_le_twelve
    (hΔ : ∀ x, G.degree x ≤ 4) (r : V) (S : Finset V) (hr : r ∉ S) :
    (∑ x ∈ S, (rootType G r x).card) ≤ 12 := by
  rw [root_type_card_sum_eq_label_sum]
  have hb : ∀ a ∈ G.neighborFinset r,
      (S.filter (fun x => a ∈ rootType G r x)).card ≤ 3 := by
    intro a ha
    have hs : S.filter (fun x => a ∈ rootType G r x) ⊆ (G.neighborFinset a).erase r := by
      intro x hx
      obtain ⟨hxS, hax⟩ := mem_filter.mp hx
      exact mem_erase.mpr ⟨fun h => hr (h ▸ hxS),
        (G.mem_neighborFinset a x).mpr ((mem_rootType G r x a).mp hax).2.symm⟩
    have hc := card_le_card hs
    have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr
      ((G.mem_neighborFinset r a).mp ha).symm)
    have hd := hΔ a
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at he
    omega
  have hs := sum_le_sum hb
  have hd := hΔ r
  simp only [sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree] at hs
  omega

/-- Each outer edge either uses a triple tip's single residual slot, or uses
two double-tip slots. This charges at most one edge to each multiple tip. -/
theorem outer_card_add_quad_tips_le_multipleTips
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (Z : Finset V) (hZ : ∀ z ∈ Z, z ≠ r ∧ 4 ≤ (rootType G r z).card) :
    (outerEdges G Q r).card + Z.card ≤ (multipleTips G r).card := by
  let P := multipleTips G r
  let T := P.filter (fun x => 3 ≤ (rootType G r x).card)
  let D := P.filter (fun x => ¬ 3 ≤ (rootType G r x).card)
  let O := (outerEdges G Q r).filter (fun e => ¬ ∃ x ∈ T, x ∈ e.val)
  have hZT : Z ⊆ T := by
    intro z hz
    obtain ⟨hzr, hzt⟩ := hZ z hz
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩, by omega⟩
  have hOT : (edgesMeeting G (outerEdges G Q r) T).card + Z.card ≤ T.card := by
    have hi := incidence_sum_eq_meeting_add_inside G (outerEdges G Q r) T
    have hs := sum_le_sum (s := T) (f := fun x =>
      (edgeIncidences G (outerEdges G Q r) x).card + if x ∈ Z then 1 else 0)
      (g := fun _ => 1) (by
        intro x hx
        have ht := (mem_filter.mp hx).2
        have hd := hΔ x
        have hc := outer_incidence_add_type_card_le_degree G Q r x
        by_cases hz : x ∈ Z
        · have hz4 := (hZ x hz).2
          simp only [hz, ite_true]
          omega
        · simp only [hz, ite_false]
          omega)
    have hfilter : T.filter (fun x => x ∈ Z) = Z := by
      ext x
      exact ⟨fun hx => (mem_filter.mp hx).2, fun hx => mem_filter.mpr ⟨hZT hx, hx⟩⟩
    simp only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one, hfilter] at hs
    omega
  have hOsub : O ⊆ outerEdges G Q r := filter_subset _ _
  have hOeq : outerEdges G O r = O := outerEdges_eq_self_of_subset G Q O r hOsub
  have hOD : ∀ e ∈ O, ∀ x ∈ e.val, x ∈ D := by
    intro e heO
    obtain ⟨heo, hn⟩ := mem_filter.mp heO
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have he := outerEdges_endpoints G Q r e hev.symm heo
    have hu : ¬ 3 ≤ (rootType G r u).card := by
      intro ht
      exact hn ⟨u, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.1, by omega⟩, ht⟩,
        hev ▸ Sym2.mem_mk_left u v⟩
    have hv : ¬ 3 ≤ (rootType G r v).card := by
      intro ht
      exact hn ⟨v, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.2.1, by omega⟩, ht⟩,
        hev ▸ Sym2.mem_mk_right u v⟩
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans
      (card_union_le _ _)
    rw [← hev, Sym2.forall_mem_pair]
    exact ⟨mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.1, by omega⟩, hu⟩,
      mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, he.2.2.1, by omega⟩, hv⟩⟩
  have hi := outer_incidence_sum_eq_twice G O r D (by simpa only [hOeq] using hOD)
  have hs := sum_le_sum (s := D) (f := fun x => (edgeIncidences G (outerEdges G O r) x).card)
    (g := fun _ => 2) (by
      intro x hx
      have ht := (mem_filter.mp (mem_filter.mp hx).1).2.2
      have hd := hΔ x
      have hc := outer_incidence_add_type_card_le_degree G O r x
      omega)
  rw [hOeq] at hi
  simp only [sum_const, smul_eq_mul] at hs
  rw [hOeq] at hs
  have hpart := card_filter_add_card_filter_not (s := outerEdges G Q r)
    (p := fun e => ∃ x ∈ T, x ∈ e.val)
  have hPD := card_filter_add_card_filter_not (s := P)
    (p := fun x => 3 ≤ (rootType G r x).card)
  change (edgesMeeting G (outerEdges G Q r) T).card + O.card = _ at hpart
  change T.card + D.card = _ at hPD
  change _ + Z.card ≤ P.card
  omega

theorem outer_card_le_multipleTips
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4) :
    (outerEdges G Q r).card ≤ (multipleTips G r).card := by
  simpa using outer_card_add_quad_tips_le_multipleTips G hΔ Q hQ r hR ∅ (by simp)

/-- Two triple tips force a twelfth slot when there are five multiple tips. -/
theorem multipleTips_sum_ge_twice_card_add_two_of_two_triples
    {r x y : V} (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card) :
    2 * (multipleTips G r).card + 2 ≤ ∑ z ∈ multipleTips G r, (rootType G r z).card := by
  let P := multipleTips G r
  have hxP : x ∈ P := mem_filter.mpr ⟨mem_univ _, hxr, by omega⟩
  have hyP : y ∈ P.erase x := mem_erase.mpr ⟨hxy.symm,
    mem_filter.mpr ⟨mem_univ _, hyr, by omega⟩⟩
  have hc1 := card_erase_add_one hxP
  have hc2 := card_erase_add_one hyP
  have he1 := sum_erase_add P (fun z => (rootType G r z).card) hxP
  have he2 := sum_erase_add (P.erase x) (fun z => (rootType G r z).card) hyP
  have hs := sum_le_sum (s := (P.erase x).erase y) (fun z hz =>
    (mem_filter.mp (mem_erase.mp (mem_erase.mp hz).2).2).2.2)
  simp only [sum_const, smul_eq_mul] at hs
  change 2 * P.card + 2 ≤ ∑ z ∈ P, (rootType G r z).card
  omega

theorem no_single_type_of_five_multiple_two_triples
    (hΔ : ∀ x, G.degree x ≤ 4) {r x y : V}
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card)
    (hP : (multipleTips G r).card = 5) {z : V} (hzr : z ≠ r) :
    (rootType G r z).card ≠ 1 := by
  intro hz
  have hlow := multipleTips_sum_ge_twice_card_add_two_of_two_triples G hxr hyr hxy hx hy
  have hzp : z ∉ multipleTips G r := by
    intro h
    have hc := (mem_filter.mp h).2.2
    omega
  have hr : r ∉ insert z (multipleTips G r) := by
    simp only [mem_insert, multipleTips, mem_filter, mem_univ, true_and]
    tauto
  have hb := root_type_sum_le_twelve G hΔ r (insert z (multipleTips G r)) hr
  rw [sum_insert hzp] at hb
  omega

/-- With at least two triple types, five outer edges are impossible. -/
theorem outer_card_le_four_of_two_triples
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hR : (rootLabels G Q r).card = 4) {x y : V}
    (hxr : x ≠ r) (hyr : y ≠ r) (hxy : x ≠ y)
    (hx : 3 ≤ (rootType G r x).card) (hy : 3 ≤ (rootType G r y).card) :
    (outerEdges G Q r).card ≤ 4 := by
  by_contra hn
  let P := multipleTips G r
  have hlow := multipleTips_sum_ge_twice_card_add_two_of_two_triples G hxr hyr hxy hx hy
  have hsum := multipleTips_type_sum_le_twelve G hΔ r
  have houter := outer_card_le_multipleTips G hΔ Q hQ r hR
  have hPc : P.card = 5 := by change _ ≤ P.card at houter; change 2 * P.card + 2 ≤ _ at hlow; omega
  have hsupport : ∀ e ∈ outerEdges G Q r, ∀ z ∈ e.val, z ∈ P := by
    intro e heo
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
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
    have hnu := no_single_type_of_five_multiple_two_triples G hΔ hxr hyr hxy hx hy hPc he.2.1
    have hnv := no_single_type_of_five_multiple_two_triples G hΔ hxr hyr hxy hx hy hPc he.2.2.1
    rw [← hev, Sym2.forall_mem_pair]
    exact ⟨mem_filter.mpr ⟨mem_univ _, he.2.1, by omega⟩,
      mem_filter.mpr ⟨mem_univ _, he.2.2.1, by omega⟩⟩
  have hi := outer_incidence_sum_eq_twice G Q r P hsupport
  have hb := sum_le_sum (s := P) (fun z _ =>
    (outer_incidence_add_type_card_le_degree G Q r z).trans (hΔ z))
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at hb
  change _ + (∑ z ∈ P, (rootType G r z).card) ≤ _ at hb
  change 2 * P.card + 2 ≤ ∑ z ∈ P, (rootType G r z).card at hlow
  omega

end Se20Part.Legacy
