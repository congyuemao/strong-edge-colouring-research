module

public import Se20Part.Legacy.Bounds.High20Local

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem star_add_root_card_le_label_sum (Q : Finset G.edgeSet) (r : V) :
    (edgeIncidences G Q r).card + (rootEdges G Q r).card ≤
      ∑ a ∈ G.neighborFinset r, (edgeIncidences G Q a).card := by
  have hs : edgeIncidences G Q r ⊆
      (edgesMeeting G Q (G.neighborFinset r)).filter (fun e => r ∈ e.val) := by
    intro e he
    obtain ⟨heQ, hre⟩ := mem_filter.mp he
    obtain ⟨a, hea⟩ := Sym2.mem_iff_exists.mp hre
    have hra : G.Adj r a := G.mem_edgeSet.mp (hea ▸ e.property)
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨heQ, a, (G.mem_neighborFinset r a).mpr hra,
      hea.symm ▸ Sym2.mem_mk_right r a⟩, hre⟩
  have hc := card_le_card hs
  have hp := card_filter_add_card_filter_not (s := edgesMeeting G Q (G.neighborFinset r))
    (p := fun e => r ∈ e.val)
  have hi := incidence_sum_eq_meeting_add_inside G Q (G.neighborFinset r)
  change _ + (rootEdges G Q r).card = _ at hp
  omega

theorem selected_degree_add_one_le_of_missing_label
    (Q : Finset G.edgeSet) {a x : V} (hax : G.Adj a x)
    (hx : x ∉ rootLabels G Q a) : (edgeIncidences G Q a).card + 1 ≤ G.degree a := by
  have hs : rootLabels G Q a ⊆ (G.neighborFinset a).erase x :=
    fun y hy => mem_erase.mpr ⟨fun h => hx (h ▸ hy), rootLabels_subset_neighbors G Q a hy⟩
  have hc := card_le_card hs
  have he := card_erase_add_one ((G.mem_neighborFinset a x).mpr hax)
  rw [rootLabels_card] at hc
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at he
  omega

theorem root_label_mem_symm (Q : Finset G.edgeSet) {x a : V}
    (ha : a ∈ rootLabels G Q x) : x ∈ rootLabels G Q a := by
  obtain ⟨haN, e, heQ, he⟩ := mem_filter.mp ha
  exact mem_filter.mpr ⟨(G.mem_neighborFinset a x).mpr ((G.mem_neighborFinset x a).mp haN).symm,
    e, heQ, he.trans Sym2.eq_swap⟩

theorem root_card_add_missing_type_le_twelve
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V)
    (hR : (rootLabels G Q r).card = 4) (x : V) :
    (rootEdges G Q r).card + (rootType G r x \ rootLabels G Q x).card ≤ 12 := by
  let M := rootType G r x \ rootLabels G Q x
  have hs : ∀ a ∈ G.neighborFinset r,
      (edgeIncidences G Q a).card + (if a ∈ M then 1 else 0) ≤ 4 := by
    intro a _
    by_cases ha : a ∈ M
    · obtain ⟨hat, han⟩ := mem_sdiff.mp ha
      have hax := ((mem_rootType G r x a).mp hat).2.symm
      have hn : x ∉ rootLabels G Q a := fun hx => han (root_label_mem_symm G Q hx)
      have hb := (selected_degree_add_one_le_of_missing_label G Q hax hn).trans (hΔ a)
      simpa only [ha, ite_true] using hb
    · simpa only [ha, ite_false, add_zero] using (edgeIncidences_card_le_degree G Q a).trans (hΔ a)
  have hsum := sum_le_sum hs
  have hfilter : (G.neighborFinset r).filter (fun a => a ∈ M) = M := by
    ext a
    exact ⟨fun h => (mem_filter.mp h).2,
      fun h => mem_filter.mpr ⟨filter_subset _ _ (mem_sdiff.mp h).1, h⟩⟩
  simp only [sum_add_distrib, ← sum_filter, sum_const, smul_eq_mul, mul_one, hfilter,
    SimpleGraph.card_neighborFinset_eq_degree] at hsum
  have hb := star_add_root_card_le_label_sum G Q r
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hdr := hΔ r
  change (rootEdges G Q r).card + M.card ≤ 12
  omega

theorem root_card_le_ten_of_label_selected_degree_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet) (r : V)
    (hR : (rootLabels G Q r).card = 4) {a : V} (ha : G.Adj r a)
    (ha2 : (edgeIncidences G Q a).card ≤ 2) : (rootEdges G Q r).card ≤ 10 := by
  have haN := (G.mem_neighborFinset r a).mpr ha
  have hs := sum_le_sum (s := (G.neighborFinset r).erase a)
    (fun z _ => (edgeIncidences_card_le_degree G Q z).trans (hΔ z))
  have he := sum_erase_add (s := G.neighborFinset r) (f := fun z => (edgeIncidences G Q z).card) haN
  have hc := card_erase_add_one haN
  have hb := star_add_root_card_le_label_sum G Q r
  have hstar : (edgeIncidences G Q r).card = 4 := by rw [← rootLabels_card, hR]
  have hdr := hΔ r
  simp only [sum_const, smul_eq_mul] at hs
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

end Se20Part.Legacy
