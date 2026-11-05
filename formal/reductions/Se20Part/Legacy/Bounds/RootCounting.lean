module

public import Se20Part.Legacy.Bounds.High23Four

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def rootTips (Q : Finset G.edgeSet) (r : V) : Finset V :=
  univ.filter (fun x => x ≠ r ∧ ∃ a ∈ G.neighborFinset r, ∃ e ∈ Q, e.val = s(a, x))

def rootEdges (Q : Finset G.edgeSet) (r : V) : Finset G.edgeSet :=
  (edgesMeeting G Q (G.neighborFinset r)).filter (fun e => r ∉ e.val)

theorem root_single_edge_outer_adj {r a b x y : V}
    (hN : G.IsIndepSet (G.neighborSet r))
    (ha : G.Adj r a) (hb : G.Adj r b)
    (hx : rootType G r x = {a}) (hy : a ∉ rootType G r y)
    (e f : G.edgeSet) (he : e.val = s(a, x)) (hf : f.val = s(b, y))
    (hc : StrongConflict G e f) : G.Adj x y := by
  have hby : G.Adj b y := G.mem_edgeSet.mp (hf ▸ f.property)
  have hab : a ≠ b := by
    intro h
    exact hy ((mem_rootType G r y a).mpr ⟨ha, h ▸ hby.symm⟩)
  have hnab : ¬ G.Adj a b := hN ha hb hab
  have hnxb : ¬ G.Adj x b := by
    intro h
    have hm := (mem_rootType G r x b).mpr ⟨hb, h⟩
    have hba : b = a := by simpa only [hx, mem_singleton] using hm
    exact hab hba.symm
  have hnay : ¬ G.Adj a y := fun h => hy ((mem_rootType G r y a).mpr ⟨ha, h.symm⟩)
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he hc
  rw [hf, Sym2.mem_iff] at hwf
  rcases hwf with hwb | hwy
  · have hb' : b ∈ endpointNeighbourCover G a x := hwb ▸ hw
    rcases mem_union.mp hb' with h | h
    · exact (hnab ((G.mem_neighborFinset a b).mp (mem_erase.mp h).2)).elim
    · exact (hnxb ((G.mem_neighborFinset x b).mp (mem_erase.mp h).2)).elim
  · have hy' : y ∈ endpointNeighbourCover G a x := hwy ▸ hw
    rcases mem_union.mp hy' with h | h
    · exact (hnay ((G.mem_neighborFinset a y).mp (mem_erase.mp h).2)).elim
    · exact (G.mem_neighborFinset x y).mp (mem_erase.mp h).2

theorem rootTips_adj_of_single
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r a x : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ha : G.Adj r a) (hx : rootType G r x = {a})
    (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(a, x))
    {y : V} (hy : y ∈ rootTips G Q r) (hya : a ∉ rootType G r y) : G.Adj x y := by
  obtain ⟨_, _, b, hbN, f, hfQ, hf⟩ := mem_filter.mp hy
  have hb := (G.mem_neighborFinset r b).mp hbN
  have hny := root_edge_tip_not_neighbor G hN hb f hf
  have hef : e ≠ f := by
    intro h
    have haf : a ∈ f.val := h ▸ (he.symm ▸ Sym2.mem_mk_left a x)
    rw [hf, Sym2.mem_iff] at haf
    rcases haf with hab | hay
    · have hby : G.Adj b y := G.mem_edgeSet.mp (hf ▸ f.property)
      exact hya ((mem_rootType G r y a).mpr ⟨ha, hab ▸ hby.symm⟩)
    · exact hny (hay ▸ ha)
  exact root_single_edge_outer_adj G hN ha hb hx hya e f he hf (hQ heQ hfQ hef)

theorem rootTips_card_le_six_of_single
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r a x : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ha : G.Adj r a) (hx : rootType G r x = {a})
    (e : G.edgeSet) (heQ : e ∈ Q) (he : e.val = s(a, x)) :
    (rootTips G Q r).card ≤ 6 := by
  have hax : G.Adj a x := G.mem_edgeSet.mp (he ▸ e.property)
  have hs : rootTips G Q r ⊆ (G.neighborFinset a).erase r ∪ (G.neighborFinset x).erase a := by
    intro y hy
    by_cases hya : a ∈ rootType G r y
    · exact mem_union_left _ (mem_erase.mpr ⟨(mem_filter.mp hy).2.1,
        (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hya).2.symm⟩)
    · have hxy := rootTips_adj_of_single G Q hQ hN ha hx e heQ he hy hya
      obtain ⟨_, _, b, hbN, f, _, hf⟩ := mem_filter.mp hy
      have hny := root_edge_tip_not_neighbor G hN ((G.mem_neighborFinset r b).mp hbN) f hf
      exact mem_union_right _ (mem_erase.mpr ⟨fun h => hny (h.symm ▸ ha),
        (G.mem_neighborFinset x y).mpr hxy⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hca := card_erase_add_one ((G.mem_neighborFinset a r).mpr ha.symm)
  have hcx := card_erase_add_one ((G.mem_neighborFinset x a).mpr hax.symm)
  have hda := hΔ a
  have hdx := hΔ x
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca hcx
  omega

theorem rootEdges_card_le_tip_weight (Q : Finset G.edgeSet) (r : V) :
    (rootEdges G Q r).card ≤ ∑ x ∈ rootTips G Q r, (rootType G r x).card := by
  classical
  let P := ((G.neighborFinset r) ×ˢ rootTips G Q r).filter (fun p => G.Adj p.2 p.1)
  have hc : (rootEdges G Q r).card ≤ P.card := by
    apply card_le_via_relation _ _ (fun e p => e.val = s(p.1, p.2))
    · intro e he
      obtain ⟨hem, hr⟩ := mem_filter.mp he
      obtain ⟨heQ, a, ha, hae⟩ := mem_filter.mp hem
      obtain ⟨x, hex⟩ := Sym2.mem_iff_exists.mp hae
      have hxr : x ≠ r := by
        intro h
        exact hr (hex.symm ▸ h ▸ Sym2.mem_mk_right a x)
      have hax : G.Adj a x := G.mem_edgeSet.mp (hex ▸ e.property)
      refine ⟨(a, x), mem_filter.mpr ⟨mem_product.mpr ⟨ha, ?_⟩, hax.symm⟩, hex⟩
      exact mem_filter.mpr ⟨mem_univ _, hxr, a, ha, e, heQ, hex⟩
    · intro e he f hf p hep hfp
      exact Subtype.ext (hep.trans hfp.symm)
  have hp : P.card = ∑ x ∈ rootTips G Q r, (rootType G r x).card := by
    simp only [P, rootType, card_eq_sum_ones, sum_filter, sum_product]
    exact sum_comm
  exact hp ▸ hc

theorem clique_card_le_star_root_outer (Q : Finset G.edgeSet) (r : V) :
    Q.card ≤ (edgeIncidences G Q r).card + (rootEdges G Q r).card + (outerEdges G Q r).card := by
  have hs : edgesMeeting G Q (G.neighborFinset r) ⊆ edgeIncidences G Q r ∪ rootEdges G Q r := by
    intro e he
    by_cases hr : r ∈ e.val
    · exact mem_union_left _ (mem_filter.mpr ⟨(mem_filter.mp he).1, hr⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨he, hr⟩)
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have ht := selected_edges_card_le_meeting_add_outer G Q r
  omega

theorem outer_incidence_add_type_card_le_degree (Q : Finset G.edgeSet) (r x : V) :
    (edgeIncidences G (outerEdges G Q r) x).card + (rootType G r x).card ≤ G.degree x := by
  have hsub : rootLabels G (outerEdges G Q r) x ∪ rootType G r x ⊆ G.neighborFinset x := by
    apply union_subset (rootLabels_subset_neighbors G _ x)
    intro a ha
    exact (G.mem_neighborFinset x a).mpr ((mem_rootType G r x a).mp ha).2
  have hdis : Disjoint (rootLabels G (outerEdges G Q r) x) (rootType G r x) := by
    apply disjoint_left.mpr
    intro a ha ht
    obtain ⟨_, e, heo, he⟩ := mem_filter.mp ha
    exact (mem_filter.mp heo).2.2 a (he.symm ▸ Sym2.mem_mk_right x a)
      ((mem_rootType G r x a).mp ht).1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hdis, rootLabels_card, SimpleGraph.card_neighborFinset_eq_degree] at hc
  exact hc

end Se20Part.Legacy
