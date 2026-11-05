module

public import Se20Part.Legacy.Bounds.High23Outer

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def singleTips (Q : Finset G.edgeSet) (r : V) : Finset V :=
  univ.filter (fun x => x ≠ r ∧ ∃ a ∈ G.neighborFinset r,
    rootType G r x = {a} ∧ ∃ e ∈ Q, e.val = s(a, x))

def singleRootEdges (Q : Finset G.edgeSet) (r : V) : Finset G.edgeSet :=
  Q.filter (fun e => ∃ a x, a ∈ G.neighborFinset r ∧ x ≠ r ∧
    e.val = s(a, x) ∧ rootType G r x = {a})

def doubleRootEdges (Q : Finset G.edgeSet) (r : V) : Finset G.edgeSet :=
  Q.filter (fun e => ∃ a x, a ∈ G.neighborFinset r ∧ x ≠ r ∧
    e.val = s(a, x) ∧ 2 ≤ (rootType G r x).card)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem root_edge_tip_not_neighbor {r a x : V}
    (hN : G.IsIndepSet (G.neighborSet r)) (ha : G.Adj r a)
    (e : G.edgeSet) (he : e.val = s(a, x)) : ¬ G.Adj r x := by
  have hax : G.Adj a x := G.mem_edgeSet.mp (he ▸ e.property)
  intro hx
  exact hN ha hx hax.ne hax

theorem root_single_edges_outer_adj {r a b x y : V}
    (hN : G.IsIndepSet (G.neighborSet r))
    (ha : G.Adj r a) (hb : G.Adj r b) (hab : a ≠ b)
    (hx : rootType G r x = {a}) (hy : rootType G r y = {b})
    (e f : G.edgeSet) (he : e.val = s(a, x)) (hf : f.val = s(b, y))
    (hc : StrongConflict G e f) : G.Adj x y := by
  have hnab : ¬ G.Adj a b := hN ha hb hab
  have hnxb : ¬ G.Adj x b := by
    intro h
    have hm := (mem_rootType G r x b).mpr ⟨hb, h⟩
    have hba : b = a := by simpa only [hx, mem_singleton] using hm
    exact hab hba.symm
  have hnay : ¬ G.Adj a y := by
    intro h
    have hm := (mem_rootType G r y a).mpr ⟨ha, h.symm⟩
    exact hab (by simpa only [hy, mem_singleton] using hm)
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

variable [DecidableRel (conflictGraph G).Adj]

theorem high23_singleTips_card_le_six
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hR : 3 ≤ (rootLabels G Q r).card) : (singleTips G Q r).card ≤ 6 := by
  classical
  by_cases hs : singleTips G Q r = ∅
  · simp [hs]
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hs
  obtain ⟨_, hxr, a, haN, hxT, e, heQ, he⟩ := mem_filter.mp hx
  have ha := (G.mem_neighborFinset r a).mp haN
  have hax : G.Adj a x := G.mem_edgeSet.mp (he ▸ e.property)
  have hN := high23_root_neighborhood_independent G hΔ Q h23 r hR
  have hcover : singleTips G Q r ⊆ (G.neighborFinset a).erase r ∪ (G.neighborFinset x).erase a := by
    intro y hy
    obtain ⟨_, hyr, b, hbN, hyT, f, hfQ, hf⟩ := mem_filter.mp hy
    have hb := (G.mem_neighborFinset r b).mp hbN
    have hby : G.Adj b y := G.mem_edgeSet.mp (hf ▸ f.property)
    by_cases hab : a = b
    · exact mem_union_left _ (mem_erase.mpr ⟨hyr,
        (G.mem_neighborFinset a y).mpr (hab.symm ▸ hby)⟩)
    have hny := root_edge_tip_not_neighbor G hN hb f hf
    have hya : y ≠ a := fun h => hny (h.symm ▸ ha)
    have hef : e ≠ f := by
      intro h
      have haf : a ∈ f.val := h ▸ (he.symm ▸ Sym2.mem_mk_left a x)
      rw [hf, Sym2.mem_iff] at haf
      rcases haf with h | h
      · exact hab h
      · exact hya h.symm
    have hxy := root_single_edges_outer_adj G hN ha hb hab hxT hyT e f he hf (hQ heQ hfQ hef)
    exact mem_union_right _ (mem_erase.mpr ⟨hya, (G.mem_neighborFinset x y).mpr hxy⟩)
  have hc := (card_le_card hcover).trans (card_union_le _ _)
  have hca := card_erase_add_one ((G.mem_neighborFinset a r).mpr ha.symm)
  have hcx := card_erase_add_one ((G.mem_neighborFinset x a).mpr hax.symm)
  have hda := hΔ a
  have hdx := hΔ x
  simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca hcx
  omega

omit [DecidableRel (conflictGraph G).Adj] in
theorem singleRootEdges_card_le_singleTips (Q : Finset G.edgeSet) (r : V) :
    (singleRootEdges G Q r).card ≤ (singleTips G Q r).card := by
  classical
  apply card_le_via_relation _ _ (fun e x =>
    ∃ a ∈ G.neighborFinset r, e.val = s(a, x) ∧ rootType G r x = {a})
  · intro e he
    obtain ⟨heQ, a, x, ha, hxr, hea, hx⟩ := mem_filter.mp he
    exact ⟨x, mem_filter.mpr ⟨mem_univ _, hxr, a, ha, hx, e, heQ, hea⟩,
      a, ha, hea, hx⟩
  · intro e he f hf x hex hfx
    obtain ⟨a, ha, hea, hx⟩ := hex
    obtain ⟨b, hb, hfb, hx'⟩ := hfx
    have hab : a = b := by
      have hm : a ∈ rootType G r x := hx.symm ▸ mem_singleton_self a
      simpa only [hx', mem_singleton] using hm
    apply Subtype.ext
    rw [hea, hfb, hab]

theorem high23_doubleRootEdges_card_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (h23 : ∀ e ∈ Q, 23 ≤ (conflictGraph G).degree e)
    (r : V) (hfull : rootLabels G Q r = G.neighborFinset r) :
    (doubleRootEdges G Q r).card ≤ 4 := by
  classical
  have hc : (doubleRootEdges G Q r).card ≤ (G.neighborFinset r).card := by
    apply card_le_via_relation _ _ (fun e a =>
      a ∈ G.neighborFinset r ∧ ∃ x, x ≠ r ∧ e.val = s(a, x) ∧ 2 ≤ (rootType G r x).card)
    · intro e he
      obtain ⟨_, a, x, ha, hxr, hea, hx⟩ := mem_filter.mp he
      exact ⟨a, ha, ha, x, hxr, hea, hx⟩
    · intro e he f hf a hea hfa
      obtain ⟨haN, x, hxr, hex, hx⟩ := hea
      obtain ⟨_, y, hyr, hfy, hy⟩ := hfa
      have hax : G.Adj a x := G.mem_edgeSet.mp (hex ▸ e.property)
      have hay : G.Adj a y := G.mem_edgeSet.mp (hfy ▸ f.property)
      have haR : a ∈ rootLabels G Q r := hfull.symm ▸ haN
      have hxy := high23_double_type_unique G hΔ Q h23 haR hxr hyr
        ((mem_rootType G r x a).mpr ⟨(G.mem_neighborFinset r a).mp haN, hax.symm⟩)
        ((mem_rootType G r y a).mpr ⟨(G.mem_neighborFinset r a).mp haN, hay.symm⟩) hx hy
      exact Subtype.ext (hex.trans (by rw [hxy]; exact hfy.symm))
  simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hc.trans (hΔ r)

end Se20Part.Legacy
