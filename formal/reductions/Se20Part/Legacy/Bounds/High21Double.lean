module

public import Se20Part.Legacy.Bounds.High21Support
public import Se20Part.Legacy.Bounds.DegreeTwoClique

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def fullDoubleTips (Q : Finset G.edgeSet) (r : V) : Finset V :=
  univ.filter (fun x => x ≠ r ∧ (rootType G r x).card = 2 ∧
    rootType G r x ⊆ rootLabels G Q x)

theorem rootType_eq_neighbor_inter (r x : V) :
    rootType G r x = G.neighborFinset x ∩ G.neighborFinset r := by
  ext a
  simp only [mem_rootType, mem_inter, SimpleGraph.mem_neighborFinset, and_comm]

theorem multipleTips_not_neighbor
    {r x : V} (hN : G.IsIndepSet (G.neighborSet r)) (hx : x ∈ multipleTips G r) :
    ¬ G.Adj r x := by
  have hc := (mem_filter.mp hx).2.2
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r x).card by omega)
  obtain ⟨hra, hxa⟩ := (mem_rootType G r x a).mp ha
  intro hrx
  exact hN hrx hra hxa.ne hxa

theorem residual_neighbors_add_type_card (r x : V) :
    (G.neighborFinset x \ G.neighborFinset r).card + (rootType G r x).card = G.degree x := by
  rw [rootType_eq_neighbor_inter, card_sdiff_add_card_inter, SimpleGraph.card_neighborFinset_eq_degree]

theorem root_selected_edges_force_adj
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r a b x y : V} (hN : G.IsIndepSet (G.neighborSet r))
    (ha : G.Adj r a) (hb : G.Adj r b)
    (hxb : b ∉ rootType G r x) (hya : a ∉ rootType G r y)
    (e f : G.edgeSet) (heQ : e ∈ Q) (hfQ : f ∈ Q)
    (he : e.val = s(a, x)) (hf : f.val = s(b, y)) : G.Adj x y := by
  have hby : G.Adj b y := G.mem_edgeSet.mp (hf ▸ f.property)
  have hny := root_edge_tip_not_neighbor G hN hb f hf
  have hab : a ≠ b := fun h => hya ((mem_rootType G r y a).mpr ⟨ha, h ▸ hby.symm⟩)
  have hnab : ¬ G.Adj a b := hN ha hb hab
  have hnxb : ¬ G.Adj x b := fun h => hxb ((mem_rootType G r x b).mpr ⟨hb, h⟩)
  have hnay : ¬ G.Adj a y := fun h => hya ((mem_rootType G r y a).mpr ⟨ha, h.symm⟩)
  have hef : e ≠ f := by
    intro h
    have haf : a ∈ f.val := h ▸ (he.symm ▸ Sym2.mem_mk_left a x)
    rw [hf, Sym2.mem_iff] at haf
    exact haf.elim hab (fun h => hny (h ▸ ha))
  obtain ⟨w, hw, hwf⟩ := strongConflict_meets_cover G he (hQ heQ hfQ hef)
  rw [hf, Sym2.mem_iff] at hwf
  rcases hwf with hwb | hwy
  · have hbC : b ∈ endpointNeighbourCover G a x := hwb ▸ hw
    rcases mem_union.mp hbC with h | h
    · exact (hnab ((G.mem_neighborFinset a b).mp (mem_erase.mp h).2)).elim
    · exact (hnxb ((G.mem_neighborFinset x b).mp (mem_erase.mp h).2)).elim
  · have hyC : y ∈ endpointNeighbourCover G a x := hwy ▸ hw
    rcases mem_union.mp hyC with h | h
    · exact (hnay ((G.mem_neighborFinset a y).mp (mem_erase.mp h).2)).elim
    · exact (G.mem_neighborFinset x y).mp (mem_erase.mp h).2

theorem fullDoubleTips_adj_of_types_ne
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r x y : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hx : x ∈ fullDoubleTips G Q r) (hy : y ∈ fullDoubleTips G Q r)
    (hne : rootType G r x ≠ rootType G r y) : G.Adj x y := by
  obtain ⟨_, _, hcx, hsx⟩ := mem_filter.mp hx
  obtain ⟨_, _, hcy, hsy⟩ := mem_filter.mp hy
  have hnxy : ¬ rootType G r x ⊆ rootType G r y := by
    intro h
    exact hne (eq_of_subset_of_card_le h (by omega))
  have hnyx : ¬ rootType G r y ⊆ rootType G r x := by
    intro h
    exact hne (eq_of_subset_of_card_le h (by omega)).symm
  obtain ⟨a, ha, hna⟩ := not_subset.mp hnxy
  obtain ⟨b, hb, hnb⟩ := not_subset.mp hnyx
  obtain ⟨_, e, heQ, he⟩ := mem_filter.mp (hsx ha)
  obtain ⟨_, f, hfQ, hf⟩ := mem_filter.mp (hsy hb)
  exact root_selected_edges_force_adj G Q hQ hN ((mem_rootType G r x a).mp ha).1
    ((mem_rootType G r y b).mp hb).1 hnb hna e f heQ hfQ
    (he.trans Sym2.eq_swap) (hf.trans Sym2.eq_swap)

variable [DecidableRel (conflictGraph G).Adj]

theorem high21_full_double_types_equal_or_disjoint
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (h21 : ∀ e ∈ Q, 21 ≤ (conflictGraph G).degree e)
    {r x y : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hx : x ∈ fullDoubleTips G Q r) (hy : y ∈ fullDoubleTips G Q r) :
    rootType G r x = rootType G r y ∨ Disjoint (rootType G r x) (rootType G r y) := by
  by_cases hne : rootType G r x = rootType G r y
  · exact Or.inl hne
  right
  apply disjoint_left.mpr
  intro a hax hay
  have hxy := fullDoubleTips_adj_of_types_ne G Q hQ hN hx hy hne
  obtain ⟨_, _, _, hsx⟩ := mem_filter.mp hx
  obtain ⟨_, e, heQ, he⟩ := mem_filter.mp (hsx hax)
  exact high21_no_triangle_on_edge G hΔ e he (h21 e heQ) hxy
    ((mem_rootType G r y a).mp hay).2.symm

omit [DecidableRel (conflictGraph G).Adj] in
/-- Four fully selected double tips is a consequence of clique conflicts,
independent root neighbours and maximum degree four. -/
theorem fullDoubleTips_card_le_four
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r)) :
    (fullDoubleTips G Q r).card ≤ 4 := by
  by_cases hempty : fullDoubleTips G Q r = ∅
  · simp [hempty]
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hempty
  obtain ⟨_, hxr, hcx, _⟩ := mem_filter.mp hx
  by_cases heq : ∀ y ∈ fullDoubleTips G Q r, rootType G r y = rootType G r x
  · obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r x).card by omega)
    have hs : fullDoubleTips G Q r ⊆ (G.neighborFinset a).erase r := by
      intro y hy
      have hay : a ∈ rootType G r y := (heq y hy).symm ▸ ha
      exact mem_erase.mpr ⟨(mem_filter.mp hy).2.1,
        (G.mem_neighborFinset a y).mpr ((mem_rootType G r y a).mp hay).2.symm⟩
    have hc := card_le_card hs
    have hca := card_erase_add_one ((G.mem_neighborFinset a r).mpr ((mem_rootType G r x a).mp ha).1.symm)
    have hd := hΔ a
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hca
    omega
  · obtain ⟨y, hy⟩ := not_forall.mp heq
    have hyF : y ∈ fullDoubleTips G Q r := by by_contra hn; exact hy (fun h => (hn h).elim)
    have hne : rootType G r y ≠ rootType G r x := fun h => hy (fun _ => h)
    have hs : fullDoubleTips G Q r ⊆
        (G.neighborFinset x \ G.neighborFinset r) ∪ (G.neighborFinset y \ G.neighborFinset r) := by
      intro z hz
      obtain ⟨_, hzr, hcz, _⟩ := mem_filter.mp hz
      have hzm : z ∈ multipleTips G r := mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩
      have hzn : z ∉ G.neighborFinset r := fun h => multipleTips_not_neighbor G hN hzm
        ((G.mem_neighborFinset r z).mp h)
      by_cases hzx : rootType G r z = rootType G r x
      · apply mem_union_right
        exact mem_sdiff.mpr ⟨(G.mem_neighborFinset y z).mpr
          (fullDoubleTips_adj_of_types_ne G Q hQ hN hyF hz (by rwa [hzx])), hzn⟩
      · apply mem_union_left
        exact mem_sdiff.mpr ⟨(G.mem_neighborFinset x z).mpr
          (fullDoubleTips_adj_of_types_ne G Q hQ hN hx hz (Ne.symm hzx)), hzn⟩
    have hc := (card_le_card hs).trans (card_union_le _ _)
    have hcy := (mem_filter.mp hyF).2.2.1
    have hdx := hΔ x
    have hdy := hΔ y
    have hrx := residual_neighbors_add_type_card G r x
    have hry := residual_neighbors_add_type_card G r y
    omega

end Se20Part.Legacy
