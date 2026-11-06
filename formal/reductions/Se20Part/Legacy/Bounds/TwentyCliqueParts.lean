module

public import Se20Part.Legacy.Bounds.TwentyCliqueComponent

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The four fully selected double tips split into two pairs. A tip has
exactly the opposite pair as its neighbours outside the root neighbourhood. -/
theorem four_full_double_tips_pair_partition
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hfour : (fullDoubleTips G Q r).card = 4)
    {x : V} (hx : x ∈ fullDoubleTips G Q r) :
    ((fullDoubleTips G Q r).filter (fun y => rootType G r y = rootType G r x)).card = 2 ∧
    ((fullDoubleTips G Q r).filter (fun y => rootType G r y ≠ rootType G r x)).card = 2 ∧
    G.neighborFinset x = rootType G r x ∪
      (fullDoubleTips G Q r).filter (fun y => rootType G r y ≠ rootType G r x) := by
  let P := fullDoubleTips G Q r
  let E := P.filter (fun y => rootType G r y = rootType G r x)
  let D := P.filter (fun y => rootType G r y ≠ rootType G r x)
  have hcx := (mem_filter.mp hx).2.2.1
  have hnotN : ∀ y ∈ P, y ∉ G.neighborFinset r := by
    intro y hy hn
    obtain ⟨_, hyr, hcy, _⟩ := mem_filter.mp hy
    exact multipleTips_not_neighbor G hN
      (mem_filter.mpr ⟨mem_univ _, hyr, by omega⟩)
      ((G.mem_neighborFinset r y).mp hn)
  have hE3 : E.card ≤ 3 := by
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootType G r x).card by omega)
    have hs : E ⊆ (G.neighborFinset a).erase r := by
      intro y hy
      obtain ⟨hyP, heq⟩ := mem_filter.mp hy
      have hay := (mem_rootType G r y a).mp (heq.symm ▸ ha)
      exact mem_erase.mpr ⟨(mem_filter.mp hyP).2.1,
        (G.mem_neighborFinset a y).mpr hay.2.symm⟩
    have hc := card_le_card hs
    have he := card_erase_add_one ((G.mem_neighborFinset a r).mpr
      ((mem_rootType G r x a).mp ha).1.symm)
    have hd := hΔ a
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at he
    omega
  have hpart : E.card + D.card = 4 := by
    simpa only [E, D, P, hfour] using
      card_filter_add_card_filter_not (s := P) (p := fun y => rootType G r y = rootType G r x)
  obtain ⟨z, hz⟩ := card_pos.mp (show 0 < D.card by omega)
  obtain ⟨hzP, hzx⟩ := mem_filter.mp hz
  have hE2 : E.card ≤ 2 := by
    have hs : E ⊆ G.neighborFinset z \ G.neighborFinset r := by
      intro y hy
      obtain ⟨hyP, hyx⟩ := mem_filter.mp hy
      exact mem_sdiff.mpr ⟨(G.mem_neighborFinset z y).mpr
        (fullDoubleTips_adj_of_types_ne G Q hQ hN hzP hyP (by rwa [hyx])), hnotN y hyP⟩
    have hc := card_le_card hs
    have hr := residual_neighbors_add_type_card G r z
    have hd := hΔ z
    have ht := (mem_filter.mp hzP).2.2.1
    omega
  have hs : D ⊆ G.neighborFinset x \ G.neighborFinset r := by
    intro y hy
    obtain ⟨hyP, hyx⟩ := mem_filter.mp hy
    exact mem_sdiff.mpr ⟨(G.mem_neighborFinset x y).mpr
      (fullDoubleTips_adj_of_types_ne G Q hQ hN hx hyP (Ne.symm hyx)), hnotN y hyP⟩
  have hr := residual_neighbors_add_type_card G r x
  have hd := hΔ x
  have hDc := card_le_card hs
  have heq : D = G.neighborFinset x \ G.neighborFinset r :=
    eq_of_subset_of_card_le hs (by omega)
  refine ⟨by change E.card = 2; omega, by change D.card = 2; omega, ?_⟩
  change G.neighborFinset x = rootType G r x ∪ D
  rw [heq, rootType_eq_neighbor_inter]
  ext y
  simp only [mem_union, mem_inter, mem_sdiff]
  tauto

/-- The root labels split into the same two complementary pairs. -/
theorem full_double_types_equal_or_complement
    (Q : Finset G.edgeSet) (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    {r : V} (hN : G.IsIndepSet (G.neighborSet r))
    (hA : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a))
    (hNr : (G.neighborFinset r).card = 4)
    {x y : V} (hx : x ∈ fullDoubleTips G Q r) (hy : y ∈ fullDoubleTips G Q r)
    (hne : rootType G r y ≠ rootType G r x) :
    rootType G r y = G.neighborFinset r \ rootType G r x := by
  have hxy := fullDoubleTips_adj_of_types_ne G Q hQ hN hx hy hne.symm
  have hdis : Disjoint (rootType G r y) (rootType G r x) := by
    apply disjoint_left.mpr
    intro a hay hax
    exact hA a (filter_subset _ _ hax) ((mem_rootType G r x a).mp hax).2.symm
      ((mem_rootType G r y a).mp hay).2.symm hxy.ne hxy
  have hs : rootType G r y ⊆ G.neighborFinset r \ rootType G r x := by
    intro a ha
    exact mem_sdiff.mpr ⟨filter_subset _ _ ha, fun h => disjoint_left.mp hdis ha h⟩
  have hc := card_sdiff_add_card_eq_card (filter_subset (G.Adj x) (G.neighborFinset r))
  have hcx := (mem_filter.mp hx).2.2.1
  have hcy := (mem_filter.mp hy).2.2.1
  apply eq_of_subset_of_card_le hs
  change (G.neighborFinset r \ rootType G r x).card + (rootType G r x).card = _ at hc
  omega

/-- A concrete finite realization of a whole C5[2] component. The five parts
are independent pairs, and the equations specify all original neighbours. -/
def IsFiveCycleBlowupComponent (S : Finset V) : Prop :=
  ∃ B A X Y C : Finset V,
    B.card = 2 ∧ A.card = 2 ∧ X.card = 2 ∧ Y.card = 2 ∧ C.card = 2 ∧
    List.Pairwise Disjoint [B, A, X, Y, C] ∧
    S = B ∪ A ∪ X ∪ Y ∪ C ∧
    (∀ v ∈ B, G.neighborFinset v = A ∪ C) ∧
    (∀ v ∈ A, G.neighborFinset v = B ∪ X) ∧
    (∀ v ∈ X, G.neighborFinset v = A ∪ Y) ∧
    (∀ v ∈ Y, G.neighborFinset v = X ∪ C) ∧
    (∀ v ∈ C, G.neighborFinset v = B ∪ Y)

end Se20Part.Legacy
