module

public import Se20Part.Legacy.Bounds.High20Local

@[expose] public section

namespace Se20Part.Legacy

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem outer_avoiding_card_le_four_of_other_types_le_two
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet))
    (r : V) (hR : (rootLabels G Q r).card = 4)
    (hN : G.IsIndepSet (G.neighborSet r))
    (x : V) (ht : ∀ y, y ≠ r → y ≠ x → (rootType G r y).card ≤ 2) :
    ((outerEdges G Q r).filter (fun e => x ∉ e.val)).card ≤ 4 := by
  let O := (outerEdges G Q r).filter (fun e => x ∉ e.val)
  have hP : ∀ e ∈ O, ∀ y ∈ e.val, y ∈ multipleTips G r := by
    intro e he y hye
    obtain ⟨heo, hxe⟩ := mem_filter.mp he
    obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
    have hends := outerEdges_endpoints G Q r e hev.symm heo
    have hux : u ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_left u v)
    have hvx : v ≠ x := fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_right u v)
    have hu := ht u hends.2.1 hux
    have hv := ht v hends.2.2.1 hvx
    have hc := (card_le_card (outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo)).trans (card_union_le _ _)
    rw [← hev, Sym2.mem_iff] at hye
    rcases hye with rfl | rfl
    · exact mem_filter.mpr ⟨mem_univ _, hends.2.1, by omega⟩
    · exact mem_filter.mpr ⟨mem_univ _, hends.2.2.1, by omega⟩
  have hd : ∀ x ∈ multipleTips G r, (G.neighborFinset x ∩ multipleTips G r).card ≤ 2 := by
    intro x hx
    have hs : G.neighborFinset x ∩ multipleTips G r ⊆ G.neighborFinset x \ G.neighborFinset r := by
      intro y hy
      obtain ⟨hyN, hyP⟩ := mem_inter.mp hy
      exact mem_sdiff.mpr ⟨hyN, fun h => multipleTips_not_neighbor G hN hyP
        ((G.mem_neighborFinset r y).mp h)⟩
    have hc := card_le_card hs
    have hi := residual_neighbors_add_type_card G r x
    have hd := hΔ x
    have ht := (mem_filter.mp hx).2.2
    omega
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (rootLabels G Q r).card by omega)
  let L := (multipleTips G r).filter (fun x => a ∈ rootType G r x)
  apply degree_two_clique_card_le_four_of_selected_bipartition G O
    (fun e he f hf hef => hQ (mem_filter.mp (mem_filter.mp he).1).1 (mem_filter.mp (mem_filter.mp hf).1).1 hef)
    (multipleTips G r) hP hd L
  intro e heO
  obtain ⟨heo, hxe⟩ := mem_filter.mp heO
  obtain ⟨u, v, hev⟩ := Sym2.exists.mp (show ∃ z : Sym2 V, z = e.val from ⟨e.val, rfl⟩)
  have huP := hP e heO u (hev ▸ Sym2.mem_mk_left u v)
  have hvP := hP e heO v (hev ▸ Sym2.mem_mk_right u v)
  have hu := ht u (mem_filter.mp huP).2.1 (fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_left u v))
  have hv := ht v (mem_filter.mp hvP).2.1 (fun h => hxe (hev ▸ h ▸ Sym2.mem_mk_right u v))
  have hcov := outer_edge_types_cover_root_labels G Q hQ r e hev.symm heo
  have hc := card_le_card hcov
  have hi := card_union_add_card_inter (rootType G r u) (rootType G r v)
  have hdis : Disjoint (rootType G r u) (rootType G r v) := by
    apply disjoint_iff_inter_eq_empty.mpr
    apply card_eq_zero.mp
    omega
  have hex : ∃ w ∈ L, w ∈ e.val := by
    rcases mem_union.mp (hcov ha) with hau | hav
    · exact ⟨u, mem_filter.mpr ⟨huP, hau⟩, hev ▸ Sym2.mem_mk_left u v⟩
    · exact ⟨v, mem_filter.mpr ⟨hvP, hav⟩, hev ▸ Sym2.mem_mk_right u v⟩
  have hn : ¬ ∀ w ∈ e.val, w ∈ L := by
    intro hall
    have huL := hall u (hev ▸ Sym2.mem_mk_left u v)
    have hvL := hall v (hev ▸ Sym2.mem_mk_right u v)
    exact disjoint_left.mp hdis (mem_filter.mp huL).2 (mem_filter.mp hvL).2
  rw [edge_endpoint_count]
  simp only [hex, hn, ite_true, ite_false, add_zero]

end Se20Part.Legacy
