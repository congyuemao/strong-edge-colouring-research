module

public import Se20Part.Legacy.Bounds.TwentyCliqueParts

@[expose] public section

namespace Se20Part.Legacy

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
theorem neighbors_eq_of_four_subset (hΔ : ∀ x, G.degree x ≤ 4)
    (v : V) (S : Finset V) (hc : S.card = 4) (hs : S ⊆ G.neighborFinset v) :
    G.neighborFinset v = S := by
  apply (eq_of_subset_of_card_le hs ?_).symm
  rw [SimpleGraph.card_neighborFinset_eq_degree, hc]
  exact hΔ v

variable [DecidableRel (conflictGraph G).Adj]

set_option maxHeartbeats 400000 in
/-- Every twenty-clique is the complete edge set of a whole C5[2] component,
expressed here by five disjoint pairs and exact original-neighbour equations. -/
theorem twenty_clique_support_is_five_cycle_blowup
    (hΔ : ∀ x, G.degree x ≤ 4) (Q : Finset G.edgeSet)
    (hQ : (conflictGraph G).IsClique (Q : Set G.edgeSet)) (hq : Q.card = 20) :
    IsFiveCycleBlowupComponent G (selectedSupport G Q) := by
  obtain ⟨r, hR⟩ := twenty_clique_exists_root_four G hΔ Q hQ (by omega)
  obtain ⟨z, hzr, hz⟩ := twenty_clique_exists_type_four G hΔ Q hQ (by omega) r hR
  have hN := twenty_clique_root_neighborhood_independent G hΔ Q hQ (by omega) r hR
  obtain ⟨_, ho, _, _⟩ := twenty_clique_quad_counts G hΔ Q hQ (by omega) hR hzr hz
  obtain ⟨_, hP4, _⟩ := twenty_clique_quad_double_tips G hΔ Q hQ (by omega) hR hzr hz
  obtain ⟨hdA, hfull⟩ := twenty_clique_labels_saturated_of_outer_le_four G hΔ Q (by omega) r hR (by omega)
  have hAind : ∀ a ∈ G.neighborFinset r, G.IsIndepSet (G.neighborSet a) := by
    intro a ha
    apply twenty_clique_root_neighborhood_independent G hΔ Q hQ (by omega) a
    rw [rootLabels_card, hdA a ha]
  let P := fullDoubleTips G Q r
  obtain ⟨x, hx⟩ := card_pos.mp (show 0 < P.card by change 0 < (fullDoubleTips G Q r).card; omega)
  let B : Finset V := {r, z}
  let A := rootType G r x
  let C := G.neighborFinset r \ A
  let X := P.filter (fun y => rootType G r y = A)
  let Y := P.filter (fun y => rootType G r y ≠ A)
  have hAc : A.card = 2 := (mem_filter.mp hx).2.2.1
  have hNr : (G.neighborFinset r).card = 4 := by
    have hc := card_le_card (rootLabels_subset_neighbors G Q r)
    have hd := hΔ r
    simp only [SimpleGraph.card_neighborFinset_eq_degree] at hc ⊢
    omega
  have hAs : A ⊆ G.neighborFinset r := filter_subset _ _
  have hCs : C ⊆ G.neighborFinset r := sdiff_subset
  have hCc : C.card = 2 := by
    have hc := card_sdiff_add_card_eq_card hAs
    change C.card + A.card = _ at hc
    omega
  have hBc : B.card = 2 := by simp [B, hzr.symm]
  have hXp := four_full_double_tips_pair_partition G hΔ Q hQ hN hP4 hx
  have hXc : X.card = 2 := hXp.1
  have hYc : Y.card = 2 := hXp.2.1
  have hXP : X ⊆ P := filter_subset _ _
  have hYP : Y ⊆ P := filter_subset _ _
  have hpartsP : X ∪ Y = P := filter_union_filter_not_eq _ _
  have hpartsN : A ∪ C = G.neighborFinset r := by
    ext a
    simp only [C, mem_union, mem_sdiff]
    exact ⟨fun h => h.elim (fun h => hAs h) (fun h => h.1), fun h => by tauto⟩
  have hPnotN : Disjoint P (G.neighborFinset r) := by
    apply disjoint_left.mpr
    intro v hv hvN
    obtain ⟨_, hvr, hvt, _⟩ := mem_filter.mp hv
    exact multipleTips_not_neighbor G hN (mem_filter.mpr ⟨mem_univ _, hvr, by omega⟩)
      ((G.mem_neighborFinset r v).mp hvN)
  have hzP : z ∉ P := by
    intro h
    have ht := (mem_filter.mp h).2.2.1
    omega
  have hrP : r ∉ P := fun h => (mem_filter.mp h).2.1 rfl
  have hrN : r ∉ G.neighborFinset r := by simp
  have hzN : z ∉ G.neighborFinset r := fun h => multipleTips_not_neighbor G hN
    (mem_filter.mpr ⟨mem_univ _, hzr, by omega⟩) ((G.mem_neighborFinset r z).mp h)
  have hBN : Disjoint B (G.neighborFinset r) := by
    apply disjoint_left.mpr
    intro v hv hvN
    rcases (show v = r ∨ v = z by simpa only [B, mem_insert, mem_singleton] using hv) with rfl | rfl
    · exact hrN hvN
    · exact hzN hvN
  have hBP : Disjoint B P := by
    apply disjoint_left.mpr
    intro v hv hvP
    rcases (show v = r ∨ v = z by simpa only [B, mem_insert, mem_singleton] using hv) with rfl | rfl
    · exact hrP hvP
    · exact hzP hvP
  have hAC : Disjoint A C := disjoint_sdiff_self_right
  have hXY : Disjoint X Y := disjoint_filter_filter_not _ _ _
  have hBA := hBN.mono_right hAs
  have hBC := hBN.mono_right hCs
  have hBX := hBP.mono_right hXP
  have hBY := hBP.mono_right hYP
  have hAX := hPnotN.symm.mono hAs hXP
  have hAY := hPnotN.symm.mono hAs hYP
  have hXC := hPnotN.mono hXP hCs
  have hYC := hPnotN.mono hYP hCs
  have hdis : List.Pairwise Disjoint [B, A, X, Y, C] := by
    simp [List.pairwise_cons, hBA, hBX, hBY, hBC, hAX, hAY, hAC, hXY, hXC, hYC]
  have htypeX : ∀ v ∈ X, rootType G r v = A := fun _ hv => (mem_filter.mp hv).2
  have htypeY : ∀ v ∈ Y, rootType G r v = C := by
    intro v hv
    exact full_double_types_equal_or_complement G Q hQ hN hAind hNr hx
      (mem_filter.mp hv).1 (mem_filter.mp hv).2
  have hneAC : A ≠ C := by
    intro h
    have hself : Disjoint A A := h.symm ▸ hAC
    have hempty : A = ∅ := disjoint_self.mp hself
    rw [hempty, card_empty] at hAc
    omega
  have hzType : rootType G r z = G.neighborFinset r :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have hzNeigh : G.neighborFinset z = G.neighborFinset r := by
    apply neighbors_eq_of_four_subset G hΔ z _ hNr
    intro a ha
    exact (G.mem_neighborFinset z a).mpr ((mem_rootType G r z a).mp (hzType.symm ▸ ha)).2
  have hneighB : ∀ v ∈ B, G.neighborFinset v = A ∪ C := by
    intro v hv
    rcases (show v = r ∨ v = z by simpa only [B, mem_insert, mem_singleton] using hv) with rfl | rfl
    · exact hpartsN.symm
    · exact hzNeigh.trans hpartsN.symm
  have hneighX : ∀ v ∈ X, G.neighborFinset v = A ∪ Y := by
    intro v hv
    have he := (four_full_double_tips_pair_partition G hΔ Q hQ hN hP4 (hXP hv)).2.2
    simpa only [htypeX v hv] using he
  have hneighY : ∀ v ∈ Y, G.neighborFinset v = X ∪ C := by
    intro v hv
    have he := (four_full_double_tips_pair_partition G hΔ Q hQ hN hP4 (hYP hv)).2.2
    have hfilter : P.filter (fun w => rootType G r w ≠ rootType G r v) = X := by
      ext w
      constructor
      · intro hw
        obtain ⟨hwP, hn⟩ := mem_filter.mp hw
        have hwpart : w ∈ X ∪ Y := hpartsP.symm ▸ hwP
        rcases mem_union.mp hwpart with h | h
        · exact h
        · exact (hn ((htypeY w h).trans (htypeY v hv).symm)).elim
      · intro hw
        exact mem_filter.mpr ⟨hXP hw, by rw [htypeX w hw, htypeY v hv]; exact hneAC⟩
    change _ = rootType G r v ∪ P.filter (fun w => rootType G r w ≠ rootType G r v) at he
    rw [hfilter, htypeY v hv, union_comm] at he
    exact he
  have hneighA : ∀ v ∈ A, G.neighborFinset v = B ∪ X := by
    intro v hv
    apply neighbors_eq_of_four_subset G hΔ v _ (by rw [card_union_of_disjoint hBX, hBc, hXc])
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · rcases (show w = r ∨ w = z by simpa only [B, mem_insert, mem_singleton] using hw) with hwr | hwz
      · subst w
        exact (G.mem_neighborFinset v r).mpr ((G.mem_neighborFinset r v).mp (hAs hv)).symm
      · subst w
        exact (G.mem_neighborFinset v z).mpr
          (((G.mem_neighborFinset z v).mp (hzNeigh.symm ▸ hAs hv)).symm)
    · exact (G.mem_neighborFinset v w).mpr
        ((mem_rootType G r w v).mp ((htypeX w hw).symm ▸ hv)).2.symm
  have hneighC : ∀ v ∈ C, G.neighborFinset v = B ∪ Y := by
    intro v hv
    apply neighbors_eq_of_four_subset G hΔ v _ (by rw [card_union_of_disjoint hBY, hBc, hYc])
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · rcases (show w = r ∨ w = z by simpa only [B, mem_insert, mem_singleton] using hw) with hwr | hwz
      · subst w
        exact (G.mem_neighborFinset v r).mpr ((G.mem_neighborFinset r v).mp (hCs hv)).symm
      · subst w
        exact (G.mem_neighborFinset v z).mpr
          (((G.mem_neighborFinset z v).mp (hzNeigh.symm ▸ hCs hv)).symm)
    · exact (G.mem_neighborFinset v w).mpr
        ((mem_rootType G r w v).mp ((htypeY w hw).symm ▸ hv)).2.symm
  have hS : selectedSupport G Q = insert r (insert z (G.neighborFinset r ∪ P)) := by
    apply Subset.antisymm (twenty_clique_quad_support_subset G hΔ Q hQ (by omega) hR hzr hz)
    intro v hv
    have hd : (edgeIncidences G Q v).card = 4 := by
      rcases mem_insert.mp hv with h | hv
      · subst v; rwa [rootLabels_card] at hR
      rcases mem_insert.mp hv with h | hv
      · subst v
        have hc := card_le_card (hfull z)
        have hb := (edgeIncidences_card_le_degree G Q z).trans (hΔ z)
        rw [rootLabels_card] at hc
        omega
      rcases mem_union.mp hv with h | h
      · exact hdA v h
      · exact twenty_clique_quad_double_tips_selected_degree_four G hΔ Q hQ (by omega) hR hzr hz v h
    exact mem_filter.mpr ⟨mem_univ _, by omega⟩
  refine ⟨B, A, X, Y, C, hBc, hAc, hXc, hYc, hCc, hdis, ?_,
    hneighB, hneighA, hneighX, hneighY, hneighC⟩
  rw [hS, ← hpartsN, ← hpartsP]
  ext v
  simp only [B, mem_insert, mem_singleton, mem_union, or_assoc, or_left_comm, or_comm]

end Se20Part.Legacy
