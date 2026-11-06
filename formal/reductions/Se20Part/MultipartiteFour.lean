import Se20Part.MultipartiteLists

noncomputable section
open scoped Classical
namespace Se20Part

theorem triple_intersection_budget {C : Type*} [DecidableEq C]
    (A B D U : Finset C) (hA : A ⊆ U) (hB : B ⊆ U) (hD : D ⊆ U) :
    A.card + B.card + D.card ≤ U.card + (A ∩ B).card + (A ∩ D).card + (B ∩ D).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 := Finset.card_union_add_card_inter (A ∪ B) D
  have h3 := Finset.card_le_card (Finset.union_subset (Finset.union_subset hA hB) hD)
  have h4 : ((A ∪ B) ∩ D).card ≤ (A ∩ D).card + (B ∩ D).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

theorem triple_pair_four {C : Type*} [DecidableEq C]
    (L : Fin 3 → Finset C) (U : Finset C) (hsub : ∀ j, L j ⊆ U)
    (hbudget : U.card + 10 ≤ (L 0).card + (L 1).card + (L 2).card) :
    ∃ p : Equiv.Perm (Fin 3), 4 ≤ (L (p 0) ∩ L (p 1)).card := by
  have hb := triple_intersection_budget (L 0) (L 1) (L 2) U (hsub 0) (hsub 1) (hsub 2)
  by_cases h01 : 4 ≤ (L 0 ∩ L 1).card
  · exact ⟨Equiv.refl _,h01⟩
  by_cases h02 : 4 ≤ (L 0 ∩ L 2).card
  · exact ⟨Equiv.swap 1 2,by simpa [Equiv.swap_apply_def] using h02⟩
  refine ⟨Equiv.swap 0 2,?_⟩
  simpa [Equiv.swap_apply_def,Finset.inter_comm] using (show 4 ≤ (L 1 ∩ L 2).card by omega)

theorem relabel_three_parts {I C : Type*} [DecidableEq C]
    (L : I × Fin 3 → Finset C) (p : I → Equiv.Perm (Fin 3))
    (h : HasListColouring (ThreePartGraph I) (fun v => L (v.1,p v.1 v.2))) :
    HasListColouring (ThreePartGraph I) L := by
  obtain ⟨c,hc,hp⟩ := h
  refine ⟨fun v => c (v.1,(p v.1).symm v.2),?_,?_⟩
  · intro v; simpa using hc (v.1,(p v.1).symm v.2)
  · intro u v huv; exact hp _ _ huv

theorem no_triple_merged_disjoint {I C : Type*} [DecidableEq C]
    (L : I × Fin 3 → Finset C) (hn : ∀ i, ¬ ∃ c, ∀ j, c ∈ L (i,j))
    (p : I → Equiv.Perm (Fin 3)) (i : I) :
    Disjoint (L (i,p i 0) ∩ L (i,p i 1)) (L (i,p i 2)) := by
  apply Finset.disjoint_left.mpr
  intro c hc hc2
  obtain ⟨hc0,hc1⟩ := Finset.mem_inter.mp hc
  apply hn i
  refine ⟨c,?_⟩
  intro j
  obtain ⟨a,rfl⟩ := (p i).surjective j
  fin_cases a <;> assumption

theorem same_colour_part_extend {I C : Type*} [DecidableEq C]
    (L : I × Fin 3 → Finset C) (i : I) (a : C) (ha : ∀ j, a ∈ L (i,j))
    (hrest : HasListColouring (ThreePartGraph {j : I // j ≠ i})
      (fun v => (L (v.1.1,v.2)).erase a)) :
    HasListColouring (ThreePartGraph I) L := by
  obtain ⟨c,hc,hp⟩ := hrest
  let f : I × Fin 3 → C := fun v => if hv : v.1 = i then a else c (⟨v.1,hv⟩,v.2)
  refine ⟨f,?_,?_⟩
  · intro v; dsimp [f]; split_ifs with hv
    · change a ∈ L (v.1,v.2)
      simpa [hv] using ha v.2
    · exact Finset.mem_of_mem_erase (hc (⟨v.1,hv⟩,v.2))
  · intro u v huv
    dsimp [f]; split_ifs with hu hv hv
    · exact (huv (hu.trans hv.symm)).elim
    · exact (Finset.mem_erase.mp (hc (⟨v.1,hv⟩,v.2))).1.symm
    · exact (Finset.mem_erase.mp (hc (⟨u.1,hu⟩,u.2))).1
    · apply hp
      intro he
      exact huv (congrArg Subtype.val he)

theorem four_parts_seven_choosable {I C : Type*} [Fintype I] [DecidableEq C]
    (hI : Fintype.card I = 4) (L : I × Fin 3 → Finset C)
    (hL : ∀ v, 7 ≤ (L v).card) : HasListColouring (ThreePartGraph I) L := by
  apply small_colour_pool (ThreePartGraph I) 7 _ L hL
  intro L hL hpool
  by_cases ht : ∃ i c, ∀ j, c ∈ L (i,j)
  · obtain ⟨i,c,hc⟩ := ht
    apply same_colour_part_extend L i c hc
    apply three_parts_six_choosable
    · simp [Fintype.card_subtype_compl,hI]
    · intro v
      have h := hL (v.1.1,v.2)
      have herase := Finset.card_erase_eq_ite (s := L (v.1.1,v.2)) (a := c)
      split_ifs at herase <;> omega
  push_neg at ht
  have hn : ∀ i, ¬ ∃ c, ∀ j, c ∈ L (i,j) := by simpa using ht
  have hp : (Finset.univ.biUnion L).card ≤ 11 := by
    simp only [Fintype.card_prod,Fintype.card_fin,hI] at hpool; omega
  have hex : ∀ i, ∃ p : Equiv.Perm (Fin 3), 4 ≤ (L (i,p 0) ∩ L (i,p 1)).card := by
    intro i
    apply triple_pair_four (fun j => L (i,j)) (Finset.univ.biUnion L)
    · intro j c hc; exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_univ _,hc⟩
    · have h0 := hL (i,0); have h1 := hL (i,1); have h2 := hL (i,2); omega
  choose p hpM using hex
  apply relabel_three_parts L p
  apply merge_three_parts
  apply paired_lists_hall _ _ 4 7 hpM (fun i => hL (i,p i 2))
    (no_triple_merged_disjoint L hn p) (by omega) (by omega)
  intro A
  by_cases hA : A = ∅
  · simp [hA]
  obtain ⟨i,hi⟩ := Finset.nonempty_iff_ne_empty.mpr hA
  exact ((Finset.card_le_univ A).trans_eq hI).trans ((hpM i).trans (Finset.card_le_card
    (show L (i,p i 0) ∩ L (i,p i 1) ⊆ A.biUnion (fun j => L (j,p j 0) ∩ L (j,p j 1)) from
      fun c hc => Finset.mem_biUnion.mpr ⟨i,hi,hc⟩)))

end Se20Part
