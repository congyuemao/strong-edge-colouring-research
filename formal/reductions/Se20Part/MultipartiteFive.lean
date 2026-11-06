import Se20Part.MultipartiteFour

noncomputable section
open scoped Classical
namespace Se20Part

theorem triple_pair_repair {C : Type*} [DecidableEq C]
    (L : Fin 3 → Finset C) (U : Finset C) (hsub : ∀ j, L j ⊆ U)
    (hbudget : U.card + 10 ≤ (L 0).card + (L 1).card + (L 2).card)
    (hfour : (L 0 ∩ L 1).card = 4) (hn : ¬ ∃ c, ∀ j, c ∈ L j) :
    ∃ p : Equiv.Perm (Fin 3), 3 ≤ (L (p 0) ∩ L (p 1)).card ∧
      Disjoint (L (p 0) ∩ L (p 1)) (L 0 ∩ L 1) := by
  have hb := triple_intersection_budget (L 0) (L 1) (L 2) U (hsub 0) (hsub 1) (hsub 2)
  have hd02 : Disjoint (L 0 ∩ L 2) (L 0 ∩ L 1) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    apply hn
    refine ⟨c,?_⟩
    intro j; fin_cases j
    · exact (Finset.mem_inter.mp hc).1
    · exact (Finset.mem_inter.mp hd).2
    · exact (Finset.mem_inter.mp hc).2
  have hd12 : Disjoint (L 1 ∩ L 2) (L 0 ∩ L 1) := by
    apply Finset.disjoint_left.mpr
    intro c hc hd
    apply hn
    refine ⟨c,?_⟩
    intro j; fin_cases j
    · exact (Finset.mem_inter.mp hd).1
    · exact (Finset.mem_inter.mp hc).1
    · exact (Finset.mem_inter.mp hc).2
  by_cases h02 : 3 ≤ (L 0 ∩ L 2).card
  · exact ⟨Equiv.swap 1 2,by simpa [Equiv.swap_apply_def] using h02,
      by simpa [Equiv.swap_apply_def] using hd02⟩
  exact ⟨Equiv.swap 0 2,
    by simpa [Equiv.swap_apply_def,Finset.inter_comm] using (show 3 ≤ (L 1 ∩ L 2).card by omega),
    by simpa [Equiv.swap_apply_def,Finset.inter_comm] using hd12⟩

theorem four_uniform_one_disjoint_hall {I C : Type*} [Fintype I] [DecidableEq C]
    (hI : Fintype.card I = 5) (M : I → Finset C) (i : I) (U : Finset C)
    (hU : U.card = 4) (hm : 3 ≤ (M i).card) (hd : Disjoint (M i) U)
    (heq : ∀ j, j ≠ i → M j = U) :
    ∀ A : Finset I, A.card ≤ (A.biUnion M).card := by
  intro A
  by_cases hA : A = ∅
  · simp [hA]
  obtain ⟨j,hj⟩ := Finset.nonempty_iff_ne_empty.mpr hA
  by_cases hi : i ∈ A
  · by_cases ho : ∃ t ∈ A, t ≠ i
    · obtain ⟨t,ht,hti⟩ := ho
      have hsub : M i ∪ U ⊆ A.biUnion M := by
        intro c hc
        rcases Finset.mem_union.mp hc with hc | hc
        · exact Finset.mem_biUnion.mpr ⟨i,hi,hc⟩
        · exact Finset.mem_biUnion.mpr ⟨t,ht,by simpa [heq t hti] using hc⟩
      have hh := Finset.card_le_card hsub
      rw [Finset.card_union_of_disjoint hd,hU] at hh
      have ht := Finset.card_le_univ A
      omega
    · have hs : A ⊆ {i} := by
        intro t ht
        apply Finset.mem_singleton.mpr
        by_contra hti
        exact ho ⟨t,ht,hti⟩
      have ht := Finset.card_le_card hs
      have hl := Finset.card_le_card (show M i ⊆ A.biUnion M from
        fun c hc => Finset.mem_biUnion.mpr ⟨i,hi,hc⟩)
      simp only [Finset.card_singleton] at ht
      omega
  · have hs : A ⊆ (Finset.univ : Finset I).erase i := by
      intro t ht; exact Finset.mem_erase.mpr ⟨fun he => hi (he ▸ ht),Finset.mem_univ _⟩
    have ht := Finset.card_le_card hs
    simp only [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,hI] at ht
    have hji : j ≠ i := fun he => hi (he ▸ hj)
    have hl := Finset.card_le_card (show M j ⊆ A.biUnion M from
      fun c hc => Finset.mem_biUnion.mpr ⟨j,hj,hc⟩)
    rw [heq j hji,hU] at hl
    omega

theorem five_parts_eight_choosable {I C : Type*} [Fintype I] [DecidableEq C]
    (hI : Fintype.card I = 5) (L : I × Fin 3 → Finset C)
    (hL : ∀ v, 8 ≤ (L v).card) : HasListColouring (ThreePartGraph I) L := by
  apply small_colour_pool (ThreePartGraph I) 8 _ L hL
  intro L hL hpool
  by_cases ht : ∃ i c, ∀ j, c ∈ L (i,j)
  · obtain ⟨i,c,hc⟩ := ht
    apply same_colour_part_extend L i c hc
    apply four_parts_seven_choosable
    · simp [Fintype.card_subtype_compl,hI]
    · intro v
      have h := hL (v.1.1,v.2)
      have he := Finset.card_erase_eq_ite (s := L (v.1.1,v.2)) (a := c)
      split_ifs at he <;> omega
  have hn : ∀ i, ¬ ∃ c, ∀ j, c ∈ L (i,j) := by simpa only [not_exists] using ht
  have hp : (Finset.univ.biUnion L).card ≤ 14 := by
    simp only [Fintype.card_prod,Fintype.card_fin,hI] at hpool; omega
  have hex : ∀ i, ∃ p : Equiv.Perm (Fin 3), 4 ≤ (L (i,p 0) ∩ L (i,p 1)).card := by
    intro i
    apply triple_pair_four (fun j => L (i,j)) (Finset.univ.biUnion L)
    · intro j c hc; exact Finset.mem_biUnion.mpr ⟨(i,j),Finset.mem_univ _,hc⟩
    · have h0 := hL (i,0); have h1 := hL (i,1); have h2 := hL (i,2); omega
  choose p hpM using hex
  let K : I × Fin 3 → Finset C := fun v => L (v.1,p v.1 v.2)
  let M : I → Finset C := fun i => K (i,0) ∩ K (i,1)
  apply relabel_three_parts L p
  change HasListColouring (ThreePartGraph I) K
  by_cases hh : ∀ A : Finset I, A.card ≤ (A.biUnion M).card
  · apply merge_three_parts
    exact paired_lists_hall M (fun i => K (i,2)) 4 8 hpM
      (fun i => hL (i,p i 2)) (no_triple_merged_disjoint L hn p) (by omega) (by omega) hh
  have huniform := near_full_lists_sdr_or_uniform M 5 (by omega) hI hpM
  obtain ⟨U,hUc,hMu⟩ := huniform.resolve_left (fun h => hh
    ((Finset.all_card_le_biUnion_card_iff_existsInjective' M).mpr h))
  obtain ⟨i⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card I by omega)
  have hKn : ¬ ∃ c, ∀ j, c ∈ K (i,j) := by
    rintro ⟨c,hc⟩
    apply hn i
    exact ⟨c,fun j => by simpa [K] using hc ((p i).symm j)⟩
  obtain ⟨q,hq,hqd⟩ := triple_pair_repair (fun j => K (i,j)) (Finset.univ.biUnion L)
    (fun j c hc => Finset.mem_biUnion.mpr ⟨(i,p i j),Finset.mem_univ _,hc⟩)
    (by have h0 := hL (i,p i 0); have h1 := hL (i,p i 1); have h2 := hL (i,p i 2); dsimp [K]; omega)
    (by change (M i).card = 4; rw [hMu i]; exact hUc) hKn
  let q' : I → Equiv.Perm (Fin 3) := fun j => if j = i then q else Equiv.refl _
  let M' : I → Finset C := fun j => K (j,q' j 0) ∩ K (j,q' j 1)
  have hM'i : M' i = K (i,q 0) ∩ K (i,q 1) := by simp [M',q']
  have hM'j : ∀ j, j ≠ i → M' j = U := by
    intro j hji; simpa [M',q',hji,M] using hMu j
  have hM' : ∀ j, 3 ≤ (M' j).card := by
    intro j
    by_cases hji : j = i
    · subst j; simpa [hM'i] using hq
    · rw [hM'j j hji,hUc]; omega
  have hM'd : Disjoint (M' i) U := by
    rw [hM'i,← hMu i]; exact hqd
  apply relabel_three_parts K q'
  apply merge_three_parts
  apply paired_lists_hall M' (fun j => K (j,q' j 2)) 3 8 hM'
    (fun j => hL (j,p j (q' j 2))) _ (by omega) (by omega)
    (four_uniform_one_disjoint_hall hI M' i U hUc (by simpa [hM'i] using hq) hM'd hM'j)
  apply no_triple_merged_disjoint
  intro j hc
  obtain ⟨c,hc⟩ := hc
  exact hn j ⟨c,fun a => by simpa [K] using hc ((p j).symm a)⟩

end Se20Part
