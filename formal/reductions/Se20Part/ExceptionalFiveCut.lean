import Se20Part.FiveCutChoices

noncomputable section
open scoped Classical
namespace Se20Part

/-- Counting repeated colours against a group of small unions of single
colours. The complement stars are charged only their actual size budget. -/
theorem single_union_incidence_bound {I C : Type*} [Fintype I] [Fintype C]
    [DecidableEq C] (S L : I → Finset C) (b l : ℕ)
    (hS : ∀ i, (S i).card ≤ b) (hL : ∀ i, l ≤ (L i).card)
    (hdis : ∀ i, Disjoint (L i) (S i)) (J : Finset I) :
    let M := Finset.univ.filter (fun c : C =>
      2 ≤ (Finset.univ.filter (fun i => c ∈ S i)).card)
    let U := J.biUnion (fun i => (L i).filter
      (fun c => (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1))
    2 * M.card ≤ J.card * (U.card + M.card - l) +
      (Fintype.card I - J.card) * b := by
  intro M U
  have hb : ∀ i ∈ J, l + (M ∩ S i).card ≤ U.card + M.card := by
    intro i hi
    have hcover : L i ⊆ U ∪ (M \ S i) := by
      intro c hc
      by_cases hcm : c ∈ M
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hcm,fun hs => Finset.disjoint_left.mp (hdis i) hc hs⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i,hi,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
        have hnot : ¬ 2 ≤ (Finset.univ.filter (fun j => c ∈ S j)).card := by
          simpa only [M,Finset.mem_filter,Finset.mem_univ,true_and] using hcm
        omega
    have hle := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have he := Finset.card_sdiff_add_card_inter M (S i)
    have := hL i
    omega
  calc
    2 * M.card = ∑ _c ∈ M, 2 := by simp [Nat.mul_comm]
    _ ≤ ∑ c ∈ M, (Finset.univ.filter (fun i => c ∈ S i)).card :=
      Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
    _ = ∑ i : I, (M ∩ S i).card := star_incidence_count S M
    _ = (∑ i ∈ J, (M ∩ S i).card) +
        ∑ i ∈ Finset.univ \ J, (M ∩ S i).card :=
      (Finset.sum_add_sum_compl J _).symm
    _ ≤ (∑ _i ∈ J, (U.card + M.card - l)) + ∑ _i ∈ Finset.univ \ J, b := by
      exact Nat.add_le_add (Finset.sum_le_sum (fun i hi => by have := hb i hi; omega))
        (Finset.sum_le_sum (fun i _ =>
          (Finset.card_le_card Finset.inter_subset_right).trans (hS i)))
    _ = _ := by simp [Finset.card_sdiff_of_subset (Finset.subset_univ J)]

/-- After removing a colour common to all five stars, each star has size
at most two. Its single-colour lists have size four, and every union of
at least two such lists has size at least five. -/
theorem five_two_stars_robust {C : Type*} [Fintype C] [DecidableEq C]
    (S L : Fin 5 → Finset C) (hS : ∀ i, (S i).card ≤ 2)
    (hL : ∀ i, 8 ≤ (L i).card) (hdis : ∀ i, Disjoint (L i) (S i)) :
    let X := fun i => (L i).filter
      (fun c => (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1)
    (∀ i, 4 ≤ (X i).card) ∧
      ∀ J : Finset (Fin 5), 2 ≤ J.card → 5 ≤ (J.biUnion X).card := by
  intro X
  let M := Finset.univ.filter (fun c : C =>
    2 ≤ (Finset.univ.filter (fun i => c ∈ S i)).card)
  have hM : M.card ≤ 5 := by
    have h := repeated_colours_bound S M 2 hS
      (fun c hc => (Finset.mem_filter.mp hc).2)
    norm_num at h
    omega
  have hbase : ∀ J : Finset (Fin 5), J.Nonempty → 8 ≤ (J.biUnion X).card + M.card := by
    intro J ⟨i,hi⟩
    have hcover : L i ⊆ J.biUnion X ∪ M := by
      intro c hc
      by_cases hm : c ∈ M
      · exact Finset.mem_union_right _ hm
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i,hi,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
        have hn : ¬ 2 ≤ (Finset.univ.filter (fun j => c ∈ S j)).card := by
          simpa only [M,Finset.mem_filter,Finset.mem_univ,true_and] using hm
        omega
    exact (hL i).trans ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _))
  constructor
  · intro i
    have hh := single_union_incidence_bound S L 2 8 hS hL hdis {i}
    have hb := hbase {i} (Finset.singleton_nonempty i)
    change 2*M.card ≤ _ at hh
    simp only [Finset.card_singleton,Finset.singleton_biUnion,Fintype.card_fin] at hh hb
    change 2*M.card ≤ 1 * ((X i).card + M.card - 8) + (5-1)*2 at hh
    omega
  · intro J hJ
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (by omega : 1 < J.card)
    have hpair : ({i,j} : Finset (Fin 5)).card = 2 := by simp [hij]
    have hh := single_union_incidence_bound S L 2 8 hS hL hdis {i,j}
    have hb := hbase {i,j} (by simp)
    change 2*M.card ≤ _ at hh
    rw [hpair] at hh
    change 2*M.card ≤ 2 * ((Finset.biUnion {i,j} X).card + M.card - 8) + (5-2)*2 at hh
    have hl : 5 ≤ (Finset.biUnion {i,j} X).card := by omega
    apply hl.trans (Finset.card_le_card _)
    intro c hc
    obtain ⟨k,hk,hc⟩ := Finset.mem_biUnion.mp hc
    have hkJ : k ∈ J := by
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hi
      · exact hj
    exact Finset.mem_biUnion.mpr ⟨k,hkJ,hc⟩

/-- Any at most three already chosen single representatives extend to all
five. This is the robust Hall step used in the exceptional five-cut case. -/
theorem robust_five_representatives {C : Type*} [DecidableEq C]
    (X : Fin 5 → Finset C) (hX : ∀ i, 4 ≤ (X i).card)
    (hpair : ∀ J : Finset (Fin 5), 2 ≤ J.card → 5 ≤ (J.biUnion X).card)
    (D : Finset (Fin 5)) (hD : D.card ≤ 3) (f : Fin 5 → C)
    (hf : Set.InjOn f D) (hfX : ∀ i ∈ D, f i ∈ X i) :
    ∃ g : Fin 5 → C, Function.Injective g ∧ (∀ i, g i ∈ X i) ∧ ∀ i ∈ D, g i = f i := by
  apply representatives_extend X D f hf hfX
  intro J
  let K := J.image Subtype.val
  have hK : K.card = J.card := Finset.card_image_of_injective _ Subtype.val_injective
  have he : J.biUnion (fun i => X i.val \ D.image f) = K.biUnion X \ D.image f := by
    ext c
    simp only [Finset.mem_biUnion,Finset.mem_sdiff,K,Finset.mem_image]
    constructor
    · rintro ⟨i,hi,hc,hn⟩; exact ⟨⟨i.val,⟨i,hi,rfl⟩,hc⟩,hn⟩
    · rintro ⟨⟨i,⟨j,hj,rfl⟩,hc⟩,hn⟩; exact ⟨j,hj,hc,hn⟩
  rw [he]
  rcases J.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
  · simp
  have hsingle : 4 ≤ (K.biUnion X).card := (hX i.val).trans
    (Finset.card_le_card (Finset.subset_biUnion_of_mem X
      (Finset.mem_image.mpr ⟨i,hi,rfl⟩)))
  have hdiff := Finset.le_card_sdiff (D.image f) (K.biUnion X)
  have himage := Finset.card_image_le (s := D) (f := f)
  have hJ := Finset.card_le_univ J
  rw [Fintype.card_subtype_compl,Fintype.card_coe,Fintype.card_fin] at hJ
  by_cases htwo : 2 ≤ K.card
  · have := hpair K htwo; omega
  · omega

/-- Enough single-occurrence colours remain even after forbidding all
colours on t specified stars. This is the exceptional-row source count. -/
theorem single_allowed_candidates {C : Type*} [Fintype C] [DecidableEq C]
    (S : Fin 5 → Finset C) (hS : ∀ i, (S i).card ≤ 2)
    (i : Fin 5) (L : Finset C) (hL : 8 ≤ L.card) (hdis : Disjoint L (S i))
    (J : Finset (Fin 5)) :
    4 - J.card ≤ (L.filter (fun c =>
      (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1 ∧
        ∀ j ∈ J, c ∉ S j)).card := by
  let occ := fun c => (Finset.univ.filter (fun j => c ∈ S j)).card
  let M := L.filter (fun c => 2 ≤ occ c)
  let B := L.filter (fun c => occ c ≤ 1 ∧ ∃ j ∈ J, c ∈ S j)
  let A := L.filter (fun c => occ c ≤ 1 ∧ ∀ j ∈ J, c ∉ S j)
  have hMB : Disjoint M B := by
    apply Finset.disjoint_left.mpr
    intro c hm hb
    have := (Finset.mem_filter.mp hm).2
    have := (Finset.mem_filter.mp hb).2.1
    omega
  have hcov : L = (M ∪ B) ∪ A := by
    ext c
    simp only [M,B,A,Finset.mem_filter,Finset.mem_union]
    constructor
    · intro hc
      by_cases hm : 2 ≤ occ c
      · exact Or.inl (Or.inl ⟨hc,hm⟩)
      · by_cases hb : ∃ j ∈ J, c ∈ S j
        · exact Or.inl (Or.inr ⟨hc,by omega,hb⟩)
        · exact Or.inr ⟨hc,by omega,by simpa only [not_exists,not_and] using hb⟩
    · tauto
  have hcard : L.card ≤ M.card + B.card + A.card := by
    rw [hcov]
    exact (Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have hB : B.card ≤ J.card * 2 := by
    have hsub : B ⊆ J.biUnion S := by
      intro c hc
      exact Finset.mem_biUnion.mpr (Finset.mem_filter.mp hc).2.2
    exact (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (fun j _ => hS j)).trans_eq (by simp)))
  have hweight : 2 * M.card + B.card ≤ 8 := by
    calc
      _ = (∑ _c ∈ M, 2) + ∑ _c ∈ B, 1 := by simp [Nat.mul_comm]
      _ ≤ (∑ c ∈ M, occ c) + ∑ c ∈ B, occ c := by
        apply Nat.add_le_add
        · exact Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
        · apply Finset.sum_le_sum
          intro c hc
          obtain ⟨j,_,hj⟩ := (Finset.mem_filter.mp hc).2.2
          exact Finset.card_pos.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
      _ = ∑ c ∈ M ∪ B, occ c := (Finset.sum_union hMB).symm
      _ = ∑ j : Fin 5, ((M ∪ B) ∩ S j).card := star_incidence_count S (M ∪ B)
      _ ≤ ∑ j : Fin 5, if j = i then 0 else 2 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : j = i
        · subst j
          rw [if_pos rfl]
          apply Nat.le_zero.mpr
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro c hc
          have hcL : c ∈ L := by
            rcases Finset.mem_union.mp (Finset.mem_inter.mp hc).1 with h | h
            · exact (Finset.mem_filter.mp h).1
            · exact (Finset.mem_filter.mp h).1
          exact Finset.disjoint_left.mp hdis hcL (Finset.mem_inter.mp hc).2
        · rw [if_neg hj]
          exact (Finset.card_le_card Finset.inter_subset_right).trans (hS j)
      _ = 8 := by simp [Finset.sum_ite,Finset.filter_ne',Finset.card_erase_of_mem]
  change 4 - J.card ≤ A.card
  omega

end Se20Part
