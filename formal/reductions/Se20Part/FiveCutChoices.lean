import Se20Part.CutPaletteChoices

noncomputable section
open scoped Classical
namespace Se20Part

/-- In the failed five-single-representative case there are exactly seven
repeated colours, and at most one colour occurs three or more times. -/
theorem five_stars_failure_counts {C : Type*} [Fintype C] [DecidableEq C]
    (S L : Fin 5 → Finset C) (hS : ∀ i, (S i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hdis : ∀ i, Disjoint (L i) (S i))
    (hU : (Finset.univ.biUnion (fun i => (L i).filter
      (fun c => (Finset.univ.filter (fun j => c ∈ S j)).card ≤ 1))).card ≤ 4) :
    (Finset.univ.filter (fun c : C =>
      2 ≤ (Finset.univ.filter (fun i => c ∈ S i)).card)).card = 7 ∧
    (Finset.univ.filter (fun c : C =>
      3 ≤ (Finset.univ.filter (fun i => c ∈ S i)).card)).card ≤ 1 := by
  let occ := fun c => (Finset.univ.filter (fun i => c ∈ S i)).card
  let M : Finset C := Finset.univ.filter (fun c => 2 ≤ occ c)
  let B : Finset C := Finset.univ.filter (fun c => 3 ≤ occ c)
  let U := Finset.univ.biUnion (fun i => (L i).filter (fun c => occ c ≤ 1))
  have hm : M.card ≤ 7 := by
    have h := repeated_colours_bound S M 3 hS (fun c hc => (Finset.mem_filter.mp hc).2)
    norm_num at h
    omega
  have hb : ∀ i, 8 + (M ∩ S i).card ≤ U.card + M.card := by
    intro i
    have hcover : L i ⊆ U ∪ (M \ S i) := by
      intro c hc
      by_cases hm : c ∈ M
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hm,fun hs => Finset.disjoint_left.mp (hdis i) hc hs⟩)
      · apply Finset.mem_union_left
        apply Finset.mem_biUnion.mpr
        refine ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hc,?_⟩⟩
        have hnot : ¬ 2 ≤ occ c := by simpa only [M,Finset.mem_filter,
          Finset.mem_univ,true_and] using hm
        omega
    have hle := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have he := Finset.card_sdiff_add_card_inter M (S i)
    have := hL i
    omega
  have hinc : 2 * M.card ≤ 5 * (U.card + M.card - 8) := by
    calc
      2 * M.card = ∑ _c ∈ M, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ c ∈ M, occ c := Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2)
      _ = ∑ i : Fin 5, (M ∩ S i).card := star_incidence_count S M
      _ ≤ ∑ _i : Fin 5, (U.card + M.card - 8) := Finset.sum_le_sum
        (fun i _ => by have := hb i; omega)
      _ = _ := by simp
  have hbase := hb 0
  have hU' : U.card ≤ 4 := hU
  have hM7 : M.card = 7 := by omega
  have hBM : B ⊆ M := by
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_trans (by decide)
      (Finset.mem_filter.mp hc).2⟩
  have hweight : 3 * B.card + 2 * (M \ B).card ≤ 15 := by
    calc
      _ = (∑ _c ∈ B, 3) + ∑ _c ∈ M \ B, 2 := by simp [Nat.mul_comm]
      _ ≤ (∑ c ∈ B, occ c) + ∑ c ∈ M \ B, occ c := by
        exact Nat.add_le_add
          (Finset.sum_le_sum (fun c hc => (Finset.mem_filter.mp hc).2))
          (Finset.sum_le_sum (fun c hc =>
            (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).2))
      _ = ∑ c ∈ M, occ c := by rw [Nat.add_comm]; exact Finset.sum_sdiff hBM
      _ = ∑ i : Fin 5, (M ∩ S i).card := star_incidence_count S M
      _ ≤ ∑ _i : Fin 5, 3 := Finset.sum_le_sum (fun i _ =>
        (Finset.card_le_card Finset.inter_subset_right).trans (hS i))
      _ = 15 := by norm_num
  have hdiff := Finset.card_sdiff_add_card_eq_card hBM
  change M.card = 7 ∧ B.card ≤ 1
  omega

/-- All five source colours can be distinct, with at most one occurring
twice and each other source occurring at most once among the five stars. -/
theorem five_stars_source_choices {C : Type*} [Fintype C] [DecidableEq C]
    (S L : Fin 5 → Finset C) (hS : ∀ i, (S i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hdis : ∀ i, Disjoint (L i) (S i)) :
    ∃ x : Fin 5 → C, Function.Injective x ∧ (∀ i, x i ∈ L i) ∧
      ∃ e : Fin 5, (Finset.univ.filter (fun j => x e ∈ S j)).card ≤ 2 ∧
        ∀ i, i ≠ e → (Finset.univ.filter (fun j => x i ∈ S j)).card ≤ 1 := by
  let occ := fun c => (Finset.univ.filter (fun j => c ∈ S j)).card
  let X := fun i => (L i).filter (fun c => occ c ≤ 1)
  by_cases hh : ∀ J : Finset (Fin 5), J.card ≤ (J.biUnion X).card
  · obtain ⟨x,hx,hmem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' X).mp hh
    refine ⟨x,hx,fun i => (Finset.mem_filter.mp (hmem i)).1,0,?_,?_⟩
    · exact le_trans (Finset.mem_filter.mp (hmem 0)).2 (by decide)
    · intro i _; exact (Finset.mem_filter.mp (hmem i)).2
  push_neg at hh
  obtain ⟨J,hJ⟩ := hh
  have hJ5 : J = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hle := Finset.card_le_univ J
    have h4 := five_stars_single_hall S L hS hL hdis J
    norm_num at hle ⊢
    by_contra hn
    have := h4 (by omega)
    exact Nat.not_le_of_lt hJ this
  have hU : (Finset.univ.biUnion X).card ≤ 4 := by
    rw [hJ5] at hJ
    norm_num at hJ
    omega
  obtain ⟨_,hB⟩ := five_stars_failure_counts S L hS hL hdis hU
  let B : Finset C := Finset.univ.filter (fun c => 3 ≤ occ c)
  obtain ⟨c,hc,hc2⟩ : ∃ c ∈ L 0, occ c = 2 := by
    by_contra! hn
    have hcover : L 0 ⊆ (Finset.univ.biUnion X) ∪ B := by
      intro c hc
      by_cases hs : occ c ≤ 1
      · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨0,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hc,hs⟩⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,by have := hn c hc; omega⟩)
    have hcount := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hB' : B.card ≤ 1 := hB
    have := hL 0
    omega
  let Y : Fin 5 → Finset C := fun i => if i = 0 then {c} else X i
  have hyHall : ∀ J : Finset {i : Fin 5 // i ∉ ({0} : Finset (Fin 5))},
      J.card ≤ (J.biUnion (fun i => Y i.val \ ({0} : Finset (Fin 5)).image (fun _ => c))).card := by
    intro J
    let K := J.image Subtype.val
    have hK : K.card ≤ 4 := by
      have hJ := Finset.card_le_univ J
      norm_num [Fintype.card_subtype_compl] at hJ
      exact (Finset.card_image_le).trans hJ
    have hchoice := five_stars_single_hall S L hS hL hdis K hK
    have he : J.biUnion (fun i => Y i.val \ ({0} : Finset (Fin 5)).image (fun _ => c)) = K.biUnion X := by
      ext d
      simp only [Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_image, K]
      constructor
      · rintro ⟨i,hi,hd,_⟩
        refine ⟨i.val,⟨i,hi,rfl⟩,?_⟩
        simpa only [Y,if_neg (by simpa using i.prop)] using hd
      · rintro ⟨i,⟨j,hj,rfl⟩,hd⟩
        refine ⟨j,hj,?_,?_⟩
        · simpa only [Y,if_neg (by simpa using j.prop)] using hd
        · rintro ⟨_,_,he⟩
          have ho := (Finset.mem_filter.mp hd).2
          rw [← he] at ho
          omega
    rw [he]
    simpa only [K,Finset.card_image_of_injective _ Subtype.val_injective] using hchoice
  obtain ⟨x,hx,hxY,_⟩ := representatives_extend Y {0} (fun _ => c)
    (by
      intro i hi j hj _
      exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm)
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; simp [Y]) hyHall
  have hx0 : x 0 = c := by simpa [Y] using hxY 0
  refine ⟨x,hx,?_,0,?_,?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i; rwa [hx0]
    · exact (Finset.mem_filter.mp (show x i ∈ X i by simpa only [Y,if_neg hi] using hxY i)).1
  · change occ (x 0) ≤ 2; rw [hx0,hc2]
  · intro i hi
    exact (Finset.mem_filter.mp (show x i ∈ X i by simpa only [Y,if_neg hi] using hxY i)).2

/-- Five compatible prescribed pairs, including the twice-occurring source.
The exceptional source is assigned a target first. -/
theorem matching_cut_five_prescribed {C : Type*} [Fintype C] [DecidableEq C]
    (S T L K : Fin 5 → Finset C)
    (hS : ∀ i, (S i).card ≤ 3) (hT : ∀ i, (T i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hK : ∀ i, 8 ≤ (K i).card)
    (hdis : ∀ i, Disjoint (L i) (S i)) :
    ∃ x y : Fin 5 → C, Function.Injective x ∧ Function.Injective y ∧
      ∀ i, x i ∈ L i ∧ y i ∈ K i ∧ ¬ starForbidden S T (x i) (y i) := by
  obtain ⟨x,hx,hxL,e,he,hother⟩ := five_stars_source_choices S L hS hL hdis
  let Y := fun i => K i \ Finset.univ.filter (starForbidden S T (x i))
  have hrow : ∀ i, (Finset.univ.filter (starForbidden S T (x i))).card ≤
      (Finset.univ.filter (fun j => x i ∈ S j)).card * 3 := by
    intro i
    convert starForbidden_row S T 3 hT (x i) using 2 <;> congr 2
  have heY : 0 < (Y e).card := by
    have := hrow e
    have := hK e
    have := Finset.le_card_sdiff (Finset.univ.filter (starForbidden S T (x e))) (K e)
    dsimp [Y]
    omega
  obtain ⟨c,hc⟩ := Finset.card_pos.mp heY
  obtain ⟨y,hy,hyY,_⟩ := representatives_extend_of_card Y {e} (fun _ => c)
    (by
      intro i hi j hj _
      exact (Finset.mem_singleton.mp hi).trans (Finset.mem_singleton.mp hj).symm)
    (by intro i hi; simpa only [Finset.mem_singleton.mp hi] using hc)
    (by
      intro i hi
      have hn : i ≠ e := by simpa using hi
      have := hother i hn
      have := hrow i
      have := hK i
      have := Finset.le_card_sdiff (Finset.univ.filter (starForbidden S T (x i))) (K i)
      dsimp [Y]
      norm_num
      omega)
  refine ⟨x,y,hx,hy,fun i => ⟨hxL i,(Finset.mem_sdiff.mp (hyY i)).1,?_⟩⟩
  intro h
  exact (Finset.mem_sdiff.mp (hyY i)).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

end Se20Part
