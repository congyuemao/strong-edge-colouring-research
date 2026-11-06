import Se20Part.ExceptionalFiveCut

noncomputable section
open scoped Classical
namespace Se20Part

theorem star_union_occurrence_bound {I C : Type*} [Fintype I] [DecidableEq C]
    (S : I → Finset C) (b : ℕ) (hS : ∀ i, (S i).card ≤ b)
    (c : C) (hc : c ∈ Finset.univ.biUnion S) :
    (Finset.univ.biUnion S).card + (Finset.univ.filter (fun i => c ∈ S i)).card ≤
      Fintype.card I * b + 1 := by
  let U := Finset.univ.biUnion S
  let occ := fun d => (Finset.univ.filter (fun i => d ∈ S i)).card
  have hsum : (U.erase c).card + occ c ≤ Fintype.card I * b := by
    calc
      _ = (∑ _d ∈ U.erase c, 1) + occ c := by simp
      _ ≤ (∑ d ∈ U.erase c, occ d) + occ c := by
        apply Nat.add_le_add_right
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (Finset.mem_of_mem_erase hd)
        exact Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
      _ = ∑ d ∈ U, occ d := Finset.sum_erase_add _ _ hc
      _ = ∑ i : I, (U ∩ S i).card := star_incidence_count S U
      _ ≤ ∑ _i : I, b := Finset.sum_le_sum (fun i _ =>
        (Finset.card_le_card Finset.inter_subset_right).trans (hS i))
      _ = _ := by simp
  have hcard := Finset.card_erase_add_one hc
  change (U.erase c).card + 1 = U.card at hcard
  change U.card + occ c ≤ _
  omega

/-- The exceptional five-cut choice: a universal source-star colour and
a target-star union of size 12+k allow k prescribed targets in that union.
No residual-matrix or colouring conclusion is assumed. -/
theorem five_cut_forced_targets {C : Type*} [Fintype C] [DecidableEq C]
    (hC : Fintype.card C = 20) (S T L K : Fin 5 → Finset C)
    (hS : ∀ i, (S i).card ≤ 3) (hT : ∀ i, (T i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hK : ∀ i, 8 ≤ (K i).card)
    (hdis : ∀ i, Disjoint (L i) (S i))
    (z : C) (hz : ∀ i, z ∈ S i) (k : ℕ) (hk : 1 ≤ k) (hk3 : k ≤ 3)
    (hU : (Finset.univ.biUnion T).card = 12+k) :
    ∃ x y : Fin 5 → C, Function.Injective x ∧ Function.Injective y ∧
      (∀ i, x i ∈ L i ∧ y i ∈ K i ∧ ¬ starForbidden S T (x i) (y i)) ∧
      k ≤ ((Finset.univ.image y) ∩ Finset.univ.biUnion T).card := by
  let R := fun i => (S i).erase z
  let occ := fun c => (Finset.univ.filter (fun j => c ∈ R j)).card
  let X := fun i => (L i).filter (fun c => occ c ≤ 1)
  let U := Finset.univ.biUnion T
  have hU' : U.card = 12+k := hU
  have hR : ∀ i, (R i).card ≤ 2 := by
    intro i
    have := Finset.card_erase_add_one (hz i)
    have := hS i
    dsimp [R]
    omega
  have hdisR : ∀ i, Disjoint (L i) (R i) :=
    fun i => (hdis i).mono_right (Finset.erase_subset _ _)
  have hnez : ∀ i c, c ∈ L i → c ≠ z := by
    intro i c hc he
    exact Finset.disjoint_left.mp (hdis i) hc (he ▸ hz i)
  have hocc : ∀ c, c ≠ z → (Finset.univ.filter (fun j => c ∈ S j)).card = occ c := by
    intro c hc
    congr 1
    ext j
    simp [R,hc]
  obtain ⟨hX,hpair⟩ := five_two_stars_robust R L hR hL hdisR
  have hKU : ∀ i, k ≤ (K i ∩ U).card := by
    intro i
    have he := Finset.card_union_add_card_inter (K i) U
    have hle := Finset.card_le_univ (K i ∪ U)
    have := hK i
    change U.card = 12+k at hU
    omega
  obtain ⟨D,hDsub,hD⟩ := Finset.exists_subset_card_eq (show k ≤ (Finset.univ : Finset (Fin 5)).card by simp; omega)
  obtain ⟨yD,hyD,hyDK⟩ := representatives_of_card
    (fun i : D => K i.val ∩ U) (by
      intro i
      simpa only [Fintype.card_coe,hD] using hKU i.val)
  let y0 : Fin 5 → C := fun i => if hi : i ∈ D then yD ⟨i,hi⟩ else z
  have hy0 : Set.InjOn y0 D := by
    intro i hi j hj he
    have hi' : i ∈ D := hi
    have hj' : j ∈ D := hj
    exact congrArg Subtype.val (hyD (by simpa [y0,hi',hj'] using he))
  have hy0KU : ∀ i ∈ D, y0 i ∈ K i ∩ U := by
    intro i hi
    simpa only [y0,dif_pos hi] using hyDK ⟨i,hi⟩
  let J := fun a => Finset.univ.filter (fun j => a ∈ T j)
  let A := fun i a => (L i).filter (fun c => occ c ≤ 1 ∧ ∀ j ∈ J a, c ∉ R j)
  have hA : ∀ i ∈ D, k ≤ (A i (y0 i)).card := by
    intro i hi
    have hcount := star_union_occurrence_bound T 3 hT (y0 i) (Finset.mem_inter.mp (hy0KU i hi)).2
    have hcan := single_allowed_candidates R hR i (L i) (hL i) (hdisR i) (J (y0 i))
    have hJ : (J (y0 i)).card ≤ 4-k := by
      change U.card + (J (y0 i)).card ≤ _ at hcount
      norm_num at hcount
      omega
    exact (show k ≤ 4 - (J (y0 i)).card by omega).trans hcan
  obtain ⟨xD,hxD,hxDA⟩ := representatives_of_card
    (fun i : D => A i.val (y0 i.val)) (by
      intro i
      simpa only [Fintype.card_coe,hD] using hA i.val i.prop)
  let x0 : Fin 5 → C := fun i => if hi : i ∈ D then xD ⟨i,hi⟩ else z
  have hx0A : ∀ i ∈ D, x0 i ∈ A i (y0 i) := by
    intro i hi
    simpa only [x0,dif_pos hi] using hxDA ⟨i,hi⟩
  have hx0 : Set.InjOn x0 D := by
    intro i hi j hj he
    have hi' : i ∈ D := hi
    have hj' : j ∈ D := hj
    exact congrArg Subtype.val (hxD (by simpa [x0,hi',hj'] using he))
  obtain ⟨x,hx,hxX,hxx0⟩ := robust_five_representatives X hX hpair D (by omega) x0 hx0 (by
    intro i hi
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (hx0A i hi)).1,
      (Finset.mem_filter.mp (hx0A i hi)).2.1⟩)
  have hxL : ∀ i, x i ∈ L i := fun i => (Finset.mem_filter.mp (hxX i)).1
  have hxsingle : ∀ i, (Finset.univ.filter (fun j => x i ∈ S j)).card ≤ 1 := by
    intro i
    rw [hocc _ (hnez i _ (hxL i))]
    exact (Finset.mem_filter.mp (hxX i)).2
  have hallow : ∀ i ∈ D, ¬ starForbidden S T (x i) (y0 i) := by
    intro i hi ⟨j,hjS,hjT⟩
    have ha := (Finset.mem_filter.mp (hx0A i hi)).2.2 j
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hjT⟩)
    apply ha
    rw [← hxx0 i hi]
    exact Finset.mem_erase.mpr ⟨hnez i _ (hxL i),hjS⟩
  let Y := fun i => K i \ Finset.univ.filter (starForbidden S T (x i))
  have hY : ∀ i, 5 ≤ (Y i).card := by
    intro i
    have hr := starForbidden_row S T 3 hT (x i)
    have hh := hxsingle i
    have hc : (Finset.univ.filter (starForbidden S T (x i))).card ≤ 3 := by
      apply hr.trans
      convert Nat.mul_le_mul_right 3 hh using 2 <;> congr 2
    have hd := Finset.le_card_sdiff (Finset.univ.filter (starForbidden S T (x i))) (K i)
    have := hK i
    dsimp [Y]
    omega
  obtain ⟨y,hy,hyY,hyy0⟩ := representatives_extend_of_card Y D y0 hy0
    (by
      intro i hi
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (hy0KU i hi)).1,
        by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hallow i hi⟩)
    (by intro i _; simpa using hY i)
  refine ⟨x,y,hx,hy,?_,?_⟩
  · intro i
    exact ⟨hxL i,(Finset.mem_sdiff.mp (hyY i)).1,
      by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using
        (Finset.mem_sdiff.mp (hyY i)).2⟩
  · have hd : (D.image y).card = k := by rw [Finset.card_image_of_injective _ hy,hD]
    rw [← hd]
    apply Finset.card_le_card
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,
      by rw [hyy0 i hi]; exact (Finset.mem_inter.mp (hy0KU i hi)).2⟩

end Se20Part
