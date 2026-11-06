import Se20Part.PaletteCompletion

noncomputable section
open scoped Classical
namespace Se20Part

theorem starForbidden_row_union {I A B : Type*} [Fintype I] [Fintype B]
    [DecidableEq B] (S : I → Finset A) (T : I → Finset B) (x : A) :
    Finset.univ.filter (starForbidden S T x) ⊆ Finset.univ.biUnion T := by
  intro y hy
  obtain ⟨i,_,hi⟩ := (Finset.mem_filter.mp hy).2
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩

theorem starForbidden_symm {I A B : Type*} (S : I → Finset A) (T : I → Finset B)
    (x : A) (y : B) : starForbidden S T x y ↔ starForbidden T S y x := by
  simp only [starForbidden,and_comm]

theorem five_stars_row_twelve {C : Type*} [Fintype C] [DecidableEq C]
    (S T : Fin 5 → Finset C) (hT : ∀ i, (T i).card ≤ 3)
    (hcase : (∃ z, ∀ i, z ∈ S i) → (Finset.univ.biUnion T).card ≤ 12) :
    ∀ c, (Finset.univ.filter (starForbidden S T c)).card ≤ 12 := by
  intro c
  by_cases hfull : ∀ i, c ∈ S i
  · exact (Finset.card_le_card (starForbidden_row_union S T c)).trans (hcase ⟨c,hfull⟩)
  · have hocc : (Finset.univ.filter (fun i => c ∈ S i)).card ≤ 4 := by
      have hle := Finset.card_le_univ (Finset.univ.filter (fun i => c ∈ S i))
      norm_num at hle
      by_contra hn
      have he : Finset.univ.filter (fun i => c ∈ S i) = Finset.univ :=
        Finset.eq_univ_of_card _ (by simp only [Fintype.card_fin]; omega)
      apply hfull
      intro i
      have hi : i ∈ Finset.univ.filter (fun i => c ∈ S i) := by rw [he]; exact Finset.mem_univ _
      exact (Finset.mem_filter.mp hi).2
    apply (starForbidden_row S T 3 hT c).trans
    convert Nat.mul_le_mul_right 3 hocc using 2 <;> congr 2

theorem universal_five_star_union {C : Type*} [DecidableEq C]
    (S : Fin 5 → Finset C) (hS : ∀ i, (S i).card ≤ 3)
    (z : C) (hz : ∀ i, z ∈ S i) : (Finset.univ.biUnion S).card ≤ 11 := by
  have h := star_union_occurrence_bound S 3 hS z
    (Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,hz 0⟩)
  have he : Finset.univ.filter (fun i => z ∈ S i) = Finset.univ := by
    ext i; simp [hz]
  rw [he] at h
  norm_num at h
  omega

/-- Complete palette construction for a five-edge matching cut. The
universal-colour exception is handled on whichever side requires it. -/
theorem matching_cut_five_palette {C : Type*} [Fintype C] [DecidableEq C]
    (hC : Fintype.card C = 20) (S T L K : Fin 5 → Finset C)
    (hS : ∀ i, (S i).card ≤ 3) (hT : ∀ i, (T i).card ≤ 3)
    (hL : ∀ i, 8 ≤ (L i).card) (hK : ∀ i, 8 ≤ (K i).card)
    (hdisS : ∀ i, Disjoint (L i) (S i)) (hdisT : ∀ i, Disjoint (K i) (T i)) :
    ∃ (p : C ≃ C) (x y : Fin 5 → C),
      Function.Injective x ∧ Function.Injective y ∧
      (∀ i, x i ∈ L i ∧ y i ∈ K i ∧ p (x i) = y i) ∧
      ∀ c, ¬ starForbidden S T c (p c) := by
  have exception : ∀ (S T L K : Fin 5 → Finset C),
      (∀ i, (S i).card ≤ 3) → (∀ i, (T i).card ≤ 3) →
      (∀ i, 8 ≤ (L i).card) → (∀ i, 8 ≤ (K i).card) →
      (∀ i, Disjoint (L i) (S i)) →
      (∃ z, ∀ i, z ∈ S i) → 12 < (Finset.univ.biUnion T).card →
      ∃ (p : C ≃ C) (x y : Fin 5 → C),
        Function.Injective x ∧ Function.Injective y ∧
        (∀ i, x i ∈ L i ∧ y i ∈ K i ∧ p (x i) = y i) ∧
        ∀ c, ¬ starForbidden S T c (p c) := by
    intro S T L K hS hT hL hK hdis ⟨z,hz⟩ hlarge
    let U := Finset.univ.biUnion T
    have hUc : U.card ≤ 15 := Finset.card_biUnion_le.trans
      ((Finset.sum_le_sum (fun i _ => hT i)).trans_eq (by norm_num))
    let k := U.card - 12
    have hk : 1 ≤ k := by dsimp [k,U]; omega
    have hk3 : k ≤ 3 := by dsimp [k]; omega
    have hU : U.card = 12+k := by dsimp [k,U] at *; omega
    obtain ⟨x,y,hx,hy,hmem,hcover⟩ := five_cut_forced_targets hC S T L K
      hS hT hL hK hdis z hz k hk hk3 hU
    have hsource := universal_five_star_union S hS z hz
    have htarget : (U \ Finset.univ.image y).card ≤ 12 := by
      have hc := Finset.card_sdiff_add_card_inter U (Finset.univ.image y)
      rw [Finset.inter_comm] at hc
      change k ≤ ((Finset.univ.image y) ∩ U).card at hcover
      omega
    obtain ⟨p,hp,hgood⟩ := palette_complete_five hC (starForbidden S T) x y hx hy
      (fun i => (hmem i).2.2)
      (by
        intro c
        apply le_trans (Finset.card_le_card _) htarget
        intro d hd
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd
        obtain ⟨hn,hr⟩ := hd
        refine Finset.mem_sdiff.mpr ⟨?_,?_⟩
        · exact starForbidden_row_union S T c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
        · simpa only [Finset.mem_image,Finset.mem_univ,true_and,Set.mem_range] using hn)
      (by
        intro d
        apply le_trans (Finset.card_le_card _) (hsource.trans (by decide : 11 ≤ 12))
        intro c hc
        simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hc
        obtain ⟨_,hr⟩ := hc
        exact starForbidden_row_union T S d (Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,(starForbidden_symm S T c d).mp hr⟩))
      (by simpa using starForbidden_total S T 3 3 hS hT)
    exact ⟨p,x,y,hx,hy,fun i => ⟨(hmem i).1,(hmem i).2.1,hp i⟩,hgood⟩
  by_cases hs : (∃ z, ∀ i, z ∈ S i) ∧ 12 < (Finset.univ.biUnion T).card
  · exact exception S T L K hS hT hL hK hdisS hs.1 hs.2
  by_cases ht : (∃ z, ∀ i, z ∈ T i) ∧ 12 < (Finset.univ.biUnion S).card
  · obtain ⟨p,y,x,hy,hx,hmem,hgood⟩ := exception T S K L hT hS hK hL hdisT ht.1 ht.2
    refine ⟨p.symm,x,y,hx,hy,?_,?_⟩
    · intro i
      exact ⟨(hmem i).2.1,(hmem i).1,(p.symm_apply_eq).mpr (hmem i).2.2.symm⟩
    · intro c hc
      apply hgood (p.symm c)
      simpa only [Equiv.apply_symm_apply] using (starForbidden_symm S T _ _).mp hc
  obtain ⟨x,y,hx,hy,hmem⟩ := matching_cut_five_prescribed S T L K hS hT hL hK hdisS
  have hr := five_stars_row_twelve S T hT (by intro h; by_contra hn; exact hs ⟨h,by omega⟩)
  have hc := five_stars_row_twelve T S hS (by intro h; by_contra hn; exact ht ⟨h,by omega⟩)
  obtain ⟨p,hp,hgood⟩ := palette_complete_five hC (starForbidden S T) x y hx hy
    (fun i => (hmem i).2.2)
    (by
      intro c
      apply le_trans _ (hr c)
      apply Finset.card_le_card
      intro d hd
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd.2⟩)
    (by
      intro d
      apply le_trans _ (hc d)
      apply Finset.card_le_card
      intro c hc
      simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hc
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(starForbidden_symm S T c d).mp hc.2⟩)
    (by simpa using starForbidden_total S T 3 3 hS hT)
  exact ⟨p,x,y,hx,hy,fun i => ⟨(hmem i).1,(hmem i).2.1,hp i⟩,hgood⟩

end Se20Part
