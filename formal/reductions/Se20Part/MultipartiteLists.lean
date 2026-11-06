import Se20Part.SmallColourPool

noncomputable section
open scoped Classical BigOperators
namespace Se20Part

def ThreePartGraph (I : Type*) : SimpleGraph (I × Fin 3) where
  Adj u v := u.1 ≠ v.1
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

def mergedLists {I C : Type*} [DecidableEq C] (L : I × Fin 3 → Finset C) :
    I × Bool → Finset C := fun v =>
  if v.2 then L (v.1,2) else L (v.1,0) ∩ L (v.1,1)

theorem merge_three_parts {I C : Type*} [Fintype I] [DecidableEq C]
    (L : I × Fin 3 → Finset C)
    (hh : ∀ T : Finset (I × Bool), T.card ≤ (T.biUnion (mergedLists L)).card) :
    HasListColouring (ThreePartGraph I) L := by
  obtain ⟨f,hf,hm⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' _).mp hh
  refine ⟨fun v => f (v.1,v.2 = 2),?_,?_⟩
  · rintro ⟨i,j⟩
    fin_cases j
    · exact (Finset.mem_inter.mp (hm (i,false))).1
    · exact (Finset.mem_inter.mp (hm (i,false))).2
    · exact hm (i,true)
  · intro u v huv he
    exact huv (congrArg (fun w : I × Bool => w.1) (hf he))

/-- A Hall criterion for merged and singleton lists. The separate Hall
condition on the merged lists is exactly the exceptional case in G14. -/
theorem paired_lists_hall {I C : Type*} [Fintype I] [DecidableEq C]
    (M S : I → Finset C) (m k : ℕ)
    (hM : ∀ i, m ≤ (M i).card) (hS : ∀ i, k ≤ (S i).card)
    (hdis : ∀ i, Disjoint (M i) (S i))
    (hk : Fintype.card I ≤ k) (hmk : 2 * Fintype.card I ≤ m+k)
    (hHM : ∀ A : Finset I, A.card ≤ (A.biUnion M).card) :
    ∀ T : Finset (I × Bool), T.card ≤
      (T.biUnion (fun v => if v.2 then S v.1 else M v.1)).card := by
  intro T
  let L : I × Bool → Finset C := fun v => if v.2 then S v.1 else M v.1
  change T.card ≤ (T.biUnion L).card
  by_cases hs : ∃ i, (i,true) ∈ T
  · obtain ⟨i,hi⟩ := hs
    have hlow : k ≤ (T.biUnion L).card := (hS i).trans (Finset.card_le_card
      (show S i ⊆ T.biUnion L from fun c hc => Finset.mem_biUnion.mpr ⟨(i,true),hi,hc⟩))
    by_cases hTk : T.card ≤ k
    · exact hTk.trans hlow
    have hp : ∃ j, (j,false) ∈ T ∧ (j,true) ∈ T := by
      by_contra! hn
      have hinj : Set.InjOn Prod.fst (↑T : Set (I × Bool)) := by
        intro a ha b hb hab
        rcases a with ⟨a,ba⟩; rcases b with ⟨b,bb⟩
        dsimp at hab; subst b
        cases ba <;> cases bb <;> simp_all
      have heq := Finset.card_image_iff.mpr hinj
      have hle := Finset.card_le_univ (T.image Prod.fst)
      omega
    obtain ⟨j,hj0,hj1⟩ := hp
    have hsub : M j ∪ S j ⊆ T.biUnion L := by
      intro c hc
      rcases Finset.mem_union.mp hc with hc | hc
      · exact Finset.mem_biUnion.mpr ⟨(j,false),hj0,hc⟩
      · exact Finset.mem_biUnion.mpr ⟨(j,true),hj1,hc⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint (hdis j)] at hc
    have ht := Finset.card_le_univ T
    simp only [Fintype.card_prod,Fintype.card_bool] at ht
    have hm := hM j; have hs := hS j
    omega
  · push_neg at hs
    have hinj : Set.InjOn Prod.fst (↑T : Set (I × Bool)) := by
      intro a ha b hb hab
      rcases a with ⟨a,ba⟩; rcases b with ⟨b,bb⟩
      dsimp at hab; subst b
      cases ba <;> cases bb <;> simp_all
    have heq := Finset.card_image_iff.mpr hinj
    have hsub : (T.image Prod.fst).biUnion M ⊆ T.biUnion L := by
      intro c hc
      obtain ⟨i,hi,hci⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨⟨j,b⟩,hj,hji⟩ := Finset.mem_image.mp hi
      dsimp at hji; subst i
      cases b
      · exact Finset.mem_biUnion.mpr ⟨(j,false),hj,hci⟩
      · exact (hs j hj).elim
    exact heq ▸ (hHM _).trans (Finset.card_le_card hsub)

theorem intersection_card_lower {C : Type*} [DecidableEq C]
    (A B U : Finset C) (hA : A ⊆ U) (hB : B ⊆ U) :
    A.card + B.card ≤ U.card + (A ∩ B).card := by
  have h := Finset.card_union_add_card_inter A B
  have hs := Finset.card_le_card (Finset.union_subset hA hB)
  omega

theorem three_parts_six_choosable {I C : Type*} [Fintype I] [DecidableEq C]
    (hI : Fintype.card I = 3) (L : I × Fin 3 → Finset C)
    (hL : ∀ v, 6 ≤ (L v).card) : HasListColouring (ThreePartGraph I) L := by
  apply small_colour_pool (ThreePartGraph I) 6 _ L hL
  intro L hL hpool
  have hp : (Finset.univ.biUnion L).card ≤ 8 := by
    simp only [Fintype.card_prod,Fintype.card_fin,hI] at hpool; omega
  have hm : ∀ i, 4 ≤ (L (i,0) ∩ L (i,1)).card := by
    intro i
    have ha := hL (i,0); have hb := hL (i,1)
    have hh := intersection_card_lower (L (i,0)) (L (i,1)) (Finset.univ.biUnion L)
      (fun c hc => Finset.mem_biUnion.mpr ⟨(i,0),Finset.mem_univ _,hc⟩)
      (fun c hc => Finset.mem_biUnion.mpr ⟨(i,1),Finset.mem_univ _,hc⟩)
    omega
  apply merge_three_parts L
  intro T
  by_cases hs : ∃ i, (i,true) ∈ T
  · obtain ⟨i,hi⟩ := hs
    have ht := Finset.card_le_univ T
    simp only [Fintype.card_prod,Fintype.card_bool,hI] at ht
    exact ht.trans ((hL (i,2)).trans (Finset.card_le_card
      (show L (i,2) ⊆ T.biUnion (mergedLists L) from
        fun c hc => Finset.mem_biUnion.mpr ⟨(i,true),hi,hc⟩)))
  · push_neg at hs
    by_cases he : T = ∅
    · simp [he]
    obtain ⟨⟨i,b⟩,hi⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hb : b = false := by cases b <;> simp_all
    subst b
    have hsub : T ⊆ (Finset.univ : Finset I) ×ˢ {false} := by
      rintro ⟨j,b⟩ hj
      cases b <;> simp_all
    have ht := Finset.card_le_card hsub
    simp only [Finset.card_product,Finset.card_univ,Finset.card_singleton,mul_one,hI] at ht
    exact (show T.card ≤ 4 by omega).trans ((hm i).trans (Finset.card_le_card
      (show L (i,0) ∩ L (i,1) ⊆ T.biUnion (mergedLists L) from
        fun c hc => Finset.mem_biUnion.mpr ⟨(i,false),hi,hc⟩)))

end Se20Part
