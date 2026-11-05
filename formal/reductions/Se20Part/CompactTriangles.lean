import Se20Part.CompactGeometry

noncomputable section
open scoped Classical
namespace Se20Part
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace Partition
variable {W C : Type*} [Fintype W] [Fintype C] (H : SimpleGraph W)

theorem typed_triangle_own_degree {R : Finset W → Prop} {π : W → C}
    (hΔ : ∀ v, degreeIn H π v (π v) ≤ 2)
    {T : Finset W} (hT : T ∈ typedTriangles H R π) {x : W} (hx : x ∈ T) :
    degreeIn H π x (π x) = 2 := by
  obtain ⟨ht,hr,hcl⟩ := (Finset.mem_filter.mp hT).2
  have hh : T.erase x ⊆ (Finset.univ.filter (fun y => H.Adj x y ∧ π y = π x)) := by
    intro y hy
    obtain ⟨hne,hy⟩ := Finset.mem_erase.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hcl x hx y hy hne.symm).1,
      (hcl x hx y hy hne.symm).2.symm⟩
  have hc := Finset.card_le_card hh
  have he := Finset.card_erase_add_one hx
  have hb := hΔ x
  rw [degreeIn_eq_card] at hb ⊢
  omega

theorem typed_triangle_bad {R : Finset W → Prop} {π : W → C}
    {T : Finset W} (hT : T ∈ typedTriangles H R π) {x : W} (hx : x ∈ T) :
    ¬ ((monochrome H π).connectedComponentMk x).toSimpleGraph.Colorable 2 := by
  obtain ⟨ht,hr,hcl⟩ := (Finset.mem_filter.mp hT).2
  let K := (monochrome H π).connectedComponentMk x
  have hm (y : T) : y.val ∈ K.supp := by
    by_cases hy : y.val = x
    · subst x
      exact K.mem_supp_iff _ |>.mpr rfl
    · exact K.mem_supp_of_adj_mem_supp (K.mem_supp_iff x |>.mpr rfl)
        (hcl x hx y y.prop (Ne.symm hy))
  let f : T → K.supp := fun y => ⟨y,hm y⟩
  intro hc
  have hh := hc.card_le_of_pairwise_adj f (by
    intro a b hab
    exact hcl a a.prop b b.prop (fun he => hab (Subtype.ext he)))
  rw [Nat.card_eq_fintype_card,Fintype.card_coe] at hh
  omega

end Partition

variable {V C : Type*} [Fintype V] [Fintype C] (G : SimpleGraph V)
open Partition

/-- The injection underlying both compact-triangle exclusions. -/
theorem compact_zeroClasses_le_four (hΔ : MaxDegreeFour G) {π : G.edgeSet → C}
    (hπ : MinimumThree (L2 G) (Compact G) π)
    (hbound : ∀ σ : G.edgeSet → C, Minimum (L2 G) σ →
      ∀ v, degreeIn (L2 G) σ v (σ v) ≤ 2)
    (T : Finset G.edgeSet) (hT : T ∈ typedTriangles (L2 G) (Compact G) π)
    (e : G.edgeSet) (he : e ∈ T) (hpivot : T.erase e ⊆ hubs G e) :
    (zeroClasses (L2 G) π e).card ≤ 4 := by
  obtain ⟨ht,hcompact,hcl⟩ := (mem_typedTriangles _ _ _ _).mp hT
  have hown := typed_triangle_own_degree (L2 G) (hbound π hπ.1.1) hT he
  have hbad := typed_triangle_bad (L2 G) hT he
  let A := (hubs G e).filter (fun f => π f ≠ π e)
  have hA : A.card ≤ 4 := by
    have hsub : A ⊆ hubs G e \ T.erase e := by
      intro f hf
      obtain ⟨hh,hne⟩ := Finset.mem_filter.mp hf
      refine Finset.mem_sdiff.mpr ⟨hh,?_⟩
      intro hfT
      obtain ⟨hfe,hfT⟩ := Finset.mem_erase.mp hfT
      exact hne (hcl f hfT e he hfe).2
    have hh := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hpivot] at hh
    have hc := hubs_card_le_six G hΔ e
    have hec := Finset.card_erase_add_one he
    omega
  have hex (j : zeroClasses (L2 G) π e) : ∃ f ∈ A, π f = j.val := by
    obtain ⟨hj,hzero⟩ := (Finset.mem_filter.mp j.prop).2
    have hm := minimumTwo_update_of_bad (L2 G) hπ.1 (hbound π hπ.1.1) e j
      (hzero.trans hown.symm) hbad
    obtain ⟨S,hS,heS⟩ := typed_triangle_replacement (L2 G) hπ e j hj hm T hT he
    obtain ⟨hs,hco,hclS⟩ := (mem_typedTriangles _ _ _ _).mp hS
    obtain ⟨f,hf,hfh⟩ := compact_has_hub G S hs hco e heS
    have hfe := (Finset.mem_filter.mp hfh).2.1
    have hc := (hclS f hf e heS hfe).2
    simp [Function.update,hfe] at hc
    exact ⟨f,Finset.mem_filter.mpr ⟨hfh,fun h => hj (hc.symm.trans h)⟩,hc⟩
  let f : zeroClasses (L2 G) π e → A := fun j => ⟨(hex j).choose,(hex j).choose_spec.1⟩
  have hinj : Function.Injective f := by
    intro j k heq
    apply Subtype.ext
    exact (hex j).choose_spec.2.symm.trans
      ((congrArg (fun t : A => π t.val) heq).trans (hex k).choose_spec.2)
  have hc := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_coe] using hc.trans (by simpa only [Fintype.card_coe] using hA)

/-- Lemma 4.6. In fact maximum degree four suffices. -/
theorem no_compact_triangles_ten (hΔ : MaxDegreeFour G) {π : G.edgeSet → Fin 10}
    (hπ : MinimumThree (L2 G) (Compact G) π) :
    typedTriangles (L2 G) (Compact G) π = ∅ := by
  have hd (e : G.edgeSet) : (L2 G).degree e ≤ 24 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have heq : (L2 G).neighborFinset e = conflicts G e := by ext f; simp
    rw [heq]
    exact card_conflicts_le_twentyFour G hΔ e
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro T hT
  obtain ⟨ht,hco,_⟩ := (mem_typedTriangles _ _ _ _).mp hT
  obtain ⟨e,he,hp⟩ := compact_has_pivot G T ht hco
  have hbound := fun (σ : G.edgeSet → Fin 10) (hs : Minimum (L2 G) σ) =>
    minimum_ten_degree_le_two (L2 G) hs hd
  have h4 := compact_zeroClasses_le_four G hΔ hπ hbound T hT e he hp
  have h5 := zeroClasses_ten (L2 G) hπ.1.1 e
    (typed_triangle_own_degree (L2 G) (hbound π hπ.1.1) hT he) (hd e)
  omega

/-- Lemma 4.6': every compact-triangle pivot has deficit at most two. -/
theorem compact_pivot_deficit_nine (hΔ : MaxDegreeFour G) {π : G.edgeSet → Fin 9}
    (hπ : MinimumThree (L2 G) (Compact G) π)
    (T : Finset G.edgeSet) (hT : T ∈ typedTriangles (L2 G) (Compact G) π)
    (e : G.edgeSet) (he : e ∈ T) (hp : T.erase e ⊆ hubs G e) :
    24 - (L2 G).degree e ≤ 2 := by
  have hd (e : G.edgeSet) : (L2 G).degree e ≤ 24 := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    have heq : (L2 G).neighborFinset e = conflicts G e := by ext f; simp
    rw [heq]
    exact card_conflicts_le_twentyFour G hΔ e
  have hbound := fun (σ : G.edgeSet → Fin 9) (hs : Minimum (L2 G) σ) =>
    minimum_nine_degree_le_two (L2 G) hs hd
  have h4 := compact_zeroClasses_le_four G hΔ hπ hbound T hT e he hp
  have hl := zeroClasses_nine_deficit (L2 G) hπ.1.1 e
    (typed_triangle_own_degree (L2 G) (hbound π hπ.1.1) hT he) (hd e)
  omega

end Se20Part
