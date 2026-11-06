import Se20Part.HighCliqueCritical

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part

/-- End blocks inside a specified induced vertex set, expressed in the
ambient vertex type. -/
theorem induced_set_end_block {W : Type} [Fintype W] (H : SimpleGraph W)
    (T : Finset W) (ht : T.Nonempty) :
    ∃ S B : Finset W, S.Nonempty ∧ S ⊆ B ∧ B ⊆ T ∧ (B \ S).card ≤ 1 ∧
      (∀ x ∈ S, ∀ y ∈ T, H.Adj x y → y ∈ B) ∧ BlockEligible H B := by
  classical
  letI : Nonempty T := let ⟨x,hx⟩ := ht; ⟨⟨x,hx⟩⟩
  obtain ⟨S,B,hs,hsb,hbs,hcl,he⟩ := exists_end_block (H.induce (T : Set W))
  let S' := S.image Subtype.val
  let B' := B.image Subtype.val
  have hbT : B' ⊆ T := by
    intro x hx
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hx
    exact x.prop
  have liftB (x : B') : (⟨x.val,hbT x.prop⟩ : T) ∈ B := by
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp x.prop
    have hh : (⟨x.val,hbT x.prop⟩ : T) = y := Subtype.ext hyx.symm
    exact hh ▸ hy
  let e : (H.induce (T : Set W)).induce (B : Set T) ≃g H.induce (B' : Set W) :=
    { toEquiv :=
        { toFun := fun x => ⟨x.val.val,Finset.mem_image.mpr ⟨x.val,x.prop,rfl⟩⟩
          invFun := fun x => ⟨⟨x.val,hbT x.prop⟩,liftB x⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      map_rel_iff' := Iff.rfl }
  refine ⟨S',B',hs.image _,Finset.image_subset_image hsb,hbT,?_,?_,?_,?_⟩
  · have hh : B' \ S' = (B \ S).image Subtype.val := by
      ext x
      simp only [B',S',Finset.mem_sdiff,Finset.mem_image]
      constructor
      · rintro ⟨⟨u,hu,rfl⟩,hsu⟩
        exact ⟨u,⟨hu,fun h => hsu ⟨u,h,rfl⟩⟩,rfl⟩
      · rintro ⟨u,⟨hu,hsu⟩,rfl⟩
        refine ⟨⟨u,hu,rfl⟩,?_⟩
        rintro ⟨v,hv,heq⟩
        exact hsu ((Subtype.ext heq : v = u) ▸ hv)
    rw [hh,Finset.card_image_of_injective _ Subtype.val_injective]
    convert hbs using 1
    congr 1
    ext x
    simp only [Finset.mem_sdiff]
  · intro x hx y hy hxy
    obtain ⟨u,hu,hux⟩ := Finset.mem_image.mp (show x ∈ S.image Subtype.val from hx)
    exact Finset.mem_image.mpr ⟨⟨y,hy⟩,hcl u hu ⟨y,hy⟩ (by
      change H.Adj u.val y
      rwa [hux]),rfl⟩
  · exact e.connected_iff.mp he.1
  · intro v
    let f : ((H.induce (T : Set W)).induce (B : Set T)).induce {x | x ≠ e.symm v} →g
        (H.induce (B' : Set W)).induce {x | x ≠ v} :=
      { toFun := fun x => ⟨e x.val,fun hh => x.prop (e.injective (hh.trans (e.apply_symm_apply v).symm))⟩
        map_rel' := fun h => e.toHom.map_adj h }
    apply (he.2 (e.symm v)).map f
    intro x
    refine ⟨⟨e.symm x.val,fun hh => x.prop ?_⟩,?_⟩
    · exact e.symm.injective hh
    · exact Subtype.ext (e.apply_symm_apply _)

def residualPalette {W : Type} [Fintype W] (H : SimpleGraph W) (k : ℕ)
    (B : Finset W) (c : W → Fin k) (v : W) : Finset (Fin k) :=
  Finset.univ \ (H.neighborFinset v \ B).image c

/-- These are the prescribed residual lists of one actual outside colouring.
Their uncolourability follows by gluing, without reconstructing arbitrary lists. -/
theorem critical_prescribed_lists {W : Type} [Fintype W] (H : SimpleGraph W)
    (k : ℕ) (hk : 0 < k) (hmin : VertexMinimalNoncolourable H k)
    (B : Finset W) (hb : B.Nonempty) (hl : ∀ v ∈ B, H.degree v = k) :
    ∃ c : W → Fin k,
      (∀ u ∉ B, ∀ v ∉ B, H.Adj u v → c u ≠ c v) ∧
      (∀ v : B, (H.induce (B : Set W)).degree v ≤ (residualPalette H k B c v.val).card) ∧
      ¬ DegreeList.ColourableOn (H.induce (B : Set W))
        (fun v => residualPalette H k B c v.val) Finset.univ := by
  let O := Finset.univ \ B
  have ho : O.card < Fintype.card W := by
    have hh := Finset.card_sdiff_add_card_inter (Finset.univ : Finset W) B
    have hp := Finset.card_pos.mpr hb
    simp only [Finset.univ_inter,Finset.card_univ] at hh
    dsimp [O]
    omega
  obtain ⟨d⟩ := hmin.2 O ho
  let c : W → Fin k := fun v => if hv : v ∈ B then ⟨0,hk⟩ else
    d ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩
  have hc : ∀ u ∉ B, ∀ v ∉ B, H.Adj u v → c u ≠ c v := by
    intro u hu v hv huv
    simpa only [c,dite_eq_right hu,dite_eq_right hv] using
      d.valid (v := ⟨u,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hu⟩⟩)
        (w := ⟨v,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hv⟩⟩) huv
  refine ⟨c,hc,?_,?_⟩
  · intro v
    have hp := Finset.card_sdiff_add_card_inter (H.neighborFinset v.val) B
    have hi : H.neighborFinset v.val ∩ B = B.filter (H.Adj v.val) := by
      ext w
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,Finset.mem_filter]
      exact and_comm
    rw [hi,← degree_induce_finset,SimpleGraph.card_neighborFinset_eq_degree,hl v.val v.prop] at hp
    have hc' := Finset.card_image_le (s := H.neighborFinset v.val \ B) (f := c)
    simp only [residualPalette,Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_univ,Fintype.card_fin]
    omega
  · rintro ⟨f,hf,hp⟩
    have free (v : B) (w : W) (hw : w ∉ B) (hvw : H.Adj v.val w) : f v ≠ c w := by
      intro hh
      exact (Finset.mem_sdiff.mp (hf v (Finset.mem_univ _))).2
        (Finset.mem_image.mpr ⟨w,Finset.mem_sdiff.mpr
          ⟨(H.mem_neighborFinset _ _).mpr hvw,hw⟩,hh.symm⟩)
    apply hmin.1
    refine ⟨SimpleGraph.Coloring.mk (fun v => if hv : v ∈ B then f ⟨v,hv⟩ else c v) ?_⟩
    intro u v huv
    split_ifs with hu hv hv
    · exact hp ⟨u,hu⟩ (Finset.mem_univ _) ⟨v,hv⟩ (Finset.mem_univ _) huv
    · exact free ⟨u,hu⟩ v hv huv
    · exact (free ⟨v,hv⟩ u hu huv.symm).symm
    · exact hc u hu v hv huv

/-- Equal prescribed palettes recover equal external neighbourhoods when
the outside vertices belong to one properly coloured clique. -/
theorem external_neighbours_eq_of_palette_eq {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (B Q : Finset W) (c : W → Fin k)
    (hQ : H.IsClique (Q : Set W)) (hqB : Disjoint Q B)
    (hc : ∀ u ∉ B, ∀ v ∉ B, H.Adj u v → c u ≠ c v)
    (x y : W) (hx : H.neighborFinset x \ B ⊆ Q)
    (hy : H.neighborFinset y \ B ⊆ Q)
    (he : residualPalette H k B c x = residualPalette H k B c y) :
    H.neighborFinset x \ B = H.neighborFinset y \ B := by
  have inj : Set.InjOn c (Q : Set W) := by
    intro u hu v hv heq
    by_contra hne
    exact hc u (fun hh => Finset.disjoint_left.mp hqB hu hh)
      v (fun hh => Finset.disjoint_left.mp hqB hv hh) (hQ hu hv hne) heq
  have imageEq : (H.neighborFinset x \ B).image c = (H.neighborFinset y \ B).image c := by
    ext a
    have hh := Finset.ext_iff.mp he a
    simp only [residualPalette,Finset.mem_sdiff,Finset.mem_univ,true_and] at hh
    exact not_iff_not.mp hh
  apply Finset.Subset.antisymm
  · intro u hu
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp (imageEq ▸ Finset.mem_image_of_mem c hu)
    exact inj (hy hv) (hx hu) heq ▸ hv
  · intro u hu
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp (imageEq.symm ▸ Finset.mem_image_of_mem c hu)
    exact inj (hx hv) (hy hu) heq ▸ hv

/-- A clique of interior vertices with identical external neighbourhoods
joins to the high clique in the original graph. -/
theorem clique_union_external {W : Type} [Fintype W] (H : SimpleGraph W)
    (B Q D : Finset W) (x : W) (hdB : D ⊆ B)
    (hd : H.IsClique (D : Set W)) (hq : H.IsClique (Q : Set W))
    (hn : H.neighborFinset x \ B ⊆ Q)
    (he : ∀ y ∈ D, H.neighborFinset y \ B = H.neighborFinset x \ B) :
    H.IsClique (↑(D ∪ (H.neighborFinset x \ B)) : Set W) ∧
      (D ∪ (H.neighborFinset x \ B)).card = D.card + (H.neighborFinset x \ B).card := by
  refine ⟨?_,Finset.card_union_of_disjoint (Finset.disjoint_left.mpr ?_)⟩
  · intro u hu v hv huv
    rcases Finset.mem_union.mp hu with hu | hu <;>
      rcases Finset.mem_union.mp hv with hv | hv
    · exact hd hu hv huv
    · exact (H.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp ((he u hu).symm ▸ hv)).1
    · exact ((H.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp ((he v hv).symm ▸ hu)).1).symm
    · exact hq (hn hu) (hn hv) huv
  · intro y hy hn
    exact (Finset.mem_sdiff.mp hn).2 (hdB hy)

/-- On a nontrivial low block, criticality forces the actual residual
palettes of a fixed outside colouring to be uniform. -/
theorem critical_block_uniform_palettes {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hk : 0 < k)
    (hmin : VertexMinimalNoncolourable H k) (B : Finset W)
    (he : BlockEligible H B) (hb : 2 ≤ B.card) (hl : ∀ v ∈ B, H.degree v = k) :
    ∃ c : W → Fin k, (∀ u ∉ B, ∀ v ∉ B, H.Adj u v → c u ≠ c v) ∧
      ∀ x ∈ B, ∀ y ∈ B, residualPalette H k B c x = residualPalette H k B c y := by
  letI : Nonempty (Fin k) := ⟨⟨0,hk⟩⟩
  have hp : B.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c,hc,hd,hbad⟩ := critical_prescribed_lists H k hk hmin B hp hl
  have hnt : Nontrivial B := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [Fintype.card_coe]; omega)
  letI := hnt
  have hdel : ∀ v : B, ((H.induce (B : Set W)).induce {x | x ≠ v}).Connected := by
    intro v
    obtain ⟨w,hw⟩ := exists_ne v
    exact { preconnected := he.2 v, nonempty := ⟨⟨w,hw⟩⟩ }
  refine ⟨c,hc,?_⟩
  intro x hx y hy
  exact (DegreeList.bad_noncut_uniform (H.induce (B : Set W))
    (fun v => residualPalette H k B c v.val) he.1 hdel hd hbad ⟨y,hy⟩ ⟨x,hx⟩).1

/-- The critical obstruction required for A03. Both possible low end
blocks produce a genuine ambient clique of order at least k. -/
theorem critical_high_clique_contains_clique {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hk : 3 ≤ k)
    (hmin : VertexMinimalNoncolourable H k) (hΔ : ∀ v, H.degree v ≤ k+1)
    (hQ : H.IsClique (highVertices H k : Set W)) :
    ∃ D : Finset W, k ≤ D.card ∧ H.IsClique (D : Set W) := by
  classical
  by_contra! hn
  have hcl : ∀ D : Finset W, H.IsClique (D : Set W) → D.card < k := by
    intro D hd
    by_contra! hh
    exact hn D hh hd
  have hdeg := vertex_minimal_noncolourable_degree H k hmin
  have degrees : ∀ v, H.degree v = k ∨ H.degree v = k+1 := by
    intro v
    have := hdeg v
    have := hΔ v
    omega
  let Q := highVertices H k
  let T := Finset.univ.filter (fun v => H.degree v = k)
  have ht : T.Nonempty := by
    by_contra ht
    have hall : ∀ v, v ∈ Q := by
      intro v
      rcases degrees v with hv | hv
      · exact (ht ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩⟩).elim
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    have hcard := hcl Finset.univ (fun u _ v _ huv => hQ (hall u) (hall v) huv)
    have hne : Nonempty W := by
      by_contra he
      haveI : IsEmpty W := not_nonempty_iff.mp he
      exact hmin.1 ⟨SimpleGraph.Coloring.mk isEmptyElim (fun {x} => isEmptyElim x)⟩
    obtain ⟨v⟩ := hne
    have := H.degree_lt_card_verts v
    have := hdeg v
    rw [Finset.card_univ] at hcard
    omega
  obtain ⟨S,B,hs,hsB,hBT,hbs,hclosed,he⟩ := induced_set_end_block H T ht
  have low : ∀ v ∈ B, H.degree v = k := fun v hv => (Finset.mem_filter.mp (hBT hv)).2
  have hQB : Disjoint Q B := by
    apply Finset.disjoint_left.mpr
    intro v hv hb
    have hd := (Finset.mem_filter.mp hv).2
    have hl := low v hb
    omega
  have external : ∀ x ∈ S, H.neighborFinset x \ B ⊆ Q := by
    intro x hx y hy
    obtain ⟨hyN,hyB⟩ := Finset.mem_sdiff.mp hy
    have hxy := (H.mem_neighborFinset _ _).mp hyN
    rcases degrees y with hd | hd
    · exact (hyB (hclosed x hx y (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩) hxy)).elim
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd⟩
  have same : ∀ x ∈ S, ∀ y ∈ S, H.neighborFinset x \ B = H.neighborFinset y \ B := by
    by_cases hb : 2 ≤ B.card
    · obtain ⟨c,hc,hu⟩ := critical_block_uniform_palettes H k (by omega) hmin B he hb low
      intro x hx y hy
      exact external_neighbours_eq_of_palette_eq H k B Q c hQ hQB hc x y
        (external x hx) (external y hy) (hu x (hsB hx) y (hsB hy))
    · intro x hx y hy
      have hxy := Finset.card_le_one.mp (show B.card ≤ 1 by omega) x (hsB hx) y (hsB hy)
      rw [hxy]
  obtain ⟨x,hx⟩ := hs
  have hxB := hsB hx
  have budget : (H.neighborFinset x \ B).card + (H.induce (B : Set W)).degree ⟨x,hxB⟩ = k := by
    have hh := Finset.card_sdiff_add_card_inter (H.neighborFinset x) B
    have hi : H.neighborFinset x ∩ B = B.filter (H.Adj x) := by
      ext y
      simp only [Finset.mem_inter,SimpleGraph.mem_neighborFinset,Finset.mem_filter]
      exact and_comm
    rw [degree_induce_finset H B ⟨x,hxB⟩]
    rwa [hi,SimpleGraph.card_neighborFinset_eq_degree,low x hxB] at hh
  rcases minimal_low_block_classification H k hmin B he.1 he.2 low with complete | cycle
  · have hinner : (H.induce (B : Set W)).degree ⟨x,hxB⟩ + 1 = B.card := by
      rw [degree_induce_finset]
      have hh : B.filter (H.Adj x) = B.erase x := by
        ext y
        simp only [Finset.mem_filter,Finset.mem_erase]
        exact ⟨fun h => ⟨h.2.ne.symm,h.1⟩,
          fun h => ⟨h.2,complete x hxB y h.2 h.1.symm⟩⟩
      rw [hh]
      exact Finset.card_erase_add_one hxB
    obtain ⟨hc,hcard⟩ := clique_union_external H B Q S x hsB
      (fun u hu v hv huv => complete u (hsB hu) v (hsB hv) huv) hQ (external x hx)
      (fun y hy => same y hy x hx)
    have hd := hcl _ hc
    have hparts := Finset.card_sdiff_add_card_inter B S
    rw [Finset.inter_eq_right.mpr hsB] at hparts
    omega
  · have htwo : (H.induce (B : Set W)).degree ⟨x,hxB⟩ = 2 := by
      simpa only [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card]
        using cycle.2.2 ⟨x,hxB⟩
    have hfilter : (B.filter (H.Adj x)).card = 2 := by
      rwa [degree_induce_finset H B ⟨x,hxB⟩] at htwo
    obtain ⟨y,hy,hyout⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show (B \ S).card < (B.filter (H.Adj x)).card by omega)
    obtain ⟨hyB,hxy⟩ := Finset.mem_filter.mp hy
    have hyS : y ∈ S := by
      by_contra hh
      exact hyout (Finset.mem_sdiff.mpr ⟨hyB,hh⟩)
    have pairSub : ({x,y} : Finset W) ⊆ S := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact (Finset.mem_singleton.mp hz).symm ▸ hyS
    have pairClique : H.IsClique (↑({x,y} : Finset W) : Set W) := by
      simpa only [Finset.coe_pair] using (SimpleGraph.isClique_pair.mpr (fun _ => hxy))
    obtain ⟨hc,hcard⟩ := clique_union_external H B Q {x,y} x (pairSub.trans hsB)
      pairClique hQ (external x hx) (fun y hy => same y (pairSub hy) x hx)
    have hd := hcl _ hc
    rw [Finset.card_pair hxy.ne] at hcard
    omega

/-- A03: for k≥3, a finite K_k-free graph of maximum degree k+1 is
k-colourable when its degree-(k+1) vertices form a clique. -/
theorem high_clique_low_clique_free_colourable {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hk : 3 ≤ k) (hΔ : ∀ v, H.degree v ≤ k+1)
    (hfree : H.CliqueFree k) (hQ : H.IsClique (highVertices H k : Set W)) :
    H.Colorable k := by
  classical
  by_contra hn
  obtain ⟨A,hA⟩ := exists_vertex_minimal_noncolourable H k hn
  have hdeg : ∀ x : A, (H.induce (A : Set W)).degree x ≤ k+1 := by
    intro x
    rw [degree_induce_finset]
    apply le_trans _ (hΔ x.val)
    rw [← SimpleGraph.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro y hy
    exact (H.mem_neighborFinset _ _).mpr (Finset.mem_filter.mp hy).2
  obtain ⟨D,hD,hc⟩ := critical_high_clique_contains_clique _ k hk hA hdeg
    (induced_high_clique H k hΔ hQ A)
  have hc' : H.IsClique (↑(D.image Subtype.val) : Set W) := by
    intro u hu v hv huv
    obtain ⟨uu,huu,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨vv,hvv,rfl⟩ := Finset.mem_image.mp hv
    exact hc huu hvv (fun he => huv (congrArg Subtype.val he))
  have hd : k ≤ (D.image Subtype.val).card := by
    rwa [Finset.card_image_of_injective _ Subtype.val_injective]
  obtain ⟨E,he,hcard⟩ := Finset.exists_subset_card_eq hd
  exact hfree E ⟨fun u hu v hv huv => hc' (he hu) (he hv) huv,hcard⟩

end Se20Part
