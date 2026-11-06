import Se20Part.GallaiLowBlocks

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part

theorem exists_vertex_minimal_noncolourable {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hb : ¬ H.Colorable k) :
    ∃ A : Finset W, VertexMinimalNoncolourable (H.induce (A : Set W)) k := by
  let bad := (Finset.univ : Finset W).powerset.filter
    (fun A : Finset W => ¬ (H.induce (A : Set W)).Colorable k)
  have hn : bad.Nonempty := by
    refine ⟨Finset.univ,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),?_⟩⟩
    rintro ⟨c⟩
    exact hb ⟨SimpleGraph.Coloring.mk (fun x => c ⟨x,Finset.mem_univ _⟩)
      (fun h => c.valid h)⟩
  obtain ⟨A,hA,hmin⟩ := bad.exists_min_image Finset.card hn
  refine ⟨A,(Finset.mem_filter.mp hA).2,?_⟩
  intro B hB
  let D := B.image Subtype.val
  have hc : D.card = B.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hcard : Fintype.card (A : Set W) = A.card := Fintype.card_coe A
  have hsmall : D.card < A.card := by simpa only [hc,hcard] using hB
  have hg : (H.induce (D : Set W)).Colorable k := by
    by_contra hh
    have hm := hmin D (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),hh⟩)
    omega
  obtain ⟨c⟩ := hg
  refine ⟨SimpleGraph.Coloring.mk
    (fun x => c ⟨x.val.val,Finset.mem_image.mpr ⟨x.val,x.prop,rfl⟩⟩) ?_⟩
  intro x y hxy
  exact c.valid hxy

theorem vertex_minimal_noncolourable_degree {W : Type} [Fintype W]
    (H : SimpleGraph W) (k : ℕ) (hmin : VertexMinimalNoncolourable H k) :
    ∀ v, k ≤ H.degree v := by
  intro v
  by_contra! hv
  let O := (Finset.univ : Finset W).erase v
  have hsmall : O.card < Fintype.card W := by
    simpa only [O,Finset.card_univ] using Finset.card_erase_lt_of_mem (Finset.mem_univ v)
  obtain ⟨c⟩ := hmin.2 O hsmall
  let N := H.neighborFinset v
  let f : N → Fin k := fun x => c ⟨x.val,Finset.mem_erase.mpr
    ⟨((H.mem_neighborFinset _ _).mp x.prop).ne.symm,Finset.mem_univ _⟩⟩
  have hsize : (Finset.univ.image f).card < (Finset.univ : Finset (Fin k)).card := by
    have hc := Finset.card_image_le (s := Finset.univ) (f := f)
    have hc' : (Finset.univ.image f).card ≤ H.degree v := by
      simpa only [Finset.card_univ,Fintype.card_coe,N,SimpleGraph.card_neighborFinset_eq_degree]
        using hc
    simpa only [Finset.card_univ,Fintype.card_fin] using hc'.trans_lt hv
  obtain ⟨a,_,ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hsize
  let d : W → Fin k := fun x => if hx : x = v then a else
    c ⟨x,Finset.mem_erase.mpr ⟨hx,Finset.mem_univ _⟩⟩
  apply hmin.1
  refine ⟨SimpleGraph.Coloring.mk d ?_⟩
  intro x y hxy
  dsimp only [d]
  split_ifs with hx hy hy
  · exact (hxy.ne (hx.trans hy.symm)).elim
  · subst x
    intro he
    exact ha (Finset.mem_image.mpr
      ⟨⟨y,(H.mem_neighborFinset _ _).mpr hxy⟩,Finset.mem_univ _,he.symm⟩)
  · subst y
    intro he
    exact ha (Finset.mem_image.mpr
      ⟨⟨x,(H.mem_neighborFinset _ _).mpr hxy.symm⟩,Finset.mem_univ _,he⟩)
  · exact c.valid hxy

end Se20Part
