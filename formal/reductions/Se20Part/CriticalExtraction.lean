import Se20Part.CliqueTwenty

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every non-20-colourable ambient edge set contains a 21-critical edge
set. No witness edge is removed from the ambient graph. -/
theorem exists_critical21 {F : Finset G.edgeSet}
    (hF : ¬ ((L2 G).induce (F : Set G.edgeSet)).Colorable 20) :
    ∃ A ⊆ F, Critical21 G A := by
  let S := F.powerset.filter (fun (A : Finset G.edgeSet) => ¬ ((L2 G).induce (A : Set G.edgeSet)).Colorable 20)
  obtain ⟨A,hAS,hmin⟩ := S.exists_min_image Finset.card
    ⟨F,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.Subset.refl _),hF⟩⟩
  obtain ⟨hAF,hA⟩ := Finset.mem_filter.mp hAS
  have hsub : A ⊆ F := Finset.mem_powerset.mp hAF
  have hdel : ∀ e ∈ A, ((L2 G).induce (A.erase e : Set G.edgeSet)).Colorable 20 := by
    intro e he
    by_contra hn
    have hh := hmin (A.erase e) (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hsub),hn⟩)
    have hc := Finset.card_erase_lt_of_mem he
    omega
  have hpos : 0 < A.card := by
    by_contra hn
    exact hA (colourable_of_finset_card (L2 G) A 20 (by omega))
  obtain ⟨e,he⟩ := Finset.card_pos.mp hpos
  obtain ⟨φ⟩ := (partialColouring_iff_colourable (L2 G) (A.erase e)).mpr (hdel e he)
  let lift : Fin 20 → Fin 21 := Fin.castLE (by decide)
  let c : A → Fin 21 := fun x => if x.val = e then ⟨20,by decide⟩ else lift (φ.colour x)
  refine ⟨A,hsub,⟨⟨SimpleGraph.Coloring.mk c ?_⟩,hA,hdel⟩⟩
  intro x y hxy heq
  have hval := congrArg Fin.val heq
  dsimp [c,lift] at hval
  by_cases hx : x.val = e <;> by_cases hy : y.val = e
  · exact hxy.ne (Subtype.ext (hx.trans hy.symm))
  · simp only [hx,hy,if_pos,if_false,Fin.val_castLE] at hval
    have := (φ.colour y).isLt
    omega
  · simp only [hx,hy,if_pos,if_false,Fin.val_castLE] at hval
    have := (φ.colour x).isLt
    omega
  · have hcol : φ.colour x = φ.colour y := Fin.ext (by simpa only [hx,hy,if_false,Fin.val_castLE] using hval)
    exact φ.proper (Finset.mem_erase.mpr ⟨hx,x.prop⟩) (Finset.mem_erase.mpr ⟨hy,y.prop⟩) hxy hcol

end Se20Part
