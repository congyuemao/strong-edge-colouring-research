import Se20Part.RepeatedCutGeometry
import Se20Part.MatchingCutGluing

noncomputable section
open scoped Classical
namespace Se20Part
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}
local instance labelledCutGluingDecEq : DecidableEq G.edgeSet := Classical.decEq _

namespace LabelledCut
variable (C : LabelledCut G I)

/-- Assemble the actual cut edges after choosing a compatible palette and
distinct cut colours. Every conflict is still an ambient conflict. -/
theorem gluing_of_palette
    (φ : PartialColouring (L2 G) (sideEdges G C.side))
    (ψ : PartialColouring (L2 G) (sideEdges G C.swap.side))
    (p : Colour ≃ Colour) (x y : I → Colour) (hy : Function.Injective y)
    (hmem : ∀ i, x i ∈ C.swap.targetList ψ i ∧ y i ∈ C.targetList φ i ∧ p (x i) = y i)
    (hp : ∀ c, ¬ starForbidden (C.swap.starColours ψ) (C.starColours φ) c (p c)) :
    ∃ θ : (L2 G).Coloring Colour,
      (∀ e ∈ sideEdges G C.side, θ e = φ.colour e) ∧
      ∀ e ∈ sideEdges G C.swap.side, θ e = p (ψ.colour e) := by
  have hcross : ∀ e ∈ sideEdges G C.side, ∀ f ∈ sideEdges G C.swap.side,
      (L2 G).Adj e f → φ.colour e ≠ p (ψ.colour f) := by
    intro e he f hf hef heq
    obtain ⟨u,hu,v,hv,huv⟩ := (cut_cross_conflict_iff G C.side he hf).mp hef
    obtain ⟨i,hi,hj⟩ := C.complete u ((mem_sideEdges G _ _).mp he u hu) v
      (Finset.mem_sdiff.mp ((mem_sideEdges G _ _).mp hf v hv)).2 huv
    apply hp (ψ.colour f)
    refine ⟨i,Finset.mem_image.mpr ⟨f,?_,rfl⟩,?_⟩
    · exact Finset.mem_inter.mpr ⟨(mem_incident G _ _).mpr
        (by change C.right i ∈ f.val; exact hj.symm ▸ hv),hf⟩
    · rw [← heq]
      exact Finset.mem_image.mpr ⟨e,Finset.mem_inter.mpr
        ⟨(mem_incident G _ _).mpr (hi.symm ▸ hu),he⟩,rfl⟩
  have hnewA : ∀ i e, e ∈ sideEdges G C.side → (L2 G).Adj (C.edge i) e → y i ≠ φ.colour e :=
    fun i _ he hie => C.targetList_free φ i (hmem i).2.1 he hie
  have hnewB : ∀ i e, e ∈ sideEdges G C.swap.side → (L2 G).Adj (C.edge i) e → y i ≠ p (ψ.colour e) := by
    intro i e he hie heq
    apply C.swap.targetList_free ψ i (hmem i).1 he (by simpa only [swap_edge] using hie)
    exact p.injective ((hmem i).2.2.trans heq)
  let c : G.edgeSet → Colour := fun e => if e ∈ sideEdges G C.side then φ.colour e
    else if e ∈ sideEdges G C.swap.side then p (ψ.colour e)
    else if he : ∃ i, C.edge i = e then y he.choose else 0
  have hcA : ∀ e ∈ sideEdges G C.side, c e = φ.colour e := fun e he => if_pos he
  have hcB : ∀ e ∈ sideEdges G C.swap.side, c e = p (ψ.colour e) := by
    intro e he
    have hn := fun h => Finset.disjoint_left.mp C.side_disjoint h he
    simp only [c,if_neg hn,if_pos he]
  have hcE : ∀ i, c (C.edge i) = y i := by
    intro i
    have he : ∃ j, C.edge j = C.edge i := ⟨i,rfl⟩
    have hnB : C.edge i ∉ sideEdges G C.swap.side := by
      simpa only [LabelledCut.swap] using C.edge_not_other_side i
    simp only [c,if_neg (C.edge_not_side i),if_neg hnB,
      dif_pos he,C.edge_injective he.choose_spec]
  have hproper : ∀ e f, (L2 G).Adj e f → c e ≠ c f := by
    intro e f hef
    rcases C.edge_cases e with he | he | ⟨i,rfl⟩ <;>
      rcases C.edge_cases f with hf | hf | ⟨j,rfl⟩
    · rw [hcA e he,hcA f hf]; exact φ.proper he hf hef
    · rw [hcA e he,hcB f hf]; exact hcross e he f hf hef
    · rw [hcA e he,hcE j]; exact (hnewA j e he hef.symm).symm
    · rw [hcB e he,hcA f hf]; exact (hcross f hf e he hef.symm).symm
    · rw [hcB e he,hcB f hf]; exact fun h => ψ.proper he hf hef (p.injective h)
    · rw [hcB e he,hcE j]; exact (hnewB j e he hef.symm).symm
    · rw [hcE i,hcA f hf]; exact hnewA i f hf hef
    · rw [hcE i,hcB f hf]; exact hnewB i f hf hef
    · rw [hcE i,hcE j]; exact fun h => hef.ne (congrArg C.edge (hy h))
  exact ⟨SimpleGraph.Coloring.mk c (fun {e f} h => hproper e f h),hcA,hcB⟩

end LabelledCut

/-- The repeated-endpoint three/four-cut construction, also covering smaller
cuts. Source rows are made empty by avoiding all source boundary stars. -/
theorem repeated_small_cut_gluing (hΔ : MaxDegreeFour G) (n : ℕ) (hn : n ≤ 4)
    (C : LabelledCut G (Fin n)) (hrep : ¬ Function.Injective C.right)
    (htwo : ∀ v, C.swap.multiplicity v ≤ 2)
    (φ : PartialColouring (L2 G) (sideEdges G C.side))
    (ψ : PartialColouring (L2 G) (sideEdges G C.swap.side)) :
    StrongColourable G 20 := by
  obtain ⟨p,x,y,hx,hy,hmem,hp⟩ := repeated_cut_small_palette rfl n hn
    (C.swap.starColours ψ) (C.starColours φ) (C.swap.sourceList ψ) (C.targetList φ)
    (C.swap.starColours_card hΔ ψ) (C.starColours_card hΔ φ)
    (C.swap.sourceList_three hΔ (by simpa using hn) hrep ψ)
    (by
      intro _
      obtain ⟨i,hi⟩ := C.swap.sourceList_large hΔ (by simpa using hn) hrep ψ
      exact ⟨i,by omega⟩)
    (fun i => (by omega : n ≤ 5).trans (C.targetList_five hΔ htwo φ i))
    (by
      intro i
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_union_right _ hb))
  obtain ⟨θ,_⟩ := C.gluing_of_palette φ ψ p x y hy
    (fun i => ⟨C.swap.sourceList_subset_target ψ i (hmem i).1,(hmem i).2⟩) hp
  exact ⟨θ⟩

/-- Every cut of size at most four with endpoint multiplicities at most two
can be glued from induced-side strong colourings. -/
theorem small_cut_strongColourable (hΔ : MaxDegreeFour G) (n : ℕ) (hn : n ≤ 4)
    (C : LabelledCut G (Fin n))
    (hleft : ∀ v, C.multiplicity v ≤ 2) (hright : ∀ v, C.swap.multiplicity v ≤ 2)
    (hA : StrongColourable (G.induce (C.side : Set V)) 20)
    (hB : StrongColourable (G.induce (C.swap.side : Set V)) 20) :
    StrongColourable G 20 := by
  obtain ⟨φ⟩ := (side_colourable_iff G C.side).mp hA
  obtain ⟨ψ⟩ := (side_colourable_iff G C.swap.side).mp hB
  by_cases hr : Function.Injective C.right
  · by_cases hl : Function.Injective C.left
    · let M : MatchingCut G (Fin n) :=
        ⟨C.side,C.left,C.right,C.left_mem,C.right_notMem,C.adjacent,hl,hr,C.complete⟩
      obtain ⟨θ,_⟩ := matching_cut_gluing G hΔ n (by omega) M φ ψ
      exact ⟨θ⟩
    · have hss : C.swap.swap.side = C.side := by
        ext v
        simp [LabelledCut.swap]
      have φ' : PartialColouring (L2 G) (sideEdges G C.swap.swap.side) := hss.symm ▸ φ
      exact repeated_small_cut_gluing hΔ n hn C.swap hl hleft ψ φ'
  · exact repeated_small_cut_gluing hΔ n hn C hr hright φ ψ

end Se20Part
