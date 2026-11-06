import Se20Part.LabelledCut
import Se20Part.RepeatedCutPalette

noncomputable section
open scoped Classical
namespace Se20Part
variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}
local instance repeatedCutGeometryDecEq : DecidableEq G.edgeSet := Classical.decEq _

namespace LabelledCut
variable (C : LabelledCut G I)

def starColours (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) : Finset Colour :=
  (sideStar G C.side (C.left i)).image φ.colour

def boundaryColours (φ : PartialColouring (L2 G) (sideEdges G C.side)) : Finset Colour :=
  Finset.univ.biUnion (C.starColours φ)

def nearColours (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) : Finset Colour :=
  (sideNear G C.side (C.left i)).image φ.colour

def sourceList (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) : Finset Colour :=
  Finset.univ \ (C.nearColours φ i ∪ C.boundaryColours φ)

def targetForbidden (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) : Finset Colour :=
  C.nearColours φ i ∪ (Finset.univ.filter (fun j => j ≠ i ∧ C.right j = C.right i)).biUnion (C.starColours φ)

def targetList (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) : Finset Colour :=
  Finset.univ \ C.targetForbidden φ i

theorem starColours_card (hΔ : MaxDegreeFour G)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) :
    (C.starColours φ i).card ≤ 3 := by
  have := (C.endpoint_budgets hΔ i).1
  have := C.multiplicity_pos i
  exact Finset.card_image_le.trans (by omega)

theorem nearColours_card (hΔ : MaxDegreeFour G)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) :
    (C.nearColours φ i).card ≤ 12 := by
  have := (C.endpoint_budgets hΔ i).2
  have := C.multiplicity_pos i
  exact Finset.card_image_le.trans (by omega)

theorem boundaryColours_eight (hΔ : MaxDegreeFour G) (hn : Fintype.card I ≤ 4)
    (hrep : ¬ Function.Injective C.left)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) :
    (C.boundaryColours φ).card ≤ 8 := by
  have hlt : (Finset.univ.image C.left).card < Fintype.card I := by
    have hle := Finset.card_image_le (s := Finset.univ) (f := C.left)
    have hne : (Finset.univ.image C.left).card ≠ (Finset.univ : Finset I).card := by
      intro he
      apply hrep
      exact fun i j hij => (Finset.card_image_iff.mp he) (Finset.mem_univ i) (Finset.mem_univ j) hij
    simpa only [Finset.card_univ] using lt_of_le_of_ne hle hne
  have := C.boundary_colour_budget hΔ φ
  change (C.boundaryColours φ).card + Fintype.card I ≤ _ at this
  omega

theorem sourceList_budget (hΔ : MaxDegreeFour G)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) :
    20 ≤ (C.sourceList φ i).card +
      3 * (G.neighborFinset (C.left i) ∩ C.side).card + (C.boundaryColours φ).card := by
  have hb := sideNear_union_colour_budget G hΔ C.side φ (C.left_mem i)
    (C.boundaryColours φ) (fun c hc => Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hc⟩)
  have he := Finset.card_sdiff_add_card_inter (Finset.univ : Finset Colour)
    (C.nearColours φ i ∪ C.boundaryColours φ)
  simp only [Finset.univ_inter,Finset.card_univ,Fintype.card_fin] at he
  change (C.sourceList φ i).card + _ = 20 at he
  change (C.nearColours φ i ∪ C.boundaryColours φ).card ≤ _ at hb
  omega

theorem sourceList_three (hΔ : MaxDegreeFour G) (hn : Fintype.card I ≤ 4)
    (hrep : ¬ Function.Injective C.left)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) :
    3 ≤ (C.sourceList φ i).card := by
  have := C.sourceList_budget hΔ φ i
  have := C.boundaryColours_eight hΔ hn hrep φ
  have hb := (C.endpoint_budgets hΔ i).1
  rw [sideStar_card G C.side (C.left_mem i)] at hb
  have := C.multiplicity_pos i
  omega

theorem sourceList_large (hΔ : MaxDegreeFour G) (hn : Fintype.card I ≤ 4)
    (hrep : ¬ Function.Injective C.left)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) :
    ∃ i, 6 ≤ (C.sourceList φ i).card := by
  have hre := hrep
  simp only [Function.Injective] at hre
  push_neg at hre
  obtain ⟨i,j,he,hij⟩ := hre
  have hm : 2 ≤ C.multiplicity (C.left i) := by
    have hsub : {i,j} ⊆ Finset.univ.filter (fun k => C.left k = C.left i) := by
      intro k hk
      simp only [Finset.mem_insert,Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · simp
      · simp [he]
    simpa only [multiplicity,Finset.card_pair hij] using Finset.card_le_card hsub
  have := C.sourceList_budget hΔ φ i
  have := C.boundaryColours_eight hΔ hn hrep φ
  have hb := (C.endpoint_budgets hΔ i).1
  rw [sideStar_card G C.side (C.left_mem i)] at hb
  exact ⟨i,by omega⟩

theorem targetList_five (hΔ : MaxDegreeFour G)
    (htwo : ∀ v, C.swap.multiplicity v ≤ 2)
    (φ : PartialColouring (L2 G) (sideEdges G C.side)) (i : I) :
    5 ≤ (C.targetList φ i).card := by
  let J := Finset.univ.filter (fun j => j ≠ i ∧ C.right j = C.right i)
  have hJe : J = (Finset.univ.filter (fun j => C.right j = C.right i)).erase i := by
    ext j
    simp [J,and_left_comm,and_assoc]
  have hJ : J.card ≤ 1 := by
    have he := Finset.card_erase_add_one
      (show i ∈ Finset.univ.filter (fun j => C.right j = C.right i) by simp)
    have ht := htwo (C.right i)
    change (Finset.univ.filter (fun j => C.right j = C.right i)).card ≤ 2 at ht
    rw [hJe]
    omega
  have hextra : (J.biUnion (C.starColours φ)).card ≤ 3 := by
    calc
      _ ≤ ∑ j ∈ J, (C.starColours φ j).card := Finset.card_biUnion_le
      _ ≤ ∑ _j ∈ J, 3 := Finset.sum_le_sum (fun j _ => C.starColours_card hΔ φ j)
      _ = J.card * 3 := by simp
      _ ≤ 3 := by omega
  have hb := (Finset.card_union_le (C.nearColours φ i) (J.biUnion (C.starColours φ))).trans
    (Nat.add_le_add (C.nearColours_card hΔ φ i) hextra)
  have he := Finset.card_sdiff_add_card_inter (Finset.univ : Finset Colour) (C.targetForbidden φ i)
  simp only [Finset.univ_inter,Finset.card_univ,Fintype.card_fin] at he
  change (C.targetForbidden φ i).card ≤ 15 at hb
  change (C.targetList φ i).card + _ = 20 at he
  omega

theorem targetList_free (φ : PartialColouring (L2 G) (sideEdges G C.side))
    (i : I) {a : Colour} (ha : a ∈ C.targetList φ i)
    {e : G.edgeSet} (he : e ∈ sideEdges G C.side) (hie : (L2 G).Adj (C.edge i) e) :
    a ≠ φ.colour e := by
  intro heq
  apply (Finset.mem_sdiff.mp ha).2
  rcases C.conflict_cover i he hie with hnear | ⟨j,hj,hejr,hstar⟩
  · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e,hnear,heq.symm⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj,hejr⟩,
        Finset.mem_image.mpr ⟨e,hstar,heq.symm⟩⟩)

theorem sourceList_subset_target (φ : PartialColouring (L2 G) (sideEdges G C.side))
    (i : I) : C.sourceList φ i ⊆ C.targetList φ i := by
  intro a ha
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,?_⟩
  intro hb
  apply (Finset.mem_sdiff.mp ha).2
  rcases Finset.mem_union.mp hb with hn | hb
  · exact Finset.mem_union_left _ hn
  · obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,hj⟩)

end LabelledCut
end Se20Part
