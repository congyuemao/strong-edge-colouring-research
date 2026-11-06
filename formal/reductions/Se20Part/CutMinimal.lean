import Se20Part.CutBoundary

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
local instance cutMinimalDecEq : DecidableEq G.edgeSet := Classical.decEq _

/-- Moving a vertex across the cut removes its outside incidences and adds
its inside incidences. The identity retains both terms without truncation. -/
theorem cutBoundary_erase_identity (A : Finset V) {v : V} (hv : v ∈ A) :
    (cutBoundary G (A.erase v)).card + 2 * (G.neighborFinset v \ A).card =
      (cutBoundary G A).card + G.degree v := by
  let R := (cutBoundary G A).filter (fun p => p.1 ≠ v)
  let D := (cutBoundary G A).filter (fun p => p.1 = v)
  let N := (G.neighborFinset v ∩ A).image (fun w => (w,v))
  have hsplit : R.card + D.card = (cutBoundary G A).card := by
    simpa only [R,D,not_not] using Finset.card_filter_add_card_filter_not
      (s := cutBoundary G A) (fun p : V × V => p.1 ≠ v)
  have hD : D.card = (G.neighborFinset v \ A).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · intro p hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨_,_,hn,ha⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr (he ▸ ha),hn⟩
    · intro p hp q hq he
      exact Prod.ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he
    · intro w hw
      obtain ⟨hwN,hwA⟩ := Finset.mem_sdiff.mp hw
      exact ⟨(v,w),Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,hv,hwA,(G.mem_neighborFinset _ _).mp hwN⟩,rfl⟩,rfl⟩
  have hN : N.card = (G.neighborFinset v ∩ A).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hdis : Disjoint R N := by
    apply Finset.disjoint_left.mpr
    intro p hp hn
    obtain ⟨w,_,he⟩ := Finset.mem_image.mp hn
    have hnv := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.2.1
    exact hnv ((congrArg Prod.snd he) ▸ hv)
  have he : cutBoundary G (A.erase v) = R ∪ N := by
    ext p
    constructor
    · intro hp
      obtain ⟨_,hu,hw,hadj⟩ := Finset.mem_filter.mp hp
      obtain ⟨huv,huA⟩ := Finset.mem_erase.mp hu
      by_cases hpv : p.2 = v
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨p.1,Finset.mem_inter.mpr
          ⟨(G.mem_neighborFinset _ _).mpr (hpv ▸ hadj.symm),huA⟩,Prod.ext rfl hpv.symm⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _,huA,(fun h => hw (Finset.mem_erase.mpr ⟨hpv,h⟩)),hadj⟩,huv⟩)
    · intro hp
      rcases Finset.mem_union.mp hp with hr | hn
      · obtain ⟨hr,huv⟩ := Finset.mem_filter.mp hr
        obtain ⟨_,hu,hw,hadj⟩ := Finset.mem_filter.mp hr
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_erase.mpr ⟨huv,hu⟩,
          fun h => hw (Finset.mem_of_mem_erase h),hadj⟩
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hn
        have hadj := (G.mem_neighborFinset _ _).mp (Finset.mem_inter.mp hw).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,Finset.mem_erase.mpr
          ⟨hadj.ne.symm,(Finset.mem_inter.mp hw).2⟩,by simp,hadj.symm⟩
  have hc := congrArg Finset.card he
  rw [Finset.card_union_of_disjoint hdis,hN] at hc
  have hdeg := Finset.card_sdiff_add_card_inter (G.neighborFinset v) A
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hdeg
  omega

/-- Every proper induced subgraph is colourable. A counterexample minimal
among all original graphs has this property; no regular-only minimality is used. -/
def InducedMinimalCounterexample : Prop :=
  MaxDegreeFour G ∧ ¬ StrongColourable G 20 ∧
    ∀ A : Finset V, A.card < Fintype.card V → StrongColourable (G.induce (A : Set V)) 20

namespace InducedMinimalCounterexample
variable {G} (hG : InducedMinimalCounterexample G)
include hG

theorem cut_side_colourings (A : Finset V) (hA : A.Nonempty)
    (hB : (Finset.univ \ A).Nonempty) :
    StrongColourable (G.induce (A : Set V)) 20 ∧
      StrongColourable (G.induce ((Finset.univ \ A : Finset V) : Set V)) 20 := by
  have he := Finset.card_sdiff_add_card_inter (Finset.univ : Finset V) A
  simp only [Finset.univ_inter,Finset.card_univ] at he
  have := Finset.card_pos.mpr hA
  have := Finset.card_pos.mpr hB
  exact ⟨hG.2.2 A (by omega),hG.2.2 _ (by omega)⟩

theorem cut_three (A : Finset V) (hA : A.Nonempty)
    (hB : (Finset.univ \ A).Nonempty) : 3 ≤ (cutBoundary G A).card := by
  by_contra hn
  let C := labelledBoundary G A
  obtain ⟨hAc,hBc⟩ := hG.cut_side_colourings A hA hB
  apply hG.2.1
  apply small_cut_strongColourable hG.1 (cutBoundary G A).card (by omega) C
  · intro v
    have h := Finset.card_le_univ (Finset.univ.filter (fun i => C.left i = v))
    simp only [Fintype.card_fin] at h
    exact h.trans (by omega)
  · intro v
    have h := Finset.card_le_univ (Finset.univ.filter (fun i => C.right i = v))
    simp only [Fintype.card_fin] at h
    exact h.trans (by omega)
  · exact hAc
  · exact hBc

theorem preconnected : G.Preconnected := by
  intro a b
  by_contra hn
  let A := Finset.univ.filter (G.Reachable a)
  have ha : a ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.rfl⟩
  have hb : b ∈ Finset.univ \ A := by simpa [A] using hn
  have hc := hG.cut_three A ⟨a,ha⟩ ⟨b,hb⟩
  have he : cutBoundary G A = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨_,hu,hw,hadj⟩ := Finset.mem_filter.mp hp
    exact hw (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      ((Finset.mem_filter.mp hu).2).trans hadj.reachable⟩)
  rw [he,Finset.card_empty] at hc
  omega

theorem nontrivial_cut_endpoint_two (A : Finset V) (hA : 2 ≤ A.card)
    (hB : (Finset.univ \ A).Nonempty) (hsmall : (cutBoundary G A).card ≤ 4)
    {v : V} (hv : v ∈ A) : (G.neighborFinset v \ A).card ≤ 2 := by
  have hAe : (A.erase v).Nonempty := by
    apply Finset.card_pos.mp
    have he := Finset.card_erase_add_one hv
    omega
  have hBe : (Finset.univ \ A.erase v).Nonempty := hB.mono
    (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) (Finset.erase_subset _ _))
  have hc := hG.cut_three (A.erase v) hAe hBe
  have hid := cutBoundary_erase_identity G A hv
  have hdeg := hG.1 v
  omega

/-- Every nontrivial cut of a minimal counterexample has at least five
edges, including cuts with repeated boundary endpoints. -/
theorem nontrivial_cut_five (A : Finset V) (hA : 2 ≤ A.card)
    (hB : 2 ≤ (Finset.univ \ A).card) : 5 ≤ (cutBoundary G A).card := by
  by_contra hn
  have hsmall : (cutBoundary G A).card ≤ 4 := by omega
  have hAn := Finset.card_pos.mp (show 0 < A.card by omega)
  have hBn := Finset.card_pos.mp (show 0 < (Finset.univ \ A).card by omega)
  have hcompl : Finset.univ \ (Finset.univ \ A) = A := by ext v; simp
  let C := labelledBoundary G A
  obtain ⟨hAc,hBc⟩ := hG.cut_side_colourings A hAn hBn
  apply hG.2.1
  apply small_cut_strongColourable hG.1 (cutBoundary G A).card hsmall C
  · intro v
    by_cases hv : v ∈ C.side
    · rw [C.multiplicity_eq_cross hv]
      exact hG.nontrivial_cut_endpoint_two A hA hBn hsmall hv
    · rw [C.multiplicity_zero hv]; omega
  · intro v
    by_cases hv : v ∈ C.swap.side
    · rw [C.swap.multiplicity_eq_cross hv]
      apply hG.nontrivial_cut_endpoint_two (Finset.univ \ A) hB
      · simpa only [hcompl] using hAn
      · simpa only [cutBoundary_compl] using hsmall
      · exact hv
    · rw [C.swap.multiplicity_zero hv]; omega
  · exact hAc
  · exact hBc

theorem regular_nontrivial_cut_six (hreg : FourRegular G) (A : Finset V)
    (hA : 2 ≤ A.card) (hB : 2 ≤ (Finset.univ \ A).card) :
    6 ≤ (cutBoundary G A).card :=
  fourRegular_nontrivial_cut_six G hreg A (hG.nontrivial_cut_five A hA hB)

end InducedMinimalCounterexample
end Se20Part
