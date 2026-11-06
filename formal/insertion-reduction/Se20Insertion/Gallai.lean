import Se20Insertion.RegularCycle

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion
variable {W : Type*} [DecidableEq W] (H : SimpleGraph W)

/-- A nonempty connected induced subgraph with no cut vertex. Preconnected
deletions include the one-vertex case (whose deletion is empty). -/
def BlockEligible (B : Finset W) : Prop :=
  (H.induce (B : Set W)).Connected ∧
    ∀ v : B, ((H.induce (B : Set W)).induce {x | x ≠ v}).Preconnected

/-- Finite blocks, including bridges and isolated vertices: maximal induced
connected vertex sets with no cut vertex, inside the specified domain U. -/
def FiniteBlock (U B : Finset W) : Prop :=
  B ⊆ U ∧ BlockEligible H B ∧
    ∀ D, D ⊆ U → BlockEligible H D → B ⊆ D → D = B

def GallaiForestOn (U : Finset W) : Prop :=
  ∀ B, FiniteBlock H U B →
    (∀ x ∈ B, ∀ y ∈ B, x ≠ y → H.Adj x y) ∨
      DegreeList.IsOddCycleGraph (H.induce (B : Set W))

def GallaiTree [Fintype W] : Prop := H.Connected ∧ GallaiForestOn H Finset.univ

namespace DegreeList
variable {C : Type*} [Nonempty C]

/-- Passing to the finite subtype changes neither the lists nor properness. -/
theorem bad_lists_on_induce (L : W → Finset C) (B : Finset W)
    (hdeg : ∀ x ∈ B, (B.filter (H.Adj x)).card ≤ (L x).card)
    (hbad : ¬ ColourableOn H L B) :
    (∀ x : B, (H.induce (B : Set W)).degree x ≤ (L x.val).card) ∧
      ¬ ColourableOn (H.induce (B : Set W)) (fun x => L x.val) Finset.univ := by
  refine ⟨fun x => ?_,?_⟩
  · have himage : ((H.induce (B : Set W)).neighborFinset x).image Subtype.val =
        B.filter (H.Adj x.val) := by
      ext y
      simp only [Finset.mem_image,SimpleGraph.mem_neighborFinset,Finset.mem_filter]
      constructor
      · rintro ⟨z,hz,rfl⟩
        exact ⟨z.prop,hz⟩
      · rintro ⟨hy,hxy⟩
        exact ⟨⟨y,hy⟩,hxy,rfl⟩
    have hcard : (H.induce (B : Set W)).degree x = (B.filter (H.Adj x.val)).card := by
      rw [← himage,Finset.card_image_of_injective _ Subtype.val_injective]
      rfl
    rw [hcard]
    exact hdeg x.val x.prop
  · rintro ⟨c,hc,hp⟩
    apply hbad
    refine ⟨fun x => if hx : x ∈ B then c ⟨x,hx⟩ else Classical.choice inferInstance,?_,?_⟩
    · intro x hx
      simpa only [dite_eq_left hx] using hc ⟨x,hx⟩ (Finset.mem_univ _)
    · intro x hx y hy hxy heq
      exact hp ⟨x,hx⟩ (Finset.mem_univ _) ⟨y,hy⟩ (Finset.mem_univ _) hxy
        (by simpa only [dite_eq_left hx,dite_eq_left hy] using heq)

theorem eligible_bad_lists_complete_or_odd (B : Finset W) (he : BlockEligible H B)
    (L : W → Finset C) (hdeg : ∀ x ∈ B, (B.filter (H.Adj x)).card ≤ (L x).card)
    (hbad : ¬ ColourableOn H L B) :
    (∀ x ∈ B, ∀ y ∈ B, x ≠ y → H.Adj x y) ∨ IsOddCycleGraph (H.induce (B : Set W)) := by
  by_cases hsmall : B.card ≤ 1
  · left
    intro x hx y hy hxy
    exact (hxy ((Finset.card_le_one.mp hsmall) x hx y hy)).elim
  have hdel : ∀ v : B, ((H.induce (B : Set W)).induce {x | x ≠ v}).Connected := by
    intro v
    have hlt : ({v.val} : Finset W).card < B.card := by simp only [Finset.card_singleton]; omega
    obtain ⟨w,hw,hwn⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    have hwv : (⟨w,hw⟩ : B) ≠ v := fun hh => hwn (by simpa using congrArg Subtype.val hh)
    exact { preconnected := he.2 v, nonempty := ⟨⟨⟨w,hw⟩,hwv⟩⟩ }
  obtain ⟨hd,hb⟩ := bad_lists_on_induce H L B hdeg hbad
  rcases bad_noncut_complete_or_odd_cycle (H.induce (B : Set W)) (fun x => L x.val)
      he.1 hdel hd hb with hc | ho
  · exact Or.inl (fun x hx y hy hxy => hc ⟨x,hx⟩ ⟨y,hy⟩
      (fun heq => hxy (congrArg Subtype.val heq)))
  · exact Or.inr ho

end DegreeList

theorem gallaiForest_of_induced_obstructions {C : Type*} [Nonempty C] (U : Finset W)
    (hbad : ∀ B ⊆ U, B.Nonempty → ∃ L : W → Finset C,
      (∀ x ∈ B, (B.filter (H.Adj x)).card ≤ (L x).card) ∧ ¬ DegreeList.ColourableOn H L B) :
    GallaiForestOn H U := by
  intro B hB
  obtain ⟨x⟩ := hB.2.1.1.nonempty
  obtain ⟨L,hd,hb⟩ := hbad B hB.1 ⟨x.val,x.prop⟩
  exact DegreeList.eligible_bad_lists_complete_or_odd H B hB.2.1 L hd hb

/-- Gallai / Borodin--Erdos--Rubin--Taylor, obstruction direction: a finite
connected graph with uncolourable lists at least its degrees is a Gallai tree.
Every exceptional block is either explicitly complete or isomorphic to an
odd cycle; no structural lemma is a premise. -/
theorem degree_list_obstruction_gallai_tree [Fintype W] {C : Type*}
    (L : W → Finset C) (hc : H.Connected) (hd : ∀ x, H.degree x ≤ (L x).card)
    (hbad : ¬ DegreeList.ColourableOn H L Finset.univ) : GallaiTree H := by
  by_cases hC : Nonempty C
  · letI : Nonempty C := hC
    refine ⟨hc,gallaiForest_of_induced_obstructions (C := C) H Finset.univ ?_⟩
    intro B _ hB
    exact DegreeList.bad_induced_lists H L hc hd hbad B hB
  · refine ⟨hc,fun B _ => Or.inl ?_⟩
    intro x _ y _ hxy
    have hL : L x = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      exact fun c _ => hC ⟨c⟩
    have hz := hd x
    rw [hL,Finset.card_empty] at hz
    have hp := (hc x y).degree_pos_left hxy
    omega

/-- Exactly the degree-20 vertices of the critical induced graph. -/
def criticalDegreeTwenty (F : Finset W) : Finset W :=
  F.filter (fun x => (F.filter (H.Adj x)).card = 20)

/-- Corollary 11.40(5), in its general critical-graph form. -/
theorem critical_degree_twenty_gallai {F : Finset W} (hcrit : CriticalSet H F) :
    GallaiForestOn H (criticalDegreeTwenty H F) := by
  apply gallaiForest_of_induced_obstructions (C := Colour) H
  intro B hB hne
  have hBF : B ⊆ F := hB.trans (Finset.filter_subset _ _)
  have hd : ∀ x ∈ B, (F.filter (H.Adj x)).card = 20 :=
    fun x hx => (Finset.mem_filter.mp (hB hx)).2
  obtain ⟨L,hL,hbad⟩ := critical_low_degree_list_obstruction hcrit B hBF hne hd
  refine ⟨L,hL,?_⟩
  rintro ⟨c,hc,hp⟩
  exact hbad ⟨fun x => c x.val,fun x => hc x.val x.prop,
    fun x y hxy => hp x.val x.prop y.val y.prop hxy⟩

/-- The manuscript specialization, retaining the ambient L² adjacency. -/
theorem corollary1140_five {V : Type*} (G : SimpleGraph V) {F : Finset G.edgeSet}
    (hcrit : CriticalSet (L2 G) F) :
    GallaiForestOn (L2 G) (criticalDegreeTwenty (L2 G) F) :=
  critical_degree_twenty_gallai (L2 G) hcrit

end Se20Insertion
