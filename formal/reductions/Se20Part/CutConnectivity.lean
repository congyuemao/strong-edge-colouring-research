import Se20Part.CutMinimal

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
local instance cutConnectivityDecEq : DecidableEq G.edgeSet := Classical.decEq _

theorem cutBoundary_le_degree_sum (A : Finset V) :
    (cutBoundary G A).card ≤ ∑ v ∈ A, G.degree v := by
  have := cutBoundary_degree_sum G A
  omega

/-- For disjoint sets with no edge between them, their boundaries add. -/
theorem cutBoundary_union_anticomplete (A B : Finset V) (hd : Disjoint A B)
    (hab : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) :
    (cutBoundary G (A ∪ B)).card = (cutBoundary G A).card + (cutBoundary G B).card := by
  have he : cutBoundary G (A ∪ B) = cutBoundary G A ∪ cutBoundary G B := by
    ext p
    simp only [cutBoundary,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    constructor
    · rintro ⟨ha | hb,hn,hp⟩
      · exact Or.inl ⟨ha,fun h => hn (Or.inl h),hp⟩
      · exact Or.inr ⟨hb,fun h => hn (Or.inr h),hp⟩
    · rintro (⟨ha,hn,hp⟩ | ⟨hb,hn,hp⟩)
      · exact ⟨Or.inl ha,fun h => h.elim hn (fun h => hab _ ha _ h hp),hp⟩
      · exact ⟨Or.inr hb,fun h => h.elim (fun h => hab _ h _ hb hp.symm) hn,hp⟩
  rw [he,Finset.card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro p hp hq
  exact Finset.disjoint_left.mp hd (Finset.mem_filter.mp hp).2.1
    (Finset.mem_filter.mp hq).2.1

namespace InducedMinimalCounterexample
variable (hG : InducedMinimalCounterexample G)
include hG

theorem card_vertices_eleven : 11 ≤ Fintype.card V := by
  by_contra hn
  have hs : (∑ v, G.degree v) ≤ 4 * Fintype.card V := by
    calc
      _ ≤ ∑ _v : V, 4 := Finset.sum_le_sum (fun v _ => hG.1 v)
      _ = _ := by simp [Nat.mul_comm]
  rw [G.sum_degrees_eq_twice_card_edges,← G.card_edgeSet] at hs
  apply hG.2.1
  exact (L2 G).colorable_of_fintype.mono (by omega)

theorem degree_three (v : V) : 3 ≤ G.degree v := by
  have hn := hG.card_vertices_eleven
  have hb : (Finset.univ \ ({v} : Finset V)).Nonempty := by
    apply Finset.card_pos.mp
    simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_singleton,Finset.card_univ]
    omega
  have hc := hG.cut_three {v} (by simp) hb
  exact hc.trans (by simpa using cutBoundary_le_degree_sum (G := G) {v})

theorem no_matching_five_cut (C : MatchingCut G (Fin 5)) : False := by
  have hA : C.side.Nonempty := ⟨C.left 0,C.left_mem 0⟩
  have hB : (Finset.univ \ C.side).Nonempty :=
    ⟨C.right 0,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,C.right_notMem 0⟩⟩
  obtain ⟨hAc,hBc⟩ := hG.cut_side_colourings C.side hA hB
  exact hG.2.1 (matching_cut_strongColourable G hG.1 5 (by decide) C hAc hBc)

theorem regular_cut_four (hreg : FourRegular G) (A : Finset V)
    (hA : A.Nonempty) (hB : (Finset.univ \ A).Nonempty) :
    4 ≤ (cutBoundary G A).card := by
  have h := hG.cut_three A hA hB
  obtain ⟨k,hk⟩ := fourRegular_cut_even G hreg A
  omega

/-- A component separated from the rest by at most two vertices cannot be
a singleton: simplicity would give it degree at most two. -/
theorem separated_side_card_two (S A : Finset V) (hS : S.card ≤ 2)
    (hA : A.Nonempty) (hd : Disjoint A S)
    (hout : ∀ a ∈ A, ∀ b, G.Adj a b → b ∈ A ∨ b ∈ S) : 2 ≤ A.card := by
  by_contra hn
  have he : A.card = 1 := by have := Finset.card_pos.mpr hA; omega
  obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp he
  have hs : G.neighborFinset a ⊆ S := by
    intro b hb
    rcases hout a (by simp) b ((G.mem_neighborFinset _ _).mp hb) with ha | hs
    · have he : b = a := by simpa using ha
      exact False.elim (((G.mem_neighborFinset _ _).mp hb).ne he.symm)
    · exact hs
  have hc := Finset.card_le_card hs
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hc
  have := hG.degree_three a
  omega

/-- The cut inequalities rule out every separation by at most two vertices. -/
theorem no_small_separator (S A B : Finset V) (hS : S.card ≤ 2)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hd : Disjoint A B) (hAS : Disjoint A S) (hBS : Disjoint B S)
    (hcover : A ∪ B = Finset.univ \ S)
    (hab : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b) : False := by
  have hpart : ∀ v, v ∈ A ∨ v ∈ B ∨ v ∈ S := by
    intro v
    by_cases hs : v ∈ S
    · exact Or.inr (Or.inr hs)
    · have hv : v ∈ A ∪ B := hcover.symm ▸ Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hs⟩
      exact (Finset.mem_union.mp hv).imp_right Or.inl
  have hAc : 2 ≤ A.card := hG.separated_side_card_two S A hS hA hAS (by
    intro a ha b hp
    rcases hpart b with hb | hb | hb
    · exact Or.inl hb
    · exact False.elim (hab a ha b hb hp)
    · exact Or.inr hb)
  have hBc : 2 ≤ B.card := hG.separated_side_card_two S B hS hB hBS (by
    intro b hb a hp
    rcases hpart a with ha | ha | ha
    · exact False.elim (hab a ha b hb hp.symm)
    · exact Or.inl ha
    · exact Or.inr ha)
  have hsubB : B ⊆ Finset.univ \ A := fun b hb => Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _,fun ha => Finset.disjoint_left.mp hd ha hb⟩
  have hsubA : A ⊆ Finset.univ \ B := fun a ha => Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _,fun hb => Finset.disjoint_left.mp hd ha hb⟩
  have hca := hG.nontrivial_cut_five A hAc (hBc.trans (Finset.card_le_card hsubB))
  have hcb := hG.nontrivial_cut_five B hBc (hAc.trans (Finset.card_le_card hsubA))
  have he := cutBoundary_union_anticomplete A B hd hab
  rw [hcover,cutBoundary_compl] at he
  have hc := cutBoundary_le_degree_sum (G := G) S
  have hs : (∑ v ∈ S, G.degree v) ≤ 4 * S.card := by
    calc
      _ ≤ ∑ _v ∈ S, 4 := Finset.sum_le_sum (fun v _ => hG.1 v)
      _ = _ := by simp [Nat.mul_comm]
  omega

/-- Deleting any set of at most two vertices preserves reachability. -/
theorem delete_two_preconnected (S : Finset V) (hS : S.card ≤ 2) :
    (G.induce ((Finset.univ \ S : Finset V) : Set V)).Preconnected := by
  let R := Finset.univ \ S
  let H := G.induce (R : Set V)
  intro a b
  by_contra hn
  let X := Finset.univ.filter (H.Reachable a)
  let A := X.image Subtype.val
  let B := R \ A
  have hAR : A ⊆ R := by
    intro v hv
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hv
    exact w.prop
  have ha : a.val ∈ A := Finset.mem_image.mpr
    ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.rfl⟩,rfl⟩
  have hb : b.val ∈ B := by
    refine Finset.mem_sdiff.mpr ⟨b.prop,?_⟩
    intro hb
    obtain ⟨w,hw,he⟩ := Finset.mem_image.mp hb
    have hwb : w = b := Subtype.ext he
    exact hn (hwb ▸ (Finset.mem_filter.mp hw).2)
  apply hG.no_small_separator S A B hS ⟨a.val,ha⟩ ⟨b.val,hb⟩
  · exact Finset.disjoint_left.mpr (fun _ ha hb => (Finset.mem_sdiff.mp hb).2 ha)
  · exact Finset.disjoint_left.mpr (fun _ hv hs => (Finset.mem_sdiff.mp (hAR hv)).2 hs)
  · exact Finset.disjoint_left.mpr (fun _ hv hs =>
      (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hs)
  · exact Finset.union_sdiff_of_subset hAR
  · intro u hu v hv huv
    obtain ⟨w,hw,hwu⟩ := Finset.mem_image.mp hu
    have hvR := (Finset.mem_sdiff.mp hv).1
    have hp : H.Adj w ⟨v,hvR⟩ := by change G.Adj w.val v; simpa only [hwu] using huv
    apply (Finset.mem_sdiff.mp hv).2
    exact Finset.mem_image.mpr ⟨⟨v,hvR⟩,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,((Finset.mem_filter.mp hw).2).trans hp.reachable⟩,rfl⟩

/-- G12's vertex connectivity conclusion, stated explicitly in terms of
deleting vertices rather than assuming an abstract connectivity oracle. -/
theorem delete_two_connected (S : Finset V) (hS : S.card ≤ 2) :
    (G.induce ((Finset.univ \ S : Finset V) : Set V)).Connected := by
  have hn := hG.card_vertices_eleven
  have hc : (Finset.univ \ S : Finset V).Nonempty := by
    apply Finset.card_pos.mp
    simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ]
    omega
  letI : Nonempty ((Finset.univ \ S : Finset V) : Set V) := ⟨⟨hc.choose,hc.choose_spec⟩⟩
  exact ⟨hG.delete_two_preconnected S hS⟩

end InducedMinimalCounterexample
end Se20Part
