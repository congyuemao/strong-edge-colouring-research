import Se20Part.DegreeListReduction

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Part.DegreeList
variable {W C : Type*} [Fintype W] [DecidableEq W] [Nonempty C] (H : SimpleGraph W)

theorem degree_delete_set (B : Finset W) (x : {x // x ∉ B}) :
    (H.induce {x | x ∉ B}).degree x + (H.neighborFinset x.val ∩ B).card = H.degree x.val := by
  have hc : (H.induce {x | x ∉ B}).degree x = (H.neighborFinset x.val \ B).card := by
    rw [← SimpleGraph.card_neighborSet_eq_degree,← Fintype.card_coe (H.neighborFinset x.val \ B)]
    apply Fintype.card_congr
      { toFun := fun y => ⟨y.val.val,Finset.mem_sdiff.mpr
          ⟨(H.mem_neighborFinset _ _).mpr y.prop,y.val.prop⟩⟩
        invFun := fun y => ⟨⟨y.val,(Finset.mem_sdiff.mp y.prop).2⟩,
          (H.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp y.prop).1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hc]
  simpa using Finset.card_sdiff_add_card_inter (H.neighborFinset x.val) B

/-- Precolour an independent set with one common colour. A remaining vertex
with two neighbours in it supplies the strict slack for the connected remainder. -/
theorem colourable_of_independent_precolour (L : W → Finset C) (B : Finset W)
    (hconn : (H.induce {x | x ∉ B}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card)
    (hB : ∀ x ∈ B, ∀ y ∈ B, ¬ H.Adj x y) {a : C}
    (ha : ∀ x ∈ B, a ∈ L x) (r : {x // x ∉ B})
    (hr : 2 ≤ (H.neighborFinset r.val ∩ B).card) : ColourableOn H L Finset.univ := by
  let J := H.induce {x | x ∉ B}
  let d (x : {x // x ∉ B}) := (H.neighborFinset x.val ∩ B).card
  let L' (x : {x // x ∉ B}) := if 0 < d x then (L x.val).erase a else L x.val
  have hdeg (x : {x // x ∉ B}) : J.degree x ≤ (L' x).card := by
    have hx : J.degree x + d x = H.degree x.val := degree_delete_set H B x
    have hl := hd x.val
    have he : (L x.val).card ≤ ((L x.val).erase a).card + 1 := by
      by_cases hm : a ∈ L x.val
      · exact (Finset.card_erase_add_one hm).ge
      · simp [Finset.erase_eq_of_notMem hm]
    dsimp only [L']
    split_ifs with hdpos <;> omega
  have hslack : J.degree r < (L' r).card := by
    have hx : J.degree r + d r = H.degree r.val := degree_delete_set H B r
    have hl := hd r.val
    have hr' : 2 ≤ d r := hr
    have he : (L r.val).card ≤ ((L r.val).erase a).card + 1 := by
      by_cases hm : a ∈ L r.val
      · exact (Finset.card_erase_add_one hm).ge
      · simp [Finset.erase_eq_of_notMem hm]
    rw [show L' r = (L r.val).erase a from if_pos (by omega)]
    omega
  obtain ⟨c,hc,hproper⟩ := colourable_of_one_slack J L' hconn hdeg r hslack
  have hcL (x : {x // x ∉ B}) : c x ∈ L x.val := by
    have hh := hc x (Finset.mem_univ _)
    dsimp only [L'] at hh
    split_ifs at hh
    · exact Finset.mem_of_mem_erase hh
    · exact hh
  have hca (x : {x // x ∉ B}) (y : W) (hy : y ∈ B) (hxy : H.Adj x.val y) : c x ≠ a := by
    have hp : 0 < d x := Finset.card_pos.mpr
      ⟨y,Finset.mem_inter.mpr ⟨(H.mem_neighborFinset _ _).mpr hxy,hy⟩⟩
    have hh := hc x (Finset.mem_univ _)
    exact (Finset.mem_erase.mp (show c x ∈ (L x.val).erase a from by simpa [L',hp] using hh)).1
  refine ⟨fun x => if hx : x ∈ B then a else c ⟨x,hx⟩,?_,?_⟩
  · intro x _
    dsimp only
    split_ifs with hx
    · exact ha x hx
    · exact hcL ⟨x,hx⟩
  · intro x _ y _ hxy heq
    by_cases hx : x ∈ B <;> by_cases hy : y ∈ B
    · exact hB x hx y hy hxy
    · exact hca ⟨y,hy⟩ x hx hxy.symm (by simpa [hx,hy] using heq.symm)
    · exact hca ⟨x,hx⟩ y hy hxy (by simpa [hx,hy] using heq)
    · exact hproper ⟨x,hx⟩ (Finset.mem_univ _) ⟨y,hy⟩ (Finset.mem_univ _) hxy
        (by simpa [hx,hy] using heq)

/-- The non-separating pair colouring argument used in degree-choosability.
Existence of such a pair is a separate structural theorem, not a hypothesis
that is silently inferred from two-connectivity. -/
theorem colourable_of_nonseparating_pair (L : W → Finset C) {u v r : W}
    (huv : u ≠ v) (hn : ¬ H.Adj u v) (hru : H.Adj r u) (hrv : H.Adj r v)
    (hconn : (H.induce {x | x ∉ ({u,v} : Finset W)}).Connected)
    (hd : ∀ x, H.degree x ≤ (L x).card) {a : C} (hau : a ∈ L u) (hav : a ∈ L v) :
    ColourableOn H L Finset.univ := by
  refine colourable_of_independent_precolour H L {u,v} hconn hd ?_
    (a := a) ?_ ⟨r,by simp [hru.ne,hrv.ne]⟩ ?_
  · intro x hx y hy hxy
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact hxy.ne rfl
    · exact hn hxy
    · exact hn hxy.symm
    · exact hxy.ne rfl
  · intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  · have hs : ({u,v} : Finset W) ⊆ H.neighborFinset r := by
      intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [hru,hrv]
    rw [Finset.inter_eq_right.mpr hs,Finset.card_pair huv]

end Se20Part.DegreeList
