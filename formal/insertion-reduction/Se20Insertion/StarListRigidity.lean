import Se20Insertion.ListRigidity

noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency.types false
namespace Se20Insertion.PartialColouring
variable {W : Type*} [DecidableEq W] {H : SimpleGraph W} {F : Finset W}

theorem eighteen_split (φ : PartialColouring H F) (K S : Finset W) (A : Finset Colour)
    (hA : A.card = 18) (hK : K.card ≤ 9) (hS : S.card ≤ 9)
    (hall : ∀ c ∈ A, ∃ x ∈ K ∪ S, x ∈ F ∧ φ.colour x = c) :
    K.card = 9 ∧ S.card = 9 ∧ Disjoint K S ∧
      (∀ x ∈ K ∪ S, x ∈ F) ∧ Set.InjOn φ.colour (↑(K ∪ S) : Set W) ∧
      S.image φ.colour = A \ K.image φ.colour := by
  let D := (K ∪ S).filter (· ∈ F)
  have hsub : A ⊆ D.image φ.colour := by
    intro c hc; obtain ⟨x,hx,hxF,hxc⟩ := hall c hc
    exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hxF⟩,hxc⟩
  have hl := Finset.card_le_card hsub
  have hi := Finset.card_image_le (s := D) (f := φ.colour)
  have hd : D.card ≤ (K ∪ S).card := Finset.card_filter_le _ _
  have hu := Finset.card_union_le K S
  have hp := Finset.card_union_add_card_inter K S
  have hD : D = K ∪ S := Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
  have him : D.image φ.colour = A := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hdis : Disjoint K S := Finset.disjoint_iff_inter_eq_empty.mpr
    (Finset.card_eq_zero.mp (by omega))
  have hinj : Set.InjOn φ.colour (↑(K ∪ S) : Set W) := by
    apply Finset.card_image_iff.mp
    rw [← hD,him]; omega
  refine ⟨by omega,by omega,hdis,?_,hinj,?_⟩
  · intro x hx; rw [← hD] at hx; exact (Finset.mem_filter.mp hx).2
  · ext c
    constructor
    · intro hc
      obtain ⟨x,hx,hxc⟩ := Finset.mem_image.mp hc
      refine Finset.mem_sdiff.mpr ⟨?_,?_⟩
      · rw [← him,hD]; exact Finset.mem_image.mpr ⟨x,Finset.mem_union_right _ hx,hxc⟩
      · rintro hy
        obtain ⟨y,hy,hyc⟩ := Finset.mem_image.mp hy
        have hxy := hinj (Finset.mem_union_right _ hx) (Finset.mem_union_left _ hy) (hxc.trans hyc.symm)
        exact Finset.disjoint_left.mp hdis hy (hxy ▸ hx)
    · intro hc
      obtain ⟨x,hx,_,hxc⟩ := hall c (Finset.mem_sdiff.mp hc).1
      exact Finset.mem_image.mpr ⟨x,(Finset.mem_union.mp hx).resolve_left
        (fun h => (Finset.mem_sdiff.mp hc).2 (Finset.mem_image.mpr ⟨x,h,hxc⟩)),hxc⟩

end Se20Insertion.PartialColouring
namespace Se20Insertion
variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- The tree-like corollary of 11.24. In fact the obstruction forces the
needed shell equalities without assuming local tree-likeness. -/
theorem degree_three_star_list_rigidity (hΔ : MaxDegreeFour G) {u : V}
    (hu : G.degree u = 3) {F : Finset G.edgeSet} (φ : PartialColouring (L2 G) F)
    (hF : Disjoint F (incident G u)) (hno : ¬ φ.OneSwapListRepair (incident G u)) :
    ∃ L A : Finset Colour, L.card = 2 ∧ A.card = 9 ∧
      (starBase G u).card = 9 ∧
      (∀ e ∈ incident G u, φ.available e = L) ∧
      ∀ (v : V) (huv : G.Adj u v),
        (shell G u v).card = 9 ∧ Disjoint (starBase G u) (shell G u v) ∧
        (∀ x ∈ starBase G u ∪ shell G u v, x ∈ F) ∧
        Set.InjOn φ.colour (↑(starBase G u ∪ shell G u v) : Set G.edgeSet) ∧
        (starBase G u ∪ shell G u v).image φ.colour = Finset.univ \ L ∧
        (shell G u v).image φ.colour = A ∧
        ∀ a ∈ L, ∀ c ∈ A, ∀ x ∈ shell G u v, φ.colour x = c →
          ∀ (w : V) (huw : G.Adj u w), ∀ y ∈ shell G u w, φ.colour y = c →
            φ.SameComponent a c x y := by
  have hi : (incident G u).card = 3 := by rw [card_incident,hu]
  have hL := (degree_three_lists G hΔ u hu φ hF).1
  obtain ⟨L,hLc,hlists,htight,hconn⟩ := φ.one_swap_list_rigidity (incident G u) hF
    (Finset.card_pos.mp (by omega)) (by simpa only [hi] using hL)
    (by intro e he; have hc := star_coloured_conflicts_le G hΔ φ u hF e ((mem_incident G u e).mp he); omega) hno
  have hLc : L.card = 2 := by omega
  let C := Finset.univ \ L
  have hC : C.card = 18 := by simp [C,Finset.card_sdiff_of_subset (Finset.subset_univ L),hLc]
  have cover (v : V) (huv : G.Adj u v) :
      ∀ c ∈ C, ∃ x ∈ starBase G u ∪ shell G u v, x ∈ F ∧ φ.colour x = c := by
    intro c hc
    obtain ⟨x,hx,_⟩ := (htight (edge G huv) (by simp [edge])).2 c (Finset.mem_sdiff.mp hc).2
    have hm := (mem_conflicts G (edge G huv) x).mpr hx.2.1
    rw [conflicts_star_decomposition G (edge G huv) rfl] at hm
    rcases Finset.mem_union.mp hm with hm | hm
    · rcases Finset.mem_union.mp hm with hm | hm
      · exact False.elim (Finset.disjoint_left.mp hF hx.1 (Finset.mem_erase.mp hm).2)
      · exact ⟨x,Finset.mem_union_left _ hm,hx.1,hx.2.2⟩
    · exact ⟨x,Finset.mem_union_right _ hm,hx.1,hx.2.2⟩
  have split (v : V) (huv : G.Adj u v) := φ.eighteen_split (starBase G u) (shell G u v) C hC
    (by have := starBase_card_le G hΔ u; omega) (shell_card_le G hΔ huv) (cover v huv)
  have hn : (G.neighborFinset u).Nonempty := Finset.card_pos.mp (by simpa [hu])
  obtain ⟨v,hv⟩ := hn
  have huv := (G.mem_neighborFinset _ _).mp hv
  let A := (shell G u v).image φ.colour
  have sp := split v huv
  have hA : A.card = 9 := by
    rw [Finset.card_image_of_injOn (sp.2.2.2.2.1.mono (by intro x hx; exact Finset.mem_union_right _ hx))]
    exact sp.2.1
  refine ⟨L,A,hLc,hA,sp.1,hlists,?_⟩
  intro w huw
  have sw := split w huw
  have hAw : (shell G u w).image φ.colour = A := sw.2.2.2.2.2.trans sp.2.2.2.2.2.symm
  have him : (starBase G u ∪ shell G u w).image φ.colour = C := by
    have hsub : C ⊆ (starBase G u ∪ shell G u w).image φ.colour := by
      intro c hc; obtain ⟨x,hx,_,hxc⟩ := cover w huw c hc; exact Finset.mem_image.mpr ⟨x,hx,hxc⟩
    apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
    have hh := Finset.card_image_le (s := starBase G u ∪ shell G u w) (f := φ.colour)
    have hh' := Finset.card_union_le (starBase G u) (shell G u w)
    omega
  refine ⟨sw.2.1,sw.2.2.1,sw.2.2.2.1,sw.2.2.2.2.1,him,hAw,?_⟩
  intro a ha c hc x hx hxc z huz y hy hyc
  have hcL : c ∉ L := by
    change c ∈ (shell G u v).image φ.colour at hc
    rw [sp.2.2.2.2.2] at hc
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hc).1).2
  have shellN (t : V) (hut : G.Adj u t) (q : G.edgeSet) (hq : q ∈ shell G u t)
      (hqc : φ.colour q = c) : φ.Neighbour (edge G hut) c q := by
    have st := split t hut
    refine ⟨st.2.2.2.1 q (Finset.mem_union_right _ hq),?_,hqc⟩
    apply (mem_conflicts G (edge G hut) q).mp
    rw [conflicts_star_decomposition G (edge G hut) rfl]
    exact Finset.mem_union_right _ hq
  exact hconn a ha c hcL (edge G huw) (by simp [edge]) (edge G huz) (by simp [edge]) x y
    (shellN w huw x hx hxc) (shellN z huz y hy hyc)

end Se20Insertion
