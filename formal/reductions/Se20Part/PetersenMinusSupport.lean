import Se20Part.PetersenMinusKernel

noncomputable section
open scoped Classical
namespace Se20Part
variable {V : Type*} [Fintype V] {G : SimpleGraph V}
local instance petersenMinusSupportDecEq : DecidableEq G.edgeSet := Classical.decEq _

theorem selected_conflicts_le_eighteen (hΔ : MaxDegreeFour G)
    (F : Finset G.edgeSet) (e : G.edgeSet) {u v : V} (he : e.val = s(u,v))
    (hlow : ∀ z ∈ (G.neighborFinset u).erase v, (incident G z ∩ F).card ≤ 2) :
    (F.filter ((L2 G).Adj e)).card ≤ 18 := by
  have huv : G.Adj u v := G.mem_edgeSet.mp (he ▸ e.prop)
  have hu := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv)
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr huv.symm)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hu hv
  have hdu := hΔ u
  have hdv := hΔ v
  have hsum := selected_conflicts_le_rim_sum F e he
  have hsplit : (∑ z ∈ rim G u v, (incident G z ∩ F).card) ≤
      (∑ z ∈ (G.neighborFinset u).erase v, (incident G z ∩ F).card) +
      ∑ z ∈ (G.neighborFinset v).erase u, (incident G z ∩ F).card := by
    have hh := Finset.sum_union_inter (s₁ := (G.neighborFinset u).erase v)
      (s₂ := (G.neighborFinset v).erase u) (f := fun z => (incident G z ∩ F).card)
    unfold rim
    omega
  have hlu : (∑ z ∈ (G.neighborFinset u).erase v, (incident G z ∩ F).card) ≤
      2 * ((G.neighborFinset u).erase v).card := by
    calc
      _ ≤ ∑ _z ∈ (G.neighborFinset u).erase v, 2 := Finset.sum_le_sum hlow
      _ = _ := by simp [Nat.mul_comm]
  have hlv : (∑ z ∈ (G.neighborFinset v).erase u, (incident G z ∩ F).card) ≤
      4 * ((G.neighborFinset v).erase u).card := by
    calc
      _ ≤ ∑ _z ∈ (G.neighborFinset v).erase u, 4 := Finset.sum_le_sum (by
        intro z _
        exact (Finset.card_le_card Finset.inter_subset_left).trans
          (by simpa only [card_incident] using hΔ z))
      _ = _ := by simp [Nat.mul_comm]
  omega

theorem petersenMinus_selected_degree_two (hΔ : MaxDegreeFour G)
    (f : PetersenMinusGraph ↪g G) (F : Finset G.edgeSet)
    (hdis : Disjoint F (petersenMinusInternalEdges f)) (u : Fin 10) :
    (incident G (f u) ∩ F).card ≤ 2 := by
  let J := (incident PetersenMinusGraph u).image f.mapEdgeSet
  have hJ : 2 ≤ J.card := by
    have hi : Function.Injective f.mapEdgeSet :=
      SimpleGraph.Hom.mapEdgeSet.injective f.toHom f.injective
    dsimp only [J]
    rw [Finset.card_image_of_injective _ hi,card_incident]
    have hd := petersenMinus_degree_bounds.1 u
    simp only [← SimpleGraph.card_neighborSet_eq_degree,Fintype.card_eq_nat_card] at hd ⊢
    exact hd
  have hJI : J ⊆ incident G (f u) := by
    intro e he
    obtain ⟨d,hd,rfl⟩ := Finset.mem_image.mp he
    apply (mem_incident G _ _).mpr
    exact Sym2.mem_map.mpr ⟨u,(mem_incident PetersenMinusGraph _ _).mp hd,rfl⟩
  have hJF : Disjoint J (incident G (f u) ∩ F) := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp he
    exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp hf).2
      (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,rfl⟩)
  have hc := Finset.card_le_card
    (Finset.union_subset hJI (Finset.inter_subset_left : incident G (f u) ∩ F ⊆ incident G (f u)))
  rw [Finset.card_union_of_disjoint hJF,card_incident] at hc
  have := hΔ (f u)
  omega

/-- G15's list theorem excludes the whole induced block from critical
support, including the case with no selected internal edge. -/
theorem critical21_no_supported_induced_petersenMinus
    (hG15 : PetersenMinusListTheoremG15) (hΔ : MaxDegreeFour G)
    (f : PetersenMinusGraph ↪g G) {F : Finset G.edgeSet} (hF : Critical21 G F) :
    ¬ (∀ u : Fin 10, ∃ e ∈ F, f u ∈ e.val) := by
  intro hsupp
  have hdis := critical21_disjoint_induced_petersenMinus G hG15 hΔ f hF
  obtain ⟨e,heF,heu⟩ := hsupp 1
  obtain ⟨x,hex⟩ := Sym2.mem_iff_exists.mp heu
  have hux : G.Adj (f 1) x := G.mem_edgeSet.mp (hex ▸ e.prop)
  let N := (PetersenMinusGraph.neighborFinset 1).image f
  have hN : N.card = 3 := by
    rw [Finset.card_image_of_injective _ f.injective,
      SimpleGraph.card_neighborFinset_eq_degree,petersenMinus_degree_bounds.2]
  have hNsub : N ⊆ G.neighborFinset (f 1) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (G.mem_neighborFinset _ _).mpr
      (f.toHom.map_adj ((PetersenMinusGraph.mem_neighborFinset _ _).mp hw))
  have hxN : x ∉ N := by
    intro hx
    obtain ⟨w,hw,hwx⟩ := Finset.mem_image.mp hx
    let d : PetersenMinusGraph.edgeSet :=
      ⟨s(1,w),PetersenMinusGraph.mem_edgeSet.mpr ((PetersenMinusGraph.mem_neighborFinset _ _).mp hw)⟩
    have hd : f.mapEdgeSet d = e := by
      apply Subtype.ext
      change s(f 1,f w) = e.val
      rw [hwx,hex]
    exact Finset.disjoint_left.mp hdis heF
      (Finset.mem_image.mpr ⟨d,Finset.mem_univ _,hd⟩)
  have hfull : insert x N = G.neighborFinset (f 1) := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset ((G.mem_neighborFinset _ _).mpr hux) hNsub
    · rw [Finset.card_insert_of_notMem hxN,hN,SimpleGraph.card_neighborFinset_eq_degree]
      exact hΔ (f 1)
  have hlow : ∀ z ∈ (G.neighborFinset (f 1)).erase x, (incident G z ∩ F).card ≤ 2 := by
    intro z hz
    obtain ⟨hzx,hzN⟩ := Finset.mem_erase.mp hz
    rw [← hfull] at hzN
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp ((Finset.mem_insert.mp hzN).resolve_left hzx)
    exact petersenMinus_selected_degree_two hΔ f F hdis w
  have hmax := selected_conflicts_le_eighteen hΔ F e hex hlow
  have hmin := critical21_min_degree G hF heF
  omega

/-- In girth at least five, a Petersen-minus-edge subgraph is either
induced or completes to an induced Petersen graph. Both are excluded. -/
theorem critical21_no_supported_petersenMinus_subgraph
    (hG15 : PetersenMinusListTheoremG15) (hΔ : MaxDegreeFour G) (hg : 5 ≤ G.egirth)
    (f : PetersenMinusGraph →g G) (hf : Function.Injective f)
    {F : Finset G.edgeSet} (hF : Critical21 G F) :
    ¬ (∀ u : Fin 10, ∃ e ∈ F, f u ∈ e.val) := by
  intro hsupp
  by_cases h07 : G.Adj (f 0) (f 7)
  · let p : PetersenGraph ↪g G :=
      { toFun := f
        inj' := hf
        map_rel_iff' := by
          intro a b
          constructor
          · intro hab
            rcases petersenMinus_only_missing_chord hg f hf hab with h | h | h
            · exact h.1
            · rcases h with ⟨rfl,rfl⟩; decide
            · rcases h with ⟨rfl,rfl⟩; decide
          · intro hab
            by_cases he : (a = 0 ∧ b = 7) ∨ (a = 7 ∧ b = 0)
            · rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
              · exact h07
              · exact h07.symm
            · exact f.map_adj ⟨hab,he⟩ }
    exact critical21_no_supported_induced_petersen hΔ p hF hsupp
  · let p : PetersenMinusGraph ↪g G :=
      { toFun := f
        inj' := hf
        map_rel_iff' := by
          intro a b
          constructor
          · intro hab
            rcases petersenMinus_only_missing_chord hg f hf hab with h | h | h
            · exact h
            · rcases h with ⟨rfl,rfl⟩; exact False.elim (h07 hab)
            · rcases h with ⟨rfl,rfl⟩; exact False.elim (h07 hab.symm)
          · exact f.map_adj }
    exact critical21_no_supported_induced_petersenMinus hG15 hΔ p hF hsupp

end Se20Part
