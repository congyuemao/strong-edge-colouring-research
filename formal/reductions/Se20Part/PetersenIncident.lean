import Se20Part.PetersenMinusSupport
import Se20Part.TriangleInsertion

namespace Se20Part

set_option maxRecDepth 10000 in
theorem petersen_common_neighbour : ∀ u v : Fin 10, u ≠ v →
    ¬ PetersenGraph.Adj u v → ∃ w, PetersenGraph.Adj u w ∧ PetersenGraph.Adj w v := by
  decide +kernel

noncomputable section
open scoped Classical
local instance petersenIncidentDecEq {V : Type*} (G : SimpleGraph V) :
    DecidableEq G.edgeSet := Classical.decEq _

/-- Any injected Petersen subgraph is induced in ambient girth at least five. -/
def inducedPetersenOfGirth {V : Type*} {G : SimpleGraph V} (hg : 5 ≤ G.egirth)
    (f : PetersenGraph →g G) (hf : Function.Injective f) : PetersenGraph ↪g G where
  toFun := f
  inj' := hf
  map_rel_iff' := by
    intro u v
    constructor
    · intro huv
      by_contra hn
      obtain ⟨w,huw,hwv⟩ := petersen_common_neighbour u v
        (fun h => huv.ne (congrArg f h)) hn
      exact GirthFive.no_triangle hg (f.map_adj huw) (f.map_adj hwv) huv.symm
    · exact f.map_adj

/-- Greedy extension with a budget measured in the unchanged ambient graph. -/
theorem greedy_partial_extension {W : Type*} (H : SimpleGraph W)
    (A B : Finset W) (hdis : Disjoint A B)
    (hbudget : ∀ e ∈ B, ((A ∪ B).filter (H.Adj e)).card < 20)
    (φ : PartialColouring H A) :
    ∃ θ : PartialColouring H (A ∪ B), ∀ a ∈ A, θ.colour a = φ.colour a := by
  have aux : ∀ T : Finset W, T ⊆ B →
      ∃ θ : PartialColouring H (A ∪ T), ∀ a ∈ A, θ.colour a = φ.colour a := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.union_empty]
      exact ⟨φ,by simp⟩
    | @insert e T heT ih =>
      intro hT
      obtain ⟨ψ,hψ⟩ := ih (fun x hx => hT (Finset.mem_insert_of_mem hx))
      have heB := hT (Finset.mem_insert_self e T)
      have heA : e ∉ A := fun he => Finset.disjoint_left.mp hdis he heB
      let D := ((A ∪ T).filter (H.Adj e)).image ψ.colour
      have hDc : D.card < (Finset.univ : Finset Colour).card := by
        have hsub : (A ∪ T).filter (H.Adj e) ⊆ (A ∪ B).filter (H.Adj e) := by
          intro x hx
          obtain ⟨hx,hxe⟩ := Finset.mem_filter.mp hx
          refine Finset.mem_filter.mpr ⟨?_,hxe⟩
          rcases Finset.mem_union.mp hx with hx | hx
          · exact Finset.mem_union_left _ hx
          · exact Finset.mem_union_right _ (hT (Finset.mem_insert_of_mem hx))
        have hc := (Finset.card_image_le (s := (A ∪ T).filter (H.Adj e))
          (f := ψ.colour)).trans (Finset.card_le_card hsub)
        exact (hc.trans_lt (hbudget e heB)).trans_eq (by simp)
      obtain ⟨c,_,hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hDc
      have hfree : ψ.Free e c := by
        rintro ⟨x,hx,hex,hxc⟩
        exact hc (Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,hex⟩,hxc⟩)
      have heq : A ∪ insert e T = insert e (A ∪ T) := by
        ext w
        simp only [Finset.mem_union,Finset.mem_insert]
        tauto
      rw [heq]
      refine ⟨ψ.insertFree e c hfree,?_⟩
      intro a ha
      exact (ψ.insertFree_unchanged (by simp [heA,heT]) hfree a
        (Finset.mem_union_left _ ha)).trans (hψ a ha)
  exact aux B (Finset.Subset.refl _)

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def petersenIncidentEdges (f : PetersenGraph ↪g G) : Finset G.edgeSet :=
  Finset.univ.filter (fun e => ∃ u, f u ∈ e.val)

def petersenSpokes (f : PetersenGraph ↪g G) : Finset G.edgeSet :=
  petersenIncidentEdges f \ petersenInternalEdges f

theorem petersen_spoke_ends (f : PetersenGraph ↪g G) {e : G.edgeSet}
    (he : e ∈ petersenSpokes f) :
    ∃ u x, e.val = s(f u,x) ∧ x ∉ Set.range f := by
  obtain ⟨hei,hen⟩ := Finset.mem_sdiff.mp he
  obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hei).2
  obtain ⟨x,hx⟩ := Sym2.mem_iff_exists.mp hu
  refine ⟨u,x,hx,?_⟩
  rintro ⟨v,rfl⟩
  have huv : PetersenGraph.Adj u v := f.map_rel_iff.mp (G.mem_edgeSet.mp (hx ▸ e.prop))
  let d : PetersenGraph.edgeSet := ⟨s(u,v),PetersenGraph.mem_edgeSet.mpr huv⟩
  apply hen
  exact Finset.mem_image.mpr ⟨d,Finset.mem_univ _,Subtype.ext hx.symm⟩

theorem petersen_external_rim (hΔ : MaxDegreeFour G) (f : PetersenGraph ↪g G)
    {u : Fin 10} {x : V} (hx : x ∉ Set.range f) (hux : G.Adj (f u) x) :
    (G.neighborFinset (f u)).erase x = (PetersenGraph.neighborFinset u).image f := by
  let N := (PetersenGraph.neighborFinset u).image f
  have hN : N.card = 3 := by
    rw [Finset.card_image_of_injective _ f.injective,
      SimpleGraph.card_neighborFinset_eq_degree,petersen_cubic]
  have hNsub : N ⊆ G.neighborFinset (f u) := by
    intro z hz
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
    exact (G.mem_neighborFinset _ _).mpr
      (f.toHom.map_adj ((PetersenGraph.mem_neighborFinset _ _).mp hw))
  have hxN : x ∉ N := by
    intro hxN; obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hxN; exact hx ⟨w,hw⟩
  have hfull : insert x N = G.neighborFinset (f u) := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.insert_subset ((G.mem_neighborFinset _ _).mpr hux) hNsub
    · rw [Finset.card_insert_of_notMem hxN,hN,SimpleGraph.card_neighborFinset_eq_degree]
      exact hΔ (f u)
  rw [← hfull,Finset.erase_insert hxN]

theorem petersen_external_unique_parent (hg : 5 ≤ G.egirth) (f : PetersenGraph ↪g G)
    {u v : Fin 10} {x : V} (hx : x ∉ Set.range f)
    (hux : G.Adj (f u) x) (hvx : G.Adj (f v) x) : u = v := by
  by_contra huv
  by_cases hp : PetersenGraph.Adj u v
  · exact GirthFive.no_triangle hg (f.toHom.map_adj hp) hvx hux.symm
  · obtain ⟨w,huw,hwv⟩ := petersen_common_neighbour u v huv hp
    rcases GirthFive.square_backtrack hg (f.toHom.map_adj huw)
      (f.toHom.map_adj hwv) hvx hux.symm with h | h
    · exact huv (f.injective h)
    · exact hx ⟨w,h⟩

theorem petersen_spokes_matching (hΔ : MaxDegreeFour G) (hg : 5 ≤ G.egirth)
    (f : PetersenGraph ↪g G) :
    ∀ z, ∀ e ∈ petersenSpokes f, ∀ d ∈ petersenSpokes f,
      z ∈ e.val → z ∈ d.val → e = d := by
  have unique : ∀ u x y, x ∉ Set.range f → y ∉ Set.range f →
      G.Adj (f u) x → G.Adj (f u) y → x = y := by
    intro u x y hx hy hux huy
    by_contra hxy
    have hyN : y ∈ (G.neighborFinset (f u)).erase x := by
      exact Finset.mem_erase.mpr ⟨Ne.symm hxy,(G.mem_neighborFinset _ _).mpr huy⟩
    rw [petersen_external_rim hΔ f hx hux] at hyN
    obtain ⟨w,_,hw⟩ := Finset.mem_image.mp hyN
    exact hy ⟨w,hw⟩
  intro z e he d hd hze hzd
  obtain ⟨u,x,hex,hx⟩ := petersen_spoke_ends f he
  obtain ⟨v,y,hdy,hy⟩ := petersen_spoke_ends f hd
  have hux := G.mem_edgeSet.mp (hex ▸ e.prop)
  have hvy := G.mem_edgeSet.mp (hdy ▸ d.prop)
  rw [hex,Sym2.mem_iff] at hze
  rw [hdy,Sym2.mem_iff] at hzd
  have huv : u = v := by
    rcases hze with rfl | rfl <;> rcases hzd with h | h
    · exact f.injective h
    · exact False.elim (hy ⟨u,h⟩)
    · exact False.elim (hx ⟨v,h.symm⟩)
    · exact petersen_external_unique_parent hg f hx hux (h.symm ▸ hvy)
  subst v
  have hxy := unique u x y hx hy hux hvy
  apply Subtype.ext
  rw [hex,hdy,hxy]

theorem petersen_spoke_outside_conflicts (hΔ : MaxDegreeFour G)
    (f : PetersenGraph ↪g G) (A : Finset G.edgeSet)
    (hA : ∀ e ∈ A, ∀ u, f u ∉ e.val) {e : G.edgeSet} (he : e ∈ petersenSpokes f) :
    (A.filter ((L2 G).Adj e)).card ≤ 12 := by
  obtain ⟨u,x,hex,hx⟩ := petersen_spoke_ends f he
  have hux := G.mem_edgeSet.mp (hex ▸ e.prop)
  have hlow : ∀ z ∈ (G.neighborFinset (f u)).erase x, (incident G z ∩ A).card = 0 := by
    intro z hz
    rw [petersen_external_rim hΔ f hx hux] at hz
    obtain ⟨w,_,rfl⟩ := Finset.mem_image.mp hz
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    exact hA d (Finset.mem_inter.mp hd).2 w
      ((mem_incident G _ _).mp (Finset.mem_inter.mp hd).1)
  have hs := selected_conflicts_le_rim_sum A e hex
  have hsplit := Finset.sum_union_inter (s₁ := (G.neighborFinset (f u)).erase x)
    (s₂ := (G.neighborFinset x).erase (f u)) (f := fun z => (incident G z ∩ A).card)
  have hzero : (∑ z ∈ (G.neighborFinset (f u)).erase x, (incident G z ∩ A).card) = 0 :=
    Finset.sum_eq_zero hlow
  have hv := Finset.card_erase_add_one ((G.mem_neighborFinset _ _).mpr hux.symm)
  rw [SimpleGraph.card_neighborFinset_eq_degree] at hv
  have hdv := hΔ x
  have hlv : (∑ z ∈ (G.neighborFinset x).erase (f u), (incident G z ∩ A).card) ≤
      4 * ((G.neighborFinset x).erase (f u)).card := by
    calc
      _ ≤ ∑ _z ∈ (G.neighborFinset x).erase (f u), 4 := Finset.sum_le_sum (by
        intro z _
        exact (Finset.card_le_card Finset.inter_subset_left).trans
          (by simpa only [card_incident] using hΔ z))
      _ = _ := by simp [Nat.mul_comm]
  unfold rim at hs
  omega

/-- Full G14 extension, including every edge incident with the Petersen
vertices and preserving an arbitrary fixed outside partial colouring. -/
theorem petersen_incident_extension (hΔ : MaxDegreeFour G) (hg : 5 ≤ G.egirth)
    (f : PetersenGraph ↪g G) (A : Finset G.edgeSet)
    (hA : ∀ e ∈ A, ∀ u, f u ∉ e.val) (φ : PartialColouring (L2 G) A) :
    ∃ θ : PartialColouring (L2 G) (A ∪ petersenIncidentEdges f),
      ∀ a ∈ A, θ.colour a = φ.colour a := by
  have hAI : Disjoint A (petersenIncidentEdges f) := by
    apply Finset.disjoint_left.mpr
    intro e he hei
    obtain ⟨u,hu⟩ := (Finset.mem_filter.mp hei).2
    exact hA e he u hu
  have hsub : petersenInternalEdges f ⊆ petersenIncidentEdges f := by
    intro e he
    obtain ⟨d,_,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨u,v,hd⟩ : ∃ u v, d.val = s(u,v) := Sym2.ind (fun u v => ⟨u,v,rfl⟩) d.val
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,u,?_⟩
    exact Sym2.mem_map.mpr ⟨u,hd ▸ Sym2.mem_mk_left u v,rfl⟩
  have hbudget : ∀ e ∈ petersenSpokes f,
      ((A ∪ petersenSpokes f).filter ((L2 G).Adj e)).card < 20 := by
    intro e he
    have ha := petersen_spoke_outside_conflicts hΔ f A hA he
    have hb := matching_conflicts_le_six G hΔ (petersenSpokes f)
      (petersen_spokes_matching hΔ hg f) e
    rw [Finset.filter_union]
    have hc := Finset.card_union_le (A.filter ((L2 G).Adj e))
      ((petersenSpokes f).filter ((L2 G).Adj e))
    omega
  obtain ⟨ψ,hψ⟩ := greedy_partial_extension (L2 G) A (petersenSpokes f)
    (hAI.mono_right Finset.sdiff_subset) hbudget φ
  have hdis : Disjoint (A ∪ petersenSpokes f) (petersenInternalEdges f) := by
    exact Finset.disjoint_union_left.mpr ⟨hAI.mono_right hsub,Finset.sdiff_disjoint⟩
  obtain ⟨θ,hθ⟩ := induced_petersen_extension G hΔ f _ hdis ψ
  have heq : A ∪ petersenSpokes f ∪ petersenInternalEdges f = A ∪ petersenIncidentEdges f := by
    rw [Finset.union_assoc,petersenSpokes,Finset.sdiff_union_of_subset hsub]
  rw [← heq]
  exact ⟨θ,fun a ha => (hθ a (Finset.mem_union_left _ ha)).trans (hψ a ha)⟩

theorem critical21_no_supported_petersen_subgraph (hΔ : MaxDegreeFour G)
    (hg : 5 ≤ G.egirth) (f : PetersenGraph →g G) (hf : Function.Injective f)
    {F : Finset G.edgeSet} (hF : Critical21 G F) :
    ¬ (∀ u : Fin 10, ∃ e ∈ F, f u ∈ e.val) :=
  critical21_no_supported_induced_petersen hΔ (inducedPetersenOfGirth hg f hf) hF

end
end Se20Part
